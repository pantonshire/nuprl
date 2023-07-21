mod de_bruijn;
mod metadata;
mod object_id;
mod path;
mod phase1_parse;
mod phase2_nameres;
mod phase3_proofck;
mod stdlib;
mod source;
mod unif_var;
mod uniform_term;
mod utils;
mod var_stack;

use std::{io::{self, Read}, path::{PathBuf, Path}, fs, collections::{HashSet, BTreeMap}, fmt, process::ExitCode, borrow::Cow};

use clap::Parser;
use metadata::{ObjectMetadataStore, ObjectMetadata};
use object_id::ObjectIdGen;
use path::{path::{CanonLibPath, CanonLibPathBuf}, name_tree::{NameTreeError, NameTree}};
use phase1_parse::{error::ParseError, parse_expr, parse_statements};
use phase2_nameres::{expr::NameResolveError, statement::Statement};
use phase3_proofck::{library::{Library, ResolveError, Resolver, Context}, var_names::NameAssignments, object::{UnresolvedObjectKind, UnresolvedObject}};
use rkyv::{ser::{serializers::AllocSerializer, Serializer}, de::deserializers::SharedDeserializeMap, Deserialize, AlignedVec};
use serde::Serialize;
use source::{Span, Source, SourceIdGen, SourceKind, SourceModule, SourceId, SourceError, TextSource, SourceRepr};
use stdlib::StdLibObjs;
use var_stack::VarStack;
use walkdir::WalkDir;

use crate::{phase3_proofck::inf_intrinsic::InfIntrinsic, uniform_term::Term};

const DEFAULT_NAMESPACE: u64 = 0;

#[cfg(feature = "standard_library")]
const STD_ARCHIVE: &[u8] = include_bytes!("../std.nulib");

#[derive(Parser, Debug)]
#[command(author, version, about, long_about = None)]
struct Args {
    #[clap(subcommand)]
    subcommand: Subcommand,
}

#[derive(Parser, Debug)]
enum Subcommand {
    Check(CheckArgs),
    Compile(CompileArgs),
    Reduce(ReduceArgs),
    ImportTerm(ImportTermArgs),
}

#[derive(Parser, Debug)]
struct CheckArgs {
    paths: Vec<String>,
}

#[derive(Parser, Debug)]
struct CompileArgs {
    #[clap(short, long)]
    namespace: u64,
    #[clap(short, long)]
    output: PathBuf,
    paths: Vec<String>,
}

#[derive(Parser, Debug)]
struct ReduceArgs {
    /// A list of paths to Nuprl source code to load before reducing the expression.
    #[arg(short = 'l', long = "load")]
    paths: Vec<String>,
    /// A path to a Nuprl file whose namespace should be used as the current namespace when
    /// evaluating the expression.
    #[arg(short = 'f', long = "namespace-file")]
    namespace_file: Option<String>,
    #[arg(short = 's', long = "max-steps")]
    max_steps: Option<u64>,
    expression: Option<String>,
}

#[derive(Parser, Debug)]
struct ImportTermArgs {
    file: PathBuf,
}

fn main() -> ExitCode {
    let args = Args::parse();
    let mut source_id_gen = SourceIdGen::new();

    match args.subcommand {
        Subcommand::Check(args) => {
            let paths = args.paths
                .iter()
                .map(|path| match path.split_once('=') {
                    Some((lhs, rhs)) => (Some(lhs), AsRef::<Path>::as_ref(rhs)),
                    None => (None, AsRef::<Path>::as_ref(path)),
                })
                .collect::<Vec<_>>();

            let (stdlib, sources) = load_sources(&mut source_id_gen, &paths)
                .unwrap();

            check(stdlib.as_ref(), &sources);

            ExitCode::SUCCESS
        },

        Subcommand::Compile(args) => {
            let paths = args.paths
                .iter()
                .map(|path| match path.split_once('=') {
                    Some((lhs, rhs)) => (Some(lhs), AsRef::<Path>::as_ref(rhs)),
                    None => (None, AsRef::<Path>::as_ref(path)),
                })
                .collect::<Vec<_>>();

            let (stdlib, sources) = load_sources(&mut source_id_gen, &paths)
                .unwrap();

            compile(stdlib.as_ref(), &sources, &args.output, args.namespace)
        }

        Subcommand::Reduce(args) => {
            // FIXME: make a function for this
            let paths = args.paths
                .iter()
                .map(|path| match path.split_once('=') {
                    Some((lhs, rhs)) => (Some(lhs), AsRef::<Path>::as_ref(rhs)),
                    None => (None, AsRef::<Path>::as_ref(path)),
                })
                .collect::<Vec<_>>();

            let (stdlib, sources) = load_sources(&mut source_id_gen, &paths)
                .unwrap();

            let module = match args.namespace_file {
                Some(namespace_file) => {
                    sources
                        .iter()
                        .find(|source| source
                            .path()
                            .map(|path| path == AsRef::<Path>::as_ref(&namespace_file))
                            .unwrap_or(false))
                        .map(Source::module)
                        .unwrap()
                },
                None => CanonLibPath::ROOT,
            };

            let expr = match args.expression {
                Some(expr) => expr,
                None => {
                    let mut buf = String::new();
                    io::stdin().read_to_string(&mut buf).unwrap();
                    buf
                },
            };

            let expr = Source::new(
                source_id_gen.next_id(),
                SourceModule::Custom(module.to_owned()),
                // FIXME: maybe a separate expression kind?
                SourceKind::NuprlSrc,
                Cow::Owned(expr.into_bytes())
            ).unwrap();

            let expr = expr.text_source().unwrap();

            reduce(expr, stdlib.as_ref(), &sources, args.max_steps);

            ExitCode::SUCCESS
        },

        Subcommand::ImportTerm(args) => {
            let (stdlib, _) = load_sources::<&str, &str>(&mut source_id_gen, &[])
                .unwrap();

            let (res, _) = gen_lib_from_src(stdlib.as_ref(), &[], DEFAULT_NAMESPACE);
            let (resolver, _) = res.unwrap();

            let source = {
                let source = fs::read(&args.file)
                    .unwrap();

                Source::new(
                    source_id_gen.next_id(),
                    SourceModule::Custom(CanonLibPathBuf::root()),
                    SourceKind::NuprlSrc,
                    Cow::Owned(source)
                )
            }.unwrap();

            let source = source.text_source().unwrap();

            let term = source.text().parse::<Term>().unwrap();

            let (defs, thm, resolver) = term.to_main_parts("imported_proof".into(), resolver).unwrap();

            for def in &defs {
                let mut buf = String::new();
                def.format(&mut buf, resolver.ctx()).unwrap();
                println!("{}", buf);
            }
            
            println!();

            let mut buf = String::new();
            thm.format(&mut buf, resolver.ctx()).unwrap();
            println!("{}", buf);

            ExitCode::SUCCESS
        },
    }
}

fn load_sources<S, P>(id_gen: &mut SourceIdGen, paths: &[(Option<S>, P)])
    -> Result<(Option<Source>, Vec<Source>), SourceError>
where
    S: AsRef<str>,
    P: AsRef<Path>,
{
    let mut visited_paths = HashSet::new();
    let mut sources = Vec::new();
    
    let stdlib;

    #[cfg(feature = "standard_library")] {
        stdlib = Some(Source::new(
            id_gen.next_id(),
            SourceModule::Custom(CanonLibPathBuf::from_nodes(["std"])),
            SourceKind::NuprlLib,
            Cow::Borrowed(STD_ARCHIVE)
        )?);
    }

    #[cfg(not(feature = "standard_library"))] {
        stdlib = None;
    }

    for (module, module_path) in paths {
        let module = module
            .as_ref()
            .map(|module| CanonLibPathBuf::from_nodes([module]));

        let module_path = module_path.as_ref();

        for entry in WalkDir::new(module_path) {
            let entry = entry?;
            let entry_path = entry.path();

            if entry.file_type().is_file() && !visited_paths.contains(entry_path) {
                if let Some(source_kind) = SourceKind::from_path(entry_path) {
                    let text = fs::read(entry_path)?;
                    let id = id_gen.next_id();
                    let entry_path = entry.into_path();
    
                    sources.push(Source::new(
                        id,
                        SourceModule::FromPath {
                            base_module: module.as_deref(),
                            base_path: module_path,
                            full_path: entry_path.clone(),
                        },
                        source_kind,
                        Cow::Owned(text)
                    )?);

                    visited_paths.insert(entry_path);
                }
            }
        }
    }

    Ok((stdlib, sources))
}

fn reduce(
    expr: TextSource,
    stdlib: Option<&Source>,
    sources: &[Source],
    max_steps: Option<u64>
) {
    let (res, errs) = try_reduce(expr, stdlib, sources, max_steps);

    let json_out = JsonOutput {
        sources: SourceInfo::from_sources(sources),
        result: res,
        errors: errs.into_iter().map(Error::into_error_json).collect(),
    };

    println!("{}", serde_json::to_string(&json_out).unwrap());
}

fn try_reduce(
    expr: TextSource,
    stdlib: Option<&Source>,
    sources: &[Source],
    max_steps: Option<u64>
) -> (Option<ReduceResult>, Vec<Error>)
{
    let (res, mut errs) = gen_lib_from_src(stdlib, sources, DEFAULT_NAMESPACE);

    let Some((mut resolver, _)) = res else {
        return (None, errs)
    };

    let original_expr = match parse_expr(expr, resolver.std_objs()) {
        Ok(expr) => expr,
        Err(err) => {
            errs.insert(0, err.into());
            return (None, errs)
        },
    };

    let original_expr = match original_expr.resolve(
        expr.module(),
        resolver.lib().names(),
        resolver.std_objs(),
        &mut VarStack::new(),
        None
    ) {
        Ok(expr) => expr,
        Err(err) => {
            errs.insert(0, Error::NameResolve(err, None));
            return (None, errs)
        },
    };

    let original_expr = match original_expr.resolve(&mut resolver) {
        Ok(expr) => expr,
        Err(err) => {
            errs.insert(0, Error::Resolve(err, None));
            return (None, errs)
        },
    };

    let mut reduced_expr = original_expr.clone();
    let mut steps = 0u64;

    loop {
        match max_steps {
            Some(max_steps) if steps >= max_steps => break,
            _ => (),
        }

        match reduced_expr.reduce_step(resolver.ctx()) {
            Some(new_reduced_expr) => {
                reduced_expr = new_reduced_expr;
                steps = steps.saturating_add(1);
            },
            None => break,
        }
    }

    (Some(ReduceResult {
        original: original_expr.format_to_string(resolver.ctx(), &mut NameAssignments::new()),
        reduced: reduced_expr.format_to_string(resolver.ctx(), &mut NameAssignments::new()),
        steps
    }), errs)
}

fn check(stdlib: Option<&Source>, sources: &[Source]) {
    let (res, errs) = gen_lib_from_src(stdlib, sources, DEFAULT_NAMESPACE);

    let res = res.map(|(resolver, meta)| {
        let (lib, std_objs) = resolver.into_lib();
        (lib, std_objs, meta)
    });

    let json_out = JsonOutput {
        sources: SourceInfo::from_sources(sources),
        result: res.as_ref().map(|(lib, std_objs, meta)| {
            CheckResult { lib: Context { lib, std_objs }, meta }
        }),
        errors: errs.into_iter().map(Error::into_error_json).collect(),
    };

    println!("{}", serde_json::to_string(&json_out).unwrap());
}

fn compile(
    stdlib: Option<&Source>,
    sources: &[Source],
    output: &Path,
    namespace: u64
) -> ExitCode
{
    if namespace == DEFAULT_NAMESPACE {
        eprintln!("Cannot use default namespace when compiling a library");
        return ExitCode::FAILURE
    }
    
    let (res, errs) = gen_lib_from_src(stdlib, sources, namespace);

    match (res, &errs[..]) {
        (Some((res, _)), []) => {
            let (lib, _) = res.into_lib();

            let mut serializer = AllocSerializer::<4096>::default();
            serializer.serialize_value(&lib).unwrap();
            let serialized = serializer.into_serializer().into_inner();

            fs::write(output, &serialized).unwrap();

            ExitCode::SUCCESS
        },

        (_, errs) => {
            for err in errs {
                eprintln!("{}", err);
            }
            
            ExitCode::FAILURE
        },
    }
}

fn gen_lib_from_src(stdlib: Option<&Source>, sources: &[Source], namespace: u64)
    -> (Option<(Resolver, ObjectMetadataStore)>, Vec<Error>)
{
    let mut loaded_libs = Vec::new();
    let mut names = NameTree::empty_module();
    let mut statements = Vec::new();
    let mut std_objs = StdLibObjs::default();

    let mut obj_id_gen = ObjectIdGen::new(namespace);

    if let Some(stdlib) = stdlib {
        let SourceRepr::NuprlLib { bytes: stdlib_bytes } = stdlib.repr() else {
            panic!("std must be a library");
        };

        if let Err(err) = load_archived_lib(
            stdlib,
            stdlib_bytes,
            &mut names,
            &mut loaded_libs,
            namespace,
            |library| {
                std_objs = StdLibObjs::from_library(library);
            }
        ) {
            return (None, vec![err]);
        }
    }

    for source in sources {
        match source.repr() {
            SourceRepr::NuprlSrc { source_text: _, line_indices: _ } => {
                let source = source.text_source().unwrap();

                let source_statements = match parse_statements(source, &std_objs) {
                    Ok(statements) => statements,
                    Err(err) => return (None, vec![Error::Parse(err)]),
                };
        
                for statement in source_statements {
                    let (name, params, span) = match statement {
                        Statement::Def(ref def) => {
                            (def.name().clone(), def.params().len(), def.span())
                        },
                        
                        Statement::Thm(ref thm) => {
                            (thm.name().clone(), 0, thm.span())
                        },
                        
                        Statement::Exp(ref exp) => {
                            (exp.name().clone(), exp.params().len(), exp.span())
                        },
                        
                        Statement::Inf(ref inf) => {
                            (inf.name().clone(), inf.params().len(), inf.span())
                        },
                        
                        Statement::Imp(target_path, span) => {
                            let Some(import_name) = target_path.last_named() else {
                                return (None, vec![Error::NameResolve(
                                    NameResolveError::BadImportPath { path: target_path },
                                    Some(span)
                                )])
                            };
        
                            let (entry, _) = match names
                                .prepare_entry(source.module(), import_name.clone())
                            {
                                Ok(res) => res,
                                Err(err) => {
                                    return (None, vec![Error::NameTree(err, Some(span))])
                                },
                            };
        
                            entry.insert(NameTree::Alias {
                                ctx: source.module().to_owned(),
                                path: target_path,
                            });
        
                            continue
                        },

                        Statement::Intrinsic(ref name, span) => {
                            (name.clone(), 0, span)
                        },
                    };
        
                    let (entry, path) = match names
                        .prepare_entry(source.module(), name)
                    {
                        Ok(res) => res,
                        Err(err) => {
                            return (None, vec![Error::NameTree(err, Some(span))])
                        },
                    };
        
                    let id = obj_id_gen.next_id();
        
                    entry.insert(NameTree::Object { id, params });
        
                    statements.push((source, id, statement, path));
                }
            },
            
            SourceRepr::NuprlLib { bytes } => {
                if let Err(err) = load_archived_lib(
                    source,
                    bytes, &mut names,
                    &mut loaded_libs,
                    namespace,
                    |_| {}
                ) {
                    return (None, vec![err]);
                }
            },
        }
    }

    let mut unres_objects = BTreeMap::new();
    let mut meta_store = ObjectMetadataStore::new();

    for (source, id, statement, path) in statements {
        eprintln!("resolving {}", path);
        
        let obj_kind = match statement {
            Statement::Def(def) => {
                let (def, meta) = match def.resolve(source.module(), &names, &std_objs) {
                    Ok(res) => res,
                    Err(err) => {
                        return (None, vec![Error::NameResolve(err, Some(def.span()))])
                    },
                };

                meta_store.insert(id, meta);

                UnresolvedObjectKind::Def(def)
            },
            
            Statement::Thm(thm) => {
                let (thm, meta) = match thm.reify(source.module(), &names, &std_objs) {
                    Ok(res) => res,
                    Err(err) => {
                        return (None, vec![Error::NameResolve(err, Some(thm.span()))])
                    },
                };

                meta_store.insert(id, meta);
                
                UnresolvedObjectKind::Thm(thm)
            },
            
            Statement::Exp(exp) => {
                let (exp, meta) = match exp.resolve(source.module(), &names, &std_objs) {
                    Ok(res) => res,
                    Err(err) => {
                        return (None, vec![Error::NameResolve(err, Some(exp.span()))])
                    },
                };

                meta_store.insert(id, meta);

                UnresolvedObjectKind::Exp(exp)
            },
            
            Statement::Inf(inf) => {
                let inf = match inf.resolve(source.module(), &names, &std_objs) {
                    Ok(res) => res,
                    Err(err) => {
                        return (None, vec![Error::NameResolve(err, Some(inf.span()))])
                    },
                };

                UnresolvedObjectKind::Inf(inf)
            },

            Statement::Imp(_, _) => unreachable!(),

            Statement::Intrinsic(name, span) => {
                let Some(intrinsic) = InfIntrinsic::from_str(&name) else {
                    return (None, vec![Error::UnknownIntrinsic(name.as_ref().into(), span)])
                };

                UnresolvedObjectKind::InfIntrinsic(intrinsic)
            },
        };

        unres_objects.insert(id, UnresolvedObject::new(
            id,
            source.module().to_owned(),
            path,
            obj_kind
        ));
    }

    let mut resolver = Resolver::new(namespace, names, unres_objects, std_objs);

    for loaded_lib in loaded_libs {
        resolver.extend(loaded_lib);
    }

    let errs = resolver
        .resolve_all()
        .into_iter()
        .map(|(err, id)| {
            let span = meta_store.get(id).map(ObjectMetadata::span);
            Error::Resolve(err, span)
        })
        .collect::<Vec<_>>();

    (Some((resolver, meta_store)), errs)
}

fn load_archived_lib<F>(
    source: &Source,
    lib_bytes: &[u8],
    names: &mut NameTree,
    loaded_libs: &mut Vec<Library>,
    reserved_namespace: u64,
    pre_reroot: F
) -> Result<(), Error>
where
    F: FnOnce(&Library),
{
    let lib_bytes = {
        let mut buf = AlignedVec::new();
        buf.extend_from_slice(&lib_bytes);
        buf
    };

    // FIXME: validation
    let archived_lib = unsafe { rkyv::archived_root::<Library>(&lib_bytes) };

    let mut deserialised_lib: Library = archived_lib
        .deserialize(&mut SharedDeserializeMap::new())
        .unwrap();
    
    if deserialised_lib.namespace() == reserved_namespace
        || loaded_libs
            .iter()
            .any(|lib: &Library| deserialised_lib.namespace() == lib.namespace())
    {
        return Err(Error::DuplicateNamespace(deserialised_lib.namespace()));
    }

    pre_reroot(&deserialised_lib);

    deserialised_lib.reroot(source.module());

    eprintln!("loaded {} containing {} objects", source.module(), deserialised_lib.num_objects());

    let (entry, _) = match names.prepare_entry_last_segment(source.module()) {
        Ok(res) => res,
        Err(err) => {
            return Err(Error::NameTree(err, None));
        },
    };

    entry.insert(deserialised_lib.names().clone());

    loaded_libs.push(deserialised_lib);

    Ok(())
}

#[cfg(test)]
fn load_stdlib() -> Resolver {
    let (stdlib, _) = load_sources::<&str, &str>(&mut SourceIdGen::new(), &[])
        .unwrap();

    let (res, _) = gen_lib_from_src(stdlib.as_ref(), &[], DEFAULT_NAMESPACE);
    let (resolver, _) = res.unwrap();
    resolver
}

#[derive(Debug)]
enum Error {
    DuplicateNamespace(u64),
    Parse(ParseError),
    NameTree(NameTreeError, Option<Span>),
    NameResolve(NameResolveError, Option<Span>),
    Resolve(ResolveError, Option<Span>),
    UnknownIntrinsic(Box<str>, Span),
}

impl Error {
    fn message(&self) -> String {
        match self {
            Self::DuplicateNamespace(namespace) => {
                format!("Duplicate namespace: {}", namespace)
            },
            Self::Parse(err) => {
                format!("Parse error: {}", err)
            },
            Self::NameTree(err, _) => {
                format!("Name error: {}", err)
            },
            Self::NameResolve(err, _) => {
                format!("Resolve error: {}", err)
            },
            Self::Resolve(err, _) => {
                format!("Resolve error: {}", err)
            },
            Self::UnknownIntrinsic(name, _) => {
                format!("Unknown intrinsic `{}`", name)
            },
        }
    }

    fn span(&self) -> Option<Span> {
        match self {
            Self::DuplicateNamespace(_) => None,
            Self::Parse(err) => Some(err.span),
            Self::NameTree(_, span) => *span,
            Self::NameResolve(_, span) => *span,
            Self::Resolve(_, span) => *span,
            Self::UnknownIntrinsic(_, span) => Some(*span),
        }
    }
    
    fn into_error_json(self) -> ErrorJson {
        ErrorJson {
            message: self.message(),
            span: self.span(),
        }
    }
}

impl From<ParseError> for Error {
    fn from(err: ParseError) -> Self {
        Self::Parse(err)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.message())?;
        if let Some(span) = self.span() {
            write!(
                f,
                " at line {}:{} \u{2013} {}:{}",
                span.visual().start().line(),
                span.visual().start().col(),
                span.visual().end().line(),
                span.visual().end().col()
            )?;
        }
        Ok(())
    }
}

#[derive(Debug, Serialize)]
struct JsonOutput<T> {
    sources: BTreeMap<SourceId, SourceInfo>,
    result: T,
    errors: Vec<ErrorJson>,
}

#[derive(Debug, Serialize)]
struct ErrorJson {
    message: String,
    span: Option<Span>,
}

#[derive(Debug, Serialize)]
struct ReduceResult {
    original: String,
    reduced: String,
    steps: u64,
}

#[derive(Serialize, Debug)]
struct CheckResult<'a> {
    lib: Context<'a>,
    meta: &'a ObjectMetadataStore,
}

// FIXME: output this regardless of whether there was an error or not
#[derive(Serialize, Debug)]
struct SourceInfo {
    path: Option<PathBuf>,
    module: CanonLibPathBuf,
    kind: SourceKind,
}

impl SourceInfo {
    fn from_sources(sources: &[Source]) -> BTreeMap<SourceId, Self> {
        sources
            .iter()
            .map(|source| (source.id(), Self {
                path: source.path().map(ToOwned::to_owned),
                module: source.module().to_owned(),
                kind: source.kind(),
            }))
            .collect()
    }
}
