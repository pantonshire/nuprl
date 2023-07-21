use std::{rc::Rc, error, fmt, cmp::Ordering};

use crate::{
    path::{path::{LibPathBuf, CanonLibPath, CanonLibPathBuf}, name_tree::{NameTree, NameTreeError}},
    unif_var::{UnifVarKind, UnifVarIndicesRef},
    phase3_proofck::{expr::{ReductionSteps, RcExpr, Expr, SecondOrderMappingBuf, Var, Bound, UnifVar, Subst, Tag, ObjExpr, FormatTok}, library::Context},
    object_id::ObjectId, var_stack::{VarStack, VarStackEntry},
    utils::{ReborrowMut, InliningBuf}, stdlib::StdLibObjs,
};

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum NamedExpr {
    Var(LibPathBuf),
    SecondOrderVar {
        name: LibPathBuf,
        mapping: Box<[LibPathBuf]>,
    },
    Tok(Rc<str>),
    Nat(u64),
    Bound {
        var: Rc<str>,
        body: Box<Self>,
    },
    UnifVar {
        var: Rc<str>,
        kind: UnifVarKind,
    },
    Subst {
        bound: Box<Self>,
        args: Box<[Self]>,
    },
    Tag {
        steps: ReductionSteps,
        body: Box<Self>,
    },
    Jux {
        lhs: Box<Self>,
        rhs: Box<Self>,
    },
    Obj {
        id: ObjectId,
        args: Box<[Self]>,
    },
}

impl NamedExpr {
    pub fn boxed(self) -> Box<Self> {
        Box::new(self)
    }

    pub fn resolve(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs,
        vars: &mut VarStack,
        unif_vars: Option<UnifVarIndicesRef>
    ) -> Result<RcExpr, NameResolveError>
    {
        match self.resolve_partial(ctx, objects, std_objs, vars, unif_vars)? {
            PartialResolveOk::Expr(expr) => Ok(expr),
            PartialResolveOk::Incomplete { id: _, path, params, args } => {
                Err(NameResolveError::InsufficientArgs {
                    path,
                    params,
                    args: args.len(),
                })
            },
        }
    }

    fn resolve_partial(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs,
        vars: &mut VarStack,
        mut unif_vars: Option<UnifVarIndicesRef>
    ) -> Result<PartialResolveOk, NameResolveError>
    {
        match self {
            Self::Var(var) => {
                let var_unitary = var.as_unitary();
                match var_unitary.and_then(|var| vars.de_bruijn_index_of(&var)) {
                    Some((index, 0)) => {
                        Ok(PartialResolveOk::Expr(Var::first_order(index).expr().rc()))
                    },
                    Some((_, n)) => {
                        Err(NameResolveError::WrongVarArity {
                            name: var.clone(),
                            expected_arity: 0,
                            actual_arity: n,
                        })
                    },
                    None => match objects.get_obj(ctx, var) {
                        Ok((id, path, params)) => match params {
                            0 => {
                                Ok(PartialResolveOk::Expr(ObjExpr::new(
                                    id,
                                    InliningBuf::new()
                                ).expr().rc()))
                            },
                            params => {
                                Ok(PartialResolveOk::Incomplete {
                                    id,
                                    path,
                                    params,
                                    args: Vec::new(),
                                })
                            },
                        },
                        Err(_) => match var_unitary {
                            Some(var_unitary) => {
                                Ok(PartialResolveOk::Expr(Expr::Free(var_unitary.clone()).rc()))
                            },
                            None => {
                                Err(NameResolveError::UnknownName { name: var.clone() })
                            },
                        },
                    },
                }
            },

            Self::SecondOrderVar { name, mapping } => {
                match name
                    .as_unitary()
                    .and_then(|name| vars.de_bruijn_index_of(&name))
                {
                    Some((index, n)) if n == mapping.len() => {
                        let mapping = mapping
                            .iter()
                            .map(|arg_name| {
                                match arg_name
                                    .as_unitary()
                                    .and_then(|arg_name| vars.de_bruijn_index_of(arg_name))
                                {
                                    Some((index, 0)) => Ok(index),
                                    Some((_, n)) => Err(NameResolveError::WrongVarArity {
                                        name: arg_name.clone(),
                                        expected_arity: 0,
                                        actual_arity: n,
                                    }),
                                    None => Err(NameResolveError::UnknownSecondOrderArg {
                                        second_order_name: name.clone(),
                                        arg_name: arg_name.clone(),
                                    }),
                                }
                            })
                            .collect::<Result<SecondOrderMappingBuf, _>>()?;
    
                        Ok(PartialResolveOk::Expr(Var::new(index, mapping).expr().rc()))
                    },
                    Some((_, n)) => Err(NameResolveError::WrongVarArity {
                        name: name.clone(),
                        expected_arity: mapping.len(),
                        actual_arity: n,
                    }),
                    None => Err(NameResolveError::UnknownSecondOrderVar {
                        name: name.clone(),
                    }),
                }
            },
            
            Self::Tok(tok) => {
                Ok(PartialResolveOk::Expr(Expr::Tok(tok.clone()).rc()))
            },
            
            Self::Nat(nat) => {
                Ok(PartialResolveOk::Expr(Expr::Nat(*nat).rc()))
            },
            
            Self::Bound { var, body } => {
                let body = vars.with(VarStackEntry::named(var.clone(), 0), |vars| {
                    body.resolve(ctx, objects, std_objs, vars, unif_vars)
                })?;
                Ok(PartialResolveOk::Expr(Bound::new(var.clone(), body).expr().rc()))
            },
            
            Self::UnifVar { var, kind } => {
                match unif_vars.reborrow_mut() {
                    Some(UnifVarIndicesRef::Mutable(unif_vars)) => {
                        let index = unif_vars.get_or_generate(var.clone());
                        Ok(PartialResolveOk::Expr(UnifVar::new(
                            var.clone(),
                            index,
                            *kind
                        ).expr().rc()))
                    },
                    Some(UnifVarIndicesRef::Immutable(unif_vars)) => {
                        match unif_vars.get(var) {
                            Some(index) => {
                                Ok(PartialResolveOk::Expr(UnifVar::new(
                                    var.clone(),
                                    index,
                                    *kind
                                ).expr().rc()))
                            },
                            None => Err(NameResolveError::UnknownUnifVar { name: var.clone() }),
                        }
                    },
                    None => Err(NameResolveError::UnexpectedUnifVar { name: var.clone() }),
                }
            },
            
            Self::Subst { bound, args } => {
                let num_args = args.len();

                let args = args
                    .iter()
                    .map(|arg| arg.resolve(ctx, objects, std_objs, vars, unif_vars.reborrow_mut()))
                    .collect::<Result<_, _>>()?;
                
                for _ in 0..num_args {
                    vars.push(VarStackEntry::unnamed(0));
                }
                
                let bound = bound.resolve(ctx, objects, std_objs, vars, unif_vars)?;

                for _ in 0..num_args {
                    vars.pop();
                }

                Ok(PartialResolveOk::Expr(Subst::new(bound, args).expr().rc()))
            },
            
            Self::Tag { steps, body } => {
                let body = body.resolve(ctx, objects, std_objs, vars, unif_vars)?;
                Ok(PartialResolveOk::Expr(Tag::new(*steps, body).expr().rc()))
            },
            
            Self::Jux { lhs, rhs } => {
                let lhs = lhs.resolve_partial(ctx, objects, std_objs, vars, unif_vars.reborrow_mut())?;
                let rhs = rhs.resolve(ctx, objects, std_objs, vars, unif_vars)?;

                match lhs {
                    PartialResolveOk::Expr(lhs) => {
                        let app_id = std_objs.app.unwrap();

                        Ok(PartialResolveOk::Expr(ObjExpr::new(
                            app_id,
                            [lhs, rhs].into_iter().collect()
                        ).expr().rc()))
                    },

                    PartialResolveOk::Incomplete { id, path, params, mut args } => {
                        args.push(rhs);
                        
                        match args.len().cmp(&params) {
                            Ordering::Less => {
                                Ok(PartialResolveOk::Incomplete { id, path, params, args })
                            },
                            Ordering::Equal => {
                                Ok(PartialResolveOk::Expr(ObjExpr::new(
                                    id,
                                    args.into_iter().collect()
                                ).expr().rc()))
                            },
                            Ordering::Greater => {
                                unreachable!()
                            },
                        }
                    },
                }
            },
            
            Self::Obj { id, args } => {
                let args = args
                    .iter()
                    .map(|arg| arg.resolve(ctx, objects, std_objs, vars, unif_vars.reborrow_mut()))
                    .collect::<Result<_, _>>()?;

                Ok(PartialResolveOk::Expr(ObjExpr::new(*id, args).expr().rc()))
            },
        }
    }

    pub fn format<W: fmt::Write>(
        &self,
        f: &mut W,
        ctx: Context
    ) -> fmt::Result
    {
        match self {
            Self::Var(var) => {
                write!(f, "{}", var)
            },
            Self::SecondOrderVar { name, mapping } => {
                write!(f, "{}[", name)?;
                let mut write_semicolon = false;
                for var in &mapping[..] {
                    if write_semicolon {
                        write!(f, "; ")?;
                    } else {
                        write_semicolon = true;
                    }
                    write!(f, "{}", var)?;
                }
                write!(f, "]")?;
                Ok(())
            },
            Self::Tok(tok) => write!(f, "\"{}\"", FormatTok(tok)),
            Self::Nat(n) => write!(f, "{}", n),
            Self::Bound{ var, body } => {
                write!(f, "{}. ", var)?;
                body.format(f, ctx)?;
                Ok(())
            },
            Self::UnifVar { var, kind } => {
                write!(f, "${}", var)?;
                match kind.str_name() {
                    Some(kind) => write!(f, ":{}", kind),
                    None => Ok(()),
                }
            },
            Self::Subst { bound, args } => {
                write!(f, "[")?;
                let mut args = args.iter();
                if let Some(arg) = args.next() {
                    arg.format(f, ctx)?;
                    for arg in args {
                        write!(f, ", ")?;
                        arg.format(f, ctx)?;
                    }
                }
                write!(f, "]")?;
                bound.format_paren(f, ctx, Precedence::Contained)?;
                Ok(())
            },
            Self::Obj { id, args } => {
                let res = match (*id, args.as_ref()) {
                    (id, [body]) if Some(id) == ctx.std_objs.neg => {
                        write!(f, "-")?;
                        body.format_paren(f, ctx, Precedence::Neg)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.add => {
                        lhs.format_paren(f, ctx, Precedence::Mul)?;
                        write!(f, " + ")?;
                        rhs.format_paren(f, ctx, Precedence::Mul)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.mul => {
                        lhs.format_paren(f, ctx, Precedence::Neg)?;
                        write!(f, " * ")?;
                        rhs.format_paren(f, ctx, Precedence::Neg)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.div => {
                        lhs.format_paren(f, ctx, Precedence::Neg)?;
                        write!(f, " div ")?;
                        rhs.format_paren(f, ctx, Precedence::Neg)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.rem => {
                        lhs.format_paren(f, ctx, Precedence::Neg)?;
                        write!(f, " rem ")?;
                        rhs.format_paren(f, ctx, Precedence::Neg)?;
                        Some(Ok(()))
                    },
                    (id, [body]) if Some(id) == ctx.std_objs.lambda => {
                        match body {
                            Self::Bound { var, body } => {
                                write!(f, "\\{}. ", var)?;
                                body.format(f, ctx)?;
                                Some(Ok(()))
                            },
                            _ => None,
                        }
                    },
                    (id, [func, arg]) if Some(id) == ctx.std_objs.app => {
                        func.format_paren(f, ctx, Precedence::App)?;
                        write!(f, " ")?;
                        arg.format_paren(f, ctx, Precedence::Contained)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.pair => {
                        write!(f, "<")?;
                        lhs.format(f, ctx)?;
                        write!(f, ", ")?;
                        rhs.format(f, ctx)?;
                        write!(f, ">")?;
                        Some(Ok(()))
                    },
                    (id, [val, body]) if Some(id) == ctx.std_objs.spread => {
                        match body {
                            Self::Bound { var: lhs_var, body: body_outer } => match body_outer.as_ref() {
                                Self::Bound { var: rhs_var, body: body_inner } => {
                                    write!(f, "let <{}, {}> = ", lhs_var, rhs_var)?;
                                    val.format(f, ctx)?;
                                    write!(f, " in ")?;
                                    body_inner.format(f, ctx)?;
                                    Some(Ok(()))
                                },
                                _ => None,
                            },
                            _ => None,
                        }
                    },
                    (id, [val, l_case, r_case]) if Some(id) == ctx.std_objs.decide => {
                        match (l_case, r_case) {
                            (Self::Bound { var: inl_var, body: l_case }, Self::Bound { var: inr_var, body: r_case }) => {
                                write!(f, "case ")?;
                                val.format(f, ctx)?;
                                write!(f, " of inl({}) => ", inl_var)?;
                                l_case.format(f, ctx)?;
                                write!(f, ", inr({}) => ", inr_var)?;
                                r_case.format(f, ctx)?;
                                Some(Ok(()))
                            },
                            _ => None,
                        }
                    },
                    (id, [val, body]) if Some(id) == ctx.std_objs.cbv => {
                        match body {
                            Self::Bound { var, body } => {
                                write!(f, "let {} := ", var)?;
                                val.format(f, ctx)?;
                                write!(f, " in ")?;
                                body.format(f, ctx)?;
                                Some(Ok(()))
                            },
                            _ => None,
                        }
                    },
                    (id, [lhs, rhs, l_case, r_case]) if Some(id) == ctx.std_objs.compare_eq => {
                        write!(f, "if ")?;
                        lhs.format_paren(f, ctx, Precedence::Add)?;
                        write!(f, " = ")?;
                        rhs.format_paren(f, ctx, Precedence::Add)?;
                        write!(f, " then ")?;
                        l_case.format(f, ctx)?;
                        write!(f, " else ")?;
                        r_case.format(f, ctx)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs, l_case, r_case]) if Some(id) == ctx.std_objs.compare_lt => {
                        write!(f, "if ")?;
                        lhs.format_paren(f, ctx, Precedence::Add)?;
                        write!(f, " < ")?;
                        rhs.format_paren(f, ctx, Precedence::Add)?;
                        write!(f, " then ")?;
                        l_case.format(f, ctx)?;
                        write!(f, " else ")?;
                        r_case.format(f, ctx)?;
                        Some(Ok(()))
                    },
                    (id, [domain, codomain]) if Some(id) == ctx.std_objs.func => {
                        match codomain {
                            Self::Bound { var, body: codomain } => {
                                write!(f, "{}: ", var)?;
                                domain.format_paren(f, ctx, Precedence::SumTy)?;
                                write!(f, " -> ")?;
                                codomain.format_paren(f, ctx, Precedence::FnTy)?;
                                Some(Ok(()))
                            },
                            _ => {
                                domain.format_paren(f, ctx, Precedence::SumTy)?;
                                write!(f, " -> ")?;
                                codomain.format_paren(f, ctx, Precedence::FnTy)?;
                                Some(Ok(()))
                            },
                        }
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.sum => {
                        lhs.format_paren(f, ctx, Precedence::ProdTy)?;
                        write!(f, " | ")?;
                        rhs.format_paren(f, ctx, Precedence::SumTy)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.prod => {
                        match rhs {
                            Self::Bound { var, body: rhs } => {
                                write!(f, "{}: ", var)?;
                                lhs.format_paren(f, ctx, Precedence::LtTy)?;
                                write!(f, " # ")?;
                                rhs.format_paren(f, ctx, Precedence::ProdTy)?;
                                Some(Ok(()))
                            },
                            _ => {
                                lhs.format_paren(f, ctx, Precedence::LtTy)?;
                                write!(f, " # ")?;
                                rhs.format_paren(f, ctx, Precedence::ProdTy)?;
                                Some(Ok(()))
                            },
                        }
                    },
                    (id, [ty, lhs, rhs]) if Some(id) == ctx.std_objs.eq => {
                        lhs.format_paren(f, ctx, Precedence::FnTy)?;
                        write!(f, " = ")?;
                        rhs.format_paren(f, ctx, Precedence::FnTy)?;
                        write!(f, " in ")?;
                        ty.format_paren(f, ctx, Precedence::EqTy)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.isect => {
                        match rhs {
                            Self::Bound { var, body: rhs } => {
                                write!(f, "{}: ", var)?;
                                lhs.format_paren(f, ctx, Precedence::Add)?;
                                write!(f, " & ")?;
                                rhs.format_paren(f, ctx, Precedence::IsectTy)?;
                                Some(Ok(()))
                            },
                            _ => None,
                        }
                    },
                    _ => None,
                };

                match res {
                    Some(res) => res,
                    None => {
                        match ctx.lib.get(*id) {
                            Some(lib_obj) => {
                                write!(f, "{}", lib_obj.path())?;
                            },
                            None => {
                                write!(f, "obj!{}", id.inner_val())?;
                            },
                        }
                        for arg in args.iter() {
                            write!(f, " ")?;
                            arg.format_paren(f, ctx, Precedence::Contained)?;
                        }
                        Ok(())
                    },
                }
            },
            Self::Tag { steps, body } => {
                match steps {
                    ReductionSteps::Finite(n) => write!(f, "[[{}; ", n),
                    ReductionSteps::Infinite => write!(f, "[[*; "),
                }?;
                body.format(f, ctx)?;
                write!(f, "]]")
            },
            Self::Jux { lhs, rhs } => {
                lhs.format_paren(f, ctx, Precedence::App)?;
                write!(f, " ")?;
                rhs.format_paren(f, ctx, Precedence::Contained)
            },
        }
    }

    fn format_paren<W: fmt::Write>(
        &self,
        f: &mut W,
        ctx: Context,
        min_prec: Precedence,
    ) -> fmt::Result
    {
        if self.precedence(ctx) < min_prec {
            write!(f, "(")?;
            self.format(f, ctx)?;
            write!(f, ")")
        } else {
            self.format(f, ctx)
        }
    }

    fn precedence(&self, ctx: Context) -> Precedence {
        match self {
            Self::Var(_) => Precedence::Contained,
            Self::SecondOrderVar { name: _, mapping: _ } => Precedence::Contained,
            Self::Tok(_) => Precedence::Contained,
            Self::Nat(_) => Precedence::Contained,
            Self::Bound { var: _, body: _ } => Precedence::Loose,
            Self::UnifVar { var: _, kind: _ } => Precedence::Contained,
            Self::Subst { bound: _, args: _ } => Precedence::Subst,
            Self::Obj { id, args } => {
                match *id {
                    id if Some(id) == ctx.std_objs.neg => Precedence::Neg,
                    id if Some(id) == ctx.std_objs.add => Precedence::Add,
                    id if Some(id) == ctx.std_objs.mul => Precedence::Mul,
                    id if Some(id) == ctx.std_objs.div => Precedence::Mul,
                    id if Some(id) == ctx.std_objs.rem => Precedence::Mul,
                    id if Some(id) == ctx.std_objs.lambda => Precedence::Loose,
                    id if Some(id) == ctx.std_objs.app => Precedence::App,
                    id if Some(id) == ctx.std_objs.pair => Precedence::Contained,
                    id if Some(id) == ctx.std_objs.spread => Precedence::Loose,
                    id if Some(id) == ctx.std_objs.decide => Precedence::Loose,
                    id if Some(id) == ctx.std_objs.cbv => Precedence::Loose,
                    id if Some(id) == ctx.std_objs.compare_eq => Precedence::Loose,
                    id if Some(id) == ctx.std_objs.compare_lt => Precedence::Loose,
                    id if Some(id) == ctx.std_objs.func => Precedence::FnTy,
                    id if Some(id) == ctx.std_objs.sum => Precedence::SumTy,
                    id if Some(id) == ctx.std_objs.prod => Precedence::ProdTy,
                    id if Some(id) == ctx.std_objs.eq => Precedence::EqTy,
                    id if Some(id) == ctx.std_objs.isect => Precedence::IsectTy,
                    _ => {
                        if args.is_empty() {
                            Precedence::Contained
                        } else {
                            Precedence::App
                        }
                    }
                }
            },
            Self::Tag { steps: _, body: _ } => Precedence::Contained,
            Self::Jux { lhs: _, rhs: _ } => Precedence::App,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum Precedence {
    Loose,
    IsectTy,
    EqTy,
    FnTy,
    SumTy,
    ProdTy,
    LtTy,
    Add,
    Mul,
    Neg,
    App,
    Subst,
    Contained,
}

enum PartialResolveOk {
    Expr(RcExpr),
    Incomplete {
        id: ObjectId,
        path: CanonLibPathBuf,
        params: usize,
        args: Vec<RcExpr>,
    },
}

#[derive(Debug)]
pub enum NameResolveError {
    WrongVarArity {
        name: LibPathBuf,
        expected_arity: usize,
        actual_arity: usize,
    },
    UnknownName {
        name: LibPathBuf,
    },
    UnknownSecondOrderVar {
        name: LibPathBuf,
    },
    UnknownSecondOrderArg {
        second_order_name: LibPathBuf,
        arg_name: LibPathBuf,
    },
    UnexpectedUnifVar {
        name: Rc<str>,
    },
    UnknownUnifVar {
        name: Rc<str>,
    },
    DuplicateUnifVar {
        name: Rc<str>,
    },
    BadImportPath {
        path: LibPathBuf,
    },
    InsufficientArgs {
        path: CanonLibPathBuf,
        params: usize,
        args: usize,
    },
    NameTree {
        err: NameTreeError,
    },
}

impl fmt::Display for NameResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongVarArity { name: var, expected_arity, actual_arity } => {
                write!(f, "expected `{}` to be a ", var)?;
                match expected_arity {
                    0 => write!(f, "a first-order variable")?,
                    n => write!(f, "an arity {} second-order variable", n)?,
                }
                write!(f, ", but found ")?;
                match actual_arity {
                    0 => write!(f, "a first-order variable")?,
                    n => write!(f, "an arity {} second-order variable", n)?,
                }
                Ok(())
            },
            Self::UnknownName { name } => {
                write!(f, "unknown name `{}`", name)
            },
            Self::UnknownSecondOrderVar { name } => {
                write!(f, "unknown second-order variable `{}`", name)
            },
            Self::UnknownSecondOrderArg { second_order_name, arg_name } => {
                write!(
                    f,
                    "unknown argument `{}` to second-order variable `{}`",
                    arg_name,
                    second_order_name
                )
            },
            Self::UnexpectedUnifVar { name } => {
                write!(f, "unification placeholder `${}` not allowed in this context", name)
            },
            Self::UnknownUnifVar { name } => {
                write!(f, "unknown unification placeholder `${}`", name)
            },
            Self::DuplicateUnifVar { name } => {
                write!(f, "found a duplicate unification placeholder `${}` where a fresh one was expected", name)
            },
            Self::BadImportPath { path } => {
                write!(f, "bad import path: `{}`", path)
            },
            Self::InsufficientArgs { path, params, args } => {
                write!(f, "`{}` expects {} arguments, but {} were found", path, params, args)
            },
            Self::NameTree { err } => {
                write!(f, "{}", err)
            }
        }
    }
}

impl error::Error for NameResolveError {}

#[cfg(test)]
mod tests {
    use crate::{load_stdlib, phase2_nameres::expr::NamedExpr, path::path::{CanonLibPath, LibPathBuf}, var_stack::VarStack, phase3_proofck::expr::{Expr, Bound, Var, ObjExpr}, de_bruijn::DeBruijnIndex};

    #[test]
    fn test_resolve() {
        let stdlib = load_stdlib();

        assert_eq!(
            NamedExpr::Nat(1)
                .resolve(
                    CanonLibPath::ROOT,
                    stdlib.lib().names(),
                    stdlib.std_objs(),
                    &mut VarStack::new(),
                    None
                ).unwrap(),
            Expr::Nat(1).rc()
        );

        assert_eq!(
            NamedExpr::Bound {
                var: "x".into(),
                body: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed()
            }.resolve(
                CanonLibPath::ROOT,
                stdlib.lib().names(),
                stdlib.std_objs(),
                &mut VarStack::new(),
                None
            ).unwrap(),
            Bound::new(
                "foobaa".into(),
                Var::first_order(DeBruijnIndex::new(0)).expr().rc()
            ).expr().rc()
        );

        assert_eq!(
            NamedExpr::Bound {
                var: "x".into(),
                body: NamedExpr::Bound {
                    var: "y".into(),
                    body: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed()
                }.boxed()
            }.resolve(
                CanonLibPath::ROOT,
                stdlib.lib().names(),
                stdlib.std_objs(),
                &mut VarStack::new(),
                None
            ).unwrap(),
            Bound::new(
                "foobaa".into(),
                Bound::new(
                    "foobaa".into(),
                    Var::first_order(DeBruijnIndex::new(1)).expr().rc()
                ).expr().rc()
            ).expr().rc()
        );

        assert_eq!(
            NamedExpr::Bound {
                var: "x".into(),
                body: NamedExpr::Bound {
                    var: "y".into(),
                    body: NamedExpr::Var(LibPathBuf::new_unitary("y".into())).boxed()
                }.boxed()
            }.resolve(
                CanonLibPath::ROOT,
                stdlib.lib().names(),
                stdlib.std_objs(),
                &mut VarStack::new(),
                None
            ).unwrap(),
            Bound::new(
                "foobaa".into(),
                Bound::new(
                    "foobaa".into(),
                    Var::first_order(DeBruijnIndex::new(0)).expr().rc()
                ).expr().rc()
            ).expr().rc()
        );

        assert_eq!(
            NamedExpr::Bound {
                var: "x".into(),
                body: NamedExpr::Bound {
                    var: "x".into(),
                    body: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed()
                }.boxed()
            }.resolve(
                CanonLibPath::ROOT,
                stdlib.lib().names(),
                stdlib.std_objs(),
                &mut VarStack::new(),
                None
            ).unwrap(),
            Bound::new(
                "foobaa".into(),
                Bound::new(
                    "foobaa".into(),
                    Var::first_order(DeBruijnIndex::new(0)).expr().rc()
                ).expr().rc()
            ).expr().rc()
        );

        assert_eq!(
            NamedExpr::Jux {
                lhs: NamedExpr::Bound {
                    var: "x".into(),
                    body: NamedExpr::Var(LibPathBuf::new_unitary("x".into())).boxed()
                }.boxed(),
                rhs: NamedExpr::Tok("a".into()).boxed(),
            }.resolve(
                CanonLibPath::ROOT,
                stdlib.lib().names(),
                stdlib.std_objs(),
                &mut VarStack::new(),
                None
            ).unwrap(),
            ObjExpr::new(stdlib.std_objs().app.unwrap(), [
                Bound::new(
                    "foobaa".into(),
                    Var::first_order(DeBruijnIndex::new(0)).expr().rc()
                ).expr().rc(),
                Expr::Tok("a".into()).rc()
            ].into_iter().collect()).expr().rc()
        )
    }
}
