use std::{collections::{BTreeMap, btree_map, BTreeSet}, rc::Rc, fmt, error};

use rkyv::{Archive, Serialize, Deserialize};

use crate::{object_id::ObjectId, path::{path::{CanonLibPath, CanonLibPathBuf}, name_tree::NameTree}, utils::IntoResultOk, stdlib::StdLibObjs};

use super::{
    object::{Object, ObjectKind, UnresolvedObject, UnresolvedObjectKind},
    proof::DisplayTheorem,
};

pub struct Resolver {
    std_objs: StdLibObjs,
    unres_objects: BTreeMap<ObjectId, UnresolvedObject>,
    res_lib: Library,
    visited: BTreeSet<ObjectId>,
}

impl Resolver {
    pub fn new(
        namespace: u64,
        names: NameTree,
        objects: BTreeMap<ObjectId, UnresolvedObject>,
        std_objs: StdLibObjs,
    ) -> Self
    {
        Self {
            unres_objects: objects,
            res_lib: Library::new(namespace, names),
            visited: BTreeSet::new(),
            std_objs,
        }
    }

    pub fn extend(&mut self, other: Library) {
        self.res_lib.extend(other)
    }

    pub fn resolve(&mut self, id: ObjectId) -> Result<Rc<Object>, ResolveError> {
        if let Some(object) = self.res_lib.get(id) {
            return Ok(object.clone());
        }

        let Some(object) = self.unres_objects.remove(&id) else {
            return Err(ResolveError::UnknownObjectId(id))
        };

        self.resolve_obj(object)
    }

    fn resolve_obj(&mut self, object: UnresolvedObject) -> Result<Rc<Object>, ResolveError> {
        let id = object.id();

        self.visited.insert(id);

        match object.kind() {
            UnresolvedObjectKind::Def(def) => {
                let def = def.resolve(self)?;
                let object = Object::def(id, object.path().to_owned(), def);
                self.res_lib.insert(Rc::new(object)).ok()
            },

            UnresolvedObjectKind::Thm(thm) => {
                let thm = thm.resolve_and_check(self)?;
                let object = Object::thm(id, object.path().to_owned(), thm);
                self.res_lib.insert(Rc::new(object)).ok()
            },
            
            UnresolvedObjectKind::Exp(exprkind) => 'resolve: {
                // Put the exprkind without any of its reductions into the library so that its
                // beta reductions can refer to it when resolving.
                self.res_lib.insert(Rc::new(Object::exp(
                    id,
                    object.path().to_owned(),
                    exprkind.clone()
                )));

                let mut reductions = Vec::new();
                for reduction in exprkind.reductions() {
                    let reduction = match reduction.resolve(id, self) {
                        Ok(reduction) => reduction,
                        Err(err) => break 'resolve Err(err),
                    };
                    reductions.push(reduction);
                }

                let exprkind_obj = self.res_lib.get_mut(id).unwrap();
                let exprkind_obj_mut = Rc::get_mut(exprkind_obj).unwrap();
                let ObjectKind::Exp(exprkind) = exprkind_obj_mut.kind_mut() else {
                    unreachable!()
                };

                exprkind.set_reductions(reductions.into());

                Ok(exprkind_obj.clone())
            },

            UnresolvedObjectKind::Inf(inf) => {
                let inf = inf.resolve(self)?;
                let object = Object::inf(id, object.path().to_owned(), inf);
                self.res_lib.insert(Rc::new(object)).ok()
            },

            UnresolvedObjectKind::InfIntrinsic(intrinsic) => {
                let object = Object::new(
                    id,
                    object.path().to_owned(),
                    ObjectKind::InfIntrinsic(*intrinsic)
                );
                self.res_lib.insert(Rc::new(object)).ok()
            },
        }
    }

    pub fn resolve_all(&mut self) -> Vec<(ResolveError, ObjectId)> {
        let mut errors = Vec::new();

        while let Some((_, unresolved)) = self.unres_objects.pop_first() {
            let id = unresolved.id();
            if let Err(err) = self.resolve_obj(unresolved) {
                errors.push((err, id));
            }
        }

        errors
    }

    pub fn lib(&self) -> &Library {
        &self.res_lib
    }

    pub fn std_objs(&self) -> &StdLibObjs {
        &self.std_objs
    }

    pub fn ctx(&self) -> Context {
        Context { lib: &self.res_lib, std_objs: &self.std_objs }
    }

    pub fn into_lib(self) -> (Library, StdLibObjs) {
        (self.res_lib, self.std_objs)
    }
}

#[derive(Archive, Serialize, Deserialize, Debug)]
pub struct Library {
    namespace: u64,
    #[with(rkyv::with::AsVec)]
    objects: BTreeMap<ObjectId, Rc<Object>>,
    names: NameTree,
}

impl Library {
    pub fn new(namespace: u64, names: NameTree) -> Self {
        Self { namespace, objects: BTreeMap::new(), names }
    }

    pub fn num_objects(&self) -> usize {
        self.objects.len()
    }

    pub fn namespace(&self) -> u64 {
        self.namespace
    }

    pub fn names(&self) -> &NameTree {
        &self.names
    }
    
    pub fn get(&self, id: ObjectId) -> Option<&Rc<Object>> {
        self.objects.get(&id)
    }

    fn get_mut(&mut self, id: ObjectId) -> Option<&mut Rc<Object>> {
        self.objects.get_mut(&id)
    }

    pub fn extend(&mut self, other: Library) {
        // Rerooting does not change the keys of the btree map (yet), so we can't use the keys.
        for (_, object) in other.objects {
            self.insert(object);
        }
    }

    pub fn insert(&mut self, object: Rc<Object>) -> Rc<Object> {
        self.insert_at_id(object.id(), object)
    }

    pub fn insert_at_id(&mut self, id: ObjectId, object: Rc<Object>) -> Rc<Object> {
        match self.objects.entry(id) {
            btree_map::Entry::Vacant(entry) => {
                entry.insert(object).clone()
            },
            btree_map::Entry::Occupied(_) => {
                panic!("duplicate object id {}", id.inner_val());
            },
        }
    }

    // N.B. does not change the keys of the btree map
    pub fn reroot(&mut self, new_root: &CanonLibPath) {
        for object in self.objects.values_mut() {
            let object = Rc::make_mut(object);
            object.reroot(new_root);
        }
        self.names.reroot(new_root);
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Context<'a> {
    pub lib: &'a Library,
    pub std_objs: &'a StdLibObjs,
}

impl<'a> serde::Serialize for Context<'a> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        #[derive(serde::Serialize)]
        struct DisplayLibrary<'a> {
            objects: BTreeMap<ObjectId, DisplayObject<'a>>,
        }

        #[derive(serde::Serialize)]
        struct DisplayObject<'a> {
            id: ObjectId,
            path: &'a CanonLibPath,
            kind: DisplayObjectKind<'a>,
        }

        #[derive(serde::Serialize)]
        #[serde(tag = "tag")]
        enum DisplayObjectKind<'a> {
            #[serde(rename = "def")]
            Def,
            #[serde(rename = "thm")]
            Thm { proof: DisplayTheorem<'a> },
            #[serde(rename = "exp")]
            Exp,
            #[serde(rename = "inf")]
            Inf,
            #[serde(rename = "inf_intrinsic")]
            InfIntrinsic,
        }

        let objects = self.lib.objects.iter().map(|(id, object)| (*id, DisplayObject {
            id: object.id(),
            path: object.path(),
            kind: match object.kind() {
                ObjectKind::Def(_) => DisplayObjectKind::Def,
                ObjectKind::Thm(thm) => DisplayObjectKind::Thm { proof: DisplayTheorem {
                    thm,
                    ctx: *self,
                }},
                ObjectKind::Exp(_) => DisplayObjectKind::Exp,
                ObjectKind::Inf(_) => DisplayObjectKind::Inf,
                ObjectKind::InfIntrinsic(_) => DisplayObjectKind::InfIntrinsic,
            },
        }))
        .collect();

        DisplayLibrary { objects }.serialize(serializer)
    }
}

#[derive(Debug)]
pub enum ResolveError {
    UnknownObjectId(ObjectId),
    FreeVar(Box<str>),
    Cycle(CanonLibPathBuf),
    ExpectedTheorem(CanonLibPathBuf),
    InvalidTheoremAsDef(CanonLibPathBuf),
    BadArgCount {
        path: CanonLibPathBuf,
        params: usize,
        args: usize,
    },
    BadArg {
        path: CanonLibPathBuf,
        arg_num: usize,
        expected: &'static str,
    },
    UnexpectedInfRule(CanonLibPathBuf),
    ExpectedInfRule(CanonLibPathBuf),
    // FIXME: include extra information
    BadInferenceRuleArg,
    // FIXME: include extra information
    BadBetaRule,
    // FIXME: include extra information
    BadInferenceRuleDef,
}

impl fmt::Display for ResolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnknownObjectId(id) => {
                write!(f, "unknown object id {}", id.inner_val())
            },
            Self::FreeVar(free) => {
                write!(f, "unknown free variable `{}`", free)
            },
            Self::Cycle(path) => {
                write!(f, "cycle detected in definition of `{}`", path)
            },
            Self::ExpectedTheorem(path) => {
                write!(f, "expected `{}` to be a theorem", path)
            },
            Self::InvalidTheoremAsDef(path) => {
                write!(f, "theorem `{}` has no extract so cannot be used in an expression", path)
            },
            Self::BadArgCount { path: def_name, params: n_params, args } => {
                write!(f, "`{}` expects {} arguments, but {} were found", def_name, n_params, args)
            },
            Self::BadArg { path, arg_num, expected } => {
                write!(f, "expected argument {} of `{}` to be {}", arg_num + 1, path, expected)
            },
            Self::ExpectedInfRule(path) => {
                write!(f, "expected an inference rule, found `{}`", path)
            },
            Self::UnexpectedInfRule(path) => {
                write!(f, "cannot use inference rule `{}` as an expression", path)
            },
            Self::BadInferenceRuleArg => {
                write!(f, "bad inference rule argument")
            },
            Self::BadBetaRule => {
                write!(f, "bad beta rule")
            },
            Self::BadInferenceRuleDef => {
                write!(f, "bad inference rule definition")
            },
        }
    }
}

impl error::Error for ResolveError {}
