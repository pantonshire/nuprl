use rkyv::{Archive, Serialize, Deserialize};

use crate::{object_id::ObjectId, path::path::{CanonLibPathBuf, CanonLibPath}};

use super::{
    exprkind_def::ExprKindDef,
    definition::Definition,
    inf_def::InfDef, proof::{Theorem, UncheckedTheorem}, inf_intrinsic::InfIntrinsic, inference::InfRuleObj,
};

#[derive(Debug)]
pub struct UnresolvedObject {
    id: ObjectId,
    ctx: CanonLibPathBuf,
    path: CanonLibPathBuf,
    kind: UnresolvedObjectKind,
}

impl UnresolvedObject {
    pub fn new(
        id: ObjectId,
        ctx: CanonLibPathBuf,
        path: CanonLibPathBuf,
        kind: UnresolvedObjectKind
    ) -> Self
    {
        Self { id, ctx, path, kind }
    }
    
    pub fn id(&self) -> ObjectId {
        self.id
    }

    pub fn ctx(&self) -> &CanonLibPath {
        &self.ctx
    }
    
    pub fn path(&self) -> &CanonLibPath {
        &self.path
    }

    pub fn kind(&self) -> &UnresolvedObjectKind {
        &self.kind
    }
}

#[derive(Debug)]
pub enum UnresolvedObjectKind {
    Def(Definition),
    Thm(UncheckedTheorem),
    Exp(ExprKindDef),
    Inf(InfDef),
    InfIntrinsic(InfIntrinsic),
}


#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct Object {
    id: ObjectId,
    path: CanonLibPathBuf,
    kind: ObjectKind,
}

impl Object {
    pub fn new(id: ObjectId, path: CanonLibPathBuf, kind: ObjectKind) -> Self {
        Self { id, path, kind }
    }

    pub fn def(id: ObjectId, path: CanonLibPathBuf, def: Definition) -> Self {
        Self::new(id, path, ObjectKind::Def(def))
    }

    pub fn thm(id: ObjectId, path: CanonLibPathBuf, thm: Theorem) -> Self {
        Self::new(id, path, ObjectKind::Thm(thm))
    }

    pub fn exp(id: ObjectId, path: CanonLibPathBuf, exprkind: ExprKindDef) -> Self {
        Self::new(id, path, ObjectKind::Exp(exprkind))
    }

    pub fn inf(id: ObjectId, path: CanonLibPathBuf, inf: InfDef) -> Self {
        Self::new(id, path, ObjectKind::Inf(inf))
    }

    pub fn id(&self) -> ObjectId {
        self.id
    }

    pub fn path(&self) -> &CanonLibPathBuf {
        &self.path
    }

    pub fn kind(&self) -> &ObjectKind {
        &self.kind
    }

    pub fn kind_mut(&mut self) -> &mut ObjectKind {
        &mut self.kind
    }

    pub fn reroot(&mut self, new_root: &CanonLibPath) {
        self.path = self.path.rerooted(new_root);
    }

    pub fn as_inf(&self) -> Option<InfRuleObj> {
        match self.kind() {
            ObjectKind::Inf(inf_def) => Some(InfRuleObj::Def(inf_def)),
            ObjectKind::InfIntrinsic(intrinsic) => Some(InfRuleObj::Intrinsic(intrinsic)),
            _ => None,
        }
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub enum ObjectKind {
    Def(Definition),
    Thm(Theorem),
    Exp(ExprKindDef),
    Inf(InfDef),
    InfIntrinsic(InfIntrinsic),
}
