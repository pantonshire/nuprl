use std::rc::Rc;

use crate::{
    source::Span,
    phase3_proofck::exprkind_def::{ExprKindDefParam, ExprKindDef, BetaReduction},
    metadata::{ObjectMetadata, ObjectMedatataKind},
    path::{path::CanonLibPath, name_tree::NameTree},
    unif_var::{UnifVarIndices, UnifVarIndicesRef},
    var_stack::VarStack, stdlib::StdLibObjs,
};

use super::expr::{NameResolveError, NamedExpr};

#[derive(Debug)]
pub struct NamedExprKindDef {
    name: Rc<str>,
    params: Rc<[ExprKindDefParam]>,
    reductions: Box<[NamedBetaReduction]>,
    span: Span,
}

impl NamedExprKindDef {
    pub fn new(
        name: Rc<str>,
        params: Rc<[ExprKindDefParam]>,
        reductions: Box<[NamedBetaReduction]>,
        span: Span
    ) -> Self
    {
        Self { name, params, reductions, span }
    }

    pub fn name(&self) -> &Rc<str> {
        &self.name
    }

    pub fn params(&self) -> &Rc<[ExprKindDefParam]> {
        &self.params
    }

    pub fn span(&self) -> Span {
        self.span
    }

    pub fn resolve(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs
    ) -> Result<(ExprKindDef, ObjectMetadata), NameResolveError>
    {
        let reductions = self.reductions
            .iter()
            .map(|reduction| reduction.resolve(ctx, objects, std_objs))
            .collect::<Result<_, _>>()?;

        let exprkind_def = ExprKindDef::new(self.params.clone(), reductions);
        
        let metadata = ObjectMetadata {
            span: self.span,
            kind: ObjectMedatataKind::Exp,
        };

        Ok((exprkind_def, metadata))
    }
}

#[derive(Debug)]
pub struct NamedBetaReduction {
    target: NamedExpr,
    reduced: NamedExpr,
    _span: Span,
}

impl NamedBetaReduction {
    pub fn new(target: NamedExpr, reduced: NamedExpr, span: Span) -> Self {
        Self { target, reduced, _span: span }
    }

    pub fn resolve(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs
    ) -> Result<BetaReduction, NameResolveError>
    {
        let mut unif_vars = UnifVarIndices::new();

        let target = self.target.resolve(
            ctx,
            objects,
            std_objs,
            &mut VarStack::new(),
            Some(UnifVarIndicesRef::Mutable(&mut unif_vars))
        )?;

        let reduced = self.reduced.resolve(
            ctx,
            objects,
            std_objs,
            &mut VarStack::new(),
            Some(UnifVarIndicesRef::Immutable(&unif_vars))
        )?;

        Ok(BetaReduction::new(target, reduced))
    }
}
