use std::rc::Rc;

use crate::{
    source::Span,
    phase3_proofck::inf_def::{InfDef, InfDefParam, InfDefSubgoal, HypothesisOp, HypothesisPattern},
    unif_var::{UnifVarIndices, UnifVarIndicesRef},
    var_stack::VarStack,
    path::{path::CanonLibPath, name_tree::NameTree}, stdlib::StdLibObjs,
};

use super::expr::{NamedExpr, NameResolveError};

#[derive(Debug)]
pub struct NamedInfDef {
    name: Rc<str>,
    params: Box<[NamedInfDefParam]>,
    goal_hys: Box<[NamedHypothesisPattern]>,
    goal_concl: NamedExpr,
    subgoals: Box<[NamedInfDefSubgoal]>,
    ext: NamedExpr,
    span: Span,
}

impl NamedInfDef {
    pub fn new(
        name: Rc<str>,
        params: Box<[NamedInfDefParam]>,
        goal_hys: Box<[NamedHypothesisPattern]>,
        goal_concl: NamedExpr,
        subgoals: Box<[NamedInfDefSubgoal]>,
        ext: NamedExpr,
        span: Span
    ) -> Self
    {
        Self { name, params, goal_hys, goal_concl, subgoals, ext, span  }
    }

    pub fn name(&self) -> &Rc<str> {
        &self.name
    }

    pub fn params(&self) -> &[NamedInfDefParam] {
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
    ) -> Result<InfDef, NameResolveError>
    {
        let mut unif_vars = UnifVarIndices::new();
        let mut varname_unif_vars = UnifVarIndices::new();

        let params = self.params
            .iter()
            .map(|param| param.resolve(
                ctx,
                objects,
                std_objs,
                &mut unif_vars,
                &mut varname_unif_vars
            ))
            .collect::<Result<Rc<[_]>, _>>()?;

        let goal_hys = self.goal_hys
            .iter()
            .map(|hy_pattern| hy_pattern.resolve(
                ctx,
                objects,
                std_objs,
                &mut unif_vars
            ))
            .collect::<Result<Rc<[_]>, _>>()?;

        let goal_concl = self.goal_concl.resolve(
            ctx,
            objects,
            std_objs,
            &mut VarStack::new(),
            Some(UnifVarIndicesRef::Mutable(&mut unif_vars))
        )?;

        // Make a copy of the unif vars before we put any subgoal extract placeholders into it.
        // This is necessary because we do not allow subgoals to refer to each others' extracts.
        let subgoal_unif_vars = unif_vars.clone();

        let subgoals = self.subgoals
            .iter()
            .map(|subgoal| {
                subgoal.resolve(
                    ctx,
                    objects,
                    std_objs,
                    &mut unif_vars,
                    subgoal_unif_vars.clone(),
                    &varname_unif_vars
                )
            })
            .collect::<Result<Rc<[_]>, _>>()?;

        drop(subgoal_unif_vars);

        let ext = self.ext.resolve(
            ctx,
            objects,
            std_objs,
            &mut VarStack::new(),
            Some(UnifVarIndicesRef::Immutable(&unif_vars))
        )?;

        Ok(InfDef::new(params, goal_hys, goal_concl, subgoals, ext))
    }
}

#[derive(Debug)]
pub enum NamedInfDefParam {
    Expr(NamedExpr),
    Var(Rc<str>),
}

impl NamedInfDefParam {
    fn resolve(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs,
        unif_vars: &mut UnifVarIndices,
        varname_unif_vars: &mut UnifVarIndices
    ) -> Result<InfDefParam, NameResolveError>
    {
        match self {
            Self::Expr(expr) => {
                // Resolve the parameter expression, creating unif var indices for any placehodlers
                // it contains.
                expr
                    .resolve(
                        ctx,
                        objects,
                        std_objs,
                        &mut VarStack::new(),
                        Some(UnifVarIndicesRef::Mutable(unif_vars))
                    )
                    .map(|expr| InfDefParam::Expr(expr))
            },
            Self::Var(var) => {
                // Generate a new unif var index for the variable name placeholder. This must be a
                // new unif var; return an error for any duplicate placeholder names.
                varname_unif_vars
                    .generate(var.clone())
                    .map(|index| InfDefParam::Var(index))
                    .ok_or_else(|| NameResolveError::DuplicateUnifVar {
                        name: var.clone()
                    })
            },
        }
    }
}

#[derive(Debug)]
pub enum NamedHypothesisPattern {
    Hypothesis {
        pos: NamedExpr,
        var: Rc<str>,
        hy: NamedExpr,
    },
    Len {
        var: Rc<str>,
    },
}

impl NamedHypothesisPattern {    
    fn resolve(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs,
        unif_vars: &mut UnifVarIndices
    ) -> Result<HypothesisPattern, NameResolveError>
    {
        match self {
            Self::Hypothesis { pos, var, hy } => {
                // Resolve the position expression, allowing placeholders that have already been
                // declared but denying any new placeholders.
                let pos = pos.resolve(
                    ctx,
                    objects,
                    std_objs,
                    &mut VarStack::new(),
                    Some(UnifVarIndicesRef::Immutable(unif_vars))
                )?;

                // Resolve the hypothesis type, allowing new placeholders to be declared. We
                // resolve the hypothesis type before creating a unif var index for its variable
                // because we don't want the hypothesis type to be able to refer to its own
                // variable.
                let hy = hy.resolve(
                    ctx,
                    objects,
                    std_objs,
                    &mut VarStack::new(),
                    Some(UnifVarIndicesRef::Mutable(unif_vars))
                )?;

                let var_expr = unif_vars.generate(var.clone())
                    .ok_or_else(|| NameResolveError::DuplicateUnifVar { name: var.clone() })?;

                Ok(HypothesisPattern::Hypothesis { pos, hy, var_expr })
            },

            Self::Len { var } => {
                let var_expr = unif_vars.generate(var.clone())
                    .ok_or_else(|| NameResolveError::DuplicateUnifVar { name: var.clone() })?;

                Ok(HypothesisPattern::Len { var_expr })
            },
        }
    }
}

#[derive(Debug)]
pub struct NamedInfDefSubgoal {
    hys: Box<[NamedHypothesisOp]>,
    concl: NamedExpr,
    ext: Option<Rc<str>>,
}

impl NamedInfDefSubgoal {
    pub fn new(hys: Box<[NamedHypothesisOp]>, concl: NamedExpr, ext: Option<Rc<str>>) -> Self {
        Self { hys, concl, ext }
    }
    
    fn resolve(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs,
        main_unif_vars: &mut UnifVarIndices,
        mut subgoal_unif_vars: UnifVarIndices,
        varname_unif_vars: &UnifVarIndices
    ) -> Result<InfDefSubgoal, NameResolveError>
    {
        // Resolve the hypotheses using a copy of `unif_vars` rather than `unif_vars` itself, since
        // we don't want the placeholders representing the hypothesis variables to be available to
        // other subgoals or the overall extract.
        let hys = self.hys
            .iter()
            .map(|hy_op| hy_op.resolve(
                ctx,
                objects,
                std_objs,
                &mut subgoal_unif_vars,
                varname_unif_vars
            ))
            .collect::<Result<Box<[_]>, _>>()?;

        // Resolve the conclusion using our copy of `unif_vars` so that it can refer to any new
        // hypothesis variables.
        let concl = self.concl.resolve(
            ctx,
            objects,
            std_objs,
            &mut VarStack::new(),
            Some(UnifVarIndicesRef::Immutable(&subgoal_unif_vars))
        )?;

        let ext = self.ext
            .as_ref()
            .map(|ext| main_unif_vars.generate(ext.clone())
                .ok_or_else(|| NameResolveError::DuplicateUnifVar { name: ext.clone() }))
            .transpose()?;

        Ok(InfDefSubgoal::new(hys, concl, ext))
    }
}

#[derive(Debug)]
pub enum NamedHypothesisOp {
    Insert {
        pos: NamedExpr,
        var: Rc<str>,
        hy: NamedExpr,
    },
    Remove {
        pos: NamedExpr,
    },
    Len {
        var: Rc<str>,
    },
}

impl NamedHypothesisOp {
    fn resolve(
        &self,
        ctx: &CanonLibPath,
        objects: &NameTree,
        std_objs: &StdLibObjs,
        unif_vars: &mut UnifVarIndices,
        varname_unif_vars: &UnifVarIndices
    ) -> Result<HypothesisOp, NameResolveError>
    {
        match self {
            Self::Insert { pos, var, hy } => {
                let pos = pos.resolve(
                    ctx,
                    objects,
                    std_objs,
                    &mut VarStack::new(),
                    Some(UnifVarIndicesRef::Immutable(unif_vars))
                )?;

                let hy = hy.resolve(
                    ctx,
                    objects,
                    std_objs,
                    &mut VarStack::new(),
                    Some(UnifVarIndicesRef::Immutable(unif_vars))
                )?;
        
                let var_name = varname_unif_vars.get(var)
                    .ok_or_else(|| NameResolveError::UnknownUnifVar { name: var.clone() })?;
        
                let var_expr = unif_vars.generate(var.clone())
                    .ok_or_else(|| NameResolveError::DuplicateUnifVar { name: var.clone() })?;

                Ok(HypothesisOp::Insert { pos, hy, var_expr, var_name })
            },

            Self::Remove { pos } => {
                let pos = pos.resolve(
                    ctx,
                    objects,
                    std_objs,
                    &mut VarStack::new(),
                    Some(UnifVarIndicesRef::Immutable(unif_vars))
                )?;
                
                Ok(HypothesisOp::Remove { pos })
            },

            Self::Len { var } => {
                let var_expr = unif_vars.generate(var.clone())
                    .ok_or_else(|| NameResolveError::UnknownUnifVar { name: var.clone() })?;

                Ok(HypothesisOp::Len { var_expr })
            },
        }
    }
}
