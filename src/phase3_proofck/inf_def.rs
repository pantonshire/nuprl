use std::{rc::Rc, collections::BTreeMap};

use rkyv::{Archive, Serialize, Deserialize};

use crate::{unif_var::UnifVarIndex, de_bruijn::DeBruijnIndex, utils::InliningBuf};

use super::{
    sequent::{SequentRef, Sequent},
    expr::{Expr, RcExpr, ReductionSteps},
    inference::{InfArg, InferenceResult, Validation, InfParamKind},
    hypothesis::{Hypothesis, Visibility},
    library::{Resolver, ResolveError, Context},
};

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct InfDef {
    params: Rc<[InfDefParam]>,
    goal_hys: Rc<[HypothesisPattern]>,
    goal_concl: RcExpr,
    subgoals: Rc<[InfDefSubgoal]>,
    ext: RcExpr,
    constant_ext: bool,
}

impl InfDef {
    pub fn new(
        params: Rc<[InfDefParam]>,
        goal_hys: Rc<[HypothesisPattern]>,
        goal_concl: RcExpr,
        subgoals: Rc<[InfDefSubgoal]>,
        ext: RcExpr
    ) -> Self
    {
        let constant_ext = !ext.contains_placeholders();
        Self { params, goal_hys, goal_concl, subgoals, ext, constant_ext }
    }
    
    pub fn params(&self) -> &[InfDefParam] {
        &self.params
    }

    pub fn param_kinds(&self) -> InliningBuf<InfParamKind, 8> {
        self.params.iter().map(InfDefParam::kind).collect()
    }

    pub fn resolve(&self, resolver: &mut Resolver) -> Result<Self, ResolveError> {
        let mut depths = BTreeMap::new();

        let params = self.params
            .iter()
            .map(|param| match param {
                InfDefParam::Expr(expr) => {
                    let expr = expr.resolve(resolver)?;
                    expr.placeholder_conflict::<true>(&mut depths)
                        .map_err(|_| ResolveError::BadInferenceRuleDef)?;
                    
                    Ok(InfDefParam::Expr(expr))
                },

                InfDefParam::Var(var) => Ok(InfDefParam::Var(var.clone())),
            })
            .collect::<Result<Rc<[_]>, ResolveError>>()?;

        let goal_hys = self.goal_hys
            .iter()
            .map(|goal_hy| match goal_hy {
                HypothesisPattern::Hypothesis { pos, hy, var_expr } => {
                    let pos = pos.resolve(resolver)?;
                    pos.placeholder_conflict::<false>(&mut depths)
                        .map_err(|_| ResolveError::BadInferenceRuleDef)?;
    
                    let hy = hy.resolve(resolver)?;
                    hy.placeholder_conflict::<true>(&mut depths)
                        .map_err(|_| ResolveError::BadInferenceRuleDef)?;
    
                    depths.insert(*var_expr, DeBruijnIndex::ZERO);
    
                    Ok(HypothesisPattern::Hypothesis {
                        pos,
                        hy,
                        var_expr: *var_expr,
                    })
                },

                HypothesisPattern::Len { var_expr } => {
                    depths.insert(*var_expr, DeBruijnIndex::ZERO);

                    Ok(HypothesisPattern::Len { var_expr: *var_expr })
                },
            })
            .collect::<Result<Rc<[_]>, ResolveError>>()?;

        let goal_concl = self.goal_concl.resolve(resolver)?;
        goal_concl.placeholder_conflict::<true>(&mut depths)
            .map_err(|_| ResolveError::BadInferenceRuleDef)?;

        let subgoal_depths = depths.clone();

        let subgoals = self.subgoals
            .iter()
            .map(|subgoal| {
                let mut subgoal_depths = subgoal_depths.clone();

                let mut num_new_visible_hys = 0usize;

                let hys = subgoal.hys
                    .iter()
                    .map(|subgoal_hy| match subgoal_hy {
                        HypothesisOp::Insert { pos, hy, var_expr, var_name } => {
                            let pos = pos.resolve(resolver)?;
                            pos.placeholder_conflict::<false>(&mut subgoal_depths)
                                .map_err(|_| ResolveError::BadInferenceRuleDef)?;

                            let hy = hy.resolve(resolver)?;
                            hy.placeholder_conflict::<false>(&mut subgoal_depths)
                                .map_err(|_| ResolveError::BadInferenceRuleDef)?;

                            subgoal_depths.insert(*var_expr, DeBruijnIndex::ZERO);

                            // FIXME: hidden hypotheses should not count towards this total
                            num_new_visible_hys += 1;

                            Ok(HypothesisOp::Insert {
                                pos,
                                hy,
                                var_expr: *var_expr,
                                var_name: *var_name,
                            })
                        },

                        HypothesisOp::Remove { pos } => {
                            let pos = pos.resolve(resolver)?;
                            pos.placeholder_conflict::<false>(&mut subgoal_depths)
                                .map_err(|_| ResolveError::BadInferenceRuleDef)?;

                            Ok(HypothesisOp::Remove { pos })
                        },

                        HypothesisOp::Len { var_expr } => {
                            subgoal_depths.insert(*var_expr, DeBruijnIndex::ZERO);

                            Ok(HypothesisOp::Len { var_expr: *var_expr })
                        },
                    })
                    .collect::<Result<Box<[_]>, _>>()?;

                let concl = subgoal.concl.resolve(resolver)?;
                concl.placeholder_conflict::<false>(&mut subgoal_depths)
                    .map_err(|_| ResolveError::BadInferenceRuleDef)?;

                if let Some(ext) = subgoal.ext {
                    depths.insert(ext, DeBruijnIndex::new(num_new_visible_hys));
                }

                Ok(InfDefSubgoal { hys, concl, ext: subgoal.ext })
            })
            .collect::<Result<Rc<[_]>, _>>()?;

        let ext = self.ext.resolve(resolver)?;
        ext.placeholder_conflict::<false>(&mut depths)
            .map_err(|_| ResolveError::BadInferenceRuleDef)?;

        Ok(Self::new(params, goal_hys, goal_concl, subgoals, ext))
    }

    pub fn apply(&self, ctx: Context, args: &[InfArg], goal: SequentRef) -> InferenceResult {
        fn eval_hy_pos(ctx: Context, pos: &RcExpr, placeholders: &BTreeMap<UnifVarIndex, RcExpr>)
            -> Option<usize>
        {
            let pos = pos
                .subst_placeholders_or_clone(placeholders)
                .ok()?
                .reduce_or_clone(ctx, ReductionSteps::Infinite);

            pos.as_hy_pos()
        }

        let mut placeholders = BTreeMap::<UnifVarIndex, RcExpr>::new();
        let mut var_names = BTreeMap::<UnifVarIndex, Rc<str>>::new();

        assert_eq!(args.len(), self.params.len());
        
        for (i, (param, arg)) in self.params
            .iter()
            .zip(args.iter())
            .enumerate()
        {
            match param {
                InfDefParam::Expr(param) => {
                    let InfArg::Expr(arg) = arg else {
                        panic!("expected argument {} to be an expression", i)
                    };

                    if param.unify_placeholders_rec(arg, &mut placeholders).is_err() {
                        return InferenceResult::Conflict
                    }
                },

                InfDefParam::Var(var) => {
                    let InfArg::Var(arg) = arg else {
                        panic!("expected argument {} to be a variable name", i)
                    };

                    var_names.insert(*var, arg.clone());
                },
            }
        }

        for hy_pattern in self.goal_hys.iter() {
            match hy_pattern {
                HypothesisPattern::Hypothesis { pos, hy, var_expr } => {
                    let Some(pos) = eval_hy_pos(ctx, pos, &placeholders) else {
                        return InferenceResult::Conflict
                    };

                    // FIXME: find a more elegant way of writing this
                    // Only allow retrieval of a hidden hypothesis if the extract contains no
                    // placeholders.
                    let concrete_hy = if self.constant_ext {
                        let Ok(concrete_hy) = goal.hys().get_any(pos) else {
                            return InferenceResult::Conflict
                        };
                        concrete_hy
                    } else {
                        let Ok(concrete_hy) = goal.hys().get_visible(pos) else {
                            return InferenceResult::Conflict
                        };
                        concrete_hy
                    };

                    if hy.unify_placeholders_rec(concrete_hy.hy.ty(), &mut placeholders).is_err() {
                        return InferenceResult::Conflict
                    }

                    placeholders.insert(*var_expr, Expr::Hy(concrete_hy.id).rc());
                },

                HypothesisPattern::Len { var_expr } => {
                    let Some(end) = u64::try_from(goal.hys().len())
                        .ok()
                        .and_then(|len| len.checked_add(1))
                    else {
                        return InferenceResult::Conflict
                    };

                    placeholders.insert(*var_expr, Expr::Nat(end).rc());
                },
            }
        }

        if self.goal_concl.unify_placeholders_rec(goal.concl(), &mut placeholders).is_err() {
            return InferenceResult::Conflict
        }

        let mut subgoals = Vec::new();
        let mut subgoal_new_visible_hy_ids = Vec::new();

        for subgoal in self.subgoals.iter() {
            let mut hys = goal.hys().clone();
            let mut new_visible_hy_ids = Vec::new();
            let mut removed_hy_ids = Vec::new();
            let mut placeholders = placeholders.clone();

            for hy_op in subgoal.hys.iter() {
                match hy_op {
                    HypothesisOp::Insert { pos, hy, var_expr, var_name } => {
                        let Some(pos) = eval_hy_pos(ctx, pos, &placeholders) else {
                            return InferenceResult::Conflict
                        };
                        
                        let Ok(hy) = hy.subst_placeholders_or_clone(&placeholders) else {
                            return InferenceResult::Conflict
                        };

                        for removed_hy_id in removed_hy_ids.iter() {
                            if hy.contains_hypothesis(*removed_hy_id) {
                                return InferenceResult::Conflict
                            }
                        }

                        let Some(var_name) = var_names.get(var_name) else {
                            return InferenceResult::Conflict
                        };

                        // FIXME: implement a way for the user to create a hidden hypothesis
                        let hy = Hypothesis::new(var_name.clone(), hy, Visibility::Visible);

                        let Some((new_hys, hy_id)) = hys.with_inserted(pos, hy) else {
                            return InferenceResult::Conflict
                        };

                        placeholders.insert(*var_expr, Expr::Hy(hy_id).rc());
                        // FIXME: remember not to push if the hypothesis is hidden
                        new_visible_hy_ids.push(hy_id);

                        hys = new_hys;
                    },

                    HypothesisOp::Remove { pos } => {
                        let Some(pos) = eval_hy_pos(ctx, pos, &placeholders) else {
                            return InferenceResult::Conflict
                        };

                        let Ok((new_hys, removed)) = hys.with_removed(pos) else {
                            return InferenceResult::Conflict
                        };

                        removed_hy_ids.push(removed.id);

                        hys = new_hys;
                    },
                    
                    HypothesisOp::Len { var_expr } => {
                        let Some(end) = u64::try_from(hys.len())
                            .ok()
                            .and_then(|len| len.checked_add(1)) 
                        else {
                            return InferenceResult::Conflict
                        };
    
                        placeholders.insert(*var_expr, Expr::Nat(end).rc());
                    },
                }
            }

            let Ok(concl) = subgoal.concl.subst_placeholders_or_clone(&placeholders) else {
                return InferenceResult::Conflict
            };

            for removed_hy_id in removed_hy_ids.iter() {
                if concl.contains_hypothesis(*removed_hy_id) {
                    return InferenceResult::Conflict
                }
            }

            subgoals.push(Sequent::new(hys, concl));
            subgoal_new_visible_hy_ids.push(new_visible_hy_ids);
        }

        let validation = Validation::dynamic({
            let subgoals = self.subgoals.clone();
            let validation_ext = self.ext.clone();

            move |sub_theorems| {
                for ((sub_theorem, subgoal), new_visible_hy_ids) in sub_theorems
                    .iter()
                    .zip(subgoals.iter())
                    .zip(subgoal_new_visible_hy_ids.iter())
                {
                    if let Some(ext_placeholder) = subgoal.ext {
                        let mut ext = sub_theorem.extract().clone();
                        for new_visible_hy_id in new_visible_hy_ids {
                            ext = ext.bind_hypothesis_or_clone(*new_visible_hy_id);
                        }

                        placeholders.insert(ext_placeholder, ext);
                    }
                }
    
                validation_ext
                    .subst_placeholders_or_clone(&placeholders)
                    .expect("extract should not contain any new placeholders")
            }
        });
        
        InferenceResult::Ok { subgoals, validation }
    }
}

#[derive(Archive, Serialize, Deserialize, Debug)]
pub enum InfDefParam {
    Expr(RcExpr),
    Var(UnifVarIndex),
}

impl InfDefParam {
    pub fn kind(&self) -> InfParamKind {
        match self {
            InfDefParam::Expr(_) => InfParamKind::Expr,
            InfDefParam::Var(_) => InfParamKind::Var,
        }
    }
}

#[derive(Archive, Serialize, Deserialize, Debug)]
pub struct InfDefSubgoal {
    hys: Box<[HypothesisOp]>,
    concl: RcExpr,
    ext: Option<UnifVarIndex>,
}

impl InfDefSubgoal {
    pub fn new(hys: Box<[HypothesisOp]>, concl: RcExpr, ext: Option<UnifVarIndex>) -> Self {
        Self { hys, concl, ext }
    }
}

#[derive(Archive, Serialize, Deserialize, Debug)]
pub enum HypothesisPattern {
    Hypothesis {
        pos: RcExpr,
        hy: RcExpr,
        var_expr: UnifVarIndex,
    },
    Len {
        var_expr: UnifVarIndex,
    },
}

#[derive(Archive, Serialize, Deserialize, Debug)]
pub enum HypothesisOp {
    Insert {
        pos: RcExpr,
        hy: RcExpr,
        var_expr: UnifVarIndex,
        var_name: UnifVarIndex,
    },
    Remove {
        pos: RcExpr,
    },
    Len {
        var_expr: UnifVarIndex,
    },
}
