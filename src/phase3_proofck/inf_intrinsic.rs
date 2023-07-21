use rkyv::{Archive, Serialize, Deserialize};

use crate::{phase3_proofck::{expr::Expr, hypothesis::{Visibility, Hypothesis}}, utils::InliningBuf};

use super::{library::Context, inference::{InfArg, InferenceResult, InfParamKind, Validation}, sequent::{SequentRef, Sequent}, expr::{ObjExpr, ReductionSteps, Bound}, hypothesis::HypothesisEntryRef};

#[derive(Archive, Serialize, Deserialize, Clone, Copy, Debug)]
pub enum InfIntrinsic {
    FunctionEquality,
    LambdaEquality,
    LambdaFormation,
    ApplyEquality,
    UniverseFormation,
    UniverseEquality,
    Cumulativity,
    IsectMemberFormation,
    DirectComputation,
    ReverseDirectComputation,
    DirectComputationHypothesis,
    ReverseDirectComputationHypothesis,
    Lemma,
    Extract,
}

impl InfIntrinsic {
    pub fn from_str(name: &str) -> Option<Self> {
        match name {
            "functionEquality" => Some(Self::FunctionEquality),
            "lambdaEquality" => Some(Self::LambdaEquality),
            "lambdaFormation" => Some(Self::LambdaFormation),
            "applyEquality" => Some(Self::ApplyEquality),
            "universeFormation" => Some(Self::UniverseFormation),
            "universeEquality" => Some(Self::UniverseEquality),
            "cumulativity" => Some(Self::Cumulativity),
            "isect_memberFormation" => Some(Self::IsectMemberFormation),
            "direct_computation" => Some(Self::DirectComputation),
            "reverse_direct_computation" => Some(Self::ReverseDirectComputation),
            "direct_computation_hypothesis" => Some(Self::DirectComputationHypothesis),
            "reverse_direct_computation_hypothesis" => Some(Self::ReverseDirectComputationHypothesis),
            "lemma" => Some(Self::Lemma),
            "extract" => Some(Self::Extract),
            _ => None,
        }
    }

    pub fn params(&self) -> &'static [InfParamKind] {
        match self {
            Self::FunctionEquality => {
                &[InfParamKind::Var]
            },
            Self::LambdaEquality => {
                &[InfParamKind::Expr, InfParamKind::Var]
            },
            Self::LambdaFormation => {
                &[InfParamKind::Expr, InfParamKind::Var]
            },
            Self::ApplyEquality => {
                &[InfParamKind::Expr]
            },
            Self::UniverseFormation => {
                &[InfParamKind::Expr]
            },
            Self::UniverseEquality => {
                &[]
            },
            Self::Cumulativity => {
                &[InfParamKind::Expr]
            },
            Self::IsectMemberFormation => {
                &[InfParamKind::Expr, InfParamKind::Var]
            },
            Self::DirectComputation => {
                &[InfParamKind::Expr]
            },
            Self::ReverseDirectComputation => {
                &[InfParamKind::Expr]
            },
            Self::DirectComputationHypothesis => {
                &[InfParamKind::Expr, InfParamKind::Expr]
            },
            Self::ReverseDirectComputationHypothesis => {
                &[InfParamKind::Expr, InfParamKind::Expr]
            },
            Self::Lemma => {
                &[InfParamKind::ProofResult]
            },
            Self::Extract => {
                &[InfParamKind::ProofResult]
            },
        }
    }

    pub fn apply(&self, ctx: Context, args: &[InfArg], goal: SequentRef) -> InferenceResult {
        match self {
            Self::FunctionEquality => {
                let Some(ax_id) = ctx.std_objs.ax else {
                    return InferenceResult::Conflict
                };

                let Some(eq_id) = ctx.std_objs.eq else {
                    return InferenceResult::Conflict
                };
                
                let Some(fn_id) = ctx.std_objs.func else {
                    return InferenceResult::Conflict
                };

                let Some(uni_id) = ctx.std_objs.universe else {
                    return InferenceResult::Conflict
                };

                let [InfArg::Var(x)] = args else {
                    return InferenceResult::Conflict
                };

                let Expr::Obj(eq_ty) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if eq_ty.id() != eq_id {
                    return InferenceResult::Conflict
                }

                let [uni_expr, lhs_fn, rhs_fn] = eq_ty.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Expr::Obj(uni) = uni_expr.as_ref() else {
                    return InferenceResult::Conflict
                };

                if uni.id() != uni_id {
                    return InferenceResult::Conflict
                }

                let (s1, t1) = {
                    let Expr::Obj(lhs_app) = lhs_fn.as_ref() else {
                        return InferenceResult::Conflict
                    };

                    if lhs_app.id() != fn_id {
                        return InferenceResult::Conflict
                    }

                    let [s1, t1] = lhs_app.args().as_ref() else {
                        return InferenceResult::Conflict
                    };

                    (s1, t1)
                };

                let (s2, t2) = {
                    let Expr::Obj(rhs_app) = rhs_fn.as_ref() else {
                        return InferenceResult::Conflict
                    };

                    if rhs_app.id() != fn_id {
                        return InferenceResult::Conflict
                    }

                    let [s2, t2] = rhs_app.args().as_ref() else {
                        return InferenceResult::Conflict
                    };

                    (s2, t2)
                };

                let Some((hys_with_s1, s1_hy_id)) = goal.hys().clone()
                    .with_appended(Hypothesis::new(
                        x.clone(),
                        s1.clone(),
                        Visibility::Visible
                    ))
                else {
                    return InferenceResult::Conflict
                };

                let s1_hy = Expr::Hy(s1_hy_id).rc();

                match (t1.as_ref(), t2.as_ref()) {
                    (Expr::Bound(t1), Expr::Bound(t2)) => {
                        InferenceResult::Ok {
                            subgoals: vec![
                                Sequent::new(
                                    goal.hys().clone(),
                                    ObjExpr::new(eq_id, [
                                        uni_expr.clone(),
                                        s1.clone(),
                                        s2.clone(),
                                    ].into_iter().collect()).expr().rc()
                                ),
                                Sequent::new(
                                    hys_with_s1,
                                    ObjExpr::new(eq_id, [
                                        uni_expr.clone(),
                                        t1.body(&s1_hy),
                                        t2.body(&s1_hy),
                                    ].into_iter().collect()).expr().rc()
                                )
                            ],
                            validation: Validation::dynamic(move |_| {
                                ObjExpr::new(ax_id, InliningBuf::new()).expr().rc()
                            }),
                        }
                    },

                    _ => {
                        InferenceResult::Ok {
                            subgoals: vec![
                                Sequent::new(
                                    goal.hys().clone(),
                                    ObjExpr::new(eq_id, [
                                        uni_expr.clone(),
                                        s1.clone(),
                                        s2.clone(),
                                    ].into_iter().collect()).expr().rc()
                                ),
                                Sequent::new(
                                    hys_with_s1,
                                    ObjExpr::new(eq_id, [
                                        uni_expr.clone(),
                                        t1.clone(),
                                        t2.clone(),
                                    ].into_iter().collect()).expr().rc()
                                )
                            ],
                            validation: Validation::dynamic(move |_| {
                                ObjExpr::new(ax_id, InliningBuf::new()).expr().rc()
                            }),
                        }
                    },
                }
            },

            Self::LambdaEquality => {
                let Some(ax_id) = ctx.std_objs.ax else {
                    return InferenceResult::Conflict
                };

                let Some(lambda_id) = ctx.std_objs.lambda else {
                    return InferenceResult::Conflict
                };

                let Some(eq_id) = ctx.std_objs.eq else {
                    return InferenceResult::Conflict
                };
                
                let Some(fn_id) = ctx.std_objs.func else {
                    return InferenceResult::Conflict
                };
                
                let Some(uni_id) = ctx.std_objs.universe else {
                    return InferenceResult::Conflict
                };

                let [InfArg::Expr(j), InfArg::Var(x)] = args else {
                    return InferenceResult::Conflict
                };

                if !matches!(j.as_ref(), Expr::Nat(_)) {
                    return InferenceResult::Conflict
                }

                let Expr::Obj(eq_ty) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if eq_ty.id() != eq_id {
                    return InferenceResult::Conflict
                }

                let [fn_ty, lhs_lambda, rhs_lambda] = eq_ty.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let t1 = {
                    let Expr::Obj(lhs_lambda) = lhs_lambda.as_ref() else {
                        return InferenceResult::Conflict
                    };
    
                    if lhs_lambda.id() != lambda_id {
                        return InferenceResult::Conflict
                    }
    
                    let [lhs_lambda_bound] = lhs_lambda.args().as_ref() else {
                        return InferenceResult::Conflict
                    };
    
                    let Expr::Bound(t1) = lhs_lambda_bound.as_ref() else {
                        return InferenceResult::Conflict
                    };

                    t1
                };

                let t2 = {
                    let Expr::Obj(rhs_lambda) = rhs_lambda.as_ref() else {
                        return InferenceResult::Conflict
                    };
    
                    if rhs_lambda.id() != lambda_id {
                        return InferenceResult::Conflict
                    }
    
                    let [rhs_lambda_bound] = rhs_lambda.args().as_ref() else {
                        return InferenceResult::Conflict
                    };
    
                    let Expr::Bound(t2) = rhs_lambda_bound.as_ref() else {
                        return InferenceResult::Conflict
                    };

                    t2
                };

                let Expr::Obj(fn_ty) = fn_ty.as_ref() else {
                    return InferenceResult::Conflict
                };

                if fn_ty.id() != fn_id {
                    return InferenceResult::Conflict
                }

                let [domain, codomain] = fn_ty.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Some((hys_with_domain, domain_hy_id)) = goal.hys().clone()
                    .with_appended(Hypothesis::new(
                        x.clone(),
                        domain.clone(),
                        Visibility::Visible
                    ))
                else {
                    return InferenceResult::Conflict
                };

                let domain_hy = Expr::Hy(domain_hy_id).rc();

                match codomain.as_ref() {
                    Expr::Bound(codomain) => {
                        InferenceResult::Ok {
                            subgoals: vec![
                                Sequent::new(
                                    hys_with_domain,
                                    ObjExpr::new(eq_id, [
                                        codomain.body(&domain_hy),
                                        t1.body(&domain_hy),
                                        t2.body(&domain_hy),
                                    ].into_iter().collect()).expr().rc()
                                ),
                                Sequent::new(
                                    goal.hys().clone(),
                                    ObjExpr::new(eq_id, [
                                        ObjExpr::new(uni_id, [
                                            j.clone()
                                        ].into_iter().collect()).expr().rc(),
                                        domain.clone(),
                                        domain.clone(),
                                    ].into_iter().collect()).expr().rc()
                                ),
                            ],
                            validation: Validation::dynamic(move |_| {
                                ObjExpr::new(ax_id, InliningBuf::new()).expr().rc()
                            }),
                        }
                    },

                    _ => {
                        InferenceResult::Ok {
                            subgoals: vec![
                                Sequent::new(
                                    hys_with_domain,
                                    ObjExpr::new(eq_id, [
                                        codomain.clone(),
                                        t1.body(&domain_hy),
                                        t2.body(&domain_hy),
                                    ].into_iter().collect()).expr().rc()
                                ),
                                Sequent::new(
                                    goal.hys().clone(),
                                    ObjExpr::new(eq_id, [
                                        ObjExpr::new(uni_id, [
                                            j.clone()
                                        ].into_iter().collect()).expr().rc(),
                                        domain.clone(),
                                        domain.clone(),
                                    ].into_iter().collect()).expr().rc()
                                ),
                            ],
                            validation: Validation::dynamic(move |_| {
                                ObjExpr::new(ax_id, InliningBuf::new()).expr().rc()
                            }),
                        }
                    },
                }
            },

            Self::LambdaFormation => {
                let Some(lambda_id) = ctx.std_objs.lambda else {
                    return InferenceResult::Conflict
                };

                let Some(eq_id) = ctx.std_objs.eq else {
                    return InferenceResult::Conflict
                };
                
                let Some(fn_id) = ctx.std_objs.func else {
                    return InferenceResult::Conflict
                };

                let Some(uni_id) = ctx.std_objs.universe else {
                    return InferenceResult::Conflict
                };

                let [InfArg::Expr(j), InfArg::Var(x)] = args else {
                    return InferenceResult::Conflict
                };

                if !matches!(j.as_ref(), Expr::Nat(_)) {
                    return InferenceResult::Conflict
                }

                let Expr::Obj(fn_ty) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if fn_ty.id() != fn_id {
                    return InferenceResult::Conflict
                }

                let [domain, codomain] = fn_ty.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Some((hys_with_domain, domain_hy_id)) = goal.hys().clone()
                    .with_appended(Hypothesis::new(
                        x.clone(),
                        domain.clone(),
                        Visibility::Visible
                    ))
                else {
                    return InferenceResult::Conflict
                };

                let domain_hy = Expr::Hy(domain_hy_id).rc();

                match codomain.as_ref() {
                    Expr::Bound(codomain) => {    
                        InferenceResult::Ok {
                            subgoals: vec![
                                Sequent::new(
                                    hys_with_domain,
                                    codomain.body(&domain_hy)
                                ),
                                Sequent::new(
                                    goal.hys().clone(),
                                    ObjExpr::new(eq_id, [
                                        ObjExpr::new(uni_id, [
                                            j.clone()
                                        ].into_iter().collect()).expr().rc(),
                                        domain.clone(),
                                        domain.clone(),
                                    ].into_iter().collect()).expr().rc()
                                ),
                            ],
                            validation: Validation::dynamic({
                                let x = x.clone();
                                move |sub_theorems| {
                                    let lambda_body = sub_theorems[0].extract()
                                        .bind_hypothesis_or_clone(domain_hy_id);

                                    ObjExpr::new(lambda_id, [
                                        Bound::new(x, lambda_body).expr().rc()
                                    ].into_iter().collect()).expr().rc()
                                }
                            })
                        }
                    },

                    _ => {
                        InferenceResult::Ok {
                            subgoals: vec![
                                Sequent::new(
                                    hys_with_domain,
                                    codomain.clone()
                                ),
                                Sequent::new(
                                    goal.hys().clone(),
                                    ObjExpr::new(eq_id, [
                                        ObjExpr::new(uni_id, [
                                            j.clone()
                                        ].into_iter().collect()).expr().rc(),
                                        domain.clone(),
                                        domain.clone(),
                                    ].into_iter().collect()).expr().rc()
                                ),
                            ],
                            validation: Validation::dynamic({
                                let x = x.clone();
                                move |sub_theorems| {
                                    let lambda_body = sub_theorems[0].extract()
                                        .bind_hypothesis_or_clone(domain_hy_id);

                                    ObjExpr::new(lambda_id, [
                                        Bound::new(x, lambda_body).expr().rc()
                                    ].into_iter().collect()).expr().rc()
                                }
                            })
                        }
                    },
                }
            },

            Self::ApplyEquality => {
                let Some(ax_id) = ctx.std_objs.ax else {
                    return InferenceResult::Conflict
                };

                let Some(app_id) = ctx.std_objs.app else {
                    return InferenceResult::Conflict
                };
                
                let Some(eq_id) = ctx.std_objs.eq else {
                    return InferenceResult::Conflict
                };
                
                let Some(fn_id) = ctx.std_objs.func else {
                    return InferenceResult::Conflict
                };

                let [InfArg::Expr(fn_ty_expr)] = args else {
                    return InferenceResult::Conflict
                };

                let Expr::Obj(fn_ty) = fn_ty_expr.as_ref() else {
                    return InferenceResult::Conflict
                };

                if fn_ty.id() != fn_id {
                    return InferenceResult::Conflict
                }

                let [domain, codomain] = fn_ty.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Expr::Obj(eq_ty) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if eq_ty.id() != eq_id {
                    return InferenceResult::Conflict
                }

                let [t_ty_subst, lhs_app, rhs_app] = eq_ty.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let (f1, t1) = {
                    let Expr::Obj(lhs_app) = lhs_app.as_ref() else {
                        return InferenceResult::Conflict
                    };

                    if lhs_app.id() != app_id {
                        return InferenceResult::Conflict
                    }

                    let [f1, t1] = lhs_app.args().as_ref() else {
                        return InferenceResult::Conflict
                    };

                    (f1, t1)
                };

                let (f2, t2) = {
                    let Expr::Obj(rhs_app) = rhs_app.as_ref() else {
                        return InferenceResult::Conflict
                    };

                    if rhs_app.id() != app_id {
                        return InferenceResult::Conflict
                    }

                    let [f2, t2] = rhs_app.args().as_ref() else {
                        return InferenceResult::Conflict
                    };

                    (f2, t2)
                };

                match codomain.as_ref() {
                    Expr::Bound(codomain) => {
                        if t_ty_subst != &codomain.body(t1) {
                            return InferenceResult::Conflict
                        }
                    },

                    _ => {
                        let t_ty = t_ty_subst;
                        if t_ty != codomain {
                            return InferenceResult::Conflict
                        }
                    },
                }

                InferenceResult::Ok {
                    subgoals: vec![
                        Sequent::new(
                            goal.hys().clone(),
                            ObjExpr::new(eq_id, [
                                fn_ty_expr.clone(),
                                f1.clone(),
                                f2.clone(),
                            ].into_iter().collect()).expr().rc()
                        ),
                        Sequent::new(
                            goal.hys().clone(),
                            ObjExpr::new(eq_id, [
                                domain.clone(),
                                t1.clone(),
                                t2.clone(),
                            ].into_iter().collect()).expr().rc()
                        ),
                    ],
                    validation: Validation::dynamic(move |_| {
                        ObjExpr::new(ax_id, InliningBuf::new()).expr().rc()
                    }),
                }
            },

            Self::UniverseFormation => {
                let Some(uni_id) = ctx.std_objs.universe else {
                    return InferenceResult::Conflict
                };

                let [InfArg::Expr(j)] = args else {
                    return InferenceResult::Conflict
                };

                let Expr::Nat(j) = j.as_ref() else {
                    return InferenceResult::Conflict
                };

                let j = *j;

                let Expr::Obj(goal_uni) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if goal_uni.id() != uni_id {
                    return InferenceResult::Conflict
                }

                let [k] = goal_uni.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Expr::Nat(k) = k.as_ref() else {
                    return InferenceResult::Conflict
                };

                let k = *k;

                if j >= k {
                    return InferenceResult::Conflict
                }

                InferenceResult::Ok {
                    subgoals: Vec::new(),
                    validation: Validation::dynamic(move |_| {
                        ObjExpr::new(uni_id, [
                            Expr::Nat(j).rc()
                        ].into_iter().collect()).expr().rc()
                    })
                }
            },

            Self::UniverseEquality => {
                let Some(uni_id) = ctx.std_objs.universe else {
                    return InferenceResult::Conflict
                };

                let Some(eq_id) = ctx.std_objs.eq else {
                    return InferenceResult::Conflict
                };

                let Some(ax_id) = ctx.std_objs.ax else {
                    return InferenceResult::Conflict
                };

                if !args.is_empty() {
                    return InferenceResult::Conflict
                }

                let Expr::Obj(goal_eq) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if goal_eq.id() != eq_id {
                    return InferenceResult::Conflict
                }

                let [uni_k, uni_j1, uni_j2] = goal_eq.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                if uni_j1 != uni_j2 {
                    return InferenceResult::Conflict
                }

                let uni_j = uni_j1;

                let Expr::Obj(uni_j) = uni_j.as_ref() else {
                    return InferenceResult::Conflict
                };

                if uni_j.id() != uni_id {
                    return InferenceResult::Conflict
                }

                let [j] = uni_j.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Expr::Nat(j) = j.as_ref() else {
                    return InferenceResult::Conflict
                };

                let j = *j;

                let Expr::Obj(uni_k) = uni_k.as_ref() else {
                    return InferenceResult::Conflict
                };

                if uni_k.id() != uni_id {
                    return InferenceResult::Conflict
                }

                let [k] = uni_k.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Expr::Nat(k) = k.as_ref() else {
                    return InferenceResult::Conflict
                };

                let k = *k;

                if j >= k {
                    return InferenceResult::Conflict
                }

                InferenceResult::Ok {
                    subgoals: Vec::new(),
                    validation: Validation::dynamic(move |_| {
                        ObjExpr::new(ax_id, InliningBuf::new()).expr().rc()
                    }),
                }
            },

            Self::Cumulativity => {
                let Some(uni_id) = ctx.std_objs.universe else {
                    return InferenceResult::Conflict
                };

                let Some(eq_id) = ctx.std_objs.eq else {
                    return InferenceResult::Conflict
                };

                let Some(ax_id) = ctx.std_objs.ax else {
                    return InferenceResult::Conflict
                };

                let [InfArg::Expr(j)] = args else {
                    return InferenceResult::Conflict
                };

                let Expr::Nat(j) = j.as_ref() else {
                    return InferenceResult::Conflict
                };

                let j = *j;

                let Expr::Obj(goal_eq) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if goal_eq.id() != eq_id {
                    return InferenceResult::Conflict
                }

                let [uni_k, t1, t2] = goal_eq.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                if t1 != t2 {
                    return InferenceResult::Conflict
                }

                let Expr::Obj(uni_k) = uni_k.as_ref() else {
                    return InferenceResult::Conflict
                };

                if uni_k.id() != uni_id {
                    return InferenceResult::Conflict
                }

                let [k] = uni_k.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Expr::Nat(k) = k.as_ref() else {
                    return InferenceResult::Conflict
                };

                let k = *k;

                if j > k {
                    return InferenceResult::Conflict
                }

                InferenceResult::Ok {
                    subgoals: vec![
                        Sequent::new(
                            goal.hys().clone(),
                            ObjExpr::new(eq_id, [
                                ObjExpr::new(uni_id, [
                                    Expr::Nat(j).rc()
                                ].into_iter().collect()).expr().rc(),
                                t1.clone(),
                                t1.clone(),
                            ].into_iter().collect()).expr().rc()
                        )
                    ],
                    validation: Validation::dynamic(move |_| {
                        ObjExpr::new(ax_id, InliningBuf::new()).expr().rc()
                    }),
                }
            },

            Self::IsectMemberFormation => {
                let [InfArg::Expr(j), InfArg::Var(x)] = args else {
                    return InferenceResult::Conflict
                };

                if !matches!(j.as_ref(), Expr::Nat(_)) {
                    return InferenceResult::Conflict
                }

                let Expr::Obj(isect) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if Some(isect.id()) != ctx.std_objs.isect {
                    return InferenceResult::Conflict
                }

                let [s_ty, t_ty] = isect.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                let Expr::Bound(t_ty) = t_ty.as_ref() else {
                    return InferenceResult::Conflict
                };

                let Some((hys_with_s_ty, s_ty_hy_id)) = goal.hys().clone()
                    .with_appended(Hypothesis::new(
                        x.clone(), 
                        s_ty.clone(),
                        Visibility::Hidden
                    ))
                else {
                    return InferenceResult::Conflict
                };

                let s_ty_hy_expr = Expr::Hy(s_ty_hy_id).rc();
                let t_ty_subst = t_ty.body(&s_ty_hy_expr);

                let Some(uni_id) = ctx.std_objs.universe else {
                    return InferenceResult::Conflict
                };

                let Some(eq_id) = ctx.std_objs.eq else {
                    return InferenceResult::Conflict
                };

                InferenceResult::Ok {
                    subgoals: vec![
                        Sequent::new(
                            hys_with_s_ty,
                            t_ty_subst
                        ),
                        Sequent::new(
                            goal.hys().clone(),
                            ObjExpr::new(eq_id, [
                                ObjExpr::new(uni_id, [
                                    j.clone()
                                ].into_iter().collect()).expr().rc(),
                                s_ty.clone(),
                                s_ty.clone()
                            ].into_iter().collect()).expr().rc()
                        )
                    ],
                    validation: Validation::Static(|sub_theorems| {
                        sub_theorems[0].extract().clone()
                    }),
                }
            },

            Self::DirectComputation => {
                let [InfArg::Expr(tag_c_ty)] = args else {
                    return InferenceResult::Conflict
                };

                if &tag_c_ty.remove_tags_or_clone() != goal.concl() {
                    return InferenceResult::Conflict
                };

                InferenceResult::Ok {
                    subgoals: vec![
                        Sequent::new(
                            goal.hys().clone(),
                            tag_c_ty.reduce_at_tags_or_clone(ctx)
                        )
                    ],
                    validation: Validation::Static(|sub_theorems| {
                        sub_theorems[0].extract().clone()
                    })
                }
            },

            Self::ReverseDirectComputation => {
                let [InfArg::Expr(tag_c_ty)] = args else {
                    return InferenceResult::Conflict
                };
                
                if &tag_c_ty.reduce_at_tags_or_clone(ctx) != goal.concl() {
                    return InferenceResult::Conflict
                };

                InferenceResult::Ok {
                    subgoals: vec![
                        Sequent::new(
                            goal.hys().clone(),
                            tag_c_ty.remove_tags_or_clone()
                        )
                    ],
                    validation: Validation::Static(|sub_theorems| {
                        sub_theorems[0].extract().clone()
                    }),
                }
            },
            
            Self::DirectComputationHypothesis => {
                let [InfArg::Expr(i), InfArg::Expr(tag_t_ty)] = args else {
                    return InferenceResult::Conflict
                };
                
                let Some(i) = i.reduce_or_clone(ctx, ReductionSteps::Infinite).as_hy_pos() else {
                    return InferenceResult::Conflict
                };

                let Ok(HypothesisEntryRef { id: _, hy }) = goal.hys().get_any(i) else {
                    return InferenceResult::Conflict
                };

                if &tag_t_ty.remove_tags_or_clone() != hy.ty() {
                    return InferenceResult::Conflict
                };

                let reduced = tag_t_ty.reduce_at_tags_or_clone(ctx);

                let Some((hys, _)) = goal.hys().clone().with_ty_replaced(i, reduced) else {
                    return InferenceResult::Conflict
                };

                InferenceResult::Ok {
                    subgoals: vec![
                        Sequent::new(
                            hys,
                            goal.concl().clone()
                        )
                    ],
                    validation: Validation::Static(|sub_theorems| {
                        sub_theorems[0].extract().clone()
                    })
                }
            },
            
            Self::ReverseDirectComputationHypothesis => {
                let [InfArg::Expr(i), InfArg::Expr(tag_t_ty)] = args else {
                    return InferenceResult::Conflict
                };

                let Some(i) = i.reduce_or_clone(ctx, ReductionSteps::Infinite).as_hy_pos() else {
                    return InferenceResult::Conflict
                };

                let Ok(HypothesisEntryRef { id: _, hy }) = goal.hys().get_any(i) else {
                    return InferenceResult::Conflict
                };

                if &tag_t_ty.reduce_at_tags_or_clone(ctx) != hy.ty() {
                    return InferenceResult::Conflict
                };

                let tags_removed = tag_t_ty.remove_tags_or_clone();

                let Some((hys, _)) = goal.hys().clone().with_ty_replaced(i, tags_removed) else {
                    return InferenceResult::Conflict
                };

                InferenceResult::Ok {
                    subgoals: vec![
                        Sequent::new(
                            hys,
                            goal.concl().clone()
                        )
                    ],
                    validation: Validation::Static(|sub_theorems| {
                        sub_theorems[0].extract().clone()
                    })
                }
            },
            
            Self::Lemma => {
                let [InfArg::ProofResult { concl, extract }] = args else {
                    return InferenceResult::Conflict
                };
                
                if concl != goal.concl() {
                    return InferenceResult::Conflict
                }

                InferenceResult::Ok {
                    subgoals: Vec::new(),
                    validation: Validation::dynamic({
                        let extract = extract.clone();
                        move |_| extract
                    }),
                }
            },
            
            Self::Extract => {
                let [InfArg::ProofResult { concl, extract }] = args else {
                    return InferenceResult::Conflict
                };

                let Expr::Obj(obj_expr) = goal.concl().as_ref() else {
                    return InferenceResult::Conflict
                };

                if Some(obj_expr.id()) != ctx.std_objs.eq {
                    return InferenceResult::Conflict
                }

                let [ty, lhs, rhs] = obj_expr.args().as_ref() else {
                    return InferenceResult::Conflict
                };

                if lhs != rhs || lhs != extract || ty != concl {
                    return InferenceResult::Conflict
                }

                let Some(ax_id) = ctx.std_objs.ax else {
                    return InferenceResult::Conflict
                };

                InferenceResult::Ok {
                    subgoals: Vec::new(),
                    validation: Validation::dynamic(move |_| {
                        ObjExpr::new(ax_id, InliningBuf::new()).expr().rc()
                    }),
                }
            },
        }
    }
}
