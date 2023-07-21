use std::rc::Rc;

use rkyv::{Archive, Serialize, Deserialize};

use crate::{utils::InliningBuf, object_id::ObjectId};

use super::{
    expr::{RcExpr, Expr},
    sequent::{Sequent, SequentRef},
    object::ObjectKind,
    library::{ResolveError, Resolver, Context},
    proof::TheoremRef,
    hypothesis::Hypotheses, inf_def::InfDef, inf_intrinsic::InfIntrinsic,
};

#[derive(Clone, Copy, Debug)]
pub enum InfRuleObj<'a> {
    Def(&'a InfDef),
    Intrinsic(&'a InfIntrinsic),
}

impl<'a> InfRuleObj<'a> {
    pub fn params(self) -> InliningBuf<InfParamKind, 8> {
        match self {
            InfRuleObj::Def(def) => {
                def.param_kinds()
            },
            InfRuleObj::Intrinsic(intrinsic) => {
                intrinsic
                    .params()
                    .iter()
                    .copied()
                    .collect()
            },
        }
    }

    pub fn apply(self, ctx: Context, args: &[InfArg], goal: SequentRef) -> InferenceResult {
        match self {
            InfRuleObj::Def(def) => def.apply(ctx, args, goal),
            InfRuleObj::Intrinsic(intrinsic) => intrinsic.apply(ctx, args, goal),
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub enum InfParamKind {
    Expr,
    Var,
    ProofResult,
}

#[derive(Clone, Debug)]
pub struct UnresolvedInferenceRule {
    id: ObjectId,
    args: Box<[RcExpr]>,
}

impl UnresolvedInferenceRule {
    pub fn new(id: ObjectId, args: Box<[RcExpr]>) -> Self {
        Self { id, args }
    }
    
    pub fn id(&self) -> ObjectId {
        self.id
    }
    
    pub fn resolve(
        &self,
        resolver: &mut Resolver,
        hys: &Hypotheses
    ) -> Result<InferenceRule, ResolveError>
    {
        let obj = resolver.resolve(self.id)?;
        let Some(inf) = obj.as_inf() else {
            return  Err(ResolveError::ExpectedInfRule(obj.path().clone()))
        };

        let params = inf.params();

        if self.args.len() != params.len() {
            return Err(ResolveError::BadArgCount {
                path: obj.path().clone(),
                params: params.len(),
                args: self.args.len(),
            })
        }

        let args = params
            .iter()
            .zip(self.args.iter())
            .enumerate()
            .map(|(i, (param, arg))| {
                match param {
                    InfParamKind::Expr => {
                        let expr = arg
                            .apply_hypotheses_or_clone(hys)
                            .resolve(resolver)?;

                        Ok(InfArg::Expr(expr))
                    },
                    
                    InfParamKind::Var => match arg.as_ref() {
                        Expr::Free(free) => {
                            Ok(InfArg::Var(free.clone()))
                        },
                        _ => Err(ResolveError::BadArg {
                            path: obj.path().to_owned(),
                            arg_num: i,
                            expected: "a variable name",
                        }),
                    },

                    InfParamKind::ProofResult => match arg.as_ref() {
                        Expr::Obj(thm_obj) if thm_obj.args().is_empty() => {
                            let thm_obj = resolver.resolve(thm_obj.id())?;
                            
                            let ObjectKind::Thm(thm) = thm_obj.kind() else {
                                return Err(ResolveError::BadArg {
                                    path: obj.path().to_owned(),
                                    arg_num: i,
                                    expected: "the name of a theorem",
                                })
                            };

                            let Some(extract) = thm.extract() else {
                                return Err(ResolveError::InvalidTheoremAsDef(thm_obj.path().clone()))
                            };

                            Ok(InfArg::ProofResult {
                                concl: thm.goal().clone(),
                                extract: extract.clone(),
                            })
                        },
                        _ => Err(ResolveError::BadArg {
                            path: obj.path().to_owned(),
                            arg_num: i,
                            expected: "the name of a theorem",
                        }),
                    },
                }
            })
            .collect::<Result<_, _>>()?;

        Ok(InferenceRule { id: self.id, args })
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub enum InfArg {
    Expr(RcExpr),
    Var(Rc<str>),
    ProofResult {
        concl: RcExpr,
        extract: RcExpr,
    },
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct InferenceRule {
    id: ObjectId,
    args: InliningBuf<InfArg, 5>,
}

impl InferenceRule {
    pub fn id(&self) -> ObjectId {
        self.id
    }

    pub fn args(&self) -> &[InfArg] {
        &self.args
    }
}

pub enum InferenceResult {
    Ok {
        subgoals: Vec<Sequent>,
        validation: Validation,
    },
    Conflict,
}

type DynValidationFn = dyn FnOnce(&[TheoremRef]) -> RcExpr;

pub enum Validation {
    Static(fn(&[TheoremRef]) -> RcExpr),
    Dynamic(Box<DynValidationFn>),
}

impl Validation {
    pub fn dynamic<F>(f: F) -> Self
    where
        F: FnOnce(&[TheoremRef]) -> RcExpr + 'static
    {
        Self::Dynamic(Box::new(f))
    }

    pub fn eval(self, sub_theorems: &[TheoremRef]) -> RcExpr {
        match self {
            Self::Static(f) => f(sub_theorems),
            Self::Dynamic(f) => f(sub_theorems),
        }
    }
}
