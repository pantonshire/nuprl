use std::{rc::Rc, collections::BTreeMap};

use rkyv::{Archive, Serialize, Deserialize};

use crate::{unif_var::UnifVarIndex, object_id::ObjectId};

use super::{expr::{RcExpr, Expr, PlaceholderConflict}, library::{ResolveError, Resolver}};

#[derive(Archive, Serialize, Deserialize, Debug)]
pub struct ExprKindDefParam {
    name: Rc<str>,
    principal: bool,
}

impl ExprKindDefParam {
    pub fn new(name: Rc<str>, principal: bool) -> Self {
        Self { name, principal }
    }

    pub fn principal(&self) -> bool {
        self.principal
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct ExprKindDef {
    params: Rc<[ExprKindDefParam]>,
    reductions: Rc<[BetaReduction]>,
}

impl ExprKindDef {
    pub fn new(params: Rc<[ExprKindDefParam]>, reductions: Rc<[BetaReduction]>) -> Self {
        Self { params, reductions }
    }

    pub fn set_reductions(&mut self, reductions: Rc<[BetaReduction]>) {
        self.reductions = reductions
    }

    pub fn params(&self) -> &Rc<[ExprKindDefParam]> {
        &self.params
    }

    pub fn reductions(&self) -> &[BetaReduction] {
        &self.reductions
    }
}

#[derive(Archive, Serialize, Deserialize, Debug)]
pub struct BetaReduction {
    target: RcExpr,
    reduced: RcExpr,
}

 // FIXME: move more unification logic out of `Expr::reduce` and into here
impl BetaReduction {
    pub fn new(target: RcExpr, reduced: RcExpr) -> Self {
        Self { target, reduced }
    }

    pub fn target(&self) -> &RcExpr {
        &self.target
    }

    pub fn reduced(&self, placeholder_vals: &BTreeMap<UnifVarIndex, RcExpr>) -> Option<RcExpr> {
        self.reduced.subst_placeholders_or_clone(placeholder_vals).ok()
    }

    pub fn resolve(&self, subject_id: ObjectId, resolver: &mut Resolver)
        -> Result<Self, ResolveError>
    {
        let target = self.target.resolve(resolver)?;
        let reduced = self.reduced.resolve(resolver)?;

        // eprintln!("{} => {}", target, reduced);

        match target.as_ref() {
            Expr::Obj(obj) if obj.id() == subject_id => (),
            _ => return Err(ResolveError::BadBetaRule),
        }

        let mut depths = BTreeMap::new();

        // Check that all occurrences of the same placeholder variable are at the same depth (bound
        // the same number of times). Use the same `depths` buffer for checking both the `target`
        // and the `reduced` to check that this condition is upheld across the two expressions, as
        // well as just in each expression individually.
        let placeholder_conflict = target
            .placeholder_conflict::<true>(&mut depths)
            .and_then(|_| reduced.placeholder_conflict::<false>(&mut depths));

        // FIXME: return the conflict as part of the error
        if let Err(conflict) = placeholder_conflict {
            match conflict {
                PlaceholderConflict::Depth { placeholder: _, expected_depth: _, actual_depth: _ } => {
                    // eprintln!(
                    //     "placeholder {} used at depths {} and {}",
                    //     placeholder.0,
                    //     expected_depth.get(),
                    //     actual_depth.get()
                    // );
                },
                PlaceholderConflict::FirstOccurrenceInSubst { placeholder: _ } => {
                    // eprintln!(
                    //     "placeholder {} first occurs in a substitution",
                    //     placeholder.0
                    // );
                }
            }

            return Err(ResolveError::BadBetaRule);
        }

        Ok(BetaReduction::new(target, reduced))
    }
}
