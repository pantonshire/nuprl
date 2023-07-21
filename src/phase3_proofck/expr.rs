use std::{
    rc::Rc,
    slice,
    borrow::Borrow,
    ops::Deref,
    fmt::{self, Write},
    collections::{BTreeSet, BTreeMap, btree_map},
};

use rkyv::{Archive, Serialize, Deserialize};

use crate::{
    de_bruijn::{DeBruijnIndex, DeBruijnCmp},
    unif_var::{UnifVarIndex, UnifVarKind},
    utils::{InliningBuf, IntoResultOk, Bot},
    object_id::ObjectId,
};

use super::{
    var_names::NameAssignments,
    hypothesis::{HypothesisId, Hypotheses},
    library::{Resolver, ResolveError, Context},
    object::ObjectKind,
    definition::DeltaReductionError,
};

pub type RcExpr = Rc<Expr>;

#[derive(Archive, Serialize, Deserialize, PartialEq, Eq, Debug)]
pub enum Expr {
    Var(Var),
    Hy(HypothesisId),
    Tok(Rc<str>),
    Nat(u64),
    Bound(Bound),
    UnifVar(UnifVar),
    Subst(Subst),
    Tag(Tag),
    Obj(ObjExpr),
    Free(Rc<str>),
}

impl Expr {
    pub fn rc(self) -> RcExpr {
        Rc::new(self)
    }

    fn fold<T, S, FP, FF>(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        state: &mut S,
        map_parent: FP,
        fold_init: T,
        mut fold_fn: FF,
    ) -> T
    where
        FP: for<'a> FnOnce(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Option<T>,
        FF: for<'a> FnMut(T, &'a Rc<Self>, DeBruijnIndex, &mut S) -> T,
    {
        if let Some(t) = map_parent(self, depth, state) {
            return t;
        }

        match self.as_ref() {
            Self::Var(var) => {
                // FIXME: recurse on mapping
                if var.mapping().is_empty() {
                    fold_init
                } else {
                    todo!()
                }
            },
            Self::Hy(_) => fold_init,
            Self::Tok(_) => fold_init,
            Self::Nat(_) => fold_init,
            Self::Bound(bound) => {
                fold_fn(fold_init, bound.body_raw(), depth + 1, state)
            },
            Self::UnifVar(_) => fold_init,
            Self::Subst(subst) => {
                let acc = fold_fn(fold_init, subst.bound_raw(), depth + subst.num_args(), state);
                subst.args()
                    .iter()
                    .fold(acc, |acc, expr| fold_fn(acc, expr, depth, state))
            },
            Self::Obj(obj) => {
                obj.args()
                    .iter()
                    .fold(fold_init, |acc, item| fold_fn(acc, item, depth, state))
            },
            Self::Tag(tag) => {
                fold_fn(fold_init, tag.body(), depth, state)
            },
            Self::Free(_) => fold_init,
        }
    }

    fn alter_pre_order<E, S, FP, FC>(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        state: &mut S,
        alter_parent: FP,
        alter_child: FC,
    ) -> Result<Option<Rc<Self>>, E>
    where
        FP: for<'a> FnOnce(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Result<Option<Rc<Self>>, E>,
        FC: for<'a> FnMut(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Result<Option<Rc<Self>>, E>,
    {
        let parent = alter_parent(self, depth, state)?;

        parent
            .as_ref()
            .unwrap_or(self)
            .alter_children(depth, state, alter_child)?
            .or(parent)
            .ok()
    }

    fn alter_pre_order_infallible<S, FP, FC>(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        state: &mut S,
        alter_parent: FP,
        mut alter_child: FC,
    ) -> Option<Rc<Self>>
    where
        FP: for<'a> FnOnce(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Option<Rc<Self>>,
        FC: for<'a> FnMut(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Option<Rc<Self>>,
    {
        match self.alter_pre_order(
            depth,
            state,
            |parent, depth, state| Ok::<_, Bot>(alter_parent(parent, depth, state)),
            |child, depth, state| Ok::<_, Bot>(alter_child(child, depth, state))
        ) {
            Ok(res) => res,
            Err(bot) => bot.elim(),
        }
    }

    fn alter_post_order<E, S, FP, FC>(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        state: &mut S,
        alter_parent: FP,
        alter_child: FC,
    ) -> Result<Option<Rc<Self>>, E>
    where
        FP: for<'a> FnOnce(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Result<Option<Rc<Self>>, E>,
        FC: for<'a> FnMut(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Result<Option<Rc<Self>>, E>,
    {
        let parent = self.alter_children(depth, state, alter_child)?;

        alter_parent(parent.as_ref().unwrap_or(self), depth, state)?
            .or(parent)
            .ok()
    }

    fn alter_post_order_infallible<S, FP, FC>(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        state: &mut S,
        alter_parent: FP,
        mut alter_child: FC,
    ) -> Option<Rc<Self>>
    where
        FP: for<'a> FnOnce(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Option<Rc<Self>>,
        FC: for<'a> FnMut(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Option<Rc<Self>>,
    {
        match self.alter_post_order(
            depth,
            state,
            |parent, depth, state| Ok::<_, Bot>(alter_parent(parent, depth, state)),
            |child, depth, state| Ok::<_, Bot>(alter_child(child, depth, state))
        ) {
            Ok(res) => res,
            Err(bot) => bot.elim(),
        }
    }

    fn alter_children<E, S, FC>(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        state: &mut S,
        mut alter_child: FC,
    ) -> Result<Option<Rc<Self>>, E>
    where
        FC: for<'a> FnMut(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Result<Option<Rc<Self>>, E>,
    {
        match self.as_ref() {
            Self::Var(var) => {
                if var.mapping().is_empty() {
                    Ok(None)
                } else {
                    Self::alter_mapping(alter_child, var.mapping(), depth, state)?
                        .map(|mapping| Var::new(var.index(), mapping).expr().rc())
                        .ok()
                }
            },
            Self::Hy(_) => Ok(None),
            Self::Tok(_) => Ok(None),
            Self::Nat(_) => Ok(None),
            Self::Bound(bound) => {
                alter_child(bound.body_raw(), depth + 1, state)?
                    .map(|body| Bound::new(bound.var().clone(), body).expr().rc())
                    .ok()
            },
            Self::UnifVar(_) => Ok(None),
            Self::Subst(subst) => {
                let mut any_altered = false;

                let bound = match alter_child(subst.bound_raw(), depth + subst.num_args(), state)? {
                    Some(bound) => {
                        any_altered = true;
                        bound
                    },
                    None => subst.bound_raw().clone(),
                };

                let args = subst
                    .args()
                    .iter()
                    .map(|arg| alter_child(arg, depth, state)
                        .map(|altered| match altered {
                            Some(altered_arg) => {
                                any_altered = true;
                                altered_arg
                            },
                            None => arg.clone(),
                        }))
                    .collect::<Result<_, _>>()?;

                any_altered.then(|| {
                    Subst::new(bound, args).expr().rc()
                }).ok()
            },
            Self::Obj(obj) => {
                // FIXME: apply this `any_altered` strategy to `alter_mapping` (and perhaps
                // `alter_children`)
                let mut any_altered = false;

                let args = obj
                    .args()
                    .iter()
                    .map(|arg| alter_child(arg, depth, state)
                        .map(|altered| match altered {
                            Some(altered_arg) => {
                                any_altered = true;
                                altered_arg
                            },
                            None => arg.clone(),
                        }))
                    .collect::<Result<_, _>>()?;

                any_altered.then(|| {
                    ObjExpr::new(obj.id(), args).expr().rc()
                }).ok()
            },
            Self::Tag(tag) => {
                alter_child(tag.body(), depth, state)?
                    .map(|body| Tag::new(tag.steps(), body).expr().rc())
                    .ok()
            },
            Self::Free(_) => Ok(None),
        }
    }

    fn alter_mapping<E, S, FC>(
        mut alter_child: FC,
        mapping: &SecondOrderMapping,
        depth: DeBruijnIndex,
        state: &mut S
    ) -> Result<Option<SecondOrderMappingBuf>, E>
    where
        FC: for<'a> FnMut(&'a Rc<Self>, DeBruijnIndex, &mut S) -> Result<Option<Rc<Self>>, E>,
    {
        let children = mapping
            .iter()
            .map(|child| alter_child(child, depth, state)
                .map(|altered| (child, altered)))
            .collect::<Result<Vec<_>, _>>()?;

        children
            .iter()
            .any(|(_original, altered)| altered.is_some())
            .then(|| children
                .into_iter()
                .map(|(original, altered)| altered.unwrap_or_else(|| original.clone()))
                .collect::<SecondOrderMappingBuf>())
            .ok()
    }

    pub fn subst_all<T>(self: &Rc<Self>, exprs: &[T]) -> Rc<Self>
    where
        T: Borrow<Rc<Self>>,
    {
        let mut this = self.clone();

        for (depth, expr) in exprs
            .iter()
            .enumerate()
            .map(|(i, expr)| (DeBruijnIndex::new(exprs.len() - i - 1), expr))
        {
            this = this.subst_at_depth_or_clone(depth, expr.borrow());
        }

        this
    }

    pub fn subst_or_clone(self: &Rc<Self>, expr: &Rc<Self>) -> Rc<Self> {
        self.subst(expr).unwrap_or_else(|| self.clone())
    }

    /// Replaces De Bruijn index 0 with the given expression.
    pub fn subst(self: &Rc<Self>, expr: &Rc<Self>) -> Option<Rc<Self>> {
        self.subst_at_depth(DeBruijnIndex::ZERO, expr)
    }

    pub fn subst_at_depth_or_clone(self: &Rc<Self>, depth: DeBruijnIndex, expr: &Rc<Self>) -> Rc<Self> {
        self.subst_at_depth(depth, expr).unwrap_or_else(|| self.clone())
    }

    // Replaces De Bruijn index `depth` with the given expression.
    pub fn subst_at_depth(self: &Rc<Self>, depth: DeBruijnIndex, expr: &Rc<Self>) -> Option<Rc<Self>> {
        self.subst_rec(depth, expr)
    }

    fn subst_rec(self: &Rc<Self>, depth: DeBruijnIndex, expr: &Rc<Self>) -> Option<Rc<Self>> {
        // Substitution is post-order; we want to substitute into the children of the original node
        // then substitute into the original node itself, rather than substituting into the
        // original node first then substituting into the body of the `expr` we have substituted
        // in.
        self.alter_post_order_infallible(
            depth,
            &mut (),
            |parent, depth, _| match parent.as_ref() {
                Self::Var(var) => match var.index().compare(depth) {
                    DeBruijnCmp::Lt(_, _) => None,
                    DeBruijnCmp::Eq(_, _) => {
                        if var.mapping().is_empty() {
                            Some(expr.increment_db_indices_by_or_clone(depth.get()))
                        } else {
                            // Incrementing indices by the current depth is handled by
                            // `apply_mapping` (hence why we pass it the current depth).
                            Some(expr.apply_mapping_or_clone(var.mapping(), depth))
                        }
                    },
                    DeBruijnCmp::Gt(var_index, _) => {
                        Some(Var::new(
                            var_index.decrement(),
                            var.mapping().clone()
                        ).expr().rc())
                    },
                },
                _ => None,
            },
            |child, depth, _| child.subst_rec(depth, expr)
        )
    }

    fn increment_db_indices_by_or_clone(self: &Rc<Self>, increment: usize) -> Rc<Self> {
        self.increment_db_indices_by(increment).unwrap_or_else(|| self.clone())
    }

    fn increment_db_indices_by(self: &Rc<Self>, increment: usize) -> Option<Rc<Self>> {
        if increment == 0 {
            None
        } else {
            self.increment_db_indices_by_rec(DeBruijnIndex::ZERO, increment)
        }
    }

    fn increment_db_indices_by_rec(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        increment: usize
    ) -> Option<Rc<Self>>
    {
        self.alter_post_order_infallible(
            depth,
            &mut (),
            |parent, depth, _| match parent.as_ref() {
                Self::Var(var) if var.index() >= depth => {
                    Some(Var::new(
                        var.index() + increment,
                        var.mapping().clone()
                    ).expr().rc())
                },
                _ => None,
            },
            |child, depth, _| child.increment_db_indices_by_rec(depth, increment)
        )
    }

    fn apply_mapping_or_clone(
        self: &Rc<Self>,
        mapping: &SecondOrderMapping,
        outer_depth: DeBruijnIndex
    ) -> Rc<Self>
    {
        self.apply_mapping(mapping, outer_depth).unwrap_or_else(|| self.clone())
    }

    fn apply_mapping(
        self: &Rc<Self>,
        mapping: &SecondOrderMapping,
        outer_depth: DeBruijnIndex
    ) -> Option<Rc<Self>>
    {
        let (dep_body, num_bindings) = self.nested_dep_body_raw(mapping.len());
        let mapping = mapping.subslice(num_bindings);
        dep_body.apply_mapping_rec(DeBruijnIndex::ZERO, mapping, outer_depth)
    }

    fn apply_mapping_rec(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        mapping: &SecondOrderMapping,
        outer_depth: DeBruijnIndex
    ) -> Option<Rc<Self>>
    {
        self.alter_pre_order_infallible(
            depth,
            &mut (),
            |parent, depth, _| match parent.as_ref() {
                // Subtract the variable by the current depth to get an index into the bindings
                // slice.
                Self::Var(var) => match var.index().checked_sub(depth) {
                    // Attempt to index into the `bindings` slice with `index - depth`.
                    Some(index) => match mapping.map(index) {
                        Some(binding) => {
                            // Some(ExprKind::Var(*binding + depth).rc())
                            Some(binding.increment_db_indices_by_or_clone(depth.get()))
                        },
                        // If the variable is not covered by the `bindings` slice, subtract the
                        // length of `bindings` from it (since this is the number of
                        // `ExprKind::Dep` expressions we are removing) and add `outer_depth` to
                        // it (the depth we are at in `subst_def_param_rec`) so that it still
                        // refers to the same binding expression after this operation.
                        None => {
                            // In this case, `index - depth >= bindings.len()` must hold because
                            // `get` returned `None`. `depth >= 0`, so `index >= index - depth`.
                            // Therefore, `index >= bindings.len()`, so this cannot underflow.
                            let unbound = var.index().get() - mapping.len();
                            let rebound = DeBruijnIndex::new(unbound + outer_depth.get());
                            Some(Var::new(rebound, var.mapping().clone()).expr().rc())
                        },
                    },
                    None => None,
                },
                // If the variable is less than the depth, then the variable should not be rebound.
                _ => None,
            },
            |child, depth, _| child.apply_mapping_rec(depth, mapping, outer_depth)
        )
    }

    fn nested_dep_body_raw<'a>(self: &'a Rc<Self>, max_nest: usize) -> (&'a Rc<Self>, usize) {
        let mut expr = self;
        for i in 0..max_nest {
            expr = match expr.as_ref() {
                Expr::Bound(bound) => bound.body_raw(),
                _ => return (expr, i),
            };
        }
        (expr, max_nest)
    }

    pub fn bind_hypothesis_or_clone(self: &Rc<Self>, hy: HypothesisId) -> Rc<Self> {
        self.bind_hypothesis(hy).unwrap_or_else(|| self.clone())
    }

    /// Replaces the given hypothesis with first-order De Bruijn index 0.
    pub fn bind_hypothesis(self: &Rc<Self>, hy: HypothesisId) -> Option<Rc<Self>> {
        self.bind_hypothesis_rec(DeBruijnIndex::ZERO, hy)
    }

    fn bind_hypothesis_rec(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        hy: HypothesisId
    ) -> Option<Rc<Self>>
    {
        self.alter_pre_order_infallible(
            depth,
            &mut (),
            |parent, depth, _| match parent.as_ref() {
                // We are introducing a new variable, so we need to increment the indices greater
                // than or equal to that of the new variable by 1.
                Self::Var(var) if var.index() >= depth => {
                    Some(Var::new(
                        var.index() + 1,
                        var.mapping().clone()
                    ).expr().rc())
                },
                // Replace the hypothesis with a new first-order variable.
                Self::Hy(self_hy) if *self_hy == hy => {
                    Some(Var::first_order(depth).expr().rc())
                },
                _ => None,
            },
            |child, depth, _| child.bind_hypothesis_rec(depth, hy)
        )
    }

    pub fn contains_hypothesis(self: &Rc<Self>, hy: HypothesisId) -> bool {
        self.contains_hypothesis_rec(DeBruijnIndex::ZERO, hy)
    }

    fn contains_hypothesis_rec(self: &Rc<Self>, depth: DeBruijnIndex, hy: HypothesisId) -> bool {
        self.fold(
            depth,
            &mut (),
            |parent, _, _| match parent.as_ref() {
                Self::Hy(self_hy) => Some(*self_hy == hy),
                _ => None,
            },
            false,
            |acc, child, depth, _state| {
                acc || child.contains_hypothesis_rec(depth, hy)
            },
        )
    }

    pub fn contained_hypotheses(self: &Rc<Self>) -> BTreeSet<HypothesisId> {
        let mut hys = BTreeSet::new();
        self.contained_hypotheses_rec(DeBruijnIndex::ZERO, &mut hys);
        hys
    }

    fn contained_hypotheses_rec(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        hys: &mut BTreeSet<HypothesisId>
    ) {
        self.fold(
            depth,
            hys,
            |parent, _, hys| match parent.as_ref() {
                Self::Hy(self_hy) => {
                    hys.insert(*self_hy);
                    Some(())
                },
                _ => None,
            },
            (),
            |_acc, child, depth, hys| {
                child.contained_hypotheses_rec(depth, hys);
            },
        )
    }

    pub fn remove_tags_or_clone(self: &Rc<Self>) -> Rc<Self> {
        self.remove_tags().unwrap_or_else(|| self.clone())
    }

    pub fn remove_tags(self: &Rc<Self>) -> Option<Rc<Self>> {
        self.remove_tags_rec(DeBruijnIndex::ZERO)
    }

    fn remove_tags_rec(self: &Rc<Self>, depth: DeBruijnIndex) -> Option<Rc<Self>> {
        self.alter_pre_order_infallible(
            depth,
            &mut (),
            |parent, _, _| match parent.as_ref() {
                Self::Tag(tag) => Some(tag.body().clone()),
                _ => None,
            },
            |child, index, _| child.remove_tags_rec(index)
        )
    }

    pub fn contains_placeholders(self: &Rc<Self>) -> bool {
        self.contains_placeholders_rec(DeBruijnIndex::ZERO)
    }

    fn contains_placeholders_rec(self: &Rc<Self>, depth: DeBruijnIndex) -> bool {
        self.fold(
            depth,
            &mut (),
            |parent, _, _| match parent.as_ref() {
                Self::UnifVar(_) => Some(true),
                _ => None,
            },
            false,
            |acc, child, depth, _| {
                acc || child.contains_placeholders_rec(depth)
            }
        )
    }

    /// Check for any invalid placeholders occurring in the expression. The const `UNIF` parameter
    /// indicates whether or not unification will be performed on this expression (i.e.
    /// `unify_placeholders_rec` will be called), in which case additional checks will be
    /// performed.
    pub fn placeholder_conflict<const UNIF: bool>(
        self: &Rc<Self>,
        depths: &mut BTreeMap<UnifVarIndex, DeBruijnIndex>
    ) -> Result<(), PlaceholderConflict>
    {
        self.placeholder_conflict_rec::<UNIF>(DeBruijnIndex::ZERO, depths)
    }

    fn placeholder_conflict_rec<const UNIF: bool>(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        depths: &mut BTreeMap<UnifVarIndex, DeBruijnIndex>
    ) -> Result<(), PlaceholderConflict>
    {
        self.fold(
            depth,
            depths,
            |parent, depth, depths| match parent.as_ref() {
                // If the expression if a placeholder (unif var), we need to make sure that it
                // is at the same depth as every other occurrence of the same placeholder we
                // have seen so far.
                Self::UnifVar(unif_var) => {
                    match depths.entry(unif_var.index()) {
                        btree_map::Entry::Vacant(entry) => {
                            entry.insert(depth);
                            Some(Ok(()))
                        },
                        btree_map::Entry::Occupied(entry) => {
                            let other_depth = *entry.get();
                            if depth == other_depth {
                                Some(Ok(()))
                            } else {
                                Some(Err(PlaceholderConflict::Depth {
                                    placeholder: unif_var.index(),
                                    expected_depth: other_depth,
                                    actual_depth: depth,
                                }))
                            }
                        },
                    }
                },
                
                Self::Subst(subst) => {
                    // If the expression is a subst `[t]s`, we need to make sure that `s` contains
                    // no placeholders that we have not yet seen, since we will be applying
                    // (reducing) the subst as part of unification and we need to know the concrete
                    // values of the placeholders to do that. This constraint could be lifted if we
                    // did a more traditional unification (generate constraints then solve the
                    // constraints, rather than doing it all in one go).
                    if UNIF {
                        match subst.bound_raw().check_placeholders_all_in_map(depths) {
                            Ok(()) => None,
                            Err(err) => Some(Err(err)),
                        }
                    } else {
                        None
                    }
                },

                _ => None,
            },
            Ok(()),
            |acc, child, depth, depths| {
                match acc {
                    Ok(()) => child.placeholder_conflict_rec::<UNIF>(depth, depths),
                    Err(conflict) => Err(conflict),
                }
            }
        )
    }

    fn check_placeholders_all_in_map<V>(
        self: &Rc<Self>,
        map: &BTreeMap<UnifVarIndex, V>
    ) -> Result<(), PlaceholderConflict>
    {
        self.check_placeholders_all_in_map_rec(DeBruijnIndex::ZERO, map)
    }

    fn check_placeholders_all_in_map_rec<V>(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        map: &BTreeMap<UnifVarIndex, V>
    ) -> Result<(), PlaceholderConflict>
    {
        self.fold(
            depth,
            &mut (),
            |parent, _, _| match parent.as_ref() {
                Self::UnifVar(unif_var) => {
                    if map.contains_key(&unif_var.index()) {
                        Some(Ok(()))
                    } else {
                        Some(Err(PlaceholderConflict::FirstOccurrenceInSubst {
                            placeholder: unif_var.index(),
                        }))
                    }
                },
                _ => None,
            },
            Ok(()),
            |acc, child, depth, _| {
                match acc {
                    Ok(()) => child.check_placeholders_all_in_map_rec(depth, map),
                    Err(conflict) => Err(conflict),
                }
            }
        )
    }

    pub fn subst_placeholders_or_clone(
        self: &Rc<Self>,
        exprs: &BTreeMap<UnifVarIndex, Rc<Self>>
    ) -> Result<Rc<Self>, SubstPlaceholderError>
    {
        self.subst_placeholders(exprs)
            .map(|res| res.unwrap_or_else(|| self.clone()))
    }

    // N.B. this assumes that all placeholder values are at a suitable depth; no DB index
    // modification is performed. This is ok for unification, because at the moment we require that
    // placeholder variables are at the same depth in all occurrences.
    pub fn subst_placeholders(
        self: &Rc<Self>,
        exprs: &BTreeMap<UnifVarIndex, Rc<Self>>
    ) -> Result<Option<Rc<Self>>, SubstPlaceholderError>
    {
        self.subst_placeholders_rec(DeBruijnIndex::ZERO, exprs)
    }

    fn subst_placeholders_rec(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        exprs: &BTreeMap<UnifVarIndex, Rc<Self>>
    ) -> Result<Option<Rc<Self>>, SubstPlaceholderError>
    {
        self.alter_post_order(
            depth,
            &mut (),
            |parent, _depth, _| match parent.as_ref() {
                Self::UnifVar(unif_var) => {
                    match exprs.get(&unif_var.index()) {
                        Some(expr) => Ok(Some(expr.clone())),
                        None => Err(SubstPlaceholderError::NoConcreteValue {
                            name: unif_var.display_name().clone(),
                            index: unif_var.index(),
                        }),
                    }
                },
                Self::Subst(subst) => {
                    Ok(Some(subst.apply()))
                },
                _ => Ok(None),
            },
            |child, depth, _| child.subst_placeholders_rec(depth, exprs)
        )
    }

    /// Compare an expression containing unification placeholders with an expression with no
    /// unification placeholders, filling the given btree with values for the placeholders or
    /// returning an error containing two conflicting sub-expressions.
    pub fn unify_placeholders_rec(
        self: &Rc<Self>,
        other: &Rc<Self>,
        unified: &mut BTreeMap<UnifVarIndex, Rc<Self>>,
    ) -> Result<(), [Rc<Self>; 2]>
    {
        match (self.as_ref(), other.as_ref()) {
            (Self::Var(lhs), Self::Var(rhs)) => {
                if lhs.index() == rhs.index() && lhs.mapping().len() == rhs.mapping().len() {
                    for (lhs, rhs) in lhs.mapping().iter().zip(rhs.mapping().iter()) {
                        lhs.unify_placeholders_rec(rhs, unified)?;
                    }
                    Some(())
                } else {
                    None
                }
            },
            (Self::Hy(lhs), Self::Hy(rhs)) => {
                (lhs == rhs).then_some(())
            },
            (Self::Tok(lhs), Self::Tok(rhs)) => {
                (lhs == rhs).then_some(())
            },
            (Self::Nat(lhs), Self::Nat(rhs)) => {
                (*lhs == *rhs).then_some(())
            },
            (Self::Bound(lhs), Self::Bound(rhs)) => {
                lhs.body_raw().unify_placeholders_rec(rhs.body_raw(), unified)?;
                Some(())
            },
            (Self::UnifVar(lhs), rhs) => {
                match (lhs.kind(), rhs) {
                    (UnifVarKind::Any, _) | (UnifVarKind::Nat, Self::Nat(_)) => {
                        match unified.entry(lhs.index()) {
                            btree_map::Entry::Vacant(entry) => {
                                entry.insert(other.clone());
                                Some(())
                            },
                            btree_map::Entry::Occupied(entry) => {
                                (entry.get() == other).then_some(())
                            },
                        }
                    },
                    _ => None,
                }
            },
            (Self::Subst(lhs), _) => {
                // Prior checks performed by `placeholder_conflict` should ensure that every
                // placeholder in the `s` of the `[t]s` should have been visited and unified by
                // now, so we can substitute the concrete values of the placeholders into `s`.
                //
                // N.B. a better way to do this would be to generate constraints then solve them
                // in a separate step, since this wouldn't require that we have already unified all
                // of the placeholders in `s` before visiting this `[t]s` (although this would be
                // more expensive).
                let lhs_bound_subst = lhs
                    .bound_raw()
                    .subst_placeholders_or_clone(unified)
                    .unwrap();

                let lhs = Subst::new(
                    lhs_bound_subst,
                    lhs.args().clone()
                ).apply();

                lhs.unify_placeholders_rec(other, unified)?;

                Some(())
            },
            (Self::Obj(lhs), Self::Obj(rhs)) => {
                if lhs.id() == rhs.id() && lhs.num_args() == rhs.num_args() {
                    for (lhs, rhs) in lhs.args().iter().zip(rhs.args().iter()) {
                        lhs.unify_placeholders_rec(rhs, unified)?;
                    }
                    Some(())
                } else {
                    None
                }
            },
            (Self::Tag(lhs), Self::Tag(rhs)) => {
                if lhs.steps() == rhs.steps() {
                    lhs.body().unify_placeholders_rec(rhs.body(), unified)?;
                    Some(())
                } else {
                    None
                }
            },
            _ => None,
        }.ok_or_else(|| [self.clone(), other.clone()])
    }

    pub fn reduce_at_tags_or_clone(self: &Rc<Self>, ctx: Context) -> Rc<Self> {
        self.reduce_at_tags(ctx).unwrap_or_else(|| self.clone())
    }

    pub fn reduce_at_tags(self: &Rc<Self>, ctx: Context) -> Option<Rc<Self>> {
        self.reduce_at_tags_rec(ctx, DeBruijnIndex::ZERO)
    }

    fn reduce_at_tags_rec(self: &Rc<Self>, ctx: Context, depth: DeBruijnIndex) -> Option<Rc<Self>> {
        // Use post-order recursion because we want to reduce the innermost tags first.
        self.alter_post_order_infallible(
            depth,
            &mut (),
            |parent, _, _| match parent.as_ref() {
                // If the parent expression node is a tag, reduce it.
                Self::Tag(tag) => {
                    Some(tag.body().reduce_or_clone(ctx, tag.steps()))
                },
                // Otherwise, leave the parent expression node unchanged.
                _ => None,
            },
            // Recurse on the expression node's children. Since this is post-order, this will be
            // run *before* the parent is reduced.
            |child, index, _| child.reduce_at_tags_rec(ctx, index)
        )
    }

    pub fn reduce_or_clone(self: &Rc<Self>, ctx: Context, steps: ReductionSteps) -> Rc<Self> {
        self.reduce(ctx, steps).unwrap_or_else(|| self.clone())
    }

    pub fn reduce(self: &Rc<Self>, ctx: Context, steps: ReductionSteps) -> Option<Rc<Self>> {
        let mut steps = steps.decremented()?;
        let mut current = self.reduce_step(ctx)?;
        loop {
            (steps, current) = match steps.decremented() {
                Some(steps) => {
                    match current.reduce_step(ctx) {
                        Some(reduced) => (steps, reduced),
                        None => break Some(current),
                    }
                },
                None => break Some(current),
            };
        }
    }

    pub fn reduce_step_or_clone(self: &Rc<Self>, ctx: Context) -> Rc<Self> {
        self.reduce_step(ctx).unwrap_or_else(|| self.clone())
    }

    pub fn reduce_step(self: &Rc<Self>, ctx: Context) -> Option<Rc<Self>> {
        match self.as_ref() {
            Self::Obj(obj) => 'reduction: {
                let Some(lib_obj) = ctx.lib.get(obj.id()) else {
                    break 'reduction None
                };

                let ObjectKind::Exp(exprkind) = lib_obj.kind() else {
                    break 'reduction None
                };

                // Iterate over the principal arguments and try to reduce them.
                for (i, (_, arg)) in exprkind.params().iter()
                    .zip(obj.args().iter())
                    .enumerate()
                    .filter(|(_, (param, _))| param.principal())
                {
                    if let Some(arg_reduced) = arg.reduce_step(ctx) {
                        let args = obj.args()
                            .iter()
                            .enumerate()
                            .map(|(j, arg)| if i == j {
                                arg_reduced.clone()
                            } else {
                                arg.clone()
                            })
                            .collect();

                        break 'reduction Some(ObjExpr::new(
                            obj.id(),
                            args
                        ).expr().rc());
                    }
                }

                // Attempt to apply any hard-coded reductions, such as arithmetic.
                match (obj.id(), obj.args().as_ref()) {
                    (id, [arg]) if Some(id) == ctx.std_objs.neg => {
                        match arg.as_ref() {
                            Expr::Obj(obj) => match (obj.id(), obj.args().as_ref()) {
                                (id, [arg]) if Some(id) == ctx.std_objs.neg => {
                                    break 'reduction Some(arg.clone())
                                },
                                _ => (),
                            },
                            _ => (),
                        }
                    },
                    
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.add => {
                        match (lhs.as_signed_num(ctx), rhs.as_signed_num(ctx)) {
                            (Some(lhs), Some(rhs)) => {
                                if let Some(res) = lhs
                                    .checked_add(rhs)
                                    .and_then(|res| Self::from_signed_num(res, ctx))
                                {
                                    break 'reduction Some(res)
                                }
                            },
                            _ => (),
                        }
                    },

                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.mul => {
                        match (lhs.as_signed_num(ctx), rhs.as_signed_num(ctx)) {
                            (Some(lhs), Some(rhs)) => {
                                if let Some(res) = lhs
                                    .checked_mul(rhs)
                                    .and_then(|res| Self::from_signed_num(res, ctx))
                                {
                                    break 'reduction Some(res)
                                }
                            },
                            _ => (),
                        }
                    },

                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.div => {
                        match (lhs.as_signed_num(ctx), rhs.as_signed_num(ctx)) {
                            (Some(lhs), Some(rhs)) => {
                                let res = if rhs == 0 {
                                    Some(0)
                                } else {
                                    lhs.checked_div(rhs)
                                }.and_then(|res| Self::from_signed_num(res, ctx));

                                if let Some(res) = res {
                                    break 'reduction Some(res)
                                }
                            },
                            _ => (),
                        }
                    },

                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.rem => {
                        match (lhs.as_signed_num(ctx), rhs.as_signed_num(ctx)) {
                            (Some(lhs), Some(rhs)) => {
                                let res = if rhs == 0 {
                                    Some(0)
                                } else {
                                    lhs.checked_rem(rhs)
                                }.and_then(|res| Self::from_signed_num(res, ctx));

                                if let Some(res) = res {
                                    break 'reduction Some(res)
                                }
                            },
                            _ => (),
                        }
                    },

                    (id, [lhs, rhs, l_case, r_case]) if Some(id) == ctx.std_objs.compare_lt => {
                        if let (Some(lhs), Some(rhs)) = (lhs.as_signed_num(ctx), rhs.as_signed_num(ctx)) {
                            break 'reduction Some(if lhs < rhs {
                                l_case.clone()
                            } else {
                                r_case.clone()
                            })
                        }
                    },

                    (id, [lhs, rhs, l_case, r_case]) if Some(id) == ctx.std_objs.compare_eq => {
                        if let (Self::Tok(lhs), Self::Tok(rhs)) = (lhs.as_ref(), rhs.as_ref()) {
                            break 'reduction Some(if lhs == rhs {
                                l_case.clone()
                            } else {
                                r_case.clone()
                            })
                        }

                        if let (Some(lhs), Some(rhs)) = (lhs.as_signed_num(ctx), rhs.as_signed_num(ctx)) {
                            break 'reduction Some(if lhs == rhs {
                                l_case.clone()
                            } else {
                                r_case.clone()
                            })
                        }
                    },

                    _ => (),
                }

                let reductions = exprkind.reductions();

                // FIXME: try to avoid allocating lots of btrees; keep a single btree and
                // pass it as a recursion parameter?
                let mut unified = BTreeMap::new();
                
                for reduction in reductions.iter() {
                    unified.clear();

                    // FIXME: change types in library object to be new expression type
                    match reduction.target().unify_placeholders_rec(self, &mut unified) {
                        Ok(()) => {
                            // eprintln!("suitable rule found for {}:", obj.obj().path());
                            // for (key, val) in unified.iter() {
                            //     eprintln!("  {} => {}", key.0, val);
                            // }

                            if let Some(reduced) = reduction.reduced(&unified) {
                                break 'reduction Some(reduced);
                            }
                        },
                        Err([_e1, _e2]) => {
                            // eprintln!("conflict: {} != {}", e1, e2);
                        }
                    }
                }

                None
            },
            _ => None,
        }
    }

    fn as_signed_num(&self, ctx: Context) -> Option<i64> {
        match self {
            Expr::Nat(n) => i64::try_from(*n).ok(),
            Expr::Obj(obj) if Some(obj.id()) == ctx.std_objs.neg => match obj.args().as_ref() {
                [arg] => match arg.as_ref() {
                    Expr::Nat(n) => i64::try_from(*n).ok().and_then(|n| n.checked_neg()),
                    _ => None,
                },
                _ => None,
            },
            _ => None,
        }
    }

    fn from_signed_num(n: i64, ctx: Context) -> Option<Rc<Self>> {
        if n < 0 {
            match ctx.std_objs.neg {
                Some(neg_id) => {
                    Some(Self::Obj(ObjExpr::new(
                        neg_id,
                        [
                            Self::Nat(n.unsigned_abs()).rc()
                        ].into_iter().collect()
                    )).rc())
                },
                None => None,
            }
        } else {
            Some(Self::Nat(n.unsigned_abs()).rc())
        }
    }

    pub fn as_hy_pos(&self) -> Option<usize> {
        match self {
            Self::Nat(pos) => {
                usize::try_from(*pos)
                    .ok()
                    .and_then(|pos| pos.checked_sub(1))
            },
            _ => None
        }
    }

    pub fn apply_hypotheses_or_clone(self: &Rc<Self>, hys: &Hypotheses) -> Rc<Self> {
        self.apply_hypotheses(hys).unwrap_or_else(|| self.clone())
    }

    pub fn apply_hypotheses(self: &Rc<Self>, hys: &Hypotheses) -> Option<Rc<Self>> {
        self.apply_hypotheses_rec(DeBruijnIndex::ZERO, hys)
    }

    fn apply_hypotheses_rec(
        self: &Rc<Self>,
        depth: DeBruijnIndex,
        hys: &Hypotheses
    ) -> Option<Rc<Self>>
    {
        self.alter_pre_order_infallible(
            depth,
            &mut (),
            |parent, _depth, _| match parent.as_ref() {
                Expr::Free(free) => {
                    hys.get_any_by_name(free)
                        .map(|hy_entry| Expr::Hy(hy_entry.id).rc())
                },
                _ => None,
            },
            |child, depth, _| child.apply_hypotheses_rec(depth, hys)
        )
    }

    pub fn resolve(self: &Rc<Self>, resolver: &mut Resolver) -> Result<Rc<Self>, ResolveError> {
        self
            .resolve_rec(resolver, DeBruijnIndex::ZERO)
            .map(|res| res.unwrap_or_else(|| self.clone()))
    }

    pub fn resolve_rec(
        self: &Rc<Self>,
        resolver: &mut Resolver,
        depth: DeBruijnIndex
    ) -> Result<Option<Rc<Self>>, ResolveError>
    {
        self.alter_post_order(
            depth,
            resolver,
            |parent, _, resolver| {
                match parent.as_ref() {
                    Self::Obj(obj_expr) => {
                        let obj = resolver.resolve(obj_expr.id())?;
                        match obj.kind() {
                            ObjectKind::Def(def) => {
                                def
                                    .unfold(obj_expr.args())
                                    .map(Some)
                                    .map_err(|err| match err {
                                        DeltaReductionError::BadArgCount { expected, actual } => {
                                            ResolveError::BadArgCount {
                                                path: obj.path().to_owned(),
                                                params: expected,
                                                args: actual,
                                            }
                                        },
                                    })
                            },
                            ObjectKind::Thm(thm) => {
                                if !obj_expr.args().is_empty() {
                                    Err(ResolveError::BadArgCount {
                                        path: obj.path().to_owned(),
                                        params: 0,
                                        args: obj_expr.args().len(),
                                    })
                                } else {
                                    thm
                                        .extract()
                                        .cloned()
                                        .map(Some)
                                        .ok_or_else(|| {
                                            ResolveError::InvalidTheoremAsDef(obj.path().to_owned())
                                        })
                                }
                            },
                            _ => Ok(None),
                        }
                    },
                    Self::Free(free) => {
                        Err(ResolveError::FreeVar(free.as_ref().into()))
                    },
                    _ => Ok(None),
                }
            },
            |child, depth, resolver| {
                child.resolve_rec(resolver, depth)
            },
        )
    }

    pub fn format_to_string(&self, ctx: Context, names: &mut NameAssignments) -> String {
        let mut buf = String::new();
        self.format(&mut buf, ctx, names).unwrap();
        buf
    }

    pub fn format<W: fmt::Write>(
        &self,
        f: &mut W,
        ctx: Context,
        names: &mut NameAssignments
    ) -> fmt::Result 
    {
        match self {
            // FIXME: display the second-order variable mapping, if there is one
            Expr::Var(var) => match names.var_name(var.index()) {
                Some(var_name) => write!(f, "{}", var_name),
                None => write!(f, "var!{}", var.index().get()),
            },
            Expr::Hy(hy_index) => match names.hypothesis_name(*hy_index) {
                Some(hy_name) => write!(f, "{}", hy_name),
                None => write!(f, "hy!{}", hy_index.inner_val()),
            },
            Expr::Tok(tok) => write!(f, "\"{}\"", FormatTok(tok)),
            Expr::Nat(n) => write!(f, "{}", n),
            Expr::Bound(bound) => {
                let var = names.find_available_name(bound.body_raw(), Some(bound.var().clone()));
                write!(f, "{}. ", var)?;
                names.push_var_name(Some(var));
                bound.body_raw().format(f, ctx, names)?;
                names.pop_var_name();
                Ok(())
            },
            Expr::UnifVar(unif_var) => {
                write!(f, "${}", unif_var.display_name())?;
                match unif_var.kind().str_name() {
                    Some(kind) => write!(f, ":{}", kind),
                    None => Ok(()),
                }
            },
            Expr::Subst(subst) => {
                write!(f, "[")?;
                let mut args = subst.args().iter();
                if let Some(arg) = args.next() {
                    arg.format(f, ctx, names)?;
                    for arg in args {
                        write!(f, ", ")?;
                        arg.format(f, ctx, names)?;
                    }
                }
                write!(f, "]")?;
                for _ in 0..subst.num_args() {
                    names.push_var_name(None);
                }
                subst.bound_raw().format_paren(f, ctx, names, Precedence::Contained)?;
                for _ in 0..subst.num_args() {
                    names.pop_var_name();
                }
                Ok(())
            },
            Expr::Obj(obj) => {
                let res = match (obj.id(), obj.args().as_ref()) {
                    (id, [body]) if Some(id) == ctx.std_objs.neg => {
                        write!(f, "-")?;
                        body.format_paren(f, ctx, names, Precedence::Neg)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.add => {
                        lhs.format_paren(f, ctx, names, Precedence::Mul)?;
                        write!(f, " + ")?;
                        rhs.format_paren(f, ctx, names, Precedence::Mul)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.mul => {
                        lhs.format_paren(f, ctx, names, Precedence::Neg)?;
                        write!(f, " * ")?;
                        rhs.format_paren(f, ctx, names, Precedence::Neg)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.div => {
                        lhs.format_paren(f, ctx, names, Precedence::Neg)?;
                        write!(f, " div ")?;
                        rhs.format_paren(f, ctx, names, Precedence::Neg)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.rem => {
                        lhs.format_paren(f, ctx, names, Precedence::Neg)?;
                        write!(f, " rem ")?;
                        rhs.format_paren(f, ctx, names, Precedence::Neg)?;
                        Some(Ok(()))
                    },
                    (id, [body]) if Some(id) == ctx.std_objs.lambda => {
                        match body.as_ref() {
                            Expr::Bound(body) => {
                                let var = names.find_available_name(body.body_raw(), Some(body.var().clone()));
                                write!(f, "\\{}. ", var)?;
                                names.push_var_name(Some(var));
                                body.body_raw().format(f, ctx, names)?;
                                names.pop_var_name();
                                Some(Ok(()))
                            },
                            _ => None,
                        }
                    },
                    (id, [func, arg]) if Some(id) == ctx.std_objs.app => {
                        func.format_paren(f, ctx, names, Precedence::App)?;
                        write!(f, " ")?;
                        arg.format_paren(f, ctx, names, Precedence::Contained)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.pair => {
                        write!(f, "<")?;
                        lhs.format(f, ctx, names)?;
                        write!(f, ", ")?;
                        rhs.format(f, ctx, names)?;
                        write!(f, ">")?;
                        Some(Ok(()))
                    },
                    (id, [val, body]) if Some(id) == ctx.std_objs.spread => {
                        match body.as_ref() {
                            Expr::Bound(body_outer) => match body_outer.body_raw().as_ref() {
                                Expr::Bound(body_inner) => {
                                    let lhs_var = names.find_available_name(body_inner.body_raw(), Some(body_outer.var().clone()));
                                    names.push_var_name(Some(lhs_var.clone()));
                                    let rhs_var = names.find_available_name(body_inner.body_raw(), Some(body_inner.var().clone()));
                                    names.pop_var_name();
                                    write!(f, "let <{}, {}> = ", lhs_var, rhs_var)?;
                                    val.format(f, ctx, names)?;
                                    write!(f, " in ")?;
                                    names.push_var_name(Some(lhs_var));
                                    names.push_var_name(Some(rhs_var));
                                    body_inner.body_raw().format(f, ctx, names)?;
                                    names.pop_var_name();
                                    names.pop_var_name();
                                    Some(Ok(()))
                                },
                                _ => None,
                            },
                            _ => None,
                        }
                    },
                    (id, [val, l_case, r_case]) if Some(id) == ctx.std_objs.decide => {
                        match (l_case.as_ref(), r_case.as_ref()) {
                            (Expr::Bound(l_case), Expr::Bound(r_case)) => {
                                let inl_var = names.find_available_name(l_case.body_raw(), Some(l_case.var().clone()));
                                let inr_var = names.find_available_name(r_case.body_raw(), Some(r_case.var().clone()));
                                write!(f, "case ")?;
                                val.format(f, ctx, names)?;
                                write!(f, " of inl({}) => ", inl_var)?;
                                names.push_var_name(Some(inl_var));
                                l_case.body_raw().format(f, ctx, names)?;
                                names.pop_var_name();
                                write!(f, ", inr({}) => ", inr_var)?;
                                names.push_var_name(Some(inr_var));
                                r_case.body_raw().format(f, ctx, names)?;
                                names.pop_var_name();
                                Some(Ok(()))
                            },
                            _ => None,
                        }
                    },
                    (id, [val, body]) if Some(id) == ctx.std_objs.cbv => {
                        match body.as_ref() {
                            Expr::Bound(body) => {
                                let var = names.find_available_name(body.body_raw(), Some(body.var().clone()));
                                write!(f, "let {} := ", var)?;
                                val.format(f, ctx, names)?;
                                write!(f, " in ")?;
                                names.push_var_name(Some(var));
                                body.body_raw().format(f, ctx, names)?;
                                names.pop_var_name();
                                Some(Ok(()))
                            },
                            _ => None,
                        }
                    },
                    (id, [lhs, rhs, l_case, r_case]) if Some(id) == ctx.std_objs.compare_eq => {
                        write!(f, "if ")?;
                        lhs.format_paren(f, ctx, names, Precedence::Add)?;
                        write!(f, " = ")?;
                        rhs.format_paren(f, ctx, names, Precedence::Add)?;
                        write!(f, " then ")?;
                        l_case.format(f, ctx, names)?;
                        write!(f, " else ")?;
                        r_case.format(f, ctx, names)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs, l_case, r_case]) if Some(id) == ctx.std_objs.compare_lt => {
                        write!(f, "if ")?;
                        lhs.format_paren(f, ctx, names, Precedence::Add)?;
                        write!(f, " < ")?;
                        rhs.format_paren(f, ctx, names, Precedence::Add)?;
                        write!(f, " then ")?;
                        l_case.format(f, ctx, names)?;
                        write!(f, " else ")?;
                        r_case.format(f, ctx, names)?;
                        Some(Ok(()))
                    },
                    (id, [domain, codomain]) if Some(id) == ctx.std_objs.func => {
                        match codomain.as_ref() {
                            Expr::Bound(codomain) => {
                                let var = names.find_available_name(codomain.body_raw(), Some(codomain.var().clone()));
                                write!(f, "{}: ", var)?;
                                domain.format_paren(f, ctx, names, Precedence::SumTy)?;
                                write!(f, " -> ")?;
                                names.push_var_name(Some(var));
                                codomain.body_raw().format_paren(f, ctx, names, Precedence::FnTy)?;
                                names.pop_var_name();
                                Some(Ok(()))
                            },
                            _ => {
                                domain.format_paren(f, ctx, names, Precedence::SumTy)?;
                                write!(f, " -> ")?;
                                codomain.format_paren(f, ctx, names, Precedence::FnTy)?;
                                Some(Ok(()))
                            },
                        }
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.sum => {
                        lhs.format_paren(f, ctx, names, Precedence::ProdTy)?;
                        write!(f, " | ")?;
                        rhs.format_paren(f, ctx, names, Precedence::SumTy)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.prod => {
                        match rhs.as_ref() {
                            Expr::Bound(rhs) => {
                                let var = names.find_available_name(rhs.body_raw(), Some(rhs.var().clone()));
                                write!(f, "{}: ", var)?;
                                lhs.format_paren(f, ctx, names, Precedence::LtTy)?;
                                write!(f, " # ")?;
                                names.push_var_name(Some(var));
                                rhs.body_raw().format_paren(f, ctx, names, Precedence::ProdTy)?;
                                names.pop_var_name();
                                Some(Ok(()))
                            },
                            _ => {
                                lhs.format_paren(f, ctx, names, Precedence::LtTy)?;
                                write!(f, " # ")?;
                                rhs.format_paren(f, ctx, names, Precedence::ProdTy)?;
                                Some(Ok(()))
                            },
                        }
                    },
                    (id, [ty, lhs, rhs]) if Some(id) == ctx.std_objs.eq => {
                        lhs.format_paren(f, ctx, names, Precedence::FnTy)?;
                        write!(f, " = ")?;
                        rhs.format_paren(f, ctx, names, Precedence::FnTy)?;
                        write!(f, " in ")?;
                        ty.format_paren(f, ctx, names, Precedence::EqTy)?;
                        Some(Ok(()))
                    },
                    (id, [lhs, rhs]) if Some(id) == ctx.std_objs.isect => {
                        match rhs.as_ref() {
                            Expr::Bound(rhs) => {
                                let var = names.find_available_name(rhs.body_raw(), Some(rhs.var().clone()));
                                write!(f, "{}: ", var)?;
                                lhs.format_paren(f, ctx, names, Precedence::Add)?;
                                write!(f, " & ")?;
                                names.push_var_name(Some(var));
                                rhs.body_raw().format_paren(f, ctx, names, Precedence::IsectTy)?;
                                names.pop_var_name();
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
                        match ctx.lib.get(obj.id()) {
                            Some(lib_obj) => {
                                write!(f, "{}", lib_obj.path())?;
                            },
                            None => {
                                write!(f, "obj!{}", obj.id().inner_val())?;
                            },
                        }
                        for arg in obj.args().iter() {
                            write!(f, " ")?;
                            arg.format_paren(f, ctx, names, Precedence::Contained)?;
                        }
                        Ok(())
                    }
                }
            },
            Expr::Tag(tag) => {
                match tag.steps() {
                    ReductionSteps::Finite(n) => write!(f, "[[{}; ", n),
                    ReductionSteps::Infinite => write!(f, "[[*; "),
                }?;
                tag.body().format(f, ctx, names)?;
                write!(f, "]]")
            },
            Expr::Free(free) => {
                write!(f, "{}", free)
            }
        }
    }

    fn format_paren<W: fmt::Write>(
        &self,
        f: &mut W,
        ctx: Context,
        names: &mut NameAssignments,
        min_prec: Precedence,
    ) -> fmt::Result
    {
        if self.precedence(ctx) < min_prec {
            write!(f, "(")?;
            self.format(f, ctx, names)?;
            write!(f, ")")
        } else {
            self.format(f, ctx, names)
        }
    }

    fn precedence(&self, ctx: Context) -> Precedence {
        match self {
            Self::Var(_) => Precedence::Contained,
            Self::Hy(_) => Precedence::Contained,
            Self::Tok(_) => Precedence::Contained,
            Self::Nat(_) => Precedence::Contained,
            Self::Bound(_) => Precedence::Loose,
            Self::UnifVar(_) => Precedence::Contained,
            Self::Subst(_) => Precedence::Subst,
            Self::Obj(obj) => {
                match obj.id() {
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
                        if obj.args().is_empty() {
                            Precedence::Contained
                        } else {
                            Precedence::App
                        }
                    }
                }
            },
            Self::Tag(_) => Precedence::Contained,
            Self::Free(_) => Precedence::Contained,
        }
    }
}

/// A first-order variable instance `v` or second-order variable instance `v[a1; a2; ...; an]`.
#[derive(Archive, Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
pub struct Var {
    index: DeBruijnIndex,
    mapping: SecondOrderMappingBuf,
}

impl Var {
    pub fn first_order(index: DeBruijnIndex) -> Self {
        Self { index, mapping: SecondOrderMappingBuf::empty() }
    }

    pub fn new(index: DeBruijnIndex, mapping: SecondOrderMappingBuf) -> Self {
        Self { index, mapping }
    }

    pub fn index(&self) -> DeBruijnIndex {
        self.index
    }

    pub fn mapping(&self) -> &SecondOrderMappingBuf {
        &self.mapping
    }

    pub fn expr(self) -> Expr {
        Expr::Var(self)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
pub struct SecondOrderMappingBuf {
    repr: SecondOrderMappingBufRepr,
}

impl SecondOrderMappingBuf {
    pub fn empty() -> Self {
        Self { repr: SecondOrderMappingBufRepr::Unallocated }
    }
}

impl FromIterator<DeBruijnIndex> for SecondOrderMappingBuf {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = DeBruijnIndex>,
    {
        let exprs = iter
            .into_iter()
            .map(|index| Var::first_order(index).expr().rc())
            .collect();

        Self { repr: SecondOrderMappingBufRepr::Allocated(exprs) }
    }
}

impl FromIterator<RcExpr> for SecondOrderMappingBuf {
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = RcExpr>,
    {
        Self { repr: SecondOrderMappingBufRepr::Allocated(iter.into_iter().collect()) }
    }
}

impl AsRef<SecondOrderMapping> for SecondOrderMappingBuf {
    fn as_ref(&self) -> &SecondOrderMapping {
        self
    }
}

impl Borrow<SecondOrderMapping> for SecondOrderMappingBuf {
    fn borrow(&self) -> &SecondOrderMapping {
        self
    }
}

impl Deref for SecondOrderMappingBuf {
    type Target = SecondOrderMapping;

    fn deref(&self) -> &Self::Target {
        self.repr.as_de_bruijn_mapping()
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
#[archive(bound(serialize = "__S: rkyv::ser::Serializer + rkyv::ser::ScratchSpace + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "__D: rkyv::de::SharedDeserializeRegistry"))]
pub enum SecondOrderMappingBufRepr {
    Unallocated,
    Allocated(#[omit_bounds] Rc<[RcExpr]>),
}

impl SecondOrderMappingBufRepr {
    fn as_de_bruijn_mapping(&self) -> &SecondOrderMapping {
        match self {
            Self::Unallocated => SecondOrderMapping::from_slice(&[]),
            Self::Allocated(mapping) => SecondOrderMapping::from_slice(mapping),
        }
    }
}

impl PartialEq for SecondOrderMappingBufRepr {
    fn eq(&self, other: &Self) -> bool {
        self.as_de_bruijn_mapping().eq(other.as_de_bruijn_mapping())
    }
}

impl Eq for SecondOrderMappingBufRepr {}

#[derive(PartialEq, Eq, Debug)]
#[repr(transparent)]
pub struct SecondOrderMapping([RcExpr]);

impl SecondOrderMapping {
    pub fn subslice(&self, len: usize) -> &Self {
        Self::from_slice(&self.0[..len.min(self.len())])
    }

    pub fn map(&self, index: DeBruijnIndex) -> Option<&RcExpr> {
        self
            .len()
            .checked_sub(1)
            .and_then(|max_index| max_index.checked_sub(index.get()))
            .and_then(|index| self.0.get(index))
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn iter(&self) -> slice::Iter<RcExpr> {
        self.0.iter()
    }

    fn from_slice(slice: &[RcExpr]) -> &Self {
        unsafe { &*(slice as *const [RcExpr] as *const Self) }
    }
}

impl<'a> IntoIterator for &'a SecondOrderMapping {
    type Item = &'a RcExpr;

    type IntoIter = slice::Iter<'a, RcExpr>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Eq, Debug)]
#[archive(bound(serialize = "__S: rkyv::ser::Serializer + rkyv::ser::ScratchSpace + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "__D: rkyv::de::SharedDeserializeRegistry"))]
pub struct Bound {
    var: Rc<str>,
    #[omit_bounds]
    body: RcExpr,
}

impl Bound {
    pub fn new(var: Rc<str>, body: RcExpr) -> Self {
        Self { var, body }
    }

    pub fn var(&self) -> &Rc<str> {
        &self.var
    }

    pub fn body(&self, subst: &RcExpr) -> RcExpr {
        self.body.subst_or_clone(subst)
    }

    pub fn body_raw(&self) -> &RcExpr {
        &self.body
    }

    pub fn expr(self) -> Expr {
        Expr::Bound(self)
    }
}

impl PartialEq for Bound {
    fn eq(&self, other: &Self) -> bool {
        self.body == other.body
    }
}

/// If the same `UnifVar` appears in an expression multiple times, it must be bound an equal number
/// of times in all occurrences (i.e. it appears at the same depth in all occurrenes).
#[derive(Archive, Serialize, Deserialize, Clone, Eq, Debug)]
pub struct UnifVar {
    display_name: Rc<str>,
    index: UnifVarIndex,
    kind: UnifVarKind,
}

impl UnifVar {
    pub fn new(name: Rc<str>, index: UnifVarIndex, kind: UnifVarKind) -> Self {
        Self { display_name: name, index, kind }
    }

    pub fn display_name(&self) -> &Rc<str> {
        &self.display_name
    }
    
    pub fn index(&self) -> UnifVarIndex {
        self.index
    }

    pub fn kind(&self) -> UnifVarKind {
        self.kind
    }

    pub fn expr(self) -> Expr {
        Expr::UnifVar(self)
    }
}

impl PartialEq for UnifVar {
    fn eq(&self, other: &Self) -> bool {
        // The `display_name` does not contribute to equality.
        self.index == other.index
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
#[archive(bound(serialize = "__S: rkyv::ser::Serializer + rkyv::ser::ScratchSpace + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "__D: rkyv::de::SharedDeserializeRegistry"))]
pub struct Subst {
    #[omit_bounds]
    bound: RcExpr,
    #[omit_bounds]
    args: InliningBuf<RcExpr, 5>,
}

impl Subst {
    pub fn new(bound: RcExpr, args: InliningBuf<RcExpr, 5>) -> Self {
        Self { bound, args }
    }

    pub fn bound_raw(&self) -> &RcExpr {
        &self.bound
    }

    pub fn num_args(&self) -> usize {
        self.args.len()
    }

    pub fn args(&self) -> &InliningBuf<RcExpr, 5> {
        &self.args
    }

    pub fn apply(&self) -> RcExpr {
        self.bound.subst_all(&self.args)
    }

    pub fn expr(self) -> Expr {
        Expr::Subst(self)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Eq, Debug)]
#[archive(bound(serialize = "__S: rkyv::ser::Serializer + rkyv::ser::ScratchSpace + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "__D: rkyv::de::SharedDeserializeRegistry"))]
pub struct ObjExpr {
    id: ObjectId,

    // Inline up to 5 arguments so that we get a nice round 64 bytes (on 64-bit targets):
    // - 8-byte object id
    // - 56-byte `InliningBuf`
    //   - 5 * 8 = 40 byte array
    //   - 8 byte length
    //   - 1 byte discriminant
    //   - Rounded up from 40 + 8 + 1 = 49 to 56 for alignment
    // FIXME: make this more compact
    #[omit_bounds]
    args: InliningBuf<RcExpr, 5>,
}

impl ObjExpr {
    pub fn new(id: ObjectId, args: InliningBuf<RcExpr, 5>) -> Self {
        Self { id, args }
    }

    pub fn id(&self) -> ObjectId {
        self.id
    }

    pub fn num_args(&self) -> usize {
        self.args.len()
    }
    
    pub fn args(&self) -> &InliningBuf<RcExpr, 5> {
        &self.args
    }

    pub fn expr(self) -> Expr {
        Expr::Obj(self)
    }
}

impl PartialEq for ObjExpr {
    fn eq(&self, other: &Self) -> bool {
        self.id() == other.id() && self.args() == other.args()
    }
}

/// Tagged expression `[[steps; body]]`, for use by the `direct_computation` family of inference
/// rules.
#[derive(Archive, Serialize, Deserialize, Clone, PartialEq, Eq, Debug)]
#[archive(bound(serialize = "__S: rkyv::ser::Serializer + rkyv::ser::ScratchSpace + rkyv::ser::SharedSerializeRegistry"))]
#[archive(bound(deserialize = "__D: rkyv::de::SharedDeserializeRegistry"))]
pub struct Tag {
    steps: ReductionSteps,
    #[omit_bounds]
    body: RcExpr,
}

impl Tag {
    pub fn new(steps: ReductionSteps, body: RcExpr) -> Self {
        Self { steps, body }
    }

    pub fn steps(&self) -> ReductionSteps {
        self.steps
    }

    pub fn body(&self) -> &RcExpr {
        &self.body
    }

    pub fn expr(self) -> Expr {
        Expr::Tag(self)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
pub enum ReductionSteps {
    Finite(u64),
    Infinite,
}

impl ReductionSteps {
    #[must_use]
    pub fn decremented(self) -> Option<Self> {
        match self {
            ReductionSteps::Finite(n) => n.checked_sub(1).map(ReductionSteps::Finite),
            ReductionSteps::Infinite => Some(self),
        }
    }
}

impl fmt::Display for ReductionSteps {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Finite(n) => write!(f, "{}", n),
            Self::Infinite => f.write_str("*"),
        }
    }
}

#[derive(Debug)]
pub enum PlaceholderConflict {
    Depth {
        placeholder: UnifVarIndex,
        expected_depth: DeBruijnIndex,
        actual_depth: DeBruijnIndex,
    },
    FirstOccurrenceInSubst {
        placeholder: UnifVarIndex,
    },
}

#[derive(Debug)]
pub enum SubstPlaceholderError {
    NoConcreteValue {
        name: Rc<str>,
        index: UnifVarIndex,
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

/// Helper struct for displaying token strings, escaping the double-quote and backslash characters.
#[derive(Debug)]
pub struct FormatTok<'a>(pub &'a str);

impl<'a> fmt::Display for FormatTok<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for c in self.0.chars() {
            match c {
                '\\' => f.write_str("\\\\")?,
                '\"' => f.write_str("\\\"")?,
                '\n' => f.write_str("\\n")?,
                '\r' => f.write_str("\\r")?,
                '\t' => f.write_str("\\t")?,
                '\0' => f.write_str("\\0")?,
                c => f.write_char(c)?,
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::{load_stdlib, phase3_proofck::{var_names::NameAssignments, expr::{ObjExpr, Bound, Var}, hypothesis::HypothesisIdGen}, de_bruijn::DeBruijnIndex, object_id::ObjectIdGen, DEFAULT_NAMESPACE};

    use super::Expr;

    #[test]
    fn test_subst() {
        assert_eq!(
            Expr::Nat(1).rc()
                .subst(&Expr::Nat(2).rc()),
            None
        );

        assert_eq!(
            Var::first_order(DeBruijnIndex::new(0)).expr().rc()
                .subst(&Expr::Nat(2).rc()),
            Some(Expr::Nat(2).rc())
        );

        assert_eq!(
            Var::first_order(DeBruijnIndex::new(1)).expr().rc()
                .subst(&Expr::Nat(2).rc()),
            Some(Var::first_order(DeBruijnIndex::new(0)).expr().rc())
        );

        assert_eq!(
            Bound::new(
                "x".into(),
                Var::first_order(DeBruijnIndex::new(0)).expr().rc()
            ).expr().rc()
                .subst(&Expr::Nat(2).rc()),
            None
        );

        assert_eq!(
            Bound::new(
                "x".into(),
                Var::first_order(DeBruijnIndex::new(1)).expr().rc()
            ).expr().rc()
                .subst(&Expr::Nat(2).rc()),
            Some(Bound::new(
                "x".into(),
                Expr::Nat(2).rc()
            ).expr().rc())
        );

        assert_eq!(
            Var::first_order(DeBruijnIndex::new(0)).expr().rc()
                .subst(&Var::first_order(DeBruijnIndex::new(0)).expr().rc()),
            Some(Var::first_order(DeBruijnIndex::new(0)).expr().rc())
        );

        assert_eq!(
            Bound::new(
                "x".into(),
                Bound::new(
                    "y".into(),
                    Var::first_order(DeBruijnIndex::new(2)).expr().rc()
                ).expr().rc()
            ).expr().rc()
                .subst(&Var::first_order(DeBruijnIndex::new(3)).expr().rc()),
            Some(Bound::new(
                "x".into(),
                Bound::new(
                    "y".into(),
                    Var::first_order(DeBruijnIndex::new(5)).expr().rc()
                ).expr().rc()
            ).expr().rc())
        );

        let id = ObjectIdGen::new(DEFAULT_NAMESPACE).next_id();

        assert_eq!(
            ObjExpr::new(id, [
                Var::first_order(DeBruijnIndex::new(0)).expr().rc(),
                Var::first_order(DeBruijnIndex::new(1)).expr().rc()
            ].into_iter().collect()).expr().rc()
                .subst(&Expr::Nat(2).rc()),
            Some(ObjExpr::new(id, [
                Expr::Nat(2).rc(),
                Var::first_order(DeBruijnIndex::new(0)).expr().rc()
            ].into_iter().collect()).expr().rc())
        );
    }

    #[test]
    fn test_bind_hys() {
        let mut hy_id_gen = HypothesisIdGen::zero();
        let id1 = hy_id_gen.get_next();
        let id2 = hy_id_gen.get_next();

        assert_eq!(
            Expr::Nat(1).rc()
                .bind_hypothesis(id1),
            None
        );

        assert_eq!(
            Expr::Hy(id1).rc()
                .bind_hypothesis(id1),
            Some( Var::first_order(DeBruijnIndex::new(0)).expr().rc())
        );

        assert_eq!(
            Expr::Hy(id2).rc()
                .bind_hypothesis(id1),
            None
        );

        assert_eq!(
            Bound::new(
                "x".into(),
                Expr::Hy(id1).rc()
            ).expr().rc()
                .bind_hypothesis(id1),
            Some(Bound::new(
                "x".into(),
                Var::first_order(DeBruijnIndex::new(1)).expr().rc()
            ).expr().rc())
        );

        assert_eq!(
            Bound::new(
                "x".into(),
                Expr::Hy(id2).rc()
            ).expr().rc()
                .bind_hypothesis(id1),
            None
        );
    }

    #[test]
    fn test_format() {
        let stdlib = load_stdlib();

        let format_to_string = |expr: &Expr| {
            let mut buf = String::new();
            expr.format(&mut buf, stdlib.ctx(), &mut NameAssignments::new())
                .unwrap();
            buf
        };

        assert_eq!(
            &format_to_string(
                &ObjExpr::new(stdlib.std_objs().add.unwrap(), [
                    Expr::Nat(1).rc(),
                    Expr::Nat(2).rc()
                ].into_iter().collect()).expr()
            ),
            "1 + 2"
        );

        assert_eq!(
            &format_to_string(
                &ObjExpr::new(stdlib.std_objs().mul.unwrap(), [
                    Expr::Nat(1).rc(),
                    ObjExpr::new(stdlib.std_objs().add.unwrap(), [
                        Expr::Nat(2).rc(),
                        Expr::Nat(3).rc()
                    ].into_iter().collect()).expr().rc()
                ].into_iter().collect()).expr()
            ),
            "1 * (2 + 3)"
        );

        assert_eq!(
            &format_to_string(
                &ObjExpr::new(stdlib.std_objs().add.unwrap(), [
                    Expr::Nat(1).rc(),
                    ObjExpr::new(stdlib.std_objs().mul.unwrap(), [
                        Expr::Nat(2).rc(),
                        Expr::Nat(3).rc()
                    ].into_iter().collect()).expr().rc()
                ].into_iter().collect()).expr()
            ),
            "1 + 2 * 3"
        );

        assert_eq!(
            &format_to_string(
                &ObjExpr::new(stdlib.std_objs().app.unwrap(), [
                    Expr::Nat(1).rc(),
                    Expr::Nat(2).rc()
                ].into_iter().collect()).expr()
            ),
            "1 2"
        );

        assert_eq!(
            &format_to_string(
                &Bound::new(
                    "foo".into(),
                    Var::first_order(DeBruijnIndex::new(0)).expr().rc()
                ).expr()
            ),
            "foo. foo"
        );

        assert_eq!(
            &format_to_string(
                &ObjExpr::new(stdlib.std_objs().lambda.unwrap(), [
                    Bound::new(
                        "foo".into(),
                        Var::first_order(DeBruijnIndex::new(0)).expr().rc()
                    ).expr().rc()
                ].into_iter().collect()).expr()
            ),
            "\\foo. foo"
        );

        assert_eq!(
            &format_to_string(
                &ObjExpr::new(stdlib.std_objs().lambda.unwrap(), [
                    Bound::new(
                        "foo".into(),
                        ObjExpr::new(stdlib.std_objs().lambda.unwrap(), [
                            Bound::new(
                                "foo".into(),
                                Var::first_order(DeBruijnIndex::new(1)).expr().rc()
                            ).expr().rc()
                        ].into_iter().collect()).expr().rc()
                    ).expr().rc()
                ].into_iter().collect()).expr()
            ),
            "\\foo. \\x. foo"
        );
    }
}
