use std::{mem, rc::Rc, iter::FusedIterator, ops};

use rkyv::{Archive, Serialize, Deserialize};

use super::expr::RcExpr;

#[derive(Archive, Serialize, Deserialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct HypothesisId(usize);

impl HypothesisId {
    pub fn inner_val(self) -> usize {
        self.0
    }
}

/// A type representing whether or not a hypothesis is hidden. `Visibility::Visible` indicates that
/// the hypothesis is not hidden, and `Visibility::Hidden` indicates that the hypothesis is hidden
/// and therefore cannot be used in an extract.
#[derive(Archive, Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
pub enum Visibility {
    Visible,
    Hidden,
}

impl Visibility {
    pub fn is_hidden(self) -> bool {
        matches!(self, Visibility::Hidden)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct Hypothesis {
    var: Rc<str>,
    ty: RcExpr,
    visibility: Visibility,
}

impl Hypothesis {
    pub fn new(var: Rc<str>, ty: RcExpr, visibility: Visibility) -> Self {
        Self { var, ty, visibility }
    }

    pub fn var(&self) -> &Rc<str> {
        &self.var
    }

    pub fn ty(&self) -> &RcExpr {
        &self.ty
    }

    pub fn visibility(&self) -> Visibility {
        self.visibility
    }

    pub fn replace_ty(&mut self, new_ty: RcExpr) -> RcExpr {
        mem::replace(&mut self.ty, new_ty)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct HypothesisEntry {
    pub id: HypothesisId,
    pub hy: Hypothesis,
}

impl HypothesisEntry {
    pub fn new(id: HypothesisId, hy: Hypothesis) -> Self {
        Self { id, hy }
    }

    pub fn as_entry_ref(&self) -> HypothesisEntryRef {
        HypothesisEntryRef { id: self.id, hy: &self.hy }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct HypothesisEntryRef<'a> {
    pub id: HypothesisId,
    pub hy: &'a Hypothesis,
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct Hypotheses {
    allocation: HypothesesAllocation,
    ids: HypothesisIdGen,
}

impl Hypotheses {
    pub const EMPTY: Self = Self::empty();
    pub const EMPTY_REF: &Self = &Self::EMPTY;

    pub const fn empty() -> Self {
        Self {
            allocation: HypothesesAllocation::Unallocated,
            ids: HypothesisIdGen::zero(),
        }
    }

    pub fn len(&self) -> usize {
        self.allocation.get_slice().len()
    }

    pub fn is_empty(&self) -> bool {
        self.allocation.get_slice().is_empty()
    }

    pub fn get_any(&self, n: usize) -> Result<HypothesisEntryRef, GetAnyHypothesisError> {
        self.allocation.get_slice().get_any(n)
    }

    /// Returns the `n`th hypothesis in this hypotheses list, provided that the hypothesis is not
    /// hidden.
    /// 
    /// Returns an error if `n` is out of bounds or the hypothesis is hidden.
    pub fn get_visible(&self, n: usize) -> Result<HypothesisEntryRef, GetVisibleHypothesisError> {
        self.allocation.get_slice().get_visible(n)
    }

    /// Returns the hypothesis in this list with the given variable name, if one exists. The
    /// returned hypothesis may be either visible or hidden.
    pub fn get_any_by_name(&self, name: &str) -> Option<HypothesisEntryRef> {
        self.allocation.get_slice().get_any_by_name(name)
    }

    pub fn iter(&self) -> impl Iterator<Item = HypothesisEntryRef>
        + DoubleEndedIterator
        + ExactSizeIterator
        + FusedIterator
    {
        self.allocation.get_slice().iter()
    }

    pub fn append(&mut self, hypothesis: Hypothesis) -> Option<HypothesisId> {
        self.allocation.make_mut_list().append(&mut self.ids, hypothesis)
    }

    pub fn with_appended(self, hypothesis: Hypothesis) -> Option<(Self, HypothesisId)> {
        let mut this = self;
        let id = this.append(hypothesis)?;
        Some((this, id))
    }

    pub fn with_inserted(
        self,
        insert_at: usize,
        hypothesis: Hypothesis,
    ) -> Option<(Self, HypothesisId)>
    {
        let mut this = self;
        let id = this.allocation.make_mut_list().insert(&mut this.ids, insert_at, hypothesis)?;
        Some((this, id))
    }

    pub fn with_ty_replaced(self, n: usize, new_ty: RcExpr) -> Option<(Self, RcExpr)> {
        let mut this = self;
        let old_ty = this.allocation.make_mut_list().replace_ty(n, new_ty)?;
        Some((this, old_ty))
    }

    pub fn with_removed(self, n: usize)
        -> Result<(Self, HypothesisEntry), RemoveHypothesisError>
    {
        let mut this = self;
        let entry = this.allocation.make_mut_list().remove(n)?;
        Ok((this, entry))
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub enum HypothesesAllocation {
    /// The `Unallocated` variant allows the empty hypotheses list to be represented without having
    /// to allocate an `Rc`.
    Unallocated,
    Allocated(Rc<HypothesesList>),
}

impl HypothesesAllocation {
    fn get_slice(&self) -> &HypothesesSlice {
        match self {
            Self::Unallocated => HypothesesSlice::from_slice(&[]),
            Self::Allocated(list) => list,
        }
    }

    fn make_mut_list(&mut self) -> &mut Rc<HypothesesList> {
        match self {
            Self::Unallocated => {
                *self = HypothesesAllocation::Allocated(HypothesesList::empty_rc());
                match self {
                    Self::Unallocated => unreachable!(),
                    Self::Allocated(list) => list,
                }
            },
            Self::Allocated(list) => list,
        }
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct HypothesesList(Vec<HypothesisEntry>);

impl HypothesesList {
    fn empty() -> Self {
        Self(Vec::new())
    }

    fn empty_rc() -> Rc<Self> {
        Rc::new(Self::empty())
    }
}

impl HypothesesList {
    // FIXME: return a Result rather than an Option
    fn append(
        self: &mut Rc<Self>,
        id_gen: &mut HypothesisIdGen,
        hypothesis: Hypothesis
    ) -> Option<HypothesisId>
    {
        // We forbid duplicate hypothesis variable names; if there is already a hypothesis with the
        // same name, return `None`.
        if self.contains_name(&hypothesis.var) {
            return None;
        }

        // Generate an ID for the new hypothesis.
        let id = id_gen.get_next();

        // Get a mutable reference to the inner vector, cloning if we don't have exclusive access to
        // it, then push the hypothesis and its id at the end.
        self.make_mut().0.push(HypothesisEntry::new(id, hypothesis));

        // Return the ID of the new hypothesis, which the caller can use to refer to the hypothesis
        // within this collection of hypotheses.
        Some(id)
    }

    // FIXME: return a Result rather than an Option
    fn insert(
        self: &mut Rc<Self>,
        id_gen: &mut HypothesisIdGen,
        insert_at: usize,
        hypothesis: Hypothesis
    ) -> Option<HypothesisId>
    {
        if insert_at > self.len() {
            return None;
        }

        // We forbid duplicate hypothesis variable names; if there is already a hypothesis with the
        // same name, return `None`.
        if self.contains_name(&hypothesis.var) {
            return None;
        }

        // Ensure that the new hypothesis will not be bound by any hypothesis to its right.
        let bound_by = hypothesis.ty.contained_hypotheses();
        for existing_entry in &self.0[insert_at..] {
            if bound_by.contains(&existing_entry.id) {
                return None;
            }
        }

        // Generate an ID for the new hypothesis.
        let id = id_gen.get_next();
        
        // Get a mutable reference to the inner vector, cloning if we don't have exclusive access to
        // it, then insert the hypothesis and its id at the given position.
        self.make_mut().0.insert(insert_at, HypothesisEntry::new(id, hypothesis));
        
        // Return the ID of the new hypothesis, which the caller can use to refer to the hypothesis
        // within this collection of hypotheses.
        Some(id)
    }

    // FIXME: return a Result rather than an Option
    fn replace_ty(self: &mut Rc<Self>, n: usize, new_ty: RcExpr)
        -> Option<RcExpr>
    {
        if n >= self.len() {
            return None;
        }

        // Ensure that the new hypothesis will not be bound by itself or any hypothesis to its right.
        let bound_by = new_ty.contained_hypotheses();
        for existing_entry in &self.0[n..] {
            if bound_by.contains(&existing_entry.id) {
                return None;
            }
        }

        let entry = self.make_mut().0.get_mut(n)?;
        Some(entry.hy.replace_ty(new_ty))
    }

    fn remove(self: &mut Rc<Self>, n: usize) -> Result<HypothesisEntry, RemoveHypothesisError> {
        if n >= self.len() {
            return Err(RemoveHypothesisError::OutOfBounds);
        }

        let to_remove = &self.0[n];

        // Ensure that no other hypothesis is referring to the hypothesis we are going to remove.
        if self.iter().any(|entry| entry.hy.ty().contains_hypothesis(to_remove.id)) {
            return Err(RemoveHypothesisError::UsedByHypothesis);
        }

        let removed = self.make_mut().0.remove(n);

        Ok(removed)
    }

    fn make_mut<'a>(self: &'a mut Rc<Self>) -> &'a mut Self {
        Rc::make_mut(self)
    }
}

impl ops::Deref for HypothesesList {
    type Target = HypothesesSlice;

    fn deref(&self) -> &Self::Target {
        HypothesesSlice::from_slice(&self.0)
    }
}

impl AsRef<HypothesesSlice> for HypothesesList {
    fn as_ref(&self) -> &HypothesesSlice {
        self
    }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct HypothesesSlice([HypothesisEntry]);

impl HypothesesSlice {
    fn from_slice(hys: &[HypothesisEntry]) -> &Self {
        // SAFETY:
        // `HypothesesSlice` uses `repr(transparent)`, so it is guaranteed to have the same memory
        // layout as `[HypothesisEntry]`. Therefore, this pointer cast is valid.
        unsafe { &*(hys as *const [HypothesisEntry] as *const Self) }
    }

    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn len(&self) -> usize {
        self.0.len()
    }

    fn get_any(&self, n: usize) -> Result<HypothesisEntryRef, GetAnyHypothesisError> {
        self.0
            .get(n)
            .ok_or(GetAnyHypothesisError::OutOfBounds)
            .map(HypothesisEntry::as_entry_ref)
    }

    fn get_visible(&self, n: usize) -> Result<HypothesisEntryRef, GetVisibleHypothesisError> {
        self.0
            .get(n)
            .ok_or(GetVisibleHypothesisError::OutOfBounds)
            .and_then(|entry| match entry.hy.visibility() {
                Visibility::Visible => Ok(entry.as_entry_ref()),
                Visibility::Hidden => Err(GetVisibleHypothesisError::Hidden),
            })
    }

    fn get_any_by_name(&self, name: &str) -> Option<HypothesisEntryRef> {
        self.iter().rev().find(|entry| entry.hy.var().as_ref() == name)
    }

    fn contains_name(&self, name: &str) -> bool {
        self.iter().any(|entry| entry.hy.var().as_ref() == name)
    }

    fn iter(&self) -> impl Iterator<Item = HypothesisEntryRef>
        + DoubleEndedIterator
        + ExactSizeIterator
        + FusedIterator
    {
        self.0.iter().map(HypothesisEntry::as_entry_ref)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Debug)]
pub struct HypothesisIdGen {
    next_id: HypothesisId,
}

impl HypothesisIdGen {
    pub const fn zero() -> Self {
        Self {
            next_id: HypothesisId(0),
        }
    }

    pub fn get_next(&mut self) -> HypothesisId {
        let id = self.next_id;
        self.next_id.0 += 1;
        id
    }
}

impl Iterator for HypothesisIdGen {
    type Item = HypothesisId;

    fn next(&mut self) -> Option<Self::Item> {
        Some(self.get_next())
    }
}

#[derive(Debug)]
pub enum GetAnyHypothesisError {
    OutOfBounds,
}

#[derive(Debug)]
pub enum GetVisibleHypothesisError {
    OutOfBounds,
    Hidden,
}

#[derive(Debug)]
pub enum RemoveHypothesisError {
    OutOfBounds,
    UsedByHypothesis,
}
