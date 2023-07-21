use std::{cmp::Ordering, num::NonZeroUsize, ops};

use rkyv::{Archive, Serialize, Deserialize};

// FIXME: make this an opaque type which panics (or returns an error) on overflow, since an
// overflow will cause incorrect behaviour and potentially allow nonsense proofs.
#[derive(Archive, Serialize, Deserialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct DeBruijnIndex(usize);

impl DeBruijnIndex {
    pub const ZERO: Self = Self::new(0);

    pub const fn new(index: usize) -> Self {
        Self(index)
    }

    pub fn get(self) -> usize {
        self.0
    }

    pub fn checked_sub(self, other: Self) -> Option<Self> {
        self.get().checked_sub(other.get()).map(Self::new)
    }

    #[must_use]
    pub fn compare(self, other: DeBruijnIndex) -> DeBruijnCmp {
        match self.cmp(&other) {
            Ordering::Less => {
                // SAFETY:
                // If `self < other`, then `other` cannot be zero because `self >= 0` (De Bruijn
                // indices are non-negative).
                let other_nonzero = unsafe { NonZeroUsize::new_unchecked(other.get()) };
                DeBruijnCmp::Lt(self, NonZeroDeBruijnIndex(other_nonzero))
            }
            Ordering::Equal => DeBruijnCmp::Eq(self, other),
            Ordering::Greater => {
                // SAFETY:
                // If `self > other`, then `self` cannot be zero because `other >= 0` (De Bruijn
                // indices are non-negative).
                let self_nonzero = unsafe { NonZeroUsize::new_unchecked(self.get()) };
                DeBruijnCmp::Gt(NonZeroDeBruijnIndex(self_nonzero), other)
            }
        }
    }
}

impl ops::Add for DeBruijnIndex {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(self.0 + rhs.0)
    }
}

impl ops::Add<usize> for DeBruijnIndex {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        Self(self.0 + rhs)
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct NonZeroDeBruijnIndex(pub NonZeroUsize);

impl NonZeroDeBruijnIndex {
    #[must_use]
    pub fn get(self) -> DeBruijnIndex {
        DeBruijnIndex(self.0.get())
    }

    #[must_use]
    pub fn decrement(self) -> DeBruijnIndex {
        DeBruijnIndex(self.0.get() - 1)
    }
}

pub enum DeBruijnCmp {
    Lt(DeBruijnIndex, NonZeroDeBruijnIndex),
    Eq(DeBruijnIndex, DeBruijnIndex),
    Gt(NonZeroDeBruijnIndex, DeBruijnIndex),
}
