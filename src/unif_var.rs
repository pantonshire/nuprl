use std::{collections::{BTreeMap, btree_map}, rc::Rc};

use rkyv::{Archive, Serialize, Deserialize};

use crate::utils::ReborrowMut;

#[derive(Debug)]
pub enum UnifVarIndicesRef<'a> {
    Mutable(&'a mut UnifVarIndices),
    Immutable(&'a UnifVarIndices),
}

impl<'a> ReborrowMut for UnifVarIndicesRef<'a> {
    type Target<'rb> = UnifVarIndicesRef<'rb>
        where Self: 'rb;

    fn reborrow_mut<'rb>(&'rb mut self) -> Self::Target<'rb> {
        match self {
            Self::Mutable(indices) => UnifVarIndicesRef::Mutable(&mut *indices),
            Self::Immutable(indices) => UnifVarIndicesRef::Immutable(&*indices),
        }
    }
}

#[derive(Clone, Debug)]
pub struct UnifVarIndices {
    indices: BTreeMap<Rc<str>, UnifVarIndex>,
    index_gen: UnifVarIndexGen,
}

impl UnifVarIndices {
    pub fn new() -> Self {
        Self {
            indices: BTreeMap::new(),
            index_gen: UnifVarIndexGen::new(),
        }
    }

    pub fn get(&self, name: &str) -> Option<UnifVarIndex> {
        self.indices.get(name).copied()
    }

    pub fn get_or_generate(&mut self, name: Rc<str>) -> UnifVarIndex {
        match self.indices.entry(name) {
            btree_map::Entry::Vacant(entry) => {
                let index = self.index_gen.next_index();
                entry.insert(index);
                index
            },
            btree_map::Entry::Occupied(entry) => {
                *entry.get()
            },
        }
    }

    pub fn generate(&mut self, name: Rc<str>) -> Option<UnifVarIndex> {
        match self.indices.entry(name) {
            btree_map::Entry::Vacant(entry) => {
                let index = self.index_gen.next_index();
                entry.insert(index);
                Some(index)
            },
            btree_map::Entry::Occupied(_) => {
                None
            },
        }
    }
}

#[derive(Archive, Serialize, Deserialize, serde::Serialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct UnifVarIndex(pub usize);

#[derive(Clone, Debug)]
struct UnifVarIndexGen {
    next: usize,
}

impl UnifVarIndexGen {
    fn new() -> Self {
        Self { next: 0 }
    }

    fn next_index(&mut self) -> UnifVarIndex {
        let index = self.next;
        // FIXME: overflow?
        self.next += 1;
        UnifVarIndex(index)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, Copy, PartialEq, Eq, Debug)]
pub enum UnifVarKind {
    Any,
    Nat,
    Var,
}

impl UnifVarKind {
    pub fn str_name(self) -> Option<&'static str> {
        match self {
            Self::Any => None,
            Self::Nat => Some("n"),
            Self::Var => Some("v"),
        }
    }
}
