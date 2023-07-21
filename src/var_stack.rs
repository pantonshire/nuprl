use std::rc::Rc;

use super::de_bruijn::DeBruijnIndex;

pub struct VarStackEntry {
    pub name: Option<Rc<str>>,
    pub arity: usize,
}

impl VarStackEntry {
    pub fn new(name: Option<Rc<str>>, arity: usize) -> Self {
        Self { name, arity }
    }

    pub fn named(name: Rc<str>, arity: usize) -> Self {
        Self::new(Some(name), arity)
    }

    pub fn unnamed(arity: usize) -> Self {
        Self::new(None, arity)
    }
}

pub struct VarStack {
    inner: Vec<VarStackEntry>,
}

impl VarStack {
    pub fn new() -> Self {
        Self { inner: Vec::new() }
    }

    pub fn with<T, F>(&mut self, entry: VarStackEntry, f: F) -> T
    where
        F: FnOnce(&mut Self) -> T,
    {
        self.push(entry);
        let res = f(self);
        self.pop().unwrap();
        res
    }

    pub fn push(&mut self, entry: VarStackEntry) {
        self.inner.push(entry);
    }

    pub fn pop(&mut self) -> Option<VarStackEntry> {
        self.inner.pop()
    }

    pub fn de_bruijn_index_of(&self, var: &str) -> Option<(DeBruijnIndex, usize)> {
        let (i, entry) = self
            .inner
            .iter()
            .enumerate()
            .rev()
            .find(|(_, entry)| {
                entry.name
                    .as_deref()
                    .map(|name| name == var)
                    .unwrap_or(false)
            })?;

        let db_index = self.current_level()?.checked_sub(i)?;

        Some((DeBruijnIndex::new(db_index), entry.arity))
    }

    fn current_level(&self) -> Option<usize> {
        self.inner.len().checked_sub(1)
    }
}
