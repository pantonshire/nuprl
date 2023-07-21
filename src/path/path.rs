use std::{fmt, rc::Rc, mem, str, borrow::Borrow, ops::Deref};

use rkyv::{Archive, Serialize, Deserialize};

#[derive(Archive, Serialize, Deserialize, Clone, PartialEq, Eq, Hash, Debug)]
pub enum LibPathNode {
    Super,
    Module,
    Named(Rc<str>),
}

impl fmt::Display for LibPathNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::Super => "..",
            Self::Module => ".",
            Self::Named(node) => node.as_ref(),
        })
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, PartialEq, Eq, Hash, Debug)]
pub struct LibPathBuf {
    nodes: Box<[LibPathNode]>,
    absolute: bool,
}

impl LibPathBuf {
    pub fn new(nodes: Box<[LibPathNode]>, absolute: bool) -> Self {
        Self { nodes, absolute }
    }

    pub fn new_unitary(node: Rc<str>) -> Self {
        Self::new([LibPathNode::Named(node)].into(), false)
    }

    pub fn absolute(&self) -> bool {
        self.absolute
    }

    pub fn nodes(&self) -> &[LibPathNode] {
        &self.nodes
    }

    pub fn as_unitary(&self) -> Option<&Rc<str>> {
        match &self.nodes[..] {
            [LibPathNode::Named(node)] => Some(node),
            _ => None,
        }
    }

    pub fn last_named(&self) -> Option<&Rc<str>> {
        match self.nodes.last() {
            Some(LibPathNode::Named(node)) => Some(node),
            _ => None,
        }
    }
}

impl fmt::Display for LibPathBuf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.absolute {
            write!(f, "/")?;
        }

        let mut nodes = self.nodes.iter();

        if let Some(node) = nodes.next() {
            write!(f, "{}", node)?;

            for node in nodes {
                write!(f, "/{}", node)?;
            }
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct CanonLibPath {
    inner: [u8],
}

impl CanonLibPath {
    const LEN_SIZE: usize = mem::size_of::<usize>();

    // SAFETY:
    // An empty slice is a valid path.
    pub const ROOT: &Self = unsafe { Self::from_raw(&[]) };

    /// # Safety
    /// The bytes of the path must be either:
    /// - An empty slice.
    /// - A native-endian encoded `usize` "`len`", followed by `len` bytes of valid UTF-8, followed
    ///   by the bytes of another valid path.
    const unsafe fn from_raw(bytes: &[u8]) -> &Self {
        // SAFETY:
        // `Path` uses `repr(transparent)`, so it is guaranteed to have the same memory layout as
        // `[u8]`. Therefore, this pointer cast is valid.
        unsafe { &*(bytes as *const [u8] as *const Self) }
    }

    pub fn is_root(&self) -> bool {
        self.inner.is_empty()
    }

    pub fn iter(&self) -> CanonLibPathIter {
        CanonLibPathIter::new(self)
    }

    pub fn split_at_first(&self) -> Option<(&Self, &Self)> {
        let (segment_len, _) = self.first_node_segment()?;
        // FIXME: safety justification
        unsafe { Some(self.split_at_byte_index(segment_len)) }
    }

    /// Returns the first path node along with the length of the segment it is stored in (the node
    /// length and the node itself).
    fn first_node_segment(&self) -> Option<(usize, &str)> {
        if self.inner.is_empty() {
            return None
        }

        // FIXME: make this unchecked
        let (len_bytes, rest) = self.inner.split_at(Self::LEN_SIZE);
        
        // FIXME: make this unchecked
        let len_bytes = <[u8; Self::LEN_SIZE]>::try_from(len_bytes)
            .expect("`len_bytes` slice should always be the size of a `usize`");

        let node_len = usize::from_ne_bytes(len_bytes);

        // FIXME: make this unchecked
        let node = &rest[..node_len];

        // FIXME: make this unchecked
        let node_str = str::from_utf8(node).unwrap();

        let segment_len = node.len().checked_add(Self::LEN_SIZE).unwrap();

        Some((segment_len, node_str))
    }

    fn as_bytes(&self) -> &[u8] {
        &self.inner
    }

    unsafe fn split_at_byte_index(&self, mid: usize) -> (&Self, &Self) {
        let (lhs, rhs) = self.as_bytes().split_at(mid);
        // FIXME: safety justification
        unsafe { (Self::from_raw(lhs), Self::from_raw(rhs)) }
    }
}

impl ToOwned for CanonLibPath {
    type Owned = CanonLibPathBuf;

    fn to_owned(&self) -> Self::Owned {
        unsafe { CanonLibPathBuf::from_raw(self.inner.into()) }
    }
}

impl<'a> IntoIterator for &'a CanonLibPath {
    type Item = (Self, Self, &'a str);

    type IntoIter = CanonLibPathIter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl fmt::Debug for CanonLibPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.to_string(), f)
    }
}

impl fmt::Display for CanonLibPath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_root() {
            write!(f, "/")
        } else {
            for node in self.iter().map(|(_, _, node)| node) {
                write!(f, "/{}", node)?;
            }
            Ok(())
        }
    }
}

impl serde::Serialize for CanonLibPath {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer
    {
        serde::Serialize::serialize(&self.to_string(), serializer)
    }
}

#[derive(Clone, Debug)]
pub struct CanonLibPathIter<'a> {
    path: &'a CanonLibPath,
    index: usize,
}

impl<'a> CanonLibPathIter<'a> {
    fn new(path: &'a CanonLibPath) -> Self {
        Self { path, index: 0 }
    }
}

impl<'a> Iterator for CanonLibPathIter<'a> {
    type Item = (&'a CanonLibPath, &'a CanonLibPath, &'a str);

    fn next(&mut self) -> Option<Self::Item> {
        // FIXME: safety justification
        let (parent_path, current_path) = unsafe { self.path.split_at_byte_index(self.index) };

        let (segment_len, node) = current_path.first_node_segment()?;

        self.index = self.index.checked_add(segment_len).unwrap();
        
        // FIXME: safety justification
        let (node_path, _) = unsafe { self.path.split_at_byte_index(self.index) };

        Some((parent_path, node_path, node))
    }
}

#[derive(Archive, Serialize, Deserialize, Clone, PartialEq, Eq, Hash)]
pub struct CanonLibPathBuf {
    inner: Vec<u8>,
}

impl CanonLibPathBuf {
    unsafe fn from_raw(raw: Vec<u8>) -> Self {
        Self { inner: raw }
    }

    pub fn root() -> Self {
        // FIXME: safety justification
        unsafe { Self::from_raw(Vec::new()) }
    }

    pub fn push(&mut self, node: &str) {
        self.inner.extend(node.len().to_ne_bytes());
        self.inner.extend(node.bytes());
    }

    pub fn extend(&mut self, other: &CanonLibPath) {
        self.inner.extend(other.as_bytes())
    }

    pub fn rerooted(&self, new_root: &CanonLibPath) -> Self {
        let mut buf = new_root.to_owned();
        buf.extend(self);
        buf
    }

    pub fn from_nodes<'a, S, I>(nodes: I) -> Self
    where
        S: AsRef<str>,
        I: IntoIterator<Item = S>,
    {
        let mut buf = Self::root();
        for node in nodes.into_iter() {
            buf.push(node.as_ref());
        }
        buf
    }
}

impl AsRef<CanonLibPath> for CanonLibPathBuf {
    fn as_ref(&self) -> &CanonLibPath {
        self
    }
}

impl Borrow<CanonLibPath> for CanonLibPathBuf {
    fn borrow(&self) -> &CanonLibPath {
        self
    }
}

impl Deref for CanonLibPathBuf {
    type Target = CanonLibPath;

    fn deref(&self) -> &Self::Target {
        // FIXME: safety justification
        unsafe { CanonLibPath::from_raw(&self.inner) }
    }
}

impl<'a, S> FromIterator<S> for CanonLibPathBuf
where
    S: AsRef<str>,
{
    fn from_iter<T>(iter: T) -> Self
    where
        T: IntoIterator<Item = S>,
    {
        Self::from_nodes(iter)
    }
}

impl fmt::Debug for CanonLibPathBuf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_ref(), f)
    }
}

impl fmt::Display for CanonLibPathBuf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_ref(), f)
    }
}

impl serde::Serialize for CanonLibPathBuf {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer
    {
        serde::Serialize::serialize(self.as_ref(), serializer)
    }
}

#[cfg(test)]
mod tests {
    use super::{LibPathBuf, LibPathNode};

    #[test]
    fn test_noncanon_path_display() {
        assert_eq!(
            LibPathBuf::new([
                LibPathNode::Named("xyz".into()),
            ].into(), false).to_string(),
            "xyz",
        );

        assert_eq!(
            LibPathBuf::new([
                LibPathNode::Named("xyz".into()),
                LibPathNode::Named("abc".into()),
                LibPathNode::Named("foo".into()),
            ].into(), false).to_string(),
            "xyz/abc/foo",
        );

        assert_eq!(
            LibPathBuf::new(Box::default(), true).to_string(),
            "/",
        );

        assert_eq!(
            LibPathBuf::new([
                LibPathNode::Named("xyz".into()),
            ].into(), true).to_string(),
            "/xyz",
        );

        assert_eq!(
            LibPathBuf::new([
                LibPathNode::Module
            ].into(), false).to_string(),
            ".",
        );

        assert_eq!(
            LibPathBuf::new([
                LibPathNode::Module,
                LibPathNode::Named("xyz".into()),
            ].into(), false).to_string(),
            "./xyz",
        );

        assert_eq!(
            LibPathBuf::new([
                LibPathNode::Super
            ].into(), false).to_string(),
            "..",
        );

        assert_eq!(
            LibPathBuf::new([
                LibPathNode::Super,
                LibPathNode::Named("xyz".into()),
            ].into(), false).to_string(),
            "../xyz",
        );

        assert_eq!(
            LibPathBuf::new([
                LibPathNode::Named("abc".into()),
                LibPathNode::Super,
                LibPathNode::Named("xyz".into()),
            ].into(), false).to_string(),
            "abc/../xyz",
        );
    }
}

