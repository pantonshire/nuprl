use std::{
    mem::{MaybeUninit, self, ManuallyDrop},
    ops::Deref,
    borrow::Borrow,
    fmt,
    slice,
    iter,
    num::NonZeroUsize,
    ptr,
    hash::{Hash, Hasher},
    cmp::Ordering,
};

use rkyv::{
    Archive,
    Serialize,
    Deserialize,
    vec::{ArchivedVec, VecResolver},
    ser::{ScratchSpace, Serializer}, 
    Fallible,
};

pub const NONZERO_USIZE_ONE: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(1) };

#[derive(Debug)]
pub struct ComparePtr<'a, T>(pub &'a T);

impl<'a, T> PartialEq for ComparePtr<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        ptr::eq(self.0, other.0)
    }
}

impl<'a, T> Eq for ComparePtr<'a, T> {}

impl<'a, T> PartialOrd for ComparePtr<'a, T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a, T> Ord for ComparePtr<'a, T> {
    fn cmp(&self, other: &Self) -> Ordering {
        (self.0 as *const T).cmp(&(other.0 as *const T))
    }
}

impl<'a, T> Hash for ComparePtr<'a, T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        (self.0 as *const T).hash(state);
    }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub enum Bot {}

impl Bot {
    pub fn elim(self) -> ! {
        match self {}
    }
}

pub trait IntoResultOk: Sized {
    fn ok<E>(self) -> Result<Self, E>;
}

impl<T> IntoResultOk for T {
    fn ok<E>(self) -> Result<Self, E> {
        Ok(self)
    }
}

pub trait ApplyFn: Sized {
    fn apply<T, F>(self, f: F) -> T
    where
        F: FnOnce(Self) -> T;
}

impl<U> ApplyFn for U
where
    U: Sized,
{
    fn apply<T, F>(self, f: F) -> T
    where
        F: FnOnce(Self) -> T,
    {
        f(self)
    }
}

pub trait ReborrowMut {
    type Target<'rb>
        where Self: 'rb;

    fn reborrow_mut<'rb>(&'rb mut self) -> Self::Target<'rb>;
}

impl<T> ReborrowMut for Option<T>
where
    T: ReborrowMut,
{
    type Target<'rb> = Option<T::Target<'rb>>
        where Self: 'rb;

    fn reborrow_mut<'rb>(&'rb mut self) -> Self::Target<'rb> {
        match self {
            Some(t) => Some(t.reborrow_mut()),
            None => None,
        }
    }
}

#[derive(Archive, Serialize, Deserialize, Clone)]
pub struct InliningBuf<T, const N: usize> {
    repr: InliningBufRepr<T, N>,
}

impl<T, const N: usize> InliningBuf<T, N> {
    pub fn new() -> Self {
        Self { repr: InliningBufRepr::Inlined(ArrayBuf::new()) }
    }
    
    // FIXME: add a `copy_from_slice` method which uses `ptr::copy_nonoverlapping` rather than
    // individually cloning items.
    pub fn clone_from_slice(slice: &[T]) -> Self
    where
        T: Clone,
    {
        let repr = ArrayBuf::clone_from_slice(slice)
            .map(InliningBufRepr::Inlined)
            .unwrap_or_else(|| InliningBufRepr::Allocated(slice.to_vec()));

        Self { repr }
    }

    pub fn as_slice(&self) -> &[T] {
        match &self.repr {
            InliningBufRepr::Inlined(buf) => buf,
            InliningBufRepr::Allocated(buf) => buf,
        }
    }

    pub fn iter(&self) -> slice::Iter<T> {
        match &self.repr {
            InliningBufRepr::Inlined(buf) => buf.iter(),
            InliningBufRepr::Allocated(buf) => buf.iter(),
        }
    }
}

impl<T, const N: usize> AsRef<[T]> for InliningBuf<T, N> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> Borrow<[T]> for InliningBuf<T, N> {
    fn borrow(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> Deref for InliningBuf<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const N: usize> PartialEq for InliningBuf<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T, const N: usize> Eq for InliningBuf<T, N>
where
    T: Eq,
{}

impl<T, const N: usize> FromIterator<T> for InliningBuf<T, N> {
    fn from_iter<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        let mut iter = iter.into_iter();

        if iter.size_hint().0 > N {
            Self { repr: InliningBufRepr::Allocated(iter.collect()) }
        } else {
            match ArrayBuf::try_from_iter(&mut iter) {
                Ok(buf) => {
                    Self { repr: InliningBufRepr::Inlined(buf) }
                },
    
                Err((ts, t)) => {
                    let buf = ts.into_iter()
                        .chain(iter::once(t))
                        .chain(iter)
                        .collect();
    
                    Self { repr: InliningBufRepr::Allocated(buf) }
                },
            }
        }
    }
}

impl<T, const N: usize> fmt::Debug for InliningBuf<T, N>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_ref(), f)
    }
}

#[derive(Archive, Serialize, Deserialize, Clone)]
pub enum InliningBufRepr<T, const N: usize> {
    Inlined(ArrayBuf<T, N>),
    Allocated(Vec<T>),
}

pub struct ArrayBuf<T, const N: usize> {
    /// The fixed-size buffer that stores the items. The first `len` items must be initialised
    /// and valid.
    buf: [MaybeUninit<T>; N],
    /// The length of the initialised prefix of the buffer. Must be `<= N`.
    len: usize,
}

impl<T: Archive, const N: usize> Archive for ArrayBuf<T, N> {
    type Archived = ArchivedVec<T::Archived>;

    type Resolver = VecResolver;

    unsafe fn resolve(&self, pos: usize, resolver: Self::Resolver, out: *mut Self::Archived) {
        ArchivedVec::resolve_from_len(self.len(), pos, resolver, out);
    }
}

impl<T, S, const N: usize> Serialize<S> for ArrayBuf<T, N>
where
    T: Serialize<S>,
    S: ScratchSpace + Serializer + ?Sized,
{
    #[inline]
    fn serialize(&self, serializer: &mut S) -> Result<Self::Resolver, S::Error> {
        ArchivedVec::serialize_from_slice(self.as_slice(), serializer)
    }
}

impl<T, D, const N: usize> Deserialize<ArrayBuf<T, N>, D> for ArchivedVec<T::Archived>
where
    T: Archive,
    D: Fallible + ?Sized,
    T::Archived: Deserialize<T, D>,
{
    #[inline]
    fn deserialize(&self, deserializer: &mut D) -> Result<ArrayBuf<T, N>, D::Error> {
        let vec = <Self as Deserialize<Vec<T>, D>>::deserialize(self, deserializer)?;
        ArrayBuf::try_from_iter(&mut vec.into_iter()).ok().unwrap().ok()
    }
}

impl<T, const N: usize> ArrayBuf<T, N> {
    pub fn new() -> Self {
        // SAFETY:
        // An array of `MaybeUninit<T>` does not need any initialisation to be valid.
        let buf = unsafe {
            MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init()
        };

        // SAFETY:
        // `0 <= N` always holds because `usize` is unsigned, and it is vacuously true that the
        // first 0 elements of `buf` are initialised.
        unsafe { Self::from_raw_parts(buf, 0) }
    }

    /// # Safety
    /// `len <= N` must hold. The first `len` elements of `buf` must be initialised and valid.
    unsafe fn from_raw_parts(buf: [MaybeUninit<T>; N], len: usize) -> Self {
        Self { buf, len }
    }

    /// # Safety
    /// `slice.len() <= N` must hold.
    unsafe fn clone_from_slice_unchecked(slice: &[T]) -> Self
    where
        T: Clone,
    {
        // SAFETY:
        // An array of `MaybeUninit<T>` does not need any initialisation to be valid.
        let mut buf = unsafe {
            MaybeUninit::<[MaybeUninit<T>; N]>::uninit().assume_init()
        };

        for (i, item) in slice.iter().enumerate() {
            // SAFETY:
            // The caller is responsible for ensuring that `slice.len() <= N`. 
            unsafe {
                *buf.get_unchecked_mut(i) = MaybeUninit::new(item.clone())
            }
        }

        // SAFETY:
        // The caller is responsible for ensuring that `slice.len() <= N`. The first `slice.len()`
        // elements of `buf` are initialised and valid because we cloned them from a slice of
        // initialised `T`s.
        unsafe { Self::from_raw_parts(buf, slice.len()) }
    }

    // FIXME: add a `copy_from_slice` method which uses `ptr::copy_nonoverlapping` rather than
    // individually cloning items.
    pub fn clone_from_slice(slice: &[T]) -> Option<Self>
    where
        T: Clone,
    {
        if slice.len() > N {
            return None;
        }

        // SAFETY:
        // We just checked that `slice.len() <= N`.
        unsafe { Some(Self::clone_from_slice_unchecked(slice)) }
    }

    fn try_from_iter<I>(iter: &mut I) -> Result<Self, ([T; N], T)>
    where
        I: Iterator<Item = T>,
    {
        // We start from an empty `ArrayBuf` and incrementally fill it up so that if the iterator
        // panics, the `Drop` implementation of `ArrayBuf` will clean up the `T`s we got from the
        // iterator.
        let mut this = Self::new();
        
        for item in iter.by_ref().take(N) {
            // SAFETY:
            // We iterate at most `N` items, and each `push_unchecked` increments the length by 1,
            // so `this.len < N` must hold at the start of each iteration.
            unsafe {
                this.push_unchecked(item);
            }
        }

        if this.len == N {
            if let Some(item) = iter.next() {
                // SAFETY:
                // We have just checked that `this.len == N`.
                let buf = unsafe { this.into_array_unchecked() };

                return Err((buf, item));
            }
        }

        Ok(this)
    }

    pub fn as_slice(&self) -> &[T] {
        // SAFETY:
        // It is an invariant of `ArrayBuf` that `len <= N`.
        let initialised_prefix = unsafe { self.buf.get_unchecked(..self.len) };

        // SAFETY:
        // `MaybeUninit<T>` has the same layout as `T` when it is initialised, 
        // It is an invariant of `ArrayBuf` that the first `len` elements of the array are
        // initialised and valid
        unsafe { &*(initialised_prefix as *const [MaybeUninit<T>] as *const [T]) }
    }

    pub fn iter(&self) -> slice::Iter<T> {
        self.as_slice().iter()
    }

    pub fn into_array(self) -> Result<[T; N], Self> {
        if self.len == N {
            // SAFETY:
            // We have just checked that `self.len == N`.
            let buf = unsafe { self.into_array_unchecked() };
            Ok(buf)
        } else {
            Err(self)
        }
    }

    /// # Safety
    /// `self.len == N` must hold.
    unsafe fn into_array_unchecked(self) -> [T; N] {
        // Use `ManuallyDrop` to prevent `self` from being dropped; we do not want to call its
        // destructor because we are moving `self.buf` out of `self`.
        let this = ManuallyDrop::new(self);

        // SAFETY:
        // `MaybeUninit<T>` has the same layout as `T` when it is initialised. The caller is
        // responsible for ensuring that `self.len == N`, in which case every element of `self.buf`
        // is initialised. Copying the `buf` out of `this` is sound because we do not use `this` /
        // `self` again, and the destructor for `this` is not called because it is wrapped in a
        // `ManuallyDrop`.
        let buf = unsafe { mem::transmute_copy::<[MaybeUninit<T>; N], [T; N]>(&this.buf) };

        buf
    }

    pub fn push(&mut self, item: T) -> Result<(), T> {
        if self.len < N {
            // SAFETY:
            // We have just checked that `self.len < N`.
            unsafe {
                self.push_unchecked(item);
            }
            Ok(())
        } else {
            Err(item)
        }
    }

    /// # Safety
    /// `self.len < N` must hold.
    unsafe fn push_unchecked(&mut self, item: T) {
        unsafe {
            *self.buf.get_unchecked_mut(self.len) = MaybeUninit::new(item);
        }
        self.len += 1;
    }
}

impl<T, const N: usize> Drop for ArrayBuf<T, N> {
    fn drop(&mut self) {
        // SAFETY:
        // It is an invariant of `ArrayBuf` that `len <= N`.
        let initialised_prefix = unsafe { self.buf.get_unchecked_mut(..self.len) };

        for item in initialised_prefix {
            // SAFETY:
            // It is an invariant of `ArrayBuf` that the first `len` elements of the array are
            // initialised and valid.
            unsafe {
                item.assume_init_drop();
            }
        }
    }
}

impl<T, const N: usize> AsRef<[T]> for ArrayBuf<T, N> {
    fn as_ref(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> Borrow<[T]> for ArrayBuf<T, N> {
    fn borrow(&self) -> &[T] {
        self
    }
}

impl<T, const N: usize> Deref for ArrayBuf<T, N> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<T, const N: usize> Clone for ArrayBuf<T, N>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        // SAFETY:
        // It is an invariant of `ArrayBuf` that `len <= N`.
        unsafe { Self::clone_from_slice_unchecked(self.as_slice()) }
    }
}

impl<T, const N: usize> PartialEq for ArrayBuf<T, N>
where
    T: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        self.as_ref() == other.as_ref()
    }
}

impl<T, const N: usize> Eq for ArrayBuf<T, N>
where
    T: Eq,
{}

impl<T, const N: usize> fmt::Debug for ArrayBuf<T, N>
where
    T: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_ref(), f)
    }
}

#[cfg(test)]
mod test {
    use crate::utils::{InliningBuf, InliningBufRepr};

    use super::ArrayBuf;

    #[test]
    fn test_array_buf() {
        let strings_1 = &[
            "hello, world".to_owned(),
            "lorem ipsum".to_owned(),
        ];

        let strings_2 = &[
            "hello, world".to_owned(),
        ];

        let strings_3 = &[
            "HELLO, WORLD".to_owned(),
            "lorem ipsum".to_owned(),
        ];

        let strings_4 = &[
            "abc".to_owned(),
            "def".to_owned(),
            "hij".to_owned(),
        ];

        {
            let array_buf = ArrayBuf::<String, 2>::clone_from_slice(strings_1).unwrap();
            assert_eq!(array_buf.as_ref(), strings_1);
            assert_ne!(array_buf.as_ref(), strings_2);
            assert_ne!(array_buf.as_ref(), strings_3);
            assert_ne!(array_buf.as_ref(), <&[String]>::default());
        }

        {
            let array_buf = ArrayBuf::<String, 3>::clone_from_slice(strings_1).unwrap();
            assert_eq!(array_buf.as_ref(), strings_1);
            assert_ne!(array_buf.as_ref(), strings_2);
            assert_ne!(array_buf.as_ref(), strings_3);
            assert_ne!(array_buf.as_ref(), <&[String]>::default());
        }

        {
            let array_buf = ArrayBuf::<String, 100>::clone_from_slice(strings_1).unwrap();
            assert_eq!(array_buf.as_ref(), strings_1);
            assert_ne!(array_buf.as_ref(), strings_2);
            assert_ne!(array_buf.as_ref(), strings_3);
            assert_ne!(array_buf.as_ref(), <&[String]>::default());
        }

        {
            let array_buf = ArrayBuf::<String, 0>::clone_from_slice(&[]).unwrap();
            assert_ne!(array_buf.as_ref(), strings_1);
            assert_ne!(array_buf.as_ref(), strings_2);
            assert_ne!(array_buf.as_ref(), strings_3);
            assert_eq!(array_buf.as_ref(), <&[String]>::default());
        }

        assert!(ArrayBuf::<String, 1>::clone_from_slice(strings_1).is_none());
        assert!(ArrayBuf::<String, 0>::clone_from_slice(strings_1).is_none());

        {
            let array_buf_1 = ArrayBuf::<String, 2>::clone_from_slice(strings_1).unwrap();
            let array_buf_2 = array_buf_1.clone();
            assert_eq!(array_buf_1, array_buf_2);
        }

        assert_eq!(
            ArrayBuf::<String, 3>::try_from_iter(&mut strings_4.iter().cloned()).as_deref(),
            Ok(strings_4.as_ref())
        );

        assert_eq!(
            ArrayBuf::<String, 4>::try_from_iter(&mut strings_4.iter().cloned()).as_deref(),
            Ok(strings_4.as_ref())
        );

        assert_eq!(
            ArrayBuf::<String, 2>::try_from_iter(&mut strings_4.iter().cloned()).as_deref(),
            Err(&(["abc".to_owned(), "def".to_owned()], "hij".to_owned()))
        );
    }

    #[test]
    fn test_inlining_buf() {
        let strings = &[
            "hello, world".to_owned(),
            "lorem ipsum".to_owned(),
        ];

        {
            let inlining_buf = InliningBuf::<String, 2>::clone_from_slice(strings);
            assert_eq!(inlining_buf.as_ref(), strings);
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Inlined(_)));
        }

        {
            let inlining_buf = InliningBuf::<String, 3>::clone_from_slice(strings);
            assert_eq!(inlining_buf.as_ref(), strings);
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Inlined(_)));
        }

        {
            let inlining_buf = InliningBuf::<String, 100>::clone_from_slice(strings);
            assert_eq!(inlining_buf.as_ref(), strings);
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Inlined(_)));
        }

        {
            let inlining_buf = InliningBuf::<String, 1>::clone_from_slice(strings);
            assert_eq!(inlining_buf.as_ref(), strings);
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Allocated(_)));
        }

        {
            let inlining_buf = InliningBuf::<String, 0>::clone_from_slice(strings);
            assert_eq!(inlining_buf.as_ref(), strings);
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Allocated(_)));
        }

        {
            let inlining_buf = InliningBuf::<String, 0>::clone_from_slice(&[]);
            assert_eq!(inlining_buf.as_ref(), <&[String]>::default());
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Inlined(_)));
        }

        {
            let inlining_buf = strings.iter().cloned().collect::<InliningBuf<String, 2>>();
            assert_eq!(inlining_buf.as_ref(), strings);
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Inlined(_)));
        }

        {
            let inlining_buf = strings.iter().cloned().collect::<InliningBuf<String, 3>>();
            assert_eq!(inlining_buf.as_ref(), strings);
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Inlined(_)));
        }

        {
            let inlining_buf = strings.iter().cloned().collect::<InliningBuf<String, 1>>();
            assert_eq!(inlining_buf.as_ref(), strings);
            assert!(matches!(inlining_buf.repr, InliningBufRepr::Allocated(_)));
        }
    }
}
