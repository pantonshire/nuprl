use std::{
    iter,
    ops::RangeInclusive,
    path::{PathBuf, Path, Component},
    borrow::Cow, num::NonZeroUsize,
    io,
    fmt,
    error,
    str,
};

use serde::Serialize;

use crate::{
    utils::NONZERO_USIZE_ONE,
    path::path::{CanonLibPath, CanonLibPathBuf},
};

pub const NUPRL_EXTENSION: &str = "nuprl";
pub const LIBRARY_EXTENSION: &str = "nulib";
pub const MODULE_FILE: &str = "module";

pub struct SourceIdGen {
    next_id: NonZeroUsize,
}

impl SourceIdGen {
    pub fn new() -> Self {
        Self { next_id: NONZERO_USIZE_ONE }
    }

    pub fn next_id(&mut self) -> SourceId {
        let next_id = self.next_id;
        self.next_id = self.next_id.checked_add(1)
            .expect("all possible source ids exhausted");
        SourceId(next_id)
    }
}

#[derive(Serialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[serde(transparent)]
pub struct SourceId(NonZeroUsize);

#[derive(Serialize, Clone, Copy, PartialEq, Eq, Debug)]
pub enum SourceKind {
    NuprlSrc,
    NuprlLib,
}

impl SourceKind {
    pub fn from_path<P>(path: P) -> Option<Self>
    where
        P: AsRef<Path>,
    {
        match path.as_ref().extension() {
            Some(extension) if extension == NUPRL_EXTENSION => Some(Self::NuprlSrc),
            Some(extension) if extension == LIBRARY_EXTENSION => Some(Self::NuprlLib),
            _ => None,
        }
    }
}

pub enum SourceModule<'a> {
    FromPath {
        base_module: Option<&'a CanonLibPath>,
        base_path: &'a Path,
        full_path: PathBuf,
    },
    Custom(CanonLibPathBuf),
}

#[derive(Debug)]
pub struct Source {
    id: SourceId,
    path: Option<PathBuf>,
    module: CanonLibPathBuf,
    repr: SourceRepr,
}

impl Source {
    pub fn new(
        id: SourceId,
        module: SourceModule,
        kind: SourceKind,
        text: Cow<'static, [u8]>,
    ) -> Result<Self, SourceError>
    {
        let (path, module) = match module {
            SourceModule::FromPath { base_module, base_path, full_path } => {
                let base_module_components = base_module
                    .iter()
                    .flat_map(|base_module| base_module
                        .into_iter()
                        .map(|(_, _, component)| Cow::Borrowed(component)));

                let mut cleaned_path_for_module = full_path
                    .strip_prefix(base_path)
                    .unwrap_or(&full_path)
                    .with_extension("");

                if cleaned_path_for_module
                    .file_name()
                    .map(|file_name| file_name == MODULE_FILE)
                    .unwrap_or(false)
                {
                    cleaned_path_for_module.pop();
                }

                let path_components = cleaned_path_for_module
                    .components()
                    .filter_map(|component| match component {
                        Component::Normal(component) => {
                            Some(component.to_string_lossy())
                        },
                        Component::ParentDir => {
                            panic!("paths containing `..` should not be used as source paths")
                        },
                        _ => None,
                    });

                let module = base_module_components
                    .chain(path_components)
                    .collect();

                (Some(full_path), module)
            },

            SourceModule::Custom(module) => {
                (None, module)
            },
        };

        let repr = match kind {
            SourceKind::NuprlSrc => {
                let text = match text {
                    Cow::Borrowed(text) => {
                        str::from_utf8(text)
                            .map(Cow::Borrowed)
                            .map_err(|_| SourceError::InvalidUtf8)?
                    },
                    Cow::Owned(text) => {
                        String::from_utf8(text)
                            .map(Cow::Owned)
                            .map_err(|_| SourceError::InvalidUtf8)?
                    },
                };
                
                let line_indices = iter::once(0)
                    .chain(text
                        .match_indices('\n')
                        .map(|(index, _)| index + 1))
                    .collect();

                SourceRepr::NuprlSrc { source_text: text, line_indices }
            },

            SourceKind::NuprlLib => {
                SourceRepr::NuprlLib { bytes: text }
            },
        };

        Ok(Self { id, path, module, repr })
    }

    pub fn id(&self) -> SourceId {
        self.id
    }

    pub fn path(&self) -> Option<&Path> {
        self.path.as_deref()
    }

    pub fn module(&self) -> &CanonLibPath {
        &self.module
    }

    pub fn repr(&self) -> &SourceRepr {
        &self.repr
    }

    pub fn kind(&self) -> SourceKind {
        match &self.repr {
            SourceRepr::NuprlSrc { source_text: _, line_indices: _ } => SourceKind::NuprlSrc,
            SourceRepr::NuprlLib { bytes: _ } => SourceKind::NuprlLib,
        }
    }

    pub fn text_source(&self) -> Option<TextSource> {
        match &self.repr {
            SourceRepr::NuprlSrc { source_text, line_indices } => {
                Some(TextSource {
                    id: self.id,
                    module: &self.module,
                    source_text,
                    line_indices,
                })
            },
            SourceRepr::NuprlLib { bytes: _ } => None,
        }
    }
}

#[derive(Serialize, Clone, PartialEq, Eq, Debug)]
#[serde(tag = "tag")]
pub enum SourceRepr {
    NuprlSrc {
        source_text: Cow<'static, str>,
        line_indices: Vec<usize>,
    },
    NuprlLib {
        bytes: Cow<'static, [u8]>,
    },
}

#[derive(Clone, Copy, Debug)]
pub struct TextSource<'a> {
    id: SourceId,
    module: &'a CanonLibPath,
    source_text: &'a str,
    line_indices: &'a [usize],
}

impl<'a> TextSource<'a> {
    pub fn text(self) -> &'a str {
        self.source_text
    }

    pub fn module(self) -> &'a CanonLibPath {
        self.module
    }
    
    pub fn make_span<S>(self, span: S) -> Span
    where
        RangeSpan: From<S>,
    {
        let range_span = RangeSpan::from(span);
        Span {
            source_id: self.id,
            range: range_span,
            visual: self.visual_span_of(range_span),
        }
    }

    fn visual_span_of(self, range_span: RangeSpan) -> VisualSpan {
        VisualSpan::new(
            self.visual_pos_of(range_span.start()),
            self.visual_pos_of(range_span.end())
        )
    }

    fn visual_pos_of(self, index: usize) -> VisualPos {
        let (line, line_index) = {
            let mut line = 0;
            let mut line_index = 0;
            
            for (next_line, next_line_index) in self.line_indices.iter().copied().enumerate() {
                if index < next_line_index {
                    break;
                }
                line = next_line;
                line_index = next_line_index;
            }
            
            (line, line_index)
        };
        
        let col = index - line_index;
        
        VisualPos::new(line, col)
    }
}

#[derive(Debug)]
pub enum SourceError {
    Io(io::Error),
    InvalidUtf8,
}

impl From<io::Error> for SourceError {
    fn from(err: io::Error) -> Self {
        Self::Io(err)
    }
}

impl From<walkdir::Error> for SourceError {
    fn from(err: walkdir::Error) -> Self {
        Self::from(io::Error::from(err))
    }
}

impl fmt::Display for SourceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Io(err) => write!(f, "{}", err),
            Self::InvalidUtf8 => write!(f, "invalid utf-8"),
        }
    }
}

impl error::Error for SourceError {}

#[derive(Serialize, Clone, Copy, PartialEq, Eq, Debug)]
pub struct Span {
    source_id: SourceId,
    range: RangeSpan,
    visual: VisualSpan,
}

impl Span {
    /// Span for use in places where a span is needed but span information is not available. This
    /// is a hack, and all callers should eventually be refactored so that this is not needed.
    #[deprecated]
    pub fn fixme_dummy_span() -> Self {
        Self {
            source_id: SourceId(NONZERO_USIZE_ONE),
            range: RangeSpan { start: 0, end: 0 },
            visual: VisualSpan {
                start: VisualPos { line: 0, col: 0 },
                end: VisualPos { line: 0, col: 0 },
            }
        }
    }

    pub fn visual(self) -> VisualSpan {
        self.visual
    }
}

#[derive(Serialize, Clone, Copy, PartialEq, Eq, Debug)]
pub struct RangeSpan {
    start: usize,
    end: usize,
}

impl RangeSpan {
    pub fn new(start: usize, end: usize) -> Self {
        Self { start, end: end.max(start) }
    }

    pub fn start(self) -> usize {
        self.start
    }

    pub fn end(self) -> usize {
        self.end
    }
}

impl From<RangeInclusive<usize>> for RangeSpan {
    fn from(range: RangeInclusive<usize>) -> Self {
        Self::new(*range.start(), *range.end())
    }
}

impl<'s> From<pest::Span<'s>> for RangeSpan {
    fn from(span: pest::Span<'s>) -> Self {
        Self::new(span.start(), span.end())
    }
}

impl From<pest::error::InputLocation> for RangeSpan {
    fn from(location: pest::error::InputLocation) -> Self {
        match location {
            pest::error::InputLocation::Pos(index) => {
                Self::new(index, index)
            },
            pest::error::InputLocation::Span((start, end)) => {
                Self::new(start, end)
            },
        }
    }
}

#[derive(Serialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct VisualPos {
    line: usize,
    col: usize,
}

impl VisualPos {
    pub fn new(line: usize, col: usize) -> Self {
        Self { line, col }
    }

    pub fn line(self) -> usize {
        self.line
    }

    pub fn col(self) -> usize {
        self.col
    }
}

#[derive(Serialize, Clone, Copy, PartialEq, Eq, Debug)]
pub struct VisualSpan {
    start: VisualPos,
    end: VisualPos,
}

impl VisualSpan {
    pub fn new(start: VisualPos, end: VisualPos) -> Self {
        Self { start, end }
    }

    pub fn start(self) -> VisualPos {
        self.start
    }

    pub fn end(self) -> VisualPos {
        self.end
    }
}
