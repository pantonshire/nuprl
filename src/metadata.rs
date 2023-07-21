use std::collections::BTreeMap;

use serde::Serialize;

use crate::{source::Span, object_id::ObjectId, phase3_proofck::proof::ProofNodeId};

#[derive(Serialize, Debug)]
#[serde(transparent)]
pub struct ObjectMetadataStore {
    inner: BTreeMap<ObjectId, ObjectMetadata>,
}

impl ObjectMetadataStore {
    pub fn new() -> Self {
        Self { inner: BTreeMap::new() }
    }

    pub fn get(&self, id: ObjectId) -> Option<&ObjectMetadata> {
        self.inner.get(&id)
    }

    pub fn insert(&mut self, id: ObjectId, metadata: ObjectMetadata) {
        self.inner.insert(id, metadata);
    }
}

#[derive(Serialize, Debug)]
pub struct ObjectMetadata {
    pub span: Span,
    pub kind: ObjectMedatataKind,
}

impl ObjectMetadata {
    pub fn span(&self) -> Span {
        self.span
    }
}

// FIXME: use `#[serde(tag = ...)]`
#[derive(Serialize, Debug)]
pub enum ObjectMedatataKind {
    #[serde(rename = "def")]
    Def,
    #[serde(rename = "thm")]
    Thm(TheoremMetadata),
    // FIXME: span information for beta reductions
    #[serde(rename = "exp")]
    Exp,
}

#[derive(Serialize, Debug)]
pub struct TheoremMetadata {
    pub nodes: BTreeMap<ProofNodeId, ProofNodeMetadata>,
    pub root_id: ProofNodeId,
}

#[derive(Serialize, Debug)]
pub struct ProofNodeMetadata {
    pub span: Span,
}
