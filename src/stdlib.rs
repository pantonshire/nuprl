use crate::{object_id::ObjectId, phase3_proofck::library::Library, path::path::{CanonLibPath, LibPathBuf, LibPathNode}};

#[derive(Default, Debug)]
pub struct StdLibObjs {
    pub universe: Option<ObjectId>,
    pub int: Option<ObjectId>,
    pub atom: Option<ObjectId>,
    pub eq: Option<ObjectId>,
    pub func: Option<ObjectId>,
    pub prod: Option<ObjectId>,
    pub sum: Option<ObjectId>,
    pub isect: Option<ObjectId>,
    pub rectype: Option<ObjectId>,
    pub ax: Option<ObjectId>,
    pub lambda: Option<ObjectId>,
    pub app: Option<ObjectId>,
    pub pair: Option<ObjectId>,
    pub spread: Option<ObjectId>,
    pub inl: Option<ObjectId>,
    pub inr: Option<ObjectId>,
    pub decide: Option<ObjectId>,
    pub compare_eq: Option<ObjectId>,
    pub compare_lt: Option<ObjectId>,
    pub fix: Option<ObjectId>,
    pub cbv: Option<ObjectId>,
    pub neg: Option<ObjectId>,
    pub add: Option<ObjectId>,
    pub mul: Option<ObjectId>,
    pub div: Option<ObjectId>,
    pub rem: Option<ObjectId>,
}

impl StdLibObjs {
    pub fn from_library(library: &Library) -> Self {
        let names = library.names();

        Self {
            universe: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("U".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            int: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("Int".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            atom: {
                names
                .get_obj(
                    CanonLibPath::ROOT, 
                    &LibPathBuf::new([LibPathNode::Named("Atom".into())].into(), true)
                )
                .ok()
                .map(|(id, _, _)| id)
            },
            eq: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("Eq".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            func: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("Fn".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            prod: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("Prod".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            sum: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("Sum".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            isect: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("Isect".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            rectype: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("Rectype".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            ax: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("ax".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            lambda: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("lambda".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            app: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("app".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            pair: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("pair".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            spread: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("spread".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            inl: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("inl".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            inr: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("inr".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            decide: {
                names
                .get_obj(
                    CanonLibPath::ROOT, 
                    &LibPathBuf::new([LibPathNode::Named("decide".into())].into(), true)
                )
                .ok()
                .map(|(id, _, _)| id)
            },
            compare_eq: {
                names
                .get_obj(
                    CanonLibPath::ROOT, 
                    &LibPathBuf::new([LibPathNode::Named("compare_eq".into())].into(), true)
                )
                .ok()
                .map(|(id, _, _)| id)
            },
            compare_lt: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("compare_lt".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            fix: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("fix".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            cbv: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("cbv".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            neg: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("arith_neg".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            add: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("arith_add".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            mul: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("arith_mul".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            div: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("arith_div".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
            rem: {
                names
                    .get_obj(
                        CanonLibPath::ROOT, 
                        &LibPathBuf::new([LibPathNode::Named("arith_rem".into())].into(), true)
                    )
                    .ok()
                    .map(|(id, _, _)| id)
            },
        }
    }
}
