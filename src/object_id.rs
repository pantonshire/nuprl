use rkyv::{Archive, Serialize, Deserialize};

#[derive(Debug)]
pub struct ObjectIdGen {
    namespace_mask: u128,
    next_id: u64,
}

impl ObjectIdGen {
    pub fn new(namespace: u64) -> Self {
        let namespace_mask = u128::from(namespace) << 64;
        Self { namespace_mask, next_id: 0 }
    }

    pub fn next_id(&mut self) -> ObjectId {
        let next_id = self.next_id;
        self.next_id += 1;
        ObjectId(u128::from(next_id) | self.namespace_mask)
    }
}

#[derive(Archive, Serialize, Deserialize, serde::Serialize, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct ObjectId(u128);

impl ObjectId {
    pub fn inner_val(self) -> u128 {
        self.0
    }
}
