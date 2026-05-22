use std::marker::PhantomData;

use bitvec::vec::BitVec;

use crate::id::DenseIndex;

/// A dense set keyed by a [`DenseIndex`]. Equivalent to a `HashSet<Id>` but
/// backed by a [`BitVec`], so test-and-set is O(1) with no hashing overhead.
/// Grows on demand to fit the largest inserted index.
pub struct IndexedSet<Id> {
    bits: BitVec,
    _marker: PhantomData<fn(Id) -> Id>,
}

impl<Id> Default for IndexedSet<Id> {
    fn default() -> Self {
        Self {
            bits: BitVec::new(),
            _marker: PhantomData,
        }
    }
}

impl<Id: DenseIndex> IndexedSet<Id> {
    /// Inserts `id`. Returns `true` if `id` was not already present.
    pub fn insert(&mut self, id: Id) -> bool {
        let idx = id.to_index();
        if idx >= self.bits.len() {
            self.bits.resize(idx + 1, false);
        }
        // SAFETY: `resize` above guarantees `idx < self.bits.len()`.
        !unsafe { self.bits.replace_unchecked(idx, true) }
    }

    /// Returns `true` if `id` is present.
    pub fn contains(&self, id: Id) -> bool {
        self.bits.get(id.to_index()).is_some_and(|b| *b)
    }
}
