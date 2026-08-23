use std::marker::PhantomData;

use crate::id::DenseIndex;

const WORD_BITS: usize = usize::BITS as usize;

/// A dense set keyed by a [`DenseIndex`]. Equivalent to a `HashSet<Id>` but
/// backed by native machine words, so test-and-set is O(1) with no hashing
/// overhead. Grows on demand to fit the largest inserted index.
pub struct IndexedSet<Id> {
    words: Vec<usize>,
    _marker: PhantomData<fn(Id) -> Id>,
}

impl<Id> Default for IndexedSet<Id> {
    fn default() -> Self {
        Self {
            words: Vec::new(),
            _marker: PhantomData,
        }
    }
}

impl<Id: DenseIndex> IndexedSet<Id> {
    /// Inserts `id`. Returns `true` if `id` was not already present.
    #[inline]
    pub fn insert(&mut self, id: Id) -> bool {
        let idx = id.to_index();
        let (word, bit) = (idx / WORD_BITS, 1usize << (idx % WORD_BITS));
        if word >= self.words.len() {
            self.words.resize(word + 1, 0);
        }
        let entry = &mut self.words[word];
        let was_set = *entry & bit != 0;
        *entry |= bit;
        !was_set
    }

    /// Returns `true` if `id` is present.
    #[inline]
    pub fn contains(&self, id: Id) -> bool {
        let idx = id.to_index();
        self.words
            .get(idx / WORD_BITS)
            .is_some_and(|word| word & (1usize << (idx % WORD_BITS)) != 0)
    }
}

#[cfg(test)]
mod tests {
    use super::{IndexedSet, WORD_BITS};
    use crate::{DenseIndex, NameId};

    fn id(index: usize) -> NameId {
        NameId::from_index(index)
    }

    #[test]
    fn word_boundaries() {
        let mut set = IndexedSet::<NameId>::default();
        for index in [
            0,
            WORD_BITS - 1,
            WORD_BITS,
            WORD_BITS + 1,
            WORD_BITS * 2 - 1,
            WORD_BITS * 2,
        ] {
            assert!(set.insert(id(index)));
            assert!(set.contains(id(index)));
            assert!(!set.insert(id(index)));
        }
        for index in [1, WORD_BITS - 2, WORD_BITS + 2, WORD_BITS * 2 + 1] {
            assert!(!set.contains(id(index)));
        }
    }

    #[test]
    fn sparse_and_large_indices() {
        let mut set = IndexedSet::<NameId>::default();
        assert!(!set.contains(id(10_000)));
        assert!(set.insert(id(10_000)));
        assert!(set.contains(id(10_000)));
        assert!(!set.contains(id(9_999)));
        assert!(!set.contains(id(10_001)));

        assert!(set.insert(id(0)));
        assert!(set.contains(id(0)));
        assert!(set.contains(id(10_000)));
        assert!(!set.contains(id(WORD_BITS - 1)));
        assert!(!set.contains(id(WORD_BITS)));
        assert!(!set.contains(id(WORD_BITS + 1)));
    }

    #[test]
    fn duplicate_inserts_and_sequential_fill() {
        let mut set = IndexedSet::<NameId>::default();
        for index in 0..=WORD_BITS * 32 {
            assert!(set.insert(id(index)));
        }
        for index in 0..=WORD_BITS * 32 {
            assert!(!set.insert(id(index)));
            assert!(set.contains(id(index)));
        }
        assert!(!set.contains(id(WORD_BITS * 32 + 1)));

        let mut reverse = IndexedSet::<NameId>::default();
        for index in (0..=WORD_BITS * 4).rev() {
            assert!(reverse.insert(id(index)));
        }
        for index in 0..=WORD_BITS * 4 {
            assert!(reverse.contains(id(index)));
        }
    }
}
