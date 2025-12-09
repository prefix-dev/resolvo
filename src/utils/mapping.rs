use std::{cmp, iter::FusedIterator, marker::PhantomData};

use crate::internal::arena::ArenaId;

const VALUES_PER_CHUNK: usize = 128;

/// A `Mapping<TValue>` holds a collection of `TValue`s that can be addressed by
/// `TId`s. You can think of it as a HashMap<TId, TValue>, optimized for the
/// case in which we know the `TId`s are contiguous.
#[derive(Clone)]
pub struct Mapping<TId, TValue> {
    chunks: Vec<[Option<TValue>; VALUES_PER_CHUNK]>,
    len: usize,
    max: usize,
    _phantom: PhantomData<TId>,
}

impl<TId: ArenaId, TValue> Default for Mapping<TId, TValue> {
    fn default() -> Self {
        Self::new()
    }
}

impl<TId: ArenaId, TValue> Mapping<TId, TValue> {
    pub(crate) fn new() -> Self {
        Self::with_capacity(1)
    }

    /// Returns the total number of values that can be stored in the mapping without reallocating.
    pub fn capacity(&self) -> usize {
        self.chunks.len() * VALUES_PER_CHUNK
    }

    /// Returns the total number of bytes allocated by this instance.
    pub fn size_in_bytes(&self) -> usize {
        self.capacity() * std::mem::size_of::<Option<TValue>>()
    }

    /// Constructs a new arena with a capacity for `n` values pre-allocated.
    pub fn with_capacity(n: usize) -> Self {
        let n = cmp::max(1, n);
        let n_chunks = (n - 1) / VALUES_PER_CHUNK + 1;
        let mut chunks = Vec::new();
        chunks.resize_with(n_chunks, || std::array::from_fn(|_| None));
        Self {
            chunks,
            len: 0,
            max: 0,
            _phantom: Default::default(),
        }
    }

    /// Get chunk and offset for specific id
    #[inline]
    pub const fn chunk_and_offset(id: usize) -> (usize, usize) {
        let chunk = id / VALUES_PER_CHUNK;
        let offset = id % VALUES_PER_CHUNK;
        (chunk, offset)
    }

    /// Insert into the mapping with the specific value
    pub fn insert(&mut self, id: TId, value: TValue) -> Option<TValue> {
        let idx = id.to_usize();
        let (chunk, offset) = Self::chunk_and_offset(idx);

        // Resize to fit if needed
        if chunk >= self.chunks.len() {
            self.chunks
                .resize_with(chunk + 1, || std::array::from_fn(|_| None));
        }
        let previous_value = self.chunks[chunk][offset].replace(value);
        if previous_value.is_none() {
            self.len += 1;
        }
        self.max = self.max.max(idx);
        previous_value
    }

    /// Unset a specific value in the mapping, returns the previous value.
    pub fn unset(&mut self, id: TId) -> Option<TValue> {
        let idx = id.to_usize();
        let (chunk, offset) = Self::chunk_and_offset(idx);
        if chunk >= self.chunks.len() {
            return None;
        }

        let previous_value = self.chunks[chunk][offset].take();
        if previous_value.is_some() {
            self.len -= 1;
        }
        previous_value
    }

    /// Get a specific value in the mapping with bound checks
    pub fn get(&self, id: TId) -> Option<&TValue> {
        let (chunk, offset) = Self::chunk_and_offset(id.to_usize());
        if chunk >= self.chunks.len() {
            return None;
        }

        // Safety: we know that the chunk and offset are valid
        unsafe {
            self.chunks
                .get_unchecked(chunk)
                .get_unchecked(offset)
                .as_ref()
        }
    }

    /// Get a mutable specific value in the mapping with bound checks
    pub fn get_mut(&mut self, id: TId) -> Option<&mut TValue> {
        let (chunk, offset) = Self::chunk_and_offset(id.to_usize());
        if chunk >= self.chunks.len() {
            return None;
        }

        // Safety: we know that the chunk and offset are valid
        unsafe {
            self.chunks
                .get_unchecked_mut(chunk)
                .get_unchecked_mut(offset)
                .as_mut()
        }
    }

    /// Get a specific value in the mapping without bound checks
    ///
    /// # Safety
    /// The caller must uphold most of the safety requirements for
    /// `get_unchecked`. i.e. the id having been inserted into the Mapping
    /// before.
    pub unsafe fn get_unchecked(&self, id: TId) -> &TValue {
        let (chunk, offset) = Self::chunk_and_offset(id.to_usize());
        unsafe { self.chunks.get_unchecked(chunk).get_unchecked(offset) }
            .as_ref()
            .unwrap()
    }

    /// Get a specific value in the mapping without bound checks
    ///
    /// # Safety
    /// The caller must uphold most of the safety requirements for
    /// `get_unchecked_mut`. i.e. the id having been inserted into the Mapping
    /// before.
    pub unsafe fn get_unchecked_mut(&mut self, id: TId) -> &mut TValue {
        let (chunk, offset) = Self::chunk_and_offset(id.to_usize());
        unsafe {
            self.chunks
                .get_unchecked_mut(chunk)
                .get_unchecked_mut(offset)
        }
        .as_mut()
        .unwrap()
    }

    /// Returns the number of mapped items
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the Mapping is empty
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Returns the maximum id that has been inserted
    pub(crate) fn max(&self) -> usize {
        self.max
    }

    /// Defines the number of slots that can be used
    /// theses slots are not initialized
    pub fn slots(&self) -> usize {
        self.chunks.len() * VALUES_PER_CHUNK
    }

    /// Returns an iterator over all the existing key value pairs.
    pub fn iter(&self) -> MappingIter<'_, TId, TValue> {
        MappingIter {
            mapping: self,
            offset: 0,
        }
    }
}

/// An iterator over a [`Mapping`]
pub struct MappingIter<'a, TId, TValue> {
    mapping: &'a Mapping<TId, TValue>,
    offset: usize,
}

impl<'a, TId: ArenaId, TValue> Iterator for MappingIter<'a, TId, TValue> {
    type Item = (TId, &'a TValue);

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if self.offset >= self.mapping.len {
                return None;
            }

            let (chunk, offset) = Mapping::<TId, TValue>::chunk_and_offset(self.offset);
            let id = TId::from_usize(self.offset);
            self.offset += 1;

            unsafe {
                if let Some(value) = &self
                    .mapping
                    .chunks
                    .get_unchecked(chunk)
                    .get_unchecked(offset)
                {
                    break Some((id, value));
                }
            }
        }
    }
}

impl<TId: ArenaId, TValue> FusedIterator for MappingIter<'_, TId, TValue> {}

#[cfg(feature = "serde")]
impl<K: ArenaId, V: serde::Serialize> serde::Serialize for Mapping<K, V> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.chunks
            .iter()
            .flatten()
            .take(self.max() + 1)
            .collect::<Vec<_>>()
            .serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, K: ArenaId, V: serde::Deserialize<'de>> serde::Deserialize<'de> for Mapping<K, V> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let values = Vec::<Option<V>>::deserialize(deserializer)?;
        let mut mapping = Mapping::with_capacity(values.len());
        for (i, value) in values.into_iter().enumerate() {
            if let Some(value) = value {
                mapping.insert(K::from_usize(i), value);
            }
        }
        Ok(mapping)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Id {
        id: usize,
    }

    impl ArenaId for Id {
        fn from_usize(x: usize) -> Self {
            Id { id: x }
        }

        fn to_usize(self) -> usize {
            self.id
        }
    }

    #[test]
    pub fn test_mapping() {
        // New mapping should have 128 slots per default
        let mut mapping = Mapping::<Id, usize>::new();
        assert_eq!(mapping.len(), 0);
        assert_eq!(mapping.slots(), VALUES_PER_CHUNK);

        // Inserting a value should increase the length
        // and the number of slots should stay the same
        mapping.insert(Id::from_usize(0), 10usize);
        assert_eq!(mapping.len(), 1);

        // Should be able to get it
        assert_eq!(*mapping.get(Id::from_usize(0)).unwrap(), 10usize);
        assert_eq!(mapping.slots(), VALUES_PER_CHUNK);

        // Inserting higher than the slot size should trigger a resize
        mapping.insert(Id::from_usize(VALUES_PER_CHUNK), 20usize);
        assert_eq!(
            *mapping.get(Id::from_usize(VALUES_PER_CHUNK)).unwrap(),
            20usize
        );

        // Now contains 2 elements
        assert_eq!(mapping.len(), 2);
        // And double number of slots due to resize
        assert_eq!(mapping.slots(), VALUES_PER_CHUNK * 2);
    }

    #[cfg(feature = "serde")]
    #[test]
    pub fn test_serde() {
        use serde_json::{from_value, to_value};

        let values = [1, 3, 6, 9, 2, 4, 6, 1, 2, 3];
        let json = to_value(values).unwrap();
        let mapping =
            values
                .iter()
                .copied()
                .enumerate()
                .fold(Mapping::new(), |mut mapping, (i, v)| {
                    mapping.insert(Id::from_usize(i), v);
                    mapping
                });

        assert_eq!(json, to_value(&mapping).unwrap());
        itertools::assert_equal(
            mapping.iter().map(|(_, &v)| v),
            from_value::<Vec<i32>>(json).unwrap(),
        );
    }
}
