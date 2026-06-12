//! ID-keyed storage primitives used by the solver.
//!
//! These traits are intentionally narrower than general-purpose maps and sets.
//! They model small pieces of solver state keyed by provider-owned IDs. The
//! storage implementation is selected by the ID type, so dense IDs can keep
//! using vector/bitset-backed storage while sparse IDs use hash-backed storage.

use std::{
    collections::{HashMap, HashSet},
    fmt,
    hash::{BuildHasher, Hash},
    marker::PhantomData,
};

use crate::{IndexedSet, id::DenseIndex};

macro_rules! impl_dense_index_for_int {
    ($($ty:ty),* $(,)?) => {
        $(
            impl crate::id::DenseIndex for $ty {
                fn from_index(index: usize) -> Self {
                    index.try_into().expect("solver id overflow")
                }

                fn to_index(self) -> usize {
                    self.try_into().expect("solver id does not fit in usize")
                }
            }
        )*
    };
}

impl_dense_index_for_int!(u16, u32, u64);

/// Dense zero-based ID with a domain tag and configurable integer width.
///
/// Dense IDs select vector/bitset-backed storage through [`SolverId`]. The
/// `Tag` parameter keeps independent ID domains from being mixed accidentally.
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct DenseId<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static = u32> {
    raw: Repr,
    _marker: PhantomData<fn(Tag) -> Tag>,
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> DenseId<Tag, Repr> {
    /// Constructs an ID from its raw representation.
    ///
    /// For dense IDs the raw representation is the zero-based index.
    pub fn from_raw(raw: Repr) -> Self {
        Self {
            raw,
            _marker: PhantomData,
        }
    }

    /// Returns the raw integer representation.
    pub fn into_raw(self) -> Repr {
        self.raw
    }
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> Copy for DenseId<Tag, Repr> {}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> Clone for DenseId<Tag, Repr> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> PartialEq
    for DenseId<Tag, Repr>
{
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> Eq for DenseId<Tag, Repr> {}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> Hash for DenseId<Tag, Repr> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.raw.hash(state);
    }
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> fmt::Debug
    for DenseId<Tag, Repr>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.raw.fmt(f)
    }
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static + Ord> Ord
    for DenseId<Tag, Repr>
{
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.raw.cmp(&other.raw)
    }
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static + Ord> PartialOrd
    for DenseId<Tag, Repr>
{
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> DenseIndex
    for DenseId<Tag, Repr>
{
    fn from_index(x: usize) -> Self {
        Self::from_raw(Repr::from_index(x))
    }

    fn to_index(self) -> usize {
        self.raw.to_index()
    }
}

impl<Tag, Repr: DenseIndex + Copy + Eq + Hash + fmt::Debug + 'static> SolverId
    for DenseId<Tag, Repr>
{
    type Map<V: Copy + Default> = Vec<V>;
    type Set = IndexedSet<Self>;
}

/// Sparse ID with a domain tag and configurable integer width.
///
/// Sparse IDs select hash-backed storage through [`SolverId`].
#[repr(transparent)]
pub struct SparseId<
    Tag,
    Repr: Copy + Eq + Hash + fmt::Debug + 'static = u32,
    H = ahash::RandomState,
> {
    raw: Repr,
    _marker: PhantomData<fn(Tag, H) -> Tag>,
}

impl<Tag, Repr: Copy + Eq + Hash + fmt::Debug + 'static, H> SparseId<Tag, Repr, H> {
    /// Constructs an ID from its raw integer representation.
    pub fn from_raw(raw: Repr) -> Self {
        Self {
            raw,
            _marker: PhantomData,
        }
    }

    /// Returns the raw integer representation.
    pub fn into_raw(self) -> Repr {
        self.raw
    }
}

impl<Tag, Repr: Copy + Eq + Hash + fmt::Debug + 'static, H> Copy for SparseId<Tag, Repr, H> {}

impl<Tag, Repr: Copy + Eq + Hash + fmt::Debug + 'static, H> Clone for SparseId<Tag, Repr, H> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<Tag, Repr: Copy + Eq + Hash + fmt::Debug + 'static, H> PartialEq for SparseId<Tag, Repr, H> {
    fn eq(&self, other: &Self) -> bool {
        self.raw == other.raw
    }
}

impl<Tag, Repr: Copy + Eq + Hash + fmt::Debug + 'static, H> Eq for SparseId<Tag, Repr, H> {}

impl<Tag, Repr: Copy + Eq + Hash + fmt::Debug + 'static, H> Hash for SparseId<Tag, Repr, H> {
    fn hash<HA: std::hash::Hasher>(&self, state: &mut HA) {
        self.raw.hash(state);
    }
}

impl<Tag, Repr: Copy + Eq + Hash + fmt::Debug + 'static, H> fmt::Debug for SparseId<Tag, Repr, H> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.raw.fmt(f)
    }
}

impl<Tag, Repr: Copy + Eq + Hash + fmt::Debug + 'static, H: Default + BuildHasher> SolverId
    for SparseId<Tag, Repr, H>
{
    type Map<V: Copy + Default> = HashMap<Self, V, H>;
    type Set = HashSet<Self, H>;
}

/// A total map keyed by solver IDs.
///
/// This is intentionally not a general-purpose associative map. Every key has
/// an implicit value of `V::default()` until explicitly overwritten. Callers
/// that need absence should use an optional value, e.g.
/// `IdMap<SolvableId, Option<DependenciesId>>`.
///
/// Values are required to be [`Copy`] because these maps are used on solver hot
/// paths and often behind interior-mutability wrappers. Returning values by
/// copy avoids exposing references into either dense vector-backed storage or
/// sparse hash-backed storage, and keeps mutation/lookup aliasing simple.
/// Store larger data in an arena or cache and put the small handle in this map.
pub trait IdMap<K, V: Copy + Default> {
    /// Returns the value for `key`, or `V::default()` if no value was written.
    fn get(&self, key: K) -> V;

    /// Sets the value for `key`.
    fn set(&mut self, key: K, value: V);

    /// Visits explicitly stored values.
    ///
    /// Dense maps visit every allocated slot. Sparse maps visit only entries
    /// that were explicitly written.
    fn for_each_mut(&mut self, visit: impl FnMut(&mut V));

    /// Immutable variant of [`Self::for_each_mut`].
    fn for_each(&self, visit: impl FnMut(&V));
}

/// A set keyed by solver IDs.
pub trait IdSet<K> {
    /// Returns whether `key` is in the set.
    fn contains(&self, key: K) -> bool;

    /// Inserts `key` into the set. Returns `true` if it was newly inserted.
    fn insert(&mut self, key: K) -> bool;
}

/// A provider-owned ID that selects the storage used for ID-keyed solver state.
pub trait SolverId: Copy + Eq + Hash + std::fmt::Debug {
    /// Default-valued map storage for this ID.
    type Map<V: Copy + Default>: IdMap<Self, V> + Default;

    /// Set storage for this ID.
    type Set: IdSet<Self> + Default;
}

/// Dense map storage backed by a `Vec<V>`.
impl<K: DenseIndex, V: Copy + Default> IdMap<K, V> for Vec<V> {
    fn get(&self, key: K) -> V {
        self.as_slice()
            .get(key.to_index())
            .copied()
            .unwrap_or_default()
    }

    fn set(&mut self, key: K, value: V) {
        let idx = key.to_index();
        if idx >= self.len() {
            self.resize(idx + 1, V::default());
        }
        self[idx] = value;
    }

    fn for_each_mut(&mut self, visit: impl FnMut(&mut V)) {
        self.iter_mut().for_each(visit);
    }

    fn for_each(&self, visit: impl FnMut(&V)) {
        self.iter().for_each(visit);
    }
}

impl<K: DenseIndex> IdSet<K> for IndexedSet<K> {
    fn contains(&self, key: K) -> bool {
        IndexedSet::contains(self, key)
    }

    fn insert(&mut self, key: K) -> bool {
        IndexedSet::insert(self, key)
    }
}

/// Sparse map storage backed by a hash map.
impl<K: Eq + Hash, V: Copy + Default, S: BuildHasher> IdMap<K, V> for HashMap<K, V, S> {
    fn get(&self, key: K) -> V {
        HashMap::get(self, &key).copied().unwrap_or_default()
    }

    fn set(&mut self, key: K, value: V) {
        HashMap::insert(self, key, value);
    }

    fn for_each_mut(&mut self, visit: impl FnMut(&mut V)) {
        HashMap::values_mut(self).for_each(visit);
    }

    fn for_each(&self, visit: impl FnMut(&V)) {
        HashMap::values(self).for_each(visit);
    }
}

/// Sparse set storage backed by a hash set.
impl<K: Eq + Hash, H: BuildHasher> IdSet<K> for HashSet<K, H> {
    fn contains(&self, key: K) -> bool {
        HashSet::contains(self, &key)
    }

    fn insert(&mut self, key: K) -> bool {
        HashSet::insert(self, key)
    }
}
