//! Markers that describe how a [`DependencyProvider`] allocates
//! [`SolvableId`]s. The solver uses this hint to pick the most efficient
//! representation for tracking them.
//!
//! Every implementor of [`DependencyProvider`] selects one of these markers
//! via its `SolvableIdLayout` associated type, e.g.
//! `type SolvableIdLayout = resolvo::solvable_id::Sparse;`. See [`Sparse`]
//! and [`Dense`] for guidance on which to pick.
//!
//! [`DependencyProvider`]: crate::DependencyProvider
//! [`SolvableId`]: crate::SolvableId

use std::{cell::UnsafeCell, hash::Hash};

use ahash::{HashSet, HashSetExt};

use crate::{
    SolvableId,
    internal::{arena::ArenaId, indexed_set::IndexedSet},
};

/// Sealed marker trait. Implemented only by [`Sparse`] and [`Dense`].
///
/// Describes how a [`DependencyProvider`] allocates its [`SolvableId`]s. The
/// trait carries no methods and cannot be implemented outside of this crate.
///
/// [`DependencyProvider`]: crate::DependencyProvider
/// [`SolvableId`]: crate::SolvableId
// `Sealed` is intentionally `pub(crate)`: that is what prevents external
// crates from implementing `Layout`. The lint is exactly the sealing
// mechanism, not a mistake.
#[allow(private_bounds)]
pub trait Layout: Default + Sealed {}

/// Pick this when [`SolvableId`]s are not allocated contiguously, span
/// multiple pools, or you're unsure. This is the safe default.
///
/// [`SolvableId`]: crate::SolvableId
#[derive(Default)]
pub struct Sparse;

/// Pick this when [`SolvableId`]s are allocated contiguously from 0, the
/// common case for a single pool. Faster than [`Sparse`] when the assumption
/// holds; otherwise memory grows with the largest id observed.
///
/// [`SolvableId`]: crate::SolvableId
#[derive(Default)]
pub struct Dense;

impl Layout for Sparse {}
impl Layout for Dense {}

/// Sealing trait that also carries the concrete container types each
/// [`Layout`] marker selects.
pub(crate) trait Sealed {
    /// Solvable-keyed lookup of a copyable value.
    type Map<V: Copy>: SolvableMap<Value = V> + Default;
    /// Set of solvable-keyed identifiers.
    type Set<K: ArenaId + Eq + Hash>: SolvableSet<K> + Default;
}

/// Internal solvable-keyed map abstraction. The only way to select between
/// implementations is via the [`Layout`] markers.
pub(crate) trait SolvableMap {
    type Value: Copy;

    fn get(&self, id: SolvableId) -> Option<Self::Value>;
    fn insert(&mut self, id: SolvableId, value: Self::Value);
    #[cfg(feature = "diagnostics")]
    fn size_in_bytes(&self) -> usize;
}

/// Internal solvable-keyed set abstraction. The only way to select between
/// implementations is via the [`Layout`] markers.
pub(crate) trait SolvableSet<K> {
    /// Returns whether `id` is in the set.
    fn contains(&self, id: K) -> bool;
    /// Inserts `id` into the set. Returns `true` if `id` was newly inserted.
    fn insert(&mut self, id: K) -> bool;
}

impl Sealed for Sparse {
    type Map<V: Copy> = SparseMap<V>;
    type Set<K: ArenaId + Eq + Hash> = SparseSet<K>;
}

impl Sealed for Dense {
    type Map<V: Copy> = DenseMap<V>;
    type Set<K: ArenaId + Eq + Hash> = DenseSet<K>;
}

pub(crate) struct SparseMap<V>(ahash::HashMap<SolvableId, V>);

impl<V> Default for SparseMap<V> {
    fn default() -> Self {
        Self(ahash::HashMap::default())
    }
}

impl<V: Copy> SolvableMap for SparseMap<V> {
    type Value = V;

    fn get(&self, id: SolvableId) -> Option<V> {
        self.0.get(&id).copied()
    }

    fn insert(&mut self, id: SolvableId, value: V) {
        self.0.insert(id, value);
    }

    #[cfg(feature = "diagnostics")]
    fn size_in_bytes(&self) -> usize {
        self.0.capacity() * std::mem::size_of::<(SolvableId, V)>()
    }
}

pub(crate) struct DenseMap<V>(Vec<Option<V>>);

impl<V> Default for DenseMap<V> {
    fn default() -> Self {
        Self(Vec::new())
    }
}

impl<V: Copy> SolvableMap for DenseMap<V> {
    type Value = V;

    fn get(&self, id: SolvableId) -> Option<V> {
        self.0.get(id.to_usize()).copied().flatten()
    }

    fn insert(&mut self, id: SolvableId, value: V) {
        let idx = id.to_usize();
        if idx >= self.0.len() {
            self.0.resize(idx + 1, None);
        }
        self.0[idx] = Some(value);
    }

    #[cfg(feature = "diagnostics")]
    fn size_in_bytes(&self) -> usize {
        self.0.capacity() * std::mem::size_of::<Option<V>>()
    }
}

pub(crate) struct SparseSet<K>(HashSet<K>);

impl<K> Default for SparseSet<K> {
    fn default() -> Self {
        Self(HashSet::new())
    }
}

impl<K: Eq + Hash> SolvableSet<K> for SparseSet<K> {
    fn contains(&self, id: K) -> bool {
        self.0.contains(&id)
    }

    fn insert(&mut self, id: K) -> bool {
        self.0.insert(id)
    }
}

pub(crate) struct DenseSet<K>(IndexedSet<K>);

impl<K> Default for DenseSet<K> {
    fn default() -> Self {
        Self(IndexedSet::default())
    }
}

impl<K: ArenaId> SolvableSet<K> for DenseSet<K> {
    fn contains(&self, id: K) -> bool {
        self.0.contains(id)
    }

    fn insert(&mut self, id: K) -> bool {
        self.0.insert(id)
    }
}

/// Interior-mutable wrapper around a [`SolvableMap`].
///
/// Lets callers `get` and `insert` through a shared reference. The unsafe
/// dereferences below are sound under three invariants:
///
/// 1. **No reentrancy.** No method on `M` may, while executing, invoke any
///    method on the enclosing `Frozen<M>`. The `M` impls used here
///    ([`SparseMap`], [`DenseMap`]) only touch the underlying `HashMap`/`Vec`,
///    so this holds. New impls must preserve it.
/// 2. **No escaping references.** `get`/`insert` return values by copy, so no
///    `&` into `M` ever outlives the call site. An `insert` that grows the
///    storage cannot dangle a borrow we already handed out.
/// 3. **Single-threaded.** The contained [`UnsafeCell`] makes `Frozen<M>`
///    `!Sync`, so two threads cannot share `&Frozen<M>`. The `&self` ops
///    therefore cannot race across threads.
pub(crate) struct Frozen<T>(UnsafeCell<T>);

impl<T: Default> Default for Frozen<T> {
    fn default() -> Self {
        Self(UnsafeCell::new(T::default()))
    }
}

impl<M: SolvableMap> Frozen<M> {
    pub fn get(&self, id: SolvableId) -> Option<M::Value> {
        // SAFETY: read-only and never hands out a reference into M.
        unsafe { (*self.0.get()).get(id) }
    }

    pub fn insert(&self, id: SolvableId, value: M::Value) {
        // SAFETY: no `&mut M` aliases live across this call because
        // `get`/`insert` only return `Copy` values, not references into M.
        unsafe { (*self.0.get()).insert(id, value) }
    }
}
