use std::cell::UnsafeCell;

use crate::solver_id::{IdMap, IdSet, SolverId};

/// A key that can refer to the solver root or to a provider solvable.
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub(crate) enum SolvableIdOrRoot<S> {
    /// The synthetic solver root.
    Root,
    /// A provider-owned solvable ID.
    Solvable(S),
}

impl<S> SolvableIdOrRoot<S> {
    /// Constructs the root key.
    pub(crate) const fn root() -> Self {
        Self::Root
    }

    /// Returns the solvable ID, or `None` for the root.
    pub(crate) fn solvable(self) -> Option<S> {
        match self {
            Self::Root => None,
            Self::Solvable(solvable) => Some(solvable),
        }
    }
}

impl<S> From<S> for SolvableIdOrRoot<S> {
    fn from(value: S) -> Self {
        Self::Solvable(value)
    }
}

/// Root-aware set storage.
///
/// Root is stored as a single boolean while solvable keys delegate to the
/// solvable ID's selected set storage.
pub(crate) struct WithRootSet<S: SolverId> {
    root: bool,
    solvables: S::Set,
}

impl<S: SolverId> Default for WithRootSet<S> {
    fn default() -> Self {
        Self {
            root: false,
            solvables: Default::default(),
        }
    }
}

impl<S: SolverId> IdSet<SolvableIdOrRoot<S>> for WithRootSet<S> {
    fn contains(&self, key: SolvableIdOrRoot<S>) -> bool {
        match key {
            SolvableIdOrRoot::Root => self.root,
            SolvableIdOrRoot::Solvable(solvable) => self.solvables.contains(solvable),
        }
    }

    fn insert(&mut self, key: SolvableIdOrRoot<S>) -> bool {
        match key {
            SolvableIdOrRoot::Root => {
                let was_present = self.root;
                self.root = true;
                !was_present
            }
            SolvableIdOrRoot::Solvable(solvable) => self.solvables.insert(solvable),
        }
    }
}

/// Interior-mutable wrapper around an [`IdMap`].
///
/// This keeps the same single-threaded, no-reference-returning aliasing model
/// as the solver's previous specialized frozen storage.
pub(crate) struct Frozen<T>(UnsafeCell<T>);

impl<T: Default> Default for Frozen<T> {
    fn default() -> Self {
        Self(UnsafeCell::new(T::default()))
    }
}

impl<T> Frozen<T> {
    pub(crate) fn get<K, V: Copy + Default>(&self, key: K) -> V
    where
        T: IdMap<K, V>,
    {
        // SAFETY: read-only and never hands out a reference into M.
        unsafe { (*self.0.get()).get(key) }
    }

    pub(crate) fn set<K, V: Copy + Default>(&self, key: K, value: V)
    where
        T: IdMap<K, V>,
    {
        // SAFETY: `get`/`set` only move `Copy` values, so no references into M
        // can be invalidated by mutation.
        unsafe { (*self.0.get()).set(key, value) }
    }
}
