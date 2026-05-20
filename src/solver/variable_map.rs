use std::fmt::Display;

use ahash::HashMap;

use crate::{
    Interner, NameId, SolvableId,
    internal::{
        arena::ArenaId,
        id::{SolvableOrRootId, VariableId},
    },
};

/// Trait abstracting over the solvable-to-variable mapping strategy.
///
/// Two implementations are provided:
/// - [`DenseSolvableMap`]: `Vec`-based, O(1) lookup. Best when `SolvableId`s are
///   allocated sequentially from 0 with no gaps.
/// - [`SparseSolvableMap`]: `HashMap`-based. Only stores entries for solvables
///   the solver has visited, efficient when the pool is large but few solvables
///   are touched.
pub trait SolvableMap: Default {
    /// Look up the variable assigned to the given solvable, if any.
    fn get(&self, id: SolvableId) -> Option<VariableId>;
    /// Record the mapping from a solvable to its solver variable.
    fn insert(&mut self, id: SolvableId, variable_id: VariableId);
    /// Returns the approximate heap size in bytes.
    fn size_in_bytes(&self) -> usize;
}

/// Vec-indexed solvable map. O(1) lookup without hashing.
///
/// Best when `SolvableId`s are dense and sequential (allocated from a single
/// pool starting at 0).
#[derive(Default)]
pub struct DenseSolvableMap(Vec<Option<VariableId>>);

impl SolvableMap for DenseSolvableMap {
    fn get(&self, id: SolvableId) -> Option<VariableId> {
        self.0.get(id.to_usize()).copied().flatten()
    }

    fn insert(&mut self, id: SolvableId, variable_id: VariableId) {
        let idx = id.to_usize();
        if idx >= self.0.len() {
            self.0.resize(idx + 1, None);
        }
        self.0[idx] = Some(variable_id);
    }

    fn size_in_bytes(&self) -> usize {
        self.0.capacity() * std::mem::size_of::<Option<VariableId>>()
    }
}

/// HashMap-backed solvable map. Only stores entries for visited solvables.
///
/// Best when the pool contains many solvables but only a small fraction are
/// visited during solving.
#[derive(Default)]
pub struct SparseSolvableMap(HashMap<SolvableId, VariableId>);

impl SolvableMap for SparseSolvableMap {
    fn get(&self, id: SolvableId) -> Option<VariableId> {
        self.0.get(&id).copied()
    }

    fn insert(&mut self, id: SolvableId, variable_id: VariableId) {
        self.0.insert(id, variable_id);
    }

    fn size_in_bytes(&self) -> usize {
        self.0.capacity() * std::mem::size_of::<(SolvableId, VariableId)>()
    }
}

/// All variables in the solver are stored in a `VariableMap`. This map is used
/// to keep track of the semantics of a variable, e.g. what a specific variable
/// represents.
///
/// The `VariableMap` is responsible for assigning unique identifiers to each
/// variable represented by [`VariableId`].
pub(crate) struct VariableMap<SM: SolvableMap> {
    /// A map from solvable id to variable id.
    solvable_to_variable: SM,

    /// Records the origin of each variable, indexed by its [`VariableId`].
    ///
    /// Invariant: every allocated variable has its slot pushed in the same step
    /// it is handed out. Do not insert gaps; [`Self::origin`] indexes directly.
    origins: Vec<VariableOrigin>,
}

/// Describes the origin of a variable.
#[derive(Clone, Copy, Debug)]
pub(crate) enum VariableOrigin {
    /// The variable is the root of the decision tree.
    Root,

    /// The variable represents a specific solvable.
    Solvable(SolvableId),

    /// A variable that helps encode an at most one constraint.
    ForbidMultiple(NameId),

    /// A variable that indicates that any solvable of a particular package is
    /// part of the solution.
    AtLeastOne(NameId),
}

impl<SM: SolvableMap> Default for VariableMap<SM> {
    fn default() -> Self {
        Self {
            solvable_to_variable: SM::default(),
            // Index 0 is reserved for the root variable.
            origins: vec![VariableOrigin::Root],
        }
    }
}

impl<SM: SolvableMap> VariableMap<SM> {
    /// Allocate a new variable with the given origin and hand back its id.
    ///
    /// This is the single place that mutates `origins`, preserving the
    /// invariant that every variable has exactly one origin slot. Always
    /// extends `origins` by exactly one slot.
    fn alloc(&mut self, origin: VariableOrigin) -> VariableId {
        let id = self.origins.len();
        self.origins.push(origin);
        VariableId::from_usize(id)
    }

    /// Allocate a variable for a new variable or reuse an existing one.
    pub fn intern_solvable(&mut self, solvable_id: SolvableId) -> VariableId {
        if let Some(variable_id) = self.solvable_to_variable.get(solvable_id) {
            return variable_id;
        }
        let variable_id = self.alloc(VariableOrigin::Solvable(solvable_id));
        self.solvable_to_variable.insert(solvable_id, variable_id);
        variable_id
    }

    #[cfg(feature = "diagnostics")]
    pub fn count(&self) -> usize {
        self.origins.len()
    }

    #[cfg(feature = "diagnostics")]
    pub fn size_in_bytes(&self) -> usize {
        self.origins.capacity() * std::mem::size_of::<VariableOrigin>()
            + self.solvable_to_variable.size_in_bytes()
    }

    /// Allocate a variable for a solvable or the root.
    pub fn intern_solvable_or_root(&mut self, solvable_or_root_id: SolvableOrRootId) -> VariableId {
        match solvable_or_root_id.solvable() {
            Some(solvable_id) => self.intern_solvable(solvable_id),
            None => VariableId::root(),
        }
    }

    /// Allocate a variable that helps encode an at most one constraint.
    pub fn alloc_forbid_multiple_variable(&mut self, name: NameId) -> VariableId {
        self.alloc(VariableOrigin::ForbidMultiple(name))
    }

    /// Allocate a variable helps encode whether at least one solvable for a
    /// particular package is selected.
    pub fn alloc_at_least_one_variable(&mut self, name: NameId) -> VariableId {
        self.alloc(VariableOrigin::AtLeastOne(name))
    }

    /// Returns the origin of a variable. The origin describes the semantics of
    /// a variable.
    pub fn origin(&self, variable_id: VariableId) -> VariableOrigin {
        self.origins[variable_id.to_usize()]
    }
}

impl VariableId {
    /// Returns the solvable id associated with the variable if it represents a
    /// solvable.
    pub(crate) fn as_solvable<SM: SolvableMap>(
        self,
        variable_map: &VariableMap<SM>,
    ) -> Option<SolvableId> {
        variable_map.origin(self).as_solvable()
    }

    /// Returns the solvable-or-root id associated with the variable.
    pub(crate) fn as_solvable_or_root<SM: SolvableMap>(
        self,
        variable_map: &VariableMap<SM>,
    ) -> Option<SolvableOrRootId> {
        variable_map.origin(self).as_solvable_or_root()
    }

    /// Returns an object that can be used to format the variable.
    pub(crate) fn display<'i, SM: SolvableMap, I: Interner>(
        self,
        variable_map: &'i VariableMap<SM>,
        interner: &'i I,
    ) -> VariableDisplay<'i, SM, I> {
        VariableDisplay {
            variable: self,
            interner,
            variable_map,
        }
    }
}

pub(crate) struct VariableDisplay<'i, SM: SolvableMap, I: Interner> {
    variable: VariableId,
    interner: &'i I,
    variable_map: &'i VariableMap<SM>,
}

impl<SM: SolvableMap, I: Interner> Display for VariableDisplay<'_, SM, I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.variable_map.origin(self.variable) {
            VariableOrigin::Root => write!(f, "root"),
            VariableOrigin::Solvable(solvable_id) => {
                write!(f, "{}", self.interner.display_solvable(solvable_id))
            }
            VariableOrigin::ForbidMultiple(name) => {
                write!(f, "forbid-multiple({})", self.interner.display_name(name))
            }
            VariableOrigin::AtLeastOne(name) => {
                write!(f, "any-of({})", self.interner.display_name(name))
            }
        }
    }
}

impl VariableOrigin {
    pub(crate) fn as_solvable(&self) -> Option<SolvableId> {
        match self {
            VariableOrigin::Solvable(solvable_id) => Some(*solvable_id),
            _ => None,
        }
    }

    pub(crate) fn as_solvable_or_root(&self) -> Option<SolvableOrRootId> {
        match self {
            VariableOrigin::Solvable(solvable_id) => Some((*solvable_id).into()),
            VariableOrigin::Root => Some(SolvableOrRootId::root()),
            _ => None,
        }
    }
}
