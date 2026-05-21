use std::fmt::Display;

use crate::{
    Interner, NameId, SolvableId,
    internal::{
        arena::ArenaId,
        id::{SolvableOrRootId, VariableId},
    },
    solvable_id::{self, Sealed, SolvableMap},
};

/// All variables in the solver are stored in a `VariableMap`. This map is used
/// to keep track of the semantics of a variable, e.g. what a specific variable
/// represents.
///
/// The `VariableMap` is responsible for assigning unique identifiers to each
/// variable represented by [`VariableId`].
pub(crate) struct VariableMap<L: solvable_id::Layout> {
    /// A map from solvable id to variable id. Backed by the storage selected
    /// by the [`Layout`] marker.
    solvable_to_variable: <L as Sealed>::Map<VariableId>,

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

impl<L: solvable_id::Layout> Default for VariableMap<L> {
    fn default() -> Self {
        Self {
            solvable_to_variable: Default::default(),
            // Index 0 is reserved for the root variable.
            origins: vec![VariableOrigin::Root],
        }
    }
}

impl<L: solvable_id::Layout> VariableMap<L> {
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
        debug_assert!(
            !variable_id.is_root(),
            "intern_solvable must never hand out the root variable id"
        );
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
    pub(crate) fn as_solvable<L: solvable_id::Layout>(
        self,
        variable_map: &VariableMap<L>,
    ) -> Option<SolvableId> {
        variable_map.origin(self).as_solvable()
    }

    /// Returns the solvable-or-root id associated with the variable.
    pub(crate) fn as_solvable_or_root<L: solvable_id::Layout>(
        self,
        variable_map: &VariableMap<L>,
    ) -> Option<SolvableOrRootId> {
        variable_map.origin(self).as_solvable_or_root()
    }

    /// Returns an object that can be used to format the variable.
    pub(crate) fn display<'i, L: solvable_id::Layout, I: Interner>(
        self,
        variable_map: &'i VariableMap<L>,
        interner: &'i I,
    ) -> VariableDisplay<'i, L, I> {
        VariableDisplay {
            variable: self,
            interner,
            variable_map,
        }
    }
}

pub(crate) struct VariableDisplay<'i, L: solvable_id::Layout, I: Interner> {
    variable: VariableId,
    interner: &'i I,
    variable_map: &'i VariableMap<L>,
}

impl<L: solvable_id::Layout, I: Interner> Display for VariableDisplay<'_, L, I> {
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
