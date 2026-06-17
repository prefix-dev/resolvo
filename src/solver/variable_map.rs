use std::fmt::Display;

use crate::{
    DenseIndex, Interner, Requirement, VariableId, VersionSetId,
    internal::solver_id::SolvableIdOrRoot,
    solver_id::{IdMap, SolverId},
};

/// All variables in the solver are stored in a `VariableMap`. This map is used
/// to keep track of the semantics of a variable, e.g. what a specific variable
/// represents.
///
/// The `VariableMap` is responsible for assigning unique identifiers to each
/// variable represented by [`VariableId`].
pub(crate) struct VariableMap<N: SolverId, S: SolverId> {
    /// A map from solvable id to variable id. Backed by the storage selected
    /// by the [`Layout`] marker.
    solvable_to_variable: S::Map<Option<VariableId>>,

    /// Records the origin of each variable, indexed by its [`VariableId`].
    ///
    /// Invariant: every allocated variable has its slot pushed in the same step
    /// it is handed out. Do not insert gaps; [`Self::origin`] indexes directly.
    origins: Vec<VariableOrigin<N, S>>,
}

/// Describes the origin of a variable.
#[derive(Clone, Copy, Debug)]
pub(crate) enum VariableOrigin<N, S> {
    /// The variable is the root of the decision tree.
    Root,

    /// The variable represents a specific solvable.
    Solvable(S),

    /// A variable that helps encode an at most one constraint.
    ForbidMultiple(N),

    /// A variable that indicates that any solvable of a particular package is
    /// part of the solution.
    AtLeastOne(N),

    /// A variable that indicates that a candidate excluded by a constraint's
    /// version set is installed.
    ConstrainsViolation(VersionSetId),

    /// The output variable of the OR-gate formed by a requirement's candidate
    /// disjunction `c1 | ... | cN`, in the Tseitin circuit-to-CNF sense.
    /// Requirers imply the gate (`requirer -> gate`) and the gate implies the
    /// disjunction (`gate -> c1 | ... | cN`), so the (often large) disjunction is
    /// defined once and shared by every requirer instead of being repeated for
    /// each. Only the `gate -> disjunction` direction is encoded (the gate is
    /// never forced true except by a requirer): the one-sided Plaisted-Greenbaum
    /// encoding, mirroring the constrains side at the opposite polarity.
    RequiresGate(Requirement),
}

impl<N: SolverId, S: SolverId> Default for VariableMap<N, S> {
    fn default() -> Self {
        Self {
            solvable_to_variable: Default::default(),
            // Index 0 is reserved for the root variable.
            origins: vec![VariableOrigin::Root],
        }
    }
}

impl<N: SolverId, S: SolverId> VariableMap<N, S> {
    /// Allocate a new variable with the given origin and hand back its id.
    ///
    /// This is the single place that mutates `origins`, preserving the
    /// invariant that every variable has exactly one origin slot. Always
    /// extends `origins` by exactly one slot.
    fn alloc(&mut self, origin: VariableOrigin<N, S>) -> VariableId {
        let id = self.origins.len();
        self.origins.push(origin);
        VariableId::from_index(id)
    }

    /// Allocate a variable for a new variable or reuse an existing one.
    pub fn intern_solvable(&mut self, solvable_id: S) -> VariableId {
        if let Some(variable_id) = self.solvable_to_variable.get(solvable_id) {
            return variable_id;
        }
        let variable_id = self.alloc(VariableOrigin::Solvable(solvable_id));
        debug_assert!(
            !variable_id.is_root(),
            "intern_solvable must never hand out the root variable id"
        );
        self.solvable_to_variable
            .set(solvable_id, Some(variable_id));
        variable_id
    }

    /// Looks up the variable for a solvable without allocating one. Returns
    /// `None` if no variable has been allocated for this solvable yet, which
    /// implies the solvable has not been decided.
    pub fn lookup_solvable(&self, solvable_id: S) -> Option<VariableId> {
        self.solvable_to_variable.get(solvable_id)
    }

    #[cfg(feature = "diagnostics")]
    pub fn count(&self) -> usize {
        self.origins.len()
    }

    #[cfg(feature = "diagnostics")]
    pub fn size_in_bytes(&self) -> usize {
        self.origins.capacity() * std::mem::size_of::<VariableOrigin<N, S>>()
    }

    /// Allocate a variable for a solvable or the root.
    pub fn intern_solvable_or_root(
        &mut self,
        solvable_or_root_id: SolvableIdOrRoot<S>,
    ) -> VariableId {
        match solvable_or_root_id.solvable() {
            Some(solvable_id) => self.intern_solvable(solvable_id),
            None => VariableId::root(),
        }
    }

    /// Allocate a variable that helps encode an at most one constraint.
    pub fn alloc_forbid_multiple_variable(&mut self, name: N) -> VariableId {
        self.alloc(VariableOrigin::ForbidMultiple(name))
    }

    /// Allocate a variable helps encode whether at least one solvable for a
    /// particular package is selected.
    pub fn alloc_at_least_one_variable(&mut self, name: N) -> VariableId {
        self.alloc(VariableOrigin::AtLeastOne(name))
    }

    /// Allocate a variable that indicates that a candidate that is excluded by
    /// the given constraint's version set is installed.
    pub fn alloc_constrains_violation_variable(&mut self, version_set: VersionSetId) -> VariableId {
        self.alloc(VariableOrigin::ConstrainsViolation(version_set))
    }

    /// Allocate a variable that gates the shared candidate disjunction of a
    /// requirement (see [`VariableOrigin::RequiresGate`]).
    pub fn alloc_requires_gate_variable(&mut self, requirement: Requirement) -> VariableId {
        self.alloc(VariableOrigin::RequiresGate(requirement))
    }

    /// Returns the origin of a variable. The origin describes the semantics of
    /// a variable.
    #[inline]
    pub fn origin(&self, variable_id: VariableId) -> VariableOrigin<N, S> {
        self.origins[variable_id.to_index()]
    }
}

impl VariableId {
    /// Returns the solvable id associated with the variable if it represents a
    /// solvable.
    pub(crate) fn as_solvable<N: SolverId, S: SolverId>(
        self,
        variable_map: &VariableMap<N, S>,
    ) -> Option<S> {
        variable_map.origin(self).as_solvable()
    }

    /// Returns the solvable-or-root id associated with the variable.
    pub(crate) fn as_solvable_or_root<N: SolverId, S: SolverId>(
        self,
        variable_map: &VariableMap<N, S>,
    ) -> Option<SolvableIdOrRoot<S>> {
        variable_map.origin(self).as_solvable_or_root()
    }

    /// Returns an object that can be used to format the variable.
    pub(crate) fn display<'i, I: Interner>(
        self,
        variable_map: &'i VariableMap<I::NameId, I::SolvableId>,
        interner: &'i I,
    ) -> VariableDisplay<'i, I> {
        VariableDisplay {
            variable: self,
            interner,
            variable_map,
        }
    }
}

pub(crate) struct VariableDisplay<'i, I: Interner> {
    variable: VariableId,
    interner: &'i I,
    variable_map: &'i VariableMap<I::NameId, I::SolvableId>,
}

impl<I: Interner> Display for VariableDisplay<'_, I> {
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
            VariableOrigin::ConstrainsViolation(version_set) => {
                write!(
                    f,
                    "constrains-violation({} {})",
                    self.interner
                        .display_name(self.interner.version_set_name(version_set)),
                    self.interner.display_version_set(version_set)
                )
            }
            VariableOrigin::RequiresGate(requirement) => {
                write!(f, "requires-gate({})", requirement.display(self.interner))
            }
        }
    }
}

impl<N: SolverId, S: SolverId> VariableOrigin<N, S> {
    pub(crate) fn as_solvable(&self) -> Option<S> {
        match self {
            VariableOrigin::Solvable(solvable_id) => Some(*solvable_id),
            _ => None,
        }
    }

    pub(crate) fn as_solvable_or_root(&self) -> Option<SolvableIdOrRoot<S>> {
        match self {
            VariableOrigin::Solvable(solvable_id) => Some((*solvable_id).into()),
            VariableOrigin::Root => Some(SolvableIdOrRoot::root()),
            _ => None,
        }
    }
}
