//! Implements a SAT solver for dependency resolution based on the CDCL
//! algorithm (conflict-driven clause learning)
//!
//! The CDCL algorithm is masterly explained in [An Extensible
//! SAT-solver](http://minisat.se/downloads/MiniSat.pdf). Regarding the data structures used, we
//! mostly follow the approach taken by [libsolv](https://github.com/openSUSE/libsolv). The code of
//! libsolv is, however, very low level C, so if you are looking for an
//! introduction to CDCL, you are encouraged to look at the paper instead or to
//! keep reading through this codebase and its comments.

#![deny(missing_docs)]
#![deny(unnameable_types)]

mod conditional_requirement;
pub mod conflict;
pub mod id;
pub(crate) mod internal;
mod requirement;
pub mod runtime;
pub mod snapshot;
mod solver;
pub mod solver_id;
pub mod utils;

use std::{
    any::Any,
    fmt::{Debug, Display},
};

pub use conditional_requirement::{Condition, ConditionalRequirement, LogicalOperator};
pub use id::{
    ConditionId, DenseIndex, NameId, NameTag, SolvableId, SolvableTag, StringId, VariableId,
    VersionSetId, VersionSetUnionId,
};
use itertools::Itertools;
pub use requirement::Requirement;
pub use solver::{EmptySolvables, Problem, Solver, SolverCache, UnsolvableOrCancelled};
pub use solver_id::{DenseId, IdMap, IdSet, SolverId, SparseId};
pub use utils::{IndexedSet, Mapping, MappingIter};

/// An object that is used by the solver to query certain properties of
/// different internalized objects.
pub trait Interner {
    /// The package-name ID type used by this interner.
    type NameId: SolverId;

    /// The solvable ID type used by this interner.
    type SolvableId: SolverId;

    /// Returns an object that can be used to display the given solvable in a
    /// user-friendly way.
    ///
    /// When formatting the solvable, it should it include both the name of
    /// the package and any other identifying properties.
    fn display_solvable(&self, solvable: Self::SolvableId) -> impl Display + '_;

    /// Returns an object that can be used to display the name of a solvable in
    /// a user-friendly way.
    fn display_solvable_name(&self, solvable: Self::SolvableId) -> impl Display + '_ {
        self.display_name(self.solvable_name(solvable))
    }

    /// Returns an object that can be used to display multiple solvables in a
    /// user-friendly way. For example the conda provider should only display
    /// the versions (not build strings etc.) and merges multiple solvables
    /// into one line.
    ///
    /// When formatting the solvables, both the name of the package and any
    /// other identifying properties should be displayed.
    fn display_merged_solvables(&self, solvables: &[Self::SolvableId]) -> impl Display + '_ {
        if solvables.is_empty() {
            return String::new();
        }

        let versions = solvables
            .iter()
            .map(|&id| self.display_solvable(id).to_string())
            .sorted()
            .unique()
            .format(" | ");

        let name = self.display_solvable_name(solvables[0]);
        format!("{name} {versions}")
    }

    /// Returns an object that can be used to display the given name in a
    /// user-friendly way.
    fn display_name(&self, name: Self::NameId) -> impl Display + '_;

    /// Returns an object that can be used to display the given version set in a
    /// user-friendly way.
    ///
    /// The name of the package should *not* be included in the display. Where
    /// appropriate, this information is added.
    fn display_version_set(&self, version_set: VersionSetId) -> impl Display + '_;

    /// Displays the string with the given id.
    fn display_string(&self, string_id: StringId) -> impl Display + '_;

    /// Returns the name of the package that the specified version set is
    /// associated with.
    fn version_set_name(&self, version_set: VersionSetId) -> Self::NameId;

    /// Returns the name of the package for the given solvable.
    fn solvable_name(&self, solvable: Self::SolvableId) -> Self::NameId;

    /// Returns the version sets comprising the given union.
    ///
    /// The implementor must take care that the order in which the version sets
    /// are returned is deterministic.
    fn version_sets_in_union(
        &self,
        version_set_union: VersionSetUnionId,
    ) -> impl Iterator<Item = VersionSetId>;

    /// Resolves how a condition should be represented in the solver.
    ///
    /// Internally, the solver uses `ConditionId` to represent conditions. This
    /// allows implementers to have a custom representation for conditions that
    /// differ from the representation of the solver.
    fn resolve_condition(&self, condition: ConditionId) -> Condition;
}

/// Defines implementation specific behavior for the solver and a way for the
/// solver to access the packages that are available in the system.
#[allow(async_fn_in_trait)]
pub trait DependencyProvider: Sized + Interner {
    /// Given a set of solvables, return the candidates that match the given
    /// version set or if `inverse` is true, the candidates that do *not* match
    /// the version set.
    async fn filter_candidates(
        &self,
        candidates: &[Self::SolvableId],
        version_set: VersionSetId,
        inverse: bool,
    ) -> Vec<Self::SolvableId>;

    /// Obtains a list of solvables that should be considered when a package
    /// with the given name is requested.
    async fn get_candidates(&self, name: Self::NameId) -> Option<Candidates<Self::SolvableId>>;

    /// Sort the specified solvables based on which solvable to try first. The
    /// solver will iteratively try to select the highest version. If a
    /// conflict is found with the highest version the next version is
    /// tried. This continues until a solution is found.
    async fn sort_candidates(&self, solver: &SolverCache<Self>, solvables: &mut [Self::SolvableId]);

    /// Returns the dependencies for the specified solvable.
    async fn get_dependencies(&self, solvable: Self::SolvableId) -> Dependencies;

    /// Whether the solver should stop the dependency resolution algorithm.
    ///
    /// This method gets called at the beginning of each unit propagation round
    /// and before potentially blocking operations (like
    /// [Self::get_dependencies] and [Self::get_candidates]). If it returns
    /// `Some(...)`, the solver will stop and return
    /// [UnsolvableOrCancelled::Cancelled].
    fn should_cancel_with_value(&self) -> Option<Box<dyn Any>> {
        None
    }
}

/// A list of candidate solvables for a specific package. This is returned from
/// [`DependencyProvider::get_candidates`].
#[derive(Clone, Debug)]
pub struct Candidates<S = SolvableId> {
    /// A list of all solvables for the package.
    pub candidates: Vec<S>,

    /// Optionally the id of the solvable that is favored over other solvables.
    /// The solver will first attempt to solve for the specified solvable
    /// but will fall back to other candidates if no solution could be found
    /// otherwise.
    ///
    /// The same behavior can be achieved by sorting this candidate to the top
    /// using the [`DependencyProvider::sort_candidates`] function but using
    /// this method provides better error messages to the user.
    pub favored: Option<S>,

    /// If specified this is the Id of the only solvable that can be selected.
    /// Although it would also be possible to simply return a single
    /// candidate using this field provides better error messages to the
    /// user.
    pub locked: Option<S>,

    /// A hint to the solver that the dependencies of some of the solvables are
    /// also directly available. This allows the solver to request the
    /// dependencies of these solvables immediately. Having the dependency
    /// information available might make the solver much faster because it
    /// has more information available up-front which provides the solver with a
    /// more complete picture of the entire problem space. However, it might
    /// also be the case that the solver doesnt actually need this
    /// information to form a solution. In general though, if the
    /// dependencies can easily be provided one should provide them up-front.
    pub hint_dependencies_available: HintDependenciesAvailable<S>,

    /// A list of solvables that are available but have been excluded from the
    /// solver. For example, a package might be excluded from the solver
    /// because it is not compatible with the runtime. The solver will not
    /// consider these solvables when forming a solution but will use
    /// them in the error message if no solution could be found.
    pub excluded: Vec<(S, StringId)>,

    /// When `true`, self-referential constraints (where a package conflicts
    /// with something it also provides) are silently ignored rather than
    /// marking the package uninstallable. Defaults to `false`.
    ///
    /// Some ecosystems (e.g. RPM) require this because packages routinely
    /// provide and conflict with the same virtual capability.
    pub allow_self_conflicts: bool,
}

impl<S> Default for Candidates<S> {
    fn default() -> Self {
        Self {
            candidates: Vec::new(),
            favored: None,
            locked: None,
            hint_dependencies_available: HintDependenciesAvailable::None,
            excluded: Vec::new(),
            allow_self_conflicts: false,
        }
    }
}

/// Defines for which candidates dependencies are available without the
/// [`DependencyProvider`] having to perform extra work, e.g. it's cheap to
/// request them.
#[derive(Default, Clone, Debug)]
pub enum HintDependenciesAvailable<S = SolvableId> {
    /// None of the dependencies are available up-front. The dependency provide
    /// will have to do work to find the dependencies.
    #[default]
    None,

    /// All the dependencies are available up-front. Querying them is cheap.
    All,

    /// Only the dependencies for the specified solvables are available.
    /// Querying the dependencies for these solvables is cheap. Querying
    /// dependencies for other solvables is expensive.
    Some(Vec<S>),
}

/// Holds information about the dependencies of a package.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(untagged))]
pub enum Dependencies {
    /// The dependencies are known.
    Known(KnownDependencies),
    /// The dependencies are unknown, so the parent solvable should be excluded
    /// from the solution.
    ///
    /// The string provides more information about why the dependencies are
    /// unknown (e.g. an error message).
    Unknown(StringId),
}

/// Holds information about the dependencies of a package when they are known.
#[derive(Default, Clone, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct KnownDependencies {
    /// Defines which packages should be installed alongside the depending
    /// package and the constraints applied to the package.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub requirements: Vec<ConditionalRequirement>,

    /// Defines additional constraints on packages that may or may not be part
    /// of the solution. Different from `requirements`, packages in this set
    /// are not necessarily included in the solution. Only when one or more
    /// packages list the package in their `requirements` is the
    /// package also added to the solution.
    ///
    /// This is often useful to use for optional dependencies.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Vec::is_empty")
    )]
    pub constrains: Vec<VersionSetId>,
}
