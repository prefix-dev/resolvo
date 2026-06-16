use std::{any::Any, fmt::Display};

use ahash::{HashMap, HashSet};
pub use cache::SolverCache;
use clause::{Clause, Literal, WatchedLiterals};
use conditions::{DeferredRequirement, Disjunction, DisjunctionId, condition_disjunct_holds};
use decision::Decision;
use decision_tracker::DecisionTracker;
use encoding::Encoder;
use indexmap::IndexMap;
use itertools::Itertools;
use variable_map::VariableMap;

use watch_map::WatchMap;

use crate::{
    ConditionId, ConditionalRequirement, DenseIndex, Dependencies, DependencyProvider,
    KnownDependencies, Requirement, SolvableId, VariableId, VersionSetId,
    conflict::Conflict,
    internal::{
        arena::Arena,
        id::{ClauseId, LearntClauseId},
        solver_id::{SolvableIdOrRoot, WithRootSet},
    },
    requirement::RequirementMap,
    runtime::{AsyncRuntime, NowOrNeverRuntime},
    solver::binary_encoding::AtMostOnceTracker,
    solver_id::{IdMap, IdSet, SolverId},
    utils::{IndexedSet, Mapping},
};

mod binary_encoding;
mod cache;
pub(crate) mod clause;
mod conditions;
mod decide_queue;
mod decision;
mod decision_map;
mod decision_tracker;
#[cfg(feature = "diagnostics")]
mod diagnostics;
mod encoding;
pub(crate) mod variable_map;
mod watch_map;

/// Describes the problem that is to be solved by the solver.
///
/// This struct is generic over the type `S` of the collection of soft
/// requirements passed to the solver, typically expected to be a type
/// implementing [`IntoIterator`].
///
/// This struct follows the builder pattern and can have its fields set by one
/// of the available setter methods.
pub struct Problem<Id = SolvableId, S = EmptySolvables<Id>> {
    requirements: Vec<ConditionalRequirement>,
    constraints: Vec<VersionSetId>,
    soft_requirements: S,
    _marker: std::marker::PhantomData<fn(Id) -> Id>,
}

/// Empty soft-requirements iterator for a [`Problem`] parameterized by an ID type.
pub struct EmptySolvables<Id>(pub std::marker::PhantomData<fn(Id) -> Id>);

impl<Id> Default for EmptySolvables<Id> {
    fn default() -> Self {
        Self(std::marker::PhantomData)
    }
}

impl<Id> Iterator for EmptySolvables<Id> {
    type Item = Id;

    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

impl<Id> Default for Problem<Id, EmptySolvables<Id>> {
    fn default() -> Self {
        Self::new()
    }
}

impl<Id> Problem<Id, EmptySolvables<Id>> {
    /// Creates a new empty [`Problem`]. Use the setter methods to build the
    /// problem before passing it to the solver to be solved.
    pub fn new() -> Self {
        Self {
            requirements: Default::default(),
            constraints: Default::default(),
            soft_requirements: Default::default(),
            _marker: std::marker::PhantomData,
        }
    }
}

impl<Id, S: IntoIterator<Item = Id>> Problem<Id, S> {
    /// Sets the requirements that _must_ have one candidate solvable be
    /// included in the solution.
    ///
    /// Returns the [`Problem`] for further mutation or to pass to
    /// [`Solver::solve`].
    pub fn requirements(self, requirements: Vec<ConditionalRequirement>) -> Self {
        Self {
            requirements,
            ..self
        }
    }

    /// Sets the additional constraints imposed on individual packages that the
    /// solvable (if any) chosen for that package _must_ adhere to.
    ///
    /// Returns the [`Problem`] for further mutation or to pass to
    /// [`Solver::solve`].
    pub fn constraints(self, constraints: Vec<VersionSetId>) -> Self {
        Self {
            constraints,
            ..self
        }
    }

    /// Sets the additional requirements that the solver should _try_ and
    /// fulfill once it has found a solution to the main problem.
    ///
    /// An unsatisfiable soft requirement does not cause a conflict; the solver
    /// will try and fulfill as many soft requirements as possible and skip
    /// the unsatisfiable ones.
    ///
    /// Soft requirements are currently only specified as individual solvables
    /// to be included in the solution, however in the future they will be
    /// able to be specified as version sets.
    ///
    /// # Returns
    ///
    /// Returns the [`Problem`] for further mutation or to pass to
    /// [`Solver::solve`].
    pub fn soft_requirements<I: IntoIterator<Item = Id>>(
        self,
        soft_requirements: I,
    ) -> Problem<Id, I> {
        Problem {
            requirements: self.requirements,
            constraints: self.constraints,
            soft_requirements,
            _marker: std::marker::PhantomData,
        }
    }
}

pub(crate) struct Clauses<N> {
    pub(crate) kinds: Vec<Clause<N>>,
    watched_literals: Vec<Option<WatchedLiterals>>,
}

impl<N> Default for Clauses<N> {
    fn default() -> Self {
        Self {
            kinds: Vec::new(),
            watched_literals: Vec::new(),
        }
    }
}

impl<N> Clauses<N> {
    pub fn alloc(
        &mut self,
        watched_literals: Option<WatchedLiterals>,
        kind: Clause<N>,
    ) -> ClauseId {
        let id = ClauseId::from_index(self.kinds.len());
        self.kinds.push(kind);
        self.watched_literals.push(watched_literals);
        id
    }
}

type RequirementCandidateVariables = Vec<Vec<VariableId>>;

/// Drives the SAT solving process.
pub struct Solver<D: DependencyProvider, RT: AsyncRuntime = NowOrNeverRuntime> {
    /// The runtime to use for async operations.
    pub(crate) async_runtime: RT,

    /// A cache that stores request to the dependency provider.
    pub(crate) cache: SolverCache<D>,

    /// Holds the current state of the solver.
    pub(crate) state: SolverState<D>,

    /// The activity add factor. This is a value that is added to the activity
    /// score of each package that is part of a conflict.
    activity_add: f32,

    /// The activity decay factor. This is a value between 0 and 1 with which
    /// the activity scores of each package are multiplied when a conflict is
    /// detected.
    activity_decay: f32,
}

pub(crate) struct SolverState<D: DependencyProvider> {
    pub(crate) clauses: Clauses<D::NameId>,
    watches: WatchMap,

    /// A mapping from requirements to the variables that represent the
    /// candidates.
    requirement_to_sorted_candidates: RequirementMap<RequirementCandidateVariables>,

    pub(crate) variable_map: VariableMap<D::NameId, D::SolvableId>,

    negative_assertions: Vec<(VariableId, ClauseId)>,

    learnt_clauses: Arena<LearntClauseId, Vec<Literal>>,
    learnt_why: Mapping<LearntClauseId, Vec<ClauseId>>,
    learnt_clause_ids: Vec<ClauseId>,

    disjunctions: Arena<DisjunctionId, Disjunction>,

    clauses_added_for_package: <D::NameId as SolverId>::Set,
    clauses_added_for_solvable: WithRootSet<D::SolvableId>,
    at_most_one_trackers: HashMap<D::NameId, AtMostOnceTracker<VariableId>>,

    /// Keeps track of auxiliary variables that are used to encode at-least-one
    /// solvable for a package.
    at_least_one_tracker: <D::NameId as SolverId>::Map<Option<VariableId>>,

    /// The auxiliary variable of the shared constrains encoding per version
    /// set. The [`Clause::ConstrainsExcluded`] clauses are emitted exactly
    /// once, when the variable is allocated.
    constrains_aux_vars: HashMap<VersionSetId, VariableId>,

    /// The gate variable of the shared requires encoding per requirement. The
    /// single candidate disjunction (`Clause::Requires` on the gate) is emitted
    /// exactly once, when the variable is allocated; each requirer then only
    /// adds a binary implication to the gate. See
    /// [`variable_map::VariableOrigin::RequiresGate`].
    requires_aux_vars: HashMap<Requirement, VariableId>,

    pub(crate) decision_tracker: DecisionTracker,

    /// Activity score per package.
    name_activity: <D::NameId as SolverId>::Map<f32>,

    /// The largest activity stored in `name_activity`, maintained bit-exactly
    /// next to the bumps and decays. Used by the decision fold to stop early
    /// when no remaining item can have a strictly higher activity.
    max_activity: f32,

    /// Incremental work queue that tracks which requires clauses are eligible
    /// for the next decision. See [`decide_queue`].
    decide_queue: decide_queue::DecideQueue<D>,

    /// Conditional requirements whose condition did not hold at the moment the
    /// encoder reached them, and whose requirement candidates have therefore
    /// not been fetched. Keyed by `ConditionId`; each entry is a list of
    /// per-disjunct deferred requirements that share that condition.
    ///
    /// Invariant: an entry remains in this map only as long as the
    /// corresponding requires clause has *not* been encoded. The first time a
    /// deferred entry's disjunct fires the entry is drained and the encoder
    /// builds its requires clause exactly as the eager path would have. Once
    /// encoded the entry is removed; condition firings later in the solve
    /// (after backtracking or otherwise) do not re-encode it.
    deferred_requirements:
        IndexMap<ConditionId, Vec<DeferredRequirement<D::SolvableId>>, ahash::RandomState>,

    #[cfg(feature = "diagnostics")]
    propagation_counters: PropagationCounters,
}

impl<D: DependencyProvider> Default for SolverState<D> {
    fn default() -> Self {
        Self {
            clauses: Default::default(),
            watches: Default::default(),
            requirement_to_sorted_candidates: Default::default(),
            variable_map: Default::default(),
            negative_assertions: Default::default(),
            learnt_clauses: Default::default(),
            learnt_why: Default::default(),
            learnt_clause_ids: Default::default(),
            disjunctions: Default::default(),
            clauses_added_for_package: Default::default(),
            clauses_added_for_solvable: Default::default(),
            at_most_one_trackers: Default::default(),
            at_least_one_tracker: Default::default(),
            constrains_aux_vars: Default::default(),
            requires_aux_vars: Default::default(),
            decision_tracker: Default::default(),
            name_activity: Default::default(),
            max_activity: 0.0,
            decide_queue: Default::default(),
            deferred_requirements: Default::default(),
            #[cfg(feature = "diagnostics")]
            propagation_counters: Default::default(),
        }
    }
}

/// Counters that track propagation loop behavior for performance analysis.
#[cfg(feature = "diagnostics")]
#[derive(Default)]
pub(crate) struct PropagationCounters {
    pub decisions_propagated: u64,
    /// Total number of clause visits during watch traversal.
    pub clause_visits: u64,
    /// Number of times other_watched was already true (early skip).
    pub early_skips: u64,
    /// Number of times we found a new unwatched literal (watch moved).
    pub watch_moves: u64,
    /// Number of times we had to unit-propagate (no unwatched literal found).
    pub unit_propagations: u64,
    /// Breakdown of [`Self::clause_visits`] by clause type.
    pub visits_by_type: PropagationVisitsByType,
    /// Breakdown of `next_unwatched_literal` calls by clause type.
    pub unwatched_calls_by_type: PropagationVisitsByType,
    pub propagate_calls: u64,
    pub conflicts: u64,
    /// Time spent adding clauses from the dependency provider.
    pub encoding_duration: std::time::Duration,
    pub propagation_duration: std::time::Duration,
    pub decide_duration: std::time::Duration,
    /// Time spent in [`Self::analyze`] / `learn_from_conflict`.
    pub learn_duration: std::time::Duration,
}

#[cfg(feature = "diagnostics")]
#[derive(Default)]
pub(crate) struct PropagationVisitsByType {
    pub requires: u64,
    pub constrains: u64,
    pub forbid_multiple: u64,
    pub lock: u64,
    pub learnt: u64,
    pub any_of: u64,
    pub other: u64,
}

#[cfg(feature = "diagnostics")]
impl PropagationVisitsByType {
    fn count<N>(&mut self, clause: &Clause<N>) {
        match clause {
            Clause::Requires(..) => self.requires += 1,
            Clause::Constrains(..)
            | Clause::ConstrainsExcluded(..)
            | Clause::ConstrainsParent(..) => self.constrains += 1,
            Clause::ForbidMultipleInstances(..) => self.forbid_multiple += 1,
            Clause::Lock(..) => self.lock += 1,
            Clause::Learnt(..) => self.learnt += 1,
            Clause::AnyOf(..) => self.any_of += 1,
            _ => self.other += 1,
        }
    }
}

impl<D: DependencyProvider> Solver<D, NowOrNeverRuntime> {
    /// Creates a single threaded block solver, using the provided
    /// [`DependencyProvider`].
    pub fn new(provider: D) -> Self {
        Self {
            cache: SolverCache::new(provider),
            async_runtime: NowOrNeverRuntime,
            state: SolverState::default(),
            activity_add: 1.0,
            activity_decay: 0.95,
        }
    }
}

/// The root cause of a solver error.
#[derive(Debug)]
pub enum UnsolvableOrCancelled {
    /// The problem was unsolvable.
    Unsolvable(Conflict),
    /// The solving process was cancelled.
    Cancelled(Box<dyn Any>),
}

impl From<Conflict> for UnsolvableOrCancelled {
    fn from(value: Conflict) -> Self {
        UnsolvableOrCancelled::Unsolvable(value)
    }
}

impl From<Box<dyn Any>> for UnsolvableOrCancelled {
    fn from(value: Box<dyn Any>) -> Self {
        UnsolvableOrCancelled::Cancelled(value)
    }
}

/// An error during the propagation step
#[derive(Debug)]
pub(crate) enum PropagationError {
    Conflict(VariableId, bool, ClauseId),
    Cancelled(Box<dyn Any>),
}

impl Display for PropagationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PropagationError::Conflict(solvable, value, clause) => {
                write!(
                    f,
                    "conflict while propagating solvable {:?}, value {} caused by clause {:?}",
                    solvable, value, clause
                )
            }
            PropagationError::Cancelled(_) => {
                write!(f, "propagation was cancelled")
            }
        }
    }
}

impl<D: DependencyProvider, RT: AsyncRuntime> Solver<D, RT> {
    /// Returns the dependency provider used by this instance.
    pub fn provider(&self) -> &D {
        self.cache.provider()
    }

    /// Returns the number of clauses in the solver after solving.
    pub fn clause_count(&self) -> usize {
        self.state.clauses.kinds.len()
    }

    /// Total number of deferred per-disjunct conditional requirements still
    /// waiting for their condition to fire. Useful to verify the "remove on
    /// first fire" invariant of the lazy-conditional-candidates path.
    pub fn deferred_requirements_count(&self) -> usize {
        self.state.deferred_requirements_count()
    }

    /// Set the runtime of the solver to `runtime`.
    #[must_use]
    pub fn with_runtime<RT2: AsyncRuntime>(self, runtime: RT2) -> Solver<D, RT2> {
        Solver {
            async_runtime: runtime,
            cache: self.cache,
            state: self.state,
            activity_decay: self.activity_decay,
            activity_add: self.activity_add,
        }
    }

    /// Configure activity andd and decay parameters. This enables tweaking
    /// these parameters.
    #[must_use]
    pub fn with_activity_params(self, add: f32, decay: f32) -> Self {
        Self {
            activity_add: add,
            activity_decay: decay,
            ..self
        }
    }

    /// Solves the given [`Problem`].
    ///
    /// The solver first solves for the root requirements and constraints, and
    /// then tries to include in the solution as many of the soft
    /// requirements as it can. Each soft requirement is subject to all the
    /// clauses and decisions introduced for all the previously decided
    /// solvables in the solution.
    ///
    /// Unless the corresponding package has been requested by a version set in
    /// another solvable's clauses, each soft requirement is _not_ subject
    /// to the package-level clauses introduced in
    /// [`DependencyProvider::get_candidates`] since the solvables have been
    /// requested specifically (not through a version set) in the solution.
    ///
    /// # Returns
    ///
    /// If a solution was found, returns a [`Vec`] of the solvables included in
    /// the solution.
    ///
    /// If no solution to the _root_ requirements and constraints was found,
    /// returns a [`Conflict`] wrapped in a
    /// [`UnsolvableOrCancelled::Unsolvable`], which provides ways to
    /// inspect the causes and report them to the user. If a soft requirement is
    /// unsolvable, it is simply not included in the solution.
    ///
    /// If the solution process is cancelled (see
    /// [`DependencyProvider::should_cancel_with_value`]), returns an
    /// [`UnsolvableOrCancelled::Cancelled`] containing the cancellation value.
    pub fn solve(
        &mut self,
        problem: Problem<D::SolvableId, impl IntoIterator<Item = D::SolvableId>>,
    ) -> Result<Vec<D::SolvableId>, UnsolvableOrCancelled> {
        // Re-initialize the solver state.
        self.state = SolverState::default();

        // The decision fold's activity-based shortcuts are only sound when
        // activities can never become negative and cold packages stay at
        // exactly zero.
        self.state
            .decide_queue
            .set_standard_activity_params(self.activity_add > 0.0 && self.activity_decay >= 0.0);

        // Construct the root dependencies from the problem
        let root_dependencies = Dependencies::Known(KnownDependencies {
            requirements: problem.requirements,
            constrains: problem.constraints,
        });

        // The first clause will always be the install root clause. Here we verify that
        // this is indeed the case.
        let root_clause = {
            let (state, kind) = WatchedLiterals::root();
            self.state.add_clause(state, kind)
        };
        assert_eq!(root_clause, ClauseId::install_root());

        assert!(
            self.run_sat(SolvableIdOrRoot::root(), &root_dependencies)?,
            "bug: Since root is the first requested solvable, \
                  should have returned Err instead of Ok(false) if root is unsolvable"
        );

        for additional in problem.soft_requirements {
            let additional_var = self.state.variable_map.intern_solvable(additional);

            if self
                .state
                .decision_tracker
                .assigned_value(additional_var)
                .is_none()
            {
                self.run_sat(additional.into(), &root_dependencies)?;
            }
        }

        #[cfg(feature = "diagnostics")]
        self.report_diagnostics();
        Ok(self.state.chosen_solvables().collect())
    }

    /// Run the CDCL algorithm to solve the SAT problem
    ///
    /// The CDCL algorithm's job is to find a valid assignment to the variables
    /// involved in the provided clauses. It works in the following steps:
    ///
    /// 1. __Set__: Assign a value to a variable that hasn't been assigned yet.
    ///    An assignment in this step starts a new "level" (the first one being
    ///    level 1). If all variables have been assigned, then we are done.
    /// 2. __Propagate__: Perform [unit propagation](https://en.wikipedia.org/wiki/Unit_propagation).
    ///    Assignments in this step are associated to the same "level" as the
    ///    decision that triggered them. This "level" metadata is useful when it
    ///    comes to handling conflicts. See [`Solver::propagate`] for the
    ///    implementation of this step.
    /// 3. __Learn__: If propagation finishes without conflicts, go back to 1.
    ///    Otherwise find the combination of assignments that caused the
    ///    conflict and add a new clause to the solver to forbid that
    ///    combination of assignments (i.e. learn from this mistake so it is not
    ///    repeated in the future). Then backtrack and go back to step 1 or, if
    ///    the learnt clause is in conflict with existing clauses, declare the
    ///    problem to be unsolvable. See [`Solver::analyze`] for the
    ///    implementation of this step.
    ///
    /// The solver loop can be found in [`Solver::resolve_dependencies`].
    ///
    /// Returns `Ok(true)` if a solution was found for `solvable`. If a solution
    /// was not found, returns `Ok(false)` if some decisions have already
    /// been made by the solver (i.e. the decision tracker stack is not
    /// empty). Otherwise, returns [`UnsolvableOrCancelled::Unsolvable`] as
    /// an `Err` on no solution.
    ///
    /// If the solution process is cancelled (see
    /// [`DependencyProvider::should_cancel_with_value`]),
    /// returns [`UnsolvableOrCancelled::Cancelled`] as an `Err`.
    fn run_sat(
        &mut self,
        root_solvable: SolvableIdOrRoot<D::SolvableId>,
        root_deps: &Dependencies,
    ) -> Result<bool, UnsolvableOrCancelled> {
        let starting_level = self
            .state
            .decision_tracker
            .stack()
            .next_back()
            .map(|decision| self.state.decision_tracker.level(decision.variable))
            .unwrap_or(0);

        let mut level = starting_level;
        let mut new_solvables: Vec<(VariableId, ClauseId)> = Vec::new();
        let mut solvable_ids: Vec<SolvableIdOrRoot<D::SolvableId>> = Vec::new();

        loop {
            if level == starting_level {
                tracing::trace!("Level {starting_level}: Resetting the decision loop");
            } else {
                tracing::trace!("Level {}: Starting the decision loop", level);
            }

            // A level of starting_level means the decision loop has been completely reset
            // because a partial solution was invalidated by newly added clauses.
            if level == starting_level {
                // Level starting_level + 1 is the initial decision level
                level = starting_level + 1;

                // Assign `true` to the root solvable. This must be installed to satisfy the
                // solution. The root solvable contains the dependencies that
                // were injected when calling `Solver::solve`. If we can find a
                // solution were the root is installable we found a
                // solution that satisfies the user requirements.
                tracing::trace!(
                    "╤══ Install {} at level {level}",
                    root_solvable.display(self.provider())
                );
                self.state
                    .decision_tracker
                    .try_add_decision(
                        Decision::new(
                            self.state
                                .variable_map
                                .intern_solvable_or_root(root_solvable),
                            true,
                            ClauseId::install_root(),
                        ),
                        level,
                    )
                    .expect("already decided");

                // Add the clauses for the root solvable.
                #[cfg(feature = "diagnostics")]
                let encoding_start = std::time::Instant::now();
                let conflicting_clauses = self.async_runtime.block_on(
                    Encoder::new(&mut self.state, &self.cache, root_deps, level)
                        .encode([root_solvable]),
                )?;
                #[cfg(feature = "diagnostics")]
                {
                    self.state.propagation_counters.encoding_duration += encoding_start.elapsed();
                }

                if let Some(clause_id) = conflicting_clauses.into_iter().next() {
                    return self.run_sat_process_unsolvable(
                        root_solvable,
                        starting_level,
                        clause_id,
                    );
                }
            }

            tracing::trace!("Level {}: Propagating", level);

            // Propagate decisions from assignments above
            let propagate_result = self.propagate(level);

            tracing::trace!("Propagate result: {:?}", propagate_result);

            // Handle propagation errors
            match propagate_result {
                Ok(()) => {}
                Err(PropagationError::Conflict(_, _, clause_id)) => {
                    if level == starting_level + 1 {
                        return self.run_sat_process_unsolvable(
                            root_solvable,
                            starting_level,
                            clause_id,
                        );
                    } else {
                        // The conflict was caused because new clauses have been added dynamically.
                        // We need to start over.
                        tracing::debug!(
                            "├─ added clause {clause} introduces a conflict which invalidates the partial solution",
                            clause = self.state.clauses.kinds[clause_id.to_index()]
                                .display(&self.state.variable_map, self.provider())
                        );
                        level = starting_level;
                        self.state.decision_tracker.undo_until(starting_level);
                        continue;
                    }
                }
                Err(PropagationError::Cancelled(value)) => {
                    // Propagation was cancelled
                    return Err(UnsolvableOrCancelled::Cancelled(value));
                }
            }

            // Enter the solver loop, return immediately if no new assignments have been
            // made.
            tracing::trace!("Level {}: Resolving dependencies", level);
            level = self.resolve_dependencies(level)?;
            tracing::trace!("Level {}: Done resolving dependencies", level);

            // We have a partial solution. E.g. there is a solution that satisfies all the
            // clauses that have been added so far.

            // Determine which solvables are part of the solution for which we did not yet
            // get any dependencies. If we find any such solvable it means we
            // did not arrive at the full solution yet.
            new_solvables.clear();
            new_solvables.extend(
                self.state
                    .decision_tracker
                    .stack()
                    // Filter only decisions that led to a positive assignment
                    .filter(|d| d.value)
                    // Select solvables for which we do not yet have dependencies
                    .filter(|d| {
                        let Some(solvable_or_root) =
                            d.variable.as_solvable_or_root(&self.state.variable_map)
                        else {
                            return false;
                        };
                        !self
                            .state
                            .clauses_added_for_solvable
                            .contains(solvable_or_root)
                    })
                    .map(|d| (d.variable, d.derived_from)),
            );

            // Also detect deferred conditional requirements whose condition
            // has just started to hold. These have to be encoded before we can
            // conclude the solution is complete.
            let fired_conditions = self.state.fired_deferred_conditions();

            if new_solvables.is_empty() && fired_conditions.is_empty() {
                // If no new literals were selected and no deferred conditions
                // fired, this solution is complete and we can return.
                tracing::trace!(
                    "Level {}: No new solvables or fired conditions, solution is complete",
                    level
                );
                return Ok(true);
            }

            if !new_solvables.is_empty() {
                tracing::debug!("==== Found newly selected solvables");
                tracing::debug!(
                    " - {}",
                    new_solvables
                        .iter()
                        .copied()
                        .format_with("\n- ", |(id, derived_from), f| f(&format_args!(
                            "{} (derived from {})",
                            id.display(&self.state.variable_map, self.provider()),
                            self.state.clauses.kinds[derived_from.to_index()]
                                .display(&self.state.variable_map, self.provider()),
                        )))
                        .to_string()
                );
                tracing::debug!("====");
            }

            if !fired_conditions.is_empty() {
                tracing::debug!(
                    "==== Found {} deferred condition(s) that just fired",
                    fired_conditions.len()
                );
            }

            solvable_ids.clear();
            solvable_ids.extend(new_solvables.iter().filter_map(|(variable, _)| {
                self.state
                    .variable_map
                    .origin(*variable)
                    .as_solvable()
                    .map(SolvableIdOrRoot::from)
            }));

            // Drain the fired deferred requirements.
            let mut deferred_to_encode = Vec::new();
            for condition in fired_conditions {
                deferred_to_encode.extend(self.state.drain_fired_deferred(condition));
            }

            #[cfg(feature = "diagnostics")]
            let encoding_start = std::time::Instant::now();
            let conflicting_clauses = self.async_runtime.block_on(
                Encoder::new(&mut self.state, &self.cache, root_deps, level)
                    .encode_with_deferred(solvable_ids.iter().copied(), deferred_to_encode),
            )?;
            #[cfg(feature = "diagnostics")]
            {
                self.state.propagation_counters.encoding_duration += encoding_start.elapsed();
            }

            // Serially process the outputs, to reduce the need for synchronization
            for &clause_id in &conflicting_clauses {
                tracing::debug!(
                    "├─ Added clause {clause} introduces a conflict which invalidates the partial solution",
                    clause = self.state.clauses.kinds[clause_id.to_index()]
                        .display(&self.state.variable_map, self.provider())
                );
            }

            if let Some(_first_conflicting_clause_id) = conflicting_clauses.into_iter().next() {
                self.state.decision_tracker.undo_until(starting_level);
                level = starting_level;
            }
        }
    }

    /// Decides how to terminate the solver algorithm when the given `solvable`
    /// was deemed unsolvable by [`Solver::run_sat`].
    ///
    /// Returns an `Err` value of [`UnsolvableOrCancelled::Unsolvable`] only if
    /// `solvable` is the very first solvable we are solving for. Otherwise,
    /// undoes all the decisions made when trying to solve for `solvable`,
    /// sets it to `false` and returns `Ok(false)`.
    fn run_sat_process_unsolvable(
        &mut self,
        solvable_or_root: SolvableIdOrRoot<D::SolvableId>,
        starting_level: u32,
        clause_id: ClauseId,
    ) -> Result<bool, UnsolvableOrCancelled> {
        if starting_level == 0 {
            tracing::trace!(
                "Unsolvable: {}",
                self.state.clauses.kinds[clause_id.to_index()]
                    .display(&self.state.variable_map, self.provider(),)
            );
            Err(UnsolvableOrCancelled::Unsolvable(
                self.analyze_unsolvable(clause_id),
            ))
        } else {
            self.state.decision_tracker.undo_until(starting_level);
            self.state
                .decision_tracker
                .try_add_decision(
                    Decision::new(
                        self.state
                            .variable_map
                            .intern_solvable_or_root(solvable_or_root),
                        false,
                        ClauseId::install_root(),
                    ),
                    starting_level + 1,
                )
                .expect("bug: already decided - decision should have been undone");
            Ok(false)
        }
    }

    /// Resolves all dependencies
    ///
    /// Repeatedly chooses the next variable to assign, and calls
    /// [`Solver::set_propagate_learn`] to drive the solving process (as you
    /// can see from the name, the method executes the set, propagate and
    /// learn steps described in the [`Solver::run_sat`] docs).
    ///
    /// The next variable to assign is obtained by finding the next dependency
    /// for which no concrete package has been picked yet. Then we pick the
    /// highest possible version for that package, or the favored version if
    /// it was provided by the user, and set its value to true.
    fn resolve_dependencies(&mut self, mut level: u32) -> Result<u32, UnsolvableOrCancelled> {
        loop {
            // Make a decision. If no decision could be made it means the problem is
            // satisfyable.
            #[cfg(feature = "diagnostics")]
            let decide_start = std::time::Instant::now();
            let Some((candidate, required_by, clause_id)) = self.decide() else {
                #[cfg(feature = "diagnostics")]
                {
                    self.state.propagation_counters.decide_duration += decide_start.elapsed();
                }
                break;
            };
            #[cfg(feature = "diagnostics")]
            {
                self.state.propagation_counters.decide_duration += decide_start.elapsed();
            }

            tracing::debug!(
                "╒══ Install {} at level {level} (derived from {})",
                candidate.display(&self.state.variable_map, self.provider()),
                self.state.clauses.kinds[clause_id.to_index()]
                    .display(&self.state.variable_map, self.provider())
            );

            // Propagate the decision
            match self.set_propagate_learn(level, candidate, required_by, clause_id) {
                Ok(new_level) => {
                    level = new_level;
                    tracing::debug!("╘══ Propagation completed");
                }
                Err(UnsolvableOrCancelled::Cancelled(value)) => {
                    tracing::debug!("╘══ Propagation cancelled");
                    return Err(UnsolvableOrCancelled::Cancelled(value));
                }
                Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
                    tracing::debug!("╘══ Propagation resulted in a conflict");
                    return Err(UnsolvableOrCancelled::Unsolvable(conflict));
                }
            }
        }

        // We just went through all clauses and there are no choices left to be made
        Ok(level)
    }

    /// This function is responsible for selecting the next solvable to assign
    /// after all logical decisions have been propagated. Once this situation
    /// happens we need to take a guess to make progress in the solving process.
    /// This function tries to find the best guess to make based on several
    /// heuristics. These heuristics are tuned to find a solution that also
    /// maximizes the user's requirements.
    ///
    /// The heuristics are (in order of importance):
    /// 1. Prefer decisions on explicit requirements over non-explicit
    ///    requirements. This ensures that direct dependencies are maximized
    ///    over transitive dependencies.
    /// 2. Prefer decisions with a higher "package activity score". This score
    ///    is incremented everytime a package is involved in a conflict and the
    ///    score of all package is decreases on each conflict. This is similar
    ///    to the "activity score" of the VSIDS algorithm used in many modern
    ///    solvers.
    /// 3. Prefer decisions with the least amount of possible candidates. If
    ///    there are multiple requirements for the same package the requirement
    ///    with the least amount of possible candidates requires less
    ///    backtracking to determine unsatisfiability than a requirement with
    ///    more possible candidates.
    ///
    /// The selection is computed incrementally by [`decide_queue::DecideQueue`]
    /// instead of rescanning every requires clause on every call; debug
    /// builds verify the queue's bookkeeping invariants on every call.
    fn decide(&mut self) -> Option<(VariableId, VariableId, ClauseId)> {
        let provider = self.cache.provider();
        let SolverState {
            decide_queue,
            decision_tracker,
            requirement_to_sorted_candidates,
            disjunctions,
            name_activity,
            max_activity,
            ..
        } = &mut self.state;

        let floor = decision_tracker.take_sync_floor();
        decide_queue.sync(
            floor,
            decision_tracker.assignments(),
            decision_tracker.map(),
        );
        let decision = decide_queue.next_decision(
            decision_tracker.map(),
            requirement_to_sorted_candidates,
            disjunctions,
            name_activity,
            *max_activity,
            provider,
        );

        #[cfg(debug_assertions)]
        decide_queue.debug_assert_invariants(
            decision_tracker.map(),
            requirement_to_sorted_candidates,
            disjunctions,
            name_activity,
            *max_activity,
            provider,
        );

        if let Some(decision) = &decision {
            tracing::trace!(
                "deciding to assign {}, ({}, {} activity score, {} possible candidates)",
                decision
                    .candidate
                    .display(&self.state.variable_map, self.provider()),
                self.state.clauses.kinds[decision.clause_id.to_index()]
                    .display(&self.state.variable_map, self.provider()),
                decision.package_activity,
                decision.candidate_count,
            );
        }

        decision.map(|decision| (decision.candidate, decision.required_by, decision.clause_id))
    }

    /// Executes one iteration of the CDCL loop
    ///
    /// A set-propagate-learn round is always initiated by a requirement clause
    /// (i.e. [`Clause::Requires`]). The parameters include the variable
    /// associated to the candidate for the dependency (`solvable`), the
    /// package that originates the dependency (`required_by`), and the
    /// id of the requires clause (`clause_id`).
    ///
    /// Refer to the documentation of [`Solver::run_sat`] for details on the
    /// CDCL algorithm.
    ///
    /// Returns the new level after this set-propagate-learn round, or a
    /// [`Conflict`] if we discovered that the requested jobs are
    /// unsatisfiable.
    fn set_propagate_learn(
        &mut self,
        mut level: u32,
        solvable: VariableId,
        _required_by: VariableId,
        clause_id: ClauseId,
    ) -> Result<u32, UnsolvableOrCancelled> {
        level += 1;

        self.state
            .decision_tracker
            .try_add_decision(Decision::new(solvable, true, clause_id), level)
            .expect("bug: solvable was already decided!");

        self.propagate_and_learn(level)
    }

    fn propagate_and_learn(&mut self, mut level: u32) -> Result<u32, UnsolvableOrCancelled> {
        loop {
            match self.propagate(level) {
                Ok(()) => {
                    return Ok(level);
                }
                Err(PropagationError::Cancelled(value)) => {
                    return Err(UnsolvableOrCancelled::Cancelled(value));
                }
                Err(PropagationError::Conflict(
                    conflicting_solvable,
                    attempted_value,
                    conflicting_clause,
                )) => {
                    level = self.learn_from_conflict(
                        level,
                        conflicting_solvable,
                        attempted_value,
                        conflicting_clause,
                    )?;
                }
            }
        }
    }

    fn learn_from_conflict(
        &mut self,
        mut level: u32,
        conflicting_solvable: VariableId,
        attempted_value: bool,
        conflicting_clause: ClauseId,
    ) -> Result<u32, Conflict> {
        #[cfg(feature = "diagnostics")]
        let learn_start = std::time::Instant::now();
        {
            tracing::debug!(
                "├┬ Propagation conflicted: could not set {solvable} to {attempted_value}",
                solvable = conflicting_solvable.display(&self.state.variable_map, self.provider()),
            );
            tracing::debug!(
                "││ During unit propagation for clause: {}",
                self.state.clauses.kinds[conflicting_clause.to_index()]
                    .display(&self.state.variable_map, self.provider())
            );

            tracing::debug!(
                "││ Previously decided value: {}. Derived from: {}",
                !attempted_value,
                self.state.clauses.kinds[self
                    .state
                    .decision_tracker
                    .find_clause_for_assignment(conflicting_solvable)
                    .unwrap()
                    .to_index()]
                .display(&self.state.variable_map, self.provider()),
            );
        }

        if level == 1 {
            for decision in self.state.decision_tracker.stack() {
                let clause_id = decision.derived_from;
                let clause = self.state.clauses.kinds[clause_id.to_index()];
                let level = self.state.decision_tracker.level(decision.variable);
                let action = if decision.value { "install" } else { "forbid" };

                if let Clause::ForbidMultipleInstances(..) = clause {
                    // Skip forbids clauses, to reduce noise
                    continue;
                }

                tracing::debug!(
                    "* ({level}) {action} {}. Reason: {}",
                    decision
                        .variable
                        .display(&self.state.variable_map, self.provider()),
                    self.state.clauses.kinds[decision.derived_from.to_index()]
                        .display(&self.state.variable_map, self.provider()),
                );
            }

            #[cfg(feature = "diagnostics")]
            {
                self.state.propagation_counters.learn_duration += learn_start.elapsed();
            }
            return Err(self.analyze_unsolvable(conflicting_clause));
        }

        let (new_level, learned_clause_id, literal) =
            self.analyze(level, conflicting_solvable, conflicting_clause);
        let old_level = level;
        level = new_level;

        // Optimization: propagate right now, since we know that the clause is a unit
        // clause
        let decision = literal.satisfying_value();
        self.state
            .decision_tracker
            .try_add_decision(
                Decision::new(literal.variable(), decision, learned_clause_id),
                level,
            )
            .expect("bug: solvable was already decided!");
        tracing::trace!(
            "│├ Propagate after learn: {} = {decision}",
            literal
                .variable()
                .display(&self.state.variable_map, self.provider()),
        );

        tracing::debug!("│└ Backtracked from {old_level} -> {level}");

        #[cfg(feature = "diagnostics")]
        {
            self.state.propagation_counters.learn_duration += learn_start.elapsed();
        }

        Ok(level)
    }

    /// The propagate step of the CDCL algorithm
    ///
    /// Propagation is implemented by means of watches: each clause that has two
    /// or more literals is "subscribed" to changes in the values of two
    /// solvables that appear in the clause. When a value is assigned to a
    /// solvable, each of the clauses tracking that solvable will be notified.
    /// That way, the clause can check whether the literal that is using the
    /// solvable has become false, in which case it picks a new solvable to
    /// watch (if available) or triggers an assignment.
    fn propagate(&mut self, level: u32) -> Result<(), PropagationError> {
        #[cfg(feature = "diagnostics")]
        let propagation_start = std::time::Instant::now();
        #[cfg(feature = "diagnostics")]
        {
            self.state.propagation_counters.propagate_calls += 1;
        }

        let result = self.propagate_impl(level);

        #[cfg(feature = "diagnostics")]
        {
            self.state.propagation_counters.propagation_duration += propagation_start.elapsed();
        }

        result
    }

    fn propagate_impl(&mut self, level: u32) -> Result<(), PropagationError> {
        if let Some(value) = self.provider().should_cancel_with_value() {
            return Err(PropagationError::Cancelled(value));
        };

        // Add decisions from assertions and learned clauses. If any of these cause a
        // conflict, we will return an error.
        self.decide_assertions(level)?;
        self.decide_learned(level)?;

        // For each decision that has not been propagated yet, we propagate the
        // decision.
        //
        // Propagation entails iterating through the linked list of clauses that watch
        // the literal that the decision caused to turn false. If a clause can only be
        // satisfied if one of the literals involved is assigned a value, we also make a
        // decision on that literal to ensure that the clause is satisfied.
        //
        // Any new decision is also propagated. If by making a decision on one of the
        // remaining literals of a clause we cause a conflict, propagation is halted and
        // an error is returned.

        let interner = self.cache.provider();
        let clause_kinds = &self.state.clauses.kinds;

        while let Some(decision) = self.state.decision_tracker.next_unpropagated() {
            let watched_literal = Literal::new(decision.variable, decision.value);

            #[cfg(feature = "diagnostics")]
            {
                self.state.propagation_counters.decisions_propagated += 1;
            }

            debug_assert!(
                watched_literal.eval(self.state.decision_tracker.map()) == Some(false),
                "we are only watching literals that are turning false"
            );

            // Propagate, iterating through the linked list of clauses that
            // watch this solvable.
            let mut next_cursor = self
                .state
                .watches
                .cursor(&mut self.state.clauses.watched_literals, watched_literal);
            while let Some(cursor) = next_cursor.take() {
                let clause_id = cursor.clause_id();
                let clause = &clause_kinds[clause_id.to_index()];
                let watch_index = cursor.watch_index();

                #[cfg(feature = "diagnostics")]
                {
                    self.state.propagation_counters.clause_visits += 1;
                    self.state.propagation_counters.visits_by_type.count(clause);
                }

                // If the other literal the current clause is watching is already true, we can
                // skip this clause. Its is already satisfied.
                let watched_literals = cursor.watched_literals();
                // Prefetch the next clause's `WatchedLiterals` to overlap the
                // pointer-chasing latency with this iteration's work. The
                // inner BCP loop is memory-bound on this linked-list walk.
                cursor.prefetch_next();
                let other_watched_literal =
                    watched_literals.watched_literals[1 - cursor.watch_index()];
                if other_watched_literal.eval(self.state.decision_tracker.map()) == Some(true) {
                    #[cfg(feature = "diagnostics")]
                    {
                        self.state.propagation_counters.early_skips += 1;
                    }
                    // Continue with the next clause in the linked list.
                    next_cursor = cursor.next();
                } else if let Some(literal) = if clause.is_binary() {
                    // Binary clauses can never move their watches; skip the
                    // `next_unwatched_literal` scan entirely.
                    None
                } else {
                    #[cfg(feature = "diagnostics")]
                    {
                        self.state
                            .propagation_counters
                            .unwatched_calls_by_type
                            .count(clause);
                    }
                    watched_literals.next_unwatched_literal(
                        clause,
                        &self.state.learnt_clauses,
                        &self.state.requirement_to_sorted_candidates,
                        &self.state.disjunctions,
                        self.state.decision_tracker.map(),
                        watch_index,
                    )
                } {
                    #[cfg(feature = "diagnostics")]
                    {
                        self.state.propagation_counters.watch_moves += 1;
                    }
                    // Update the watch to point to the new literal
                    next_cursor = cursor.update(literal);
                } else {
                    #[cfg(feature = "diagnostics")]
                    {
                        self.state.propagation_counters.unit_propagations += 1;
                    }
                    // We could not find another literal to watch, which means the remaining
                    // watched literal must be set to true.
                    let decided = self
                        .state
                        .decision_tracker
                        .try_add_decision(
                            Decision::new(
                                other_watched_literal.variable(),
                                other_watched_literal.satisfying_value(),
                                clause_id,
                            ),
                            level,
                        )
                        .map_err(|_| {
                            #[cfg(feature = "diagnostics")]
                            {
                                self.state.propagation_counters.conflicts += 1;
                            }
                            PropagationError::Conflict(
                                other_watched_literal.variable(),
                                true,
                                clause_id,
                            )
                        })?;

                    if decided {
                        match clause {
                            // Skip logging for ForbidMultipleInstances, which is so noisy
                            Clause::ForbidMultipleInstances(..) => {}
                            _ => {
                                tracing::debug!(
                                    "├ Propagate {} = {}. {}",
                                    other_watched_literal
                                        .variable()
                                        .display(&self.state.variable_map, interner),
                                    other_watched_literal.satisfying_value(),
                                    clause.display(&self.state.variable_map, interner)
                                );
                            }
                        }
                    }

                    // Skip to the next clause in the linked list.
                    next_cursor = cursor.next();
                }
            }
        }

        Ok(())
    }

    /// Add decisions for negative assertions derived from other rules
    /// (assertions are clauses that consist of a single literal, and
    /// therefore do not have watches).
    fn decide_assertions(&mut self, level: u32) -> Result<(), PropagationError> {
        for &(solvable_id, clause_id) in &self.state.negative_assertions {
            let value = false;
            let decided = self
                .state
                .decision_tracker
                .try_add_decision(Decision::new(solvable_id, value, clause_id), level)
                .map_err(|_| PropagationError::Conflict(solvable_id, value, clause_id))?;

            if decided {
                tracing::trace!(
                    "Negative assertions derived from other rules: Propagate assertion {} = {}",
                    solvable_id.display(&self.state.variable_map, self.provider()),
                    value
                );
            }
        }
        Ok(())
    }

    /// Add decisions derived from learnt clauses.
    fn decide_learned(&mut self, level: u32) -> Result<(), PropagationError> {
        // Assertions derived from learnt rules
        for learn_clause_idx in 0..self.state.learnt_clause_ids.len() {
            let clause_id = self.state.learnt_clause_ids[learn_clause_idx];
            let clause = self.state.clauses.kinds[clause_id.to_index()];
            let Clause::Learnt(learnt_index) = clause else {
                unreachable!();
            };

            let literals = &self.state.learnt_clauses[learnt_index];
            if literals.len() > 1 {
                continue;
            }

            debug_assert!(!literals.is_empty());

            let literal = literals[0];
            let decision = literal.satisfying_value();

            let decided = self
                .state
                .decision_tracker
                .try_add_decision(
                    Decision::new(literal.variable(), decision, clause_id),
                    level,
                )
                .map_err(|_| PropagationError::Conflict(literal.variable(), decision, clause_id))?;

            if decided {
                tracing::trace!(
                    "├─ Propagate assertion {} = {}",
                    literal
                        .variable()
                        .display(&self.state.variable_map, self.provider()),
                    decision
                );
            }
        }

        Ok(())
    }

    /// Adds the clause with `clause_id` to the current [`Conflict`]
    ///
    /// Because learnt clauses are not relevant for the user, they are not added
    /// to the [`Conflict`]. Instead, we report the clauses that caused them.
    fn analyze_unsolvable_clause(
        clauses: &[Clause<D::NameId>],
        learnt_why: &Mapping<LearntClauseId, Vec<ClauseId>>,
        clause_id: ClauseId,
        conflict: &mut Conflict,
        seen: &mut IndexedSet<ClauseId>,
    ) {
        let clause = &clauses[clause_id.to_index()];
        match clause {
            Clause::Learnt(learnt_clause_id) => {
                if !seen.insert(clause_id) {
                    return;
                }

                for &cause in learnt_why
                    .get(*learnt_clause_id)
                    .expect("no cause for learnt clause available")
                {
                    Self::analyze_unsolvable_clause(clauses, learnt_why, cause, conflict, seen);
                }
            }
            _ => conflict.add_clause(clause_id),
        }
    }

    /// Create a [`Conflict`] based on the id of the clause that triggered an
    /// unrecoverable conflict
    fn analyze_unsolvable(&mut self, clause_id: ClauseId) -> Conflict {
        let last_decision = self.state.decision_tracker.stack().last().unwrap();
        let highest_level = self.state.decision_tracker.level(last_decision.variable);
        debug_assert_eq!(highest_level, 1);

        let mut conflict = Conflict::default();

        tracing::debug!("=== ANALYZE UNSOLVABLE");

        let mut involved = HashSet::default();
        self.state.clauses.kinds[clause_id.to_index()].visit_literals(
            &self.state.learnt_clauses,
            &self.state.requirement_to_sorted_candidates,
            &self.state.disjunctions,
            |literal| {
                involved.insert(literal.variable());
            },
        );

        let mut seen = IndexedSet::default();
        Self::analyze_unsolvable_clause(
            &self.state.clauses.kinds,
            &self.state.learnt_why,
            clause_id,
            &mut conflict,
            &mut seen,
        );

        for decision in self.state.decision_tracker.stack().rev() {
            if decision.variable.is_root() {
                continue;
            }

            let why = decision.derived_from;

            if !involved.contains(&decision.variable) {
                continue;
            }

            assert_ne!(why, ClauseId::install_root());

            Self::analyze_unsolvable_clause(
                &self.state.clauses.kinds,
                &self.state.learnt_why,
                why,
                &mut conflict,
                &mut seen,
            );

            self.state.clauses.kinds[why.to_index()].visit_literals(
                &self.state.learnt_clauses,
                &self.state.requirement_to_sorted_candidates,
                &self.state.disjunctions,
                |literal| {
                    if literal.eval(self.state.decision_tracker.map()) == Some(true) {
                        assert_eq!(literal.variable(), decision.variable);
                    } else {
                        involved.insert(literal.variable());
                    }
                },
            );
        }

        conflict
    }

    /// Analyze the causes of the conflict and learn from it
    ///
    /// This function finds the combination of assignments that caused the
    /// conflict and adds a new clause to the solver to forbid that
    /// combination of assignments (i.e. learn from this mistake
    /// so it is not repeated in the future). It corresponds to the
    /// `Solver.analyze` function from the MiniSAT paper.
    ///
    /// Returns the level to which we should backtrack, the id of the learnt
    /// clause and the literal that should be assigned (by definition, when
    /// we learn a clause, all its literals except one evaluate to false, so
    /// the value of the remaining literal must be assigned to make the clause
    /// become true)
    fn analyze(
        &mut self,
        mut current_level: u32,
        mut conflicting_solvable: VariableId,
        mut clause_id: ClauseId,
    ) -> (u32, ClauseId, Literal) {
        let mut seen = HashSet::default();
        let mut causes_at_current_level = 0u32;
        let mut learnt = Vec::new();
        let mut back_track_to = 0;
        // Index in `learnt` of the highest-level non-asserting literal, moved
        // to the front below so it becomes the second watch (watch2onhighest).
        let mut highest_level_idx = 0;

        let mut s_value;
        let mut learnt_why = Vec::new();
        let mut first_iteration = true;
        let clause_kinds = &self.state.clauses.kinds;
        loop {
            learnt_why.push(clause_id);

            clause_kinds[clause_id.to_index()].visit_literals(
                &self.state.learnt_clauses,
                &self.state.requirement_to_sorted_candidates,
                &self.state.disjunctions,
                |literal| {
                    if !first_iteration && literal.variable() == conflicting_solvable {
                        // We are only interested in the causes of the conflict, so we ignore the
                        // solvable whose value was propagated
                        return;
                    }

                    if !seen.insert(literal.variable()) {
                        // Skip literals we have already seen
                        return;
                    }

                    let decision_level = self.state.decision_tracker.level(literal.variable());
                    if decision_level == current_level {
                        causes_at_current_level += 1;
                    } else if current_level > 1 {
                        let learnt_literal = Literal::new(
                            literal.variable(),
                            self.state
                                .decision_tracker
                                .assigned_value(literal.variable())
                                .unwrap(),
                        );
                        if decision_level > back_track_to {
                            back_track_to = decision_level;
                            highest_level_idx = learnt.len();
                        }
                        learnt.push(learnt_literal);
                    } else {
                        unreachable!();
                    }
                },
            );

            first_iteration = false;

            // Select next literal to look at
            loop {
                let (last_decision, last_decision_level) = self.state.decision_tracker.undo_last();

                conflicting_solvable = last_decision.variable;
                s_value = last_decision.value;
                clause_id = last_decision.derived_from;

                current_level = last_decision_level;

                // We are interested in the first literal we come across that caused the
                // conflicting assignment
                if seen.contains(&last_decision.variable) {
                    break;
                }
            }

            causes_at_current_level = causes_at_current_level.saturating_sub(1);
            if causes_at_current_level == 0 {
                break;
            }
        }

        // Watch the two highest-level literals: the asserting literal (pushed
        // last) and the highest-level of the rest (moved to the front). They
        // are unassigned last on backtracking, so the watches move least.
        if !learnt.is_empty() {
            learnt.swap(0, highest_level_idx);
        }

        let last_literal = Literal::new(conflicting_solvable, s_value);
        learnt.push(last_literal);

        // Increase the activity of the packages in the learned clause
        for literal in &learnt {
            let name_id = literal
                .variable()
                .as_solvable(&self.state.variable_map)
                .map(|s| self.provider().solvable_name(s));
            if let Some(name_id) = name_id {
                let activity = self.state.name_activity.get(name_id) + self.activity_add;
                self.state.name_activity.set(name_id, activity);
                if activity > self.state.max_activity {
                    self.state.max_activity = activity;
                }
                self.state.decide_queue.mark_name_hot(name_id);
            }
        }

        // Add the clause
        let learnt_id = self.state.learnt_clauses.alloc(learnt);
        self.state.learnt_why.insert(learnt_id, learnt_why);

        let (watched_literals, kind) =
            WatchedLiterals::learnt(learnt_id, &self.state.learnt_clauses[learnt_id]);
        let clause_id = self.state.add_clause(watched_literals, kind);
        self.state.learnt_clause_ids.push(clause_id);

        tracing::debug!("│├ Learnt disjunction:",);
        for lit in &self.state.learnt_clauses[learnt_id] {
            tracing::debug!(
                "││ - {}{}",
                if lit.negate() { "NOT " } else { "" },
                lit.variable()
                    .display(&self.state.variable_map, self.provider()),
            );
        }

        // Should revert at most to the root level
        let target_level = back_track_to.max(1);
        self.state.decision_tracker.undo_until(target_level);

        self.decay_activity_scores();

        (target_level, clause_id, last_literal)
    }

    /// Decays the activity scores of all packages in the solver. This function
    /// is caleld after each conflict.
    fn decay_activity_scores(&mut self) {
        self.state.name_activity.for_each_mut(|activity| {
            *activity *= self.activity_decay;
        });
        // The same f32 multiplication applied to the identical value keeps
        // `max_activity` bit-exact with the largest stored activity.
        self.state.max_activity *= self.activity_decay;
    }
}

impl<D: DependencyProvider> SolverState<D> {
    /// Registers a newly encoded requires clause with the incremental decide
    /// queue.
    pub(crate) fn add_requires_clause(
        &mut self,
        parent: VariableId,
        requirement: Requirement,
        condition: Option<DisjunctionId>,
        clause_id: ClauseId,
        names: impl IntoIterator<Item = D::NameId>,
    ) {
        self.decide_queue.register_clause(
            parent,
            requirement,
            condition,
            clause_id,
            names,
            &self.disjunctions,
            self.decision_tracker.assigned_value(parent),
        );
    }

    /// Allocate a clause and, if it has watched literals, register them in
    /// the [`WatchMap`].
    pub(crate) fn add_clause(
        &mut self,
        watched_literals: Option<WatchedLiterals>,
        kind: Clause<D::NameId>,
    ) -> ClauseId {
        let clause_id = self.clauses.alloc(watched_literals, kind);
        let Some(wl) = self.clauses.watched_literals[clause_id.to_index()].as_mut() else {
            return clause_id;
        };

        self.watches.start_watching(wl, clause_id);

        clause_id
    }

    /// Returns the solvables that the solver has chosen to include in the
    /// solution so far.
    fn chosen_solvables(&self) -> impl Iterator<Item = D::SolvableId> + '_ {
        self.decision_tracker.stack().filter_map(|d| {
            if d.value {
                d.variable.as_solvable(&self.variable_map)
            } else {
                // Ignore things that are set to false
                None
            }
        })
    }

    /// Returns true if `solvable_id` has been assigned the value `true` in the
    /// current decision state. A solvable that has never been interned as a
    /// variable is treated as not decided.
    pub(crate) fn is_positively_decided(&self, solvable_id: D::SolvableId) -> bool {
        match self.variable_map.lookup_solvable(solvable_id) {
            Some(variable) => self.decision_tracker.assigned_value(variable) == Some(true),
            None => false,
        }
    }

    /// Returns the `ConditionId`s of deferred requirements whose gating
    /// disjunct currently holds. Entries are reported in insertion order so
    /// that drain order is deterministic.
    pub(crate) fn fired_deferred_conditions(&self) -> Vec<ConditionId> {
        self.deferred_requirements
            .iter()
            .filter(|(_, entries)| {
                entries.iter().any(|entry| {
                    condition_disjunct_holds(&entry.disjunct, |s| self.is_positively_decided(s))
                })
            })
            .map(|(condition, _)| *condition)
            .collect()
    }

    /// Drain deferred requirements for `condition` whose disjunct currently
    /// holds. Removed entries are returned. If, after draining, no entries
    /// remain for `condition`, the key is removed from the map entirely.
    pub(crate) fn drain_fired_deferred(
        &mut self,
        condition: ConditionId,
    ) -> Vec<DeferredRequirement<D::SolvableId>> {
        // Decide first which indices fire while only holding immutable
        // borrows of the state, then mutate the deferred map. The two-pass
        // structure avoids overlapping mutable and immutable borrows of
        // `self`.
        let fire_mask: Vec<bool> = match self.deferred_requirements.get(&condition) {
            Some(entries) => entries
                .iter()
                .map(|entry| {
                    condition_disjunct_holds(&entry.disjunct, |s| self.is_positively_decided(s))
                })
                .collect(),
            None => return Vec::new(),
        };

        let entries = self
            .deferred_requirements
            .get_mut(&condition)
            .expect("entries existed in the immutable phase");
        let mut fired = Vec::new();
        // Use `remove` instead of `swap_remove`: it preserves the relative
        // order of the entries that stay in the deferred map, so that any
        // subsequent drain visits them in the same order regardless of how
        // many drains have happened before. Walk indices in reverse so each
        // `remove` does not shift the indices we still need to inspect.
        for (i, _) in fire_mask
            .iter()
            .enumerate()
            .rev()
            .filter(|&(_, &did_fire)| did_fire)
        {
            fired.push(entries.remove(i));
        }

        if entries.is_empty() {
            self.deferred_requirements.swap_remove(&condition);
        }

        // We pushed in reverse order; restore insertion order for determinism.
        fired.reverse();
        fired
    }

    /// Register a new deferred requirement. Used by the encoder when it
    /// detects that a conditional requirement's disjunct does not yet hold.
    pub(crate) fn push_deferred(&mut self, entry: DeferredRequirement<D::SolvableId>) {
        self.deferred_requirements
            .entry(entry.condition)
            .or_default()
            .push(entry);
    }

    /// Total number of deferred per-disjunct entries still waiting for their
    /// condition to fire.
    pub(crate) fn deferred_requirements_count(&self) -> usize {
        self.deferred_requirements
            .values()
            .map(|entries| entries.len())
            .sum()
    }
}
