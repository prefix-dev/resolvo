use std::{any::Any, fmt::Display, ops::ControlFlow};

use ahash::{HashMap, HashSet};
pub use cache::SolverCache;
use clause::{Clause, Literal, WatchedLiterals};
use conditions::{Disjunction, DisjunctionId};
use decision::Decision;
use decision_tracker::DecisionTracker;
use elsa::FrozenMap;
use encoding::Encoder;
use indexmap::IndexMap;
use itertools::Itertools;
use variable_map::VariableMap;
use watch_map::WatchMap;

use crate::{
    ConditionalRequirement, Dependencies, DependencyProvider, KnownDependencies, Requirement,
    VersionSetId,
    conflict::Conflict,
    internal::{
        arena::{Arena, ArenaId},
        id::{ClauseId, LearntClauseId, NameId, SolvableId, SolvableOrRootId, VariableId},
    },
    runtime::{AsyncRuntime, NowOrNeverRuntime},
    solver::binary_encoding::AtMostOnceTracker,
    utils::Mapping,
};

mod binary_encoding;
mod cache;
pub(crate) mod clause;
mod conditions;
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
pub struct Problem<S> {
    requirements: Vec<ConditionalRequirement>,
    constraints: Vec<VersionSetId>,
    soft_requirements: S,
}

impl Default for Problem<std::iter::Empty<SolvableId>> {
    fn default() -> Self {
        Self::new()
    }
}

impl Problem<std::iter::Empty<SolvableId>> {
    /// Creates a new empty [`Problem`]. Use the setter methods to build the
    /// problem before passing it to the solver to be solved.
    pub fn new() -> Self {
        Self {
            requirements: Default::default(),
            constraints: Default::default(),
            soft_requirements: Default::default(),
        }
    }
}

impl<S: IntoIterator<Item = SolvableId>> Problem<S> {
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
    pub fn soft_requirements<I: IntoIterator<Item = SolvableId>>(
        self,
        soft_requirements: I,
    ) -> Problem<I> {
        Problem {
            requirements: self.requirements,
            constraints: self.constraints,
            soft_requirements,
        }
    }
}

#[derive(Default)]
pub(crate) struct Clauses {
    pub(crate) kinds: Vec<Clause>,
    watched_literals: Vec<Option<WatchedLiterals>>,
}

impl Clauses {
    pub fn alloc(&mut self, watched_literals: Option<WatchedLiterals>, kind: Clause) -> ClauseId {
        let id = ClauseId::from_usize(self.kinds.len());
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
    pub(crate) state: SolverState,

    /// The activity add factor. This is a value that is added to the activity
    /// score of each package that is part of a conflict.
    activity_add: f32,

    /// The activity decay factor. This is a value between 0 and 1 with which
    /// the activity scores of each package are multiplied when a conflict is
    /// detected.
    activity_decay: f32,
}

type RequiresClause = (Requirement, Option<DisjunctionId>, ClauseId);

#[derive(Default)]
pub(crate) struct SolverState {
    pub(crate) clauses: Clauses,
    requires_clauses: IndexMap<VariableId, Vec<RequiresClause>, ahash::RandomState>,
    watches: WatchMap,

    /// A mapping from requirements to the variables that represent the
    /// candidates.
    requirement_to_sorted_candidates:
        FrozenMap<Requirement, RequirementCandidateVariables, ahash::RandomState>,

    pub(crate) variable_map: VariableMap,

    negative_assertions: Vec<(VariableId, ClauseId)>,

    learnt_clauses: Arena<LearntClauseId, Vec<Literal>>,
    learnt_why: Mapping<LearntClauseId, Vec<ClauseId>>,
    learnt_clause_ids: Vec<ClauseId>,

    disjunctions: Arena<DisjunctionId, Disjunction>,

    clauses_added_for_package: HashSet<NameId>,
    clauses_added_for_solvable: HashSet<SolvableOrRootId>,
    at_most_one_trackers: HashMap<NameId, AtMostOnceTracker<VariableId>>,

    /// Keeps track of auxiliary variables that are used to encode at-least-one
    /// solvable for a package.
    at_least_one_tracker: HashMap<NameId, VariableId>,

    pub(crate) decision_tracker: DecisionTracker,

    /// Activity score per package.
    name_activity: Vec<f32>,
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
        problem: Problem<impl IntoIterator<Item = SolvableId>>,
    ) -> Result<Vec<SolvableId>, UnsolvableOrCancelled> {
        // Re-initialize the solver state.
        self.state = SolverState::default();

        // Construct the root dependencies from the problem
        let root_dependencies = Dependencies::Known(KnownDependencies {
            requirements: problem.requirements,
            constrains: problem.constraints,
        });

        // The first clause will always be the install root clause. Here we verify that
        // this is indeed the case.
        let root_clause = {
            let (state, kind) = WatchedLiterals::root();
            self.state.clauses.alloc(state, kind)
        };
        assert_eq!(root_clause, ClauseId::install_root());

        assert!(
            self.run_sat(SolvableOrRootId::root(), &root_dependencies)?,
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
        root_solvable: SolvableOrRootId,
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
                let conflicting_clauses = self.async_runtime.block_on(
                    Encoder::new(&mut self.state, &self.cache, root_deps, level)
                        .encode([root_solvable]),
                )?;

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
                            clause = self.state.clauses.kinds[clause_id.to_usize()]
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
            let new_solvables: Vec<_> = self
                .state
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
                        .contains(&solvable_or_root)
                })
                .map(|d| (d.variable, d.derived_from))
                .collect();

            if new_solvables.is_empty() {
                // If no new literals were selected this solution is complete and we can return.
                tracing::trace!(
                    "Level {}: No new solvables selected, solution is complete",
                    level
                );
                return Ok(true);
            }

            tracing::debug!("==== Found newly selected solvables");
            tracing::debug!(
                " - {}",
                new_solvables
                    .iter()
                    .copied()
                    .format_with("\n- ", |(id, derived_from), f| f(&format_args!(
                        "{} (derived from {})",
                        id.display(&self.state.variable_map, self.provider()),
                        self.state.clauses.kinds[derived_from.to_usize()]
                            .display(&self.state.variable_map, self.provider()),
                    )))
                    .to_string()
            );
            tracing::debug!("====");

            let new_solvables: Vec<SolvableOrRootId> = new_solvables
                .iter()
                .filter_map(|(variable, _)| {
                    self.state
                        .variable_map
                        .origin(*variable)
                        .as_solvable()
                        .map(Into::into)
                })
                .collect::<Vec<_>>();

            let conflicting_clauses = self.async_runtime.block_on(
                Encoder::new(&mut self.state, &self.cache, root_deps, level).encode(new_solvables),
            )?;

            // Serially process the outputs, to reduce the need for synchronization
            for &clause_id in &conflicting_clauses {
                tracing::debug!(
                    "├─ Added clause {clause} introduces a conflict which invalidates the partial solution",
                    clause = self.state.clauses.kinds[clause_id.to_usize()]
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
        solvable_or_root: SolvableOrRootId,
        starting_level: u32,
        clause_id: ClauseId,
    ) -> Result<bool, UnsolvableOrCancelled> {
        if starting_level == 0 {
            tracing::trace!(
                "Unsolvable: {}",
                self.state.clauses.kinds[clause_id.to_usize()]
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
            let Some((candidate, required_by, clause_id)) = self.decide() else {
                break;
            };

            tracing::debug!(
                "╒══ Install {} at level {level} (derived from {})",
                candidate.display(&self.state.variable_map, self.provider()),
                self.state.clauses.kinds[clause_id.to_usize()]
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
    fn decide(&mut self) -> Option<(VariableId, VariableId, ClauseId)> {
        struct PossibleDecision {
            /// The activity of the package that is selected
            package_activity: f32,

            /// If this decision is based on a requirement that is explicitly
            /// requested by the user.
            is_explicit_requirement: bool,

            /// The total number of possible candidates that are available for
            /// this requirement.
            candidate_count: u32,

            /// The decision to make.
            decision: (VariableId, VariableId, ClauseId),
        }

        let mut best_decision: Option<PossibleDecision> = None;
        for (&solvable_id, requirements) in self.state.requires_clauses.iter() {
            let is_explicit_requirement = solvable_id == VariableId::root();
            if let Some(best_decision) = &best_decision {
                // If we already have an explicit requirement, there is no need to evaluate
                // non-explicit requirements.
                if best_decision.is_explicit_requirement && !is_explicit_requirement {
                    continue;
                }
            }

            // Consider only clauses in which we have decided to install the solvable
            if self.state.decision_tracker.assigned_value(solvable_id) != Some(true) {
                continue;
            }

            for (deps, condition, clause_id) in requirements.iter() {
                let mut candidate = ControlFlow::Break(());

                // If the clause has a condition that is not yet satisfied we need to skip it.
                if let Some(condition) = *condition {
                    let literals = &self.state.disjunctions[condition].literals;
                    if !literals.iter().all(|c| {
                        let value = c.eval(self.state.decision_tracker.map());
                        value == Some(false)
                    }) {
                        // The condition is not satisfied, skip this clause.
                        continue;
                    }
                }

                // Get the candidates for the individual version sets.
                let version_set_candidates = &self.state.requirement_to_sorted_candidates[deps];

                // Iterate over all version sets in the requirement and find the first version
                // set that we can act on, or if a single candidate (from any version set) makes
                // the clause true.
                //
                // NOTE: We zip the version sets from the requirements and the variables that we
                // previously cached. This assumes that the order of the version sets is the
                // same in both collections.
                for (version_set, candidates) in deps
                    .version_sets(self.provider())
                    .zip(version_set_candidates)
                {
                    // Find the first candidate that is not yet assigned a value or find the first
                    // value that makes this clause true.
                    candidate = candidates.iter().try_fold(
                        match candidate {
                            ControlFlow::Continue(x) => x,
                            _ => None,
                        },
                        |first_candidate, &candidate| {
                            let assigned_value =
                                self.state.decision_tracker.assigned_value(candidate);
                            ControlFlow::Continue(match assigned_value {
                                Some(true) => {
                                    // This candidate has already been assigned so the clause is
                                    // already true. Skip it.
                                    return ControlFlow::Break(());
                                }
                                Some(false) => {
                                    // This candidate has already been assigned false, continue the
                                    // search.
                                    first_candidate
                                }
                                None => match first_candidate {
                                    Some((
                                        first_candidate,
                                        candidate_version_set,
                                        mut candidate_count,
                                        package_activity,
                                    )) => {
                                        // We found a candidate that has not been assigned yet, but
                                        // it is not the first candidate.
                                        if candidate_version_set == version_set {
                                            // Increment the candidate count if this is a candidate
                                            // in the same version set.
                                            candidate_count += 1u32;
                                        }
                                        Some((
                                            first_candidate,
                                            candidate_version_set,
                                            candidate_count,
                                            package_activity,
                                        ))
                                    }
                                    None => {
                                        // We found the first candidate that has not been assigned
                                        // yet.
                                        let package_activity = self.state.name_activity[self
                                            .provider()
                                            .version_set_name(version_set)
                                            .to_usize()];
                                        Some((candidate, version_set, 1, package_activity))
                                    }
                                },
                            })
                        },
                    );

                    // Stop searching if we found a candidate that makes the clause true.
                    if candidate.is_break() {
                        break;
                    }
                }

                match candidate {
                    ControlFlow::Break(_) => {
                        // A candidate has been assigned true which means the clause is already
                        // true, and we can skip it.
                        continue;
                    }
                    ControlFlow::Continue(None) => {
                        unreachable!(
                            "when we get here it means that all candidates have been assigned false. This should not be able to happen at this point because during propagation the solvable should have been assigned false as well."
                        )
                    }
                    ControlFlow::Continue(Some((
                        candidate,
                        _version_set_id,
                        candidate_count,
                        package_activity,
                    ))) => {
                        let decision = (candidate, solvable_id, *clause_id);
                        best_decision = Some(match &best_decision {
                            None => PossibleDecision {
                                is_explicit_requirement,
                                package_activity,
                                candidate_count,
                                decision,
                            },
                            Some(best_decision) => {
                                // Prefer decisions on explicit requirements over non-explicit
                                // requirements. This optimizes direct dependencies over transitive
                                // dependencies.
                                if best_decision.is_explicit_requirement && !is_explicit_requirement
                                {
                                    continue;
                                }

                                // Prefer decisions with a higher package activity score to root out
                                // conflicts faster.
                                if best_decision.package_activity >= package_activity {
                                    continue;
                                }

                                if best_decision.candidate_count <= candidate_count {
                                    continue;
                                }

                                PossibleDecision {
                                    is_explicit_requirement,
                                    package_activity,
                                    candidate_count,
                                    decision,
                                }
                            }
                        })
                    }
                }
            }
        }

        if let Some(PossibleDecision {
            candidate_count,
            package_activity,
            decision: (candidate, _solvable_id, clause_id),
            ..
        }) = &best_decision
        {
            tracing::trace!(
                "deciding to assign {}, ({}, {} activity score, {} possible candidates)",
                candidate.display(&self.state.variable_map, self.provider()),
                self.state.clauses.kinds[clause_id.to_usize()]
                    .display(&self.state.variable_map, self.provider()),
                package_activity,
                candidate_count,
            );
        }

        // Could not find a requirement that needs satisfying.
        best_decision.map(
            |PossibleDecision {
                 decision: (candidate, required_by, via),
                 ..
             }| { (candidate, required_by, via) },
        )
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
        {
            tracing::debug!(
                "├┬ Propagation conflicted: could not set {solvable} to {attempted_value}",
                solvable = conflicting_solvable.display(&self.state.variable_map, self.provider()),
            );
            tracing::debug!(
                "││ During unit propagation for clause: {}",
                self.state.clauses.kinds[conflicting_clause.to_usize()]
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
                    .to_usize()]
                .display(&self.state.variable_map, self.provider()),
            );
        }

        if level == 1 {
            for decision in self.state.decision_tracker.stack() {
                let clause_id = decision.derived_from;
                let clause = self.state.clauses.kinds[clause_id.to_usize()];
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
                    self.state.clauses.kinds[decision.derived_from.to_usize()]
                        .display(&self.state.variable_map, self.provider()),
                );
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

            debug_assert!(
                watched_literal.eval(self.state.decision_tracker.map()) == Some(false),
                "we are only watching literals that are turning false"
            );

            // Propagate, iterating through the linked list of clauses that watch this
            // solvable
            let mut next_cursor = self
                .state
                .watches
                .cursor(&mut self.state.clauses.watched_literals, watched_literal);
            while let Some(cursor) = next_cursor.take() {
                let clause_id = cursor.clause_id();
                let clause = &clause_kinds[clause_id.to_usize()];
                let watch_index = cursor.watch_index();

                // If the other literal the current clause is watching is already true, we can
                // skip this clause. Its is already satisfied.
                let watched_literals = cursor.watched_literals();
                let other_watched_literal =
                    watched_literals.watched_literals[1 - cursor.watch_index()];
                if other_watched_literal.eval(self.state.decision_tracker.map()) == Some(true) {
                    // Continue with the next clause in the linked list.
                    next_cursor = cursor.next();
                } else if let Some(literal) = watched_literals.next_unwatched_literal(
                    clause,
                    &self.state.learnt_clauses,
                    &self.state.requirement_to_sorted_candidates,
                    &self.state.disjunctions,
                    self.state.decision_tracker.map(),
                    watch_index,
                ) {
                    // Update the watch to point to the new literal
                    next_cursor = cursor.update(literal);
                } else {
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
            let clause = self.state.clauses.kinds[clause_id.to_usize()];
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
        clauses: &Vec<Clause>,
        learnt_why: &Mapping<LearntClauseId, Vec<ClauseId>>,
        clause_id: ClauseId,
        conflict: &mut Conflict,
        seen: &mut HashSet<ClauseId>,
    ) {
        let clause = &clauses[clause_id.to_usize()];
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
        self.state.clauses.kinds[clause_id.to_usize()].visit_literals(
            &self.state.learnt_clauses,
            &self.state.requirement_to_sorted_candidates,
            &self.state.disjunctions,
            |literal| {
                involved.insert(literal.variable());
            },
        );

        let mut seen = HashSet::default();
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

            self.state.clauses.kinds[why.to_usize()].visit_literals(
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

        let mut s_value;
        let mut learnt_why = Vec::new();
        let mut first_iteration = true;
        let clause_kinds = &self.state.clauses.kinds;
        loop {
            learnt_why.push(clause_id);

            clause_kinds[clause_id.to_usize()].visit_literals(
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
                        learnt.push(learnt_literal);
                        back_track_to = back_track_to.max(decision_level);
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

        let last_literal = Literal::new(conflicting_solvable, s_value);
        learnt.push(last_literal);

        // Increase the activity of the packages in the learned clause
        for literal in &learnt {
            let name_id = literal
                .variable()
                .as_solvable(&self.state.variable_map)
                .map(|s| self.provider().solvable_name(s));
            if let Some(name_id) = name_id {
                self.state.name_activity[name_id.to_usize()] += self.activity_add;
            }
        }

        // Add the clause
        let learnt_id = self.state.learnt_clauses.alloc(learnt.clone());
        self.state.learnt_why.insert(learnt_id, learnt_why);

        let (watched_literals, kind) = WatchedLiterals::learnt(learnt_id, &learnt);
        let clause_id = self.state.clauses.alloc(watched_literals, kind);
        self.state.learnt_clause_ids.push(clause_id);
        if let Some(watched_literals) =
            self.state.clauses.watched_literals[clause_id.to_usize()].as_mut()
        {
            self.state
                .watches
                .start_watching(watched_literals, clause_id);
        }

        tracing::debug!("│├ Learnt disjunction:",);
        for lit in learnt {
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
        for activity in &mut self.state.name_activity {
            *activity *= self.activity_decay;
        }
    }
}

impl SolverState {
    /// Returns the solvables that the solver has chosen to include in the
    /// solution so far.
    fn chosen_solvables(&self) -> impl Iterator<Item = SolvableId> + '_ {
        self.decision_tracker.stack().filter_map(|d| {
            if d.value {
                d.variable.as_solvable(&self.variable_map)
            } else {
                // Ignore things that are set to false
                None
            }
        })
    }
}
