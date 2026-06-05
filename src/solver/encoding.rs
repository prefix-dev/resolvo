use std::{any::Any, collections::VecDeque, future::ready};

use super::{SolverState, clause::WatchedLiterals, conditions};
use crate::{
    Candidates, ConditionId, ConditionalRequirement, DenseIndex, Dependencies, DependencyProvider,
    SolverCache, StringId, VariableId, VersionSetId,
    internal::{id::ClauseId, solver_id::SolvableIdOrRoot},
    solver::{conditions::Disjunction, decision::Decision},
    solver_id::{IdMap, IdSet},
    utils::IndexedSet,
};
use futures::{
    FutureExt, StreamExt, TryFutureExt, future::LocalBoxFuture, stream::FuturesUnordered,
};
use indexmap::IndexMap;

type PendingTask<'cache, D> = LocalBoxFuture<'cache, Result<TaskResult<'cache, D>, Box<dyn Any>>>;

type RequirementCondition<'a, S> = Option<(ConditionId, Vec<Vec<DisjunctionComplement<'a, S>>>)>;

/// An object that is responsible for encoding information from the dependency
/// provider into rules and variables that are used by the solver.
///
/// This type allows concurrency in the dependency provider by concurrently
/// requesting information from the provider. This is achieved by recording all
/// futures in a [`FuturesUnordered`] and processing them as they become
/// available instead of waiting for individual futures to complete and
/// processing their response.
///
/// The encoder itself is completely single threaded (and not `Send`) but the
/// dependency provider is free to spawn tasks on other threads.
pub(crate) struct Encoder<'a, 'cache, D: DependencyProvider> {
    state: &'a mut SolverState<D>,
    cache: &'cache SolverCache<D>,
    level: u32,

    /// The dependencies of the root solvable.
    root_dependencies: &'cache Dependencies,

    /// The set of futures that are pending to be resolved.
    pending_futures: FuturesUnordered<PendingTask<'cache, D>>,

    /// A list of clauses that were introduced that are conflicting with the
    /// current state.
    conflicting_clauses: Vec<ClauseId>,

    /// Stores for which packages and solvables we want to add forbid clauses.
    pending_forbid_clauses: IndexMap<D::NameId, Vec<VariableId>, ahash::RandomState>,

    /// Tracks which variables have already been added to
    /// `pending_forbid_clauses` to avoid accumulating millions of duplicate
    /// entries. A variable belongs to exactly one package, so deduplicating
    /// globally is safe.
    forbid_seen: IndexedSet<VariableId>,

    /// A set of packages that should have an at-least-once tracker.
    new_at_least_one_packages: IndexMap<D::NameId, VariableId, ahash::RandomState>,

    /// Results from futures that completed immediately during
    /// `try_immediate_or_queue`.
    pending_results: VecDeque<Result<TaskResult<'cache, D>, Box<dyn Any>>>,
}

/// The result of a future that was queued for processing.
enum TaskResult<'a, D: DependencyProvider> {
    Dependencies(DependenciesAvailable<'a, D::SolvableId>),
    Candidates(CandidatesAvailable<'a, D>),
    RequirementCandidates(RequirementCandidatesAvailable<'a, D>),
    ConstraintCandidates(ConstraintCandidatesAvailable<'a, D::SolvableId>),
}

/// Result of requesting the dependencies for a certain solvable.
struct DependenciesAvailable<'a, S> {
    solvable_id: SolvableIdOrRoot<S>,
    dependencies: &'a Dependencies,
}

/// Results of requesting the candidates for a certain package.
struct CandidatesAvailable<'a, D: DependencyProvider> {
    name_id: D::NameId,
    package_candidates: &'a Candidates<D::SolvableId>,
}

/// Result of querying candidates for a particular requirement.
struct RequirementCandidatesAvailable<'a, D: DependencyProvider> {
    solvable_id: SolvableIdOrRoot<D::SolvableId>,
    requirement: ConditionalRequirement,
    candidates: Vec<&'a [D::SolvableId]>,
    condition: RequirementCondition<'a, D::SolvableId>,
}

/// The complement of a solvables that match aVersionSet or an empty set.
enum DisjunctionComplement<'a, S> {
    Solvables(VersionSetId, &'a [S]),
    Empty(VersionSetId),
}

/// Result of querying candidates for a particular constraint.
struct ConstraintCandidatesAvailable<'a, S> {
    solvable_id: SolvableIdOrRoot<S>,
    constraint: VersionSetId,
    candidates: &'a [S],
}

/// The minimum number of non-matching candidates a constraint must have before
/// the shared auxiliary variable encoding is used (see
/// [`Encoder::on_constraint_candidates_available`]). Below this, pairwise
/// clauses need at most as many clauses and propagate in a single hop.
const CONSTRAINS_AUX_ENCODING_THRESHOLD: usize = 4;

impl<'a, 'cache, D: DependencyProvider> Encoder<'a, 'cache, D> {
    pub fn new(
        state: &'a mut SolverState<D>,
        cache: &'cache SolverCache<D>,
        root_dependencies: &'cache Dependencies,
        level: u32,
    ) -> Self {
        Self {
            state,
            cache,
            root_dependencies,
            pending_futures: FuturesUnordered::new(),
            conflicting_clauses: Vec::new(),
            pending_forbid_clauses: IndexMap::default(),
            forbid_seen: IndexedSet::default(),
            level,
            new_at_least_one_packages: IndexMap::default(),
            pending_results: VecDeque::new(),
        }
    }

    /// Poll `future` once on the stack. If it resolves immediately (as all
    /// futures do under [`NowOrNeverRuntime`]), record the result for
    /// iterative processing; otherwise hand the boxed future off to
    /// [`Self::pending_futures`] for later polling.
    ///
    /// We still box the future, so the allocation cost is the same. The
    /// win over pushing straight to `FuturesUnordered` is avoiding its slab
    /// and waker bookkeeping.
    fn queue_future<F>(&mut self, future: F)
    where
        F: std::future::Future<Output = Result<TaskResult<'cache, D>, Box<dyn Any>>> + 'cache,
    {
        let mut boxed = future.boxed_local();
        match boxed.as_mut().now_or_never() {
            Some(result) => self.pending_results.push_back(result),
            None => {
                // Future is still pending. Hand the boxed future to
                // `pending_futures` so it can be polled asynchronously.
                self.pending_futures.push(boxed);
            }
        }
    }

    /// Encode rules and variables for the given solvables.
    pub async fn encode(
        mut self,
        solvable_ids: impl IntoIterator<Item = SolvableIdOrRoot<D::SolvableId>>,
    ) -> Result<Vec<ClauseId>, Box<dyn Any>> {
        // Queue the initial solvables for processing.
        for solvable_id in solvable_ids {
            self.queue_solvable(solvable_id);
        }

        // Process pending work until none remains. Immediately completed
        // futures are drained iteratively rather than recursing through
        // on_task_result -> queue_* -> on_task_result. Each loop iteration
        // drains synchronously-ready results first, then awaits the next
        // truly-async future, so the trailing drain on stream exhaustion
        // happens naturally on the next iteration.
        loop {
            while let Some(result) = self.pending_results.pop_front() {
                self.on_task_result(result?);
            }
            let Some(future_result) = self.pending_futures.next().await else {
                break;
            };
            self.on_task_result(future_result?);
        }

        self.add_pending_forbid_clauses();
        self.add_pending_at_least_one_clauses();

        Ok(self.conflicting_clauses)
    }

    /// Called when the result of a future is available.
    fn on_task_result(&mut self, result: TaskResult<'cache, D>) {
        match result {
            TaskResult::Dependencies(dependencies) => self.on_dependencies_available(dependencies),
            TaskResult::Candidates(candidates) => self.on_candidates_available(candidates),
            TaskResult::RequirementCandidates(candidates) => {
                self.on_requirement_candidates_available(candidates)
            }
            TaskResult::ConstraintCandidates(candidates) => {
                self.on_constraint_candidates_available(candidates)
            }
        }
    }

    /// Called when the dependencies of a solvable are available.
    ///
    /// Iterates over all the requirements and constraints and queues querying
    ///
    /// * the candidates for any new package that was encountered,
    /// * the matching candidates for each requirement,
    /// * the non-matching candidates for each constraint.
    fn on_dependencies_available(
        &mut self,
        DependenciesAvailable {
            solvable_id,
            dependencies,
        }: DependenciesAvailable<'cache, D::SolvableId>,
    ) {
        tracing::trace!(
            "dependencies available for {}",
            solvable_id.display(self.cache.provider()),
        );

        // Extract the dependencies and constraints from the result.
        let (requirements, constraints) = match dependencies {
            Dependencies::Known(deps) => (&deps.requirements, &deps.constrains),
            Dependencies::Unknown(reason) => {
                // If the dependencies are unknown, we add an exclusion clause and stop
                // processing.
                self.add_exclusion_clause(solvable_id, *reason);
                return;
            }
        };

        // Iterate over all requirements and find out to which packages they
        // refer. Make sure we have all candidates for a particular package.
        for version_set_id in requirements
            .iter()
            .flat_map(|requirement| requirement.requirement.version_sets(self.cache.provider()))
            .chain(constraints.iter().copied())
        {
            let package_name = self.cache.provider().version_set_name(version_set_id);
            self.queue_package(package_name);
        }

        // For each requirement request the matching candidates.
        for requirement in requirements {
            self.queue_conditional_requirement(solvable_id, *requirement);
        }

        // For each constraint, request the candidates that are non-matching
        // the version spec.
        for &constraint in constraints {
            self.queue_constraint(solvable_id, constraint);
        }
    }

    /// Called when all the solvable candidates for a package are available.
    fn on_candidates_available(
        &mut self,
        CandidatesAvailable {
            name_id,
            package_candidates,
        }: CandidatesAvailable<'cache, D>,
    ) {
        tracing::trace!(
            "Package candidates available for {}",
            self.cache.provider().display_name(name_id)
        );

        if package_candidates.allow_multiple {
            self.state.allow_multiple_names.insert(name_id);
        }

        // If there is a locked solvable, forbid all other candidates
        if let Some(locked_solvable_id) = package_candidates.locked {
            self.add_locked_package_clauses(locked_solvable_id, &package_candidates.candidates);
        }

        // Add clauses for externally excluded candidates.
        for &(solvable, reason) in &package_candidates.excluded {
            let variable = self.add_exclusion_clause(solvable.into(), reason);
            debug_assert!(
                self.state.decision_tracker.assigned_value(variable) != Some(true),
                "it cannot be possible that the excluded candidate is already uninstallable"
            )
        }
    }

    /// Called when the candidates for a particular requirement are available.
    fn on_requirement_candidates_available(
        &mut self,
        RequirementCandidatesAvailable {
            solvable_id,
            requirement,
            candidates,
            condition,
        }: RequirementCandidatesAvailable<'cache, D>,
    ) {
        tracing::trace!(
            "Sorted candidates available for {}",
            requirement.requirement.display(self.cache.provider()),
        );

        let variable = self.state.variable_map.intern_solvable_or_root(solvable_id);

        // Get the variables associated with the individual candidates.
        let version_set_variables = candidates
            .iter()
            .map(|&candidates| {
                candidates
                    .iter()
                    .map(|&var| self.state.variable_map.intern_solvable(var))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();

        // Make sure that for every candidate that we require we also have a forbid
        // clause to force one solvable per package name.
        //
        // We only add these clauses for packages that can actually be selected to
        // reduce the overall number of clauses.
        for (solvable, variable_id) in candidates
            .iter()
            .zip(version_set_variables.iter())
            .flat_map(|(&candidates, variable)| {
                candidates.iter().copied().zip(variable.iter().copied())
            })
        {
            let name_id = self.cache.provider().solvable_name(solvable);
            self.register_forbid_target(name_id, variable_id);
        }

        // Queue requesting the dependencies of the candidates as well if they are
        // cheaply available from the dependency provider.
        for &candidate in candidates.iter().flat_map(|solvables| solvables.iter()) {
            // Pre-check before `queue_solvable` does the same: skips the
            // `are_dependencies_available_for` query and the async closure
            // setup on the hot duplicate path.
            if self
                .state
                .clauses_added_for_solvable
                .contains(SolvableIdOrRoot::from(candidate))
            {
                continue;
            }
            // If the dependencies are already available for the
            // candidate, queue the candidate for processing.
            if self.cache.are_dependencies_available_for(candidate) {
                self.queue_solvable(candidate.into())
            }
        }

        // Determine the disjunctions of all the conditions for this requirement.
        let mut conditions = Vec::with_capacity(condition.as_ref().map_or(0, |(_, dnf)| dnf.len()));
        if let Some((condition, dnf)) = condition {
            for disjunctions in dnf {
                let mut disjunction_literals = Vec::new();
                for disjunction_complement in disjunctions {
                    match disjunction_complement {
                        DisjunctionComplement::Solvables(version_set, solvables) => {
                            let name_id = self.cache.provider().version_set_name(version_set);
                            disjunction_literals.reserve(solvables.len());
                            for &solvable in solvables {
                                let variable = self.state.variable_map.intern_solvable(solvable);
                                disjunction_literals.push(variable.positive());
                                self.register_forbid_target(name_id, variable);
                            }
                        }
                        DisjunctionComplement::Empty(version_set) => {
                            let name_id = self.cache.provider().version_set_name(version_set);
                            let at_least_one_of_var =
                                match self.state.at_least_one_tracker.get(name_id).or_else(|| {
                                    self.new_at_least_one_packages.get(&name_id).copied()
                                }) {
                                    Some(variable) => variable,
                                    None => {
                                        let variable = self
                                            .state
                                            .variable_map
                                            .alloc_at_least_one_variable(name_id);
                                        self.new_at_least_one_packages.insert(name_id, variable);
                                        variable
                                    }
                                };
                            disjunction_literals.push(at_least_one_of_var.negative());
                        }
                    }
                }

                let disjunction_id = self.state.disjunctions.alloc(Disjunction {
                    literals: disjunction_literals,
                    _condition: condition,
                });
                conditions.push(Some(disjunction_id));
            }
        } else {
            conditions.push(None);
        }

        for condition in conditions {
            // Add the requirements clause
            let no_candidates = candidates.iter().all(|candidates| candidates.is_empty());
            let condition_literals =
                condition.map(|id| self.state.disjunctions[id].literals.as_slice());
            let (watched_literals, conflict, kind) = WatchedLiterals::requires(
                variable,
                requirement.requirement,
                version_set_variables.iter().flatten().copied(),
                condition.zip(condition_literals),
                &self.state.decision_tracker,
            );
            let clause_id = self.state.add_clause(watched_literals, kind);

            self.state
                .requires_clauses
                .entry(variable)
                .or_default()
                .push((requirement.requirement, condition, clause_id));

            if conflict {
                self.conflicting_clauses.push(clause_id);
            } else if no_candidates && condition.is_none() {
                // Add assertions for unit clauses (i.e. those with no matching candidates)
                self.state.negative_assertions.push((variable, clause_id));
            }
        }

        // Store resolved variables for later
        self.state
            .requirement_to_sorted_candidates
            .insert(requirement.requirement, version_set_variables);
    }

    /// Called when the candidates for a particular constraint are available.
    fn on_constraint_candidates_available(
        &mut self,
        ConstraintCandidatesAvailable {
            solvable_id,
            constraint,
            candidates,
        }: ConstraintCandidatesAvailable<'cache, D::SolvableId>,
    ) {
        tracing::trace!(
            "non matching candidates available for {} {}",
            self.cache
                .provider()
                .display_name(self.cache.provider().version_set_name(constraint)),
            self.cache.provider().display_version_set(constraint),
        );

        let variable = self.state.variable_map.intern_solvable_or_root(solvable_id);

        if candidates.len() < CONSTRAINS_AUX_ENCODING_THRESHOLD {
            // Pairwise encoding: one (¬parent ∨ ¬candidate) clause per
            // excluded candidate.
            for &forbidden_candidate in candidates {
                let forbidden_candidate_var =
                    self.state.variable_map.intern_solvable(forbidden_candidate);
                let (watched_literals, conflict, kind) = WatchedLiterals::constrains(
                    variable,
                    forbidden_candidate_var,
                    constraint,
                    &self.state.decision_tracker,
                );

                let clause_id = self.state.add_clause(watched_literals, kind);

                if conflict {
                    self.conflicting_clauses.push(clause_id);
                }
            }
            return;
        }

        // Shared encoding: the (¬candidate ∨ aux) clauses are emitted once per
        // version set, each parent only adds a single (¬parent ∨ ¬aux) clause.
        let aux_variable = match self.state.constrains_aux_vars.get(&constraint) {
            Some(&aux_variable) => aux_variable,
            None => {
                let aux_variable = self
                    .state
                    .variable_map
                    .alloc_constrains_violation_variable(constraint);
                self.state
                    .constrains_aux_vars
                    .insert(constraint, aux_variable);

                for &forbidden_candidate in candidates {
                    let forbidden_candidate_var =
                        self.state.variable_map.intern_solvable(forbidden_candidate);
                    let (watched_literals, kind) = WatchedLiterals::constrains_excluded(
                        forbidden_candidate_var,
                        aux_variable,
                        constraint,
                    );
                    let clause_id = self.state.add_clause(watched_literals, kind);

                    // An already installed candidate must propagate
                    // immediately so the parent clause below observes the
                    // violation, just like the pairwise encoding does.
                    if self
                        .state
                        .decision_tracker
                        .assigned_value(forbidden_candidate_var)
                        == Some(true)
                    {
                        self.state
                            .decision_tracker
                            .try_add_decision(
                                Decision::new(aux_variable, true, clause_id),
                                self.level,
                            )
                            .expect("a freshly allocated variable cannot be assigned false");
                    }
                }

                aux_variable
            }
        };

        let (watched_literals, conflict, kind) = WatchedLiterals::constrains_parent(
            variable,
            aux_variable,
            constraint,
            &self.state.decision_tracker,
        );
        let clause_id = self.state.add_clause(watched_literals, kind);
        if conflict {
            self.conflicting_clauses.push(clause_id);
        }
    }

    /// Adds clauses to forbid any other clauses than the locked solvable to be
    /// installed.
    fn add_locked_package_clauses(
        &mut self,
        locked_solvable_id: D::SolvableId,
        all_candidate_ids: &[D::SolvableId],
    ) {
        let locked_solvable_var = self.state.variable_map.intern_solvable(locked_solvable_id);
        for &other_candidate in all_candidate_ids {
            if other_candidate == locked_solvable_id {
                // Don't add a clause for the locked solvable itself
                continue;
            }
            let other_candidate_var = self.state.variable_map.intern_solvable(other_candidate);

            // Allocated the clause for the exclusion
            let (watched_literals, kind) =
                WatchedLiterals::lock(locked_solvable_var, other_candidate_var);
            self.state.add_clause(watched_literals, kind);
        }
    }

    /// Adds a clause to exclude a particular solvable
    fn add_exclusion_clause(
        &mut self,
        solvable_id: SolvableIdOrRoot<D::SolvableId>,
        reason: StringId,
    ) -> VariableId {
        let variable = self.state.variable_map.intern_solvable_or_root(solvable_id);

        // Allocate a clause for the exclusion
        let (watched_literals, kind) = WatchedLiterals::exclude(variable, reason);
        let clause_id = self.state.add_clause(watched_literals, kind);

        // Exclusions are negative assertions, tracked outside the watcher
        self.state.negative_assertions.push((variable, clause_id));

        // If the clause is already conflicting, e.g. we already decided that this
        // solvable must be installed, we add it to the list for later processing
        if self.state.decision_tracker.assigned_value(variable) == Some(true) {
            self.conflicting_clauses.push(clause_id)
        }

        variable
    }

    /// Enqueues retrieving the dependencies for a solvable.
    ///
    /// This method requests the dependencies for the given solvable in an
    /// async fashion and does not process the result itself. Instead, the
    /// future is queued for processing. When the future returns its result is
    /// processed by the [`Self::on_dependencies_available`] function.
    fn queue_solvable(&mut self, solvable_id: SolvableIdOrRoot<D::SolvableId>) {
        // Early out if the solvable has already been processed
        if !self.state.clauses_added_for_solvable.insert(solvable_id) {
            return;
        }

        let cache = self.cache;
        let root_dependencies = self.root_dependencies;
        self.queue_future(async move {
            let dependencies = match solvable_id.solvable() {
                None => root_dependencies,
                Some(solvable_id) => cache.get_or_cache_dependencies(solvable_id).await?,
            };
            Ok(TaskResult::Dependencies(DependenciesAvailable {
                solvable_id,
                dependencies,
            }))
        });
    }

    /// Enqueues retrieving all candidates for a particular package name.
    fn queue_package(&mut self, name_id: D::NameId) {
        // Early out if the package has already been processed
        if !self.state.clauses_added_for_package.insert(name_id) {
            return;
        }

        let cache = self.cache;
        self.queue_future(async move {
            let package_candidates = cache.get_or_cache_candidates(name_id).await?;
            Ok(TaskResult::Candidates(CandidatesAvailable {
                name_id,
                package_candidates,
            }))
        });
    }

    /// Enqueues retrieving the candidates for a particular requirement. These
    /// candidates are already filtered and sorted.
    fn queue_conditional_requirement(
        &mut self,
        solvable_id: SolvableIdOrRoot<D::SolvableId>,
        requirement: ConditionalRequirement,
    ) {
        let cache = self.cache;
        self.queue_future(async move {
            let candidates = futures::future::try_join_all(
                requirement
                    .requirement
                    .version_sets(cache.provider())
                    .map(|version_set| {
                        cache.get_or_cache_sorted_candidates_for_version_set(version_set)
                    }),
            );

            let condition_candidates = match requirement.condition {
                Some(condition) => futures::future::try_join_all(
                    conditions::convert_conditions_to_dnf(condition, cache.provider())
                        .into_iter()
                        .map(|cnf| {
                            futures::future::try_join_all(cnf.into_iter().map(|version_set| {
                                cache
                                    .get_or_cache_non_matching_candidates(version_set)
                                    .map_ok(move |matching_candidates| {
                                        if matching_candidates.is_empty() {
                                            DisjunctionComplement::Empty(version_set)
                                        } else {
                                            DisjunctionComplement::Solvables(
                                                version_set,
                                                matching_candidates,
                                            )
                                        }
                                    })
                            }))
                        }),
                )
                .map_ok(move |dnf| Some((condition, dnf)))
                .left_future(),
                None => ready(Ok(None)).right_future(),
            };

            let (candidates, condition) = futures::try_join!(candidates, condition_candidates)?;

            Ok(TaskResult::RequirementCandidates(
                RequirementCandidatesAvailable {
                    solvable_id,
                    requirement,
                    candidates,
                    condition,
                },
            ))
        });
    }

    /// Enqueues retrieving the candidates for a particular constraint. These
    /// are the candidates that do *not* match the version set.
    fn queue_constraint(
        &mut self,
        solvable_id: SolvableIdOrRoot<D::SolvableId>,
        constraint: VersionSetId,
    ) {
        let cache = self.cache;
        self.queue_future(async move {
            let non_matching_candidates = cache
                .get_or_cache_non_matching_candidates(constraint)
                .await?;
            Ok(TaskResult::ConstraintCandidates(
                ConstraintCandidatesAvailable {
                    solvable_id,
                    constraint,
                    candidates: non_matching_candidates,
                },
            ))
        });
    }

    /// Record `variable` as a candidate for a forbid-multiple clause under
    /// `name_id`. Returns silently if the variable has already been registered;
    /// see [`Self::forbid_seen`] for why globally-deduplicating is safe.
    /// Also skips registration for packages that allow multiple versions.
    fn register_forbid_target(&mut self, name_id: D::NameId, variable: VariableId) {
        if self.state.allow_multiple_names.contains(name_id) {
            return;
        }
        if self.forbid_seen.insert(variable) {
            self.pending_forbid_clauses
                .entry(name_id)
                .or_default()
                .push(variable);
        }
    }

    /// Add forbid clauses for solvables that we discovered as reachable from a
    /// requires clause.
    ///
    /// The number of forbid clauses for a package is O(n log n) so we only add
    /// clauses for the packages that are reachable from a requirement as an
    /// optimization.
    fn add_pending_forbid_clauses(&mut self) {
        for (name_id, candidate_var) in
            self.pending_forbid_clauses
                .drain(..)
                .flat_map(|(name_id, candidate_vars)| {
                    candidate_vars
                        .into_iter()
                        .map(move |candidate_var| (name_id, candidate_var))
                })
        {
            // Add forbid constraints for this solvable on all other
            // solvables that have been visited already for the same
            // version set name.
            let mut other_solvables = self
                .state
                .at_most_one_trackers
                .remove(&name_id)
                .unwrap_or_default();
            let variable_is_new = other_solvables.add(
                candidate_var,
                |a, b, positive| {
                    let literal_b = if positive { b.positive() } else { b.negative() };
                    let literal_a = a.negative();
                    let (watched_literals, kind) =
                        WatchedLiterals::forbid_multiple(a, literal_b, name_id);
                    // Inlined `add_clause`: `other_solvables` (above) holds a
                    // mutable borrow of `at_most_one_trackers`, so we cannot
                    // call `self.state.add_clause(..)` here.
                    let clause_id = self.state.clauses.alloc(watched_literals, kind);
                    if let Some(wl) =
                        self.state.clauses.watched_literals[clause_id.to_index()].as_mut()
                    {
                        self.state.watches.start_watching(wl, clause_id);
                    }

                    // Add a decision if a decision has already been made for one of the literals.
                    let set_literal = match (
                        literal_a.eval(self.state.decision_tracker.map()),
                        literal_b.eval(self.state.decision_tracker.map()),
                    ) {
                        (Some(false), None) => Some(literal_b),
                        (None, Some(false)) => Some(literal_a),
                        (Some(false), Some(false)) => {
                            // Both solvables are already decided true, but the
                            // forbid clause that would have prevented this didn't
                            // exist yet (it's being created right now). Report it
                            // as a conflict so the solver can backtrack.
                            self.conflicting_clauses.push(clause_id);
                            return;
                        }
                        _ => None,
                    };
                    if let Some(literal) = set_literal {
                        self.state
                            .decision_tracker
                            .try_add_decision(
                                Decision::new(
                                    literal.variable(),
                                    literal.satisfying_value(),
                                    clause_id,
                                ),
                                self.level,
                            )
                            .expect("we checked that there is no value yet");
                    }
                },
                || {
                    self.state
                        .variable_map
                        .alloc_forbid_multiple_variable(name_id)
                },
            );
            self.state
                .at_most_one_trackers
                .insert(name_id, other_solvables);

            if variable_is_new {
                if let Some(at_least_one_variable) = self.state.at_least_one_tracker.get(name_id) {
                    let (watched_literals, kind) =
                        WatchedLiterals::any_of(at_least_one_variable, candidate_var);
                    self.state.add_clause(watched_literals, kind);
                }
            }
        }
    }

    /// Adds clauses to track if at least one solvable for a particular package
    /// is selected. An auxiliary variable is introduced and for each solvable a
    /// clause is added that forces the auxiliary variable to turn true if any
    /// solvable is selected.
    ///
    /// This function only looks at solvables that are added to the at most once
    /// tracker. The encoder has an optimization that it only creates clauses
    /// for packages that are references from a requires clause. Any other
    /// solvable will never be selected anyway so we can completely ignore it.
    ///
    /// No clause is added to force the auxiliary variable to turn false. This
    /// is on purpose because we dont not need this state to compute a proper
    /// solution.
    ///
    /// See [`super::conditions`] for more information about conditions.
    fn add_pending_at_least_one_clauses(&mut self) {
        for (name_id, at_least_one_variable) in self.new_at_least_one_packages.drain(..) {
            // Find the at-most-one tracker for the package. We want to reuse the same
            // variables.
            // Collect variable IDs to avoid borrowing at_most_one_trackers
            // across the mutable add_clause call.
            let variables: Vec<_> = self
                .state
                .at_most_one_trackers
                .get(&name_id)
                .map(|tracker| tracker.variables.iter().copied().collect())
                .unwrap_or_default();

            // Add clauses for the existing variables.
            for helper_var in variables {
                let (watched_literals, kind) =
                    WatchedLiterals::any_of(at_least_one_variable, helper_var);
                let clause_id = self.state.add_clause(watched_literals, kind);

                // Assign true if any of the variables is true.
                if self.state.decision_tracker.assigned_value(helper_var) == Some(true) {
                    self.state
                        .decision_tracker
                        .try_add_decision(
                            Decision::new(at_least_one_variable, true, clause_id),
                            self.level,
                        )
                        .expect("the at least one variable must be undecided");
                }
            }

            // Record that we have a variable for this package.
            self.state
                .at_least_one_tracker
                .set(name_id, Some(at_least_one_variable));
        }
    }
}
