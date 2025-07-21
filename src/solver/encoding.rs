use std::{any::Any, future::ready};

use futures::{
    FutureExt, StreamExt, TryFutureExt, future::LocalBoxFuture, stream::FuturesUnordered,
};
use indexmap::IndexMap;

use super::{SolverState, clause::WatchedLiterals, conditions};
use crate::{
    Candidates, ConditionId, ConditionalRequirement, Dependencies, DependencyProvider, NameId,
    SolvableId, SolverCache, StringId, VersionSetId,
    internal::{
        arena::ArenaId,
        id::{ClauseId, SolvableOrRootId, VariableId},
    },
    solver::{conditions::Disjunction, decision::Decision},
};

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
    state: &'a mut SolverState,
    cache: &'cache SolverCache<D>,
    level: u32,

    /// The dependencies of the root solvable.
    root_dependencies: &'cache Dependencies,

    /// The set of futures that are pending to be resolved.
    pending_futures:
        FuturesUnordered<LocalBoxFuture<'cache, Result<TaskResult<'cache>, Box<dyn Any>>>>,

    /// A list of clauses that were introduced that are conflicting with the
    /// current state.
    conflicting_clauses: Vec<ClauseId>,

    /// Stores for which packages and solvables we want to add forbid clauses.
    pending_forbid_clauses: IndexMap<NameId, Vec<VariableId>, ahash::RandomState>,

    /// A set of packages that should have an at-least-once tracker.
    new_at_least_one_packages: IndexMap<NameId, VariableId, ahash::RandomState>,
}

/// The result of a future that was queued for processing.
enum TaskResult<'a> {
    Dependencies(DependenciesAvailable<'a>),
    Candidates(CandidatesAvailable<'a>),
    RequirementCandidates(RequirementCandidatesAvailable<'a>),
    ConstraintCandidates(ConstraintCandidatesAvailable<'a>),
}

/// Result of requesting the dependencies for a certain solvable.
struct DependenciesAvailable<'a> {
    solvable_id: SolvableOrRootId,
    dependencies: &'a Dependencies,
}

/// Results of requesting the candidates for a certain package.
struct CandidatesAvailable<'a> {
    name_id: NameId,
    package_candidates: &'a Candidates,
}

/// Result of querying candidates for a particular requirement.
struct RequirementCandidatesAvailable<'a> {
    solvable_id: SolvableOrRootId,
    requirement: ConditionalRequirement,
    candidates: Vec<&'a [SolvableId]>,
    condition: Option<(ConditionId, Vec<Vec<DisjunctionComplement<'a>>>)>,
}

/// The complement of a solvables that match aVersionSet or an empty set.
enum DisjunctionComplement<'a> {
    Solvables(VersionSetId, &'a [SolvableId]),
    Empty(VersionSetId),
}

/// Result of querying candidates for a particular constraint.
struct ConstraintCandidatesAvailable<'a> {
    solvable_id: SolvableOrRootId,
    constraint: VersionSetId,
    candidates: &'a [SolvableId],
}

impl<'a, 'cache, D: DependencyProvider> Encoder<'a, 'cache, D> {
    pub fn new(
        state: &'a mut SolverState,
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
            level,
            new_at_least_one_packages: IndexMap::default(),
        }
    }

    /// Encode rules and variables for the given solvables.
    pub async fn encode(
        mut self,
        solvable_ids: impl IntoIterator<Item = SolvableOrRootId>,
    ) -> Result<Vec<ClauseId>, Box<dyn Any>> {
        // Queue the initial solvables for processing.
        for solvable_id in solvable_ids {
            self.queue_solvable(solvable_id);
        }

        // Process all pending futures until there are no more.
        while let Some(future_result) = self.pending_futures.next().await {
            self.on_task_result(future_result?);
        }

        self.add_pending_forbid_clauses();
        self.add_pending_at_least_one_clauses();

        Ok(self.conflicting_clauses)
    }

    /// Called when the result of a future is available.
    fn on_task_result(&mut self, result: TaskResult<'cache>) {
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
        }: DependenciesAvailable<'cache>,
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
            self.queue_conditional_requirement(solvable_id, requirement.clone());
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
        }: CandidatesAvailable<'cache>,
    ) {
        tracing::trace!(
            "Package candidates available for {}",
            self.cache.provider().display_name(name_id)
        );

        // Resize the activity vector if needed
        if self.state.name_activity.len() <= name_id.to_usize() {
            self.state.name_activity.resize(name_id.to_usize() + 1, 0.0);
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
        }: RequirementCandidatesAvailable<'cache>,
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
            self.pending_forbid_clauses
                .entry(name_id)
                .or_default()
                .push(variable_id);
        }

        // Queue requesting the dependencies of the candidates as well if they are
        // cheaply available from the dependency provider.
        for &candidate in candidates.iter().flat_map(|solvables| solvables.iter()) {
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
                            let pending_forbid_clauses =
                                self.pending_forbid_clauses.entry(name_id).or_default();
                            disjunction_literals.reserve(solvables.len());
                            pending_forbid_clauses.reserve(solvables.len());
                            for &solvable in solvables {
                                let variable = self.state.variable_map.intern_solvable(solvable);
                                disjunction_literals.push(variable.positive());
                                pending_forbid_clauses.push(variable);
                            }
                        }
                        DisjunctionComplement::Empty(version_set) => {
                            let name_id = self.cache.provider().version_set_name(version_set);
                            let at_least_one_of_var = match self
                                .state
                                .at_least_one_tracker
                                .get(&name_id)
                                .copied()
                                .or_else(|| self.new_at_least_one_packages.get(&name_id).copied())
                            {
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
            let clause_id = self.state.clauses.alloc(watched_literals, kind);

            let watched_literals =
                self.state.clauses.watched_literals[clause_id.to_usize()].as_mut();

            if let Some(watched_literals) = watched_literals {
                self.state
                    .watches
                    .start_watching(watched_literals, clause_id);
            }

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
        }: ConstraintCandidatesAvailable<'cache>,
    ) {
        tracing::trace!(
            "non matching candidates available for {} {}",
            self.cache
                .provider()
                .display_name(self.cache.provider().version_set_name(constraint)),
            self.cache.provider().display_version_set(constraint),
        );

        let variable = self.state.variable_map.intern_solvable_or_root(solvable_id);
        for &forbidden_candidate in candidates {
            let forbidden_candidate_var =
                self.state.variable_map.intern_solvable(forbidden_candidate);
            let (watched_literals, conflict, kind) = WatchedLiterals::constrains(
                variable,
                forbidden_candidate_var,
                constraint,
                &self.state.decision_tracker,
            );

            // Allocate the clause for the constraint
            let clause_id = self.state.clauses.alloc(watched_literals, kind);

            // Start watching the clause
            let watched_literals = self.state.clauses.watched_literals[clause_id.to_usize()]
                .as_mut()
                .expect("a forbid clause must always have watched literals");
            self.state
                .watches
                .start_watching(watched_literals, clause_id);

            // Mark conflicting clauses
            if conflict {
                self.conflicting_clauses.push(clause_id);
            }
        }
    }

    /// Adds clauses to forbid any other clauses than the locked solvable to be
    /// installed.
    fn add_locked_package_clauses(
        &mut self,
        locked_solvable_id: SolvableId,
        all_candidate_ids: &[SolvableId],
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
            let clause_id = self.state.clauses.alloc(watched_literals, kind);

            // Start watching the clause.
            let watched_literals = self.state.clauses.watched_literals[clause_id.to_usize()]
                .as_mut()
                .expect("a forbid clause must always have watched literals");
            self.state
                .watches
                .start_watching(watched_literals, clause_id);
        }
    }

    /// Adds a clause to exclude a particular solvable
    fn add_exclusion_clause(
        &mut self,
        solvable_id: SolvableOrRootId,
        reason: StringId,
    ) -> VariableId {
        let variable = self.state.variable_map.intern_solvable_or_root(solvable_id);

        // Allocate a clause for the exclusion
        let (watched_literals, kind) = WatchedLiterals::exclude(variable, reason);
        let clause_id = self.state.clauses.alloc(watched_literals, kind);

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
    fn queue_solvable(&mut self, solvable_id: SolvableOrRootId) {
        // Early out if the solvable has already been processed
        if !self.state.clauses_added_for_solvable.insert(solvable_id) {
            return;
        }

        // Construct a future that queries the dependencies for the solvable
        let cache = self.cache;
        let root_dependencies = self.root_dependencies;
        let query_dependencies = async move {
            let dependencies = match solvable_id.solvable() {
                None => root_dependencies,
                Some(solvable_id) => cache.get_or_cache_dependencies(solvable_id).await?,
            };
            Ok(TaskResult::Dependencies(DependenciesAvailable {
                solvable_id,
                dependencies,
            }))
        };

        // Queue the future for processing
        self.pending_futures.push(query_dependencies.boxed_local());
    }

    /// Enqueues retrieving all candidates for a particular package name.
    fn queue_package(&mut self, name_id: NameId) {
        // Early out if the package has already been processed
        if !self.state.clauses_added_for_package.insert(name_id) {
            return;
        }

        // Construct a future that queries the candidates for the package
        let cache = self.cache;
        let query_candidates = async move {
            let package_candidates = cache.get_or_cache_candidates(name_id).await?;
            Ok(TaskResult::Candidates(CandidatesAvailable {
                name_id,
                package_candidates,
            }))
        };

        // Queue the future for processing
        self.pending_futures.push(query_candidates.boxed_local());
    }

    /// Enqueues retrieving the candidates for a particular requirement. These
    /// candidates are already filtered and sorted.
    fn queue_conditional_requirement(
        &mut self,
        solvable_id: SolvableOrRootId,
        requirement: ConditionalRequirement,
    ) {
        let cache = self.cache;
        let query_requirements_candidates = async move {
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
        };

        self.pending_futures
            .push(query_requirements_candidates.boxed_local());
    }

    /// Enqueues retrieving the candidates for a particular constraint. These
    /// are the candidates that do *not* match the version set.
    fn queue_constraint(&mut self, solvable_id: SolvableOrRootId, constraint: VersionSetId) {
        let cache = self.cache;
        let query_constraints_candidates = async move {
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
        };

        self.pending_futures
            .push(query_constraints_candidates.boxed_local());
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
            let other_solvables = self.state.at_most_one_trackers.entry(name_id).or_default();
            let variable_is_new = other_solvables.add(
                candidate_var,
                |a, b, positive| {
                    let literal_b = if positive { b.positive() } else { b.negative() };
                    let literal_a = a.negative();
                    let (watched_literals, kind) =
                        WatchedLiterals::forbid_multiple(a, literal_b, name_id);
                    let clause_id = self.state.clauses.alloc(watched_literals, kind);
                    let watched_literals = self.state.clauses.watched_literals
                        [clause_id.to_usize()]
                    .as_mut()
                    .expect("forbid clause must have watched literals");
                    self.state
                        .watches
                        .start_watching(watched_literals, clause_id);

                    // Add a decision if a decision has already been made for one of the literals.
                    let set_literal = match (
                        literal_a.eval(self.state.decision_tracker.map()),
                        literal_b.eval(self.state.decision_tracker.map()),
                    ) {
                        (Some(false), None) => Some(literal_b),
                        (None, Some(false)) => Some(literal_a),
                        (Some(false), Some(false)) => unreachable!(
                            "both literals cannot be false as that would be a conflict"
                        ),
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

            if variable_is_new {
                if let Some(&at_least_one_variable) = self.state.at_least_one_tracker.get(&name_id)
                {
                    let (watched_literals, kind) =
                        WatchedLiterals::any_of(at_least_one_variable, candidate_var);
                    let clause_id = self.state.clauses.alloc(watched_literals, kind);
                    let watched_literals = self.state.clauses.watched_literals
                        [clause_id.to_usize()]
                    .as_mut()
                    .expect("forbid clause must have watched literals");
                    self.state
                        .watches
                        .start_watching(watched_literals, clause_id);
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
            let variables = self
                .state
                .at_most_one_trackers
                .get(&name_id)
                .map(|tracker| &tracker.variables);

            // Add clauses for the existing variables.
            for &helper_var in variables.into_iter().flatten() {
                let (watched_literals, kind) =
                    WatchedLiterals::any_of(at_least_one_variable, helper_var);
                let clause_id = self.state.clauses.alloc(watched_literals, kind);
                let watched_literals = self.state.clauses.watched_literals[clause_id.to_usize()]
                    .as_mut()
                    .expect("forbid clause must have watched literals");
                self.state
                    .watches
                    .start_watching(watched_literals, clause_id);

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
                .insert(name_id, at_least_one_variable);
        }
    }
}
