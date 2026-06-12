use std::{
    fmt::{Debug, Display, Formatter},
    iter,
    num::NonZeroU32,
    ops::ControlFlow,
};

use crate::requirement::RequirementMap;
use crate::solver::conditions::Disjunction;
use crate::{
    DenseIndex, Interner, Requirement, SolverId, StringId, VariableId, VersionSetId,
    internal::{
        arena::Arena,
        id::{ClauseId, LearntClauseId},
    },
    solver::{
        conditions::DisjunctionId, decision_map::DecisionMap, decision_tracker::DecisionTracker,
        variable_map::VariableMap,
    },
};

/// Represents a single clause in the SAT problem
///
/// # SAT terminology
///
/// Clauses consist of disjunctions of literals (i.e. a non-empty list of
/// variables, potentially negated, joined by the logical "or" operator). Here
/// are some examples:
///
/// - (¬A ∨ ¬B)
/// - (¬A ∨ ¬B ∨ ¬C ∨ ¬D)
/// - (¬A ∨ B ∨ C)
/// - (root)
///
/// For additional clarity: if `(¬A ∨ ¬B)` is a clause, `¬A` and `¬B` are its
/// literals, and `A` and `B` are variables. In our implementation, variables
/// are represented by [`VariableId`], and assignments are tracked in
/// the [`DecisionMap`].
///
/// The solver will attempt to assign values to the variables involved in the
/// problem in such a way that all clauses become true. If that turns out to be
/// impossible, the problem is unsatisfiable.
///
/// Since we are not interested in general-purpose SAT solving, but are
/// targeting the specific use-case of dependency resolution, we only support a
/// limited set of clauses. There are thousands of clauses for a particular
/// dependency resolution problem, and we try to keep the [`Clause`] enum small.
/// A naive implementation would store a `Vec<Literal>`.
#[derive(Copy, Clone, Debug)]
pub(crate) enum Clause<N> {
    /// An assertion that the root solvable must be installed
    ///
    /// In SAT terms: (root)
    InstallRoot,
    /// Makes the solvable require the candidates associated with the
    /// [`Requirement`].
    ///
    /// Optionally the requirement can be associated with a condition in the
    /// form of a disjunction.
    ///
    /// In SAT terms: (¬A ∨ ¬D1 v ¬D2 .. v ¬D99 v B1 ∨ B2 ∨ ... ∨ B99), where D1
    /// to D99 represent the candidates of the disjunction and B1 to B99
    /// represent the possible candidates for the provided [`Requirement`].
    Requires(VariableId, Option<DisjunctionId>, Requirement),
    /// Ensures only a single version of a package is installed
    ///
    /// Usage: generate one [`Clause::ForbidMultipleInstances`] clause for each
    /// possible combination of packages under the same name. The clause
    /// itself forbids two solvables from being installed at the same time.
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    ForbidMultipleInstances(VariableId, Literal, N),
    /// Forbids packages that do not satisfy a solvable's constrains
    ///
    /// Usage: for each constrains relationship in a package, determine all the
    /// candidates that do _not_ satisfy it, and create one
    /// [`Clause::Constrains`]. The clause itself forbids two solvables from
    /// being installed at the same time, just as
    /// [`Clause::ForbidMultipleInstances`], but it pays off to have a
    /// separate variant for user-friendly error messages.
    ///
    /// In SAT terms: (¬A ∨ ¬B)
    Constrains(VariableId, VariableId, VersionSetId),
    /// Makes the constraint's auxiliary variable turn true when a candidate
    /// that is excluded by the constraint's version set is installed.
    ///
    /// Usage: constraints whose version set excludes many candidates share a
    /// single auxiliary variable per version set. The clauses that link the
    /// excluded candidates to the auxiliary variable are emitted once per
    /// version set, and each (parent, version set) pair only adds a single
    /// [`Clause::ConstrainsParent`] clause. Together these encode the same
    /// restriction as [`Clause::Constrains`] with O(candidates + parents)
    /// instead of O(candidates * parents) clauses.
    ///
    /// Only this implication direction is needed (the Plaisted-Greenbaum
    /// one-sided form): the auxiliary variable is never decided directly, it
    /// only receives a value through propagation.
    ///
    /// In SAT terms: (¬candidate ∨ aux)
    ConstrainsExcluded(VariableId, VariableId, VersionSetId),
    /// Forbids a parent solvable from being installed together with the
    /// constraint's auxiliary variable, i.e. together with any candidate that
    /// is excluded by the constraint's version set. See
    /// [`Clause::ConstrainsExcluded`] for an overview of the encoding.
    ///
    /// In SAT terms: (¬parent ∨ ¬aux)
    ConstrainsParent(VariableId, VariableId, VersionSetId),
    /// Forbids the package on the right-hand side
    ///
    /// Note that the package on the left-hand side is not part of the clause,
    /// but just context to know which exact package was locked (necessary
    /// for user-friendly error messages)
    ///
    /// In SAT terms: (¬root ∨ ¬B). Note that we could encode this as an
    /// assertion (¬B), but that would require additional logic in the
    /// solver.
    Lock(VariableId, VariableId),
    /// A clause learnt during solving
    ///
    /// The learnt clause id can be used to retrieve the clause's literals,
    /// which are stored elsewhere to prevent the size of [`Clause`] from
    /// blowing up
    Learnt(LearntClauseId),

    /// A clause that forbids a package from being installed for an external
    /// reason.
    Excluded(VariableId, StringId),

    /// A clause that indicates that any version of a package C is selected.
    /// In SAT terms: (C_selected v ¬Cj)
    AnyOf(VariableId, VariableId),
}

impl<N> Clause<N> {
    /// Returns `true` if the clause has exactly two literals that can never
    /// change. The propagation loop relies on this to skip the
    /// `next_unwatched_literal` scan, which can never succeed for such
    /// clauses.
    #[inline]
    pub fn is_binary(&self) -> bool {
        matches!(
            self,
            Clause::Constrains(..)
                | Clause::ConstrainsExcluded(..)
                | Clause::ConstrainsParent(..)
                | Clause::ForbidMultipleInstances(..)
                | Clause::Lock(..)
                | Clause::AnyOf(..)
        )
    }
}

impl<N: SolverId> Clause<N> {
    /// Returns the building blocks needed for a new [WatchedLiterals] of the
    /// [Clause::Requires] kind.
    ///
    /// These building blocks are:
    ///
    /// - The [Clause] itself;
    /// - The ids of the solvables that will be watched (unless there are no
    ///   candidates, i.e. the clause is actually an assertion);
    /// - A boolean indicating whether the clause conflicts with existing
    ///   decisions. This should always be false when adding clauses before
    ///   starting the solving process, but can be true for clauses that are
    ///   added dynamically.
    fn requires(
        parent: VariableId,
        requirement: Requirement,
        candidates: impl IntoIterator<Item = VariableId>,
        condition: Option<(DisjunctionId, &[Literal])>,
        decision_tracker: &DecisionTracker,
    ) -> (Self, Option<[Literal; 2]>, bool) {
        // On the lazy-conditional path the parent may already have been
        // propagated false by the time this clause is built (e.g. a deferred
        // requirement whose condition fires after the parent was forbidden).
        // The clause is currently satisfied by `¬parent`, but that assignment
        // can be backtracked later, so the clause must still be added.
        let parent_is_false = decision_tracker.assigned_value(parent) == Some(false);

        let kind = Clause::Requires(parent, condition.map(|d| d.0), requirement);

        // Construct literals to watch
        let condition_literals = condition
            .into_iter()
            .flat_map(|(_, candidates)| candidates)
            .copied()
            .peekable();
        let candidate_literals = candidates
            .into_iter()
            .map(|candidate| candidate.positive())
            .peekable();

        let mut literals = condition_literals.chain(candidate_literals).peekable();
        let Some(&first_literal) = literals.peek() else {
            // If there are no candidates and there is no condition, then this clause is an
            // assertion. An assertion never conflicts: it either re-asserts an already
            // false parent or will assign the parent false during propagation.
            return (kind, None, false);
        };

        match literals.find(|&c| c.eval(decision_tracker.map()) != Some(false)) {
            // Watch any candidate that is not assigned to false
            Some(watched_candidate) => (kind, Some([parent.negative(), watched_candidate]), false),

            // All candidates are assigned to false! Unless the parent is false as well
            // (which satisfies the clause), the clause conflicts with the current
            // decisions. There are no valid watches for it at the moment, but we will
            // assign default ones nevertheless, because they will become valid after the
            // solver restarts.
            None => (
                kind,
                Some([parent.negative(), first_literal]),
                !parent_is_false,
            ),
        }
    }

    /// Returns the building blocks needed for a new [WatchedLiterals] of the
    /// [Clause::Constrains] kind.
    ///
    /// These building blocks are:
    ///
    /// - The [Clause] itself;
    /// - The ids of the solvables that will be watched;
    /// - A boolean indicating whether the clause conflicts with existing
    ///   decisions. This should always be false when adding clauses before
    ///   starting the solving process, but can be true for clauses that are
    ///   added dynamically.
    fn constrains(
        parent: VariableId,
        forbidden_solvable: VariableId,
        via: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (Self, Option<[Literal; 2]>, bool) {
        // On the lazy-conditional path the parent may already have been propagated
        // false by the time this clause is built (e.g. a candidate of a deferred
        // requirement whose dependencies are prefetched). The clause `¬parent v
        // ¬forbidden` is then currently satisfied, but the assignment can be
        // backtracked later, so the clause must still be added.
        let parent_is_false = decision_tracker.assigned_value(parent) == Some(false);

        // If the forbidden solvable is already assigned to true, that means that there
        // is a conflict with current decisions, because it implies the parent
        // solvable would be false, unless the parent already is false, which
        // satisfies the clause.
        let conflict =
            !parent_is_false && decision_tracker.assigned_value(forbidden_solvable) == Some(true);

        (
            Clause::Constrains(parent, forbidden_solvable, via),
            Some([parent.negative(), forbidden_solvable.negative()]),
            conflict,
        )
    }

    /// Returns the building blocks needed for a new [WatchedLiterals] of the
    /// [Clause::ConstrainsExcluded] kind.
    fn constrains_excluded(
        candidate: VariableId,
        aux: VariableId,
        via: VersionSetId,
    ) -> (Self, Option<[Literal; 2]>) {
        (
            Clause::ConstrainsExcluded(candidate, aux, via),
            Some([candidate.negative(), aux.positive()]),
        )
    }

    /// Returns the building blocks needed for a new [WatchedLiterals] of the
    /// [Clause::ConstrainsParent] kind. See [`Clause::constrains`] for the
    /// meaning of the returned values.
    fn constrains_parent(
        parent: VariableId,
        aux: VariableId,
        via: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (Self, Option<[Literal; 2]>, bool) {
        // On the lazy-conditional path the parent may already have been propagated
        // false by the time this clause is built (e.g. a candidate of a deferred
        // requirement whose dependencies are prefetched). The clause `¬parent v
        // ¬aux` is then currently satisfied, but the assignment can be backtracked
        // later, so the clause must still be added.
        let parent_is_false = decision_tracker.assigned_value(parent) == Some(false);

        // If the auxiliary variable is already true, an excluded candidate is
        // installed, which implies the parent solvable would be false, unless
        // the parent already is false, which satisfies the clause.
        let conflict = !parent_is_false && decision_tracker.assigned_value(aux) == Some(true);

        (
            Clause::ConstrainsParent(parent, aux, via),
            Some([parent.negative(), aux.negative()]),
            conflict,
        )
    }

    /// Returns the ids of the solvables that will be watched as well as the
    /// clause itself.
    fn forbid_multiple(
        candidate: VariableId,
        constrained_candidate: Literal,
        name: N,
    ) -> (Self, Option<[Literal; 2]>) {
        (
            Clause::ForbidMultipleInstances(candidate, constrained_candidate, name),
            Some([candidate.negative(), constrained_candidate]),
        )
    }

    fn root() -> (Self, Option<[Literal; 2]>) {
        (Clause::InstallRoot, None)
    }

    fn exclude(candidate: VariableId, reason: StringId) -> (Self, Option<[Literal; 2]>) {
        (Clause::Excluded(candidate, reason), None)
    }

    fn lock(
        locked_candidate: VariableId,
        other_candidate: VariableId,
    ) -> (Self, Option<[Literal; 2]>) {
        (
            Clause::Lock(locked_candidate, other_candidate),
            Some([VariableId::root().negative(), other_candidate.negative()]),
        )
    }

    fn learnt(
        learnt_clause_id: LearntClauseId,
        literals: &[Literal],
    ) -> (Self, Option<[Literal; 2]>) {
        debug_assert!(!literals.is_empty());
        (
            Clause::Learnt(learnt_clause_id),
            if literals.len() == 1 {
                // No need for watches, since we learned an assertion
                None
            } else {
                Some([*literals.first().unwrap(), *literals.last().unwrap()])
            },
        )
    }

    fn any_of(selected_var: VariableId, other_var: VariableId) -> (Self, Option<[Literal; 2]>) {
        let kind = Clause::AnyOf(selected_var, other_var);
        (kind, Some([selected_var.positive(), other_var.negative()]))
    }

    /// Tries to fold over all the literals in the clause.
    ///
    /// This function is useful to iterate, find, or filter the literals in a
    /// clause.
    pub fn try_fold_literals<B, C, F>(
        &self,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        requirements_to_sorted_candidates: &RequirementMap<Vec<Vec<VariableId>>>,
        disjunction_to_candidates: &Arena<DisjunctionId, Disjunction>,
        init: C,
        mut visit: F,
    ) -> ControlFlow<B, C>
    where
        F: FnMut(C, Literal) -> ControlFlow<B, C>,
    {
        match *self {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(solvable, _) => visit(init, solvable.negative()),
            Clause::Learnt(learnt_id) => learnt_clauses[learnt_id]
                .iter()
                .copied()
                .try_fold(init, visit),
            Clause::Requires(solvable_id, disjunction, match_spec_id) => {
                iter::once(solvable_id.negative())
                    .chain(
                        disjunction
                            .into_iter()
                            .flat_map(|d| disjunction_to_candidates[d].literals.iter())
                            .copied(),
                    )
                    .chain(
                        requirements_to_sorted_candidates[match_spec_id]
                            .iter()
                            .flatten()
                            .map(|&s| s.positive()),
                    )
                    .try_fold(init, visit)
            }
            Clause::Constrains(s1, s2, _) => [s1.negative(), s2.negative()]
                .into_iter()
                .try_fold(init, visit),
            Clause::ConstrainsExcluded(candidate, aux, _) => [candidate.negative(), aux.positive()]
                .into_iter()
                .try_fold(init, visit),
            Clause::ConstrainsParent(parent, aux, _) => [parent.negative(), aux.negative()]
                .into_iter()
                .try_fold(init, visit),
            Clause::ForbidMultipleInstances(s1, s2, _) => {
                [s1.negative(), s2].into_iter().try_fold(init, visit)
            }
            Clause::Lock(_, s) => [s.negative(), VariableId::root().negative()]
                .into_iter()
                .try_fold(init, visit),
            Clause::AnyOf(selected, variable) => [selected.positive(), variable.negative()]
                .into_iter()
                .try_fold(init, visit),
        }
    }

    /// Visits each literal in the clause.
    ///
    /// If you need to exit early or return a value, use [`try_fold_literals`].
    pub fn visit_literals(
        &self,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        requirements_to_sorted_candidates: &RequirementMap<Vec<Vec<VariableId>>>,
        disjunction_to_candidates: &Arena<DisjunctionId, Disjunction>,
        mut visit: impl FnMut(Literal),
    ) {
        let _ = self.try_fold_literals(
            learnt_clauses,
            requirements_to_sorted_candidates,
            disjunction_to_candidates,
            (),
            |_, lit| {
                visit(lit);
                ControlFlow::<()>::Continue(())
            },
        );
    }

    /// Construct a [`ClauseDisplay`] to display the clause.
    pub fn display<'i, I: Interner<NameId = N>>(
        &self,
        variable_map: &'i VariableMap<I::NameId, I::SolvableId>,
        interner: &'i I,
    ) -> ClauseDisplay<'i, I> {
        ClauseDisplay {
            kind: *self,
            variable_map,
            interner,
        }
    }
}

/// Keeps track of the literals watched by a [`Clause`] and the state associated
/// to two linked lists this clause is part of
///
/// In our SAT implementation, each clause tracks two literals present in its
/// clause, to be notified when the value assigned to the variable has changed
/// (this technique is known as _watches_). Clauses that are tracking the same
/// variable are grouped together in a linked list, so it becomes easy to notify
/// them all.
#[derive(Clone)]
pub(crate) struct WatchedLiterals {
    /// The ids of the literals this clause is watching. A clause that is
    /// watching literals is always watching two literals, no more, no less.
    pub watched_literals: [Literal; 2],
    /// The ids of the next clause in each linked list that this clause is part
    /// of. If either of these or `None` then there is no next clause.
    pub(crate) next_watches: [Option<ClauseId>; 2],
}

impl WatchedLiterals {
    /// Shorthand method to construct a [`Clause::InstallRoot`] without
    /// requiring complicated arguments.
    pub fn root<N: SolverId>() -> (Option<Self>, Clause<N>) {
        let (kind, watched_literals) = Clause::root();
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    /// Shorthand method to construct a [Clause::Requires] without requiring
    /// complicated arguments.
    ///
    /// The returned boolean value is true when adding the clause resulted in a
    /// conflict.
    pub fn requires<N: SolverId>(
        candidate: VariableId,
        requirement: Requirement,
        matching_candidates: impl IntoIterator<Item = VariableId>,
        condition: Option<(DisjunctionId, &[Literal])>,
        decision_tracker: &DecisionTracker,
    ) -> (Option<Self>, bool, Clause<N>) {
        let (kind, watched_literals, conflict) = Clause::requires(
            candidate,
            requirement,
            matching_candidates,
            condition,
            decision_tracker,
        );

        (
            Self::from_kind_and_initial_watches(watched_literals),
            conflict,
            kind,
        )
    }

    /// Shorthand method to construct a [Clause::Constrains] without requiring
    /// complicated arguments.
    ///
    /// The returned boolean value is true when adding the clause resulted in a
    /// conflict.
    pub fn constrains<N: SolverId>(
        candidate: VariableId,
        constrained_package: VariableId,
        requirement: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (Option<Self>, bool, Clause<N>) {
        let (kind, watched_literals, conflict) = Clause::constrains(
            candidate,
            constrained_package,
            requirement,
            decision_tracker,
        );

        (
            Self::from_kind_and_initial_watches(watched_literals),
            conflict,
            kind,
        )
    }

    /// Shorthand method to construct a [Clause::ConstrainsExcluded] without
    /// requiring complicated arguments.
    pub fn constrains_excluded<N: SolverId>(
        candidate: VariableId,
        aux: VariableId,
        requirement: VersionSetId,
    ) -> (Option<Self>, Clause<N>) {
        let (kind, watched_literals) = Clause::constrains_excluded(candidate, aux, requirement);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    /// Shorthand method to construct a [Clause::ConstrainsParent] without
    /// requiring complicated arguments.
    ///
    /// The returned boolean value is true when adding the clause resulted in a
    /// conflict.
    pub fn constrains_parent<N: SolverId>(
        parent: VariableId,
        aux: VariableId,
        requirement: VersionSetId,
        decision_tracker: &DecisionTracker,
    ) -> (Option<Self>, bool, Clause<N>) {
        let (kind, watched_literals, conflict) =
            Clause::constrains_parent(parent, aux, requirement, decision_tracker);

        (
            Self::from_kind_and_initial_watches(watched_literals),
            conflict,
            kind,
        )
    }

    pub fn lock<N: SolverId>(
        locked_candidate: VariableId,
        other_candidate: VariableId,
    ) -> (Option<Self>, Clause<N>) {
        let (kind, watched_literals) = Clause::lock(locked_candidate, other_candidate);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    pub fn forbid_multiple<N: SolverId>(
        candidate: VariableId,
        other_candidate: Literal,
        name: N,
    ) -> (Option<Self>, Clause<N>) {
        let (kind, watched_literals) = Clause::forbid_multiple(candidate, other_candidate, name);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    pub fn learnt<N: SolverId>(
        learnt_clause_id: LearntClauseId,
        literals: &[Literal],
    ) -> (Option<Self>, Clause<N>) {
        let (kind, watched_literals) = Clause::learnt(learnt_clause_id, literals);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    pub fn exclude<N: SolverId>(
        candidate: VariableId,
        reason: StringId,
    ) -> (Option<Self>, Clause<N>) {
        let (kind, watched_literals) = Clause::exclude(candidate, reason);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    pub fn any_of<N: SolverId>(
        selected_var: VariableId,
        other_var: VariableId,
    ) -> (Option<Self>, Clause<N>) {
        let (kind, watched_literals) = Clause::any_of(selected_var, other_var);
        (Self::from_kind_and_initial_watches(watched_literals), kind)
    }

    fn from_kind_and_initial_watches(watched_literals: Option<[Literal; 2]>) -> Option<Self> {
        let watched_literals = watched_literals?;
        debug_assert!(watched_literals[0] != watched_literals[1]);
        Some(Self {
            watched_literals,
            next_watches: [None, None],
        })
    }

    pub fn next_unwatched_literal<N: SolverId>(
        &self,
        clause: &Clause<N>,
        learnt_clauses: &Arena<LearntClauseId, Vec<Literal>>,
        requirement_to_sorted_candidates: &RequirementMap<Vec<Vec<VariableId>>>,
        disjunction_to_candidates: &Arena<DisjunctionId, Disjunction>,
        decision_map: &DecisionMap,
        for_watch_index: usize,
    ) -> Option<Literal> {
        let other_watch_index = 1 - for_watch_index;

        match clause {
            Clause::InstallRoot => unreachable!(),
            Clause::Excluded(_, _) => unreachable!(),
            _ if clause.is_binary() => None,
            clause => {
                let next = clause.try_fold_literals(
                    learnt_clauses,
                    requirement_to_sorted_candidates,
                    disjunction_to_candidates,
                    (),
                    |_, lit| {
                        // The next unwatched variable (if available), is a variable that is:
                        // * Not already being watched
                        // * Not yet decided, or decided in such a way that the literal yields true
                        if self.watched_literals[other_watch_index] != lit
                            && lit.eval(decision_map).unwrap_or(true)
                        {
                            ControlFlow::Break(lit)
                        } else {
                            ControlFlow::Continue(())
                        }
                    },
                );
                match next {
                    ControlFlow::Break(lit) => Some(lit),
                    ControlFlow::Continue(_) => None,
                }
            }
        }
    }
}

/// Represents a literal in a SAT clause, a literal holds a variable and
/// indicates whether it should be positive or negative (i.e. either A or ¬A).
///
/// A [`Literal`] stores a [`NonZeroU32`] which ensures that the size of an
/// `Option<Literal>` is the same as a `Literal`.
#[repr(transparent)]
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub(crate) struct Literal(NonZeroU32);

impl Literal {
    /// Constructs a new [`Literal`] from a [`VariableId`] and a boolean
    /// indicating whether the literal should be negated.
    #[inline]
    pub fn new(variable: VariableId, negate: bool) -> Self {
        let variable_idx = variable.to_index();
        let encoded_literal = variable_idx << 1 | negate as usize;
        Self::from_index(encoded_literal)
    }
}

impl DenseIndex for Literal {
    #[inline]
    fn from_index(x: usize) -> Self {
        let idx: u32 = (x + 1).try_into().expect("watched literal id too big");
        // SAFETY: This is safe because we are adding 1 to the index
        unsafe { Literal(NonZeroU32::new_unchecked(idx)) }
    }

    #[inline]
    fn to_index(self) -> usize {
        self.0.get() as usize - 1
    }
}

impl Literal {
    #[inline]
    pub fn negate(&self) -> bool {
        (self.0.get() & 1) == 0
    }

    /// Returns the value that would make the literal evaluate to true if
    /// assigned to the literal's solvable
    #[inline]
    pub(crate) fn satisfying_value(self) -> bool {
        !self.negate()
    }

    /// Returns the value that would make the literal evaluate to true if
    /// assigned to the literal's solvable
    #[inline]
    pub(crate) fn variable(self) -> VariableId {
        VariableId::from_index(self.to_index() >> 1)
    }

    /// Evaluates the literal, or returns `None` if no value has been assigned
    /// to the solvable
    #[inline(always)]
    pub(crate) fn eval(self, decision_map: &DecisionMap) -> Option<bool> {
        decision_map
            .value(self.variable())
            .map(|value| value != self.negate())
    }
}

impl VariableId {
    /// Constructs a [`Literal`] that indicates this solvable should be assigned
    /// a positive value.
    #[inline]
    pub(crate) fn positive(self) -> Literal {
        Literal::new(self, false)
    }

    /// Constructs a [`Literal`] that indicates this solvable should be assigned
    /// a negative value.
    #[inline]
    pub(crate) fn negative(self) -> Literal {
        Literal::new(self, true)
    }
}

/// A representation of a clause that implements [`Debug`]
pub(crate) struct ClauseDisplay<'i, I: Interner> {
    kind: Clause<I::NameId>,
    interner: &'i I,
    variable_map: &'i VariableMap<I::NameId, I::SolvableId>,
}

impl<I: Interner> Display for ClauseDisplay<'_, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.kind {
            Clause::InstallRoot => write!(f, "InstallRoot"),
            Clause::Excluded(variable, reason) => {
                write!(
                    f,
                    "Excluded({}({:?}), {})",
                    variable.display(self.variable_map, self.interner),
                    variable,
                    self.interner.display_string(reason)
                )
            }
            Clause::Learnt(learnt_id) => write!(f, "Learnt({learnt_id:?})"),
            Clause::Requires(variable, condition, requirement) => {
                write!(
                    f,
                    "Requires({}({:?}), {}, condition={:?})",
                    variable.display(self.variable_map, self.interner),
                    variable,
                    requirement.display(self.interner),
                    condition
                )
            }
            Clause::Constrains(v1, v2, version_set_id) => {
                write!(
                    f,
                    "Constrains({}({:?}), {}({:?}), {})",
                    v1.display(self.variable_map, self.interner),
                    v1,
                    v2.display(self.variable_map, self.interner),
                    v2,
                    self.interner.display_version_set(version_set_id)
                )
            }
            Clause::ConstrainsExcluded(candidate, aux, version_set_id) => {
                write!(
                    f,
                    "ConstrainsExcluded({}({:?}), {}({:?}), {})",
                    candidate.display(self.variable_map, self.interner),
                    candidate,
                    aux.display(self.variable_map, self.interner),
                    aux,
                    self.interner.display_version_set(version_set_id)
                )
            }
            Clause::ConstrainsParent(parent, aux, version_set_id) => {
                write!(
                    f,
                    "ConstrainsParent({}({:?}), {}({:?}), {})",
                    parent.display(self.variable_map, self.interner),
                    parent,
                    aux.display(self.variable_map, self.interner),
                    aux,
                    self.interner.display_version_set(version_set_id)
                )
            }
            Clause::ForbidMultipleInstances(v1, v2, name) => {
                write!(
                    f,
                    "ForbidMultipleInstances({}({:?}), {}({:?}), {})",
                    v1.display(self.variable_map, self.interner),
                    v1,
                    v2.variable().display(self.variable_map, self.interner),
                    v2,
                    self.interner.display_name(name)
                )
            }
            Clause::Lock(locked, other) => {
                write!(
                    f,
                    "Lock({}({:?}), {}({:?}))",
                    locked.display(self.variable_map, self.interner),
                    locked,
                    other.display(self.variable_map, self.interner),
                    other,
                )
            }
            Clause::AnyOf(variable, other) => {
                write!(
                    f,
                    "AnyOf({}({:?}), {}({:?}))",
                    variable.display(self.variable_map, self.interner),
                    variable,
                    other.display(self.variable_map, self.interner),
                    other,
                )
            }
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::{DenseIndex, solver::decision::Decision};

    #[test]
    #[allow(clippy::bool_assert_comparison)]
    fn test_literal_satisfying_value() {
        let lit = VariableId::root().negative();
        assert_eq!(lit.satisfying_value(), false);

        let lit = VariableId::root().positive();
        assert_eq!(lit.satisfying_value(), true);
    }

    #[test]
    fn test_literal_eval() {
        let mut decision_map = DecisionMap::default();

        let literal = VariableId::root().positive();
        let negated_literal = VariableId::root().negative();

        // Undecided
        assert_eq!(literal.eval(&decision_map), None);
        assert_eq!(negated_literal.eval(&decision_map), None);

        // Decided
        decision_map.set(VariableId::root(), true, 1);
        assert_eq!(literal.eval(&decision_map), Some(true));
        assert_eq!(negated_literal.eval(&decision_map), Some(false));

        decision_map.set(VariableId::root(), false, 1);
        assert_eq!(literal.eval(&decision_map), Some(false));
        assert_eq!(negated_literal.eval(&decision_map), Some(true));
    }

    #[test]
    fn test_requires_with_and_without_conflict() {
        let mut decisions = DecisionTracker::default();

        let parent = VariableId::from_index(1);
        let candidate1 = VariableId::from_index(2);
        let candidate2 = VariableId::from_index(3);

        // No conflict, all candidates available
        let (clause, conflict, _kind) = WatchedLiterals::requires::<crate::NameId>(
            parent,
            VersionSetId::from_index(0).into(),
            [candidate1, candidate2],
            None,
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[0].variable(),
            parent
        );
        assert_eq!(clause.unwrap().watched_literals[1].variable(), candidate1);

        // No conflict, still one candidate available
        decisions
            .try_add_decision(Decision::new(candidate1, false, ClauseId::from_index(0)), 1)
            .unwrap();
        let (clause, conflict, _kind) = WatchedLiterals::requires::<crate::NameId>(
            parent,
            VersionSetId::from_index(0).into(),
            [candidate1, candidate2],
            None,
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[0].variable(),
            parent
        );
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[1].variable(),
            candidate2
        );

        // Conflict, no candidates available
        decisions
            .try_add_decision(
                Decision::new(candidate2, false, ClauseId::install_root()),
                1,
            )
            .unwrap();
        let (clause, conflict, _kind) = WatchedLiterals::requires::<crate::NameId>(
            parent,
            VersionSetId::from_index(0).into(),
            [candidate1, candidate2],
            None,
            &decisions,
        );
        assert!(conflict);
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[0].variable(),
            parent
        );
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[1].variable(),
            candidate1
        );

        // No conflict: all candidates are false, but the parent is false as
        // well, which satisfies the clause. This can happen on the
        // lazy-conditional path where clauses are built after the parent was
        // propagated false. The clause must still be constructed because the
        // parent's assignment can be backtracked later.
        decisions
            .try_add_decision(Decision::new(parent, false, ClauseId::install_root()), 1)
            .unwrap();
        let (clause, conflict, _kind) = WatchedLiterals::requires::<crate::NameId>(
            parent,
            VersionSetId::from_index(0).into(),
            [candidate1, candidate2],
            None,
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[0].variable(),
            parent
        );
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[1].variable(),
            candidate1
        );
    }

    #[test]
    fn test_constrains_with_and_without_conflict() {
        let mut decisions = DecisionTracker::default();

        let parent = VariableId::from_index(1);
        let forbidden = VariableId::from_index(2);

        // No conflict, forbidden package not installed
        let (clause, conflict, _kind) = WatchedLiterals::constrains::<crate::NameId>(
            parent,
            forbidden,
            VersionSetId::from_index(0),
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[0].variable(),
            parent
        );
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[1].variable(),
            forbidden
        );

        // Conflict, forbidden package installed
        decisions
            .try_add_decision(Decision::new(forbidden, true, ClauseId::install_root()), 1)
            .unwrap();
        let (clause, conflict, _kind) = WatchedLiterals::constrains::<crate::NameId>(
            parent,
            forbidden,
            VersionSetId::from_index(0),
            &decisions,
        );
        assert!(conflict);
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[0].variable(),
            parent
        );
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[1].variable(),
            forbidden
        );

        // No conflict: the forbidden solvable is installed, but the parent is
        // false, which satisfies the clause. This can happen on the
        // lazy-conditional path where clauses are built after the parent was
        // propagated false. The clause must still be constructed because the
        // parent's assignment can be backtracked later.
        decisions
            .try_add_decision(Decision::new(parent, false, ClauseId::install_root()), 1)
            .unwrap();
        let (clause, conflict, _kind) = WatchedLiterals::constrains::<crate::NameId>(
            parent,
            forbidden,
            VersionSetId::from_index(0),
            &decisions,
        );
        assert!(!conflict);
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[0].variable(),
            parent
        );
        assert_eq!(
            clause.as_ref().unwrap().watched_literals[1].variable(),
            forbidden
        );
    }

    #[test]
    fn test_watched_literals_size() {
        // This test is here to ensure we don't increase the size of `WatchedLiterals`
        // by accident, as we are creating thousands of instances.
        // libsolv: 24 bytes
        assert_eq!(std::mem::size_of::<WatchedLiterals>(), 16);
    }

    #[test]
    fn test_literal_size() {
        assert_eq!(std::mem::size_of::<Literal>(), 4);
        assert_eq!(
            std::mem::size_of::<Literal>(),
            std::mem::size_of::<Option<Literal>>()
        );
        assert_eq!(
            std::mem::size_of::<Literal>() * 2,
            std::mem::size_of::<[Literal; 2]>()
        );
        assert_eq!(
            std::mem::size_of::<Literal>() * 2,
            std::mem::size_of::<[Option<Literal>; 2]>()
        );
        assert_eq!(
            std::mem::size_of::<Literal>() * 2,
            std::mem::size_of::<Option<[Literal; 2]>>()
        );
    }

    #[test]
    fn test_watched_literal_size() {
        assert_eq!(std::mem::size_of::<WatchedLiterals>(), 16);
        assert_eq!(
            std::mem::size_of::<Option<WatchedLiterals>>(),
            std::mem::size_of::<WatchedLiterals>()
        );
    }

    #[test]
    fn test_clause_size() {
        // The Clause enum should be kept small since we create thousands of instances.
        // Asserted exactly to catch both growth (worse cache) and silent shrinkage
        // (which would mean a variant got smaller and the bound is now loose).
        assert_eq!(std::mem::size_of::<Clause<crate::NameId>>(), 16);
    }

    #[test]
    fn test_key_type_sizes() {
        use crate::internal::id::*;
        use crate::{NameId, SolvableId};
        eprintln!("=== Key type sizes ===");
        eprintln!("VariableId: {} bytes", std::mem::size_of::<VariableId>());
        eprintln!("ClauseId: {} bytes", std::mem::size_of::<ClauseId>());
        eprintln!(
            "Option<ClauseId>: {} bytes",
            std::mem::size_of::<Option<ClauseId>>()
        );
        eprintln!("SolvableId: {} bytes", std::mem::size_of::<SolvableId>());
        eprintln!("NameId: {} bytes", std::mem::size_of::<NameId>());
        eprintln!(
            "Requirement: {} bytes",
            std::mem::size_of::<crate::Requirement>()
        );
        eprintln!(
            "Decision: {} bytes",
            std::mem::size_of::<super::super::decision::Decision>()
        );
        eprintln!(
            "DecisionAndLevel (in DecisionMap): {} bytes",
            std::mem::size_of::<i32>()
        );
        eprintln!(
            "Clause + WatchedLiterals per clause: {} bytes",
            std::mem::size_of::<Clause<crate::NameId>>()
                + std::mem::size_of::<Option<WatchedLiterals>>()
        );
    }
}
