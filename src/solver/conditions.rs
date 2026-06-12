//! Resolvo supports conditional dependencies. E.g. `foo REQUIRES bar IF baz is
//! selected`.
//!
//! In SAT terms we express the requirement `A requires B` as `¬A1 v B1 .. v
//! B99` where A1 is a candidate of package A and B1 through B99 are candidates
//! that match the requirement B. In logical terms we say, either we do not
//! select A1 or we select one of matching Bs.
//!
//! If we add a condition C to the requirement, e.g. `A requires B if C` we can
//! modify the requirement clause to `¬A1 v ¬(C) v B1 .. v B2`. In logical terms
//! we say, either we do not select A1 or we do not match the condition or we
//! select one of the matching Bs.
//!
//! The condition `C` however expands to another set of matching candidates
//! (e.g. `C1 v C2 v C3`). If we insert that into the formula we get,
//!
//!   `¬A1 v ¬(C1 v C2 v C3) v B1 .. v B2`
//!
//! which expands to
//!
//!   `¬A1 v ¬C1 ^ ¬C2 ^ ¬C3 v B1 .. v B2`
//!
//! This is not in CNF form (required for SAT clauses) so we cannot use this
//! directly. To work around that problem we instead represent the condition
//! `¬(C)` as the complement of the version set C. E.g. if C would represent
//! `package >=1` then the complement would represent the candidates that match
//! `package <1`, or the candidates that do NOT match C. So if we represent the
//! complement of C as C! the final form of clause becomes:
//!
//!   `¬A1 v C!1 .. v C!99 v B1 .. v B2`
//!
//! This introduces another edge case though. What if the complement is empty?
//! The final format would be void of `C!n` variables so it would become `¬A1 v
//! B1 .. v B2`, e.g. A unconditionally requires B. To fix that issue we
//! introduce an auxiliary variable that encodes if at-least-one of the package
//! C is selected (notated as `C_selected`). For each candidate of C we add the
//! clause
//!
//!   `¬Cn v C_selected`
//!
//! This forces `C_selected` to become true if any `Cn` is set to true. We then
//! modify the requirement clause to be
//!
//!   `¬A1 v ¬C_selected v B1 .. v B2`
//!
//! Note that we do not encode any clauses to force `C_selected` to be false.
//! We argue that this state is not required to function properly. If
//! `C_selected` would be set to false it would mean that all candidates of
//! package C are unselectable. This would disable the requirement, e.g. B
//! shouldnt be selected for A1. But it doesnt prevent A1 from being selected.
//!
//! Conditions are expressed as boolean expression trees. Internally  they are
//! converted to Disjunctive Normal Form (DNF). A boolean expression is
//! in DNF if it is a **disjunction (OR)** of one or more **conjunctive clauses
//! (AND)**.
//!
//! We add a requires clause for each disjunction in the boolean expression. So
//! if we have the requirement `A requires B if C or D` we add requires clause
//! for `A requires B if C` and for `A requires B if D`.
//!
//! ## Lazy candidate loading
//!
//! To avoid fetching candidates for requirements whose condition never fires
//! the encoder may defer encoding a conditional requirement. When the encoder
//! reaches such a requirement and the condition does not yet hold, the
//! requirement is stored in [`crate::solver::SolverState::deferred_requirements`]
//! and its requirement candidates are *not* fetched. The solver loop checks
//! after each propagation whether any deferred condition has just started to
//! hold; if so, the corresponding entry is drained from the deferred map and
//! the encoder builds the requires clause exactly as the eager path would
//! have. See [`DeferredRequirement`] and [`condition_disjunct_holds`].

use std::num::NonZero;

use crate::solver::clause::Literal;
use crate::{
    Condition, ConditionId, ConditionalRequirement, DenseIndex, Interner, LogicalOperator,
    VersionSetId, internal::solver_id::SolvableIdOrRoot,
};

/// An identifier that describes a group of version sets that are combined using
/// AND logical operators.
#[derive(Debug, Clone, Copy, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct DisjunctionId(NonZero<u32>);

impl DenseIndex for DisjunctionId {
    fn from_index(x: usize) -> Self {
        // Safe because we are guaranteed that the id is non-zero by adding 1.
        DisjunctionId(unsafe { NonZero::new_unchecked((x + 1) as u32) })
    }

    fn to_index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

pub struct Disjunction {
    /// The literals associated with this particular disjunction
    pub literals: Vec<Literal>,

    /// The top-level condition to which this disjunction belongs.
    pub _condition: ConditionId,
}

/// Converts from a boolean expression tree as described by `condition` to a
/// boolean formula in disjunctive normal form (DNF). Each inner Vec represents
/// a conjunction (AND group) and the outer Vec represents the disjunction (OR
/// group).
pub fn convert_conditions_to_dnf<I: Interner>(
    condition: ConditionId,
    interner: &I,
) -> Vec<Vec<VersionSetId>> {
    match interner.resolve_condition(condition) {
        Condition::Requirement(version_set) => vec![vec![version_set]],
        Condition::Binary(LogicalOperator::Or, lhs, rhs) => {
            let mut left_dnf = convert_conditions_to_dnf(lhs, interner);
            let mut right_dnf = convert_conditions_to_dnf(rhs, interner);
            left_dnf.append(&mut right_dnf);
            left_dnf
        }
        Condition::Binary(LogicalOperator::And, lhs, rhs) => {
            let left_dnf = convert_conditions_to_dnf(lhs, interner);
            let right_dnf = convert_conditions_to_dnf(rhs, interner);

            // Distribute AND over OR
            let mut result = Vec::new();
            for l in &left_dnf {
                for r in &right_dnf {
                    let mut merged = l.clone();
                    merged.extend(r.clone());
                    result.push(merged);
                }
            }
            result
        }
    }
}

/// One conjunct of a deferred condition disjunct. Captures the candidates
/// needed to decide whether the conjunct currently holds.
#[derive(Debug, Clone)]
pub(crate) enum DeferredConjunct<S> {
    /// The version set has a non-empty complement (some candidates of the
    /// package do not match the version set). The conjunct holds when any of
    /// the matching candidates of `version_set` is positively decided.
    Solvables {
        /// The version set inside the condition that this conjunct represents.
        version_set: VersionSetId,
        /// Candidates of the package that match `version_set`.
        matching: Vec<S>,
    },
    /// The version set has an empty complement: every candidate of the package
    /// matches it. The conjunct then holds whenever any candidate of the
    /// package is positively decided.
    Empty {
        /// The version set inside the condition that this conjunct represents.
        version_set: VersionSetId,
        /// All candidates of the package whose version set was empty-complement.
        all_candidates: Vec<S>,
    },
}

impl<S> DeferredConjunct<S> {
    /// The version set inside the condition that this conjunct represents.
    pub fn version_set(&self) -> VersionSetId {
        match self {
            DeferredConjunct::Solvables { version_set, .. }
            | DeferredConjunct::Empty { version_set, .. } => *version_set,
        }
    }

    /// Candidates whose positive decision indicates that this conjunct holds.
    pub fn candidates(&self) -> &[S] {
        match self {
            DeferredConjunct::Solvables { matching, .. } => matching,
            DeferredConjunct::Empty { all_candidates, .. } => all_candidates,
        }
    }
}

/// A conditional requirement whose condition did not yet hold at the moment
/// the encoder first reached it, and whose requirement candidates were
/// therefore not loaded eagerly.
///
/// Each deferred entry corresponds to a *single* disjunct of the condition's
/// DNF (a single `requires` clause in the encoding). Once that disjunct fires
/// the entry is drained from
/// [`crate::solver::SolverState::deferred_requirements`] and the requires
/// clause is built. An entry is never encoded twice: removal happens on first
/// fire.
#[derive(Debug)]
pub(crate) struct DeferredRequirement<S> {
    /// The solvable whose dependencies introduced this requirement.
    pub solvable_id: SolvableIdOrRoot<S>,
    /// The conditional requirement itself; carries the requirement that needs
    /// to be encoded once the condition fires.
    pub requirement: ConditionalRequirement,
    /// The condition that gates the requirement. Stored for use as the key in
    /// the deferred map and for re-querying the cache when encoding.
    pub condition: ConditionId,
    /// The single disjunct of the condition's DNF that gates this entry. A
    /// conjunction of `DeferredConjunct`; the disjunct holds when every
    /// conjunct holds (see [`condition_disjunct_holds`]).
    pub disjunct: Vec<DeferredConjunct<S>>,
}

/// Returns true if every conjunct in `disjunct` currently holds. A conjunct
/// holds when at least one of its `candidates()` solvables has been
/// positively decided in `is_positively_decided`. An empty disjunct (empty
/// conjunction) is treated as trivially holding.
pub(crate) fn condition_disjunct_holds<S: Copy>(
    disjunct: &[DeferredConjunct<S>],
    mut is_positively_decided: impl FnMut(S) -> bool,
) -> bool {
    disjunct.iter().all(|conjunct| {
        conjunct
            .candidates()
            .iter()
            .any(|&s| is_positively_decided(s))
    })
}
