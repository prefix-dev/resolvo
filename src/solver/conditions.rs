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

use std::num::NonZero;

use crate::solver::clause::Literal;
use crate::{Condition, ConditionId, DenseIndex, Interner, LogicalOperator, VersionSetId};

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
