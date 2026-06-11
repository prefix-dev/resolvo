//! Tests for the structured [`ConflictHint`]s returned by `Conflict::hints`.
//!
//! Each hint is rendered to a readable line so the snapshot stays meaningful and
//! doubles as an example of resolving the interned ids through the `Interner`.

use itertools::Itertools;
use resolvo::{
    Interner, Problem, Solver, UnsolvableOrCancelled,
    conflict::{ConflictHint, RequiredBy},
};

use crate::bundle_box::BundleBoxProvider;

fn format_required_by(provider: &BundleBoxProvider, required_by: &RequiredBy) -> String {
    match required_by {
        RequiredBy::Problem => "requested by the user".to_string(),
        RequiredBy::Solvable(solvable) => {
            format!("required by {}", provider.display_solvable(*solvable))
        }
    }
}

fn format_hint(provider: &BundleBoxProvider, hint: &ConflictHint) -> String {
    match hint {
        ConflictHint::PackageUnavailable {
            name, required_by, ..
        } => format!(
            "Package '{}' is not available, {}.",
            provider.display_name(*name),
            format_required_by(provider, required_by),
        ),
        ConflictHint::NoMatchingVersion {
            requirement,
            available,
            required_by,
        } => format!(
            "No version matches '{}', {}. Available: {}.",
            requirement.display(provider),
            format_required_by(provider, required_by),
            provider.display_merged_solvables(available),
        ),
        ConflictHint::AllCandidatesExcluded {
            name,
            reasons,
            required_by,
        } => format!(
            "Every candidate for '{}' is excluded, {}: {}.",
            provider.display_name(*name),
            format_required_by(provider, required_by),
            reasons
                .iter()
                .map(|&reason| provider.display_string(reason).to_string())
                .format(", "),
        ),
        ConflictHint::IncompatibleRequests { name, solvables } => format!(
            "Package '{}' is required in incompatible versions: {}.",
            provider.display_name(*name),
            provider.display_merged_solvables(solvables),
        ),
        ConflictHint::Constrained {
            constraint,
            constrained_by,
        } => format!(
            "{} constrains '{} {}', which cannot be satisfied.",
            provider.display_solvable(*constrained_by),
            provider.display_name(provider.version_set_name(*constraint)),
            provider.display_version_set(*constraint),
        ),
        ConflictHint::Locked { locked } => format!(
            "{} is locked, but another version is required.",
            provider.display_solvable(*locked)
        ),
    }
}

/// Solve the problem (expecting it to be unsat) and return the resulting hints
/// rendered to a readable, one-per-line string.
fn solve_unsat_hints(mut provider: BundleBoxProvider, specs: &[&str]) -> String {
    let requirements = provider.requirements(specs);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    match solver.solve(problem) {
        Ok(_) => panic!("expected unsat, but a solution was found"),
        Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
            let hints = conflict.hints(&solver);
            let provider = solver.provider();
            hints
                .iter()
                .map(|hint| format_hint(provider, hint))
                .format("\n")
                .to_string()
        }
        Err(UnsolvableOrCancelled::Cancelled(reason)) => *reason.downcast().unwrap(),
    }
}

/// A top-level requested package that does not exist at all.
#[test]
fn test_package_unavailable_top_level() {
    let provider = BundleBoxProvider::from_packages(&[("asdf", 1, vec![])]);
    insta::assert_snapshot!(solve_unsat_hints(provider, &["does-not-exist"]), @"Package 'does-not-exist' is not available, requested by the user.");
}

/// A dependency of a requested package that does not exist at all.
#[test]
fn test_package_unavailable_transitive() {
    let provider = BundleBoxProvider::from_packages(&[("a", 1, vec!["b"])]);
    insta::assert_snapshot!(solve_unsat_hints(provider, &["a"]), @"Package 'b' is not available, required by a=1.");
}

/// A top-level requested version range that matches none of the existing
/// versions.
#[test]
fn test_no_matching_version_top_level() {
    let provider = BundleBoxProvider::from_packages(&[("a", 1, vec![]), ("a", 2, vec![])]);
    insta::assert_snapshot!(solve_unsat_hints(provider, &["a 5..6"]), @"No version matches 'a >=5, <6', requested by the user. Available: a 1 | 2.");
}

/// A dependency version range that matches none of the existing versions.
#[test]
fn test_no_matching_version_transitive() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 5..6"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
        ("b", 3, vec![]),
    ]);
    insta::assert_snapshot!(solve_unsat_hints(provider, &["a"]), @"No version matches 'b >=5, <6', required by a=1. Available: b 1 | 2 | 3.");
}

/// A top-level requested package whose only candidate is excluded.
#[test]
fn test_all_candidates_excluded_top_level() {
    let mut provider = BundleBoxProvider::from_packages(&[("a", 1, vec![])]);
    provider.exclude("a", 1, "not available on this platform");
    insta::assert_snapshot!(solve_unsat_hints(provider, &["a"]), @"Every candidate for 'a' is excluded, requested by the user: not available on this platform.");
}

/// A dependency whose only candidate is excluded.
#[test]
fn test_all_candidates_excluded_transitive() {
    let mut provider = BundleBoxProvider::from_packages(&[("a", 1, vec!["b"]), ("b", 1, vec![])]);
    provider.exclude("b", 1, "not available on this platform");
    insta::assert_snapshot!(solve_unsat_hints(provider, &["a"]), @"Every candidate for 'b' is excluded, required by a=1: not available on this platform.");
}

/// Two packages each requiring an incompatible version of a shared dependency.
#[test]
fn test_incompatible_requests() {
    let provider = BundleBoxProvider::from_packages(&[
        ("c", 1, vec!["b 1..2"]),
        ("d", 1, vec!["b 2..3"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
    ]);
    insta::assert_snapshot!(solve_unsat_hints(provider, &["c", "d"]), @"Package 'b' is required in incompatible versions: b 1 | 2.");
}

/// A run constraint that cannot be fulfilled together with a dependency.
#[test]
fn test_constrained() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 10, vec!["b 50..100"]),
        ("b", 50, vec![]),
        ("b", 42, vec![]),
    ]);
    provider.add_package("c", 10.into(), &[], &["b 0..50"]);
    insta::assert_snapshot!(solve_unsat_hints(provider, &["a", "c"]), @"c=10 constrains 'b >=0, <50', which cannot be satisfied.");
}

/// A locked package that conflicts with a required version.
#[test]
fn test_locked() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 2..3"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
    ]);
    provider.set_locked("b", 1);
    insta::assert_snapshot!(solve_unsat_hints(provider, &["a"]), @"b=1 is locked, but another version is required.");
}

/// The conda/rattler#2476 shape: several versions of a package each depend on a
/// different missing version of the same dependency, producing one hint per
/// distinct requirement.
#[test]
fn test_distinct_requirements() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 41..42"]),
        ("a", 2, vec!["b 42..43"]),
        ("a", 3, vec!["b 43..44"]),
    ]);
    insta::assert_snapshot!(solve_unsat_hints(provider, &["a"]), @r"
    Package 'b' is not available, required by a=1.
    Package 'b' is not available, required by a=2.
    Package 'b' is not available, required by a=3.
    ");
}
