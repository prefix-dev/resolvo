mod bundle_box;

use std::io::{Write, stderr};

use bundle_box::{BundleBoxProvider, Pack};
use insta::assert_snapshot;
use itertools::Itertools;
use resolvo::{
    ConditionalRequirement, DependencyProvider, Interner, Problem, SolvableId, Solver,
    UnsolvableOrCancelled, VersionSetId,
};
use tracing_test::traced_test;

/// Create a string from a [`Transaction`]
fn transaction_to_string(
    interner: &impl Interner<SolvableId = SolvableId>,
    solvables: &[SolvableId],
) -> String {
    use std::fmt::Write;
    let mut buf = String::new();
    for solvable in solvables
        .iter()
        .copied()
        .map(|s| interner.display_solvable(s).to_string())
        .sorted()
    {
        writeln!(buf, "{solvable}").unwrap();
    }

    buf
}

/// Unsat so that we can view the conflict
fn solve_unsat(mut provider: BundleBoxProvider, specs: &[&str]) -> String {
    let requirements = provider.requirements(specs);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    match solver.solve(problem) {
        Ok(_) => panic!("expected unsat, but a solution was found"),
        Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
            // Write the conflict graphviz to stderr
            let graph = conflict.graph(&solver);
            let mut output = stderr();
            writeln!(output, "UNSOLVABLE:").unwrap();
            graph
                .graphviz(&mut output, solver.provider(), true)
                .unwrap();
            writeln!(output, "\n").unwrap();

            // Format a user friendly error message
            conflict.display_user_friendly(&solver).to_string()
        }
        Err(UnsolvableOrCancelled::Cancelled(reason)) => *reason.downcast().unwrap(),
    }
}

/// Solve the problem and returns either a solution represented as a string or
/// an error string.
fn solve_snapshot(mut provider: BundleBoxProvider, specs: &[&str]) -> String {
    // The test dependency provider requires time support for sleeping
    let runtime = tokio::runtime::Builder::new_current_thread()
        .enable_time()
        .build()
        .unwrap();

    provider.sleep_before_return = true;

    let requirements = provider.requirements(specs);
    let mut solver = Solver::new(provider).with_runtime(runtime);
    let problem = Problem::new().requirements(requirements);
    match solver.solve(problem) {
        Ok(solvables) => transaction_to_string(solver.provider(), &solvables),
        Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
            // Write the conflict graphviz to stderr
            let graph = conflict.graph(&solver);
            let mut output = stderr();
            writeln!(output, "UNSOLVABLE:").unwrap();
            graph
                .graphviz(&mut output, solver.provider(), true)
                .unwrap();
            writeln!(output, "\n").unwrap();

            // Format a user friendly error message
            conflict.display_user_friendly(&solver).to_string()
        }
        Err(UnsolvableOrCancelled::Cancelled(reason)) => *reason.downcast().unwrap(),
    }
}

/// Test whether we can select a version, this is the most basic operation
#[test]
fn test_unit_propagation_1() {
    let mut provider = BundleBoxProvider::from_packages(&[("asdf", 1, vec![])]);
    let requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);
    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 1);
}

/// Test if we can also select a nested version
#[test]
fn test_unit_propagation_nested() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("asdf", 1u32, vec!["efgh"]),
        ("efgh", 4u32, vec![]),
        ("dummy", 6u32, vec![]),
    ]);
    let requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 2);

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 1);

    let solvable = pool.resolve_solvable(solved[1]);

    assert_eq!(pool.resolve_package_name(solvable.name), "efgh");
    assert_eq!(solvable.record.version, 4);
}

/// Test if we can resolve multiple versions at once
#[test]
fn test_resolve_multiple() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("asdf", 1, vec![]),
        ("asdf", 2, vec![]),
        ("efgh", 4, vec![]),
        ("efgh", 5, vec![]),
    ]);
    let requirements = provider.requirements(&["asdf", "efgh"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let mut solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 2);
    solved.sort_by_key(|&s| pool.resolve_package_name(pool.resolve_solvable(s).name));

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 2);

    let solvable = pool.resolve_solvable(solved[1]);

    assert_eq!(pool.resolve_package_name(solvable.name), "efgh");
    assert_eq!(solvable.record.version, 5);
}

#[test]
fn test_resolve_with_concurrent_metadata_fetching() {
    let provider = BundleBoxProvider::from_packages(&[
        ("parent", 4, vec!["child1", "child2"]),
        ("child1", 3, vec![]),
        ("child2", 2, vec![]),
    ]);

    let max_concurrent_requests = provider.concurrent_requests_max.clone();

    let result = solve_snapshot(provider, &["parent"]);
    insta::assert_snapshot!(result);

    assert_eq!(2, max_concurrent_requests.get());
}

/// In case of a conflict the version should not be selected with the conflict
#[test]
#[traced_test]
fn test_resolve_with_conflict() {
    let provider = BundleBoxProvider::from_packages(&[
        ("asdf", 4, vec!["conflicting 1"]),
        ("asdf", 3, vec!["conflicting 0"]),
        ("efgh", 7, vec!["conflicting 0"]),
        ("efgh", 6, vec!["conflicting 0"]),
        ("conflicting", 1, vec![]),
        ("conflicting", 0, vec![]),
    ]);
    let result = solve_snapshot(provider, &["asdf", "efgh"]);
    insta::assert_snapshot!(result);
}

/// The non-existing package should not be selected
#[test]
#[traced_test]
fn test_resolve_with_nonexisting() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("asdf", 4, vec!["b"]),
        ("asdf", 3, vec![]),
        ("b", 1, vec!["idontexist"]),
    ]);
    let requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 3);
}

#[test]
#[traced_test]
fn test_resolve_with_nested_deps() {
    let mut provider = BundleBoxProvider::from_packages(&[
        (
            "apache-airflow",
            3,
            vec!["opentelemetry-api 2..4", "opentelemetry-exporter-otlp"],
        ),
        (
            "apache-airflow",
            2,
            vec!["opentelemetry-api 2..4", "opentelemetry-exporter-otlp"],
        ),
        ("apache-airflow", 1, vec![]),
        ("opentelemetry-api", 3, vec!["opentelemetry-sdk"]),
        ("opentelemetry-api", 2, vec![]),
        ("opentelemetry-api", 1, vec![]),
        ("opentelemetry-exporter-otlp", 1, vec!["opentelemetry-grpc"]),
        ("opentelemetry-grpc", 1, vec!["opentelemetry-api 1"]),
    ]);
    let requirements = provider.requirements(&["apache-airflow"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "apache-airflow");
    assert_eq!(solvable.record.version, 1);
}

#[test]
#[traced_test]
fn test_resolve_with_unknown_deps() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package(
        "opentelemetry-api",
        Pack::new(3).with_unknown_deps(),
        &[],
        &[],
    );
    provider.add_package("opentelemetry-api", Pack::new(2), &[], &[]);
    let requirements = provider.requirements(&["opentelemetry-api"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);

    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(
        pool.resolve_package_name(solvable.name),
        "opentelemetry-api"
    );
    assert_eq!(solvable.record.version, 2);
}

#[test]
#[traced_test]
fn test_resolve_and_cancel() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package(
        "opentelemetry-api",
        Pack::new(3).with_unknown_deps(),
        &[],
        &[],
    );
    provider.add_package(
        "opentelemetry-api",
        Pack::new(2).cancel_during_get_dependencies(),
        &[],
        &[],
    );
    let error = solve_unsat(provider, &["opentelemetry-api"]);
    insta::assert_snapshot!(error);
}

/// Locking a specific package version in this case a lower version namely `3`
/// should result in the higher package not being considered
#[test]
fn test_resolve_locked_top_level() {
    let mut provider =
        BundleBoxProvider::from_packages(&[("asdf", 4, vec![]), ("asdf", 3, vec![])]);
    provider.set_locked("asdf", 3);

    let requirements = provider.requirements(&["asdf"]);

    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);
    let solvable_id = solved[0];
    assert_eq!(pool.resolve_solvable(solvable_id).record.version, 3);
}

/// Should ignore lock when it is not a top level package and a newer version
/// exists without it
#[test]
fn test_resolve_ignored_locked_top_level() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("asdf", 4, vec![]),
        ("asdf", 3, vec!["fgh"]),
        ("fgh", 1, vec![]),
    ]);

    provider.set_locked("fgh", 1);

    let requirements = provider.requirements(&["asdf"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let pool = &solver.provider().pool;

    assert_eq!(solved.len(), 1);
    let solvable = pool.resolve_solvable(solved[0]);

    assert_eq!(pool.resolve_package_name(solvable.name), "asdf");
    assert_eq!(solvable.record.version, 4);
}

/// Test checks if favoring without a conflict results in a package upgrade
#[test]
fn test_resolve_favor_without_conflict() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec![]),
        ("a", 2, vec![]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
    ]);
    provider.set_favored("a", 1);
    provider.set_favored("b", 1);

    // Already installed: A=1; B=1
    let result = solve_snapshot(provider, &["a", "b 2"]);
    insta::assert_snapshot!(result, @r###"
        a=1
        b=2
        "###);
}

#[test]
fn test_resolve_favor_with_conflict() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["c 1"]),
        ("a", 2, vec![]),
        ("b", 1, vec!["c 1"]),
        ("b", 2, vec!["c 2"]),
        ("c", 1, vec![]),
        ("c", 2, vec![]),
    ]);
    provider.set_favored("a", 1);
    provider.set_favored("b", 1);
    provider.set_favored("c", 1);

    let result = solve_snapshot(provider, &["a", "b 2"]);
    insta::assert_snapshot!(result, @r###"
        a=2
        b=2
        c=2
        "###);
}

#[test]
fn test_resolve_cyclic() {
    let mut provider =
        BundleBoxProvider::from_packages(&[("a", 2, vec!["b 0..10"]), ("b", 5, vec!["a 2..4"])]);
    let requirements = provider.requirements(&["a 0..100"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    insta::assert_snapshot!(result, @r###"
        a=2
        b=5
        "###);
}

#[test]
fn test_resolve_union_requirements() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec![]),
        ("b", 1, vec![]),
        ("c", 1, vec!["a"]),
        ("d", 1, vec!["b"]),
        ("e", 1, vec!["a | b"]),
    ]);

    // Make d conflict with a=1
    provider.add_package("f", 1.into(), &["b"], &["a 2"]);

    let result = solve_snapshot(provider, &["c | d", "e", "f"]);
    assert_snapshot!(result, @r###"
        b=1
        d=1
        e=1
        f=1
        "###);
}

#[test]
fn test_unsat_locked_and_excluded() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("asdf", 1, vec!["c 2"]),
        ("c", 2, vec![]),
        ("c", 1, vec![]),
    ]);
    provider.set_locked("c", 1);
    insta::assert_snapshot!(solve_snapshot(provider, &["asdf"]));
}

#[test]
#[tracing_test::traced_test]
fn test_unsat_no_candidates_for_child_1() {
    let provider = BundleBoxProvider::from_packages(&[("asdf", 1, vec!["c 2"]), ("c", 1, vec![])]);
    let error = solve_unsat(provider, &["asdf"]);
    insta::assert_snapshot!(error);
}

//
#[test]
fn test_unsat_no_candidates_for_child_2() {
    let provider = BundleBoxProvider::from_packages(&[("a", 41, vec!["B 0..20"])]);
    let error = solve_unsat(provider, &["a 0..1000"]);
    insta::assert_snapshot!(error);
}

// Versions requiring different versions of a missing dependency are each
// reported (conda/rattler#2476).
#[test]
fn test_unsat_no_candidates_distinct_requirements() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 41..42"]),
        ("a", 2, vec!["b 41..42"]),
        ("a", 3, vec!["b 42..43"]),
        ("a", 4, vec!["b 43..44"]),
    ]);
    let error = solve_unsat(provider, &["a"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_missing_top_level_dep_1() {
    let provider = BundleBoxProvider::from_packages(&[("asdf", 1, vec![])]);
    let error = solve_unsat(provider, &["fghj"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_missing_top_level_dep_2() {
    let provider = BundleBoxProvider::from_packages(&[("a", 41, vec!["b 15"]), ("b", 15, vec![])]);
    let error = solve_unsat(provider, &["a 41", "b 14"]);
    insta::assert_snapshot!(error);
}

#[test]
#[tracing_test::traced_test]
fn test_unsat_after_backtracking() {
    let provider = BundleBoxProvider::from_packages(&[
        ("b", 7, vec!["d 1"]),
        ("b", 6, vec!["d 1"]),
        ("c", 1, vec!["d 2"]),
        ("c", 2, vec!["d 2"]),
        ("d", 2, vec![]),
        ("d", 1, vec![]),
        ("e", 1, vec![]),
        ("e", 2, vec![]),
    ]);

    let error = solve_unsat(provider, &["b", "c", "e"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_incompatible_root_requirements() {
    let provider = BundleBoxProvider::from_packages(&[("a", 2, vec![]), ("a", 5, vec![])]);
    let error = solve_unsat(provider, &["a 0..4", "a 5..10"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_bluesky_conflict() {
    let provider = BundleBoxProvider::from_packages(&[
        ("suitcase-utils", 54, vec![]),
        ("suitcase-utils", 53, vec![]),
        (
            "bluesky-widgets",
            42,
            vec![
                "bluesky-live 0..10",
                "numpy 0..10",
                "python 0..10",
                "suitcase-utils 0..54",
            ],
        ),
        ("bluesky-live", 1, vec![]),
        ("numpy", 1, vec![]),
        ("python", 1, vec![]),
    ]);
    let error = solve_unsat(
        provider,
        &["bluesky-widgets 0..100", "suitcase-utils 54..100"],
    );
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_pubgrub_article() {
    // Taken from the pubgrub article: https://nex3.medium.com/pubgrub-2fb6470504f
    let provider = BundleBoxProvider::from_packages(&[
        ("menu", 15, vec!["dropdown 2..3"]),
        ("menu", 10, vec!["dropdown 1..2"]),
        ("dropdown", 2, vec!["icons 2"]),
        ("dropdown", 1, vec!["intl 3"]),
        ("icons", 2, vec![]),
        ("icons", 1, vec![]),
        ("intl", 5, vec![]),
        ("intl", 3, vec![]),
    ]);
    let error = solve_unsat(provider, &["menu", "icons 1", "intl 5"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_applies_graph_compression() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 10, vec!["b"]),
        ("a", 9, vec!["b"]),
        ("b", 100, vec!["c 0..100"]),
        ("b", 42, vec!["c 0..100"]),
        ("c", 103, vec![]),
        ("c", 101, vec![]),
        ("c", 100, vec![]),
        ("c", 99, vec![]),
    ]);
    let error = solve_unsat(provider, &["a", "c 101..104"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_unsat_constrains() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 10, vec!["b 50..100"]),
        ("a", 9, vec!["b 50..100"]),
        ("b", 50, vec![]),
        ("b", 42, vec![]),
    ]);

    provider.add_package("c", 10.into(), &[], &["b 0..50"]);
    provider.add_package("c", 8.into(), &[], &["b 0..50"]);
    let error = solve_unsat(provider, &["a", "c"]);
    insta::assert_snapshot!(error);
}

#[test]
#[tracing_test::traced_test]
fn test_unsat_constrains_2() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b"]),
        ("a", 2, vec!["b"]),
        ("b", 1, vec!["c 1"]),
        ("b", 2, vec!["c 2"]),
    ]);

    provider.add_package("c", 1.into(), &[], &["a 3"]);
    provider.add_package("c", 2.into(), &[], &["a 3"]);
    let error = solve_unsat(provider, &["a"]);
    insta::assert_snapshot!(error);
}

#[test]
fn test_missing_dep() {
    let provider = BundleBoxProvider::from_packages(&[("a", 2, vec!["missing"]), ("a", 1, vec![])]);
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
#[tracing_test::traced_test]
fn test_no_backtracking() {
    let provider = BundleBoxProvider::from_packages(&[
        ("quetz-server", 2, vec!["pydantic 10..20"]),
        ("quetz-server", 1, vec!["pydantic 0..10"]),
        ("pydantic", 1, vec![]),
        ("pydantic", 2, vec![]),
        ("pydantic", 3, vec![]),
        ("pydantic", 4, vec![]),
        ("pydantic", 5, vec![]),
        ("pydantic", 6, vec![]),
        ("pydantic", 7, vec![]),
        ("pydantic", 8, vec![]),
        ("pydantic", 9, vec![]),
        ("pydantic", 10, vec![]),
        ("pydantic", 11, vec![]),
        ("pydantic", 12, vec![]),
        ("pydantic", 13, vec![]),
        ("pydantic", 14, vec![]),
    ]);
    insta::assert_snapshot!(solve_snapshot(
        provider,
        &["quetz-server", "pydantic 0..10"]
    ));
}

#[test]
#[tracing_test::traced_test]
fn test_incremental_crash() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 3, vec!["missing"]),
        ("a", 2, vec!["missing"]),
        ("a", 1, vec!["b"]),
        ("b", 2, vec!["a 2..4"]),
        ("b", 1, vec![]),
    ]);
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
#[traced_test]
fn test_excluded() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 2, vec!["b"]),
        ("a", 1, vec!["c"]),
        ("b", 1, vec![]),
        ("c", 1, vec![]),
    ]);
    provider.exclude("b", 1, "it is externally excluded");
    provider.exclude("c", 1, "it is externally excluded");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
fn test_merge_excluded() {
    let mut provider = BundleBoxProvider::from_packages(&[("a", 1, vec![]), ("a", 2, vec![])]);
    provider.exclude("a", 1, "it is externally excluded");
    provider.exclude("a", 2, "it is externally excluded");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
#[traced_test]
fn test_merge_installable() {
    let provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec![]),
        ("a", 2, vec![]),
        ("a", 3, vec![]),
        ("a", 4, vec![]),
    ]);
    insta::assert_snapshot!(solve_snapshot(provider, &["a 0..3", "a 3..5"]));
}

#[test]
fn test_root_excluded() {
    let mut provider = BundleBoxProvider::from_packages(&[("a", 1, vec![])]);
    provider.exclude("a", 1, "it is externally excluded");
    insta::assert_snapshot!(solve_snapshot(provider, &["a"]));
}

#[test]
fn test_constraints() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 0..10"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
        ("c", 1, vec![]),
    ]);
    let requirements = provider.requirements(&["a 0..10"]);
    let constraints = provider.version_sets(&["b 1..2", "c"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new()
        .requirements(requirements)
        .constraints(constraints);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    insta::assert_snapshot!(result, @r###"
        a=1
        b=1
        "###);
}

#[test]
fn test_solve_with_additional() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 0..10"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
        ("c", 1, vec![]),
        ("d", 1, vec![]),
        ("e", 1, vec!["d"]),
        ("locked", 1, vec![]),
        ("locked", 2, vec![]),
    ]);

    provider.set_locked("locked", 2);

    let requirements = provider.requirements(&["a 0..10"]);
    let constraints = provider.version_sets(&["b 1..2", "c"]);

    let extra_solvables = [
        provider.solvable_id("b", 2),
        provider.solvable_id("c", 1),
        provider.solvable_id("e", 1),
        // Does not obey the locked clause since it has not been requested
        // in a version set by another solvable
        provider.solvable_id("locked", 1),
        provider.solvable_id("unknown-deps", Pack::new(1).with_unknown_deps()),
    ];

    let mut solver = Solver::new(provider);

    let problem = Problem::new()
        .requirements(requirements)
        .constraints(constraints)
        .soft_requirements(extra_solvables);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
        a=1
        b=1
        c=1
        d=1
        e=1
        locked=1
        "###);
}

/// Test that a soft requirement which conflicts with the hard solution is
/// handled correctly when forbid clauses are created lazily.
///
/// Only a=1 matches the hard requirement. The soft requirement a=2 has a
/// circular dependency on "a", so encoding it registers both a=1 and a=2 as
/// forbid targets after both are already decided true. The solver should
/// detect the conflict and exclude a=2 from the solution.
#[test]
fn test_solve_with_soft_requirement_forbid_clause_conflict() {
    let mut provider = BundleBoxProvider::from_packages(&[("a", 1, vec![]), ("a", 2, vec!["a"])]);

    // Only a=1 matches the hard requirement, so a=2 is never a matching
    // candidate during the hard solve and no forbid clause is created.
    let requirements = provider.requirements(&["a 1..2"]);
    let extra_solvables = [provider.solvable_id("a", 2)];

    let mut solver = Solver::new(provider);
    let problem = Problem::new()
        .requirements(requirements)
        .soft_requirements(extra_solvables);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    a=1
    "###);
}

#[test]
fn test_solve_with_additional_with_constrains() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b 0..10"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
        ("b", 3, vec![]),
        ("c", 1, vec![]),
        ("d", 1, vec!["f"]),
        ("e", 1, vec!["c"]),
    ]);

    provider.add_package("f", 1.into(), &[], &["c 2..3"]);
    provider.add_package("g", 1.into(), &[], &["b 2..3"]);
    provider.add_package("h", 1.into(), &[], &["b 1..2"]);
    provider.add_package("i", 1.into(), &[], &[]);
    provider.add_package("j", 1.into(), &["i"], &[]);
    provider.add_package("k", 1.into(), &["i"], &[]);
    provider.add_package("l", 1.into(), &["j", "k"], &[]);

    let requirements = provider.requirements(&["a 0..10", "e"]);
    let constraints = provider.version_sets(&["b 1..2", "c", "k 2..3"]);

    let extra_solvables = [
        provider.solvable_id("d", 1),
        provider.solvable_id("g", 1),
        provider.solvable_id("h", 1),
        provider.solvable_id("j", 1),
        provider.solvable_id("l", 1),
        provider.solvable_id("k", 1),
    ];

    let mut solver = Solver::new(provider);

    let problem = Problem::new()
        .requirements(requirements)
        .constraints(constraints)
        .soft_requirements(extra_solvables);

    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
        a=1
        b=1
        c=1
        e=1
        h=1
        i=1
        j=1
        "###);
}

#[test]
fn test_snapshot() {
    let provider = BundleBoxProvider::from_packages(&[
        ("menu", 15, vec!["dropdown 2..3"]),
        ("menu", 10, vec!["dropdown 1..2"]),
        ("dropdown", 2, vec!["icons 2"]),
        ("dropdown", 1, vec!["intl 3; if menu"]),
        ("icons", 2, vec![]),
        ("icons", 1, vec![]),
        ("intl", 5, vec![]),
        ("intl", 3, vec![]),
    ]);

    let menu_name_id = provider.package_name("menu");

    let snapshot = provider.into_snapshot();

    #[cfg(feature = "serde")]
    serialize_snapshot(&snapshot, "snapshot_pubgrub_menu.json");

    let mut snapshot_provider = snapshot.provider();
    let menu_req = snapshot_provider
        .add_package_requirement(menu_name_id, "*")
        .into();

    assert_snapshot!(solve_for_snapshot(snapshot_provider, &[menu_req], &[]));
}

/// The snapshot's *highest-index* version set must remain resolvable through a
/// [`resolvo::snapshot::SnapshotProvider`]. The provider used to route any
/// index `>= Mapping::max()` to the additional version sets added via
/// `add_package_requirement`, but `max()` is the highest inserted index (not a
/// count), so the snapshot's last version set was shadowed by the first
/// additional one, panicking with an out-of-bounds index when no additional
/// set existed, and silently resolving to the wrong version set otherwise.
#[test]
fn test_snapshot_highest_version_set_not_shadowed() {
    let provider = BundleBoxProvider::from_packages(&[("a", 1, vec!["b 1"]), ("b", 1, vec![])]);

    let a_name_id = provider.package_name("a");
    let snapshot = provider.into_snapshot();

    let mut snapshot_provider = snapshot.provider();
    let a_req = snapshot_provider
        .add_package_requirement(a_name_id, "*")
        .into();

    // Solving must resolve `b 1`, the highest-index version set in the
    // snapshot, to pull in `b`. With the shadowing bug the lookup either
    // panicked or resolved to the additional `a *` set, dropping `b`.
    assert_snapshot!(solve_for_snapshot(snapshot_provider, &[a_req], &[]), @r###"
    a=1
    b=1
    "###);
}

#[test]
fn test_snapshot_union_requirements() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("icons", 2, vec![]),
        ("icons", 1, vec![]),
        ("intl", 5, vec![]),
        ("intl", 3, vec![]),
        ("union", 1, vec!["icons 2 | intl"]),
    ]);

    let requirements = provider.requirements(&["intl", "union"]);

    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]));
}

#[test]
fn test_union_empty_requirements() {
    let provider = BundleBoxProvider::from_packages(&[("a", 1, vec!["b 1 | c"]), ("b", 1, vec![])]);

    let result = solve_snapshot(provider, &["a"]);
    assert_snapshot!(result, @r"
    a=1
    b=1
    ");
}

#[test]
fn test_root_constraints() {
    let mut provider =
        BundleBoxProvider::from_packages(&[("icons", 1, vec![]), ("union", 1, vec!["icons"])]);

    let requirements = provider.requirements(&["union"]);
    let constraints = provider.version_sets(&["union 5"]);

    assert_snapshot!(solve_for_snapshot(provider, &requirements, &constraints));
}

#[test]
fn test_explicit_root_requirements() {
    let mut provider = BundleBoxProvider::from_packages(&[
        // `a` depends transitively on `b`
        ("a", 1, vec!["b"]),
        // `b` depends on `c`, but the highest version of `b` constrains `c` to `<2`.
        ("b", 1, vec!["c"]),
        ("b", 2, vec!["c 1..2"]),
        // `c` has more versions than `b`, so the heuristic will most likely pick `b` first.
        ("c", 1, vec![]),
        ("c", 2, vec![]),
        ("c", 3, vec![]),
        ("c", 4, vec![]),
        ("c", 5, vec![]),
    ]);

    // We require both `a` and `c` explicitly. The expected outcome will be that we
    // get the highest versions of `a` and `c` and a lower version of `b`.
    let requirements = provider.requirements(&["a", "c"]);

    let mut solver = Solver::new(provider);
    let problem = Problem::default().requirements(requirements);
    let solved = solver.solve(problem).unwrap();

    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    a=1
    b=1
    c=5
    "###);
}

#[test]
fn test_conditional_requirements() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["baz; if bar"]),
        ("bar", 1, vec![]),
        ("baz", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=1
    baz=1
    foo=1
    "###);
}

#[test]
fn test_conditional_unsolvable() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["baz 2; if bar"]),
        ("bar", 1, vec![]),
        ("baz", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    foo * cannot be installed because there are no viable options:
    └─ foo 1 would require
       └─ baz >=2, <3, for which no candidates were found.
    The following packages are incompatible
    └─ bar * can be installed with any of the following options:
       └─ bar 1
    "###);
}

#[test]
fn test_conditional_unsolvable_without_condition() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec![]),
        ("foo", 2, vec!["baz 2; if bar"]), /* This will not be selected because baz 2 conflicts
                                            * with the requirement. */
        ("bar", 1, vec![]),
        ("baz", 1, vec![]),
        ("baz", 2, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar", "baz 1"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=1
    baz=1
    foo=1
    "###);
}

#[test]
fn test_conditional_requirements_version_set() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["baz; if bar 1"]),
        ("bar", 1, vec![]),
        ("bar", 2, vec![]),
        ("baz", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=2
    foo=1
    "###);
}

#[test]
fn test_conditional_and() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["icon; if bar and baz"]),
        ("bar", 1, vec![]),
        ("bar", 2, vec![]),
        ("baz", 1, vec![]),
        ("icon", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar", "baz"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=2
    baz=1
    foo=1
    icon=1
    "###);
}

#[test]
fn test_conditional_and_mismatch() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["icon; if bar and baz"]),
        ("bar", 1, vec![]),
        ("baz", 1, vec![]),
        ("icon", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=1
    foo=1
    "###);
}

#[test]
fn test_conditional_or() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["icon; if bar or baz"]),
        ("bar", 1, vec![]),
        ("baz", 1, vec![]),
        ("icon", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=1
    foo=1
    icon=1
    "###);
}

#[test]
fn test_conditional_complex() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["icon; if bar and baz or menu"]),
        ("bar", 1, vec![]),
        ("baz", 1, vec![]),
        ("icon", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar", "baz"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=1
    baz=1
    foo=1
    icon=1
    "###);
}

#[test]
#[traced_test]
fn test_condition_missing_requirement() {
    let mut provider =
        BundleBoxProvider::from_packages(&[("menu", 1, vec!["bla; if intl"]), ("intl", 1, vec![])]);

    let requirements = provider.requirements(&["menu"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @"menu=1");
}

// ---------------------------------------------------------------------------
// Lazy conditional candidate loading
// ---------------------------------------------------------------------------
//
// The tests below cover the edge cases of the lazy-conditional-candidates
// mechanism: deferred requirements should only fetch the gated packages once
// the condition actually fires, multi-disjunct conditions should fire
// per-disjunct, deferral must survive backtracking, etc.

/// The conditional requirement's "if C" gate never fires, so the gated package
/// `bla` (and its dependency `dep`) should never have its candidates fetched.
#[test]
#[traced_test]
fn test_lazy_conditional_skips_unreached_candidates() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["bla; if bar"]),
        ("bla", 1, vec!["dep"]),
        ("dep", 1, vec![]),
        ("bar", 1, vec![]),
    ]);

    // We do *not* require `bar`, so the condition `if bar` never fires.
    let requirements = provider.requirements(&["foo"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @"foo=1");

    let fetched = solver.provider().requested_package_names();
    assert!(
        !fetched.iter().any(|name| name == "bla"),
        "expected `bla` to remain unfetched, got {fetched:?}"
    );
    assert!(
        !fetched.iter().any(|name| name == "dep"),
        "expected `dep` to remain unfetched, got {fetched:?}"
    );
}

/// When the condition fires the deferred clause is encoded and the gated
/// package is fetched. Sanity check that the eager observable behaviour still
/// produces the right solution.
#[test]
#[traced_test]
fn test_lazy_conditional_fires_when_condition_holds() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["bla; if bar"]),
        ("bla", 1, vec![]),
        ("bar", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "bar"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=1
    bla=1
    foo=1
    "###);
}

/// `a OR b` is a multi-disjunct condition. Firing only `a` should still
/// produce a correct solution: the `a`-disjunct's clause is encoded when `a`
/// is selected, and the `b`-disjunct stays deferred (and is never needed).
#[test]
#[traced_test]
fn test_lazy_conditional_multi_disjunct_fires_per_disjunct() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["bla; if a or b"]),
        ("bla", 1, vec![]),
        ("a", 1, vec![]),
        ("b", 1, vec![]),
    ]);

    // Only require `a`, not `b`. The disjunct gated on `a` must fire so that
    // `bla` is included.
    let requirements = provider.requirements(&["foo", "a"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    a=1
    bla=1
    foo=1
    "###);
}

/// Multiple `requires ... if C` for the same condition should all be encoded
/// when `C` fires. This exercises the "Multiple conditional requirements share
/// the same `ConditionId`" edge case.
#[test]
#[traced_test]
fn test_lazy_conditional_shared_condition_fires_all() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["bla; if cond", "ext; if cond"]),
        ("bla", 1, vec![]),
        ("ext", 1, vec![]),
        ("cond", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "cond"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bla=1
    cond=1
    ext=1
    foo=1
    "###);
}

/// When the condition fires *and* the requirement is unsolvable, the solver
/// must report the conflict, not panic and not loop forever.
#[test]
#[traced_test]
fn test_lazy_conditional_late_arriving_conflict_is_reported() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["bla 2; if bar"]),
        ("bar", 1, vec![]),
        ("bla", 1, vec![]),
    ]);

    // The condition `if bar` will fire because we require `bar`; the gated
    // requirement asks for `bla 2` but only `bla 1` exists, so the resolution
    // is unsolvable.
    let requirements = provider.requirements(&["foo", "bar"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    foo * cannot be installed because there are no viable options:
    └─ foo 1 would require
       └─ bla >=2, <3, for which no candidates were found.
    The following packages are incompatible
    └─ bar * can be installed with any of the following options:
       └─ bar 1
    "###);
}

/// Force backtracking through a deferred conditional requirement: `b 1` forces
/// `cond`, which fires the deferred `bla; if cond`. Then the solver finds a
/// conflict on `bla 2` and must backtrack. After backtracking it picks `b 2`
/// (which does not force `cond`), and the deferred clause is *already*
/// encoded (clauses are not unlearnt). The solver must still find a solution
/// and must not encode the deferred clause twice.
#[test]
#[traced_test]
fn test_lazy_conditional_survives_backtracking() {
    // Force the solver down a path that fires the deferred condition and
    // then backtracks:
    //
    // - root requires `foo` and `cond`. `cond` is required unconditionally
    //   so the condition `if cond` is guaranteed to fire.
    // - `foo` has two versions; the higher (`foo=2`) carries `bla 2`
    //   (no candidate -> conflict) in addition to the deferred `bla; if
    //   cond`. The conflict is only discovered after the deferred clause
    //   fires and forces a `bla` selection.
    // - After backtracking the solver settles on `foo=1`, which only has
    //   the deferred `bla; if cond` requirement. The deferred clause is
    //   reused from the failed branch (CDCL does not unlearn clauses).
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 2, vec!["bla; if cond", "bla 2"]),
        ("foo", 1, vec!["bla; if cond"]),
        ("bla", 1, vec![]),
        ("cond", 1, vec![]),
    ]);

    let requirements = provider.requirements(&["foo", "cond"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    bla=1
    cond=1
    foo=1
    "###);

    // The `if cond` disjunct fired (cond is required), so the deferred
    // entry was drained. The map must be empty even though the solve went
    // through a conflict + backtrack on `foo=2`. A future regression that
    // accidentally re-enqueues an entry on backtrack would leave a
    // leftover here -- this is the observable hook for the "remove on
    // first fire" invariant.
    assert_eq!(
        solver.deferred_requirements_count(),
        0,
        "deferred entries must be drained on first fire and never re-added"
    );

    // Resolve the exact same problem on a fresh solver and record its
    // clause count. The lazy path is deterministic, so a re-solve from
    // scratch produces the same clauses. If the original solve's
    // backtracking accidentally caused a double-encode of any deferred
    // clause, its clause count would be higher than the fresh re-solve's.
    let fresh_clauses = {
        let mut provider = BundleBoxProvider::from_packages(&[
            ("foo", 2, vec!["bla; if cond", "bla 2"]),
            ("foo", 1, vec!["bla; if cond"]),
            ("bla", 1, vec![]),
            ("cond", 1, vec![]),
        ]);
        let requirements = provider.requirements(&["foo", "cond"]);
        let mut fresh_solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let _ = fresh_solver.solve(problem).unwrap();
        fresh_solver.clause_count()
    };
    assert_eq!(
        solver.clause_count(),
        fresh_clauses,
        "clause count must match a fresh re-solve; a mismatch would mean a \
         deferred entry was encoded more than once"
    );
}

/// Regression test for the lazy-conditional prefetch path: a candidate of a
/// deferred requirement can already be decided *false* by the time the
/// condition fires. `c`'s constraint `gated 2..3` propagates `gated=1` to
/// false as soon as `c` is installed. When `cond` is later installed, the
/// deferred `gated; if cond` fires and the encoder loads the `gated`
/// candidates, prefetching their dependencies (the provider hints that they
/// are cheaply available). Encoding `gated=1`'s requires/constrains clauses
/// while `gated=1` is false used to trip the
/// `assert_ne!(.., Some(false))` in `WatchedLiterals::constrains` (pairwise
/// encoding) and `WatchedLiterals::constrains_parent` (shared encoding). The
/// clauses must be added rather than skipped: the false assignment can be
/// backtracked later, and neither the drained deferred entry nor the
/// prefetched solvable is ever revisited.
#[test]
#[traced_test]
fn test_lazy_conditional_prefetches_forbidden_candidate() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["gated; if cond"]),
        ("trigger", 1, vec!["cond"]),
        ("cond", 1, vec![]),
        ("gated", 2, vec![]),
        ("dep", 1, vec![]),
        ("z", 1, vec![]),
        ("w", 1, vec![]),
        ("w", 2, vec![]),
        ("w", 3, vec![]),
        ("w", 4, vec![]),
    ]);
    provider.hint_dependencies_available = true;
    // Installing `c` forbids `gated=1` through a constraint.
    provider.add_package("c", 1.into(), &[], &["gated 2..3"]);
    // `gated=1` carries a requirement and two constraints so that the
    // requires path and both constrains encodings run with a false parent:
    // `z 2..3` excludes a single candidate (pairwise `Constrains`), while
    // `w 5..6` excludes four candidates (shared `ConstrainsParent` encoding).
    provider.add_package("gated", 1.into(), &["dep"], &["z 2..3", "w 5..6"]);

    let requirements = provider.requirements(&["c", "a", "trigger"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    a=1
    c=1
    cond=1
    gated=2
    trigger=1
    "###);
}

/// `condition: None` requirements must continue to behave eagerly: the gated
/// package should be fetched even though we never decide on it. This is the
/// existing behaviour, kept here as a regression guard.
#[test]
#[traced_test]
fn test_lazy_conditional_unconditional_unaffected() {
    let mut provider =
        BundleBoxProvider::from_packages(&[("foo", 1, vec!["bla"]), ("bla", 1, vec![])]);

    let requirements = provider.requirements(&["foo"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    bla=1
    foo=1
    "###);

    let fetched = solver.provider().requested_package_names();
    assert!(
        fetched.iter().any(|name| name == "bla"),
        "unconditional requirements must still fetch their candidates; got {fetched:?}"
    );
}

/// Empty-complement condition: `if bar` is `bar *`, whose complement is
/// always empty (every candidate of `bar` matches `*`). The encoder relies
/// on the at-least-one tracker for `bar` to gate the requires clause. The
/// deferred path must agree with that semantics: the condition holds iff
/// any candidate of `bar` is selected.
#[test]
#[traced_test]
fn test_lazy_conditional_empty_complement_fires() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("foo", 1, vec!["bla; if bar"]),
        // Multiple versions of bar: the VS `bar *` still matches all of
        // them, so its complement is empty.
        ("bar", 1, vec![]),
        ("bar", 2, vec![]),
        ("bla", 1, vec![]),
    ]);

    // With `bar` requested, the condition fires and the deferred clause is
    // encoded.
    let requirements = provider.requirements(&["foo", "bar"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=2
    bla=1
    foo=1
    "###);
}

/// Determinism: running the same problem ten times must produce the exact
/// same solution. The deferred-requirement drain order must not depend on
/// hash iteration.
#[test]
fn test_lazy_conditional_determinism() {
    fn build_provider() -> BundleBoxProvider {
        BundleBoxProvider::from_packages(&[
            ("foo", 1, vec!["bla; if a", "ext; if b"]),
            ("foo", 2, vec!["bla; if a", "ext; if b"]),
            ("bla", 1, vec![]),
            ("ext", 1, vec![]),
            ("a", 1, vec![]),
            ("b", 1, vec![]),
        ])
    }

    let baseline = {
        let mut provider = build_provider();
        let requirements = provider.requirements(&["foo", "a", "b"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        transaction_to_string(solver.provider(), &solved)
    };

    for _ in 0..9 {
        let mut provider = build_provider();
        let requirements = provider.requirements(&["foo", "a", "b"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        assert_eq!(result, baseline, "non-deterministic solve");
    }
}

/// Multi-conjunct (`a AND b`) condition. `convert_conditions_to_dnf`
/// distributes AND over OR, so `cond_a AND cond_b` becomes a single disjunct
/// with two conjuncts. The lazy path's `condition_disjunct_holds` only fires
/// when *every* conjunct in the disjunct holds.
///
/// Existing tests cover only single-conjunct disjuncts (`if x` or `if x or
/// y`), leaving the `disjunct.iter().all(...)` arm of
/// `condition_disjunct_holds` unexercised. This test fixes that gap with
/// three sub-cases sharing the same fixture but with different root
/// requirements.
mod test_lazy_conditional_multi_conjunct_requires_all {
    use super::*;

    fn build_provider() -> BundleBoxProvider {
        BundleBoxProvider::from_packages(&[
            ("a", 1, vec!["b; if cond_a and cond_b"]),
            ("b", 1, vec![]),
            ("cond_a", 1, vec![]),
            ("cond_b", 1, vec![]),
        ])
    }

    /// Neither conjunct fires. `b` must not be in the resolution and must
    /// not have its candidates fetched.
    #[test]
    #[traced_test]
    fn neither_selected() {
        let mut provider = build_provider();
        let requirements = provider.requirements(&["a"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        assert_snapshot!(result, @"a=1");

        let fetched = solver.provider().requested_package_names();
        assert!(
            !fetched.iter().any(|n| n == "b"),
            "expected `b` to remain unfetched when neither conjunct holds, \
             got {fetched:?}"
        );
        assert_eq!(
            solver.deferred_requirements_count(),
            1,
            "the AND-disjunct never held, its deferred entry must remain"
        );
    }

    /// Only the first conjunct fires. `b` must not be in the resolution and
    /// must not have its candidates fetched: the lazy path requires *every*
    /// conjunct of the AND-disjunct to hold.
    #[test]
    #[traced_test]
    fn only_first_selected() {
        let mut provider = build_provider();
        let requirements = provider.requirements(&["a", "cond_a"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        assert_snapshot!(result, @r###"
        a=1
        cond_a=1
        "###);

        let fetched = solver.provider().requested_package_names();
        assert!(
            !fetched.iter().any(|n| n == "b"),
            "expected `b` to remain unfetched when only one conjunct holds, \
             got {fetched:?}"
        );
        assert_eq!(
            solver.deferred_requirements_count(),
            1,
            "second conjunct (cond_b) did not hold, deferred entry must remain"
        );
    }

    /// Both conjuncts fire. `b` must be in the resolution.
    #[test]
    #[traced_test]
    fn both_selected() {
        let mut provider = build_provider();
        let requirements = provider.requirements(&["a", "cond_a", "cond_b"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        assert_snapshot!(result, @r###"
        a=1
        b=1
        cond_a=1
        cond_b=1
        "###);

        assert_eq!(
            solver.deferred_requirements_count(),
            0,
            "both conjuncts hold, the deferred entry must have been drained"
        );
    }
}

/// Determinism under non-deterministic async ordering. The plain
/// [`test_lazy_conditional_determinism`] uses the default
/// `sleep_before_return = false`, so every `get_candidates` future resolves
/// synchronously and ordering is trivially deterministic. This test enables
/// `sleep_before_return = true` so each provider call awaits a 10 ms timer
/// inside the tokio runtime, forcing the `FuturesUnordered` driving the
/// encoder to actually interleave futures.
///
/// We then assert that across 10 runs of the same problem:
/// - the resolution (the solvables list) is byte-identical, and
/// - the sorted set of packages whose candidates were fetched
///   (`requested_package_names`) is byte-identical.
///
/// The second assertion is the load-bearing one for this test: it guards the
/// deferred-requirement drain order. A regression that drains
/// `SolverState::deferred_requirements` by hash iteration would still yield
/// the same final resolution (CDCL is deterministic given the same input
/// clauses) but the *order* in which conditional packages get fetched would
/// drift, observable here as differing `requested_package_names`.
#[test]
fn test_lazy_conditional_determinism_async() {
    fn build_provider() -> BundleBoxProvider {
        let mut p = BundleBoxProvider::from_packages(&[
            // Multiple deferred conditional requirements sharing distinct
            // conditions, plus an inner conditional on `bla` that only
            // fires once `a` is selected. The graph is non-trivial enough
            // that a buggy drain order would surface.
            ("foo", 1, vec!["bla; if a", "ext; if b", "tail; if c"]),
            ("foo", 2, vec!["bla; if a", "ext; if b", "tail; if c"]),
            ("bla", 1, vec!["inner; if a"]),
            ("ext", 1, vec![]),
            ("tail", 1, vec![]),
            ("inner", 1, vec![]),
            ("a", 1, vec![]),
            ("b", 1, vec![]),
            ("c", 1, vec![]),
        ]);
        // Force every provider future to await a real timer so the encoder's
        // `FuturesUnordered` driver actually has to interleave them.
        p.sleep_before_return = true;
        p
    }

    fn run() -> (String, Vec<String>) {
        let runtime = tokio::runtime::Builder::new_current_thread()
            .enable_time()
            .build()
            .unwrap();
        let mut provider = build_provider();
        let requirements = provider.requirements(&["foo", "a", "b", "c"]);
        let mut solver = Solver::new(provider).with_runtime(runtime);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        let mut fetched = solver.provider().requested_package_names();
        // Sort so the assertion targets the *set* of fetched packages,
        // which is what determinism guarantees -- the *insertion* order
        // into the underlying HashSet is hash-randomised and not part of
        // the solver's contract.
        fetched.sort();
        (result, fetched)
    }

    let baseline = run();
    for i in 0..9 {
        let next = run();
        assert_eq!(
            next.0, baseline.0,
            "non-deterministic resolution under async ordering at iteration {i}"
        );
        assert_eq!(
            next.1, baseline.1,
            "non-deterministic fetched-packages set under async ordering at \
             iteration {i}"
        );
    }
}

/// Pin the observable semantic divergence between the lazy-conditional path
/// and the prior eager SAT encoding.
///
/// Setup: `cond` has versions `1` and `2`. The condition VS `cond 2..3` matches
/// only `cond=2`; its complement is `{cond=1}`. We externally exclude `cond=1`
/// so the *complement* is fully decided-false, while *nothing* positively
/// selects `cond=2`. The conditional requirement is `a` requires `b` if
/// `cond>=2`.
///
/// Behaviour comparison:
/// - **Eager (legacy) path**: emits the SAT clause `¬a v ¬C!1 v b1` (where
///   `C!1` is the complement candidate `cond=1`). With `cond=1` excluded
///   (decided false), `¬C!1` is satisfied, so the clause forces `b1`. `b`
///   would appear in the resolution.
/// - **Lazy path (current implementation)**: `condition_disjunct_holds`
///   checks whether any **matching** candidate of the condition VS is
///   positively decided. `cond=2` is never positively decided here, so the
///   disjunct never holds and the deferred requirement never gets encoded.
///   `b` is therefore absent from the resolution.
///
/// The lazy semantics align with what a human would expect from "if `cond>=2`
/// is selected": exclusion of `cond=1` is not the same as selection of
/// `cond=2`.
///
/// This test pins the lazy behaviour so any future regression that re-derives
/// the eager semantics fails loudly.
#[test]
#[traced_test]
fn test_lazy_conditional_externally_excluded_complement_does_not_fire() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 1, vec!["b; if cond 2..3"]),
        ("b", 1, vec![]),
        ("cond", 1, vec![]),
        ("cond", 2, vec![]),
    ]);
    // Externally reject the *complement* candidate `cond=1`. Nothing forces
    // `cond=2` to be selected; the only requirement is on `a`.
    provider.exclude("cond", 1, "it is externally excluded");

    let requirements = provider.requirements(&["a"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);

    // `b` must NOT appear in the resolution: the lazy path correctly sees
    // that `cond=2` (the *matching* candidate of `cond 2..3`) is never
    // positively decided, so the deferred requirement never fires. The
    // legacy eager path would have included `b` here -- see the doc-comment
    // above for the contrast.
    assert_snapshot!(result, @"a=1");

    // The deferred entry must still be sitting in the map (its disjunct
    // never held), confirming the lazy path's predicate is what kept `b`
    // out -- not some unrelated reason like `a` being uninstallable.
    assert_eq!(
        solver.deferred_requirements_count(),
        1,
        "the `if cond 2..3` disjunct never fired, so its deferred entry \
         must remain"
    );
}

#[cfg(feature = "serde")]
fn serialize_snapshot(
    snapshot: &resolvo::snapshot::DependencySnapshot,
    destination: impl AsRef<std::path::Path>,
) {
    let file = std::io::BufWriter::new(std::fs::File::create(destination.as_ref()).unwrap());
    serde_json::to_writer_pretty(file, snapshot).unwrap()
}

fn solve_for_snapshot<D: DependencyProvider<NameId = resolvo::NameId, SolvableId = SolvableId>>(
    provider: D,
    root_reqs: &[ConditionalRequirement],
    root_constraints: &[VersionSetId],
) -> String {
    let mut solver = Solver::new(provider);
    let problem = Problem::new()
        .requirements(root_reqs.to_vec())
        .constraints(root_constraints.to_vec());
    match solver.solve(problem) {
        Ok(solvables) => transaction_to_string(solver.provider(), &solvables),
        Err(UnsolvableOrCancelled::Unsolvable(conflict)) => {
            // Write the conflict graphviz to stderr
            let graph = conflict.graph(&solver);
            let mut output = stderr();
            writeln!(output, "UNSOLVABLE:").unwrap();
            graph
                .graphviz(&mut output, solver.provider(), true)
                .unwrap();
            writeln!(output, "\n").unwrap();

            // Format a user friendly error message
            conflict.display_user_friendly(&solver).to_string()
        }
        Err(UnsolvableOrCancelled::Cancelled(reason)) => *reason.downcast().unwrap(),
    }
}

// ============================================================================
// Constraint edge case tests
// ============================================================================
// These tests comprehensively cover the behavior of Constrains clauses
// (i.e. "if A is installed, B must NOT be installed") in both directions
// and various edge cases involving backtracking.

/// Forward direction: parent is installed, its constraint forbids certain versions
/// of another package. The solver should pick a compatible version.
/// Constraint spec "b 3..100" means b must be in [3,100). Versions outside that range are forbidden.
#[test]
fn test_constrains_forward_basic() {
    let mut provider = BundleBoxProvider::new();
    // a requires b and constrains b to >= 3 (forbids b=1, b=2)
    provider.add_package("a", 1.into(), &["b"], &["b 3..100"]);
    provider.add_package("b", 1.into(), &[], &[]);
    provider.add_package("b", 2.into(), &[], &[]);
    provider.add_package("b", 3.into(), &[], &[]);
    provider.add_package("b", 4.into(), &[], &[]);

    let requirements = provider.requirements(&["a"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    // b=4 is the highest version in the allowed range [3,100)
    assert_snapshot!(result, @r###"
    a=1
    b=4
    "###);
}

/// Forward direction: parent constrains away ALL versions of a dependency
/// by specifying an empty allowed range.
#[test]
fn test_constrains_forward_all_forbidden() {
    let mut provider = BundleBoxProvider::new();
    // a requires b but its constraint of [100,200) excludes every available version
    provider.add_package("a", 1.into(), &["b"], &["b 100..200"]);
    provider.add_package("b", 1.into(), &[], &[]);
    provider.add_package("b", 2.into(), &[], &[]);

    let error = solve_unsat(provider, &["a"]);
    assert_snapshot!(error);
}

/// Reverse direction: b=2 is forced by `x`, then `a=3` which constrains b
/// to >= 3 can't be used (b=2 is outside [3,100)), so solver falls back to `a=2`.
#[test]
fn test_constrains_reverse_direction() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("x", 1.into(), &["b 2..3"], &[]);
    provider.add_package("b", 1.into(), &[], &[]);
    provider.add_package("b", 2.into(), &[], &[]);
    provider.add_package("b", 3.into(), &[], &[]);
    provider.add_package("a", 2.into(), &[], &[]);
    // a=3 constrains b to [3,100), so b=1 and b=2 are forbidden
    provider.add_package("a", 3.into(), &[], &["b 3..100"]);

    let requirements = provider.requirements(&["x", "a"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    // b=2 forced by x, a=3 incompatible, falls back to a=2
    assert_snapshot!(result, @r###"
    a=2
    b=2
    x=1
    "###);
}

/// Reverse direction unsolvable: forced version conflicts with only parent version.
#[test]
fn test_constrains_reverse_unsat() {
    let mut provider = BundleBoxProvider::new();
    // x forces b=1
    provider.add_package("x", 1.into(), &["b 1..2"], &[]);
    provider.add_package("b", 1.into(), &[], &[]);
    provider.add_package("b", 2.into(), &[], &[]);
    // a constrains b to [2,100), so b=1 is forbidden
    provider.add_package("a", 1.into(), &[], &["b 2..100"]);

    let error = solve_unsat(provider, &["x", "a"]);
    assert_snapshot!(error);
}

/// Constraint with no version of constrained package selected.
/// The constraint should have no effect since the package isn't needed.
#[test]
fn test_constrains_no_version_selected() {
    let mut provider = BundleBoxProvider::new();
    // a constrains b to [100,200), forbidding all existing b versions
    // but nothing requires b, so constraint is irrelevant
    provider.add_package("a", 1.into(), &[], &["b 100..200"]);
    provider.add_package("b", 1.into(), &[], &[]);
    provider.add_package("b", 2.into(), &[], &[]);

    let requirements = provider.requirements(&["a"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    a=1
    "###);
}

/// Matching version selected: the constraint allows the selected version.
#[test]
fn test_constrains_matching_version_ok() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("x", 1.into(), &["b"], &[]);
    provider.add_package("b", 1.into(), &[], &[]);
    provider.add_package("b", 2.into(), &[], &[]);
    provider.add_package("b", 3.into(), &[], &[]);
    // a constrains b to [0,2), allowing b=1 and forbidding b=2 and b=3
    provider.add_package("a", 1.into(), &[], &["b 0..2"]);

    let requirements = provider.requirements(&["x", "a"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    // b=1 is the only version in the allowed range
    assert_snapshot!(result, @r###"
    a=1
    b=1
    x=1
    "###);
}

/// Backtracking through constraints: solver tries b=3 first, backtracks to b=1.
#[test]
fn test_constrains_backtracking() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("a", 1.into(), &["b"], &[]);
    provider.add_package("b", 1.into(), &[], &[]);
    provider.add_package("b", 2.into(), &[], &[]);
    provider.add_package("b", 3.into(), &[], &[]);
    // c constrains b to [0,2), allowing b=1 and forbidding b=2 and b=3
    provider.add_package("c", 1.into(), &[], &["b 0..2"]);

    let requirements = provider.requirements(&["a", "c"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    a=1
    b=1
    c=1
    "###);
}

/// Diamond dependency with constraints on both sides.
#[test]
fn test_constrains_diamond() {
    let mut provider = BundleBoxProvider::new();
    // a requires c and constrains c to [3,100), forbidding c=1 and c=2
    provider.add_package("a", 1.into(), &["c"], &["c 3..100"]);
    // b requires c and constrains c to [0,5), forbidding c=5
    provider.add_package("b", 1.into(), &["c"], &["c 0..5"]);
    provider.add_package("c", 1.into(), &[], &[]);
    provider.add_package("c", 2.into(), &[], &[]);
    provider.add_package("c", 3.into(), &[], &[]);
    provider.add_package("c", 4.into(), &[], &[]);
    provider.add_package("c", 5.into(), &[], &[]);

    let requirements = provider.requirements(&["a", "b"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    // c must be in [3,5) -> c=3 or c=4, highest wins
    assert_snapshot!(result, @r###"
    a=1
    b=1
    c=4
    "###);
}

/// Stress test: many versions with constraints.
#[test]
fn test_constrains_many_versions() {
    let mut provider = BundleBoxProvider::new();
    for v in 1..=50u32 {
        provider.add_package("big", v.into(), &[], &[]);
    }
    // a requires big and constrains it to [46,100), allowing 46-50 and forbidding 1-45
    provider.add_package("a", 1.into(), &["big"], &["big 46..100"]);

    let requirements = provider.requirements(&["a"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    assert_snapshot!(result, @r###"
    a=1
    big=50
    "###);
}

/// Transitive constraint: a constrains b, which transitively affects c.
#[test]
fn test_constrains_transitive() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("b", 1.into(), &["c 1..2"], &[]);
    provider.add_package("b", 2.into(), &["c 2..3"], &[]);
    provider.add_package("c", 1.into(), &[], &[]);
    provider.add_package("c", 2.into(), &[], &[]);
    provider.add_package("x", 1.into(), &["b"], &[]);
    // a constrains b to [2,100), so b=1 is forbidden
    provider.add_package("a", 1.into(), &[], &["b 2..100"]);

    let requirements = provider.requirements(&["x", "a"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    // a forbids b=1, so b=2 is selected, which requires c=2
    assert_snapshot!(result, @r###"
    a=1
    b=2
    c=2
    x=1
    "###);
}

/// The shared auxiliary-variable encoding emits the excluded candidates of a
/// constraint only once: N parents sharing a constraint over a package with M
/// excluded candidates produce M + N constrains clauses instead of N * M.
#[test]
fn test_constrains_shared_encoding_clause_count() {
    let solve_and_count = |parents: usize| {
        let mut provider = BundleBoxProvider::new();
        // All 10 versions of pkg are excluded, enough for the shared encoding.
        for v in 1..=10u32 {
            provider.add_package("pkg", v.into(), &[], &[]);
        }
        let parent_names = (0..parents).map(|i| format!("p{i}")).collect::<Vec<_>>();
        for name in &parent_names {
            provider.add_package(name, 1.into(), &[], &["pkg 11..100"]);
        }
        let requirements =
            provider.requirements(&parent_names.iter().map(String::as_str).collect::<Vec<_>>());
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        solver
            .solve(problem)
            .expect("nothing requires pkg, so the constraints are never violated");
        solver.clause_count()
    };

    // Each additional parent adds one requires clause and one parent clause;
    // the 10 excluded-candidate clauses are emitted only once.
    let single_parent = solve_and_count(1);
    let many_parents = solve_and_count(5);
    assert_eq!(many_parents - single_parent, 4 * 2);
}

/// Constraints that exclude only a few candidates keep the direct pairwise
/// encoding: every parent emits one clause per excluded candidate.
#[test]
fn test_constrains_pairwise_encoding_clause_count() {
    let solve_and_count = |parents: usize| {
        let mut provider = BundleBoxProvider::new();
        // Only 2 versions of pkg are excluded, too few for the shared encoding.
        provider.add_package("pkg", 1.into(), &[], &[]);
        provider.add_package("pkg", 2.into(), &[], &[]);
        let parent_names = (0..parents).map(|i| format!("p{i}")).collect::<Vec<_>>();
        for name in &parent_names {
            provider.add_package(name, 1.into(), &[], &["pkg 11..100"]);
        }
        let requirements =
            provider.requirements(&parent_names.iter().map(String::as_str).collect::<Vec<_>>());
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        solver
            .solve(problem)
            .expect("nothing requires pkg, so the constraints are never violated");
        solver.clause_count()
    };

    // Each additional parent adds one requires clause and one pairwise clause
    // per excluded candidate.
    let single_parent = solve_and_count(1);
    let many_parents = solve_and_count(5);
    assert_eq!(many_parents - single_parent, 4 * 3);
}

/// Like `test_unsat_constrains`, but with enough excluded candidates for the
/// constraint to use the shared auxiliary-variable encoding. The rendered
/// conflict must look exactly as if the constraint was encoded pairwise.
#[test]
fn test_unsat_constrains_shared_encoding() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 10, vec!["b 50..100"]),
        ("b", 55, vec![]),
        ("b", 54, vec![]),
        ("b", 53, vec![]),
        ("b", 52, vec![]),
        ("b", 51, vec![]),
        ("b", 50, vec![]),
        ("b", 42, vec![]),
    ]);

    provider.add_package("c", 10.into(), &[], &["b 0..50"]);
    let error = solve_unsat(provider, &["a", "c"]);
    insta::assert_snapshot!(error);
}

/// Reverse direction through the shared encoding: an installed candidate that
/// is excluded by the constraint forbids the constraint's parent.
#[test]
fn test_unsat_constrains_shared_encoding_reverse() {
    // x forces b=1, while a constrains b to [5,100) which excludes b=1..4.
    let mut provider = BundleBoxProvider::from_packages(&[
        ("x", 1, vec!["b 1..2"]),
        ("b", 1, vec![]),
        ("b", 2, vec![]),
        ("b", 3, vec![]),
        ("b", 4, vec![]),
    ]);
    provider.add_package("a", 1.into(), &[], &["b 5..100"]);
    let error = solve_unsat(provider, &["x", "a"]);
    insta::assert_snapshot!(error);
}

/// Multiple parents sharing the same constraint through the shared encoding.
#[test]
fn test_unsat_constrains_shared_encoding_multiple_parents() {
    let mut provider = BundleBoxProvider::from_packages(&[
        ("a", 10, vec!["b 50..100"]),
        ("b", 55, vec![]),
        ("b", 54, vec![]),
        ("b", 53, vec![]),
        ("b", 52, vec![]),
        ("b", 51, vec![]),
        ("b", 50, vec![]),
        ("b", 42, vec![]),
    ]);

    provider.add_package("c", 10.into(), &[], &["b 0..50"]);
    provider.add_package("d", 10.into(), &[], &["b 0..50"]);
    let error = solve_unsat(provider, &["a", "c", "d"]);
    insta::assert_snapshot!(error);
}

/// Multiple constraints from different parents on the same package.
#[test]
fn test_constrains_multiple_parents() {
    let mut provider = BundleBoxProvider::new();
    for v in 1..=8u32 {
        provider.add_package("pkg", v.into(), &[], &[]);
    }
    provider.add_package("x", 1.into(), &["pkg"], &[]);
    // a constrains pkg to [3,100), forbidding pkg=1 and pkg=2
    provider.add_package("a", 1.into(), &[], &["pkg 3..100"]);
    // b constrains pkg to [0,8), forbidding pkg=8
    provider.add_package("b", 1.into(), &[], &["pkg 0..8"]);

    let requirements = provider.requirements(&["x", "a", "b"]);
    let mut solver = Solver::new(provider);
    let problem = Problem::new().requirements(requirements);
    let solved = solver.solve(problem).unwrap();
    let result = transaction_to_string(solver.provider(), &solved);
    // pkg must be in [3,8) -> 3..7, highest = 7
    assert_snapshot!(result, @r###"
    a=1
    b=1
    pkg=7
    x=1
    "###);
}

// ============================================================================
// Decide-queue wake-up scenarios
// ============================================================================
// Each test targets a wake-up path of `solver::decide_queue`. In debug builds
// every decide() call verifies the queue's bookkeeping invariants, so these
// tests check the queue throughout the search, not just the solution.

/// Satisfied-watch break and re-satisfaction: a=2 satisfies its `x 2..3`
/// requirement with x=2, the conflict with b's `x 1..2` undoes that, and
/// after backtracking the requires clauses must become eligible again
/// (parent re-wake) and be satisfiable by x=1. The conflict also bumps x,
/// promoting queued items to the hot queue.
#[test]
fn test_decide_queue_satisfaction_break() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("x", 1.into(), &[], &[]);
    provider.add_package("x", 2.into(), &[], &[]);
    provider.add_package("a", 1.into(), &["x 1..2"], &[]);
    provider.add_package("a", 2.into(), &["x 2..3"], &[]);
    provider.add_package("b", 1.into(), &["x 1..2"], &[]);

    let requirements = provider.requirements(&["a", "b"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    a=1
    b=1
    x=1
    "###);
}

/// Backjump past a parent: mid=2 is undone by the conflict between its
/// `leaf 2..3` requirement and root's explicit `leaf 1..2`, so mid's queued
/// items become ineligible and mid=1's items must be woken afterwards.
#[test]
fn test_decide_queue_backjump_past_parent() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("leaf", 1.into(), &[], &[]);
    provider.add_package("leaf", 2.into(), &[], &[]);
    provider.add_package("mid", 1.into(), &["leaf 1..2"], &[]);
    provider.add_package("mid", 2.into(), &["leaf 2..3"], &[]);
    provider.add_package("top", 1.into(), &["mid"], &[]);

    let requirements = provider.requirements(&["top", "leaf 1..2"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    leaf=1
    mid=1
    top=1
    "###);
}

/// Condition wake-up in both polarities: the condition on `baz; if bar 2..3`
/// completes and breaks as bar flips between 2 and 1 during the conflict
/// with qux's `bar 1..2` requirement.
#[test]
fn test_decide_queue_condition_toggles() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("bar", 1.into(), &[], &[]);
    provider.add_package("bar", 2.into(), &[], &[]);
    provider.add_package("baz", 1.into(), &[], &[]);
    provider.add_package("foo", 1.into(), &["baz; if bar 2..3"], &[]);
    provider.add_package("qux", 1.into(), &["bar 1..2"], &[]);

    let requirements = provider.requirements(&["foo", "bar", "qux"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    bar=1
    foo=1
    qux=1
    "###);
}

/// Mid-solve reset: b=2's constraint on a is encoded only after a=1 is
/// already installed, which reports a conflicting clause, resets the search
/// to level 0 (clearing the decision tracker), and restarts. The queue's
/// trail mirror must survive the reset.
#[test]
fn test_decide_queue_reset_on_late_conflict() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("a", 1.into(), &[], &[]);
    provider.add_package("b", 1.into(), &[], &[]);
    provider.add_package("b", 2.into(), &[], &["a 2..3"]);

    let requirements = provider.requirements(&["a", "b"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    a=1
    b=1
    "###);
}

/// Union requirement naming the same package in several version sets: the
/// queue's name occurrence lists deduplicate the item registration.
#[test]
fn test_decide_queue_union_duplicate_name() {
    let mut provider = BundleBoxProvider::new();
    provider.add_package("x", 1.into(), &[], &[]);
    provider.add_package("x", 3.into(), &[], &[]);
    provider.add_package("a", 1.into(), &["x 0..2 | x 3..4"], &[]);
    provider.add_package("b", 1.into(), &["x 0..2"], &[]);

    let requirements = provider.requirements(&["a", "b"]);
    assert_snapshot!(solve_for_snapshot(provider, &requirements, &[]), @r###"
    a=1
    b=1
    x=1
    "###);
}

mod decide_queue_prop;

/// A generated dependency graph: `(name, version, deps)` triples plus root specs.
type GateFuzzGraph = (Vec<(String, u32, Vec<String>)>, Vec<String>);

/// A tiny xorshift RNG used to generate the shared-requires gate fuzz graphs.
struct GateFuzzRng(u64);

impl GateFuzzRng {
    fn new(seed: u64) -> Self {
        Self(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1)
    }

    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
}

/// Generates a random dependency graph as `(name, version, deps)` triples plus a
/// set of root requirements. Multi-version packages produce requirements with
/// enough candidates to be encoded behind a shared gate, the structure that
/// triggered the stranded-gate bug.
fn gen_gate_fuzz_graph(seed: u64) -> GateFuzzGraph {
    let mut r = GateFuzzRng::new(seed);
    let n = 5 + (r.next() % 6) as usize;
    let names: Vec<String> = (0..n).map(|i| format!("p{i}")).collect();
    let mut pkgs = Vec::new();
    for (i, name) in names.iter().enumerate() {
        let versions = 1 + (r.next() % 5) as u32;
        for v in 1..=versions {
            let num_deps = (r.next() % 4) as usize;
            let mut deps = Vec::new();
            for _ in 0..num_deps {
                let j = (r.next() as usize) % n;
                if j == i {
                    continue;
                }
                if r.next() % 3 == 0 {
                    let lo = 1 + (r.next() % 3) as u32;
                    let hi = lo + 1 + (r.next() % 3) as u32;
                    deps.push(format!("{} {}..{}", names[j], lo, hi));
                } else {
                    deps.push(names[j].clone());
                }
            }
            pkgs.push((name.clone(), v, deps));
        }
    }
    let num_roots = 1 + (r.next() % 3) as usize;
    let roots = (0..num_roots)
        .map(|_| names[(r.next() as usize) % n].clone())
        .collect();
    (pkgs, roots)
}

/// Checks that `sol` is a *complete* solution of `(pkgs, roots)`: every root and
/// every dependency of an installed package is satisfied by an installed
/// package.
fn validate_complete(
    pkgs: &[(String, u32, Vec<String>)],
    roots: &[String],
    sol: &[(String, u32)],
) -> Result<(), String> {
    use std::collections::HashMap;
    let chosen: HashMap<&str, u32> = sol.iter().map(|(n, v)| (n.as_str(), *v)).collect();
    let satisfied = |spec: &str| -> bool {
        let mut it = spec.split_whitespace();
        let name = it.next().unwrap();
        let Some(&cv) = chosen.get(name) else {
            return false;
        };
        match it.next() {
            None => true,
            Some(range) => {
                let mut p = range.split("..");
                let lo: u32 = p.next().unwrap().parse().unwrap();
                let hi: u32 = p.next().unwrap().parse().unwrap();
                cv >= lo && cv < hi
            }
        }
    };
    for root in roots {
        if !satisfied(root) {
            return Err(format!("root `{root}` is unsatisfied"));
        }
    }
    for (name, version) in sol {
        let deps = &pkgs
            .iter()
            .find(|(n, v, _)| n == name && v == version)
            .unwrap()
            .2;
        for dep in deps {
            if !satisfied(dep) {
                return Err(format!(
                    "{name}=={version} requires `{dep}` which is absent"
                ));
            }
        }
    }
    Ok(())
}

/// Solves `(pkgs, roots)` through the async `BundleBoxProvider` with `delay_seed`
/// (which varies the encode/backtrack interleaving). Returns the installed
/// `(name, version)` set, or `None` if the problem is reported unsatisfiable.
fn solve_gate_fuzz(
    pkgs: &[(String, u32, Vec<String>)],
    roots: &[String],
    delay_seed: u64,
) -> Option<Vec<(String, u32)>> {
    let pp: Vec<(&str, u32, Vec<&str>)> = pkgs
        .iter()
        .map(|(n, v, d)| (n.as_str(), *v, d.iter().map(String::as_str).collect()))
        .collect();
    let mut provider = BundleBoxProvider::from_packages(&pp);
    provider.sleep_before_return = true;
    provider.delay_seed = delay_seed;
    let root_specs: Vec<&str> = roots.iter().map(String::as_str).collect();
    let reqs = provider.requirements(&root_specs);
    // A seeded `delay_seed` drives ordering through cooperative polling, not
    // timers, so the runtime needs no time support.
    let rt = tokio::runtime::Builder::new_current_thread()
        .build()
        .unwrap();
    let mut solver = Solver::new(provider).with_runtime(rt);
    let solution = solver.solve(Problem::new().requirements(reqs)).ok()?;
    Some(
        solution
            .iter()
            .map(|s| {
                let display = format!("{}", solver.provider().display_solvable(*s));
                let mut it = display.split('=');
                (
                    it.next().unwrap().to_string(),
                    it.next_back().unwrap().parse().unwrap(),
                )
            })
            .collect(),
    )
}

/// Regression for the shared-requires gate (PR #246): an async-ordering
/// backtrack could strand the gate (unassign it while a requirer stayed
/// installed), silently dropping the gated requirement. This fuzzer-derived
/// graph (`p3==3` requires the gated `p7`) reproduces it across delay seeds;
/// every returned solution must be complete.
#[test]
fn shared_requires_gate_survives_backtrack() {
    let (pkgs, roots) = gen_gate_fuzz_graph(542);
    for delay_seed in 1..=12u64 {
        if let Some(sol) = solve_gate_fuzz(&pkgs, &roots, 542_000 + delay_seed) {
            validate_complete(&pkgs, &roots, &sol).unwrap_or_else(|e| {
                panic!(
                    "delay seed {} produced an incomplete solution: {e}",
                    542_000 + delay_seed
                )
            });
        }
    }
}

mod allow_multiple_versions {
    use super::*;

    /// Non-overlapping version requirements are unsolvable without `allow_multiple`.
    #[test]
    fn test_non_overlapping_requirements_unsat_without_allow_multiple() {
        let mut provider = BundleBoxProvider::new();
        provider.add_package("kernel", 1.into(), &[], &[]);
        provider.add_package("kernel", 2.into(), &[], &[]);
        provider.add_package("kernel", 3.into(), &[], &[]);
        provider.add_package("kmod-a", 1.into(), &["kernel 1..2"], &[]);
        provider.add_package("kmod-b", 1.into(), &["kernel 3..4"], &[]);

        let result = solve_unsat(provider, &["kmod-a", "kmod-b"]);
        assert_snapshot!(result);
    }

    /// When `allow_multiple` is set, non-overlapping version requirements
    /// from different dependents are solved by installing multiple versions.
    #[test]
    fn test_non_overlapping_requirements() {
        let mut provider = BundleBoxProvider::new();
        provider.add_package("kernel", 1.into(), &[], &[]);
        provider.add_package("kernel", 2.into(), &[], &[]);
        provider.add_package("kernel", 3.into(), &[], &[]);
        provider.set_allow_multiple("kernel");
        provider.add_package("kmod-a", 1.into(), &["kernel 1..2"], &[]);
        provider.add_package("kmod-b", 1.into(), &["kernel 3..4"], &[]);

        let requirements = provider.requirements(&["kmod-a", "kmod-b"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        assert_snapshot!(result, @r"
    kernel=1
    kernel=3
    kmod-a=1
    kmod-b=1
    ");
    }

    /// When dependents' version requirements overlap, each requirement independently
    /// selects its best (highest) candidate. Here kmod-a picks kernel=2 (highest in 1..3)
    /// and kmod-b picks kernel=3 (highest in 2..4), so both are installed even though
    /// kernel=2 alone would satisfy both requirements.
    ///
    /// This is actually NOT ideal - installing only kernel=2 would be optimal - but resolving
    /// overlapping ranges to a single common version would require additional optimization in
    /// the solver (e.g. soft forbid clauses or a post-solve minimization pass).
    #[test]
    fn test_overlapping_requirements() {
        let mut provider = BundleBoxProvider::new();
        provider.add_package("kernel", 1.into(), &[], &[]);
        provider.add_package("kernel", 2.into(), &[], &[]);
        provider.add_package("kernel", 3.into(), &[], &[]);
        provider.set_allow_multiple("kernel");
        provider.add_package("kmod-a", 1.into(), &["kernel 1..3"], &[]);
        provider.add_package("kmod-b", 1.into(), &["kernel 2..4"], &[]);

        let requirements = provider.requirements(&["kmod-a", "kmod-b"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        assert_snapshot!(result, @r"
    kernel=2
    kernel=3
    kmod-a=1
    kmod-b=1
    ");
    }

    /// `allow_multiple` works correctly when the multiversion package is required by a
    /// transitive dependency discovered in a later solver pass (i.e. a different
    /// Encoder invocation than the one that first processed the package's candidates).
    /// Uses two `allow_multiple` packages with version-pinned dependencies between them:
    /// each kmod version is built against a specific kernel, so installing multiple kmod
    /// versions transitively pulls in multiple kernels.
    ///
    /// The explanation may sound a bit tormented, but it exists to catch a regression
    /// encountered with the original implementation.
    #[test]
    fn test_allow_multiple_transitive() {
        let mut provider = BundleBoxProvider::new();
        provider.add_package("kernel", 1.into(), &[], &[]);
        provider.add_package("kernel", 2.into(), &[], &[]);
        provider.add_package("kernel", 3.into(), &[], &[]);
        provider.set_allow_multiple("kernel");
        provider.add_package("kmod", 1.into(), &["kernel 1..2"], &[]);
        provider.add_package("kmod", 2.into(), &["kernel 2..3"], &[]);
        provider.add_package("kmod", 3.into(), &["kernel 3..4"], &[]);
        provider.set_allow_multiple("kmod");
        provider.add_package("app-old", 1.into(), &["kmod 1..2"], &[]);
        provider.add_package("app-new", 1.into(), &["kmod 3..4"], &[]);

        let requirements = provider.requirements(&["app-old", "app-new"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new().requirements(requirements);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        assert_snapshot!(result, @r"
    app-new=1
    app-old=1
    kernel=1
    kernel=3
    kmod=1
    kmod=3
    ");
    }

    /// Soft requirements model the "already installed" scenario: the solver tries to keep
    /// each requested version, but when one is excluded the solve still succeeds with the
    /// multiple remaining versions.
    #[test]
    fn test_soft_requirements_with_allow_multiple() {
        let mut provider = BundleBoxProvider::new();
        provider.add_package("kernel", 1.into(), &[], &[]);
        provider.add_package("kernel", 2.into(), &[], &[]);
        provider.add_package("kernel", 3.into(), &[], &[]);
        provider.set_allow_multiple("kernel");
        provider.exclude("kernel", 1, "retracted due to security issue");

        let k1 = provider.solvable_id("kernel", 1u32);
        let k2 = provider.solvable_id("kernel", 2u32);
        let k3 = provider.solvable_id("kernel", 3u32);
        let requirements = provider.requirements(&["kernel"]);
        let mut solver = Solver::new(provider);
        let problem = Problem::new()
            .requirements(requirements)
            .soft_requirements(vec![k1, k2, k3]);
        let solved = solver.solve(problem).unwrap();
        let result = transaction_to_string(solver.provider(), &solved);
        assert_snapshot!(result, @r"
    kernel=2
    kernel=3
    ");
    }
}
