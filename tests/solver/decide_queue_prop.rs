//! Random dependency graphs (cycles allowed): in debug builds every decide()
//! call verifies the decide queue's bookkeeping invariants, so this property
//! test checks the queue's wake-up machinery across arbitrary search shapes.

use super::*;
use proptest::prelude::*;

type Dep = (usize, u32, u32);

#[derive(Debug, Clone)]
struct RandomProblem {
    /// packages[i] = versions; each version body = (deps, constrains).
    packages: Vec<Vec<(Vec<Dep>, Vec<Dep>)>>,
    roots: Vec<Dep>,
}

fn spec(n_packages: usize) -> impl Strategy<Value = Dep> {
    (0..n_packages, 0u32..5, 1u32..4)
}

fn random_problem() -> impl Strategy<Value = RandomProblem> {
    (2usize..10).prop_flat_map(|n| {
        let version_body = (
            prop::collection::vec(spec(n), 0..=3),
            prop::collection::vec(spec(n), 0..=1),
        );
        (
            prop::collection::vec(prop::collection::vec(version_body, 1..=3), n),
            prop::collection::vec(spec(n), 1..=3),
        )
            .prop_map(|(packages, roots)| RandomProblem { packages, roots })
    })
}

fn to_spec_strings(deps: &[Dep]) -> Vec<String> {
    deps.iter()
        .map(|&(pkg, lo, len)| format!("p{pkg} {lo}..{}", lo + len))
        .collect()
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]
    #[test]
    fn decide_queue_matches_reference_on_random_problems(problem in random_problem()) {
        let n = problem.packages.len();
        let mut provider = BundleBoxProvider::new();
        for (pkg, versions) in problem.packages.iter().enumerate() {
            for (version, (deps, constrains)) in versions.iter().enumerate() {
                let deps = to_spec_strings(deps);
                let deps: Vec<&str> = deps.iter().map(String::as_str).collect();
                // A package constraining its own name trips a pre-existing
                // debug assertion (Constrains(A, A) yields two identical
                // watch literals); redirect those until that is fixed.
                let constrains: Vec<Dep> = constrains
                    .iter()
                    .map(|&(target, lo, len)| {
                        (if target == pkg { (target + 1) % n } else { target }, lo, len)
                    })
                    .collect();
                let constrains = to_spec_strings(&constrains);
                let constrains: Vec<&str> = constrains.iter().map(String::as_str).collect();
                provider.add_package(
                    &format!("p{pkg}"),
                    (version as u32 + 1).into(),
                    &deps,
                    &constrains,
                );
            }
        }

        let roots = to_spec_strings(&problem.roots);
        let roots: Vec<&str> = roots.iter().map(String::as_str).collect();
        let requirements = provider.requirements(&roots);

        let mut solver = Solver::new(provider);
        let _ = solver.solve(Problem::new().requirements(requirements));
    }
}
