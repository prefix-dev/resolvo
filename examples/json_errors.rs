//! Demonstrates machine-readable error format support in resolvo
//!
//! This example shows how to:
//! 1. Handle dependency resolution errors programmatically
//! 2. Serialize errors to JSON for integration with external tools
//! 3. Use different error reporting formats
//!
//! Run with: cargo run --example json_errors --features json
//! This will create error_examples.json with the exported error data

use std::{collections::HashMap, fs};

#[cfg(feature = "json")]
use resolvo::{
    Candidates, Dependencies, DependencyProvider, HintDependenciesAvailable, Interner,
    KnownDependencies, NameId, Problem, Requirement, SolvableId, Solver, StringId,
    UnsolvableOrCancelled, VersionSetId,
};

#[cfg(feature = "json")]
#[derive(Debug)]
struct ExampleProvider;

#[cfg(feature = "json")]
impl ExampleProvider {
    fn new() -> Self {
        Self
    }
}

#[cfg(feature = "json")]
impl Interner for ExampleProvider {
    fn display_solvable(&self, _solvable: SolvableId) -> impl std::fmt::Display + '_ {
        "example-package@1.0.0"
    }

    fn display_name(&self, _name: NameId) -> impl std::fmt::Display + '_ {
        "example-package"
    }

    fn display_version_set(&self, _version_set: VersionSetId) -> impl std::fmt::Display + '_ {
        ">=1.0.0"
    }

    fn display_string(&self, _string_id: StringId) -> impl std::fmt::Display + '_ {
        "example string"
    }

    fn version_set_name(&self, _version_set: VersionSetId) -> NameId {
        NameId(0)
    }

    fn solvable_name(&self, _solvable: SolvableId) -> NameId {
        NameId(0)
    }

    fn version_sets_in_union(
        &self,
        _version_set_union: resolvo::VersionSetUnionId,
    ) -> impl Iterator<Item = VersionSetId> {
        std::iter::empty()
    }

    fn resolve_condition(&self, _condition: resolvo::ConditionId) -> resolvo::Condition {
        resolvo::Condition::Requirement(VersionSetId(0))
    }
}

#[cfg(feature = "json")]
impl DependencyProvider for ExampleProvider {
    async fn filter_candidates(
        &self,
        _candidates: &[SolvableId],
        _version_set: VersionSetId,
        _inverse: bool,
    ) -> Vec<SolvableId> {
        vec![]
    }

    async fn get_candidates(&self, _name: NameId) -> Option<Candidates> {
        Some(Candidates {
            candidates: vec![],
            favored: None,
            locked: None,
            hint_dependencies_available: HintDependenciesAvailable::None,
            excluded: vec![],
        })
    }

    async fn sort_candidates(
        &self,
        _solver: &resolvo::SolverCache<Self>,
        _solvables: &mut [SolvableId],
    ) {
    }

    async fn get_dependencies(&self, _solvable: SolvableId) -> Dependencies {
        Dependencies::Known(KnownDependencies::default())
    }
}

#[cfg(feature = "json")]
fn create_missing_dependency_error() -> (UnsolvableOrCancelled, Solver<ExampleProvider>) {
    let provider = ExampleProvider::new();
    let mut solver = Solver::new(provider);

    let problem = Problem::new().requirements(vec![Requirement::Single(VersionSetId(1)).into()]);

    match solver.solve(problem) {
        Ok(_) => panic!("Expected error for missing dependency"),
        Err(error) => (error, solver),
    }
}

fn demonstrate_json_error_serialization() -> serde_json::Value {
    #[cfg(feature = "json")]
    let mut examples: HashMap<&str, serde_json::Value> = HashMap::new();
    #[cfg(not(feature = "json"))]
    let examples: HashMap<&str, serde_json::Value> = HashMap::new();

    #[cfg(feature = "json")]
    let (error, solver) = create_missing_dependency_error();

    #[cfg(feature = "json")]
    {
        if let Ok(json) = error.to_json() {
            examples.insert(
                "unsolvable_compact",
                serde_json::from_str::<serde_json::Value>(&json).unwrap(),
            );

            if let Ok(deserialized) = UnsolvableOrCancelled::from_json(&json) {
                if !verify_lossless_conversion(&error, &deserialized) {
                    eprintln!("Warning: Lossless conversion failed for unsolvable error");
                }
            }
        }

        if let UnsolvableOrCancelled::Unsolvable(conflict) = &error {
            if let Ok(graph_json) = conflict.to_graph_json(&solver) {
                examples.insert(
                    "unsolvable_graph",
                    serde_json::from_str::<serde_json::Value>(&graph_json).unwrap(),
                );
            }
        }

        let cancelled_scenarios = vec![
            (
                "User requested cancellation during package resolution".to_string(),
                "cancelled_error",
            ),
            (
                "Operation timed out after 30 seconds".to_string(),
                "timeout_error",
            ),
            ("Network connection lost".to_string(), "network_error"),
            (
                "Insufficient memory to continue".to_string(),
                "memory_error",
            ),
        ];

        for (reason, key) in cancelled_scenarios {
            let cancelled_error = UnsolvableOrCancelled::Cancelled { reason };

            if let Ok(cancelled_json) = cancelled_error.to_json_pretty() {
                if let Ok(deserialized_cancelled) =
                    UnsolvableOrCancelled::from_json(&cancelled_json)
                {
                    if verify_lossless_conversion(&cancelled_error, &deserialized_cancelled) {
                        examples.insert(
                            key,
                            serde_json::from_str::<serde_json::Value>(&cancelled_json).unwrap(),
                        );
                    } else {
                        eprintln!("Warning: Lossless conversion failed for {}", key);
                    }
                }
            }
        }
    }

    #[cfg(not(feature = "json"))]
    {
        eprintln!("JSON feature not enabled. Run with: --features json");
    }

    serde_json::to_value(examples).unwrap()
}

/// Verifies that two UnsolvableOrCancelled errors are functionally identical
#[cfg(feature = "json")]
fn verify_lossless_conversion(
    original: &UnsolvableOrCancelled,
    deserialized: &UnsolvableOrCancelled,
) -> bool {
    match (original, deserialized) {
        (
            UnsolvableOrCancelled::Unsolvable(orig_conflict),
            UnsolvableOrCancelled::Unsolvable(deser_conflict),
        ) => orig_conflict.clause_count() == deser_conflict.clause_count(),
        (
            UnsolvableOrCancelled::Cancelled {
                reason: orig_reason,
            },
            UnsolvableOrCancelled::Cancelled {
                reason: deser_reason,
            },
        ) => orig_reason == deser_reason,
        _ => false,
    }
}

fn main() {
    let json_examples = demonstrate_json_error_serialization();

    let json_output = serde_json::json!({
        "title": "Resolvo Machine-Readable Error Examples",
        "description": "Examples of JSON-serialized error formats from resolvo dependency solver",
        "examples": json_examples
    });

    let json_string = serde_json::to_string_pretty(&json_output).unwrap();
    fs::write("examples/jsonoutput/error_examples.json", &json_string)
        .expect("Failed to write JSON file");

    println!("Examples exported to examples/jsonoutput/error_examples.json");
}
