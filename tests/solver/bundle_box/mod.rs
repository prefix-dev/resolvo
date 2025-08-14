// Let's define our own packaging version system and dependency specification.
// This is a very simple version system, where a package is identified by a name
// and a version in which the version is just an integer. The version is a range
// so can be noted as 0..2 or something of the sorts, we also support constrains
// which means it should not use that package version this is also represented
// with a range.
//
// You can also use just a single number for a range like `package 0` which
// means the range from 0..1 (excluding the end)
//
// Lets call the tuples of (Name, Version) a `Pack` and the tuples of (Name,
// Ranges<u32>) a `Spec`
//
// We also need to create a custom provider that tells us how to sort the
// candidates. This is unique to each packaging ecosystem. Let's call our
// ecosystem 'BundleBox' so that how we call the provider as well.

mod conditional_spec;
mod pack;
pub mod parser;
mod spec;

use std::{
    cell::{Cell, RefCell},
    collections::HashSet,
    fmt::Display,
    rc::Rc,
    sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    },
    time::Duration,
};

use ahash::HashMap;
pub use conditional_spec::{ConditionalSpec, SpecCondition};
use indexmap::IndexMap;
use itertools::Itertools;
pub use pack::Pack;
use resolvo::{
    Candidates, Condition, ConditionId, ConditionalRequirement, Dependencies, DependencyProvider,
    Interner, KnownDependencies, NameId, SolvableId, SolverCache, StringId, VersionSetId,
    VersionSetUnionId, snapshot::DependencySnapshot, utils::Pool,
};
pub use spec::Spec;
use version_ranges::Ranges;

/// This provides sorting functionality for our `BundleBox` packaging system
#[derive(Default)]
pub struct BundleBoxProvider {
    pub pool: Pool<Ranges<Pack>>,
    id_to_condition: Vec<SpecCondition>,
    conditions: HashMap<SpecCondition, ConditionId>,
    packages: IndexMap<String, IndexMap<Pack, BundleBoxPackageDependencies>>,
    favored: HashMap<String, Pack>,
    locked: HashMap<String, Pack>,
    excluded: HashMap<String, HashMap<Pack, String>>,
    cancel_solving: Cell<bool>,
    // TODO: simplify?
    concurrent_requests: Arc<AtomicUsize>,
    pub concurrent_requests_max: Rc<Cell<usize>>,
    pub sleep_before_return: bool,

    // A mapping of packages that we have requested candidates for. This way we can keep track of
    // duplicate requests.
    requested_candidates: RefCell<HashSet<NameId>>,
    requested_dependencies: RefCell<HashSet<SolvableId>>,
    interned_solvables: RefCell<HashMap<(NameId, Pack), SolvableId>>,
}

#[derive(Debug, Clone)]
struct BundleBoxPackageDependencies {
    dependencies: Vec<ConditionalRequirement>,
    constrains: Vec<Spec>,
}

impl BundleBoxProvider {
    pub fn new() -> Self {
        Default::default()
    }

    pub fn package_name(&self, name: &str) -> NameId {
        self.pool
            .lookup_package_name(&name.to_string())
            .expect("package missing")
    }

    pub fn intern_condition(&mut self, condition: &SpecCondition) -> ConditionId {
        if let Some(id) = self.conditions.get(&condition) {
            return *id;
        }

        if let SpecCondition::Binary(_op, sides) = condition {
            self.intern_condition(&sides[0]);
            self.intern_condition(&sides[1]);
        }

        let id = ConditionId::new(self.id_to_condition.len() as u32);
        self.id_to_condition.push(condition.clone());
        self.conditions.insert(condition.clone(), id);
        id
    }

    pub fn requirements(&mut self, requirements: &[&str]) -> Vec<ConditionalRequirement> {
        requirements
            .iter()
            .map(|dep| ConditionalSpec::from_str(*dep).unwrap())
            .map(|spec| {
                let mut iter = spec
                    .specs
                    .into_iter()
                    .map(|spec| self.intern_version_set(&spec))
                    .peekable();
                let first = iter.next().unwrap();
                let requirement = if iter.peek().is_some() {
                    self.pool.intern_version_set_union(first, iter).into()
                } else {
                    first.into()
                };

                let condition = spec.condition.map(|c| self.intern_condition(&c));

                ConditionalRequirement {
                    condition,
                    requirement,
                }
            })
            .collect()
    }

    pub fn version_sets(&mut self, requirements: &[&str]) -> Vec<VersionSetId> {
        requirements
            .iter()
            .map(|dep| Spec::from_str(*dep).unwrap())
            .map(|spec| {
                let name = self.pool.intern_package_name(&spec.name);
                self.pool.intern_version_set(name, spec.versions)
            })
            .collect()
    }

    pub fn intern_version_set(&self, spec: &Spec) -> VersionSetId {
        let dep_name = self.pool.intern_package_name(&spec.name);
        self.pool
            .intern_version_set(dep_name, spec.versions.clone())
    }

    pub fn from_packages(packages: &[(&str, u32, Vec<&str>)]) -> Self {
        let mut result = Self::new();
        for (name, version, deps) in packages {
            result.add_package(name, Pack::new(*version), deps, &[]);
        }
        result
    }

    pub fn set_favored(&mut self, package_name: &str, version: u32) {
        self.favored
            .insert(package_name.to_owned(), Pack::new(version));
    }

    pub fn exclude(&mut self, package_name: &str, version: u32, reason: impl Into<String>) {
        self.excluded
            .entry(package_name.to_owned())
            .or_default()
            .insert(Pack::new(version), reason.into());
    }

    pub fn set_locked(&mut self, package_name: &str, version: u32) {
        self.locked
            .insert(package_name.to_owned(), Pack::new(version));
    }

    pub fn add_package(
        &mut self,
        package_name: &str,
        package_version: Pack,
        dependencies: &[&str],
        constrains: &[&str],
    ) {
        self.pool.intern_package_name(package_name);

        let dependencies = self.requirements(dependencies);

        let constrains = constrains
            .iter()
            .map(|dep| Spec::from_str(dep))
            .collect::<Result<Vec<_>, _>>()
            .unwrap();

        self.packages
            .entry(package_name.to_owned())
            .or_default()
            .insert(
                package_version,
                BundleBoxPackageDependencies {
                    dependencies,
                    constrains,
                },
            );
    }

    // Sends a value from the dependency provider to the solver, introducing a
    // minimal delay to force concurrency to be used (unless there is no async
    // runtime available)
    async fn maybe_delay<T: Send + 'static>(&self, value: T) -> T {
        if self.sleep_before_return {
            tokio::time::sleep(Duration::from_millis(10)).await;
            self.concurrent_requests.fetch_sub(1, Ordering::SeqCst);
            value
        } else {
            value
        }
    }

    pub fn into_snapshot(self) -> DependencySnapshot {
        let name_ids = self
            .packages
            .keys()
            .filter_map(|name| self.pool.lookup_package_name(name))
            .collect::<Vec<_>>();
        DependencySnapshot::from_provider(self, name_ids, [], []).unwrap()
    }

    pub fn intern_solvable(&self, name_id: NameId, pack: Pack) -> SolvableId {
        *self
            .interned_solvables
            .borrow_mut()
            .entry((name_id, pack))
            .or_insert_with_key(|&(name_id, pack)| self.pool.intern_solvable(name_id, pack))
    }

    pub fn solvable_id(&self, name: impl Into<String>, version: impl Into<Pack>) -> SolvableId {
        self.intern_solvable(self.pool.intern_package_name(name.into()), version.into())
    }
}

impl Interner for BundleBoxProvider {
    fn display_solvable(&self, solvable: SolvableId) -> impl Display + '_ {
        let solvable = self.pool.resolve_solvable(solvable);
        format!("{}={}", self.display_name(solvable.name), solvable.record)
    }

    fn display_merged_solvables(&self, solvables: &[SolvableId]) -> impl Display + '_ {
        if solvables.is_empty() {
            return "".to_string();
        }

        let name = self.display_name(self.pool.resolve_solvable(solvables[0]).name);
        let versions = solvables
            .iter()
            .map(|&s| self.pool.resolve_solvable(s).record.version)
            .sorted();
        format!("{name} {}", versions.format(" | "))
    }

    fn display_name(&self, name: NameId) -> impl Display + '_ {
        self.pool.resolve_package_name(name).clone()
    }

    fn display_version_set(&self, version_set: VersionSetId) -> impl Display + '_ {
        self.pool.resolve_version_set(version_set).clone()
    }

    fn display_string(&self, string_id: StringId) -> impl Display + '_ {
        self.pool.resolve_string(string_id).to_owned()
    }

    fn version_set_name(&self, version_set: VersionSetId) -> NameId {
        self.pool.resolve_version_set_package_name(version_set)
    }

    fn solvable_name(&self, solvable: SolvableId) -> NameId {
        self.pool.resolve_solvable(solvable).name
    }
    fn version_sets_in_union(
        &self,
        version_set_union: VersionSetUnionId,
    ) -> impl Iterator<Item = VersionSetId> {
        self.pool.resolve_version_set_union(version_set_union)
    }

    fn resolve_condition(&self, condition: ConditionId) -> Condition {
        let condition = condition.as_u32();
        let condition = &self.id_to_condition[condition as usize];
        match condition {
            SpecCondition::Binary(op, items) => Condition::Binary(
                *op,
                *self.conditions.get(&items[0]).unwrap(),
                *self.conditions.get(&items[1]).unwrap(),
            ),
            SpecCondition::Requirement(requirement) => {
                Condition::Requirement(self.intern_version_set(requirement))
            }
        }
    }
}

impl DependencyProvider for BundleBoxProvider {
    async fn filter_candidates(
        &self,
        candidates: &[SolvableId],
        version_set: VersionSetId,
        inverse: bool,
    ) -> Vec<SolvableId> {
        let range = self.pool.resolve_version_set(version_set);
        candidates
            .iter()
            .copied()
            .filter(|s| range.contains(&self.pool.resolve_solvable(*s).record) == !inverse)
            .collect()
    }

    async fn sort_candidates(&self, _solver: &SolverCache<Self>, solvables: &mut [SolvableId]) {
        solvables.sort_by(|a, b| {
            let a = self.pool.resolve_solvable(*a).record;
            let b = self.pool.resolve_solvable(*b).record;
            // We want to sort with highest version on top
            b.version.cmp(&a.version)
        });
    }

    async fn get_candidates(&self, name: NameId) -> Option<Candidates> {
        let concurrent_requests = self.concurrent_requests.fetch_add(1, Ordering::SeqCst);
        self.concurrent_requests_max.set(
            self.concurrent_requests_max
                .get()
                .max(concurrent_requests + 1),
        );

        assert!(
            self.requested_candidates.borrow_mut().insert(name),
            "duplicate get_candidates request"
        );

        let package_name = self.pool.resolve_package_name(name);
        let Some(package) = self.packages.get(package_name) else {
            return self.maybe_delay(None).await;
        };

        let mut candidates = Candidates {
            candidates: Vec::with_capacity(package.len()),
            ..Candidates::default()
        };
        let favor = self.favored.get(package_name);
        let locked = self.locked.get(package_name);
        let excluded = self.excluded.get(package_name);
        for pack in package.keys() {
            let solvable = self.intern_solvable(name, *pack);
            candidates.candidates.push(solvable);
            if Some(pack) == favor {
                candidates.favored = Some(solvable);
            }
            if Some(pack) == locked {
                candidates.locked = Some(solvable);
            }
            if let Some(excluded) = excluded.and_then(|d| d.get(pack)) {
                candidates
                    .excluded
                    .push((solvable, self.pool.intern_string(excluded)));
            }
        }

        self.maybe_delay(Some(candidates)).await
    }

    async fn get_dependencies(&self, solvable: SolvableId) -> Dependencies {
        tracing::info!(
            "get dependencies for {}",
            self.pool
                .resolve_solvable(solvable)
                .name
                .display(&self.pool)
        );

        let concurrent_requests = self.concurrent_requests.fetch_add(1, Ordering::SeqCst);
        self.concurrent_requests_max.set(
            self.concurrent_requests_max
                .get()
                .max(concurrent_requests + 1),
        );

        assert!(
            self.requested_dependencies.borrow_mut().insert(solvable),
            "duplicate get_dependencies request"
        );

        let candidate = self.pool.resolve_solvable(solvable);
        let package_name = self.pool.resolve_package_name(candidate.name);
        let pack = candidate.record;

        if pack.cancel_during_get_dependencies {
            self.cancel_solving.set(true);
            let reason = self.pool.intern_string("cancelled");
            return self.maybe_delay(Dependencies::Unknown(reason)).await;
        }

        if pack.unknown_deps {
            let reason = self.pool.intern_string("could not retrieve deps");
            return self.maybe_delay(Dependencies::Unknown(reason)).await;
        }

        let Some(deps) = self.packages.get(package_name).and_then(|v| v.get(&pack)) else {
            return self
                .maybe_delay(Dependencies::Known(Default::default()))
                .await;
        };

        let mut result = KnownDependencies {
            requirements: Vec::with_capacity(deps.dependencies.len()),
            constrains: Vec::with_capacity(deps.constrains.len()),
        };
        result.requirements = deps.dependencies.clone();

        for req in &deps.constrains {
            let dep_name = self.pool.intern_package_name(&req.name);
            let dep_spec = self.pool.intern_version_set(dep_name, req.versions.clone());
            result.constrains.push(dep_spec);
        }

        self.maybe_delay(Dependencies::Known(result)).await
    }

    fn should_cancel_with_reason(&self) -> Option<String> {
        if self.cancel_solving.get() {
            Some("cancelled!".to_string())
        } else {
            None
        }
    }
}
