use std::{
    fmt::{Display, Formatter},
    hash::Hash,
};

use crate::{
    Condition, ConditionId,
    internal::{
        arena::Arena,
        frozen_copy_map::FrozenCopyMap,
        id::{NameId, SolvableId, StringId, VersionSetId, VersionSetUnionId},
        small_vec::SmallVec,
    },
};

/// A solvable represents a single candidate of a package.
/// This is type is generic on `V` which can be supplied by the user. In most
/// cases this is going to be something like a record that contains the version
/// of the package and other metadata. A solvable is always associated with a
/// [`NameId`], which is an interned name in the [`Pool`].
pub struct Solvable<V> {
    pub name: NameId,
    pub record: V,
}

/// A pool stores and internalizes data related to the available packages.
///
/// A pool never releases its memory until it is dropped. References returned by
/// the pool will remain valid for the lifetime of the pool. This allows
/// inserting into the pool without requiring a mutable reference to the pool.
/// This is what we refer to as `Frozen` data can be added but old data can
/// never be removed or mutated.
pub struct Pool<VS: VersionSet, N: PackageName = String> {
    /// All the solvables that have been registered
    pub(crate) solvables: Arena<SolvableId, Solvable<VS::V>>,

    /// Interned package names
    package_names: Arena<NameId, N>,

    /// Map from package names to the id of their interned counterpart
    pub(crate) names_to_ids: FrozenCopyMap<N, NameId, ahash::RandomState>,

    /// Interned strings
    strings: Arena<StringId, String>,

    /// Map from package names to the id of their interned counterpart
    pub(crate) string_to_ids: FrozenCopyMap<String, StringId, ahash::RandomState>,

    /// Interned match specs
    pub(crate) version_sets: Arena<VersionSetId, (NameId, VS)>,

    /// Map from version set to the id of their interned counterpart
    version_set_to_id: FrozenCopyMap<(NameId, VS), VersionSetId, ahash::RandomState>,

    version_set_unions: Arena<VersionSetUnionId, SmallVec<VersionSetId>>,

    /// Conditions that can be used to filter solvables.
    conditions: Arena<ConditionId, Condition>,

    /// Map from condition to its id
    condition_to_id: FrozenCopyMap<Condition, ConditionId, ahash::RandomState>,
}

impl<VS: VersionSet, N: PackageName> Default for Pool<VS, N> {
    fn default() -> Self {
        let solvables = Arena::new();

        Self {
            solvables,
            names_to_ids: Default::default(),
            package_names: Arena::new(),
            strings: Arena::new(),
            string_to_ids: Default::default(),
            version_set_to_id: Default::default(),
            version_sets: Arena::new(),
            version_set_unions: Arena::new(),
            conditions: Arena::new(),
            condition_to_id: Default::default(),
        }
    }
}

impl<VS: VersionSet, N: PackageName> Pool<VS, N> {
    /// Creates a new [`Pool`]
    pub fn new() -> Self {
        Self::default()
    }

    /// Interns a generic string into the `Pool` and returns its `StringId`.
    /// Strings are deduplicated.
    pub fn intern_string(&self, name: impl Into<String> + AsRef<str>) -> StringId {
        if let Some(id) = self.string_to_ids.get_copy(name.as_ref()) {
            return id;
        }

        let string = name.into();
        let id = self.strings.alloc(string.clone());
        self.string_to_ids.insert_copy(string, id);
        id
    }

    /// Returns the string associated with the provided [`StringId`].
    ///
    /// Panics if the string is not found in the pool.
    pub fn resolve_string(&self, string_id: StringId) -> &str {
        &self.strings[string_id]
    }

    /// Interns a package name into the `Pool`, returning its `NameId`. Names
    /// are deduplicated. If the same name is inserted twice the same
    /// `NameId` will be returned.
    ///
    /// The original name can be resolved using the
    /// [`Self::resolve_package_name`] function.
    pub fn intern_package_name<NValue>(&self, name: NValue) -> NameId
    where
        NValue: Into<N>,
        N: Clone,
    {
        let name = name.into();
        if let Some(id) = self.names_to_ids.get_copy(&name) {
            return id;
        }

        let next_id = self.package_names.alloc(name.clone());
        self.names_to_ids.insert_copy(name, next_id);
        next_id
    }

    /// Returns the package name associated with the provided [`NameId`].
    ///
    /// Panics if the package name is not found in the pool.
    pub fn resolve_package_name(&self, name_id: NameId) -> &N {
        &self.package_names[name_id]
    }

    /// Returns the [`NameId`] associated with the specified name or `None` if
    /// the name has not previously been interned using
    /// [`Self::intern_package_name`].
    pub fn lookup_package_name(&self, name: &N) -> Option<NameId> {
        self.names_to_ids.get_copy(name)
    }

    /// Adds a solvable to a repo and returns it's [`SolvableId`].
    ///
    /// Unlike some of the other interning functions this function does *not*
    /// deduplicate any of the inserted elements. A unique Id will be
    /// returned everytime this function is called.
    pub fn intern_solvable(&self, name_id: NameId, record: VS::V) -> SolvableId {
        self.solvables.alloc(Solvable {
            name: name_id,
            record,
        })
    }

    /// Returns the solvable associated to the provided id
    ///
    /// Panics if the solvable is not found in the pool
    pub fn resolve_solvable(&self, id: SolvableId) -> &Solvable<VS::V> {
        &self.solvables[id]
    }

    /// Interns a version set into the [`Pool`], returning its [`VersionSetId`].
    /// The returned [`VersionSetId`] can be used to retrieve a reference to
    /// the original version set using [`Self::resolve_version-set`].
    ///
    /// A version set is always associated with a specific package name to which
    /// it applies. The passed in package name can be retrieved using
    /// [`Self::resolve_version_set_package_name`].
    ///
    /// Version sets are deduplicated. This means that if the same version set
    /// is inserted twice they will share the same [`VersionSetId`].
    pub fn intern_version_set(&self, package_name: NameId, version_set: VS) -> VersionSetId {
        if let Some(entry) = self
            .version_set_to_id
            .get_copy(&(package_name, version_set.clone()))
        {
            entry
        } else {
            let id = self.version_sets.alloc((package_name, version_set.clone()));
            self.version_set_to_id
                .insert_copy((package_name, version_set), id);
            id
        }
    }

    /// Returns the version set associated with the provided id
    ///
    /// Panics if the version set is not found in the pool
    pub fn resolve_version_set(&self, id: VersionSetId) -> &VS {
        &self.version_sets[id].1
    }

    /// Returns the package name associated with the provide id.
    ///
    /// Panics if the version set is not found in the pool
    pub fn resolve_version_set_package_name(&self, id: VersionSetId) -> NameId {
        self.version_sets[id].0
    }

    /// Interns a union of two or more version sets and returns its
    /// [`VersionSetUnionId`].
    ///
    /// Version set unions are *not* deduplicated, and a unique id is returned
    /// on every invocation.
    pub fn intern_version_set_union(
        &self,
        first: VersionSetId,
        others: impl Iterator<Item = VersionSetId>,
    ) -> VersionSetUnionId {
        self.version_set_unions
            .alloc(others.fold(SmallVec::one(first), |mut vec, version_set| {
                vec.push(version_set);
                vec
            }))
    }

    /// Returns the version sets in the version set union with the given id.
    ///
    /// Panics if there is no union with the given id.
    pub fn resolve_version_set_union(
        &self,
        id: VersionSetUnionId,
    ) -> impl Iterator<Item = VersionSetId> + '_ {
        self.version_set_unions[id].iter().copied()
    }

    /// Resolve the condition associated with the provided id.
    pub fn resolve_condition(&self, id: ConditionId) -> &Condition {
        &self.conditions[id]
    }

    /// Interns a condition into the pool and returns its `ConditionId`.
    /// Conditions are deduplicated, so if the same condition is inserted
    /// twice the same `ConditionId` will be returned.
    pub fn intern_condition(&self, condition: Condition) -> ConditionId {
        if let Some(id) = self.condition_to_id.get_copy(&condition) {
            return id;
        }
        let id = self.conditions.alloc(condition.clone());
        self.condition_to_id.insert_copy(condition, id);
        id
    }
}

/// A helper struct to visualize a name.
pub struct NameDisplay<'pool, VS: VersionSet, N: PackageName> {
    id: NameId,
    pool: &'pool Pool<VS, N>,
}

impl<VS: VersionSet, N: PackageName + Display> Display for NameDisplay<'_, VS, N> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let name = self.pool.resolve_package_name(self.id);
        write!(f, "{}", name)
    }
}

impl NameId {
    /// Returns an object that can be used to format the name.
    pub fn display<VS: VersionSet, N: PackageName + Display>(
        self,
        pool: &Pool<VS, N>,
    ) -> NameDisplay<'_, VS, N> {
        NameDisplay { id: self, pool }
    }
}

/// The solver is based around the fact that for every package name we are
/// trying to find a single variant. Variants are grouped by their respective
/// package name. A package name is anything that we can compare and hash for
/// uniquenes checks.
///
/// For most implementations a package name can simply be a String. But in some
/// more advanced cases like when a single package can have additive features it
/// can make sense to create a custom type.
///
/// A blanket trait implementation is provided for any type that implements
/// [`Eq`] and [`Hash`].
pub trait PackageName: Eq + Hash {}

impl<N: Eq + Hash> PackageName for N {}

/// A [`VersionSet`] describes a set of "versions". The trait defines whether a
/// given version is part of the set or not.
///
/// One could implement [`VersionSet`] for [`std::ops::Range<u32>`] where the
/// implementation returns `true` if a given `u32` is part of the range or not.
pub trait VersionSet: Clone + Eq + Hash {
    /// The element type that is included in the set.
    type V: Display;
}

#[cfg(feature = "version-ranges")]
impl<R: Clone + Eq + Hash + Display> VersionSet for version_ranges::Ranges<R> {
    type V = R;
}
