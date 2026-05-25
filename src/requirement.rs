use std::fmt::Display;

use itertools::Itertools;

use crate::ConditionId;
use crate::utils::Mapping;
use crate::{ConditionalRequirement, Interner, VersionSetId, VersionSetUnionId};

/// Specifies the dependency of a solvable on a set of version sets.
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(rename_all = "snake_case"))]
pub enum Requirement {
    /// Specifies a dependency on a single version set.
    Single(VersionSetId),
    /// Specifies a dependency on the union (logical OR) of multiple version
    /// sets. A solvable belonging to _any_ of the version sets contained in
    /// the union satisfies the requirement. This variant is typically used
    /// for requirements that can be satisfied by two or more version sets
    /// belonging to _different_ packages.
    Union(VersionSetUnionId),
}

impl Requirement {
    /// Constructs a `ConditionalRequirement` from this `Requirement` and a
    /// condition.
    pub fn with_condition(self, condition: ConditionId) -> ConditionalRequirement {
        ConditionalRequirement {
            condition: Some(condition),
            requirement: self,
        }
    }
}

impl Default for Requirement {
    fn default() -> Self {
        Self::Single(Default::default())
    }
}

impl From<VersionSetId> for Requirement {
    fn from(value: VersionSetId) -> Self {
        Requirement::Single(value)
    }
}

impl From<VersionSetUnionId> for Requirement {
    fn from(value: VersionSetUnionId) -> Self {
        Requirement::Union(value)
    }
}

impl Requirement {
    /// Returns an object that implements `Display` for the requirement.
    pub fn display<'i>(&'i self, interner: &'i impl Interner) -> impl Display + 'i {
        DisplayRequirement {
            interner,
            requirement: self,
        }
    }

    pub(crate) fn version_sets<'i>(
        &'i self,
        interner: &'i impl Interner,
    ) -> impl Iterator<Item = VersionSetId> + 'i {
        match *self {
            Requirement::Single(version_set) => {
                itertools::Either::Left(std::iter::once(version_set))
            }
            Requirement::Union(version_set_union) => {
                itertools::Either::Right(interner.version_sets_in_union(version_set_union))
            }
        }
    }
}

pub(crate) struct DisplayRequirement<'i, I: Interner> {
    interner: &'i I,
    requirement: &'i Requirement,
}

/// A map keyed by [`Requirement`].
///
/// Internally splits into one [`Mapping`] per `Requirement` variant
/// ([`VersionSetId`] for `Single`, [`VersionSetUnionId`] for `Union`). Both
/// inner ID types are dense `u32` arena IDs so the chunked `Mapping`
/// representation is a good fit. The dispatch is a single branch on the
/// enum discriminant and the load is a direct vec index — much cheaper than
/// the hashed `FrozenMap` lookup it replaces on the BCP hot path.
pub(crate) struct RequirementMap<V> {
    singles: Mapping<VersionSetId, V>,
    unions: Mapping<VersionSetUnionId, V>,
}

impl<V> Default for RequirementMap<V> {
    fn default() -> Self {
        Self {
            singles: Mapping::new(),
            unions: Mapping::new(),
        }
    }
}

impl<V> RequirementMap<V> {
    #[inline]
    pub fn get(&self, key: Requirement) -> Option<&V> {
        match key {
            Requirement::Single(id) => self.singles.get(id),
            Requirement::Union(id) => self.unions.get(id),
        }
    }

    #[inline]
    pub fn insert(&mut self, key: Requirement, value: V) -> Option<V> {
        match key {
            Requirement::Single(id) => self.singles.insert(id, value),
            Requirement::Union(id) => self.unions.insert(id, value),
        }
    }
}

impl<V> std::ops::Index<Requirement> for RequirementMap<V> {
    type Output = V;

    #[inline]
    fn index(&self, key: Requirement) -> &V {
        self.get(key)
            .expect("requirement has no entry in the map")
    }
}

impl<I: Interner> Display for DisplayRequirement<'_, I> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match *self.requirement {
            Requirement::Single(version_set) => {
                let result = format!(
                    "{} {}",
                    self.interner
                        .display_name(self.interner.version_set_name(version_set)),
                    self.interner.display_version_set(version_set)
                );
                write!(f, "{}", result.trim_end())
            }
            Requirement::Union(version_set_union) => {
                let formatted_version_sets = self
                    .interner
                    .version_sets_in_union(version_set_union)
                    .format_with(" | ", |version_set, f| {
                        let result = format!(
                            "{} {}",
                            self.interner
                                .display_name(self.interner.version_set_name(version_set)),
                            self.interner.display_version_set(version_set)
                        );
                        f(&format_args!("{}", result.trim_end()))
                    });

                write!(f, "{}", formatted_version_sets)
            }
        }
    }
}
