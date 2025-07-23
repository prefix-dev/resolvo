use std::{
    fmt::{Display, Formatter},
    num::{NonZero, NonZeroU32},
};

use crate::{Interner, internal::arena::ArenaId};

/// The id associated to a package name
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct NameId(pub u32);

impl ArenaId for NameId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a generic string
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct StringId(pub u32);

impl ArenaId for StringId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a VersionSet.
#[repr(transparent)]
#[derive(Clone, Default, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct VersionSetId(pub u32);

impl ArenaId for VersionSetId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a Condition.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct ConditionId(NonZero<u32>);

impl ConditionId {
    /// Creates a new `ConditionId` from a `u32`
    pub fn new(id: u32) -> Self {
        Self::from_usize(id as usize)
    }

    /// Returns the inner `u32` value of the `ConditionId`.
    pub fn as_u32(self) -> u32 {
        self.0.get() - 1
    }
}

impl ArenaId for ConditionId {
    fn from_usize(x: usize) -> Self {
        let id = (x + 1).try_into().expect("condition id too big");
        Self(unsafe { NonZero::new_unchecked(id) })
    }

    fn to_usize(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

/// The id associated with a union (logical OR) of two or more version sets.
#[repr(transparent)]
#[derive(Clone, Default, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct VersionSetUnionId(pub u32);

impl ArenaId for VersionSetUnionId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to a solvable
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct SolvableId(pub u32);

impl ArenaId for SolvableId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl From<SolvableId> for u32 {
    fn from(value: SolvableId) -> Self {
        value.0
    }
}

#[repr(transparent)]
#[derive(Copy, Clone, PartialOrd, Ord, Eq, PartialEq, Debug, Hash)]
pub(crate) struct ClauseId(NonZeroU32);

impl ClauseId {
    /// There is a guarentee that ClauseId(1) will always be
    /// "Clause::InstallRoot". This assumption is verified by the solver.
    pub(crate) fn install_root() -> Self {
        Self(unsafe { NonZeroU32::new_unchecked(1) })
    }
}

impl ArenaId for ClauseId {
    fn from_usize(x: usize) -> Self {
        // SAFETY: Safe because we always add 1 to the index
        Self(unsafe { NonZeroU32::new_unchecked((x + 1).try_into().expect("clause id too big")) })
    }

    fn to_usize(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct LearntClauseId(u32);

impl ArenaId for LearntClauseId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to an arena of Candidates
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CandidatesId(u32);

impl ArenaId for CandidatesId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to an arena of PackageRequirements
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DependenciesId(u32);

impl ArenaId for DependenciesId {
    fn from_usize(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

/// A unique identifier for a variable in the solver.
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct VariableId(u32);

impl VariableId {
    pub fn root() -> Self {
        Self(0)
    }

    pub fn is_root(self) -> bool {
        self.0 == 0
    }
}

impl ArenaId for VariableId {
    #[inline]
    fn from_usize(x: usize) -> Self {
        Self(x.try_into().expect("variable id too big"))
    }

    #[inline]
    fn to_usize(self) -> usize {
        self.0 as usize
    }
}

impl SolvableId {
    pub(crate) fn display<I: Interner>(self, interner: &I) -> impl Display + '_ {
        DisplaySolvableId {
            interner,
            solvable_id: self,
        }
    }
}

pub(crate) struct DisplaySolvableId<'i, I: Interner> {
    interner: &'i I,
    solvable_id: SolvableId,
}

impl<I: Interner> Display for DisplaySolvableId<'_, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.interner.display_solvable(self.solvable_id))
    }
}

#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct SolvableOrRootId(u32);

impl SolvableOrRootId {
    pub fn root() -> Self {
        Self(0)
    }

    pub fn is_root(self) -> bool {
        self.0 == 0
    }

    pub fn solvable(self) -> Option<SolvableId> {
        if self.0 == 0 {
            None
        } else {
            Some(SolvableId(self.0 - 1))
        }
    }

    pub fn display<I: Interner>(self, interner: &I) -> impl Display + '_ {
        DisplaySolvableOrRootId {
            interner,
            solvable_id: self,
        }
    }
}

impl From<SolvableId> for SolvableOrRootId {
    fn from(value: SolvableId) -> Self {
        Self(
            (value.to_usize() + 1)
                .try_into()
                .expect("solvable id too big"),
        )
    }
}

pub(crate) struct DisplaySolvableOrRootId<'i, I: Interner> {
    interner: &'i I,
    solvable_id: SolvableOrRootId,
}

impl<I: Interner> Display for DisplaySolvableOrRootId<'_, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.solvable_id.solvable() {
            Some(solvable_id) => write!(f, "{}", solvable_id.display(self.interner)),
            None => write!(f, "root"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_clause_id_size() {
        // Verify that the size of a ClauseId is the same as an Option<ClauseId>.
        assert_eq!(
            std::mem::size_of::<ClauseId>(),
            std::mem::size_of::<Option<ClauseId>>()
        );
    }
}
