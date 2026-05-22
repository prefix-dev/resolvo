use std::{
    fmt::{Display, Formatter},
    num::NonZeroU32,
};

use crate::{DenseIndex, Interner, internal::solver_id::SolvableIdOrRoot};

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

impl DenseIndex for ClauseId {
    fn from_index(x: usize) -> Self {
        // SAFETY: Safe because we always add 1 to the index
        Self(unsafe { NonZeroU32::new_unchecked((x + 1).try_into().expect("clause id too big")) })
    }

    fn to_index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

#[derive(Copy, Clone, Debug)]
pub(crate) struct LearntClauseId(u32);

impl DenseIndex for LearntClauseId {
    fn from_index(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_index(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to an arena of Candidates
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct CandidatesId(u32);

impl DenseIndex for CandidatesId {
    fn from_index(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_index(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to an arena of PackageRequirements
#[repr(transparent)]
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DependenciesId(NonZeroU32);

impl DenseIndex for DependenciesId {
    fn from_index(x: usize) -> Self {
        let raw: u32 = (x + 1).try_into().expect("dependencies id too big");
        // SAFETY: `raw` is `x + 1`, hence at least 1, hence non-zero.
        Self(unsafe { NonZeroU32::new_unchecked(raw) })
    }

    fn to_index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

impl<S> SolvableIdOrRoot<S> {
    /// Returns an object that can be used to format the solvable or root id.
    pub fn display<I: Interner<SolvableId = S>>(self, interner: &I) -> impl Display + '_ {
        DisplaySolvableIdOrRoot {
            interner,
            solvable_id: self,
        }
    }
}

pub(crate) struct DisplaySolvableIdOrRoot<'i, I: Interner> {
    interner: &'i I,
    solvable_id: SolvableIdOrRoot<I::SolvableId>,
}

impl<I: Interner> Display for DisplaySolvableIdOrRoot<'_, I> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self.solvable_id.solvable() {
            Some(solvable_id) => write!(f, "{}", self.interner.display_solvable(solvable_id)),
            None => write!(f, "root"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::VariableId;

    #[test]
    fn test_clause_id_size() {
        // Verify that the size of a ClauseId is the same as an Option<ClauseId>.
        assert_eq!(
            std::mem::size_of::<ClauseId>(),
            std::mem::size_of::<Option<ClauseId>>()
        );
    }

    #[test]
    fn test_variable_id_niche() {
        assert_eq!(std::mem::size_of::<VariableId>(), 4);
        assert_eq!(
            std::mem::size_of::<VariableId>(),
            std::mem::size_of::<Option<VariableId>>()
        );
    }

    #[test]
    fn test_dependencies_id_niche() {
        assert_eq!(std::mem::size_of::<DependenciesId>(), 4);
        assert_eq!(
            std::mem::size_of::<DependenciesId>(),
            std::mem::size_of::<Option<DependenciesId>>()
        );
    }

    #[test]
    fn test_variable_id_root_roundtrip() {
        assert!(VariableId::root().is_root());
        assert_eq!(VariableId::root().to_index(), 0);
        assert_eq!(VariableId::from_index(0), VariableId::root());
        assert!(!VariableId::from_index(1).is_root());
        assert_eq!(VariableId::from_index(7).to_index(), 7);
    }
}
