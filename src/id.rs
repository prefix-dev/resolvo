//! Public ID types used by dependency providers, snapshots, and diagnostics.

use std::num::{NonZero, NonZeroU32};

use crate::solver_id::DenseId;

/// A dense zero-based ID that can be transformed to and from a `usize` index.
///
/// This is primarily used by dense storage such as [`crate::Mapping`] and the
/// default pool-backed IDs. Sparse provider IDs should implement
/// [`crate::SolverId`] without implementing this trait.
pub trait DenseIndex {
    /// Constructs a new ID from a zero-based index.
    fn from_index(x: usize) -> Self;

    /// Returns the zero-based index of the ID.
    fn to_index(self) -> usize;
}

/// The id associated to a package name.
pub type NameId = DenseId<NameTag>;

/// Domain tag for [`NameId`].
pub enum NameTag {}

/// The id associated with a generic string.
#[repr(transparent)]
#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct StringId(pub u32);

impl DenseIndex for StringId {
    fn from_index(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_index(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a version set.
#[repr(transparent)]
#[derive(Clone, Default, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct VersionSetId(pub u32);

impl DenseIndex for VersionSetId {
    fn from_index(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_index(self) -> usize {
        self.0 as usize
    }
}

/// The id associated with a condition.
#[repr(transparent)]
#[derive(Clone, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct ConditionId(NonZero<u32>);

impl ConditionId {
    /// Creates a new [`ConditionId`] from a `u32`.
    pub fn new(id: u32) -> Self {
        Self::from_index(id as usize)
    }

    /// Returns the inner `u32` value of the [`ConditionId`].
    pub fn as_u32(self) -> u32 {
        self.0.get() - 1
    }
}

impl DenseIndex for ConditionId {
    fn from_index(x: usize) -> Self {
        let id = (x + 1).try_into().expect("condition id too big");
        Self(unsafe { NonZero::new_unchecked(id) })
    }

    fn to_index(self) -> usize {
        (self.0.get() - 1) as usize
    }
}

/// The id associated with a union (logical OR) of two or more version sets.
#[repr(transparent)]
#[derive(Clone, Default, Copy, Debug, Hash, Eq, PartialEq, Ord, PartialOrd)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct VersionSetUnionId(pub u32);

impl DenseIndex for VersionSetUnionId {
    fn from_index(x: usize) -> Self {
        Self(x as u32)
    }

    fn to_index(self) -> usize {
        self.0 as usize
    }
}

/// The id associated to a solvable.
pub type SolvableId = DenseId<SolvableTag>;

/// Domain tag for [`SolvableId`].
pub enum SolvableTag {}

/// A unique identifier for a variable in the solver.
///
/// Uses a non-zero representation so that `Option<VariableId>` is the same
/// size as `VariableId`.
#[repr(transparent)]
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct VariableId(NonZeroU32);

impl VariableId {
    const ROOT_ID: u32 = 1;

    /// Returns the variable id representing the root of the decision tree.
    pub fn root() -> Self {
        // SAFETY: 1 is non-zero.
        Self(unsafe { NonZeroU32::new_unchecked(Self::ROOT_ID) })
    }

    /// Returns `true` if this variable represents the root.
    pub fn is_root(self) -> bool {
        self.0.get() == Self::ROOT_ID
    }
}

impl DenseIndex for VariableId {
    #[inline]
    fn from_index(x: usize) -> Self {
        let raw: u32 = (x + Self::ROOT_ID as usize)
            .try_into()
            .expect("variable id too big");
        // SAFETY: `raw` is `x + 1`, hence at least 1, hence non-zero.
        Self(unsafe { NonZeroU32::new_unchecked(raw) })
    }

    #[inline]
    fn to_index(self) -> usize {
        (self.0.get() - Self::ROOT_ID) as usize
    }
}
