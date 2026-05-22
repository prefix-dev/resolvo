use std::cmp::Ordering;

use crate::VariableId;
use crate::id::DenseIndex;

/// Represents a decision (i.e. an assignment to a variable) and the level at
/// which it was made
///
/// `= 0`: undecided
/// `> 0`: level of decision when the variable is set to true
/// `< 0`: level of decision when the variable is set to false
#[repr(transparent)]
#[derive(Copy, Clone)]
struct DecisionAndLevel(i32);

impl DecisionAndLevel {
    fn undecided() -> DecisionAndLevel {
        DecisionAndLevel(0)
    }

    fn value(self) -> Option<bool> {
        match self.0.cmp(&0) {
            Ordering::Less => Some(false),
            Ordering::Equal => None,
            Ordering::Greater => Some(true),
        }
    }

    fn level(self) -> u32 {
        self.0.unsigned_abs()
    }

    fn with_value_and_level(value: bool, level: u32) -> Self {
        debug_assert!(level <= (i32::MAX as u32), "level is too large");
        Self(if value { level as i32 } else { -(level as i32) })
    }
}

/// A map of the assignments to solvables.
#[derive(Default)]
pub(crate) struct DecisionMap {
    map: Vec<DecisionAndLevel>,
}

impl DecisionMap {
    #[cfg(feature = "diagnostics")]
    pub fn len(&self) -> usize {
        self.map.len()
    }

    pub fn reset(&mut self, variable_id: VariableId) {
        let variable_id = variable_id.to_index();
        if variable_id < self.map.len() {
            // SAFE: because we check that the solvable id is within bounds
            unsafe { *self.map.get_unchecked_mut(variable_id) = DecisionAndLevel::undecided() };
        }
    }

    pub fn set(&mut self, variable_id: VariableId, value: bool, level: u32) {
        let variable_id = variable_id.to_index();
        if variable_id >= self.map.len() {
            self.map
                .resize_with(variable_id + 1, DecisionAndLevel::undecided);
        }

        // SAFE: because we ensured that vec contains at least the correct number of
        // elements.
        unsafe {
            *self.map.get_unchecked_mut(variable_id) =
                DecisionAndLevel::with_value_and_level(value, level)
        };
    }

    pub fn level(&self, variable_id: VariableId) -> u32 {
        self.map
            .get(variable_id.to_index())
            .map_or(0, |d| d.level())
    }

    #[inline(always)]
    pub fn value(&self, variable_id: VariableId) -> Option<bool> {
        self.map.get(variable_id.to_index()).and_then(|d| d.value())
    }
}
