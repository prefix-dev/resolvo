use crate::solver::{decision::Decision, decision_map::DecisionMap};
use crate::{VariableId, internal::id::ClauseId};

/// Tracks the assignments to solvables, keeping a log that can be used to backtrack, and a map that
/// can be used to query the current value assigned
#[derive(Default)]
pub(crate) struct DecisionTracker {
    map: DecisionMap,
    stack: Vec<Decision>,
    propagate_index: usize,
}

impl DecisionTracker {
    pub(crate) fn clear(&mut self) {
        *self = Default::default();
    }

    #[cfg(feature = "diagnostics")]
    pub(crate) fn len(&self) -> usize {
        self.map.len()
    }

    #[inline(always)]
    pub(crate) fn assigned_value(&self, variable_id: VariableId) -> Option<bool> {
        self.map.value(variable_id)
    }

    #[inline]
    pub(crate) fn map(&self) -> &DecisionMap {
        &self.map
    }

    pub(crate) fn stack(&self) -> impl DoubleEndedIterator<Item = Decision> + '_ {
        self.stack.iter().copied()
    }

    pub(crate) fn level(&self, variable_id: VariableId) -> u32 {
        self.map.level(variable_id)
    }

    // Find the clause that caused the assignment of the specified solvable. If no assignment has
    // been made to the solvable than `None` is returned.
    pub(crate) fn find_clause_for_assignment(&self, variable_id: VariableId) -> Option<ClauseId> {
        self.stack
            .iter()
            .find(|d| d.variable == variable_id)
            .map(|d| d.derived_from)
    }

    /// Attempts to add a decision
    ///
    /// Returns true if the solvable was undecided, false if it was already decided to the same value
    ///
    /// Returns an error if the solvable was decided to a different value (which means there is a conflict)
    #[inline]
    pub(crate) fn try_add_decision(&mut self, decision: Decision, level: u32) -> Result<bool, ()> {
        match self.map.value(decision.variable) {
            None => {
                self.map.set(decision.variable, decision.value, level);
                self.stack.push(decision);
                Ok(true)
            }
            Some(value) if value == decision.value => Ok(false),
            _ => Err(()),
        }
    }

    pub(crate) fn undo_until(&mut self, level: u32) {
        if level == 0 {
            self.clear();
            return;
        }

        while let Some(decision) = self.stack.last() {
            if self.level(decision.variable) <= level {
                break;
            }

            self.undo_last();
        }
    }

    pub(crate) fn undo_last(&mut self) -> (Decision, u32) {
        let decision = self.stack.pop().unwrap();
        self.map.reset(decision.variable);

        self.propagate_index = self.stack.len();

        let top_decision = self.stack.last().unwrap();
        (decision, self.map.level(top_decision.variable))
    }

    /// Returns the next decision in the log for which unit propagation still needs to run
    ///
    /// Side-effect: the decision will be marked as propagated
    #[inline]
    pub(crate) fn next_unpropagated(&mut self) -> Option<Decision> {
        let &decision = self.stack[self.propagate_index..].iter().next()?;
        self.propagate_index += 1;
        Some(decision)
    }
}
