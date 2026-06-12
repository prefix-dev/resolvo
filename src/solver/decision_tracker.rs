use crate::solver::{decision::Decision, decision_map::DecisionMap};
use crate::{VariableId, internal::id::ClauseId};

/// Tracks the assignments to solvables, keeping a log that can be used to backtrack, and a map that
/// can be used to query the current value assigned
#[derive(Default)]
pub(crate) struct DecisionTracker {
    map: DecisionMap,

    /// The *trail*: every assignment in the chronological order it was made,
    /// both decisions and propagated assignments. Assigning pushes onto it
    /// and backtracking pops from it, so the trail only ever changes at its
    /// end: two snapshots of the trail always share a common prefix up to
    /// the minimum length reached in between.
    stack: Vec<Decision>,

    propagate_index: usize,

    /// The minimum length of `stack` since the last call to
    /// [`Self::take_sync_floor`]: the length of the trail prefix that is
    /// guaranteed unchanged since then. [`crate::solver::decide_queue`] keeps
    /// a copy of the trail and uses the floor to find what changed: copied
    /// entries at or beyond the floor have been popped at some point (their
    /// variables may be unassigned now or reassigned elsewhere), and current
    /// `stack` entries at or beyond it were pushed since. An assignment that
    /// was both pushed and popped in between is in neither range; it has no
    /// net effect, so a consumer comparing snapshots never needs to see it.
    sync_floor: usize,
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

    /// Returns the current decision stack as a slice.
    pub(crate) fn assignments(&self) -> &[Decision] {
        &self.stack
    }

    /// Returns the minimum trail length reached since the previous call (or
    /// since construction) and resets the floor to the current trail length.
    ///
    /// The trail up to the returned floor is unchanged since the previous
    /// call; everything a snapshot-comparing consumer has to look at lies at
    /// or beyond it. See [`Self::sync_floor`].
    pub(crate) fn take_sync_floor(&mut self) -> usize {
        std::mem::replace(&mut self.sync_floor, self.stack.len())
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
        self.sync_floor = self.sync_floor.min(self.stack.len());

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

#[cfg(test)]
mod test {
    use super::*;
    use crate::DenseIndex;

    fn var(i: usize) -> VariableId {
        VariableId::from_index(i)
    }

    fn push(tracker: &mut DecisionTracker, i: usize, level: u32) {
        tracker
            .try_add_decision(Decision::new(var(i), true, ClauseId::install_root()), level)
            .unwrap();
    }

    #[test]
    fn take_sync_floor_tracks_minimum_stack_length() {
        let mut tracker = DecisionTracker::default();
        assert_eq!(tracker.take_sync_floor(), 0);

        push(&mut tracker, 0, 1);
        push(&mut tracker, 1, 2);
        push(&mut tracker, 2, 2);
        assert_eq!(tracker.take_sync_floor(), 0);

        // An assignment made and undone between two observations cancels out:
        // the floor only drops to the minimum length reached.
        tracker.undo_last();
        push(&mut tracker, 3, 2);
        assert_eq!(tracker.take_sync_floor(), 2);

        // Two undos followed by new pushes report the deepest undo.
        tracker.undo_last();
        tracker.undo_last();
        push(&mut tracker, 4, 2);
        push(&mut tracker, 5, 2);
        assert_eq!(tracker.take_sync_floor(), 1);

        // Pushes alone never lower the floor: it stays at the stack length
        // observed by the previous take (3), not the current length (4).
        push(&mut tracker, 6, 2);
        assert_eq!(tracker.take_sync_floor(), 3);

        // Clearing resets the floor to zero.
        tracker.clear();
        assert_eq!(tracker.take_sync_floor(), 0);
    }
}
