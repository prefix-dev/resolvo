use std::hash::Hash;

use indexmap::IndexSet;

/// An object that is responsible for incrementally building clauses to enforce
/// that at most one of a set of variables can be true.
pub(crate) struct AtMostOnceTracker<V> {
    /// The set of variables of which at most one can be assigned true.
    pub(crate) variables: IndexSet<V, ahash::RandomState>,
    pub(crate) helpers: Vec<V>,
}

impl<V> Default for AtMostOnceTracker<V> {
    fn default() -> Self {
        Self {
            variables: IndexSet::default(),
            helpers: Vec::new(),
        }
    }
}

impl<V: Hash + Eq + Clone> AtMostOnceTracker<V> {
    /// Add a `variable` to the set of variables of which at most one can be
    /// assigned true.
    ///
    /// `alloc_clause` is a closure that is called to allocate a new clause to
    /// enforce (¬A ∨ B?). Where B is either positive or negative based on the
    /// value passed to the closure.
    pub fn add(
        &mut self,
        variable: V,
        mut alloc_clause: impl FnMut(V, V, bool),
        mut alloc_var: impl FnMut() -> V,
    ) -> bool {
        // If the variable is already tracked, we don't need to do anything.
        if self.variables.contains(&variable) {
            return false;
        }

        // If there are no variables yet, it means that this is the first variable that
        // is added. A single variable can never be in conflict with itself so we don't
        // need to add any clauses.
        if self.variables.is_empty() {
            self.variables.insert(variable.clone());
            return true;
        }

        // Allocate additional helper variables as needed and create clauses for the
        // preexisting variables.
        while self.variables.len() > (1 << self.helpers.len()) - 1 {
            // Allocate the helper variable
            let helper_var = alloc_var();
            let bit_idx = self.helpers.len();
            self.helpers.push(helper_var.clone());

            // Add a negative clause for all existing variables.
            let mask = 1 << bit_idx;
            for (idx, var) in self.variables.iter().cloned().enumerate() {
                alloc_clause(var, helper_var.clone(), (idx & mask) == mask);
            }
        }

        let var_idx = self.variables.len();
        self.variables.insert(variable.clone());
        for (bit_idx, helper_var) in self.helpers.iter().enumerate() {
            alloc_clause(
                variable.clone(),
                helper_var.clone(),
                ((var_idx >> bit_idx) & 1) == 1,
            );
        }

        true
    }
}

#[cfg(test)]
mod test {
    use std::fmt::{Display, Formatter};

    use itertools::Itertools;

    use super::*;

    #[derive(Hash, Eq, PartialEq, Clone)]
    enum Variable {
        Concrete(usize),
        Variable(usize),
    }

    impl Display for Variable {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            match self {
                Variable::Concrete(id) => write!(f, "x{}", id),
                Variable::Variable(id) => write!(f, "v{}", id),
            }
        }
    }

    struct Variables {
        next_concrete: usize,
        next_variable: usize,
    }

    impl Variables {
        fn new() -> Self {
            Self {
                next_concrete: 1,
                next_variable: 1,
            }
        }

        fn concrete(&mut self) -> Variable {
            let id = self.next_concrete;
            self.next_concrete += 1;
            Variable::Concrete(id)
        }

        fn variable(&mut self) -> Variable {
            let id = self.next_variable;
            self.next_variable += 1;
            Variable::Variable(id)
        }
    }

    struct NotBothClause {
        a: Variable,
        b: Variable,
        positive: bool,
    }

    impl Display for NotBothClause {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            write!(
                f,
                "¬{} ∨ {}{}",
                self.a,
                if self.positive { "" } else { "¬" },
                self.b
            )
        }
    }

    #[test]
    fn test_at_most_once_tracker() {
        let mut clauses = Vec::new();
        let mut variables = Variables::new();
        let mut tracker = AtMostOnceTracker::default();

        let mut add_new_var = || {
            let var = variables.concrete();
            tracker.add(
                var.clone(),
                |a, b, positive| {
                    clauses.push(NotBothClause { a, b, positive });
                },
                || variables.variable(),
            );
            var
        };

        add_new_var();
        add_new_var();
        add_new_var();
        add_new_var();

        insta::assert_snapshot!(clauses.iter().format("\n"));
    }
}
