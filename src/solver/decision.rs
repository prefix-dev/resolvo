use crate::{VariableId, internal::id::ClauseId};

/// Represents an assignment to a variable
#[derive(Copy, Clone, Eq, PartialEq)]
pub(crate) struct Decision {
    pub(crate) variable: VariableId,
    pub(crate) value: bool,
    pub(crate) derived_from: ClauseId,
}

impl Decision {
    pub(crate) fn new(variable: VariableId, value: bool, derived_from: ClauseId) -> Self {
        Self {
            variable,
            value,
            derived_from,
        }
    }
}
