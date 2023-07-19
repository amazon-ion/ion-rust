use crate::position::Position;
use thiserror::Error;

/// For non-blocking readers, indicates that there was not enough data available in the input buffer
/// to complete the requested action.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("ran out of input while reading {label} at offset {position}")]
pub struct IncompleteError {
    label: &'static str,
    position: Position,
}

impl IncompleteError {
    pub(crate) fn new(label: &'static str, position: impl Into<Position>) -> Self {
        IncompleteError {
            label,
            position: position.into(),
        }
    }

    pub fn position(&self) -> &Position {
        &self.position
    }
}
