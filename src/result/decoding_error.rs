use crate::position::Position;
use std::borrow::Cow;
use thiserror::Error;

/// Indicates that a read operation failed due to invalid input.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("{description}")]
pub struct DecodingError {
    description: Cow<'static, str>,
    position: Option<Position>,
}

impl DecodingError {
    pub(crate) fn new(description: impl Into<Cow<'static, str>>) -> Self {
        DecodingError {
            description: description.into(),
            position: None,
        }
    }

    pub(crate) fn with_position(mut self, position: impl Into<Position>) -> Self {
        self.position = Some(position.into());
        self
    }

    pub fn position(&self) -> Option<&Position> {
        self.position.as_ref()
    }
}
