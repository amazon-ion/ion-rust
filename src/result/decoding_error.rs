use crate::position::Position;
use std::borrow::Cow;
use thiserror::Error;

/// Indicates that a read operation failed due to invalid input.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("{description}")]
pub struct DecodingError {
    description: Cow<'static, str>,
    // This is optional because sometimes data is found to be malformed or invalid but the original
    // data source is not available. For example, consider a deserializer reading a symbol table
    // from an `Element`. If the `symbols` field is missing, it needs to raise a decoding error, but
    // no source position is available. Whenever possible, usages should specify the position.
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
