use std::borrow::Cow;
use thiserror::Error;

/// Indicates that a read operation failed due to invalid input.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("{description}")]
pub struct DecodingError {
    description: Cow<'static, str>,
}

impl DecodingError {
    pub(crate) fn new(description: impl Into<Cow<'static, str>>) -> Self {
        DecodingError {
            description: description.into(),
        }
    }
}
