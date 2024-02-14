use ice_code::ice as cold_path;
use std::borrow::Cow;
use thiserror::Error;

/// Indicates that a write operation failed to serialize the given data.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("{description}")]
pub struct EncodingError {
    description: Cow<'static, str>,
}

impl EncodingError {
    pub(crate) fn new(description: impl Into<Cow<'static, str>>) -> Self {
        EncodingError {
            description: cold_path! { encoding_error => description.into()},
        }
    }
}
