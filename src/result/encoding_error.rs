use std::borrow::Cow;
use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq)]
#[error("{description}")]
pub struct EncodingError {
    description: Cow<'static, str>,
}

impl EncodingError {
    pub(crate) fn new(description: impl Into<Cow<'static, str>>) -> Self {
        EncodingError {
            description: description.into(),
        }
    }
}
