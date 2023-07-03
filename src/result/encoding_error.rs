use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq)]
#[error("{description}")]
pub struct EncodingError {
    description: String,
}

impl EncodingError {
    pub(crate) fn new(description: impl Into<String>) -> Self {
        EncodingError {
            description: description.into(),
        }
    }
}
