use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq)]
#[error("{description}")]
pub struct DecodingError {
    description: String,
}

impl DecodingError {
    pub(crate) fn new(description: impl Into<String>) -> Self {
        DecodingError {
            description: description.into(),
        }
    }
}
