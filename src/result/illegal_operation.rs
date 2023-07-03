use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq)]
#[error("the user has performed an operation that is not legal in the current state: {operation}")]
pub struct IllegalOperation {
    operation: String,
}

impl IllegalOperation {
    pub(crate) fn new(description: impl Into<String>) -> Self {
        IllegalOperation {
            operation: description.into(),
        }
    }

    pub fn operation(&self) -> &str {
        self.operation.as_str()
    }
}
