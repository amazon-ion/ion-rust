use std::borrow::Cow;
use thiserror::Error;

#[derive(Clone, Debug, Error, PartialEq)]
#[error("the user has performed an operation that is not legal in the current state: {operation}")]
pub struct IllegalOperation {
    operation: Cow<'static, str>,
}

impl IllegalOperation {
    pub(crate) fn new(description: impl Into<Cow<'static, str>>) -> Self {
        IllegalOperation {
            operation: description.into(),
        }
    }

    pub fn operation(&self) -> &str {
        self.operation.as_ref()
    }
}
