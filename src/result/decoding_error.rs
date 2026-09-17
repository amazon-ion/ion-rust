use crate::position::Position;
use std::borrow::Cow;
use thiserror::Error;

/// Indicates that a read operation failed due to invalid input.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("{}", .inner.description)]
pub struct DecodingError {
    // Boxed so that `IonError`, which carries this variant, stays small (a smaller error shrinks
    // `Result<T, IonError>` on every read/write path). The fields are only read on the cold error
    // path, so the extra indirection and allocation are cheap.
    inner: Box<DecodingErrorInner>,
}

#[derive(Clone, Debug, PartialEq)]
struct DecodingErrorInner {
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
            inner: Box::new(DecodingErrorInner {
                description: description.into(),
                position: None,
            }),
        }
    }

    pub(crate) fn with_position(mut self, position: impl Into<Position>) -> Self {
        self.inner.position = Some(position.into());
        self
    }

    pub fn position(&self) -> Option<&Position> {
        self.inner.position.as_ref()
    }
}
