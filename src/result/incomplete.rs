use crate::position::Position;
use std::borrow::Cow;
use thiserror::Error;

/// For non-blocking readers, indicates that there was not enough data available in the input buffer
/// to complete the requested action.
#[derive(Clone, Debug, Error, PartialEq)]
#[error("ran out of input while reading {} at offset {}", .inner.label, .inner.position)]
pub struct IncompleteError {
    // Boxed so that `IonError`, which carries this variant, stays small (a smaller error shrinks
    // `Result<T, IonError>` on every read/write path). Note the trade-off: for streaming readers
    // `Incomplete` is ordinary control flow, so this adds one allocation per buffer refill where
    // the payload was previously inline. An inline (allocation-free) payload would require changing
    // the public `position() -> &Position` signature, so boxing is the non-breaking option.
    inner: Box<IncompleteErrorInner>,
}

#[derive(Clone, Debug, PartialEq)]
struct IncompleteErrorInner {
    label: Cow<'static, str>,
    position: Position,
}

impl IncompleteError {
    pub(crate) fn new(label: impl Into<Cow<'static, str>>, position: impl Into<Position>) -> Self {
        IncompleteError {
            inner: Box::new(IncompleteErrorInner {
                label: label.into(),
                position: position.into(),
            }),
        }
    }

    pub fn position(&self) -> &Position {
        &self.inner.position
    }
}
