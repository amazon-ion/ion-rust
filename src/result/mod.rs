use std::convert::From;
use std::fmt::{Debug, Error};
use std::{fmt, io};

use crate::result::encoding_error::EncodingError;
use crate::result::incomplete::Incomplete;
use io_error::IoError;
use position::Position;
use thiserror::Error;

pub mod encoding_error;
pub mod incomplete;
pub mod io_error;
pub mod position;

/// A unified Result type representing the outcome of method calls that may fail.
pub type IonResult<T> = Result<T, IonError>;

/// Represents the different types of high-level failures that might occur when reading Ion data.
#[derive(Debug, Error)]
pub enum IonError {
    /// Indicates that an IO error was encountered while reading or writing.
    #[error("{0}")]
    IoError(#[from] IoError),

    /// Indicates that the input buffer did not contain enough data to perform the requested read
    /// operation. If the input source contains more data, the reader can append it to the buffer
    /// and try again.
    #[error("{0}")]
    Incomplete(#[from] Incomplete),

    /// Indicates that the writer encountered a problem while serializing a given piece of data.
    #[error("{0}")]
    EncodingError(#[from] EncodingError),

    /// Indicates that the data stream being read contained illegal or otherwise unreadable data.
    #[error("{description}")]
    DecodingError { description: String },

    /// Returned when the user has performed an illegal operation (for example: calling stepOut()
    /// on the cursor at the top level.)
    #[error(
        "The user has performed an operation that is not legal in the current state: {operation}"
    )]
    IllegalOperation { operation: String },
}

impl From<io::Error> for IonError {
    fn from(io_error: io::Error) -> Self {
        IoError::from(io_error).into()
    }
}

impl From<io::ErrorKind> for IonError {
    fn from(error_kind: io::ErrorKind) -> Self {
        // io::ErrorKind -> io::Error
        let io_error = io::Error::from(error_kind);
        // io::Error -> IoError -> IonError
        IoError::from(io_error).into()
    }
}

impl From<fmt::Error> for IonError {
    fn from(error: Error) -> Self {
        EncodingError::new(error.to_string()).into()
    }
}

// io::Error does not implement Clone, which precludes us from simply deriving an implementation.
// IonError needs a Clone implementation because we use a jump table of cached IonResult values when
// parsing type descriptor bytes. The only error type that will be cloned by virtue of using the jump
// table is DecodingError.
impl Clone for IonError {
    fn clone(&self) -> Self {
        use IonError::*;
        match self {
            IoError(io_error) => io_error.clone().into(),
            Incomplete(incomplete) => incomplete.clone().into(),
            EncodingError(e) => e.clone().into(),
            DecodingError { description } => DecodingError {
                description: description.clone(),
            },
            IllegalOperation { operation } => IllegalOperation {
                operation: operation.clone(),
            },
        }
    }
}

// io::Error does not implement PartialEq, which precludes us from simply deriving an implementation.
// Providing an implementation of PartialEq allows IonResult values to be the left or right side in
// an assert_eq!() statement.
impl PartialEq for IonError {
    fn eq(&self, other: &Self) -> bool {
        use IonError::*;
        match (self, other) {
            // We can compare the io::Errors' ErrorKinds, offering a weak definition of equality.
            (IoError(e1), IoError(e2)) => e1 == e2,
            (Incomplete(e1), Incomplete(e2)) => e1 == e2,
            (EncodingError(e1), EncodingError(e2)) => e1 == e2,
            (DecodingError { description: s1 }, DecodingError { description: s2 }) => s1 == s2,
            (IllegalOperation { operation: s1 }, IllegalOperation { operation: s2 }) => s1 == s2,
            _ => false,
        }
    }
}

pub(crate) fn incomplete<T>(label: &'static str, position: impl Into<Position>) -> IonResult<T> {
    Err(incomplete_error(label, position))
}

pub(crate) fn incomplete_error(label: &'static str, position: impl Into<Position>) -> IonError {
    Incomplete::new(label, position).into()
}

/// A convenience method for creating an IonResult containing an IonError::DecodingError with the
/// provided description text.
pub fn decoding_error<T, S: Into<String>>(description: S) -> IonResult<T> {
    Err(decoding_error_raw(description))
}

/// A convenience method for creating an IonError::DecodingError with the provided operation
/// text. Useful for calling Option#ok_or_else.
#[inline(never)]
pub(crate) fn decoding_error_raw<S: Into<String>>(description: S) -> IonError {
    IonError::DecodingError {
        description: description.into(),
    }
}

/// A convenience method for creating an IonResult containing an IonError::EncodingError with the
/// provided description text.
pub(crate) fn encoding_error<T, S: Into<String>>(description: S) -> IonResult<T> {
    Err(encoding_error_raw(description))
}

/// A convenience method for creating an IonError::EncodingError with the provided operation
/// text. Useful for calling Option#ok_or_else.
#[inline(never)]
pub(crate) fn encoding_error_raw<S: Into<String>>(description: S) -> IonError {
    EncodingError::new(description).into()
}

/// A convenience method for creating an IonResult containing an IonError::IllegalOperation with the
/// provided operation text.
pub fn illegal_operation<T, S: Into<String>>(operation: S) -> IonResult<T> {
    Err(illegal_operation_raw(operation))
}

/// A convenience method for creating an IonError::IllegalOperation with the provided operation
/// text. Useful for calling Option#ok_or_else.
#[inline(never)]
pub(crate) fn illegal_operation_raw<S: Into<String>>(operation: S) -> IonError {
    IonError::IllegalOperation {
        operation: operation.into(),
    }
}
