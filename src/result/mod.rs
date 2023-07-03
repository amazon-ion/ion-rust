use std::convert::From;
use std::fmt::{Debug, Error};
use std::{fmt, io};

use crate::result::decoding_error::DecodingError;
use crate::result::encoding_error::EncodingError;
use crate::result::illegal_operation::IllegalOperation;
use crate::result::incomplete::IncompleteError;
use io_error::IoError;
use position::Position;
use thiserror::Error;

pub mod decoding_error;
pub mod encoding_error;
pub mod illegal_operation;
pub mod incomplete;
pub mod io_error;
pub mod position;

/// A unified Result type representing the outcome of method calls that may fail.
pub type IonResult<T> = Result<T, IonError>;

/// Represents the different types of high-level failures that might occur when reading Ion data.
#[derive(Clone, Debug, Error, PartialEq)]
pub enum IonError {
    /// Indicates that an IO error was encountered while reading or writing.
    #[error("{0}")]
    Io(#[from] IoError),

    /// Indicates that the input buffer did not contain enough data to perform the requested read
    /// operation. If the input source contains more data, the reader can append it to the buffer
    /// and try again.
    #[error("{0}")]
    Incomplete(#[from] IncompleteError),

    /// Indicates that the writer encountered a problem while serializing a given piece of data.
    #[error("{0}")]
    Encoding(#[from] EncodingError),

    /// Indicates that the data stream being read contained illegal or otherwise unreadable data.
    #[error("{0}")]
    Decoding(#[from] DecodingError),

    /// Returned when the user has performed an illegal operation (for example: calling stepOut()
    /// on the cursor at the top level.)
    #[error("{0}")]
    IllegalOperation(#[from] IllegalOperation),
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

// Crate-visible convenience methods for constructing error variants and wrapping them in the
// appropriate type: IonResult<T> or IonError. This is a trait so these methods can be added to
// `IonResult<T>`, which is just a type alias for `Result<T, IonError>`, whose implementation
// does not live in this crate.
pub(crate) trait IonFailure {
    // Note: this trait does not have an `io(...)` method because the only way we ever construct
    // an `IonError::Io` is by converting a `std::io::IoError` with the ? operator.
    // Because this trait is only crate-visible, methods can be added/changed as needed in
    // the future.
    fn incomplete(label: &'static str, position: impl Into<Position>) -> Self;
    fn decoding_error<S: Into<String>>(description: S) -> Self;
    fn encoding_error<S: Into<String>>(description: S) -> Self;
    fn illegal_operation<S: Into<String>>(operation: S) -> Self;
}

impl IonFailure for IonError {
    fn incomplete(label: &'static str, position: impl Into<Position>) -> Self {
        IncompleteError::new(label, position).into()
    }

    fn decoding_error<S: Into<String>>(description: S) -> Self {
        DecodingError::new(description).into()
    }

    fn encoding_error<S: Into<String>>(description: S) -> Self {
        EncodingError::new(description).into()
    }

    fn illegal_operation<S: Into<String>>(operation: S) -> Self {
        IllegalOperation::new(operation).into()
    }
}

impl<T> IonFailure for IonResult<T> {
    fn incomplete(label: &'static str, position: impl Into<Position>) -> Self {
        Err(IonError::incomplete(label, position))
    }

    fn decoding_error<S: Into<String>>(description: S) -> Self {
        Err(IonError::decoding_error(description))
    }

    fn encoding_error<S: Into<String>>(description: S) -> Self {
        Err(IonError::encoding_error(description))
    }

    fn illegal_operation<S: Into<String>>(operation: S) -> Self {
        Err(IonError::illegal_operation(operation))
    }
}
