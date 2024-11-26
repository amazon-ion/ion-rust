//! Types for reporting various modes of success or failure.

use std::borrow::Cow;
use std::convert::From;
use std::fmt::{Debug, Error};
use std::{fmt, io};

use thiserror::Error;

#[cfg(feature = "experimental-serde")]
use serde::{de, ser};

mod conversion;
mod decoding_error;
mod encoding_error;
mod illegal_operation;
mod incomplete;
mod io_error;

pub use conversion::Conversion;
pub use conversion::ConversionError;
pub use conversion::ConversionExpectation;
pub use conversion::ConversionResult;
pub use conversion::IonTypeExpectation;
pub use conversion::TypeExpectation;
pub use decoding_error::DecodingError;
pub use encoding_error::EncodingError;
pub use illegal_operation::IllegalOperation;
pub use incomplete::IncompleteError;
pub use io_error::IoError;

use crate::position::Position;

/// A unified Result type representing the outcome of method calls that may fail.
pub type IonResult<T> = Result<T, IonError>;

/// Represents the different types of high-level failures that might occur when reading Ion data.
#[non_exhaustive]
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

    /// Returned when the user has attempted to convert a value to a type for which that value is
    /// not trivially convertable.
    #[error("{0}")]
    Conversion(#[from] ConversionError),
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

impl From<IonError> for fmt::Error {
    fn from(_ion_error: IonError) -> Self {
        // This no-op transformation allows `?` to be used in `Debug` implementations wherever
        // an IonError could surface.
        fmt::Error
    }
}

#[cfg(feature = "experimental-serde")]
impl de::Error for IonError {
    fn custom<T>(error: T) -> Self
    where
        T: std::fmt::Display,
    {
        DecodingError::new(error.to_string()).into()
    }
}

#[cfg(feature = "experimental-serde")]
impl ser::Error for IonError {
    fn custom<T>(error: T) -> Self
    where
        T: std::fmt::Display,
    {
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
    fn incomplete(label: impl Into<Cow<'static, str>>, position: impl Into<Position>) -> Self;
    fn decoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self;
    fn encoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self;
    fn illegal_operation<S: Into<Cow<'static, str>>>(operation: S) -> Self;
}

impl IonFailure for IonError {
    fn incomplete(label: impl Into<Cow<'static, str>>, position: impl Into<Position>) -> Self {
        IncompleteError::new(label, position).into()
    }

    fn decoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self {
        DecodingError::new(description).into()
    }

    fn encoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self {
        EncodingError::new(description).into()
    }

    fn illegal_operation<S: Into<Cow<'static, str>>>(operation: S) -> Self {
        IllegalOperation::new(operation).into()
    }
}

impl<T> IonFailure for IonResult<T> {
    fn incomplete(label: impl Into<Cow<'static, str>>, position: impl Into<Position>) -> Self {
        Err(IonError::incomplete(label, position))
    }

    fn decoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self {
        Err(IonError::decoding_error(description))
    }

    fn encoding_error<S: Into<Cow<'static, str>>>(description: S) -> Self {
        Err(IonError::encoding_error(description))
    }

    fn illegal_operation<S: Into<Cow<'static, str>>>(operation: S) -> Self {
        Err(IonError::illegal_operation(operation))
    }
}
