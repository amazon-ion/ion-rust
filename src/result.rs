use thiserror::Error;

use std::convert::From;
use std::{io, fmt};

/// A unified Result type representing the outcome of method calls that may fail.
pub type IonResult<T> = Result<T, IonError>;

/// Represents the different types of high-level failures that might occur when reading Ion data.
#[derive(Debug, Error)]
pub enum IonError {
    /// Indicates that an IO error was encountered while reading or writing.
    #[error("{source:?}")]
    IoError {
        #[from]
        source: io::Error,
    },

    #[error("{source:?}")]
    FmtError {
        #[from]
        source: fmt::Error,
    },

    /// Indicates that the data stream being read contained illegal or otherwise unreadable data.
    #[error("{description}")]
    DecodingError { description: String },

    /// Returned when the user has performed an illegal operation (for example: calling stepOut()
    /// on the cursor at the top level.)
    #[error("The user has performed an operation that is not legal in the current state: {operation}")]
    IllegalOperation { operation: String },
}

// io::Error does not implement Clone, which precludes us from simply deriving an implementation.
// IonError needs a Clone implementation because we use a jump table of cached IonResult values when
// parsing type descriptor bytes. The only error type that will be cloned by virtue of using the jump
// table is DecodingError.
impl Clone for IonError {
    fn clone(&self) -> Self {
        use IonError::*;
        match self {
            IoError {source} => IoError {
                // io::Error implements From<ErrorKind>, and ErrorKind is cloneable.
                source: io::Error::from(source.kind().clone())
            },
            FmtError {source} => FmtError {
                source: source.clone()
            },
            DecodingError {description} => DecodingError {
                description: description.clone()
            },
            IllegalOperation {operation} => IllegalOperation {
                operation: operation.clone()
            }
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
            (IoError {source: s1}, IoError {source: s2}) => s1.kind() == s2.kind(),
            (FmtError {source: s1}, FmtError {source: s2}) => s1 == s2,
            (DecodingError {description: s1}, DecodingError {description: s2}) => s1 == s2,
            (IllegalOperation {operation: s1}, IllegalOperation {operation: s2}) => s1 == s2,
            _ => false
        }
    }
}

/// A convenience method for creating an IonResult containing an IonError::DecodingError with the
/// provided description text.
pub fn decoding_error<T, S: AsRef<str>>(description: S) -> IonResult<T> {
    Err(IonError::DecodingError {
        description: description.as_ref().to_string(),
    })
}

/// A convenience method for creating an IonResult containing an IonError::IllegalOperation with the
/// provided operation text.
pub fn illegal_operation<T, S: AsRef<str>>(operation: S) -> IonResult<T> {
    Err(illegal_operation_raw(operation))
}

/// A convenience method for creating an IonError::IllegalOperation with the provided operation
/// text. Useful for calling Option#ok_or_else.
pub fn illegal_operation_raw<S: AsRef<str>>(operation: S) -> IonError {
    IonError::IllegalOperation {
        operation: operation.as_ref().to_string(),
    }
}
