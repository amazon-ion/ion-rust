use std::convert::From;
use std::fmt::{Debug, Display, Error, Formatter};
use std::{fmt, io};

use thiserror::Error;

/// A unified Result type representing the outcome of method calls that may fail.
pub type IonResult<T> = Result<T, IonError>;

// If the ion-c-sys feature is enabled, use the actual IonCError type as our IonCErrorSource...
#[cfg(feature = "ion_c")]
pub type IonCErrorSource = ion_c_sys::result::IonCError;
// ...otherwise, use a placeholder error type.
#[cfg(not(feature = "ion_c"))]
pub type IonCErrorSource = ErrorStub;

/// Placeholder Error type for error variants that require conditional compilation.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct ErrorStub;

impl Display for ErrorStub {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "ion-c error support was not enabled at build time")
    }
}

impl std::error::Error for ErrorStub {}

/// Represents the different types of high-level failures that might occur when reading Ion data.
#[derive(Debug, Error)]
pub enum IonError {
    /// Indicates that an IO error was encountered while reading or writing.
    #[error("{source:?}")]
    IoError {
        #[from]
        source: io::Error,
    },

    /// Indicates that the input buffer did not contain enough data to perform the requested read
    /// operation. If the input source contains more data, the reader can append it to the buffer
    /// and try again.
    #[error("ran out of input while reading {label} at offset {offset}")]
    Incomplete { label: &'static str, offset: usize },

    /// Indicates that the writer encountered a problem while serializing a given piece of data.
    #[error("{description}")]
    EncodingError { description: String },

    /// Indicates that the data stream being read contained illegal or otherwise unreadable data.
    #[error("{description}")]
    DecodingError { description: String },

    /// Returned when the user has performed an illegal operation (for example: calling stepOut()
    /// on the cursor at the top level.)
    #[error(
        "The user has performed an operation that is not legal in the current state: {operation}"
    )]
    IllegalOperation { operation: String },

    /// Indicates that the underlying failure is due to a problem in [`ion_c_sys`].
    #[error("{source:?}")]
    IonCError {
        #[from]
        source: IonCErrorSource,
    },
}

impl From<fmt::Error> for IonError {
    fn from(error: Error) -> Self {
        IonError::EncodingError {
            description: error.to_string(),
        }
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
            IoError { source } => IoError {
                // io::Error implements From<ErrorKind>, and ErrorKind is cloneable.
                source: io::Error::from(source.kind()),
            },
            Incomplete { label, offset } => Incomplete {
                label,
                offset: *offset,
            },
            EncodingError { description } => EncodingError {
                description: description.clone(),
            },
            DecodingError { description } => DecodingError {
                description: description.clone(),
            },
            IllegalOperation { operation } => IllegalOperation {
                operation: operation.clone(),
            },
            IonCError { source } => IonCError { source: *source },
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
            (IoError { source: s1 }, IoError { source: s2 }) => s1.kind() == s2.kind(),
            (
                Incomplete {
                    label: l1,
                    offset: o1,
                },
                Incomplete {
                    label: l2,
                    offset: o2,
                },
            ) => l1 == l2 && o1 == o2,
            (EncodingError { description: s1 }, EncodingError { description: s2 }) => s1 == s2,
            (DecodingError { description: s1 }, DecodingError { description: s2 }) => s1 == s2,
            (IllegalOperation { operation: s1 }, IllegalOperation { operation: s2 }) => s1 == s2,
            (IonCError { source: s1 }, IonCError { source: s2 }) => s1 == s2,
            _ => false,
        }
    }
}

pub fn incomplete_data_error<T>(label: &'static str, offset: usize) -> IonResult<T> {
    Err(incomplete_data_error_raw(label, offset))
}

pub fn incomplete_data_error_raw(label: &'static str, offset: usize) -> IonError {
    IonError::Incomplete { label, offset }
}

/// A convenience method for creating an IonResult containing an IonError::DecodingError with the
/// provided description text.
pub fn decoding_error<T, S: AsRef<str>>(description: S) -> IonResult<T> {
    Err(decoding_error_raw(description))
}

/// A convenience method for creating an IonError::DecodingError with the provided operation
/// text. Useful for calling Option#ok_or_else.
pub fn decoding_error_raw<S: AsRef<str>>(description: S) -> IonError {
    IonError::DecodingError {
        description: description.as_ref().to_string(),
    }
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

#[cfg(all(test, feature = "ion_c"))]
mod test {
    use ion_c_sys::result::*;
    use ion_c_sys::{ion_error_code_IERR_EOF, ion_error_code_IERR_INVALID_ARG};

    use super::*;

    #[test]
    fn ion_c_error_eq() {
        // make sure we can actually convert an Ion C error
        let e1: IonError = IonCError::from(ion_error_code_IERR_EOF).into();
        let e2: IonError = IonCError::from(ion_error_code_IERR_INVALID_ARG).into();

        // make sure eq/clone works
        assert_eq!(e1, e1.clone());
        assert_ne!(e1, e2);
    }
}
