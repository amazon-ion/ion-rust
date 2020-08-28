use std::convert::From;
use std::io;

/// A unified Result type representing the outcome of method calls that may fail.
pub type IonResult<T> = Result<T, IonError>;

/// Represents the different types of high-level failures that might occur when reading Ion data.
#[derive(Debug, Fail, Clone, PartialEq)]
pub enum IonError {
    /// Indicates that an IO error was encountered while reading or writing.
    #[fail(display = "An IO error occurred: {}", description)]
    IoError { description: String },

    /// Indicates that the data stream being read contained illegal or otherwise unreadable data.
    #[fail(display = "A decoding error occurred: {}", description)]
    DecodingError { description: String },

    /// Returned when the user has performed an illegal operation (for example: calling stepOut()
    /// on the cursor at the top level.)
    #[fail(
        display = "The user has performed an action that is not legal in the current state: {}",
        description
    )]
    IllegalOperation { description: String },
}

/// A convenience method for creating an IonResult containing an IonError::IoError with the
/// provided description text.
pub fn io_error<T>(description: &str) -> IonResult<T> {
    Err(IonError::IoError {
        description: description.to_string(),
    })
}

/// A convenience method for creating an IonResult containing an IonError::DecodingError with the
/// provided description text.
pub fn decoding_error<T, S: AsRef<str>>(description: S) -> IonResult<T> {
    Err(IonError::DecodingError {
        description: description.as_ref().to_string(),
    })
}

/// A convenience method for creating an IonResult containing an IonError::IllegalOperation with the
/// provided description text.
pub fn illegal_operation<T, S: AsRef<str>>(description: S) -> IonResult<T> {
    Err(illegal_operation_raw(description))
}

/// A convenience method for creating an IonError::IllegalOperation with the provided description
/// text. Useful for calling Option#ok_or_else.
pub fn illegal_operation_raw<S: AsRef<str>>(description: S) -> IonError {
    IonError::IllegalOperation {
        description: description.as_ref().to_string(),
    }
}

/// Allows [`io::Error`]s to be converted to an IonError and propagated using the `?` operator.
impl From<io::Error> for IonError {
    fn from(error: io::Error) -> Self {
        IonError::IoError {
            description: format!("Encountered an IO error: {:?}", error),
        }
    }
}

/// Allows [`std::fmt::Error`]s to be converted to an IonError and propagated using the `?` operator.
impl From<std::fmt::Error> for IonError {
    fn from(error: std::fmt::Error) -> Self {
        IonError::IoError {
            description: format!("Encountered an IO error: {:?}", error),
        }
    }
}
