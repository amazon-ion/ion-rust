use std::convert::From;
use std::fmt::{Debug, Display, Error};
use std::{fmt, io};

use thiserror::Error;

/// Represents the position, as line and column, within a text format ion document.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TextPosition {
    /// No text position available; implies binary format is being read.
    None,
    /// The position represented as line and column.
    LineAndColumn(usize, usize),
}

/// Position represents the location within an ion document where an error has been
/// identified. For all formats `byte_offset` will contain the number of bytes into the document
/// that have been processed prior to encountering the error. When working with the text format,
/// `line_column` will be updated to contain the line and column as well.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Position {
    pub byte_offset: usize,
    pub line_column: TextPosition,
}

impl Position {
    pub fn with_offset(offset: usize) -> Self {
        Position {
            byte_offset: offset,
            line_column: TextPosition::None,
        }
    }

    pub fn with_text_position(&self, line: usize, column: usize) -> Self {
        Position {
            line_column: TextPosition::LineAndColumn(line, column),
            ..*self
        }
    }

    fn has_text_position(&self) -> bool {
        self.line_column != TextPosition::None
    }
}

impl Display for Position {
    // Formats the position based on whether we have a LineAndColumn or not.
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), Error> {
        use TextPosition::*;
        match &self.line_column {
            None => write!(f, "{}", self.byte_offset),
            LineAndColumn(line, column) => {
                write!(f, "{} ({}:{})", self.byte_offset, line, column)
            }
        }
    }
}

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

    /// Indicates that the input buffer did not contain enough data to perform the requested read
    /// operation. If the input source contains more data, the reader can append it to the buffer
    /// and try again.
    #[error("ran out of input while reading {label} at offset {position}")]
    Incomplete {
        label: &'static str,
        position: Position,
    },

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
            Incomplete { label, position } => Incomplete {
                label,
                position: position.clone(),
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
                    position: p1,
                },
                Incomplete {
                    label: l2,
                    position: p2,
                },
            ) => l1 == l2 && p1 == p2,
            (EncodingError { description: s1 }, EncodingError { description: s2 }) => s1 == s2,
            (DecodingError { description: s1 }, DecodingError { description: s2 }) => s1 == s2,
            (IllegalOperation { operation: s1 }, IllegalOperation { operation: s2 }) => s1 == s2,
            _ => false,
        }
    }
}

pub fn incomplete_data_error<T>(label: &'static str, offset: usize) -> IonResult<T> {
    Err(incomplete_data_error_raw(label, offset))
}

pub fn incomplete_data_error_raw(label: &'static str, offset: usize) -> IonError {
    IonError::Incomplete {
        label,
        position: Position::with_offset(offset),
    }
}

pub fn incomplete_text_error<T>(label: &'static str, position: Position) -> IonResult<T> {
    Err(incomplete_text_error_raw(label, position))
}

pub fn incomplete_text_error_raw(label: &'static str, position: Position) -> IonError {
    IonError::Incomplete { label, position }
}

/// A convenience method for creating an IonResult containing an IonError::DecodingError with the
/// provided description text.
pub fn decoding_error<T, S: AsRef<str>>(description: S) -> IonResult<T> {
    Err(decoding_error_raw(description))
}

/// A convenience method for creating an IonError::DecodingError with the provided operation
/// text. Useful for calling Option#ok_or_else.
#[inline(never)]
pub fn decoding_error_raw<S: AsRef<str>>(description: S) -> IonError {
    IonError::DecodingError {
        description: description.as_ref().to_string(),
    }
}

/// A convenience method for creating an IonResult containing an IonError::EncodingError with the
/// provided description text.
pub fn encoding_error<T, S: AsRef<str>>(description: S) -> IonResult<T> {
    Err(encoding_error_raw(description))
}

/// A convenience method for creating an IonError::EncodingError with the provided operation
/// text. Useful for calling Option#ok_or_else.
#[inline(never)]
pub fn encoding_error_raw<S: AsRef<str>>(description: S) -> IonError {
    IonError::EncodingError {
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
#[inline(never)]
pub fn illegal_operation_raw<S: AsRef<str>>(operation: S) -> IonError {
    IonError::IllegalOperation {
        operation: operation.as_ref().to_string(),
    }
}
