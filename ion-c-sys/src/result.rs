// Copyright Amazon.com, Inc. or its affiliates.

//! Provides convenient integration with `Error` and `Result` for Ion C.

use crate::*;

use std::error::Error;
use std::ffi::CStr;
use std::fmt;
use std::num::TryFromIntError;

/// IonC Error code and its associated error message.
///
/// `position` is populated when errors come from readers. See [`Position`] for
/// more information.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct IonCError {
    pub code: i32,
    pub message: &'static str,
    pub additional: &'static str,
    pub position: Position,
}

/// Represents a position in a data source. For example, consider a file
/// containing Ion data that is being parsed using an [`IonCReader`].
///
/// If a position is set, `bytes` will always be hydrated while `lines` and
/// `offset` will only be populated for text readers.
#[derive(Copy, Clone, Debug, PartialEq)]
pub enum Position {
    Unknown,
    Offset(i64),
    OffsetLineColumn(i64, LineColumn),
}

// see above
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct LineColumn(pub i32, pub i32);

impl Position {
    /// Make a new position based on Ion text data. `line` and `offset` are
    /// known for text sources.
    pub fn text(bytes: i64, line: i32, offset: i32) -> Position {
        Position::OffsetLineColumn(bytes, LineColumn(line, offset))
    }

    /// Make a new position based on Ion binary data. Only the byte offset is
    /// known.
    pub fn binary(bytes: i64) -> Position {
        Position::Offset(bytes)
    }
}

impl IonCError {
    /// Constructs an `IonCError` from an `iERR` error code.
    pub fn from(code: i32) -> Self {
        Self::with_additional(code, "iERR Result")
    }

    /// Constructs an `IonCError` from an `iERR` error code and its own message
    pub fn with_additional(code: i32, additional: &'static str) -> Self {
        match code {
            ion_error_code_IERR_NOT_IMPL..=ion_error_code_IERR_INVALID_LOB_TERMINATOR => {
                unsafe {
                    // this gives us static storage pointer so it doesn't violate lifetime
                    let c_str = CStr::from_ptr(ion_error_to_str(code));
                    // the error codes are all ASCII so a panic here is a bug
                    let message = c_str.to_str().unwrap();
                    Self {
                        code,
                        message,
                        additional,
                        position: Position::Unknown,
                    }
                }
            }
            _ => Self {
                code,
                message: "Unknown Ion C Error Code",
                additional,
                position: Position::Unknown,
            },
        }
    }

    /// Adds a `Position` to an existing `IonCError`.
    pub fn with_position(mut self, pos: Position) -> Self {
        self.position = pos;
        self
    }
}

impl fmt::Display for IonCError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "Error {}: {} ({})",
            self.code, self.message, self.additional
        )
    }
}

impl Error for IonCError {}

impl From<TryFromIntError> for IonCError {
    /// Due to the way Ion C works with sizes as i32, it is convenient to be able to coerce
    /// a TryFromIntError to `IonCError`.
    fn from(_: TryFromIntError) -> Self {
        IonCError::from(ion_error_code_IERR_NUMERIC_OVERFLOW)
    }
}

impl From<Utf8Error> for IonCError {
    /// Due to the way Ion C works with raw UTF-8 byte sequences, it is convenient to be able
    /// to coerce a `Utf8Error` to `IonCError`.
    fn from(_: Utf8Error) -> Self {
        IonCError::from(ion_error_code_IERR_INVALID_UTF8)
    }
}

/// A type alias to results from Ion C API, the result value is generally `()` to signify
/// `ion_error_code_IERR_OK` since Ion C doesn't return results but generally takes
/// output parameters.
pub type IonCResult<T> = Result<T, IonCError>;

/// Macro to transform Ion C error code expressions into `Result<(), IonCError>`.
/// Higher-level facades over Ion C functions could map this to `Result<T, IonCError>`
/// or the like.
///
/// NB: `ionc!` implies `unsafe` code.
///
/// ## Usage
///
/// ```
/// # use std::ptr;
/// # use ion_c_sys::*;
/// # use ion_c_sys::result::*;
/// # fn main() -> IonCResult<()> {
/// let mut data = String::from("42");
/// let mut ion_reader: hREADER = ptr::null_mut();
/// let mut ion_type: ION_TYPE = ptr::null_mut();
/// ionc!(
///     ion_reader_open_buffer(
///         &mut ion_reader,
///         data.as_mut_ptr(),
///         data.len() as i32,
///         ptr::null_mut()
///     )
/// )?;
///
/// ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
/// assert_eq!(ion_type as u32, tid_INT_INT);
///
/// let mut value = 0;
/// ionc!(ion_reader_read_int64(ion_reader, &mut value))?;
/// assert_eq!(value, 42);
///
/// ionc!(ion_reader_close(ion_reader))
/// # }
/// ```
#[macro_export]
macro_rules! ionc {
    ($e:expr) => {
        unsafe {
            let err: i32 = $e;
            match err {
                $crate::ion_error_code_IERR_OK => Ok(()),
                code => Err($crate::result::IonCError::from(code)),
            }
        }
    };
}
