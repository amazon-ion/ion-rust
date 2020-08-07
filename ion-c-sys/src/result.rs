use crate::*;

use std::ffi::CStr;
use std::error::Error;
use std::fmt;
use std::num::TryFromIntError;

/// IonC Error code and its associated error message.
#[derive(Copy, Clone, Debug)]
pub struct IonCError {
    pub code: i32,
    pub message:  &'static str,
}

impl IonCError {
    /// Constructs and `IonCError` from an `iERR` error code.
    pub fn from(code: i32) -> IonCError {
        match code {
            ion_error_code_IERR_NOT_IMPL..=ion_error_code_IERR_INVALID_LOB_TERMINATOR => {
                unsafe {
                    // this gives us static storage pointer so it doesn't violate lifetime
                    let c_str = CStr::from_ptr(ion_error_to_str(code));
                    // the error codes are all ASCII so a panic here is a bug
                    let message = c_str.to_str().unwrap();
                    IonCError { code, message }
                }
            }
            _ => IonCError { code, message: "Unknown Ion C Error Code" },
        }
    }
}

impl fmt::Display for IonCError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Error {}: {}", self.code, self.message)
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
    }
}
