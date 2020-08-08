//! Provides basic bindings for [Ion C](https://github.com/amzn/ion-c)
//!
//! These bindings are created with `bindgen` and are considerably low-level.
//!
//! ## Examples
//! Using `ion-c-sys` directly can be a pretty verbose affair, and requires checking the
//! error code for most calls.  This crate provides the [`result`](result/index.html)
//! module to make it easier to integrate with `std::result::Result` with respect
//! to the `iERR` that Ion C functions generally return.  Specifically, any low-level
//! IonC function that returns `iERR` should be called with the [`ionc!`][ionc-call] macro
//! to facilitate `Result<(), IonCError>` conversion.
//!
//! This library provides smart pointers over the low-level reader/writer pointers, and should
//! generally be used, especially with `Result` handling code.  These types provide some facade
//! over Ion C, but only for the most generally used APIs. See:
//!
//! * [IonCReaderHandle][reader-handle]
//! * [IonCWriterHandle][writer-handle]
//!
//! [ionc-call]: macro.ionc.html
//! [reader-handle]: reader/struct.IonCReaderHandle.html
//! [writer-handle]: writer/struct.IonCWriterHandle.html
//!
//! ### Ion Reader
//! Here is an end-to-end example of reading some Ion data.
//!
//! ```
//! # use std::ptr;
//! # use std::slice;
//! # use std::str;
//! # use std::convert::TryFrom;
//! # use ion_c_sys::*;
//! # use ion_c_sys::reader::*;
//! # use ion_c_sys::result::*;
//! # fn main() -> IonCResult<()> {
//! let mut reader = IonCReaderHandle::try_from("{a:2}")?;
//!
//! // step to the struct
//! assert_eq!(ION_TYPE_STRUCT, reader.next()?);
//! // step into the struct
//! reader.step_in()?;
//! // step to the field
//! assert_eq!(ION_TYPE_INT, reader.next()?);
//! // retrieve the field name
//! assert_eq!("a", reader.get_field_name()?.try_as_str()?);
//! // read the integer value
//! assert_eq!(2, reader.read_i64()?);
//! // step to the end of the struct
//! assert_eq!(ION_TYPE_EOF, reader.next()?);
//! // step out of the struct
//! reader.step_out()?;
//! // step to the end of the stream
//! assert_eq!(ION_TYPE_EOF, reader.next()?);
//!
//! # Ok(())
//! # }
//! ```
//!
//! ### Ion Writer
//! Here is an end-to-end example of writing some Ion data.
//!
//! ```
//! # use std::ptr;
//! # use std::convert::TryInto;
//! # use ion_c_sys::*;
//! # use ion_c_sys::result::*;
//! # use ion_c_sys::writer::*;
//! # fn main() -> IonCResult<()> {
//! // output buffer
//! let mut buf: Vec<u8> = vec![0; 128];
//! let len = {
//!     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut(), WriterMode::Binary)?;
//!     // start a list
//!     writer.start_container(ION_TYPE_LIST)?;
//!     // write some integers
//!     for n in 0..4 {
//!         writer.write_i64(n * 2)?;
//!     }
//!     // end the list
//!     writer.finish_container()?;
//!     // write a string
//!     writer.write_string("💩")?;
//!     // finish writing
//!     writer.finish()?
//! };
//!
//! // make sure the bytes match what we expect
//! assert_eq!(len, 17);
//! let expected: Vec<u8> = vec![
//!     0xE0, 0x01, 0x00, 0xEA,         // IVM
//!     0xB7,                           // LIST size 7
//!     0x20,                           // INT 0
//!     0x21, 0x02,                     // INT 2
//!     0x21, 0x04,                     // INT 4
//!     0x21, 0x06,                     // INT 6
//!     0x84, 0xF0, 0x9F, 0x92, 0xA9,   // STRING 💩
//! ];
//! assert_eq!(expected.as_slice(), &buf[0..len]);
//!
//! # Ok(())
//! # }
//! ```

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

pub mod reader;
pub mod result;
pub mod string;
pub mod writer;

include!(concat!(env!("OUT_DIR"), "/ionc_bindings.rs"));

use std::convert::TryInto;
use std::str::Utf8Error;
use std::{slice, str};

use paste::paste;

use crate::result::*;

impl ION_STRING {
    /// Constructs an `ION_STRING` from a `&mut str`.
    ///
    /// Note that this is effectively Ion C's `&mut str` type so lifetime is managed
    /// manually by the caller.
    ///
    /// Also note, that it is possible to violate the UTF-8 invariant of the source
    /// data, so care should be taken when using this API.
    ///
    /// ## Usage
    /// Generally, using a mutable owned source will be the safest option.
    /// ```
    /// # use ion_c_sys::ION_STRING;
    /// let mut buf = "Some data".to_string();
    /// let mut ion_str = ION_STRING::from_mut_str(buf.as_mut_str());
    /// ```
    #[inline]
    pub fn from_mut_str(src: &mut str) -> Self {
        unsafe { Self::from_mut_bytes(src.as_bytes_mut()) }
    }

    /// Internal function to coerce an immutable slice to an `ION_STRING`.
    ///
    /// Inherently unsafe and can only be used with APIs that guarantee immutability.
    pub(crate) fn from_str(src: &str) -> Self {
        Self {
            value: src.as_ptr() as *mut u8,
            length: src.len().try_into().unwrap(),
        }
    }

    /// Constructs an `ION_STRING` from a `&mut [u8]`.
    ///
    /// Note that this is effectively Ion C's `&mut [u8]` type so lifetime is managed
    /// manually by the caller.
    ///
    /// ## Usage
    /// Generally, using a mutable owned source will be the safest option.
    /// ```
    /// # use ion_c_sys::ION_STRING;
    /// let mut buf = b"Some data".to_vec();
    /// let mut ion_str = ION_STRING::from_mut_bytes(buf.as_mut_slice());
    /// ```
    #[inline]
    pub fn from_mut_bytes(src: &mut [u8]) -> Self {
        ION_STRING {
            value: src.as_mut_ptr(),
            length: src.len().try_into().unwrap(),
        }
    }

    /// Retrieves a UTF-8 slice view from an `ION_STRING`.
    ///
    /// When the `value` pointer is `null`, the conversion will fail:
    /// ```
    /// # use ion_c_sys::*;
    /// let ion_str = ION_STRING::default();
    /// match ion_str.try_as_str() {
    ///     Ok(_) => panic!("Cannot happen!"),
    ///     Err(e) => assert_eq!(ion_error_code_IERR_NULL_VALUE, e.code),
    /// }
    /// ```
    ///
    /// When the string is not valid UTF-8, the conversion will fail:
    /// ```
    /// # use ion_c_sys::*;
    /// let mut buf = b"\xFF".to_vec();
    /// let ion_str = ION_STRING::from_mut_bytes(buf.as_mut_slice());
    /// match ion_str.try_as_str() {
    ///     Ok(_) => panic!("Cannot happen!"),
    ///     Err(e) => assert_eq!(ion_error_code_IERR_INVALID_UTF8, e.code),
    /// }
    /// ```
    #[inline]
    pub fn try_as_str(&self) -> Result<&str, IonCError> {
        Ok(str::from_utf8(self.try_as_bytes()?)?)
    }

    /// Retrieves a slice view from an `ION_STRING`
    ///
    /// When the `value` pointer is `null`, the conversion will return an `IonCError`:
    /// ```
    /// # use ion_c_sys::*;
    /// let ion_str = ION_STRING::default();
    /// match ion_str.try_as_bytes() {
    ///     Ok(_) => panic!("Cannot happen!"),
    ///     Err(e) => assert_eq!(ion_error_code_IERR_NULL_VALUE, e.code),
    /// }
    /// ```
    #[inline]
    pub fn try_as_bytes(&self) -> Result<&[u8], IonCError> {
        if self.value.is_null() {
            Err(IonCError::from(ion_error_code_IERR_NULL_VALUE))
        } else {
            unsafe {
                let u8_slice = slice::from_raw_parts(
                    // TODO determine if this is a bit harsh for >2GB buffers (should we return error?)
                    self.value,
                    self.length.try_into().unwrap(),
                );
                Ok(u8_slice)
            }
        }
    }
}

/// Generates easier to use constants for `ION_TYPE`
/// These exist as C macros in `ion_types.h` that don't get translated over from `bindgen`.
///
/// Using `ion_types!(NULL)` will generate a constant of the form:
/// ```
/// # use ion_c_sys::*;
/// pub const ION_TYPE_NULL: *mut ion_type = tid_NULL_INT as *mut ion_type;
/// ```
macro_rules! ion_types {
    ( $($name:ident),* ) => {
        $(
            paste! {
                pub const [<ION_TYPE_ $name:upper>]: *mut ion_type =
                    [<tid_ $name _INT>] as *mut ion_type;
            }
        )*
    };
}

ion_types!(
    none, EOF, NULL, BOOL, INT, FLOAT, DECIMAL, TIMESTAMP, SYMBOL, STRING, CLOB, BLOB, LIST, SEXP,
    STRUCT, DATAGRAM
);

#[cfg(test)]
mod tests {
    use super::*;

    use std::error::Error;
    use std::ptr;
    use std::string::String;

    type TestResult = Result<(), Box<dyn Error>>;

    #[test]
    fn read_ion_null() -> TestResult {
        let mut input = String::from("null");
        let buf = input.as_mut_ptr();
        let buf_size = input.len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        let mut ion_type2 = ptr::null_mut();
        let mut mybool: BOOL = 0;

        ionc!(ion_reader_open_buffer(
            &mut ion_reader,
            buf,
            buf_size,
            ptr::null_mut()
        ))?;
        ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
        ionc!(ion_reader_is_null(ion_reader, &mut mybool))?;
        if mybool == 1 {
            ionc!(ion_reader_read_null(ion_reader, &mut ion_type2))?;
        }
        assert_eq!(ION_TYPE_NULL, ion_type2);

        ionc!(ion_reader_close(ion_reader))?;

        Ok(())
    }

    #[test]
    fn read_ion_timestamp_null() -> TestResult {
        let mut input = String::from("null.timestamp");
        let buf = input.as_mut_ptr();
        let buf_size = input.len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        let mut ion_type2 = ptr::null_mut();
        let mut mybool: BOOL = 0;

        ionc!(ion_reader_open_buffer(
            &mut ion_reader,
            buf,
            buf_size,
            ptr::null_mut()
        ))?;
        ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
        ionc!(ion_reader_is_null(ion_reader, &mut mybool))?;
        if mybool == 1 {
            ionc!(ion_reader_read_null(ion_reader, &mut ion_type2))?;
        }
        assert_eq!(ION_TYPE_TIMESTAMP, ion_type2);

        ionc!(ion_reader_close(ion_reader))?;

        Ok(())
    }

    #[test]
    fn read_ion_int() -> TestResult {
        let mut input = String::from("42");
        let buf = input.as_mut_ptr();
        let buf_size = input.len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        let mut ion_value = 0;

        ionc!(ion_reader_open_buffer(
            &mut ion_reader,
            buf,
            buf_size,
            ptr::null_mut()
        ))?;
        ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
        ionc!(ion_reader_read_int32(ion_reader, &mut ion_value))?;
        assert_eq!(ION_TYPE_INT, ion_type);
        assert_eq!(42, ion_value);

        ionc!(ion_reader_close(ion_reader))?;

        Ok(())
    }

    #[test]
    fn read_ion_text() -> TestResult {
        let mut input = String::from("\"this is a string\"");
        let buf = input.as_mut_ptr();
        let buf_size = input.len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();

        ionc!(ion_reader_open_buffer(
            &mut ion_reader,
            buf,
            buf_size,
            ptr::null_mut()
        ))?;
        ionc!(ion_reader_next(ion_reader, &mut ion_type))?;

        let mut ion_str = ION_STRING::default();
        ionc!(ion_reader_read_string(ion_reader, &mut ion_str))?;
        assert_eq!("this is a string", ion_str.try_as_str()?);

        ionc!(ion_reader_close(ion_reader))?;

        Ok(())
    }

    #[test]
    fn read_ion_symbol() -> TestResult {
        let mut input = String::from("'this is a symbol'");
        let buf = input.as_mut_ptr();
        let buf_size = input.len() as i32;

        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();

        ionc!(ion_reader_open_buffer(
            &mut ion_reader,
            buf,
            buf_size,
            ptr::null_mut()
        ))?;
        ionc!(ion_reader_next(ion_reader, &mut ion_type))?;

        let mut ion_str = ION_STRING::default();
        ionc!(ion_reader_read_string(ion_reader, &mut ion_str))?;
        assert_eq!("this is a symbol", ion_str.try_as_str()?);

        ionc!(ion_reader_close(ion_reader))?;

        Ok(())
    }

    #[test]
    fn read_sexp() -> TestResult {
        let mut input = String::from("(1 2 3)");
        let expected_vals = vec![1, 2, 3];
        let mut read_vals: Vec<i32> = Vec::new();

        let buf = input.as_mut_ptr();
        let buf_size = input.len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();

        ionc!(ion_reader_open_buffer(
            &mut ion_reader,
            buf,
            buf_size,
            ptr::null_mut()
        ))?;
        ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
        ionc!(ion_reader_step_in(ion_reader))?;
        while ion_type != ION_TYPE_EOF {
            ionc!(ion_reader_next(ion_reader, &mut ion_type))?;

            let mut ion_value = 0;
            if ION_TYPE_INT == ion_type {
                ionc!(ion_reader_read_int32(ion_reader, &mut ion_value))?;
                read_vals.push(ion_value);
            }
        }
        ionc!(ion_reader_step_out(ion_reader))?;

        assert_eq!(read_vals, expected_vals);

        ionc!(ion_reader_close(ion_reader))?;

        Ok(())
    }
}
