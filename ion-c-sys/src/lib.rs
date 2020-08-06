//! Provides basic bindings for [Ion C](https://github.com/amzn/ion-c)
//!
//! These bindings are created with `bindgen` and are considerably low-level.
//!
//! ## Examples
//! Using `ion-c-sys` directly is a pretty verbose affair, and requires checking the
//! error code for most calls.  This crate provides the [`result`](result/index.html)
//! module to make it easier to integrate with `std::result::Result` with respect
//! to the `iERR` that Ion C functions generally return.
//!
//! ### Ion Reader
//! Here is an end-to-end example of reading some Ion data.
//!
//! ```
//! # use std::error::Error;
//! use std::ptr;
//! use std::slice;
//! use std::str;
//! 
//! use std::convert::TryFrom;
//!
//! use ion_c_sys::*;
//! use ion_c_sys::reader::*;
//! use ion_c_sys::result::*;
//! # fn main() -> Result<(), Box<dyn Error>> {
//!
//! let mut input = String::from("{a:2}");
//!
//! let reader: IonCReaderHandle = IonCReaderHandle::try_from(input.as_mut_str())?;
//! let mut tid: ION_TYPE = ptr::null_mut();
//!
//! // step to the struct
//! ionc!(ion_reader_next(*reader, &mut tid))?;
//! assert_eq!(tid, ION_TYPE_STRUCT);
//!
//! // step into the struct
//! ionc!(ion_reader_step_in(*reader))?;
//!
//! // step to the field
//! ionc!(ion_reader_next(*reader, &mut tid))?;
//! assert_eq!(tid, ION_TYPE_INT);
//!
//! // retrieve the field name--which is 'borrowed' while we don't move the reader
//! let mut ion_str = ION_STRING::default();
//! ionc!(ion_reader_get_field_name(*reader, &mut ion_str))?;
//! assert_eq!(ion_str.as_str()?, "a");
//!
//! // read the integer value
//! let mut int_value: i64 = 0;
//! ionc!(ion_reader_read_int64(*reader, &mut int_value))?;
//! assert_eq!(int_value, 2);
//!
//! // step to the end of the struct
//! ionc!(ion_reader_next(*reader, &mut tid))?;
//! assert_eq!(tid, ION_TYPE_EOF);
//!
//! // step out of the struct
//! ionc!(ion_reader_step_out(*reader))?;
//!
//! // step to the end of the stream
//! ionc!(ion_reader_next(*reader, &mut tid))?;
//! assert_eq!(tid, ION_TYPE_EOF);
//!
//! # Ok(())
//! # }
//! ```
//!
//! ### Ion Writer
//! Here is an end-to-end example of writing some Ion data.
//!
//! ```
//! use std::ptr;
//! use std::convert::TryInto;
//!
//! use ion_c_sys::*;
//! use ion_c_sys::result::*;
//! use ion_c_sys::writer::*;
//! # fn main() -> IonCResult {
//!
//! // output buffer
//! let mut buf: Vec<u8> = vec![0; 128];
//!
//! // writer options--emit binary
//! let mut options = ION_WRITER_OPTIONS {
//!     output_as_binary: 1,
//!     .. ION_WRITER_OPTIONS::default()
//! };
//!
//! let mut len = 0;
//! {
//!     let writer = IonCWriterHandle::new_buf(buf.as_mut(), &mut options)?;
//!
//!     // start a list
//!     ionc!(ion_writer_start_container(*writer, ION_TYPE_LIST))?;
//!
//!     // write some integers
//!     for n in 0..4 {
//!         ionc!(ion_writer_write_int64(*writer, n * 2))?;
//!     }
//!
//!     // end the list
//!     ionc!(ion_writer_finish_container(*writer))?;
//!
//!     // write a string--note that we have to make a ION_STRING to 'borrow' a reference to
//!     let mut value = String::from("💩");
//!     let mut ion_str = ION_STRING::from(value.as_mut());
//!     ionc!(ion_writer_write_string(*writer, &mut ion_str))?;
//!
//!     // finish writing
//!     ionc!(ion_writer_finish(*writer, &mut len))?;
//! }
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
//! assert_eq!(&buf[0..len.try_into()?], expected.as_slice());
//!
//! # Ok(())
//! # }
//! ```

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

pub mod result;
pub mod reader;
pub mod writer;

include!(concat!(env!("OUT_DIR"), "/ionc_bindings.rs"));

use std::{slice, str};
use std::convert::TryInto;
use std::str::Utf8Error;

use paste::paste;

impl ION_STRING {
    /// Constructs an `ION_STRING` from a `&mut str`.
    ///
    /// Note that this is effectively Ion C's `str` type so lifetime is managed
    /// manually by the caller.
    ///
    /// ## Usage
    /// Generally, using a mutable owned source will be the safest option.
    /// ```
    /// # use ion_c_sys::ION_STRING;
    /// let mut buf = String::from("Some data");
    /// let mut ion_str = ION_STRING::from(buf.as_mut_str());
    /// ```
    #[inline]
    pub fn from(src: &mut str) -> Self {
        ION_STRING { value: src.as_mut_ptr(), length: src.len().try_into().unwrap() }
    }

    /// Retrieves a UTF-8 slice view from an `ION_STRING`.
    #[inline]
    pub fn as_str(&self) -> Result<&str, Utf8Error> {
        unsafe {
            let u8_slice = slice::from_raw_parts(
                self.value, self.length as usize
            );
            str::from_utf8(u8_slice)
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
    none,
    EOF,
    NULL,
    BOOL,
    INT,
    FLOAT,
    DECIMAL,
    TIMESTAMP,
    SYMBOL,
    STRING,
    CLOB,
    BLOB,
    LIST,
    SEXP,
    STRUCT,
    DATAGRAM
);

#[cfg(test)]
mod tests {
    use super::*;

    use std::error::Error;
    use std::string::String;
    use std::ptr;

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

        ionc!(ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut()))?;
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

        ionc!(ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut()))?;
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

        ionc!(ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut()))?;
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

        ionc!(ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut()))?;
        ionc!(ion_reader_next(ion_reader, &mut ion_type))?;

        let mut ion_str = ION_STRING::default();
        ionc!(ion_reader_read_string(ion_reader, &mut ion_str))?;
        assert_eq!("this is a string", ion_str.as_str()?);

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

        ionc!(ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut()))?;
        ionc!(ion_reader_next(ion_reader, &mut ion_type))?;

        let mut ion_str = ION_STRING::default();
        ionc!(ion_reader_read_string(ion_reader, &mut ion_str))?;
        assert_eq!("this is a symbol", ion_str.as_str()?);

        ionc!(ion_reader_close(ion_reader))?;

        Ok(())
    }


    #[test]
    fn read_sexp() -> TestResult {
        let mut input = String::from("(1 2 3)");
        let expected_vals = vec![1,2,3];
        let mut read_vals: Vec<i32>  = Vec::new();

        let buf = input.as_mut_ptr();
        let buf_size = input.len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();

        ionc!(ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut()))?;
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