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
//! use ion_c_sys::*;
//! use ion_c_sys::result::*;
//! # fn main() -> Result<(), Box<dyn Error>> {
//!
//! use std::error::Error;
//! let mut input = String::from("{a:2}");
//!
//! let mut ion_reader: hREADER = ptr::null_mut();
//! let mut ion_type: ION_TYPE = ptr::null_mut();
//!
//! // open the reader over a buffer
//! ionc!(ion_reader_open_buffer(
//!     &mut ion_reader,
//!     input.as_mut_ptr(),
//!     input.len() as i32,
//!     ptr::null_mut() // default options
//! ))?;
//!
//! // step to the struct
//! ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
//! assert_eq!(ion_type as u32, tid_STRUCT_INT);
//!
//! // step into the struct
//! ionc!(ion_reader_step_in(ion_reader))?;
//!
//! // step to the field
//! ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
//! assert_eq!(ion_type as u32, tid_INT_INT);
//!
//! // retrieve the field name--which is 'borrowed' while we don't move the reader
//! let mut ion_str = ION_STRING::default();
//! ionc!(ion_reader_get_field_name(ion_reader, &mut ion_str))?;
//! assert_eq!(ion_str.as_str()?, "a");
//!
//! // read the integer value
//! let mut int_value: i64 = 0;
//! ionc!(ion_reader_read_int64(ion_reader, &mut int_value))?;
//! assert_eq!(int_value, 2);
//!
//! // step to the end of the struct
//! ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
//! assert_eq!(ion_type as i32, tid_EOF_INT);
//!
//! // step out of the struct
//! ionc!(ion_reader_step_out(ion_reader))?;
//!
//! // step to the end of the stream
//! ionc!(ion_reader_next(ion_reader, &mut ion_type))?;
//! assert_eq!(ion_type as i32, tid_EOF_INT);
//!
//! // close the reader
//! ionc!(ion_reader_close(ion_reader));
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
//!
//! use ion_c_sys::*;
//! use ion_c_sys::result::*;
//! # fn main() -> IonCResult {
//!
//! // output buffer
//! let mut buf: Vec<u8> = vec![0; 128];
//!
//! // writer options--emit binary
//! let mut writer_options = ION_WRITER_OPTIONS::default();
//! writer_options.output_as_binary = 1;
//!
//! let mut ion_writer: hWRITER = ptr::null_mut();
//!
//! // construct a writer
//! ionc!(ion_writer_open_buffer(
//!     &mut ion_writer,
//!     buf.as_mut_ptr(),
//!     buf.len() as i32,
//!     &mut writer_options
//! ))?;
//!
//! // start a list
//! ionc!(ion_writer_start_container(ion_writer, tid_LIST_INT as ION_TYPE))?;
//!
//! // write some integers
//! for n in 0..4 {
//!     ionc!(ion_writer_write_int64(ion_writer, n * 2))?;
//! }
//!
//! // end the list
//! ionc!(ion_writer_finish_container(ion_writer))?;
//!
//! // write a string--note that we have to make a ION_STRING to 'borrow' a reference to
//! let mut value = String::from("💩");
//! let mut ion_str = ION_STRING {
//!     value: value.as_mut_ptr(),
//!     length: value.len() as i32,
//! };
//! ionc!(ion_writer_write_string(ion_writer, &mut ion_str))?;
//!
//! // finish writing
//! let mut bytes_written = 0;
//! ionc!(ion_writer_finish(ion_writer, &mut bytes_written))?;
//!
//! // make sure the bytes match what we expect
//! assert_eq!(bytes_written, 17);
//! buf.truncate(bytes_written as usize);
//! let expected: Vec<u8> = vec![
//!     0xE0, 0x01, 0x00, 0xEA,         // IVM
//!     0xB7,                           // LIST size 7
//!     0x20,                           // INT 0
//!     0x21, 0x02,                     // INT 2
//!     0x21, 0x04,                     // INT 4
//!     0x21, 0x06,                     // INT 6
//!     0x84, 0xF0, 0x9F, 0x92, 0xA9,   // STRING 💩
//! ];
//! assert_eq!(&buf, &expected);
//! # Ok(())
//! # }
//! ```

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/ionc_bindings.rs"));

use std::{slice, str};
use std::str::Utf8Error;

impl ION_STRING {
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

pub mod result;

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
        assert_eq!(tid_NULL_INT, ion_type2 as u32);

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
        assert_eq!(tid_TIMESTAMP_INT, ion_type2 as u32);

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
        assert_eq!(tid_INT_INT, ion_type as u32);
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
        while ion_type as i32 != tid_EOF_INT {
            ionc!(ion_reader_next(ion_reader, &mut ion_type))?;

            let mut ion_value = 0;
            if tid_INT_INT == ion_type as u32 {
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