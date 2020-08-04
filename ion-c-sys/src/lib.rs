//! Provides basic bindings for [Ion C](https://github.com/amzn/ion-c)
//!
//! These bindings are created with `bindgen` and are considerably low-level.
//!
//! ## Direct C API Examples
//! Using `ion-c-sys` directly is a pretty verbose affair, and requires checking the
//! error code for most calls.
//!
//! ### Ion Reader
//! Here is an end-to-end example of reading some Ion data.
//!
//! ```
//! use std::ptr;
//! use std::slice;
//! use std::str;
//! use ion_c_sys::*;
//!
//! let mut input = String::from("{a:2}");
//!
//! let mut ion_reader: hREADER = ptr::null_mut();
//! let mut ion_type: ION_TYPE = ptr::null_mut();
//!
//! // open the reader over a buffer
//! unsafe {
//!     let err = ion_reader_open_buffer(
//!         &mut ion_reader,
//!         input.as_mut_ptr(),
//!         input.len() as i32,
//!         ptr::null_mut() // default options
//!     );
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//!
//! // step to the struct
//! unsafe {
//!     let err = ion_reader_next(ion_reader, &mut ion_type);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//! assert_eq!(ion_type as u32, tid_STRUCT_INT);
//!
//! // step into the struct
//! unsafe {
//!     let err = ion_reader_step_in(ion_reader);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//!
//! // step to the field
//! unsafe {
//!     let err = ion_reader_next(ion_reader, &mut ion_type);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//! assert_eq!(ion_type as u32, tid_INT_INT);
//!
//! // retrieve the field name--which is 'borrowed' while we don't move the reader
//! let mut ion_str: ION_STRING = Default::default();
//! unsafe {
//!     let err = ion_reader_get_field_name(ion_reader, &mut ion_str);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//!
//!     let field_name = str::from_utf8(
//!         slice::from_raw_parts(ion_str.value, ion_str.length as usize)
//!     ).unwrap();
//!     assert_eq!(field_name, "a");
//! }
//!
//! // read the integer value
//! let mut int_value: i64 = 0;
//! unsafe {
//!     let err = ion_reader_read_int64(ion_reader, &mut int_value);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//! assert_eq!(int_value, 2);
//!
//! // step to the end of the struct
//! unsafe {
//!     let err = ion_reader_next(ion_reader, &mut ion_type);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//! assert_eq!(ion_type as i32, tid_EOF_INT);
//!
//! // step out of the struct
//! unsafe {
//!     let err = ion_reader_step_out(ion_reader);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//!
//! // step to the end of the stream
//! unsafe {
//!     let err = ion_reader_next(ion_reader, &mut ion_type);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//! assert_eq!(ion_type as i32, tid_EOF_INT);
//!
//! // close the reader
//! unsafe {
//!     let err = ion_reader_close(ion_reader);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//! ```
//!
//! ### Ion Writer
//! Here is an end-to-end example of writing some Ion data.
//!
//! ```
//! use std::ptr;
//! use ion_c_sys::*;
//!
//! // output buffer
//! let mut buf: Vec<u8> = vec![0; 128];
//!
//! // writer options--emit binary
//! let mut writer_options: ION_WRITER_OPTIONS = Default::default();
//! writer_options.output_as_binary = 1;
//!
//! let mut ion_writer: hWRITER = ptr::null_mut();
//!
//! // construct a writer
//! unsafe {
//!     let err = ion_writer_open_buffer(
//!         &mut ion_writer,
//!         buf.as_mut_ptr(),
//!         buf.len() as i32,
//!         &mut writer_options
//!     );
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//!
//! // start a list
//! unsafe {
//!     let err = ion_writer_start_container(ion_writer, tid_LIST_INT as ION_TYPE);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//!
//! // write some integers
//! for n in 0..4 {
//!     unsafe {
//!         let err = ion_writer_write_int64(ion_writer, n * 2);
//!         assert_eq!(err, ion_error_code_IERR_OK);
//!     }
//! }
//!
//! // end the list
//! unsafe {
//!     let err = ion_writer_finish_container(ion_writer);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//!
//! // write a string--note that we have to make a ION_STRING to 'borrow' a reference to
//! let mut value = String::from("💩");
//! let mut ion_str = ION_STRING {
//!     value: value.as_mut_ptr(),
//!     length: value.len() as i32,
//! };
//! unsafe {
//!     let err = ion_writer_write_string(ion_writer, &mut ion_str);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
//!
//! // finish writing
//! let mut bytes_written = 0;
//! unsafe {
//!     let err = ion_writer_finish(ion_writer, &mut bytes_written);
//!     assert_eq!(err, ion_error_code_IERR_OK);
//! }
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
//! assert_eq!(&buf, &expected)
//! ```

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

include!(concat!(env!("OUT_DIR"), "/ionc_bindings.rs"));

#[cfg(test)]
mod tests {
    use super::*;
    use std::ffi::CStr;
    use std::ffi::CString;
    use std::ptr;

    fn close_reader(reader: hREADER) {
        unsafe {
            ion_reader_close(reader);
        }
    }

    #[test]
    fn read_ion_null() {
        let input = CString::new("null").unwrap();
        let buf = input.as_ptr() as *mut u8;
        let buf_size = input.as_bytes_with_nul().len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        let mut ion_type2 = ptr::null_mut();
        let mut mybool: BOOL = 0;

        unsafe {
            ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut());
            ion_reader_next(ion_reader, &mut ion_type);
            ion_reader_is_null(ion_reader, &mut mybool);
            if mybool == 1 {
                ion_reader_read_null(ion_reader, &mut ion_type2);
            }
        }
        assert_eq!(0x000, ion_type2 as i32);
        close_reader(ion_reader);
    }

    #[test]
    fn read_ion_timestamp_null() {
        let input = CString::new("null.timestamp").unwrap();
        let buf = input.as_ptr() as *mut u8;
        let buf_size = input.as_bytes_with_nul().len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        let mut ion_type2 = ptr::null_mut();
        let mut mybool: BOOL = 0;

        unsafe {
            ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut());
            ion_reader_next(ion_reader, &mut ion_type);
            ion_reader_is_null(ion_reader, &mut mybool);
            if mybool == 1 {
                ion_reader_read_null(ion_reader, &mut ion_type2);
            }
        }
        assert_eq!(0x600, ion_type2 as i32);
        close_reader(ion_reader);
    }

    #[test]
    fn read_ion_int() {
        let input = CString::new("42").unwrap();
        let buf = input.as_ptr() as *mut u8;
        let buf_size = input.as_bytes_with_nul().len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        let mut ion_value = 0;
        unsafe {
            ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut());
            ion_reader_next(ion_reader, &mut ion_type);
            ion_reader_read_int32(ion_reader, &mut ion_value);
        }
        assert_eq!(0x200, ion_type as i32);
        assert_eq!(42, ion_value);
        close_reader(ion_reader);
    }

    #[test]
    fn read_ion_text() {
        let input = CString::new("\"this is a string\"").unwrap();
        let buf = input.as_ptr() as *mut u8;
        let buf_size = input.as_bytes_with_nul().len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        let mut ion_str_size = 0;
        let mut ion_str = _ion_string {
            length: ion_str_size,
            value: ptr::null_mut(),
        };

        unsafe {
            ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut());
            ion_reader_next(ion_reader, &mut ion_type);
            ion_reader_get_string_length(ion_reader, &mut ion_str_size);
            ion_reader_read_string(ion_reader, &mut ion_str);
        }

        unsafe {
            let yy = CStr::from_ptr(ion_str.value as *mut i8);
            let xx = match yy.to_str() {
                Ok(v) => v,
                Err(e) => panic!("BOOM! {:?}", e),
            };
            assert_eq!("this is a string", xx);
        }
        close_reader(ion_reader);
    }

    #[test]
    fn read_ion_symbol() {
        let input = CString::new("'this is a symbol'").unwrap();
        let buf = input.as_ptr() as *mut u8;
        let buf_size = input.as_bytes_with_nul().len() as i32;

        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        let mut ion_str_size = 0;

        let mut ion_str = _ion_string {
            length: ion_str_size,
            value: ptr::null_mut(),
        };

        unsafe {
            ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut());
            ion_reader_next(ion_reader, &mut ion_type);
            ion_reader_get_string_length(ion_reader, &mut ion_str_size);
            ion_reader_read_string(ion_reader, &mut ion_str);
        }

        unsafe {
            let yy = CStr::from_ptr(ion_str.value as *mut i8);
            let xx = match yy.to_str() {
                Ok(v) => v,
                Err(e) => panic!("BOOM! {:?}", e),
            };
            assert_eq!("this is a symbol", xx);
        }
        close_reader(ion_reader);
    }


    #[test]
    fn read_sexp() {
        let input = CString::new("(1 2 3)").unwrap();
        let expected_vals = vec![1,2,3];
        let mut read_vals: Vec<i32>  = Vec::new();

        let buf = input.as_ptr() as *mut u8;
        let buf_size = input.as_bytes_with_nul().len() as i32;
        let mut ion_reader = ptr::null_mut();
        let mut ion_type = ptr::null_mut();
        unsafe {
            ion_reader_open_buffer(&mut ion_reader, buf, buf_size, ptr::null_mut());
            ion_reader_next(ion_reader, &mut ion_type);
            ion_reader_step_in(ion_reader);
            while ion_type as i32 != -0x100 {
                ion_reader_next(ion_reader, &mut ion_type);

                let mut ion_value = 0;
                if 0x200 == ion_type as i32 {
                    ion_reader_read_int32(ion_reader, &mut ion_value);
                    read_vals.push(ion_value);
                }
            }
            ion_reader_step_out(ion_reader);

            assert_eq!(read_vals, expected_vals);
        }

        close_reader(ion_reader);
    }
}