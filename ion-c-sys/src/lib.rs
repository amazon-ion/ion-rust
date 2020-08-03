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

        // let mut ion_value = 0;
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

        // let mut ion_value = 0;
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