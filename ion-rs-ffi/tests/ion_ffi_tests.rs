extern crate libc;

use ion_rs_ffi::{IonResult, IonType};
use libc::c_char;
use std::ffi::{CStr, CString};
use std::ops::Deref;
use std::ptr::null_mut;

#[link(name = "ion_rs_ffi")]
extern "C" {
    fn read_one(_input: *const c_char) -> *mut IonResult;
}

#[test]
fn read_symbol_and_string() {
    unsafe {
        let inputs = vec!["\"foo\"", "foo"];
        for input in inputs.iter() {
            let str = CString::new(input.as_bytes()).unwrap();
            let result = Box::from_raw(read_one(str.as_ptr()));
            match result.deref() {
                IonResult::Error(_) => panic!("expected result!"),
                IonResult::Value(v) => match v.ion_type {
                    IonType::Symbol | IonType::String => {
                        assert_eq!(
                            "foo",
                            CStr::from_ptr(v.ptr as *const c_char).to_str().unwrap()
                        );
                    }
                    _ => panic!("expected Symbol!"),
                },
            }
        }
    };
}

#[test]
fn nulls_are_null() {
    unsafe {
        let inputs = vec!["null", "null.symbol"];
        for input in inputs.iter() {
            let str = CString::new(input.as_bytes()).unwrap();
            let result = Box::from_raw(read_one(str.as_ptr()));
            match result.deref() {
                IonResult::Error(_) => panic!("expected result!"),
                IonResult::Value(v) => {
                    assert_eq!(null_mut(), v.ptr);
                }
            }
        }
    }
}

#[test]
fn bad_ion() {
    unsafe {
        let str = CString::new("{").unwrap();
        let result = Box::from_raw(read_one(str.as_ptr()));

        match result.deref() {
            IonResult::Value(_) => panic!("expected error!"),
            IonResult::Error(_) => (),
        }
    };
}
