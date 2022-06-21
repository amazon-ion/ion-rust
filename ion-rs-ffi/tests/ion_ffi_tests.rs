extern crate libc;

use libc::c_char;
use ion_rs_ffi::{IonResult, IonType};
use std::ffi::{CString, CStr};
use std::ops::Deref;

#[link(name="ion_rs_ffi")]
extern "C" {
    fn read_one(_input: *const c_char) -> *mut IonResult;
}

#[test]
fn read_one_symbol() {
    unsafe {
        let str = CString::new("foo").unwrap();
        let result = Box::from_raw(read_one(str.as_ptr()));

        match result.deref() {
            IonResult::Error(_) => panic!("expected result!"),
            IonResult::Value(v) => {
                match v.ion_type {
                    IonType::Symbol => {
                        assert_eq!("foo", CStr::from_ptr(v.ptr as *const c_char).to_str().unwrap());
                    }
                    _ => panic!("expected Symbol!")
                }
            }
        }
    };
}

#[test]
fn bad_ion() {
    unsafe {
        let str = CString::new("{").unwrap();
        let result = Box::from_raw(read_one(str.as_ptr()));

        match result.deref() {
            IonResult::Value(_) => panic!("expected error!"),
            IonResult::Error(_) => ()
        }
    };
}
