/// ffi api to ion-rs
extern crate libc;

use ion_rs::value::ion_c_reader::IonCElementReader;
use ion_rs::value::reader::ElementReader;
use ion_rs::value::Element;
use ion_rs::IonType as IonRsType;
use libc::{c_char, c_void, size_t};
use std::ffi::CString;
use std::panic::catch_unwind;
use std::ptr::{null_mut, slice_from_raw_parts};

/// Reads a single value from the input, which may be text or binary.
/// Callers are expected to free the results, both values and errors,
/// with the free_result function.
#[no_mangle]
pub extern "C" fn read_one(input: *const u8, len: size_t) -> *mut IonResult {
    let rs_data = unsafe { &*slice_from_raw_parts(input, len) };

    let result = catch_unwind(|| {
        match IonCElementReader.read_one(rs_data) {
            Ok(e) => {
                let t = e.ion_type();
                let nvl = e.is_null();

                let rt = match t {
                    IonRsType::Null => IonType::Null,
                    IonRsType::Symbol => IonType::Symbol,
                    IonRsType::String => IonType::String,
                    _ => {
                        todo!()
                    }
                };
                // handling all null values here cuts redundant branching
                let ptr = if nvl {
                    null_mut()
                } else {
                    match rt {
                        // TODO: this doesn't handle NULL chars correctly!!!
                        IonType::Symbol | IonType::String => {
                            CString::new(e.as_str().unwrap()).unwrap().into_raw()
                        }
                        // should be dead branch, but makes compiler happy
                        IonType::Null => null_mut(),
                    }
                };
                IonResult::Value(IonValue {
                    ion_type: rt,
                    ptr: ptr as *mut c_void,
                })
            }
            Err(_) => IonResult::Error(IonError {
                message: CString::new("Default Error Message").unwrap().into_raw(),
            }),
        }
    })
    .unwrap_or_else(|_| {
        IonResult::Error(IonError {
            message: CString::new("caught panic").unwrap().into_raw(),
        })
    });

    Box::into_raw(Box::new(result))
}

/// Frees IonResults created by the read apis.
/// It is an error to call more than once for a result.
#[no_mangle]
pub extern "C" fn free_result(rptr: *mut IonResult) {
    unsafe {
        Box::from_raw(rptr);
    }
}

#[repr(C)]
pub enum IonResult {
    Value(IonValue),
    Error(IonError),
}

#[repr(C)]
#[derive(Debug)]
pub enum IonType {
    Null,
    String,
    Symbol,
}

/// TODO: consider modeling as enum to capture all the variant
///       value pointer types for each IonType
#[repr(C)]
pub struct IonValue {
    pub ion_type: IonType,
    pub ptr: *mut c_void,
}

impl Drop for IonValue {
    fn drop(&mut self) {
        unsafe { Box::from_raw(self.ptr) };
    }
}

#[repr(C)]
pub struct IonError {
    pub message: *mut c_char,
}

impl Drop for IonError {
    fn drop(&mut self) {
        unsafe { CString::from_raw(self.message) };
    }
}
