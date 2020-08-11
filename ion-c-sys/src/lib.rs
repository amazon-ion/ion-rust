// Copyright Amazon.com, Inc. or its affiliates.

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
//! assert_eq!("a", reader.get_field_name()?.as_str());
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
//!     // start a struct
//!     writer.start_container(ION_TYPE_STRUCT)?;
//!     {
//!         // write a string
//!         writer.field("name").annotations(&["version"]).write_string("💩")?;
//!     }
//!     // end the struct
//!     writer.finish_container()?;
//!     // finish writing
//!     writer.finish()?
//! };
//!
//! // make sure the bytes match what we expect
//! let expected: &[u8] = &[
//!     0xE0, 0x01, 0x00, 0xEA,         // IVM
//!     0xB7,                           // LIST size 7
//!     0x20,                           // INT 0
//!     0x21, 0x02,                     // INT 2
//!     0x21, 0x04,                     // INT 4
//!     0x21, 0x06,                     // INT 6
//!     0xD9,                           // STRUCT size 8
//!     0x84,                           // field "name" (sid 4)
//!     0xE7, 0x81, 0x85,               // annotation "version" (sid 5)
//!     0x84, 0xF0, 0x9F, 0x92, 0xA9,   // STRING 💩
//! ];
//! assert_eq!(expected.len(), len);
//! assert_eq!(expected, &buf[0..len]);
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
use std::marker::PhantomData;
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
    /// # use ion_c_sys::result::IonCResult;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = "Some data".to_string();
    /// let mut ion_str = ION_STRING::try_from_mut_str(buf.as_mut_str())?;
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn try_from_mut_str(src: &mut str) -> IonCResult<Self> {
        unsafe { Self::try_from_mut_bytes(src.as_bytes_mut()) }
    }

    /// Internal function to coerce an immutable slice to an `ION_STRING`.
    ///
    /// Inherently unsafe and can only be used with APIs that guarantee immutability.
    #[inline]
    fn try_from_str(src: &str) -> IonCResult<Self> {
        Ok(Self {
            value: src.as_ptr() as *mut u8,
            length: src.len().try_into()?,
        })
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
    /// # use ion_c_sys::result::IonCResult;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = b"Some data".to_vec();
    /// let mut ion_str = ION_STRING::try_from_mut_bytes(buf.as_mut_slice())?;
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn try_from_mut_bytes(src: &mut [u8]) -> IonCResult<Self> {
        Ok(ION_STRING {
            value: src.as_mut_ptr(),
            length: src.len().try_into()?,
        })
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
    /// let ion_str = ION_STRING::try_from_mut_bytes(buf.as_mut_slice()).unwrap();
    /// match ion_str.try_as_str() {
    ///     Ok(_) => panic!("Cannot happen!"),
    ///     Err(e) => assert_eq!(ion_error_code_IERR_INVALID_UTF8, e.code),
    /// }
    /// ```
    #[inline]
    pub fn try_as_str(&self) -> IonCResult<&str> {
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
    pub fn try_as_bytes<'a>(&'a self) -> IonCResult<&'a [u8]> {
        self.as_bytes(PhantomData::<&'a u8>::default())
    }

    /// Low-level conversion into an str reference tied to the given owner without UTF-8 validation
    fn as_str<'a>(&self, life: PhantomData<&'a u8>) -> IonCResult<&'a str> {
        unsafe {
            let raw_slice: &'a [u8] = self.as_bytes(life)?;
            // Better make sure this came from an Ion C call that checks this
            let str_slice = str::from_utf8_unchecked(raw_slice);
            Ok(str_slice)
        }
    }

    /// Low-level conversion into a slice associated with a given owner
    fn as_bytes<'a>(&self, _life: PhantomData<&'a u8>) -> IonCResult<&'a [u8]> {
        // note that we need to build the str slice at a very low level
        // to tie the lifetime to the reader
        if self.value.is_null() {
            Err(IonCError::from(ion_error_code_IERR_NULL_VALUE))
        } else {
            unsafe {
                let u8_slice = slice::from_raw_parts(self.value, self.length.try_into()?);
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
