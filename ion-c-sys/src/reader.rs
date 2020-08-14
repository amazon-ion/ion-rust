// Copyright Amazon.com, Inc. or its affiliates.

//! Provides higher-level APIs for Ion C's `hREADER`.

use std::convert::{TryFrom, TryInto};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::os::raw::c_int;
use std::ptr;

use crate::result::*;
use crate::string::*;
use crate::*;

/// Wrapper over `hREADER` to make it easier to use readers in IonC correctly.
///
/// Specifically supports the `Drop` trait to make sure `ion_reader_close` is run.
/// Access to the underlying `hREADER` pointer is done by de-referencing the handle.
///
/// ## Usage
/// ```
/// # use ion_c_sys::*;
/// # use ion_c_sys::reader::*;
/// # use ion_c_sys::result::*;
/// # use std::convert::*;
/// # use std::ptr;
/// # fn main() -> IonCResult<()> {
/// let mut reader = IonCReaderHandle::try_from(b"\xE0\x01\x00\xEA\x85hello".as_ref())?;
/// let tid = reader.next()?;
/// assert_eq!(ION_TYPE_STRING, tid);
/// // reader_handle implements Drop, so we're good to go!
/// # Ok(())
/// # }
/// ```
pub struct IonCReaderHandle<'a> {
    reader: hREADER,
    /// Placeholder to tie our lifecycle back to the source of the data--which might not
    /// actually be a byte slice (if we constructed this from a file or Ion C stream callback)
    referent: PhantomData<&'a [u8]>,
}

impl<'a> IonCReaderHandle<'a> {
    /// Constructs a reader handle from a byte slice and given options.
    pub fn new_buf(src: &'a [u8], options: &mut ION_READER_OPTIONS) -> Result<Self, IonCError> {
        let mut reader = ptr::null_mut();
        ionc!(ion_reader_open_buffer(
            &mut reader,
            // Ion C promises not to mutate this buffer!
            src.as_ptr() as *mut u8,
            src.len().try_into()?,
            options,
        ))?;
        Ok(IonCReaderHandle {
            reader,
            referent: PhantomData::default(),
        })
    }

    /// Advances the reader to the next value and returns the type.
    #[inline]
    pub fn next(&mut self) -> IonCResult<ION_TYPE> {
        let mut tid = ptr::null_mut();
        ionc!(ion_reader_next(self.reader, &mut tid))?;

        Ok(tid)
    }

    /// Returns the type of the current position.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("'''hello!'''")?;
    /// assert_eq!(ION_TYPE_NONE, reader.get_type()?);
    /// assert_eq!(ION_TYPE_STRING, reader.next()?);
    /// assert_eq!(ION_TYPE_STRING, reader.get_type()?);
    /// assert_eq!(ION_TYPE_EOF, reader.next()?);
    /// assert_eq!(ION_TYPE_EOF, reader.get_type()?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn get_type(&self) -> IonCResult<ION_TYPE> {
        let mut tid = ptr::null_mut();
        ionc!(ion_reader_get_type(self.reader, &mut tid))?;

        Ok(tid)
    }

    /// Steps in to the current container.
    #[inline]
    pub fn step_in(&mut self) -> IonCResult<()> {
        ionc!(ion_reader_step_in(self.reader))
    }

    /// Steps out of the current container.
    #[inline]
    pub fn step_out(&mut self) -> IonCResult<()> {
        ionc!(ion_reader_step_out(self.reader))
    }

    /// Returns the current container depth.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("[[]]")?;
    /// assert_eq!(ION_TYPE_LIST, reader.next()?);
    /// reader.step_in()?;
    /// assert_eq!(1, reader.depth()?);
    /// assert_eq!(ION_TYPE_LIST, reader.next()?);
    /// reader.step_in()?;
    /// assert_eq!(2, reader.depth()?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn depth(&self) -> IonCResult<i32> {
        let mut depth = 0;
        ionc!(ion_reader_get_depth(self.reader, &mut depth))?;

        Ok(depth)
    }

    /// Returns if the reader is positioned on a `null` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("null.int 4")?;
    /// assert_eq!(ION_TYPE_INT, reader.next()?);
    /// assert!(reader.is_null()?);
    /// assert_eq!(ION_TYPE_INT, reader.next()?);
    /// assert!(!reader.is_null()?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn is_null(&self) -> IonCResult<bool> {
        let mut is_null = 0;
        ionc!(ion_reader_is_null(self.reader, &mut is_null))?;

        Ok(is_null != 0)
    }

    /// Returns if the reader is positioned within a `struct` value.
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("{}")?;
    /// assert_eq!(ION_TYPE_STRUCT, reader.next()?);
    /// assert!(!reader.is_in_struct()?);
    /// reader.step_in()?;
    /// assert!(reader.is_in_struct()?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn is_in_struct(&self) -> IonCResult<bool> {
        let mut is_in_struct = 0;
        ionc!(ion_reader_is_in_struct(self.reader, &mut is_in_struct))?;

        Ok(is_in_struct != 0)
    }

    /// Returns the field name if the reader positioned within a structure.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # use ion_c_sys::string::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("{a:5}")?;
    /// assert_eq!(ION_TYPE_STRUCT, reader.next()?);
    /// reader.step_in()?;
    /// assert_eq!(ION_TYPE_INT, reader.next()?);
    /// assert_eq!("a", reader.get_field_name()?.as_str());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn get_field_name(&mut self) -> IonCResult<StrSliceRef> {
        let mut field = ION_STRING::default();
        ionc!(ion_reader_get_field_name(self.reader, &mut field))?;

        // make a str slice that is tied to our lifetime
        let field_str = field.as_str(PhantomData::<&'a u8>::default())?;
        Ok(StrSliceRef::new(self, field_str))
    }

    /// Retrieves the annotations associated with the current value.
    ///
    /// Note that this allocates a vector on the heap for the `IonCStringRef` instances.
    /// If this is not desired, use the low-level annotation functions.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # use ion_c_sys::string::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("ab::cde::fghi::5")?;
    /// assert_eq!(ION_TYPE_INT, reader.next()?);
    /// let annotations = reader.get_annotations()?;
    /// assert_eq!(
    ///     vec!["ab", "cde", "fghi"].as_slice(),
    ///     annotations.as_ref()
    /// );
    /// # Ok(())
    /// # }
    /// ```
    pub fn get_annotations(&mut self) -> IonCResult<StrSlicesRef> {
        // determine how many annotations are available
        let mut raw_len = 0;
        ionc!(ion_reader_get_annotation_count(self.reader, &mut raw_len))?;

        let len: usize = raw_len.try_into()?;
        let mut annotations = Vec::new();
        let mut curr = ION_STRING::default();
        for i in 0..len {
            ionc!(ion_reader_get_an_annotation(
                self.reader,
                i as c_int,
                &mut curr
            ))?;
            // make a str slice that is tied to our lifetime
            annotations.push(curr.as_str(PhantomData::<&'a u8>::default())?);
        }

        Ok(StrSlicesRef::new(self, annotations))
    }

    /// Reads a `bool` value from the reader.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("true")?;
    /// assert_eq!(ION_TYPE_BOOL, reader.next()?);
    /// assert!(reader.read_bool()?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn read_bool(&mut self) -> IonCResult<bool> {
        let mut value = 0;
        ionc!(ion_reader_read_bool(self.reader, &mut value))?;

        Ok(value != 0)
    }

    /// Reads an `int` value from the reader.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("42")?;
    /// assert_eq!(ION_TYPE_INT, reader.next()?);
    /// assert_eq!(42, reader.read_i64()?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn read_i64(&mut self) -> IonCResult<i64> {
        let mut value = 0;
        ionc!(ion_reader_read_int64(self.reader, &mut value))?;

        Ok(value)
    }

    /// Reads an `int` value from the reader as a `BigInt`.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # use num_bigint::BigInt;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("0x5195a4b154400e07dee3a7378c403b2d5dd6dd58735")?;
    /// assert_eq!(ION_TYPE_INT, reader.next()?);
    /// assert_eq!(
    ///   BigInt::parse_bytes(b"1907775120294590714755986204580814176547217067050805", 10).unwrap(),
    ///   reader.read_bigint()?
    /// );
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn read_bigint(&mut self) -> IonCResult<BigInt> {
        let mut value = ION_INT::default();
        ionc!(ion_reader_read_ion_int(self.reader, &mut value))?;

        Ok(value.try_to_bigint()?)
    }

    /// Reads a `float` value from the reader.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("3.0e0")?;
    /// assert_eq!(ION_TYPE_FLOAT, reader.next()?);
    /// assert_eq!(3.0, reader.read_f64()?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn read_f64(&mut self) -> IonCResult<f64> {
        let mut value = 0.0;
        ionc!(ion_reader_read_double(self.reader, &mut value))?;

        Ok(value)
    }

    /// Reads a `bigdecimal` value from the reader.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use bigdecimal::BigDecimal;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::decimal::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("3.0")?;
    /// assert_eq!(ION_TYPE_DECIMAL, reader.next()?);
    /// let value = BigDecimal::parse_bytes(b"30E-1", 10).unwrap();
    /// assert_eq!(value, reader.read_bigdecimal()?);
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn read_bigdecimal(&mut self) -> IonCResult<BigDecimal> {
        let mut value = ION_DECIMAL::default();
        ionc!(ion_reader_read_ion_decimal(self.reader, &mut value))?;

        Ok(value.try_to_bigdecimal()?)
    }

    // TODO ion-rust/#43 - support timestamp reads

    /// Reads a `string`/`symbol` value from the reader.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("\"🦄\" '✨'")?;
    /// assert_eq!(ION_TYPE_STRING, reader.next()?);
    /// assert_eq!("🦄", reader.read_string()?.as_str());
    /// assert_eq!(ION_TYPE_SYMBOL, reader.next()?);
    /// assert_eq!("✨", reader.read_string()?.as_str());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn read_string(&mut self) -> IonCResult<StrSliceRef> {
        let mut value = ION_STRING::default();
        ionc!(ion_reader_read_string(self.reader, &mut value))?;

        // make a str slice that is tied to our lifetime
        let str_ref = value.as_str(PhantomData::<&'a u8>::default())?;
        Ok(StrSliceRef::new(self, str_ref))
    }

    /// Reads a `clob`/`blob` value from the reader.
    ///
    /// This method implements a vector on the heap to store a copy of the LOB.
    /// If this is not desired, use the low-level length and read methods directly.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("{{\"hello\"}} {{d29ybGQ=}}")?;
    /// assert_eq!(ION_TYPE_CLOB, reader.next()?);
    /// assert_eq!(b"hello", reader.read_bytes()?.as_slice());
    /// assert_eq!(ION_TYPE_BLOB, reader.next()?);
    /// assert_eq!(b"world", reader.read_bytes()?.as_slice());
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn read_bytes(&mut self) -> IonCResult<Vec<u8>> {
        let mut len = 0;
        ionc!(ion_reader_get_lob_size(self.reader, &mut len))?;

        let mut read_len = 0;
        let mut buf = vec![0; len.try_into()?];
        ionc!(ion_reader_read_lob_bytes(
            self.reader,
            buf.as_mut_ptr(),
            buf.len().try_into()?,
            &mut read_len
        ))?;
        if len != read_len {
            Err(IonCError::from(ion_error_code_IERR_INVALID_STATE))
        } else {
            Ok(buf)
        }
    }
}

impl<'a> TryFrom<&'a [u8]> for IonCReaderHandle<'a> {
    type Error = IonCError;

    /// Constructs a reader from a byte slice with the default options.
    #[inline]
    fn try_from(src: &'a [u8]) -> Result<Self, Self::Error> {
        Self::new_buf(src, &mut ION_READER_OPTIONS::default())
    }
}

impl<'a> TryFrom<&'a str> for IonCReaderHandle<'a> {
    type Error = IonCError;
    /// Constructs a reader from a str slice with the default options.
    #[inline]
    fn try_from(src: &'a str) -> Result<Self, Self::Error> {
        Self::try_from(src.as_bytes())
    }
}

impl Deref for IonCReaderHandle<'_> {
    type Target = hREADER;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.reader
    }
}

impl DerefMut for IonCReaderHandle<'_> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.reader
    }
}

impl Drop for IonCReaderHandle<'_> {
    fn drop(&mut self) {
        if !self.reader.is_null() {
            ionc!(ion_reader_close(self.reader)).unwrap()
        }
    }
}
