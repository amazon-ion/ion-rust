// Copyright Amazon.com, Inc. or its affiliates.

//! Provides higher-level APIs for Ion C's `hREADER`.

use ion_c_sys_macros::position_error;
use std::convert::{TryFrom, TryInto};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::os::raw::c_int;
use std::ptr;

use crate::result::*;
use crate::string::*;
use crate::*;

/// The reading API for Ion C.
///
/// See also [`IonCReaderHandle`](./struct.IonCReaderHandle.html).
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
pub trait IonCReader {
    /// Advances the reader to the next value and returns the type.
    fn next(&mut self) -> IonCResult<ION_TYPE>;

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
    fn get_type(&self) -> IonCResult<ION_TYPE>;

    /// Steps in to the current container.
    fn step_in(&mut self) -> IonCResult<()>;

    /// Steps out of the current container.
    fn step_out(&mut self) -> IonCResult<()>;

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
    fn depth(&self) -> IonCResult<i32>;

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
    fn is_null(&self) -> IonCResult<bool>;

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
    fn is_in_struct(&self) -> IonCResult<bool>;

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
    fn get_field_name(&mut self) -> IonCResult<StrSliceRef>;

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
    fn get_annotations(&mut self) -> IonCResult<StrSlicesRef>;

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
    fn read_bool(&mut self) -> IonCResult<bool>;

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
    fn read_i64(&mut self) -> IonCResult<i64>;

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
    fn read_bigint(&mut self) -> IonCResult<BigInt>;

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
    fn read_f64(&mut self) -> IonCResult<f64>;

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
    fn read_bigdecimal(&mut self) -> IonCResult<BigDecimal>;

    /// Reads a `timestamp` value from the reader.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use chrono::DateTime;
    /// # use ion_c_sys::timestamp::*;
    /// # use ion_c_sys::timestamp::Mantissa::*;
    /// # use ion_c_sys::timestamp::TSPrecision::*;
    /// # use ion_c_sys::timestamp::TSOffsetKind::*;
    /// # use ion_c_sys::reader::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut reader = IonCReaderHandle::try_from("2020-10-10T12:34:45.123-00:00")?;
    /// assert_eq!(ION_TYPE_TIMESTAMP, reader.next()?);
    /// let ion_dt = reader.read_datetime()?;
    ///
    /// // the point in time should be the same
    /// let expected_dt = DateTime::parse_from_rfc3339("2020-10-10T12:34:45.123Z").unwrap();
    /// assert_eq!(&expected_dt, ion_dt.as_datetime());
    ///
    /// // precision should be millisecond level
    /// if let Fractional(Digits(digits)) = ion_dt.precision() {
    ///     assert_eq!(3, *digits);
    /// } else {
    ///     assert!(false, "Expected digits precision!");
    /// }
    ///
    /// // we should have an unknown offset
    /// assert_eq!(UnknownOffset, ion_dt.offset_kind());
    /// # Ok(())
    /// # }
    /// ```
    fn read_datetime(&mut self) -> IonCResult<IonDateTime>;

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
    fn read_string(&mut self) -> IonCResult<StrSliceRef>;

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
    /// let mut reader = IonCReaderHandle::try_from("{{\"hello\"}} {{d29ybGQ=}} {{}}")?;
    /// assert_eq!(ION_TYPE_CLOB, reader.next()?);
    /// assert_eq!(b"hello", reader.read_bytes()?.as_slice());
    /// assert_eq!(ION_TYPE_BLOB, reader.next()?);
    /// assert_eq!(b"world", reader.read_bytes()?.as_slice());
    /// assert_eq!(ION_TYPE_BLOB, reader.next()?);
    /// assert_eq!(b"", reader.read_bytes()?.as_slice());
    /// # Ok(())
    /// # }
    /// ```
    fn read_bytes(&mut self) -> IonCResult<Vec<u8>>;

    /// Returns the current position. TODO: blah blah.
    fn pos(&self) -> IonCResult<Position>;
}

/// Wrapper over `hREADER` to make it easier to use readers in IonC correctly.
///
/// Specifically supports the `Drop` trait to make sure `ion_reader_close` is run.
/// Access to the underlying `hREADER` pointer is done by de-referencing the handle.
pub struct IonCReaderHandle<'a> {
    reader: hREADER,
    /// Placeholder to tie our lifecycle back to the source of the data--which might not
    /// actually be a byte slice (if we constructed this from a file or Ion C stream callback)
    referent: PhantomData<&'a [u8]>,
}

impl<'a> IonCReaderHandle<'a> {
    /// Constructs a reader handle from a byte slice and given options.
    pub fn try_from_buf(
        src: &'a [u8],
        options: &mut ION_READER_OPTIONS,
    ) -> Result<Self, IonCError> {
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
}
impl<'a> IonCReader for IonCReaderHandle<'a> {
    #[position_error]
    #[inline]
    fn next(&mut self) -> IonCResult<ION_TYPE> {
        let mut tid = ptr::null_mut();
        ionc!(ion_reader_next(self.reader, &mut tid))?;

        Ok(tid)
    }

    #[position_error]
    #[inline]
    fn get_type(&self) -> IonCResult<ION_TYPE> {
        let mut tid = ptr::null_mut();
        ionc!(ion_reader_get_type(self.reader, &mut tid))?;

        Ok(tid)
    }

    #[position_error]
    #[inline]
    fn step_in(&mut self) -> IonCResult<()> {
        ionc!(ion_reader_step_in(self.reader))
    }

    #[position_error]
    #[inline]
    fn step_out(&mut self) -> IonCResult<()> {
        ionc!(ion_reader_step_out(self.reader))
    }

    #[position_error]
    #[inline]
    fn depth(&self) -> IonCResult<i32> {
        let mut depth = 0;
        ionc!(ion_reader_get_depth(self.reader, &mut depth))?;

        Ok(depth)
    }

    #[position_error]
    #[inline]
    fn is_null(&self) -> IonCResult<bool> {
        let mut is_null = 0;
        ionc!(ion_reader_is_null(self.reader, &mut is_null))?;

        Ok(is_null != 0)
    }

    #[position_error]
    #[inline]
    fn is_in_struct(&self) -> IonCResult<bool> {
        let mut is_in_struct = 0;
        ionc!(ion_reader_is_in_struct(self.reader, &mut is_in_struct))?;

        Ok(is_in_struct != 0)
    }

    #[position_error]
    #[inline]
    fn get_field_name(&mut self) -> IonCResult<StrSliceRef> {
        let mut field = ION_STRING::default();
        ionc!(ion_reader_get_field_name(self.reader, &mut field))?;

        // make a str slice that is tied to our lifetime
        let field_str = field.as_str(PhantomData::<&'a u8>::default())?;
        Ok(StrSliceRef::new(self, field_str))
    }

    fn get_annotations(&mut self) -> IonCResult<StrSlicesRef> {
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

    #[position_error]
    #[inline]
    fn read_bool(&mut self) -> IonCResult<bool> {
        let mut value = 0;
        ionc!(ion_reader_read_bool(self.reader, &mut value))?;

        Ok(value != 0)
    }

    #[position_error]
    #[inline]
    fn read_i64(&mut self) -> IonCResult<i64> {
        let mut value = 0;
        ionc!(ion_reader_read_int64(self.reader, &mut value))?;

        Ok(value)
    }

    #[position_error]
    #[inline]
    fn read_bigint(&mut self) -> IonCResult<BigInt> {
        let mut value = ION_INT::default();
        ionc!(ion_reader_read_ion_int(self.reader, &mut value))?;

        value.try_to_bigint()
    }

    #[position_error]
    #[inline]
    fn read_f64(&mut self) -> IonCResult<f64> {
        let mut value = 0.0;
        ionc!(ion_reader_read_double(self.reader, &mut value))?;

        Ok(value)
    }

    #[position_error]
    #[inline]
    fn read_bigdecimal(&mut self) -> IonCResult<BigDecimal> {
        let mut value = ION_DECIMAL::default();
        ionc!(ion_reader_read_ion_decimal(self.reader, &mut value))?;

        value.try_to_bigdecimal()
    }

    #[position_error]
    #[inline]
    fn read_datetime(&mut self) -> IonCResult<IonDateTime> {
        let mut value = ION_TIMESTAMP::default();
        ionc!(ion_reader_read_timestamp(self.reader, &mut value))?;

        value.try_to_iondt()
    }

    #[position_error]
    #[inline]
    fn read_string(&mut self) -> IonCResult<StrSliceRef> {
        let mut value = ION_STRING::default();
        ionc!(ion_reader_read_string(self.reader, &mut value))?;

        // make a str slice that is tied to our lifetime
        let str_ref = value.as_str(PhantomData::<&'a u8>::default())?;
        Ok(StrSliceRef::new(self, str_ref))
    }

    #[position_error]
    #[inline]
    fn read_bytes(&mut self) -> IonCResult<Vec<u8>> {
        let mut len = 0;
        ionc!(ion_reader_get_lob_size(self.reader, &mut len))?;
        if len == 0 {
            // XXX short-circuit the empty case
            // until amzn/ion-c#233 is fixed this will panic, but there
            // is no reason to call into Ion C in this case anyhow
            return Ok(Vec::new());
        }

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

    // *NOT* annotated with `#[position_error]` - if reading the current
    // position is an error, then we don't want to include the position in the
    // error!
    //
    // This method is actually implemented in `reader_current_pos`. Otherwise,
    // various reader trait methods require additional borrows.
    #[inline]
    fn pos(&self) -> IonCResult<Position> {
        reader_current_pos(&self.reader)
    }
}

/// Asks `reader` for its current position and includes it in `err`.
///
/// If the position is already known, then this method does nothing. If reading
/// the position returns an error, then this method also does nothing!
///
/// This method is defined on the reader handle directly because of partial
/// borrow requirements in the implementation of the `Reader` trait.
pub fn include_current_position(reader: &hREADER, err: IonCError) -> IonCError {
    if !std::matches!(err.position, Position::Unknown) {
        return err;
    }

    let pos = match reader_current_pos(reader) {
        Ok(pos) => pos,
        Err(_) => return err, // the original, not the one from failing to read the pos
    };

    err.with_position(pos)
}

#[inline]
fn reader_current_pos(reader: &hREADER) -> IonCResult<Position> {
    let mut bytes: i64 = -1;
    let mut line = -1;
    let mut offset = -1;
    ionc!(ion_reader_get_position(
        *reader,
        &mut bytes,
        &mut line,
        &mut offset
    ))?;

    Ok(match (bytes, line, offset) {
        (b, -1, -1) if b > 0 => Position::Offset(b),
        (b, l, o) if b > 0 && l > 0 && o > 0 => Position::OffsetLineColumn(b, LineColumn(l, o)),
        // Should never happen!
        _ => Position::Unknown,
    })
}

impl<'a> TryFrom<&'a [u8]> for IonCReaderHandle<'a> {
    type Error = IonCError;

    /// Constructs a reader from a byte slice with the default options.
    #[inline]
    fn try_from(src: &'a [u8]) -> Result<Self, Self::Error> {
        Self::try_from_buf(src, &mut ION_READER_OPTIONS::default())
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

#[cfg(test)]
mod reader_tests {
    use super::*;

    #[test]
    fn position_error() -> IonCResult<()> {
        let data = r#"{foo:"bar",baz:"#;
        let mut reader = IonCReaderHandle::try_from(data)?;
        reader.next()?;

        // `baz` has a field but not value - boom!
        let err = match reader.next() {
            Err(e) => e,
            Ok(t) => panic!("expected an error, found a {:?}", t),
        };

        assert_eq!(err.position, Position::text(15, 1, 16));

        Ok(())
    }
}
