// Copyright Amazon.com, Inc. or its affiliates.

//! Provides higher-level APIs for Ion C's `hWRITER`.

use std::convert::TryInto;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr;

use crate::int::*;
use crate::result::*;
use crate::*;

/// Indicates at a high-level what type of writer to use.
pub enum WriterMode {
    Text = 0,
    Binary = 1,
}

/// The API for Ion C value writing.
pub trait IonCValueWriter {
    /// Writes a `null` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     writer.write_null(ION_TYPE_INT)?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"\xE0\x01\x00\xEA\x2F", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_null(&mut self, tid: ION_TYPE) -> IonCResult<()>;

    /// Writes a `bool` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Text)?;
    ///     writer.write_bool(true)?;
    ///     writer.write_bool(false)?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"true false", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_bool(&mut self, value: bool) -> IonCResult<()>;

    /// Writes an `int` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     writer.write_i64(-16)?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"\xE0\x01\x00\xEA\x31\x10", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_i64(&mut self, value: i64) -> IonCResult<()>;

    /// Writes an `int` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # use num_bigint::BigInt;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     let value = BigInt::parse_bytes(b"987654321987654321987654321", 10).unwrap();
    ///     writer.write_bigint(&value)?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(
    ///     b"\xE0\x01\x00\xEA\x2C\x03\x30\xF7\xF0\x14\x03\xF9\x4E\xDB\x18\x12\xB1",
    ///     &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_bigint(&mut self, value: &BigInt) -> IonCResult<()>;

    /// Writes a `float` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     writer.write_f64(3.0)?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"\xE0\x01\x00\xEA\x48\x40\x08\x00\x00\x00\x00\x00\x00", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_f64(&mut self, value: f64) -> IonCResult<()>;

    /// Writes a `decimal` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # use bigdecimal::BigDecimal;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     let value = BigDecimal::parse_bytes(b"1.1", 10).unwrap();
    ///     writer.write_bigdecimal(&value)?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(
    ///     b"\xE0\x01\x00\xEA\x52\xC1\x0B",
    ///     &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_bigdecimal(&mut self, value: &BigDecimal) -> IonCResult<()>;

    /// Writes a `timestamp` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # use ion_c_sys::timestamp::*;
    /// # use ion_c_sys::timestamp::Mantissa::*;
    /// # use ion_c_sys::timestamp::TSPrecision::*;
    /// # use ion_c_sys::timestamp::TSOffsetKind::*;
    /// # use chrono::DateTime;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Text)?;
    ///     let dt = DateTime::parse_from_rfc3339("2020-01-02T12:34:00.123Z").unwrap();
    ///
    ///     // write the date time with microsecond precision and an unknown offset
    ///     let ion_dt = IonDateTime::try_new(dt, Fractional(Digits(6)), UnknownOffset)?;
    ///     writer.write_datetime(&ion_dt)?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(
    ///     b"2020-01-02T12:34:00.123000-00:00",
    ///     &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_datetime(&mut self, value: &IonDateTime) -> IonCResult<()>;

    /// Writes a `symbol` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Text)?;
    ///     writer.write_symbol("🍥")?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"'\xF0\x9F\x8D\xA5'", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_symbol(&mut self, value: &str) -> IonCResult<()>;

    /// Writes a `string` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     writer.write_string("🐡")?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"\xE0\x01\x00\xEA\x84\xF0\x9F\x90\xA1", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_string(&mut self, value: &str) -> IonCResult<()>;

    /// Writes a `clob` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     writer.write_clob("🐡".as_bytes())?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"\xE0\x01\x00\xEA\x94\xF0\x9F\x90\xA1", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_clob(&mut self, value: &[u8]) -> IonCResult<()>;

    /// Writes a `blob` value.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Text)?;
    ///     writer.write_blob("🍥".as_bytes())?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"{{8J+NpQ==}}", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn write_blob(&mut self, value: &[u8]) -> IonCResult<()>;

    /// Starts a container.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     writer.start_container(ION_TYPE_LIST)?;
    ///     writer.finish_container()?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"\xE0\x01\x00\xEA\xB0", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn start_container(&mut self, tid: ION_TYPE) -> IonCResult<()>;

    /// Finishes a container.
    fn finish_container(&mut self) -> IonCResult<()>;
}

/// The API for writing values with annotations and/or field names.
pub trait IonCAnnotationsFieldWriter {
    /// The associated type of value writer when writing within annotations/field context
    type AFValueWriter: IonCValueWriter;

    /// Writes a value within a context of annotations and/or a field name
    ///
    /// Note that it is undefined behavior if a value writing method is **not** called
    /// or if a value writing method is called **more than once**.  For this reason,
    /// most users should prefer the `field()` and/or `annotations()` method on the
    /// [`IonCWriter`](./trait.IonCWriter.html) trait as it doesn't have this edge case.
    fn write_annotations_and_field<'a, A, F, FN>(
        &mut self,
        annotations: A,
        field: F,
        applier: FN,
    ) -> IonCResult<()>
    where
        A: Into<Option<&'a [&'a str]>>,
        F: Into<Option<&'a str>>,
        FN: Fn(&mut Self::AFValueWriter) -> IonCResult<()>;
}

/// The writing API for Ion C.
///
/// See also:
/// * [`IonCValueWriter`](./trait.IonCValueWriter.html)
/// * [`IonCWriterHandle`](./struct.IonCWriterHandle.html)
///
/// ## Usage
/// ```
/// # use ion_c_sys::*;
/// # use ion_c_sys::writer::*;
/// # use ion_c_sys::result::*;
/// # use std::convert::*;
/// # use std::ptr;
/// # fn main() -> IonCResult<()> {
/// // a buffer to write to
/// let mut buf = vec![0; 12];
///
/// // borrow the buffer and do some writing!
/// let len = {
///     // write in binary
///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut(), WriterMode::Binary)?;
///
///     // write something
///     writer.write_i64(4)?;
///
///     // finish up the writing
///     writer.finish()?
///
///     // handle implements Drop, so we're good to go!
/// };
///
/// assert_eq!(b"\xE0\x01\x00\xEA\x21\x04", &buf[0..len]);
/// # Ok(())
/// # }
/// ```
pub trait IonCWriter<'a>: IonCValueWriter + IonCAnnotationsFieldWriter {
    /// Returns a lifetime safe writing context for a field.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Binary)?;
    ///     writer.start_container(ION_TYPE_STRUCT)?;
    ///     {
    ///         writer.field("name").write_string("kumo")?;
    ///     }
    ///     writer.finish_container()?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"\xE0\x01\x00\xEA\xD6\x84\x84kumo", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    fn field<'b, 'c>(
        &'b mut self,
        field: &'c str,
    ) -> IonCAnnotationsFieldWriterContext<'b, 'c, Self> {
        IonCAnnotationsFieldWriterContext::new_field(self, field)
    }

    /// Returns a lifetime safe writing context for annotations.
    ///
    /// ## Usage
    /// ```
    /// # use std::convert::*;
    /// # use std::str;
    /// # use ion_c_sys::*;
    /// # use ion_c_sys::writer::*;
    /// # use ion_c_sys::result::*;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = vec![0; 128];
    /// let len = {
    ///     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut_slice(), WriterMode::Text)?;
    ///     writer.annotations(&["a", "b", "c"]).start_container(ION_TYPE_STRUCT)?;
    ///     {
    ///         writer.field("name").annotations(&["def"]).write_string("kumo")?;
    ///         writer.annotations(&["ghi"]).field("type").write_symbol("dog")?;
    ///     }
    ///     writer.finish_container()?;
    ///     writer.finish()?
    /// };
    /// assert_eq!("a::b::c::{name:def::\"kumo\",type:ghi::dog}", str::from_utf8(&buf[0..len])?);
    /// # Ok(())
    /// # }
    /// ```
    fn annotations<'b, 'c>(
        &'b mut self,
        annotations: &'c [&'c str],
    ) -> IonCAnnotationsFieldWriterContext<'b, 'c, Self> {
        IonCAnnotationsFieldWriterContext::new_annotations(self, annotations)
    }

    /// Finalizes writing for the writer and returns the amount of bytes written.
    fn finish(&mut self) -> IonCResult<usize>;
}

/// Wrapper over `hWRITER` to make it easier to use writers in IonC correctly.
///
/// Specifically supports the `Drop` trait to make sure `ion_writer_close` is run.
/// Access to the underlying `hWRITER` pointer is done by de-referencing the handle.
///
/// See also:
/// * [IonCWriter](./trait.IonCWriter.html)
/// * [IonCValueWriter](./trait.IonCValueWriter.html)
pub struct IonCWriterHandle<'a> {
    writer: hWRITER,
    /// Placeholder to tie our lifecycle back to the destination--which might not
    /// actually be a byte slice (if we constructed this from a file or Ion C stream callback)
    referent: PhantomData<&'a mut u8>,
}

impl<'a> IonCWriterHandle<'a> {
    /// Construct a writer to a given mutable slice with options.
    #[inline]
    pub fn new_buf(buf: &'a mut [u8], options: &mut ION_WRITER_OPTIONS) -> Result<Self, IonCError> {
        let mut writer = ptr::null_mut();
        ionc!(ion_writer_open_buffer(
            &mut writer,
            buf.as_mut_ptr(),
            buf.len().try_into()?,
            options
        ))?;

        Ok(IonCWriterHandle {
            writer,
            referent: PhantomData::default(),
        })
    }

    /// Construct a text/binary mode writer with otherwise default options.
    #[inline]
    pub fn new_buf_mode(buf: &'a mut [u8], mode: WriterMode) -> Result<Self, IonCError> {
        let mut options = ION_WRITER_OPTIONS {
            output_as_binary: mode as i32,
            ..Default::default()
        };
        Self::new_buf(buf, &mut options)
    }
}

impl<'a> IonCWriter<'a> for IonCWriterHandle<'a> {
    #[inline]
    fn finish(&mut self) -> IonCResult<usize> {
        let mut len = 0;
        ionc!(ion_writer_finish(self.writer, &mut len))?;

        Ok(len.try_into()?)
    }
}

impl IonCValueWriter for IonCWriterHandle<'_> {
    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[inline]
    fn write_null(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        ionc!(ion_writer_write_typed_null(self.writer, tid))
    }

    #[inline]
    fn write_bool(&mut self, value: bool) -> IonCResult<()> {
        ionc!(ion_writer_write_bool(self.writer, value as BOOL))
    }

    #[inline]
    fn write_i64(&mut self, value: i64) -> IonCResult<()> {
        ionc!(ion_writer_write_int64(self.writer, value))
    }

    #[inline]
    fn write_bigint(&mut self, value: &BigInt) -> IonCResult<()> {
        let mut ion_int = IonIntPtr::try_from_bigint(value)?;
        ionc!(ion_writer_write_ion_int(self.writer, &mut *ion_int))
    }

    #[inline]
    fn write_f64(&mut self, value: f64) -> IonCResult<()> {
        ionc!(ion_writer_write_double(self.writer, value))
    }

    #[inline]
    fn write_bigdecimal(&mut self, value: &BigDecimal) -> IonCResult<()> {
        let mut ion_decimal = IonDecimalPtr::try_from_bigdecimal(value)?;
        ionc!(ion_writer_write_ion_decimal(self.writer, &mut *ion_decimal))
    }

    #[inline]
    fn write_datetime(&mut self, value: &IonDateTime) -> IonCResult<()> {
        let mut ion_timestamp = ION_TIMESTAMP::default();
        ion_timestamp.try_assign_from_iondt(value)?;
        ionc!(ion_writer_write_timestamp(self.writer, &mut ion_timestamp))
    }

    #[inline]
    fn write_symbol(&mut self, value: &str) -> IonCResult<()> {
        // Ion C promises that it won't do mutation for this call!
        let mut ion_str = ION_STRING::try_from_str(value)?;
        ionc!(ion_writer_write_symbol(self.writer, &mut ion_str))
    }

    #[inline]
    fn write_string(&mut self, value: &str) -> IonCResult<()> {
        // Ion C promises that it won't do mutation for this call!
        let mut ion_str = ION_STRING::try_from_str(value)?;
        ionc!(ion_writer_write_string(self.writer, &mut ion_str))
    }

    #[inline]
    fn write_clob(&mut self, value: &[u8]) -> IonCResult<()> {
        // Ion C promises that it won't mutate the buffer for this call!
        ionc!(ion_writer_write_clob(
            self.writer,
            value.as_ptr() as *mut u8,
            value.len().try_into()?
        ))
    }

    #[inline]
    fn write_blob(&mut self, value: &[u8]) -> IonCResult<()> {
        // Ion C promises that it won't mutate the buffer for this call!
        ionc!(ion_writer_write_blob(
            self.writer,
            value.as_ptr() as *mut u8,
            value.len().try_into()?
        ))
    }

    #[allow(clippy::not_unsafe_ptr_arg_deref)]
    #[inline]
    fn start_container(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        ionc!(ion_writer_start_container(self.writer, tid))
    }

    #[inline]
    fn finish_container(&mut self) -> IonCResult<()> {
        ionc!(ion_writer_finish_container(self.writer))
    }
}

impl IonCAnnotationsFieldWriter for IonCWriterHandle<'_> {
    type AFValueWriter = Self;

    #[inline]
    fn write_annotations_and_field<'a, A, F, FN>(
        &mut self,
        possible_annotations: A,
        possible_field: F,
        applier: FN,
    ) -> IonCResult<()>
    where
        A: Into<Option<&'a [&'a str]>>,
        F: Into<Option<&'a str>>,
        FN: Fn(&mut Self::AFValueWriter) -> IonCResult<()>,
    {
        // Ion C promises that it won't do mutation for these!
        if let Some(annotations) = possible_annotations.into() {
            for annotation in annotations {
                let mut annotation_str = ION_STRING::try_from_str(annotation)?;
                ionc!(ion_writer_add_annotation(self.writer, &mut annotation_str))?;
            }
        }
        if let Some(field) = possible_field.into() {
            let mut ion_field = ION_STRING::try_from_str(field)?;
            ionc!(ion_writer_write_field_name(self.writer, &mut ion_field))?;
        }
        applier(self)?;

        Ok(())
    }
}

impl Deref for IonCWriterHandle<'_> {
    type Target = hWRITER;

    fn deref(&self) -> &Self::Target {
        &self.writer
    }
}

impl DerefMut for IonCWriterHandle<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.writer
    }
}

impl Drop for IonCWriterHandle<'_> {
    fn drop(&mut self) {
        if !self.writer.is_null() {
            ionc!(ion_writer_close(self.writer)).unwrap()
        }
    }
}

/// Context for writing annotations and fields in with proper reference lifetimes.
///
/// Specifically, writing annotations and fields with Ion C with
/// `ion_writer_write_annotations`/`ion_writer_add_annotation` and `ion_writer_write_field`
/// is particularly problematic because the lifetime of the `ION_STRING`
/// passed into that function, must be valid until a corresponding
/// `ion_writer_write_*` function is called for writing a value.
///
/// This context tracks the lifetime of the string slices that a user wants to
/// write as annotations and the field name along with a mutable borrow of the writer handle
/// and ensures that calls to `ion_writer_add_annotation`/`ion_writer_write_field`
/// happen before invoking the `ion_writer_write_*` call for the value in a lifetime correct way.
///
/// Note that this context can be thought of as a partial function for writing
/// annotations and/or `struct` fields, so doing nothing with it is simply a no-op, and performing
/// multiple [`IonCValueWriter`](./trait.IonCValueWriter.html) trait method invocations
/// is the same as writing the field before invoking the value writing methods
/// (so duplicate fields would be generated in that case).
pub struct IonCAnnotationsFieldWriterContext<'b, 'c, T: IonCAnnotationsFieldWriter + ?Sized> {
    writer: &'b mut T,
    annotations: Option<&'c [&'c str]>,
    field: Option<&'c str>,
}

impl<'b, 'c, T: IonCAnnotationsFieldWriter + ?Sized> IonCAnnotationsFieldWriterContext<'b, 'c, T> {
    #[inline]
    fn new_field(writer: &'b mut T, field: &'c str) -> Self {
        Self {
            writer,
            annotations: None,
            field: Some(field),
        }
    }

    #[inline]
    fn new_annotations(writer: &'b mut T, annotations: &'c [&'c str]) -> Self {
        Self {
            writer,
            annotations: Some(annotations),
            field: None,
        }
    }

    /// Sets the annotations for the context.
    #[inline]
    pub fn annotations(&mut self, annotations: &'c [&'c str]) -> &mut Self {
        self.annotations = Some(annotations);
        self
    }

    /// Sets the field name for the context.
    #[inline]
    pub fn field(&mut self, field: &'c str) -> &mut Self {
        self.field = Some(field);
        self
    }

    #[inline]
    fn write_annotations_and_field<F>(&mut self, applier: F) -> IonCResult<()>
    where
        F: Fn(&mut T::AFValueWriter) -> IonCResult<()>,
    {
        self.writer
            .write_annotations_and_field(self.annotations, self.field, applier)?;

        Ok(())
    }
}

impl<T: IonCAnnotationsFieldWriter + ?Sized> IonCValueWriter
    for IonCAnnotationsFieldWriterContext<'_, '_, T>
{
    #[inline]
    fn write_null(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_null(tid))
    }

    #[inline]
    fn write_bool(&mut self, value: bool) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_bool(value))
    }

    #[inline]
    fn write_i64(&mut self, value: i64) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_i64(value))
    }

    #[inline]
    fn write_bigint(&mut self, value: &BigInt) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_bigint(value))
    }

    #[inline]
    fn write_f64(&mut self, value: f64) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_f64(value))
    }

    #[inline]
    fn write_bigdecimal(&mut self, value: &BigDecimal) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_bigdecimal(value))
    }

    fn write_datetime(&mut self, value: &IonDateTime) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_datetime(value))
    }

    #[inline]
    fn write_symbol(&mut self, value: &str) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_symbol(value))
    }

    #[inline]
    fn write_string(&mut self, value: &str) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_string(value))
    }

    #[inline]
    fn write_clob(&mut self, value: &[u8]) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_clob(value))
    }

    #[inline]
    fn write_blob(&mut self, value: &[u8]) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.write_blob(value))
    }

    #[inline]
    fn start_container(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        self.write_annotations_and_field(|v| v.start_container(tid))
    }

    /// This API is not relevant for this context and will always return an error.
    #[inline]
    fn finish_container(&mut self) -> IonCResult<()> {
        Err(IonCError::from(ion_error_code_IERR_INVALID_STATE))
    }
}
