// Copyright Amazon.com, Inc. or its affiliates.

use std::convert::TryInto;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr;

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
    fn write_null(&mut self, tid: ION_TYPE) -> IonCResult<()>;

    /// Writes a `bool` value.
    fn write_bool(&mut self, value: bool) -> IonCResult<()>;

    /// Writes an `int` value.
    fn write_i64(&mut self, value: i64) -> IonCResult<()>;

    // TODO ion-rust/#50 - support ION_INT (arbitrary large integer) writes

    /// Writes a `float` value.
    fn write_f64(&mut self, value: f64) -> IonCResult<()>;

    // TODO ion-rust/#42 - support decimal writes
    // TODO ion-rust/#43 - support timestamp writes

    /// Writes a `symbol` value.
    fn write_symbol(&mut self, value: &str) -> IonCResult<()>;

    /// Writes a `string` value.
    fn write_string(&mut self, value: &str) -> IonCResult<()>;

    /// Writes a `clob` value.
    fn write_clob(&mut self, value: &[u8]) -> IonCResult<()>;

    /// Writes a `blob` value.
    fn write_blob(&mut self, value: &[u8]) -> IonCResult<()>;

    /// Starts  a container.
    fn start_container(&mut self, tid: ION_TYPE) -> IonCResult<()>;

    /// Finishes a container.
    fn finish_container(&mut self) -> IonCResult<()>;
}

/// Wrapper over `hWRITER` to make it easier to writers in IonC correctly.
///
/// Specifically supports the `Drop` trait to make sure `ion_writer_close` is run.
/// Access to the underlying `hWRITER` pointer is done by de-referencing the handle.
///
/// See also [IonCValueWriter](./trait.IonCValueWriter.html) for details
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
pub struct IonCWriterHandle<'a> {
    writer: hWRITER,
    /// Placeholder to tie our lifecycle back to the source of the data--which might not
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
    pub fn field<'b, 'c>(
        &'b mut self,
        field: &'c str,
    ) -> IonCAnnotationsFieldWriterContext<'a, 'b, 'c> {
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
    pub fn annotations<'b, 'c>(
        &'b mut self,
        annotations: &'c [&'c str],
    ) -> IonCAnnotationsFieldWriterContext<'a, 'b, 'c> {
        IonCAnnotationsFieldWriterContext::new_annotations(self, annotations)
    }

    #[inline]
    pub fn finish(&mut self) -> IonCResult<usize> {
        let mut len = 0;
        ionc!(ion_writer_finish(self.writer, &mut len))?;

        Ok(len.try_into()?)
    }
}

impl IonCValueWriter for IonCWriterHandle<'_> {
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
    #[inline]
    fn write_null(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        ionc!(ion_writer_write_typed_null(self.writer, tid))
    }

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
    #[inline]
    fn write_bool(&mut self, value: bool) -> IonCResult<()> {
        ionc!(ion_writer_write_bool(self.writer, value as BOOL))
    }

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
    #[inline]
    fn write_i64(&mut self, value: i64) -> IonCResult<()> {
        ionc!(ion_writer_write_int64(self.writer, value))
    }

    // TODO ion-rust/#50 - support ION_INT (arbitrary large integer) writes

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
    #[inline]
    fn write_f64(&mut self, value: f64) -> IonCResult<()> {
        ionc!(ion_writer_write_double(self.writer, value))
    }

    // TODO ion-rust/#42 - support decimal writes
    // TODO ion-rust/#43 - support timestamp writes

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
    #[inline]
    fn write_symbol(&mut self, value: &str) -> IonCResult<()> {
        // Ion C promises that it won't do mutation for this call!
        let mut ion_str = ION_STRING::try_from_str(value)?;
        ionc!(ion_writer_write_symbol(self.writer, &mut ion_str))
    }

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
    #[inline]
    fn write_string(&mut self, value: &str) -> IonCResult<()> {
        // Ion C promises that it won't do mutation for this call!
        let mut ion_str = ION_STRING::try_from_str(value)?;
        ionc!(ion_writer_write_string(self.writer, &mut ion_str))
    }

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
    #[inline]
    fn write_clob(&mut self, value: &[u8]) -> IonCResult<()> {
        // Ion C promises that it won't mutate the buffer for this call!
        ionc!(ion_writer_write_clob(
            self.writer,
            value.as_ptr() as *mut u8,
            value.len().try_into()?
        ))
    }

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
    #[inline]
    fn write_blob(&mut self, value: &[u8]) -> IonCResult<()> {
        // Ion C promises that it won't mutate the buffer for this call!
        ionc!(ion_writer_write_blob(
            self.writer,
            value.as_ptr() as *mut u8,
            value.len().try_into()?
        ))
    }

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
    #[inline]
    fn start_container(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        ionc!(ion_writer_start_container(self.writer, tid))
    }

    /// Finishes a container.
    #[inline]
    fn finish_container(&mut self) -> IonCResult<()> {
        ionc!(ion_writer_finish_container(self.writer))
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
pub struct IonCAnnotationsFieldWriterContext<'a, 'b, 'c> {
    handle: &'b mut IonCWriterHandle<'a>,
    annotations: Option<&'c [&'c str]>,
    field: Option<&'c str>,
}

impl<'a, 'b, 'c> IonCAnnotationsFieldWriterContext<'a, 'b, 'c> {
    fn new_field(handle: &'b mut IonCWriterHandle<'a>, field: &'c str) -> Self {
        Self {
            handle,
            annotations: None,
            field: Some(field),
        }
    }

    fn new_annotations(handle: &'b mut IonCWriterHandle<'a>, annotations: &'c [&'c str]) -> Self {
        Self {
            handle,
            annotations: Some(annotations),
            field: None,
        }
    }

    /// Sets the annotations for the context.
    pub fn annotations(&mut self, annotations: &'c [&'c str]) -> &mut Self {
        self.annotations = Some(annotations);
        self
    }

    /// Sets the field name for the context.
    pub fn field(&mut self, field: &'c str) -> &mut Self {
        self.field = Some(field);
        self
    }
}

macro_rules! write_annotations_field {
    ($i:ident) => {
        // Ion C promises that it won't do mutation for these!
        if let Some(annotations) = $i.annotations {
            for annotation in annotations {
                let mut annotation_str = ION_STRING::try_from_str(annotation)?;
                ionc!(ion_writer_add_annotation(
                    $i.handle.writer,
                    &mut annotation_str
                ))?;
            }
        }
        if let Some(field) = $i.field {
            let mut field_str = ION_STRING::try_from_str(field)?;
            ionc!(ion_writer_write_field_name(
                $i.handle.writer,
                &mut field_str
            ))?;
        }
    };
}

impl IonCValueWriter for IonCAnnotationsFieldWriterContext<'_, '_, '_> {
    #[inline]
    fn write_null(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.write_null(tid)
    }

    #[inline]
    fn write_bool(&mut self, value: bool) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.write_bool(value)
    }

    #[inline]
    fn write_i64(&mut self, value: i64) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.write_i64(value)
    }

    #[inline]
    fn write_f64(&mut self, value: f64) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.write_f64(value)
    }

    #[inline]
    fn write_symbol(&mut self, value: &str) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.write_symbol(value)
    }

    #[inline]
    fn write_string(&mut self, value: &str) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.write_string(value)
    }

    #[inline]
    fn write_clob(&mut self, value: &[u8]) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.write_clob(value)
    }

    #[inline]
    fn write_blob(&mut self, value: &[u8]) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.write_blob(value)
    }

    #[inline]
    fn start_container(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        write_annotations_field!(self);
        self.handle.start_container(tid)
    }

    /// This API is not relevant for this context and will always return an error.
    #[inline]
    fn finish_container(&mut self) -> IonCResult<()> {
        Err(IonCError::from(ion_error_code_IERR_INVALID_STATE))
    }
}
