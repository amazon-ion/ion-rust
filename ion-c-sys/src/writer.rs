use std::convert::TryInto;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr;

use crate::result::*;
use crate::*;

// NB that this cannot be made generic with respect to IonCReaderHandle because
// Rust does not support specialization of Drop.

/// Indicates at a high-level what type of writer to use.
pub enum WriterMode {
    Text = 0,
    Binary = 1,
}

/// Wrapper over `hWRITER` to make it easier to writers in IonC correctly.
///
/// Specifically supports the `Drop` trait to make sure `ion_writer_close` is run.
/// Access to the underlying `hWRITER` pointer is done by de-referencing the handle.
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
    referent: PhantomData<&'a mut [u8]>,
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
            .. Default::default()
        };
        Self::new_buf(buf, &mut options)
    }

    // TODO ion-rust/#51 - Lifetime safety for references borrowed in fieldname/annotation APIs.

    /// Writes a field name.
    ///
    /// Note that the reference given to this call **must** live until a value is written.
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
    ///         writer.set_field_name("name")?;
    ///         writer.write_string("kumo")?;
    ///     }
    ///     writer.finish_container()?;
    ///     writer.finish()?
    /// };
    /// assert_eq!(b"\xE0\x01\x00\xEA\xD6\x84\x84kumo", &buf[0..len]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn set_field_name(&mut self, field: &str) -> IonCResult<()>{
        // Ion C promises that it won't do mutation for this call!
        let mut ion_field = ION_STRING::from_str(field);
        ionc!(ion_writer_write_field_name(self.writer, &mut ion_field))
    }

    // TODO ion-rust/#48 - annotation support

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
    pub fn write_null(&mut self, tid: ION_TYPE) -> IonCResult<()> {
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
    pub fn write_bool(&mut self, value: bool) -> IonCResult<()> {
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
    pub fn write_i64(&mut self, value: i64) -> IonCResult<()> {
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
    pub fn write_f64(&mut self, value: f64) -> IonCResult<()> {
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
    pub fn write_symbol(&mut self, value: &str) -> IonCResult<()> {
        // Ion C promises that it won't do mutation for this call!
        let mut ion_str = ION_STRING::from_str(value);
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
    pub fn write_string(&mut self, value: &str) -> IonCResult<()> {
        // Ion C promises that it won't do mutation for this call!
        let mut ion_str = ION_STRING::from_str(value);
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
    pub fn write_clob(&mut self, value: &[u8]) -> IonCResult<()> {
        // Ion C promises that it won't mutate the buffer for this call!
        ionc!(ion_writer_write_clob(self.writer, value.as_ptr() as *mut u8, value.len().try_into()?))
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
    pub fn write_blob(&mut self, value: &[u8]) -> IonCResult<()> {
        // Ion C promises that it won't mutate the buffer for this call!
        ionc!(ion_writer_write_blob(self.writer, value.as_ptr() as *mut u8, value.len().try_into()?))
    }

    /// Starts  a container.
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
    pub fn start_container(&mut self, tid: ION_TYPE) -> IonCResult<()> {
        ionc!(ion_writer_start_container(self.writer, tid))
    }

    #[inline]
    pub fn finish_container(&mut self) -> IonCResult<()> {
        ionc!(ion_writer_finish_container(self.writer))
    }

    #[inline]
    pub fn finish(&mut self) -> IonCResult<usize> {
        let mut len = 0;
        ionc!(ion_writer_finish(self.writer, &mut len))?;

        Ok(len.try_into()?)
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