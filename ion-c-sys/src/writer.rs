use std::convert::TryInto;
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr;

use crate::result::*;
use crate::*;

// NB that this cannot be made generic with respect to IonCReaderHandle because
// Rust does not support specialization of Drop.

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
/// let mut buf = vec![0u8; 12usize];
/// let mut len = 0;
///
/// // borrow the buffer for writing!
/// {
///     // write in binary
///     let mut options = ION_WRITER_OPTIONS {
///         output_as_binary: 1,
///         .. Default::default()
///     };
///     let writer = IonCWriterHandle::new_buf(buf.as_mut(), &mut options)?;
///
///     // write something
///     ionc!(ion_writer_write_int64(*writer, 4))?;
///
///     // finish up the writing
///     ionc!(ion_writer_finish(*writer, &mut len))?;
///
///     // handle implements Drop, so we're good to go!
/// }
///
/// let written = &buf[0..len.try_into()?];
/// assert_eq!(b"\xE0\x01\x00\xEA\x21\x04", written);
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
