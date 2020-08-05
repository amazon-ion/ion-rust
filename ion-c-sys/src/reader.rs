use std::convert::{TryFrom, TryInto};
use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};
use std::ptr;

use crate::result::*;
use crate::*;

// NB that this cannot be made generic with respect to IonCWriterHandle because
// Rust does not support specialization of Drop.

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
/// # fn main() -> IonCResult {
/// let mut buf = String::from("hello");
/// let reader_handle = IonCReaderHandle::try_from(buf.as_mut_str())?;
///
/// let mut ion_type = ptr::null_mut();
/// ionc!(ion_reader_next(*reader_handle, &mut ion_type))?;
/// assert_eq!(ION_TYPE_SYMBOL, ion_type);
///
/// // reader_handle implements Drop, so we're good to go!
/// # Ok(())
/// # }
/// ```
pub struct IonCReaderHandle<'a> {
    reader: hREADER,
    /// Placeholder to tie our lifecycle back to the source of the data--which might not
    /// actually be a byte slice (if we constructed this from a file or Ion C stream callback)
    referent: PhantomData<&'a mut [u8]>,
}

impl<'a> IonCReaderHandle<'a> {
    /// Constructs a reader handle from a mutable slice and given options.
    pub fn new_buf(src: &'a mut [u8], options: &mut ION_READER_OPTIONS) -> Result<Self, IonCError> {
        let mut reader = ptr::null_mut();
        ionc!(ion_reader_open_buffer(
            &mut reader,
            src.as_mut_ptr(),
            src.len().try_into()?,
            options,
        ))?;
        Ok(IonCReaderHandle {
            reader,
            referent: PhantomData::default(),
        })
    }
}

impl<'a> TryFrom<&'a mut [u8]> for IonCReaderHandle<'a> {
    type Error = IonCError;

    /// Constructs a reader from a mutable slice with the default options.
    #[inline]
    fn try_from(src: &'a mut [u8]) -> Result<Self, Self::Error> {
        Self::new_buf(src, &mut ION_READER_OPTIONS::default())
    }
}

impl<'a> TryFrom<&'a mut str> for IonCReaderHandle<'a> {
    type Error = IonCError;
    /// Constructs a reader from a mutable str with the default options.
    #[inline]
    fn try_from(src: &'a mut str) -> Result<Self, Self::Error> {
        unsafe { Self::try_from(src.as_bytes_mut()) }
    }
}

impl Deref for IonCReaderHandle<'_> {
    type Target = hREADER;

    fn deref(&self) -> &Self::Target {
        &self.reader
    }
}

impl DerefMut for IonCReaderHandle<'_> {
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
