use crate::lazy::text::buffer::TextBuffer;
use crate::position::Position;
use crate::result::DecodingError;
use crate::{IonError, IonResult};
use smallvec::SmallVec;

/// Attempts to validate a byte sequence as UTF-8 text. If the data is not valid UTF-8, returns
/// an [`IonError`].
///
/// The provided `position` is added to the `IonError` that is constructed if the data is not valid.
pub(crate) trait AsUtf8 {
    fn as_utf8(&self, position: impl Into<Position>) -> IonResult<&str>;
}

impl AsUtf8 for [u8] {
    fn as_utf8(&self, position: impl Into<Position>) -> IonResult<&str> {
        bytes_as_utf8(self, position)
    }
}

impl<const N: usize> AsUtf8 for SmallVec<[u8; N]> {
    fn as_utf8(&self, position: impl Into<Position>) -> IonResult<&str> {
        bytes_as_utf8(self.as_ref(), position)
    }
}

impl<'data> AsUtf8 for TextBuffer<'data> {
    fn as_utf8(&self, position: impl Into<Position>) -> IonResult<&str> {
        bytes_as_utf8(self.bytes(), position)
    }
}

fn bytes_as_utf8(bytes: &[u8], position: impl Into<Position>) -> IonResult<&str> {
    std::str::from_utf8(bytes).map_err(|_| {
        let decoding_error =
            DecodingError::new("encountered invalid UTF-8").with_position(position);
        IonError::Decoding(decoding_error)
    })
}
