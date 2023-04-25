use crate::lazy::binary::lazy_raw_reader::LazyRawValue;
use crate::result::{decoding_error, decoding_error_raw};
use crate::IonResult;

#[derive(Debug)]
/// Raw stream components that a RawReader may encounter.
pub enum RawStreamItem<'a> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    // TODO: Doc
    Value(LazyRawValue<'a>),
    /// Indicates that the reader is not positioned over anything. This can happen:
    /// * before the reader has begun processing the stream.
    /// * after the reader has stepped into a container, but before the reader has called next()
    /// * after the reader has stepped out of a container, but before the reader has called next()
    /// * after the reader has read the last item in a container
    Nothing,
}

impl<'a> RawStreamItem<'a> {
    pub fn version_marker(&self) -> Option<(u8, u8)> {
        if let Self::VersionMarker(major, minor) = self {
            Some((*major, *minor))
        } else {
            None
        }
    }

    pub fn expect_ivm(self) -> IonResult<(u8, u8)> {
        self.version_marker()
            .ok_or_else(|| decoding_error_raw(format!("expected IVM, found {:?}", self)))
    }

    pub fn value(&self) -> Option<&LazyRawValue<'a>> {
        if let Self::Value(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn expect_value(self) -> IonResult<LazyRawValue<'a>> {
        if let Self::Value(value) = self {
            Ok(value)
        } else {
            decoding_error(format!("expected value, found {:?}", self))
        }
    }
}
