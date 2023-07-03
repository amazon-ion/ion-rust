use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::result::IonFailure;
use crate::{IonError, IonResult};

#[derive(Debug)]
/// Raw stream components that a RawReader may encounter.
pub enum RawStreamItem<'data> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// An Ion value whose data has not yet been read. For more information about how to read its
    /// data and (in the case of containers) access any nested values, see the documentation
    /// for [`LazyRawValue`].
    Value(LazyRawValue<'data>),
    /// The end of the stream
    EndOfStream,
}

impl<'a> RawStreamItem<'a> {
    /// If this item is an Ion version marker (IVM), returns `Some((major, minor))` indicating the
    /// version. Otherwise, returns `None`.
    pub fn version_marker(&self) -> Option<(u8, u8)> {
        if let Self::VersionMarker(major, minor) = self {
            Some((*major, *minor))
        } else {
            None
        }
    }

    /// Like [`Self::version_marker`], but returns a [`crate::IonError::Decoding`] if this item
    /// is not an IVM.
    pub fn expect_ivm(self) -> IonResult<(u8, u8)> {
        self.version_marker()
            .ok_or_else(|| IonError::decoding_error(format!("expected IVM, found {:?}", self)))
    }

    /// If this item is a value, returns `Some(&LazyValue)`. Otherwise, returns `None`.
    pub fn value(&self) -> Option<&LazyRawValue<'a>> {
        if let Self::Value(value) = self {
            Some(value)
        } else {
            None
        }
    }

    /// Like [`Self::value`], but returns a [`crate::IonError::Decoding`] if this item is not
    /// a value.
    pub fn expect_value(self) -> IonResult<LazyRawValue<'a>> {
        if let Self::Value(value) = self {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("expected value, found {:?}", self))
        }
    }
}
