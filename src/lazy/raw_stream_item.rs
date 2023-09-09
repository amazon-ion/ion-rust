use crate::lazy::decoder::LazyDecoder;
use crate::lazy::encoding::EncodingWithMacroSupport;
use crate::result::IonFailure;
use crate::{IonError, IonResult};

#[derive(Debug)]
/// Raw stream components that a RawReader may encounter.
pub enum RawStreamItem<'data, D: LazyDecoder<'data>> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// An Ion value whose data has not yet been read. For more information about how to read its
    /// data and (in the case of containers) access any nested values, see the documentation
    /// for [`LazyRawBinaryValue`](crate::lazy::binary::raw::value::LazyRawBinaryValue).
    Value(D::Value),
    /// An Ion 1.1+ macro invocation. Ion 1.0 readers will never return a macro invocation.
    EExpression(D::MacroInvocation),
    /// The end of the stream
    EndOfStream,
}

impl<'data, D: LazyDecoder<'data>> RawStreamItem<'data, D> {
    /// If this item is an Ion version marker (IVM), returns `Some((major, minor))` indicating the
    /// version. Otherwise, returns `None`.
    pub fn version_marker(&self) -> Option<(u8, u8)> {
        if let Self::VersionMarker(major, minor) = self {
            Some((*major, *minor))
        } else {
            None
        }
    }

    /// Like [`Self::version_marker`], but returns a [`IonError::Decoding`] if this item
    /// is not an IVM.
    pub fn expect_ivm(self) -> IonResult<(u8, u8)> {
        self.version_marker()
            .ok_or_else(|| IonError::decoding_error(format!("expected IVM, found {:?}", self)))
    }

    /// If this item is a value, returns `Some(&LazyValue)`. Otherwise, returns `None`.
    pub fn value(&self) -> Option<&D::Value> {
        if let Self::Value(value) = self {
            Some(value)
        } else {
            None
        }
    }

    /// Like [`Self::value`], but returns a [`IonError::Decoding`] if this item is not
    /// a value.
    pub fn expect_value(self) -> IonResult<D::Value> {
        if let Self::Value(value) = self {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("expected value, found {:?}", self))
        }
    }
}

impl<'data, D: LazyDecoder<'data> + EncodingWithMacroSupport> RawStreamItem<'data, D> {
    pub fn as_macro_invocation(&self) -> Option<&D::MacroInvocation> {
        if let Self::EExpression(m) = self {
            Some(m)
        } else {
            None
        }
    }

    pub fn expect_macro_invocation(self) -> IonResult<D::MacroInvocation> {
        if let Self::EExpression(m) = self {
            Ok(m)
        } else {
            IonResult::decoding_error(format!("expected a macro invocation, found {:?}", self))
        }
    }
}
