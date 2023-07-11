use crate::lazy::binary::system::lazy_struct::LazyStruct;
use crate::lazy::binary::system::lazy_value::LazyValue;
use crate::result::IonFailure;
use crate::{IonError, IonResult};
use std::fmt::{Debug, Formatter};

/// System stream elements that a SystemReader may encounter.
pub enum SystemStreamItem<'top, 'data> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// An Ion symbol table encoded as a struct annotated with `$ion_symbol_table`.
    SymbolTable(LazyStruct<'top, 'data>),
    /// An application-level Ion value
    Value(LazyValue<'top, 'data>),
    /// The end of the stream
    EndOfStream,
}

impl<'top, 'data> Debug for SystemStreamItem<'top, 'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SystemStreamItem::VersionMarker(major, minor) => {
                write!(f, "version marker v{}.{}", major, minor)
            }
            SystemStreamItem::SymbolTable(_) => write!(f, "a symbol table"),
            SystemStreamItem::Value(value) => write!(f, "{}", value.ion_type()),
            SystemStreamItem::EndOfStream => write!(f, "<nothing>"),
        }
    }
}

impl<'top, 'data> SystemStreamItem<'top, 'data> {
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

    /// If this item is a application-level value, returns `Some(&LazyValue)`. Otherwise,
    /// returns `None`.
    pub fn value(&self) -> Option<&LazyValue<'top, 'data>> {
        if let Self::Value(value) = self {
            Some(value)
        } else {
            None
        }
    }

    /// Like [`Self::value`], but returns a [`crate::IonError::Decoding`] if this item is not
    /// an application-level value.
    pub fn expect_value(self) -> IonResult<LazyValue<'top, 'data>> {
        if let Self::Value(value) = self {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("expected value, found {:?}", self))
        }
    }
}
