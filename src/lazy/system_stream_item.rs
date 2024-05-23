use std::fmt::{Debug, Formatter};

use crate::lazy::decoder::{Decoder, RawVersionMarker};
use crate::lazy::expanded::ExpandedValueSource;
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem, RawStreamItem};
use crate::lazy::value::LazyValue;
use crate::result::IonFailure;
use crate::{IonError, IonResult};

/// System stream elements that a SystemReader may encounter.
#[non_exhaustive]
pub enum SystemStreamItem<'top, D: Decoder> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(D::VersionMarker<'top>),
    /// An Ion symbol table encoded as a struct annotated with `$ion_symbol_table`.
    SymbolTable(LazyStruct<'top, D>),
    /// An application-level Ion value
    Value(LazyValue<'top, D>),
    /// The end of the stream
    EndOfStream(EndPosition),
}

impl<'top, D: Decoder> Debug for SystemStreamItem<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SystemStreamItem::VersionMarker(marker) => {
                write!(f, "version marker v{}.{}", marker.major(), marker.minor())
            }
            SystemStreamItem::SymbolTable(_) => write!(f, "a symbol table"),
            SystemStreamItem::Value(value) => write!(f, "{}", value.ion_type()),
            SystemStreamItem::EndOfStream(_) => write!(f, "<nothing>"),
        }
    }
}

impl<'top, D: Decoder> SystemStreamItem<'top, D> {
    /// If this item is an Ion version marker (IVM), returns `Some(version_marker)` indicating the
    /// version. Otherwise, returns `None`.
    pub fn version_marker(&self) -> Option<D::VersionMarker<'top>> {
        if let Self::VersionMarker(marker) = self {
            Some(*marker)
        } else {
            None
        }
    }

    /// Like [`Self::version_marker`], but returns a [`crate::IonError::Decoding`] if this item
    /// is not an IVM.
    pub fn expect_ivm(self) -> IonResult<D::VersionMarker<'top>> {
        self.version_marker()
            .ok_or_else(|| IonError::decoding_error(format!("expected IVM, found {:?}", self)))
    }

    /// If this item is a application-level value, returns `Some(&LazyValue)`. Otherwise,
    /// returns `None`.
    pub fn value(&self) -> Option<&LazyValue<'top, D>> {
        if let Self::Value(value) = self {
            Some(value)
        } else {
            None
        }
    }

    /// Like [`Self::value`], but returns a [`IonError::Decoding`] if this item is not
    /// an application-level value.
    pub fn expect_value(self) -> IonResult<LazyValue<'top, D>> {
        if let Self::Value(value) = self {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("expected value, found {:?}", self))
        }
    }

    pub fn raw_stream_item(&self) -> Option<LazyRawStreamItem<'top, D>> {
        let item = match self {
            SystemStreamItem::VersionMarker(marker) => RawStreamItem::VersionMarker(*marker),
            SystemStreamItem::SymbolTable(symtab) => {
                use ExpandedValueSource::*;
                match symtab.as_value().lower().source {
                    ValueLiteral(literal) => RawStreamItem::Value(literal),
                    Template(..) | Constructed(..) => return None,
                }
            }
            SystemStreamItem::Value(value) => {
                use ExpandedValueSource::*;
                match value.lower().source {
                    ValueLiteral(literal) => RawStreamItem::Value(literal),
                    Template(..) | Constructed(..) => return None,
                }
            }
            SystemStreamItem::EndOfStream(end) => RawStreamItem::EndOfStream(*end),
        };
        Some(item)
    }
}
