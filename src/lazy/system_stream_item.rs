use std::fmt::{Debug, Formatter};

use crate::lazy::decoder::{Decoder, RawVersionMarker};
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem, RawStreamItem};
use crate::lazy::value::LazyValue;
use crate::result::IonFailure;
use crate::{ExpandedStreamItem, IonError, IonResult, LazySExp};

/// System stream elements that a SystemReader may encounter.
#[non_exhaustive]
pub enum SystemStreamItem<'top, D: Decoder> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(D::VersionMarker<'top>),
    /// An Ion 1.0-style symbol table encoded as a struct annotated with `$ion_symbol_table`.
    SymbolTable(LazyStruct<'top, D>),
    /// An Ion 1.1 encoding directive; an s-expression annotated with `$ion_encoding`.
    EncodingDirective(LazySExp<'top, D>),
    /// An application-level Ion value
    Value(LazyValue<'top, D>),
    /// The end of the stream
    EndOfStream(EndPosition),
}

impl<'top, D: Decoder> SystemStreamItem<'top, D> {
    /// Returns an [`ExpandedStreamItem`] view of this item.
    pub fn as_expanded_stream_item(&self) -> ExpandedStreamItem<'top, D> {
        use SystemStreamItem::*;
        match self {
            VersionMarker(m) => ExpandedStreamItem::VersionMarker(*m),
            SymbolTable(s) => ExpandedStreamItem::SymbolTable(*s),
            EncodingDirective(d) => ExpandedStreamItem::EncodingDirective(*d),
            Value(v) => ExpandedStreamItem::Value(*v),
            EndOfStream(e) => ExpandedStreamItem::EndOfStream(*e),
        }
    }
}

impl<'top, D: Decoder> Debug for SystemStreamItem<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SystemStreamItem::VersionMarker(marker) => {
                write!(f, "version marker v{}.{}", marker.major(), marker.minor())
            }
            SystemStreamItem::SymbolTable(_) => write!(f, "a symbol table"),
            SystemStreamItem::EncodingDirective(_) => write!(f, "an encoding directive"),
            SystemStreamItem::Value(value) => write!(f, "{}", value.ion_type()),
            SystemStreamItem::EndOfStream(_) => write!(f, "<nothing>"),
        }
    }
}

// Clippy complains that `as_` methods should return a reference. In this case, all of the types
// are `Copy`, so returning a copy isn't a problem.
#[allow(clippy::wrong_self_convention)]
impl<'top, D: Decoder> SystemStreamItem<'top, D> {
    /// If this item is an Ion version marker (IVM), returns `Some(version_marker)` indicating the
    /// version. Otherwise, returns `None`.
    pub fn as_version_marker(&self) -> Option<D::VersionMarker<'top>> {
        if let Self::VersionMarker(marker) = self {
            Some(*marker)
        } else {
            None
        }
    }

    /// Like [`Self::as_version_marker`], but returns a [`crate::IonError::Decoding`] if this item
    /// is not an IVM.
    pub fn expect_ivm(self) -> IonResult<D::VersionMarker<'top>> {
        self.as_version_marker()
            .ok_or_else(|| IonError::decoding_error(format!("expected IVM, found {:?}", self)))
    }

    /// If this item is a application-level value, returns `Some(&LazyValue)`. Otherwise,
    /// returns `None`.
    pub fn as_value(&self) -> Option<LazyValue<'top, D>> {
        if let Self::Value(value) = self {
            Some(*value)
        } else {
            None
        }
    }

    /// Like [`Self::as_value`], but returns a [`IonError::Decoding`] if this item is not
    /// an application-level value.
    pub fn expect_value(self) -> IonResult<LazyValue<'top, D>> {
        if let Self::Value(value) = self {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("expected value, found {:?}", self))
        }
    }

    /// If this item is a symbol table, returns `Some(lazy_struct)`. Otherwise, returns `None`.
    pub fn as_symbol_table(self) -> Option<LazyStruct<'top, D>> {
        if let Self::SymbolTable(struct_) = self {
            Some(struct_)
        } else {
            None
        }
    }

    /// Like [`Self::as_symbol_table`], but returns a [`IonError::Decoding`] if this item is not
    /// a symbol table.
    pub fn expect_symbol_table(self) -> IonResult<LazyStruct<'top, D>> {
        if let Self::SymbolTable(value) = self {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("expected symbol table, found {:?}", self))
        }
    }

    /// If this item is a symbol table, returns `Some(lazy_struct)`. Otherwise, returns `None`.
    pub fn as_encoding_directive(self) -> Option<LazySExp<'top, D>> {
        if let Self::EncodingDirective(sexp) = self {
            Some(sexp)
        } else {
            None
        }
    }

    /// Like [`Self::as_symbol_table`], but returns a [`IonError::Decoding`] if this item is not
    /// a symbol table.
    pub fn expect_encoding_directive(self) -> IonResult<LazySExp<'top, D>> {
        if let Self::EncodingDirective(sexp) = self {
            Ok(sexp)
        } else {
            IonResult::decoding_error(format!("expected encoding directive, found {:?}", self))
        }
    }

    pub fn raw_stream_item(&self) -> Option<LazyRawStreamItem<'top, D>> {
        let value = match self {
            SystemStreamItem::VersionMarker(marker) => {
                return Some(RawStreamItem::VersionMarker(*marker))
            }
            SystemStreamItem::SymbolTable(symtab) => symtab.as_value(),
            SystemStreamItem::EncodingDirective(directive) => directive.as_value(),
            SystemStreamItem::Value(value) => *value,
            SystemStreamItem::EndOfStream(end) => return Some(RawStreamItem::EndOfStream(*end)),
        };
        value.raw().map(RawStreamItem::Value)
    }
}
