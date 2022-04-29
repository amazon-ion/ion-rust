use crate::raw_symbol_token::RawSymbolToken;
use crate::stream_reader::StreamReader;
use crate::types::IonType;
use std::fmt::{Display, Formatter};

/// `RawReader` is a shorthand for a [Reader] implementation that returns [RawStreamItem]s and
/// uses [RawSymbolToken] to represent its field names, annotations, and symbol values.
pub trait RawReader: StreamReader<Item = RawStreamItem, Symbol = RawSymbolToken> {
    // Defines no additional functionality
}
impl<T> RawReader for T
where
    T: StreamReader<Item = RawStreamItem, Symbol = RawSymbolToken>,
{
    // No additional implementations are necessary
}

#[derive(Debug, Eq, PartialEq, Copy, Clone)]
/// Raw stream components that a RawReader may encounter.
pub enum RawStreamItem {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(u8, u8),
    /// A non-null Ion value and its corresponding Ion data type.
    /// Stream values that represent system constructs (e.g. a struct marked with a
    /// $ion_symbol_table annotation) are still considered values at the raw level.
    Value(IonType),
    /// A null Ion value and its corresponding Ion data type.
    Null(IonType),
    /// Indicates that the reader is not positioned over anything. This can happen:
    /// * before the reader has begun processing the stream.
    /// * after the reader has stepped into a container, but before the reader has called next()
    /// * after the reader has stepped out of a container, but before the reader has called next()
    /// * after the reader has read the last item in a container
    Nothing,
}

impl RawStreamItem {
    /// If `is_null` is `true`, returns `RawStreamItem::Value(ion_type)`. Otherwise,
    /// returns `RawStreamItem::Null(ion_type)`.
    pub fn nullable_value(ion_type: IonType, is_null: bool) -> RawStreamItem {
        if is_null {
            RawStreamItem::Null(ion_type)
        } else {
            RawStreamItem::Value(ion_type)
        }
    }
}

impl Display for RawStreamItem {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use RawStreamItem::*;
        match self {
            VersionMarker(major, minor) => write!(f, "ion version marker (v{}.{})", major, minor),
            Value(ion_type) => write!(f, "null.{}", ion_type),
            Null(ion_type) => write!(f, "{}", ion_type),
            Nothing => write!(f, "nothing/end-of-sequence"),
        }
    }
}
