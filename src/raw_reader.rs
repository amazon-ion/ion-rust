use crate::element::{Blob, Clob};
use crate::ion_reader::IonReader;
use crate::raw_symbol_token::RawSymbolToken;
use crate::types::{IonType, Str};
use crate::{Decimal, Int, IonResult, Timestamp};
use std::fmt::{Display, Formatter};
use std::io::Read;

/// `RawReader` is a shorthand for a [Reader](crate::Reader) implementation that returns [RawStreamItem]s and
/// uses [RawSymbolToken] to represent its field names, annotations, and symbol values.
pub trait RawReader: IonReader<Item = RawStreamItem, Symbol = RawSymbolToken> {}

impl<T> RawReader for T where T: IonReader<Item = RawStreamItem, Symbol = RawSymbolToken> {}

/// Allows a `Box<dyn RawReader>` to be used as a RawReader.
/// Note: this implementation contains some methods that are not object safe and so cannot be
///       invoked. For the moment, calling these methods via dynamic dispatch will result in a
///       panic. Longer-term, they will be replaced by object safe methods.
///       See: <https://github.com/amazon-ion/ion-rust/issues/335>
impl<R: RawReader + ?Sized> IonReader for Box<R> {
    type Item = RawStreamItem;
    type Symbol = RawSymbolToken;

    #[inline]
    fn ion_version(&self) -> (u8, u8) {
        (**self).ion_version()
    }

    fn next(&mut self) -> IonResult<Self::Item> {
        (**self).next()
    }

    fn current(&self) -> Self::Item {
        (**self).current()
    }

    fn ion_type(&self) -> Option<IonType> {
        (**self).ion_type()
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = IonResult<Self::Symbol>> + 'a> {
        (**self).annotations()
    }

    fn field_name(&self) -> IonResult<Self::Symbol> {
        (**self).field_name()
    }

    fn is_null(&self) -> bool {
        (**self).is_null()
    }

    fn read_null(&mut self) -> IonResult<IonType> {
        (**self).read_null()
    }

    fn read_bool(&mut self) -> IonResult<bool> {
        (**self).read_bool()
    }

    fn read_i64(&mut self) -> IonResult<i64> {
        (**self).read_i64()
    }

    fn read_int(&mut self) -> IonResult<Int> {
        (**self).read_int()
    }

    fn read_f32(&mut self) -> IonResult<f32> {
        (**self).read_f32()
    }

    fn read_f64(&mut self) -> IonResult<f64> {
        (**self).read_f64()
    }

    fn read_decimal(&mut self) -> IonResult<Decimal> {
        (**self).read_decimal()
    }

    fn read_string(&mut self) -> IonResult<Str> {
        (**self).read_string()
    }

    fn read_str(&mut self) -> IonResult<&str> {
        (**self).read_str()
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        (**self).read_symbol()
    }

    fn read_blob(&mut self) -> IonResult<Blob> {
        (**self).read_blob()
    }

    fn read_clob(&mut self) -> IonResult<Clob> {
        (**self).read_clob()
    }

    fn read_timestamp(&mut self) -> IonResult<Timestamp> {
        (**self).read_timestamp()
    }

    fn step_in(&mut self) -> IonResult<()> {
        (**self).step_in()
    }

    fn step_out(&mut self) -> IonResult<()> {
        (**self).step_out()
    }

    fn parent_type(&self) -> Option<IonType> {
        (**self).parent_type()
    }

    fn depth(&self) -> usize {
        (**self).depth()
    }
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
            VersionMarker(major, minor) => write!(f, "ion version marker (v{major}.{minor})"),
            Value(ion_type) => write!(f, "{ion_type}"),
            Null(ion_type) => write!(f, "null.{ion_type}"),
            Nothing => write!(f, "nothing/end-of-sequence"),
        }
    }
}

/// BufferedRawReader is a RawReader which can be created from a [`Vec<u8>`] and implements the needed
/// functionality to provide non-blocking reader support. This includes the ability to add more
/// data as needed, as well as marking when the stream is complete.
pub trait BufferedRawReader: RawReader + From<Vec<u8>> {
    fn append_bytes(&mut self, bytes: &[u8]) -> IonResult<()>;
    fn read_from<R: Read>(&mut self, source: R, length: usize) -> IonResult<usize>;
    // Mark the stream as complete. This allows the reader to understand when partial parses on
    // data boundaries are not possible.
    fn stream_complete(&mut self);
    fn is_stream_complete(&self) -> bool;
}

/// Provides a mechanism for identifying input types that allow adding more data.
/// This allows for some input-type oriented behaviors, like initializing the end of stream status
/// to true if we know more data can not be added.
pub trait Expandable {
    fn expandable(&self) -> bool;
}

impl<T: AsRef<[u8]> + ?Sized> Expandable for &T {
    fn expandable(&self) -> bool {
        false
    }
}

impl Expandable for Vec<u8> {
    fn expandable(&self) -> bool {
        true
    }
}
