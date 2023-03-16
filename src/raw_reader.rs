use crate::raw_symbol_token::RawSymbolToken;
use crate::stream_reader::IonReader;
use crate::types::IonType;
use crate::{Decimal, Int, IonResult, Timestamp};
use std::fmt::{Display, Formatter};

/// `RawReader` is a shorthand for a [Reader](crate::Reader) implementation that returns [RawStreamItem]s and
/// uses [RawSymbolToken] to represent its field names, annotations, and symbol values.
pub trait RawReader: IonReader<Item = RawStreamItem, Symbol = RawSymbolToken> {
    // Mark the stream as complete. This allows the reader to understand when partial parses on
    // data boundaries are not possible.
    fn stream_complete(&mut self);
}
impl<T> RawReader for T
where
    T: IonReader<Item = RawStreamItem, Symbol = RawSymbolToken>,
{
    fn stream_complete(&mut self) {}
}

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

    fn read_string(&mut self) -> IonResult<String> {
        (**self).read_string()
    }

    fn map_string<F, U>(&mut self, _f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&str) -> U,
    {
        todo!("Cannot use `map_string` via dynamic dispatch. Use `read_string` instead. See: https://github.com/amazon-ion/ion-rust/issues/335")
    }

    fn map_string_bytes<F, U>(&mut self, _f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        todo!("Cannot use `map_string_bytes` via dynamic dispatch. Use `read_string` instead. See: https://github.com/amazon-ion/ion-rust/issues/335")
    }

    fn read_symbol(&mut self) -> IonResult<Self::Symbol> {
        (**self).read_symbol()
    }

    fn read_blob(&mut self) -> IonResult<Vec<u8>> {
        (**self).read_blob()
    }

    fn map_blob<F, U>(&mut self, _f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        todo!("Cannot use `map_blob` via dynamic dispatch. Use `read_blob` instead. See: https://github.com/amazon-ion/ion-rust/issues/335")
    }

    fn read_clob(&mut self) -> IonResult<Vec<u8>> {
        (**self).read_clob()
    }

    fn map_clob<F, U>(&mut self, _f: F) -> IonResult<U>
    where
        Self: Sized,
        F: FnOnce(&[u8]) -> U,
    {
        todo!("Cannot use `map_clob` via dynamic dispatch. Use `read_clob` instead. See: https://github.com/amazon-ion/ion-rust/issues/335")
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
