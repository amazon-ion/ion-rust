use crate::lazy::decoder::{HasRange, HasSpan, LazyDecoder};
use crate::lazy::span::Span;
use crate::result::IonFailure;
use crate::{IonError, IonResult};
use std::fmt::Debug;
use std::ops::Range;

#[derive(Debug)]
/// Raw stream components that a RawReader may encounter.
pub enum RawStreamItem<M: Debug, V: Debug, E: Debug> {
    /// An Ion Version Marker (IVM) indicating the Ion major and minor version that were used to
    /// encode the values that follow.
    VersionMarker(M),
    /// An Ion value whose data has not yet been read. For more information about how to read its
    /// data and (in the case of containers) access any nested values, see the documentation
    /// for [`LazyRawBinaryValue`](crate::lazy::binary::raw::value::LazyRawBinaryValue_1_0).
    Value(V),
    /// An Ion 1.1+ macro invocation. Ion 1.0 readers will never return a macro invocation.
    EExpression(E),
    /// The end of the stream
    EndOfStream(EndPosition),
}

pub type LazyRawStreamItem<'top, D> = RawStreamItem<
    <D as LazyDecoder>::VersionMarker<'top>,
    <D as LazyDecoder>::Value<'top>,
    <D as LazyDecoder>::EExp<'top>,
>;

impl<M: Debug + HasRange, V: Debug + HasRange, E: Debug + HasRange> HasRange
    for RawStreamItem<M, V, E>
{
    fn range(&self) -> Range<usize> {
        use RawStreamItem::*;
        match self {
            VersionMarker(marker) => marker.range(),
            Value(value) => value.range(),
            EExpression(eexp) => eexp.range(),
            EndOfStream(eos) => eos.range(),
        }
    }
}

impl<'top, M: Debug + HasSpan<'top>, V: Debug + HasSpan<'top>, E: Debug + HasSpan<'top>>
    HasSpan<'top> for RawStreamItem<M, V, E>
{
    fn span(&self) -> Span<'top> {
        use RawStreamItem::*;
        match self {
            VersionMarker(marker) => marker.span(),
            Value(value) => value.span(),
            EExpression(eexp) => eexp.span(),
            EndOfStream(eos) => eos.span(),
        }
    }
}

impl<M: Copy + Debug, V: Copy + Debug, E: Copy + Debug> RawStreamItem<M, V, E> {
    /// If this item is an Ion version marker (IVM), returns `Some((major, minor))` indicating the
    /// version. Otherwise, returns `None`.
    pub fn version_marker(&self) -> Option<M> {
        if let Self::VersionMarker(marker) = self {
            Some(*marker)
        } else {
            None
        }
    }

    /// Like [`Self::version_marker`], but returns a [`IonError::Decoding`] if this item
    /// is not an IVM.
    pub fn expect_ivm(self) -> IonResult<M> {
        self.version_marker()
            .ok_or_else(|| IonError::decoding_error(format!("expected IVM, found {:?}", self)))
    }

    /// If this item is a value, returns `Some(&LazyValue)`. Otherwise, returns `None`.
    pub fn value(&self) -> Option<&V> {
        if let Self::Value(value) = self {
            Some(value)
        } else {
            None
        }
    }

    /// Like [`Self::value`], but returns a [`IonError::Decoding`] if this item is not
    /// a value.
    pub fn expect_value(self) -> IonResult<V> {
        if let Self::Value(value) = self {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("expected value, found {:?}", self))
        }
    }

    pub fn as_macro_invocation(&self) -> Option<&E> {
        if let Self::EExpression(m) = self {
            Some(m)
        } else {
            None
        }
    }

    pub fn expect_macro_invocation(self) -> IonResult<E> {
        if let Self::EExpression(m) = self {
            Ok(m)
        } else {
            IonResult::decoding_error(format!("expected a macro invocation, found {:?}", self))
        }
    }
}

/// Represents the end of a [`RawInputStream`].
///
/// This type implements [`HasRange`] and [`HasSpan`]. These traits aren't especially useful for the
/// `EndPosition` type itself, but implementing them allows the `RawStreamItem` type (which contains
/// an `EndOfStream(EndPosition)` variant) to also implement them.
#[derive(Debug, Copy, Clone)]
pub struct EndPosition {
    position: usize,
}

impl EndPosition {
    pub(crate) fn new(position: usize) -> Self {
        Self { position }
    }
}

impl HasRange for EndPosition {
    /// Returns an empty range whose matching `start` and `end` represent the first byte index at
    /// the end of the stream which contains no data. For example, in the stream `1 2 3`,
    /// `EndPosition::range(...)` would return the range `5..5`.
    fn range(&self) -> Range<usize> {
        self.position..self.position
    }
}

impl<'top> HasSpan<'top> for EndPosition {
    /// Returns an empty [`Span`]. The range of the span will match that produced by
    /// [`range`](Self::range).
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.position, &[])
    }
}
