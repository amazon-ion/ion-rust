use crate::lazy::binary::raw::v1_1::binary_buffer::BinaryBuffer;
use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::lazy::text::buffer::TextBuffer;
use crate::result::IonFailure;
use crate::{HasRange, IonError, IonResult};
use std::ops::Range;

/// Represents a slice of input data.
///
/// Various items in the Reader API implement the [`HasSpan`](crate::lazy::decoder::HasSpan) trait,
/// allowing the byte slice that represented that item in the input by calling `span()`.
#[derive(Debug, Copy, Clone)]
pub struct Span<'a> {
    // The input bytes that represented the item implementing `HasSpan`.
    bytes: &'a [u8],
    // The offset in the overall stream at which the contents of `bytes` were found.
    offset: usize,
}

impl AsRef<[u8]> for Span<'_> {
    fn as_ref(&self) -> &[u8] {
        self.bytes()
    }
}

impl<'a> From<Span<'a>> for &'a [u8] {
    fn from(value: Span<'a>) -> Self {
        value.bytes
    }
}

impl<A: AsRef<[u8]>> PartialEq<A> for Span<'_> {
    fn eq(&self, other: &A) -> bool {
        self.bytes() == other.as_ref()
    }
}

impl<'a> Span<'a> {
    pub fn with_offset(offset: usize, bytes: &'a [u8]) -> Self {
        Self { bytes, offset }
    }

    pub fn offset(&self) -> usize {
        self.offset
    }

    pub fn range(&self) -> Range<usize> {
        self.offset..self.offset + self.bytes.len()
    }

    pub fn bytes(&self) -> &'a [u8] {
        self.bytes
    }

    pub fn text(&self) -> Option<&'a str> {
        self.expect_text().ok()
    }

    pub fn expect_text(&self) -> IonResult<&'a str> {
        std::str::from_utf8(self.bytes)
            .map_err(|_| IonError::decoding_error("span text was not valid UTF-8"))
    }

    pub fn len(&self) -> usize {
        self.bytes.len()
    }

    pub fn is_empty(&self) -> bool {
        self.bytes.is_empty()
    }

    pub fn slice(&self, offset: usize, length: usize) -> Span<'a> {
        Self {
            bytes: &self.bytes[offset..offset + length],
            offset: self.offset + offset,
            ..*self
        }
    }

    pub fn slice_to_end(&self, offset: usize) -> Span<'a> {
        Self {
            bytes: &self.bytes[offset..],
            offset: self.offset + offset,
            ..*self
        }
    }
}

impl<'a> HasRange for Span<'a> {
    fn range(&self) -> Range<usize> {
        self.offset..self.offset + self.bytes.len()
    }
}

impl<'a> From<BinaryBuffer<'a>> for Span<'a> {
    fn from(value: BinaryBuffer<'a>) -> Self {
        Span {
            bytes: value.bytes(),
            offset: value.offset(),
        }
    }
}

impl<'a> From<TextBuffer<'a>> for Span<'a> {
    fn from(value: TextBuffer<'a>) -> Self {
        Span {
            bytes: value.bytes(),
            offset: value.offset(),
        }
    }
}

impl<'a> From<&'a IoBuffer> for Span<'a> {
    fn from(value: &'a IoBuffer) -> Self {
        Span {
            bytes: value.remaining_bytes(),
            offset: value.stream_position(),
        }
    }
}
