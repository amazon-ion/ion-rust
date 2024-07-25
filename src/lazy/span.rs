use crate::result::IonFailure;
use crate::{IonError, IonResult};
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

impl<'a> AsRef<[u8]> for Span<'a> {
    fn as_ref(&self) -> &[u8] {
        self.bytes()
    }
}

impl<'a> Into<&'a [u8]> for Span<'a> {
    fn into(self) -> &'a [u8] {
        self.bytes
    }
}

impl<'a, A: AsRef<[u8]>> PartialEq<A> for Span<'a> {
    fn eq(&self, other: &A) -> bool {
        self.bytes() == other.as_ref()
    }
}

impl<'a> Span<'a> {
    pub fn with_offset(offset: usize, bytes: &'a [u8]) -> Self {
        Self { bytes, offset }
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
}
