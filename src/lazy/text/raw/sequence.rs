#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::Range;
use winnow::combinator::opt;
use winnow::token::one_of;
use winnow::Parser;

use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, LazyRawContainer, LazyRawSequence, LazyRawValue, LazyRawValueExpr, RawValueExpr,
};
use crate::lazy::encoding::TextEncoding_1_0;
use crate::lazy::text::buffer::TextBuffer;
use crate::lazy::text::parse_result::AddContext;
use crate::lazy::text::value::{LazyRawTextValue_1_0, RawTextAnnotationsIterator};
use crate::{IonResult, IonType};

// ===== Lists =====

#[derive(Copy, Clone)]
pub struct LazyRawTextList_1_0<'data> {
    pub(crate) value: LazyRawTextValue_1_0<'data>,
}

impl<'data> LazyRawTextList_1_0<'data> {
    pub fn ion_type(&self) -> IonType {
        IonType::List
    }

    pub fn iter(&self) -> RawTextListIterator_1_0<'data> {
        // Skip past any annotations and the opening '['
        let list_contents_start = self.value.encoded_value.data_offset() + 1;
        // Make an iterator over the input bytes that follow the initial `[`
        RawTextListIterator_1_0::new(self.value.input.slice_to_end(list_contents_start))
    }
}

impl<'data> LazyContainerPrivate<'data, TextEncoding_1_0> for LazyRawTextList_1_0<'data> {
    fn from_value(value: LazyRawTextValue_1_0<'data>) -> Self {
        LazyRawTextList_1_0 { value }
    }
}

impl<'data> LazyRawContainer<'data, TextEncoding_1_0> for LazyRawTextList_1_0<'data> {
    fn as_value(&self) -> <TextEncoding_1_0 as Decoder>::Value<'data> {
        self.value
    }
}

impl<'data> LazyRawSequence<'data, TextEncoding_1_0> for LazyRawTextList_1_0<'data> {
    type Iterator = RawTextListIterator_1_0<'data>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        IonType::List
    }

    fn iter(&self) -> Self::Iterator {
        LazyRawTextList_1_0::iter(self)
    }
}

impl<'data> IntoIterator for &LazyRawTextList_1_0<'data> {
    type Item = IonResult<LazyRawValueExpr<'data, TextEncoding_1_0>>;
    type IntoIter = RawTextListIterator_1_0<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl Debug for LazyRawTextList_1_0<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for value in self {
            write!(f, "{:?}, ", value?.expect_value()?.read()?)?;
        }
        write!(f, "]").unwrap();

        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct RawTextListIterator_1_0<'data> {
    input: TextBuffer<'data>,
    // If this iterator has returned an error, it should return `None` forever afterwards
    has_returned_error: bool,
}

impl<'data> RawTextListIterator_1_0<'data> {
    pub(crate) fn new(input: TextBuffer<'data>) -> RawTextListIterator_1_0<'data> {
        RawTextListIterator_1_0 {
            input,
            has_returned_error: false,
        }
    }
}

impl RawTextListIterator_1_0<'_> {
    pub(crate) fn find_span(&self) -> IonResult<Range<usize>> {
        // The input has already skipped past the opening delimiter.
        let start = self.input.offset() - 1;
        // We need to find the input slice containing the closing delimiter. It's either...
        let mut input = if let Some(value_result) = self.last() {
            let value = value_result?.expect_value()?;
            // ...the input slice that follows the last sequence value...
            self.input
                .slice_to_end(value.input.offset() + value.total_length() - self.input.offset())
        } else {
            // ...or there aren't values, so it's just the input after the opening delimiter.
            self.input
        };
        let _ws = input
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a list", input)?;
        // Skip an optional comma and more whitespace
        let _ = (opt(","), TextBuffer::match_optional_comments_and_whitespace)
            .parse_next(&mut input)
            .with_context("skipping a list's trailing comma", input)?;
        let _end_delimiter = one_of(|c| c == b']')
            .parse_next(&mut input)
            .with_context("seeking the closing delimiter of a list", input)?;
        let end = input.offset();
        Ok(start..end)
    }
}

impl<'data> Iterator for RawTextListIterator_1_0<'data> {
    type Item = IonResult<LazyRawValueExpr<'data, TextEncoding_1_0>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_list_item() {
            Ok(Some(value)) => {
                let value = RawValueExpr::ValueLiteral(LazyRawTextValue_1_0::from(value));
                Some(Ok(value))
            }
            Ok(None) => {
                // Don't update `remaining` so subsequent calls will continue to return None
                None
            }
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next list value", self.input)
                    .transpose()
            }
        }
    }
}

// ===== S-Expressions =====

#[derive(Copy, Clone)]
pub struct LazyRawTextSExp_1_0<'top> {
    pub(crate) value: LazyRawTextValue_1_0<'top>,
}

impl<'data> LazyRawTextSExp_1_0<'data> {
    pub fn ion_type(&self) -> IonType {
        IonType::SExp
    }

    pub fn iter(&self) -> RawTextSExpIterator_1_0<'data> {
        // Make an iterator over the input bytes that follow the initial `(`; account for
        // a leading annotations sequence.
        let sexp_contents_start = self.value.encoded_value.data_offset() + 1;
        RawTextSExpIterator_1_0::new(self.value.input.slice_to_end(sexp_contents_start))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct RawTextSExpIterator_1_0<'top> {
    input: TextBuffer<'top>,
    // If this iterator has returned an error, it should return `None` forever afterwards
    has_returned_error: bool,
}

impl<'top> RawTextSExpIterator_1_0<'top> {
    pub(crate) fn new(input: TextBuffer<'top>) -> RawTextSExpIterator_1_0<'top> {
        RawTextSExpIterator_1_0 {
            input,
            has_returned_error: false,
        }
    }

    /// Scans ahead to find the end of this s-expression and reports the input span that it occupies.
    ///
    /// The `initial_bytes_skipped` parameter indicates how many bytes of input that represented the
    /// beginning of the expression are not in the buffer. For plain s-expressions, this will always
    /// be `1` as they begin with a single open parenthesis `(`. For e-expressions (which are used
    /// to invoke macros from the data stream), it will always be a minimum of `3`: two bytes for
    /// the opening `(:` and at least one for the macro identifier. (For example: `(:foo`.)
    pub(crate) fn find_span(&self, initial_bytes_skipped: usize) -> IonResult<Range<usize>> {
        // The input has already skipped past the opening delimiter.
        let start = self.input.offset() - initial_bytes_skipped;
        // We need to find the input slice containing the closing delimiter. It's either...
        let mut input = if let Some(value_result) = self.last() {
            let value = value_result?.expect_value()?;
            // ...the input slice that follows the last sequence value...
            self.input
                .slice_to_end(value.input.offset() + value.total_length() - self.input.offset())
        } else {
            // ...or there aren't values, so it's just the input after the opening delimiter.
            self.input
        };
        let _ = input
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a sexp", input)?;
        let _end_delimiter = one_of(|c| c == b')')
            .parse_next(&mut input)
            .with_context("seeking the closing delimiter of a sexp", input)?;
        let end = input.offset();
        Ok(start..end)
    }
}

impl<'data> Iterator for RawTextSExpIterator_1_0<'data> {
    type Item = IonResult<LazyRawValueExpr<'data, TextEncoding_1_0>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_sexp_item() {
            Ok(Some(value)) => Some(Ok(RawValueExpr::ValueLiteral(LazyRawTextValue_1_0::from(
                value,
            )))),
            Ok(None) => None,
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next sexp value", self.input)
                    .transpose()
            }
        }
    }
}

impl<'data> LazyContainerPrivate<'data, TextEncoding_1_0> for LazyRawTextSExp_1_0<'data> {
    fn from_value(value: LazyRawTextValue_1_0<'data>) -> Self {
        LazyRawTextSExp_1_0 { value }
    }
}

impl<'data> LazyRawContainer<'data, TextEncoding_1_0> for LazyRawTextSExp_1_0<'data> {
    fn as_value(&self) -> <TextEncoding_1_0 as Decoder>::Value<'data> {
        self.value
    }
}

impl<'data> LazyRawSequence<'data, TextEncoding_1_0> for LazyRawTextSExp_1_0<'data> {
    type Iterator = RawTextSExpIterator_1_0<'data>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        IonType::SExp
    }

    fn iter(&self) -> Self::Iterator {
        LazyRawTextSExp_1_0::iter(self)
    }
}

impl<'data> IntoIterator for &LazyRawTextSExp_1_0<'data> {
    type Item = IonResult<LazyRawValueExpr<'data, TextEncoding_1_0>>;
    type IntoIter = RawTextSExpIterator_1_0<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl Debug for LazyRawTextSExp_1_0<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for value in self {
            write!(f, "{:?} ", value?.expect_value()?.read()?)?;
        }
        write!(f, ")").unwrap();

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
    use crate::IonResult;

    fn expect_sequence_range(ion_data: &str, expected: Range<usize>) -> IonResult<()> {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let reader = &mut LazyRawTextReader_1_0::new(context, ion_data.as_bytes(), true);
        let value = reader.next()?.expect_value()?;
        let actual_range = value.data_range();
        assert_eq!(
            actual_range, expected,
            "Sequence range ({:?}) did not match expected range ({:?})",
            actual_range, expected
        );
        Ok(())
    }

    #[test]
    fn list_range() -> IonResult<()> {
        // For each pair below, we'll confirm that the top-level list is found to
        // occupy the specified input span.
        let tests = &[
            // (Ion input, expected range of the sequence)
            ("[]", 0..2),
            ("  []  ", 2..4),
            ("[1, 2]", 0..6),
            ("[1, /* comment ]]] */ 2]", 0..24),
            // Nested
            ("[1, 2, [3, 4, 5], 6]", 0..20),
            // Doubly nested
            ("[1, 2, [3, [a, b, c], 5], 6]", 0..28),
        ];
        for test in tests {
            println!("input: {}", test.0);
            expect_sequence_range(test.0, test.1.clone())?;
        }
        Ok(())
    }
}
