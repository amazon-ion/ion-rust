#![allow(non_camel_case_types)]

use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawFieldName,
    LazyRawStruct, LazyRawValue,
};
use crate::lazy::encoding::TextEncoding_1_0;
use crate::lazy::span::Span;
use crate::lazy::text::buffer::TextBuffer;
use crate::lazy::text::matched::MatchedFieldName;
use crate::lazy::text::parse_result::AddContext;
use crate::lazy::text::value::{LazyRawTextValue_1_0, RawTextAnnotationsIterator};
use crate::{IonResult, RawSymbolRef};
use std::ops::Range;
use winnow::combinator::opt;
use winnow::token::one_of;
use winnow::Parser;

#[derive(Clone, Copy, Debug)]
pub struct RawTextStructIterator_1_0<'top> {
    input: TextBuffer<'top>,
    has_returned_error: bool,
}

impl<'top> RawTextStructIterator_1_0<'top> {
    pub(crate) fn new(input: TextBuffer<'top>) -> Self {
        RawTextStructIterator_1_0 {
            input,
            has_returned_error: false,
        }
    }

    pub(crate) fn find_span(&self) -> IonResult<Range<usize>> {
        // The input has already skipped past the opening delimiter.
        let start = self.input.offset() - 1;
        // We need to find the input slice containing the closing delimiter. It's either...
        let mut input = if let Some(field_result) = self.last() {
            let field = field_result?;
            self.input
                .slice_to_end(field.range().end - self.input.offset())
        } else {
            // ...or there aren't fields, so it's just the input after the opening delimiter.
            self.input
        };
        let _ws = input
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a struct", input)?;
        // Skip an optional comma and more whitespace
        let _ = (opt(","), TextBuffer::match_optional_comments_and_whitespace)
            .parse_next(&mut input)
            .with_context("skipping a struct field's trailing comma", input)?;
        let _end_delimiter = one_of(|c| c == b'}')
            .parse_next(&mut input)
            .with_context("seeking the closing delimiter of a struct", input)?;
        let end = input.offset();
        Ok(start..end)
    }
}

impl<'top> Iterator for RawTextStructIterator_1_0<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, TextEncoding_1_0>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_struct_field() {
            Ok(Some(field)) => Some(Ok(field)),
            Ok(None) => None,
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next struct field", self.input)
                    .transpose()
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawTextFieldName_1_0<'top> {
    matched: MatchedFieldName<'top>,
}

impl<'top> LazyRawTextFieldName_1_0<'top> {
    pub(crate) fn new(matched: MatchedFieldName<'top>) -> Self {
        Self { matched }
    }
}

impl<'top> HasSpan<'top> for LazyRawTextFieldName_1_0<'top> {
    fn span(&self) -> Span<'top> {
        self.matched.span()
    }
}

impl HasRange for LazyRawTextFieldName_1_0<'_> {
    fn range(&self) -> Range<usize> {
        self.matched.range()
    }
}

impl<'top> LazyRawFieldName<'top, TextEncoding_1_0> for LazyRawTextFieldName_1_0<'top> {
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        self.matched.read()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct LazyRawTextStruct_1_0<'top> {
    pub(crate) value: LazyRawTextValue_1_0<'top>,
}

impl<'top> LazyContainerPrivate<'top, TextEncoding_1_0> for LazyRawTextStruct_1_0<'top> {
    fn from_value(value: LazyRawTextValue_1_0<'top>) -> Self {
        LazyRawTextStruct_1_0 { value }
    }
}

impl<'top> LazyRawContainer<'top, TextEncoding_1_0> for LazyRawTextStruct_1_0<'top> {
    fn as_value(&self) -> <TextEncoding_1_0 as Decoder>::Value<'top> {
        self.value
    }
}

impl<'top> LazyRawStruct<'top, TextEncoding_1_0> for LazyRawTextStruct_1_0<'top> {
    type Iterator = RawTextStructIterator_1_0<'top>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'top> {
        self.value.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        // Make an iterator over the input bytes that follow the initial `{`; account for
        // a leading annotations sequence.
        let struct_contents_start = self.value.encoded_value.data_offset() + 1;
        RawTextStructIterator_1_0::new(self.value.input.slice_to_end(struct_contents_start))
    }
}

impl<'top> IntoIterator for LazyRawTextStruct_1_0<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, TextEncoding_1_0>>;
    type IntoIter = RawTextStructIterator_1_0<'top>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use crate::lazy::decoder::{HasRange, HasSpan, LazyRawStruct, LazyRawValue};
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
    use crate::IonResult;

    fn expect_struct_range(ion_data: &str, expected: Range<usize>) -> IonResult<()> {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let reader = &mut LazyRawTextReader_1_0::new(context, ion_data.as_bytes(), true);
        let value = reader.next()?.expect_value()?;
        let actual_range = value.data_range();
        assert_eq!(
            actual_range, expected,
            "Struct range ({:?}) did not match expected range ({:?})",
            actual_range, expected
        );
        println!("input ok: {}", ion_data);
        Ok(())
    }

    #[test]
    fn struct_range() -> IonResult<()> {
        // For each pair below, we'll confirm that the top-level struct is found to
        // occupy the specified input range.
        let tests = &[
            // (Ion input, expected range of the struct)
            ("{}", 0..2),
            ("  {}  ", 2..4),
            ("{a:1}", 0..5),
            ("{a: 1}", 0..6),
            ("{a: 1, b: 2}", 0..12),
            ("{a: 1, /* comment }}} */ b: 2}", 0..30),
            // Nested
            ("{a: 1, b: 2, c: {d: 3, e: 4, f: 5}, g: 6}", 0..41),
            // Doubly nested
            ("{a: 1, b: 2, c: {d: 3, e: {foo: bar}, f: 5}, g: 6}", 0..50),
        ];
        for test in tests {
            expect_struct_range(test.0, test.1.clone())?;
        }
        Ok(())
    }

    #[test]
    // Clippy thinks a slice with a single range inside is likely to be a mistake, but in this
    // test it's intentional.
    #[allow(clippy::single_range_in_vec_init)]
    fn field_name_ranges() -> IonResult<()> {
        // For each pair below, we'll confirm that the top-level struct's field names are found to
        // occupy the specified input ranges.
        type FieldNameAndRange<'a> = (&'a str, Range<usize>);
        type FieldTest<'a> = (&'a str, &'a [FieldNameAndRange<'a>]);
        let tests: &[FieldTest<'_>] = &[
            // (Ion input, expected ranges of the struct's field names)
            ("{a:1}", &[("a", 1..2)]),
            ("{a: 1}", &[("a", 1..2)]),
            ("{a: 1, b: 2}", &[("a", 1..2), ("b", 7..8)]),
            (
                "{a: 1, /* comment }}} */ b: 2}",
                &[("a", 1..2), ("b", 25..26)],
            ),
            ("{ a: /* comment */ 1, b: 2}", &[("a", 2..3), ("b", 22..23)]),
            (
                "{a: 1, b: 2, c: {d: 3, e: 4, f: 5}, g: 6}",
                &[
                    ("a", 1..2),
                    ("b", 7..8),
                    ("c", 13..14),
                    //...nested fields...
                    ("g", 36..37),
                ],
            ),
        ];
        for (input, field_name_ranges) in tests {
            let encoding_context = EncodingContext::empty();
            let context = encoding_context.get_ref();
            let mut reader = LazyRawTextReader_1_0::new(context, input.as_bytes(), true);
            let struct_ = reader.next()?.expect_value()?.read()?.expect_struct()?;
            for (field_result, (expected_name, expected_range)) in
                struct_.iter().zip(field_name_ranges.iter())
            {
                let field_name = field_result?.name();
                assert_eq!(
                    field_name.span(),
                    expected_name.as_bytes(),
                    "span failure for input {input} -> field {expected_name}"
                );
                assert_eq!(
                    field_name.range(),
                    *expected_range,
                    "range failure for input {input} -> field {expected_name}"
                );
                println!(
                    "SUCCESS: input {} -> field {} -> {} ({:?})",
                    input,
                    expected_name,
                    field_name.span().expect_text()?,
                    field_name.range()
                );
            }
        }
        Ok(())
    }
}
