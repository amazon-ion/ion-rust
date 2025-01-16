#![allow(non_camel_case_types)]

use crate::lazy::decoder::{HasRange, HasSpan, LazyRawFieldExpr, LazyRawFieldName};
use crate::lazy::encoding::{TextEncoding, TextEncoding_1_0, TextEncoding_1_1};
use crate::lazy::span::Span;
use crate::lazy::text::buffer::{whitespace_and_then, TextBuffer};
use crate::lazy::text::matched::MatchedFieldName;
use crate::lazy::text::parse_result::WithContext;
use crate::{IonResult, RawSymbolRef};
use std::marker::PhantomData;
use std::ops::Range;
use winnow::combinator::{alt, peek, terminated};
use winnow::Parser;

#[derive(Clone, Copy, Debug)]
pub struct RawTextStructIterator<'top, E: TextEncoding<'top>> {
    input: TextBuffer<'top>,
    has_returned_error: bool,
    spooky: PhantomData<E>,
}

impl<'top, E: TextEncoding<'top>> RawTextStructIterator<'top, E> {
    pub fn new(input: TextBuffer<'top>) -> Self {
        Self {
            input,
            has_returned_error: false,
            spooky: PhantomData,
        }
    }
}

impl<'top, E: TextEncoding<'top>> Iterator for RawTextStructIterator<'top, E> {
    type Item = IonResult<LazyRawFieldExpr<'top, E>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }

        let result = whitespace_and_then(alt((
            // If it's the end of the struct, don't consume it so future calls will also yield `None`
            peek("}").value(None),
            terminated(
                E::field_expr_matcher().map(Some),
                whitespace_and_then(
                    // Either a comma (consumed) or an upcoming end-of-struct (not consumed)
                    alt((",", peek("}"))),
                ),
            ),
        )))
        .parse_next(&mut self.input);
        match result {
            Ok(Some(field)) => Some(Ok(field)),
            Ok(None) => None,
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading a struct field", self.input)
                    .transpose()
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawTextFieldName<'top, E: TextEncoding<'top>> {
    matched: MatchedFieldName<'top>,
    // XXX: Ion 1.0 and 1.1 use the same syntax for field names.
    // This type is generic over the encoding because if it is not, the user must manually
    // specify 1.0 or 1.1 in a variety of places. When it is generic, the compiler can infer
    // the Ion version from context.
    spooky: PhantomData<E>,
}

impl<'top, E: TextEncoding<'top>> LazyRawTextFieldName<'top, E> {
    pub(crate) fn new(matched: MatchedFieldName<'top>) -> Self {
        Self {
            matched,
            spooky: PhantomData,
        }
    }
}

impl<'top, E: TextEncoding<'top>> HasSpan<'top> for LazyRawTextFieldName<'top, E> {
    fn span(&self) -> Span<'top> {
        self.matched.span()
    }
}

impl<'top, E: TextEncoding<'top>> HasRange for LazyRawTextFieldName<'top, E> {
    fn range(&self) -> Range<usize> {
        self.matched.range()
    }
}

impl<'top> LazyRawFieldName<'top, TextEncoding_1_0>
    for LazyRawTextFieldName<'top, TextEncoding_1_0>
{
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        self.matched.read()
    }
}

impl<'top> LazyRawFieldName<'top, TextEncoding_1_1>
    for LazyRawTextFieldName<'top, TextEncoding_1_1>
{
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        self.matched.read()
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
