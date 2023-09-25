#![allow(non_camel_case_types)]
use std::ops::Range;

use nom::character::streaming::satisfy;

use crate::lazy::decoder::private::{LazyContainerPrivate, LazyRawFieldPrivate};
use crate::lazy::decoder::{LazyRawField, LazyRawStruct, LazyRawValue};
use crate::lazy::encoding::TextEncoding_1_0;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::{AddContext, ToIteratorOutput};
use crate::lazy::text::value::{LazyRawTextValue_1_0, RawTextAnnotationsIterator};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{IonResult, RawSymbolTokenRef};

#[derive(Clone, Copy, Debug)]
pub struct RawTextStructIterator_1_0<'data> {
    input: TextBufferView<'data>,
    has_returned_error: bool,
}

impl<'data> RawTextStructIterator_1_0<'data> {
    pub(crate) fn new(input: TextBufferView<'data>) -> Self {
        RawTextStructIterator_1_0 {
            input,
            has_returned_error: false,
        }
    }

    pub(crate) fn find_span(&self) -> IonResult<Range<usize>> {
        // The input has already skipped past the opening delimiter.
        let start = self.input.offset() - 1;
        // We need to find the input slice containing the closing delimiter. It's either...
        let input_after_last = if let Some(field_result) = self.last() {
            let field = field_result?;
            // ...the input slice that follows the last field...
            field
                .value
                .input
                .slice_to_end(field.value.encoded_value.total_length())
        } else {
            // ...or there aren't fields, so it's just the input after the opening delimiter.
            self.input
        };
        let (mut input_after_ws, _ws) =
            input_after_last
                .match_optional_comments_and_whitespace()
                .with_context("seeking the end of a struct", input_after_last)?;
        // Skip an optional comma and more whitespace
        if input_after_ws.bytes().first() == Some(&b',') {
            (input_after_ws, _) = input_after_ws
                .slice_to_end(1)
                .match_optional_comments_and_whitespace()
                .with_context("skipping a list's trailing comma", input_after_ws)?;
        }
        let (input_after_end, _end_delimiter) = satisfy(|c| c == b'}' as char)(input_after_ws)
            .with_context("seeking the closing delimiter of a struct", input_after_ws)?;
        let end = input_after_end.offset();
        Ok(start..end)
    }
}

impl<'data> Iterator for RawTextStructIterator_1_0<'data> {
    type Item = IonResult<LazyRawTextField_1_0<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_struct_field() {
            Ok((remaining_input, Some(field))) => {
                self.input = remaining_input;
                Some(Ok(field))
            }
            Ok((_, None)) => None,
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next struct field", self.input)
                    .transpose()
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct LazyRawTextField_1_0<'data> {
    pub(crate) value: LazyRawTextValue_1_0<'data>,
}

impl<'data> LazyRawTextField_1_0<'data> {
    pub(crate) fn new(value: LazyRawTextValue_1_0<'data>) -> Self {
        LazyRawTextField_1_0 { value }
    }

    pub fn name(&self) -> RawSymbolTokenRef<'data> {
        // We're in a struct field, the field name _must_ be populated.
        // If it's not (or the field name is not a valid SID or UTF-8 string),
        // that's a bug. We can safely unwrap/expect here.
        let matched_symbol = self
            .value
            .encoded_value
            .field_name_syntax()
            .expect("field name syntax not available");
        let name_length = self
            .value
            .encoded_value
            .field_name_range()
            .expect("field name length not available")
            .len();
        matched_symbol
            .read(self.value.input.slice(0, name_length))
            .expect("invalid struct field name")
    }

    pub fn value(&self) -> LazyRawTextValue_1_0<'data> {
        self.value
    }

    pub(crate) fn into_value(self) -> LazyRawTextValue_1_0<'data> {
        self.value
    }
}

impl<'data> LazyRawFieldPrivate<'data, TextEncoding_1_0> for LazyRawTextField_1_0<'data> {
    fn into_value(self) -> LazyRawTextValue_1_0<'data> {
        self.value
    }
}

impl<'data> LazyRawField<'data, TextEncoding_1_0> for LazyRawTextField_1_0<'data> {
    fn name(&self) -> RawSymbolTokenRef<'data> {
        LazyRawTextField_1_0::name(self)
    }

    fn value(&self) -> LazyRawTextValue_1_0<'data> {
        self.value()
    }
}

#[derive(Clone, Copy, Debug)]
pub struct LazyRawTextStruct_1_0<'data> {
    pub(crate) value: LazyRawTextValue_1_0<'data>,
}

impl<'data> LazyRawTextStruct_1_0<'data> {
    fn find(&self, name: &str) -> IonResult<Option<LazyRawTextValue_1_0<'data>>> {
        let name: RawSymbolTokenRef = name.as_raw_symbol_token_ref();
        for field_result in *self {
            let field = field_result?;
            let field_name = field.name();
            if field_name == name {
                let value = field.value;
                return Ok(Some(value));
            }
        }
        Ok(None)
    }
}

impl<'data> LazyContainerPrivate<'data, TextEncoding_1_0> for LazyRawTextStruct_1_0<'data> {
    fn from_value(value: LazyRawTextValue_1_0<'data>) -> Self {
        LazyRawTextStruct_1_0 { value }
    }
}

impl<'data> LazyRawStruct<'data, TextEncoding_1_0> for LazyRawTextStruct_1_0<'data> {
    type Field = LazyRawTextField_1_0<'data>;
    type Iterator = RawTextStructIterator_1_0<'data>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.value.annotations()
    }

    fn find(&self, name: &str) -> IonResult<Option<LazyRawTextValue_1_0<'data>>> {
        self.find(name)
    }

    fn iter(&self) -> Self::Iterator {
        let open_brace_index = self.value.encoded_value.data_offset() - self.value.input.offset();
        // Slice the input to skip the opening `{`
        RawTextStructIterator_1_0::new(self.value.input.slice_to_end(open_brace_index + 1))
    }
}

impl<'data> IntoIterator for LazyRawTextStruct_1_0<'data> {
    type Item = IonResult<LazyRawTextField_1_0<'data>>;
    type IntoIter = RawTextStructIterator_1_0<'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Range;

    use crate::lazy::text::raw::reader::LazyRawTextReader;
    use crate::IonResult;

    fn expect_struct_range(ion_data: &str, expected: Range<usize>) -> IonResult<()> {
        let reader = &mut LazyRawTextReader::new(ion_data.as_bytes());
        let value = reader.next()?.expect_value()?;
        let actual_range = value.encoded_value.data_range();
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
        // For each pair below, we'll confirm that the top-level list is found to
        // occupy the specified input span.
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
}
