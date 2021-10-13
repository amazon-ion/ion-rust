use nom::Err::Incomplete;
use nom::IResult;

use crate::result::{decoding_error, IonResult};
use crate::text::parsers::containers::{
    list_item_or_end, s_expression_item_or_end, struct_field_name_or_end, struct_stream_item,
};
use crate::text::parsers::top_level::top_level_stream_item;
use crate::text::text_buffer::TextBuffer;
use crate::text::text_data_source::TextIonDataSource;
use crate::text::TextStreamItem;
use crate::value::owned::OwnedSymbolToken;

// TODO: Implement a full text reader.
//       This implementation is a placeholder. It is currently capable of reading a stream of top-level
//       scalar values of any type. It cannot:
//       * Step in/out
//       * Read annotations
//       * Skip comments
//       * Report the end of the stream

pub struct TextReader<T: TextIonDataSource> {
    buffer: TextBuffer<T::TextSource>,
    current_item: Option<TextStreamItem>,
    bytes_read: usize,
    is_eof: bool,
}

impl<T: TextIonDataSource> TextReader<T> {
    fn new(input: T) -> TextReader<T> {
        let text_source = input.to_text_ion_data_source();
        TextReader {
            buffer: TextBuffer::new(text_source),
            current_item: None,
            bytes_read: 0,
            is_eof: false,
        }
    }

    pub fn bytes_read(&self) -> usize {
        self.bytes_read
    }

    //TODO: TextStreamItem is an internal data type and should not be part of the public API.
    //      This method is currently private and only usable in this module's unit tests.
    fn next(&mut self) -> IonResult<Option<(Vec<OwnedSymbolToken>, TextStreamItem)>> {
        // TODO: When the reader eventually tracks what containers we've stepped into or out of,
        //       this method will call the appropriate parser.
        self.next_top_level_item()
    }

    /// Assumes that the reader is at the top level and attempts to parse the next value or IVM in
    /// the stream.
    fn next_top_level_item(
        &mut self,
    ) -> IonResult<Option<(Vec<OwnedSymbolToken>, TextStreamItem)>> {
        match self.parse_next(top_level_stream_item) {
            Ok(Some(item)) => Ok(Some(item)),
            Ok(None) => {
                // The top level is the only depth at which EOF is legal. If we encounter an EOF,
                // double check that the buffer doesn't actually have a value in it. See the
                // comments in [parse_stream_item_at_eof] for a detailed explanation of this.
                self.parse_stream_item_at_eof()
            }
            Err(e) => Err(e),
        }
    }

    /// Assumes that the reader is inside a list and attempts to parse the next value.
    /// If the next token in the stream is an end-of-list delimiter (`]`), returns Ok(None).
    fn next_list_item(&mut self) -> IonResult<Option<(Vec<OwnedSymbolToken>, TextStreamItem)>> {
        self.parse_expected("a list", list_item_or_end)
    }

    /// Assumes that the reader is inside an s-expression and attempts to parse the next value.
    /// If the next token in the stream is an end-of-s-expression delimiter (`)`), returns Ok(None).
    fn next_s_expression_item(
        &mut self,
    ) -> IonResult<Option<(Vec<OwnedSymbolToken>, TextStreamItem)>> {
        self.parse_expected("an s-expression", s_expression_item_or_end)
    }

    /// Assumes that the reader is inside an struct and attempts to parse the next field name.
    /// If the next token in the stream is an end-of-struct delimiter (`}`), returns Ok(None).
    fn next_struct_field_name(&mut self) -> IonResult<Option<OwnedSymbolToken>> {
        // If there isn't another value, this returns Ok(None).
        self.parse_expected("a struct field name", struct_field_name_or_end)
    }

    /// Assumes that the reader is inside a struct AND that a field has already been successfully
    /// parsed from input using [next_struct_field_name] and attempts to parse the next value.
    /// In this input position, only a value (or whitespace/comments) are legal. Anything else
    /// (including EOF) will result in a decoding error.
    fn next_struct_item(&mut self) -> IonResult<(Vec<OwnedSymbolToken>, TextStreamItem)> {
        // Only called after a call to [next_struct_field_name] that returns Some(field_name).
        // It is not legal for a field name to be followed by a '}' or EOF.
        // If there isn't another value, returns an Err.
        self.parse_expected("a struct field value", struct_stream_item)
    }

    /// Attempts to parse the next entity from the stream using the provided parser.
    /// Returns a decoding error if EOF is encountered while parsing.
    /// If the parser encounters an error, it will be returned as-is.
    fn parse_expected<P, O>(&mut self, entity_name: &str, parser: P) -> IonResult<O>
    where
        P: Fn(&str) -> IResult<&str, O>,
    {
        match self.parse_next(parser) {
            Ok(Some(item)) => Ok(item),
            Ok(None) => decoding_error(format!(
                "Unexpected end of input while reading {} on line {}: '{}'",
                entity_name,
                self.buffer.lines_loaded(),
                self.buffer.remaining_text()
            )),
            Err(e) => Err(e),
        }
    }

    /// Attempts to parse the next entity from the stream using the provided parser.
    /// If there isn't enough data in the buffer for the parser to match its input conclusively,
    /// more data will be loaded into the buffer and the parser will be called again.
    /// If EOF is encountered, returns `Ok(None)`.
    fn parse_next<P, O>(&mut self, parser: P) -> IonResult<Option<O>>
    where
        P: Fn(&str) -> IResult<&str, O>,
    {
        if self.is_eof {
            return Ok(None);
        }

        let item = 'parse: loop {
            // Note the number of bytes currently in the text buffer
            let length_before_parse = self.buffer.remaining_text().len();
            // Invoke the top_level_value() parser; this will attempt to recognize the next item
            // in the stream and return a &str slice containing the remaining, not-yet-parsed text.
            match parser(self.buffer.remaining_text()) {
                // If `top_level_value` returns 'Incomplete', there wasn't enough text in the buffer
                // to match the next item. No syntax errors have been encountered (yet?), but we
                // need to load more text into the buffer before we try to parse it again.
                Err(Incomplete(_needed)) => {
                    // Ask the buffer to load another line of text.
                    // TODO: Currently this loads a single line at a time for easier testing.
                    //       We may wish to bump it to a higher number of lines at a time (8?)
                    //       for efficiency once we're confident in the correctness.
                    if self.buffer.load_next_line()? == 0 {
                        // If load_next_line() returns Ok(0), we've reached the end of our input.
                        self.is_eof = true;
                        // The buffer had an `Incomplete` value in it; now that we know we're at EOF,
                        // we can determine whether the buffer's contents should actually be
                        // considered complete.
                        return Ok(None);
                    }
                    continue;
                }
                Ok((remaining_text, item)) => {
                    // Our parser successfully matched a stream item.
                    // Note the length of the text that remains after parsing.
                    let length_after_parse = remaining_text.len();
                    // The difference in length tells us how many bytes were part of the
                    // text representation of the value that we found.
                    let bytes_consumed = length_before_parse - length_after_parse;
                    // Discard `bytes_consumed` bytes from the TextBuffer.
                    self.buffer.consume(bytes_consumed);
                    self.bytes_read += bytes_consumed;
                    // Break out of the read/parse loop, returning the stream item that we matched.
                    break 'parse item;
                }
                Err(e) => {
                    // Return an error that contains the text currently in the buffer (i.e. what we
                    // were attempting to parse with `top_level_value`.)
                    // TODO: We probably don't want to surface the nom error (`e`) directly, but it's
                    //       useful for debugging.
                    return decoding_error(format!(
                        "Parsing error occurred near line {}: '{}': '{}'",
                        self.buffer.lines_loaded(),
                        self.buffer.remaining_text(),
                        e
                    ));
                }
            };
        };

        Ok(Some(item))
    }

    // Parses the contents of the text buffer again with the knowledge that we're at the end of the
    // input stream. This allows us to resolve a number of ambiguous cases.
    // For a detailed description of the problem that this addresses, please see:
    // https://github.com/amzn/ion-rust/issues/318
    // This method should only be called when the reader is at the top level. An EOF at any other
    // depth is an error.
    fn parse_stream_item_at_eof(
        &mut self,
    ) -> IonResult<Option<(Vec<OwnedSymbolToken>, TextStreamItem)>> {
        // An arbitrary, cheap-to-parse Ion value that we append to the buffer when its contents at
        // EOF are ambiguous.
        const SENTINEL_ION_TEXT: &str = "\n0\n";
        // Make a note of the buffer's length; we're about to modify it.
        let original_length = self.buffer.remaining_text().len();
        // Append our sentinel value to the end of the input buffer.
        self.buffer.inner().push_str(SENTINEL_ION_TEXT);
        // If the buffer contained a value, the newline will indicate that the contents of the
        // buffer were complete. For example:
        // * the integer `7` becomes `7\n`; it wasn't the first digit in a truncated `755`.
        // * the boolean `true` becomes `false\n`; it wasn't actually half of the
        //   identifier `falseTeeth`.
        //
        // If the buffer contained a value that's written in segments, the extra `0` will indicate
        // that no more segments are coming. For example:
        // * `foo::bar` becomes `foo::bar\n0\n`; the parser can see that 'bar' is a value, not
        //    another annotation in the sequence.
        // * `'''long-form string'''` becomes `'''long-form string'''\n0\n`; the parser can see that
        //   there aren't any more long-form string segments in the sequence.
        //
        // Attempt to parse the updated buffer.
        let item = match top_level_stream_item(self.buffer.remaining_text()) {
            Ok(("\n", (annotations, TextStreamItem::Integer(0)))) if annotations.len() == 0 => {
                // We found the unannotated zero that we appended to the end of the buffer.
                // The "\n" in this pattern is the unparsed text left in the buffer,
                // which indicates that our 0 was parsed.
                Ok(None)
            }
            Ok((_remaining_text, (annotations, item))) => {
                // We found something else. The zero is still in the buffer; we can leave it there.
                // The reader's `is_eof` flag has been set, so the text buffer will never be used
                // again. Return the value we found.
                Ok(Some((annotations, item)))
            }
            Err(Incomplete(_needed)) => {
                decoding_error(format!(
                    "Unexpected end of input on line {}: '{}'",
                    self.buffer.lines_loaded(),
                    &self.buffer.remaining_text()[..original_length] // Don't show the extra `\n0\n`
                ))
            }
            Err(e) => {
                decoding_error(format!(
                    "Parsing error occurred near line {}: '{}': '{}'",
                    self.buffer.lines_loaded(),
                    &self.buffer.remaining_text()[..original_length], // Don't show the extra `\n0\n`
                    e
                ))
            }
        };

        // If we didn't consume the sentinel value, remove the sentinel value from the buffer.
        // Doing so makes this method idempotent.
        if self.buffer.remaining_text().ends_with(SENTINEL_ION_TEXT) {
            let length = self.buffer.remaining_text().len();
            self.buffer
                .inner()
                .truncate(length - SENTINEL_ION_TEXT.len());
        }

        item
    }
}

#[cfg(test)]
mod reader_tests {
    use crate::result::IonResult;
    use crate::text::reader::TextReader;
    use crate::text::TextStreamItem;
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;
    use crate::value::owned::{local_sid_token, text_token};
    use crate::IonType;

    #[test]
    fn test_text_read_multiple_top_level_values() {
        let ion_data = r#"
            null
            true
            5
            5e0
            5.5
            2021-09-25T
            foo
            "hello"
            {foo: bar}
            ["foo", "bar"]
            ('''foo''')
        "#;
        let mut reader = TextReader::new(ion_data);
        let mut next_is = |expected| {
            // In this test, none of the stream values are annotated.
            // Compare the stream item and ignore the annotations.
            assert_eq!(reader.next().unwrap().unwrap().1, expected);
        };
        next_is(TextStreamItem::Null(IonType::Null));
        next_is(TextStreamItem::Boolean(true));
        next_is(TextStreamItem::Integer(5));
        next_is(TextStreamItem::Float(5.0f64));
        next_is(TextStreamItem::Decimal(Decimal::new(55, -1)));
        next_is(TextStreamItem::Timestamp(
            Timestamp::with_ymd(2021, 9, 25).build().unwrap(),
        ));
        next_is(TextStreamItem::Symbol(text_token("foo")));
        next_is(TextStreamItem::String("hello".to_string()));

        // ===== CONTAINERS =====
        // This part of the test is a bit clunky because the reader does not yet support
        // step_in() and step_out(). We're calling functions like `next_struct_item()` that will
        // eventually be private helper methods.
        // TODO: Replace these calls with step_in(), step_out(), field_name(), and next().
        next_is(TextStreamItem::StructStart);
        assert_eq!(
            reader.next_struct_field_name().unwrap().unwrap(),
            text_token("foo")
        );
        assert_eq!(
            reader.next_struct_item().unwrap().1,
            TextStreamItem::Symbol(text_token("bar"))
        );
        // The struct only has one field, so asking for the next field name returns `None`.
        assert_eq!(reader.next_struct_field_name(), Ok(None));

        assert_eq!(reader.next().unwrap().unwrap().1, TextStreamItem::ListStart);
        assert_eq!(
            reader.next_list_item().unwrap().unwrap().1,
            TextStreamItem::String(String::from("foo"))
        );
        assert_eq!(
            reader.next_list_item().unwrap().unwrap().1,
            TextStreamItem::String(String::from("bar"))
        );
        // There are only two values in the list, so asking for the next one returns `None`
        assert_eq!(reader.next_list_item(), Ok(None));

        assert_eq!(
            reader.next().unwrap().unwrap().1,
            TextStreamItem::SExpressionStart
        );
        assert_eq!(
            reader.next_s_expression_item().unwrap().unwrap().1,
            TextStreamItem::String(String::from("foo"))
        );
        // There's only one value in the list, so asking for the next one returns `None`
        assert_eq!(reader.next_s_expression_item(), Ok(None));

        // There are no more top level values.
        assert_eq!(reader.next_top_level_item(), Ok(None));

        // Asking for more still results in `None`
        assert_eq!(reader.next_top_level_item(), Ok(None));
    }

    #[test]
    fn test_read_multiple_top_level_values_with_comments() {
        let ion_data = r#"
            /*
                Arrokoth is a trans-Neptunian object in the Kuiper belt.
                It is a contact binary composed of two plenetesimals joined
                along their major axes.
            */
            "(486958) 2014 MU69" // Original designation
            2014-06-26T // Date of discovery
            km::36 // width
        "#;

        let mut reader = TextReader::new(ion_data);
        let mut next_is = |expected_annotations, expected_item| {
            let (annotations, item) = reader.next().unwrap().unwrap();
            assert_eq!(annotations, expected_annotations);
            assert_eq!(item, expected_item);
        };

        next_is(
            vec![],
            TextStreamItem::String(String::from("(486958) 2014 MU69")),
        );
        next_is(
            vec![],
            TextStreamItem::Timestamp(Timestamp::with_ymd(2014, 6, 26).build().unwrap()),
        );
        next_is(vec![text_token("km")], TextStreamItem::Integer(36));
    }

    #[test]
    fn test_text_read_multiple_annotated_top_level_values() {
        let ion_data = r#"
            mercury::null
            venus::'earth'::true
            $17::mars::5
            jupiter::5e0
            'saturn'::5.5
            $100::$200::$300::2021-09-25T
            'uranus'::foo
            neptune::"hello"
            $55::{foo: bar}
            pluto::[1, 2, 3]
            haumea::makemake::eris::ceres::(++ -- &&&&&)
        "#;
        let mut reader = TextReader::new(ion_data);
        let mut next_is = |expected_annotations, expected_item| {
            let (annotations, item) = reader.next().unwrap().unwrap();
            assert_eq!(annotations, expected_annotations);
            assert_eq!(item, expected_item);
        };
        next_is(
            vec![text_token("mercury")],
            TextStreamItem::Null(IonType::Null),
        );
        next_is(
            vec![text_token("venus"), text_token("earth")],
            TextStreamItem::Boolean(true),
        );
        next_is(
            vec![local_sid_token(17), text_token("mars")],
            TextStreamItem::Integer(5),
        );
        next_is(vec![text_token("jupiter")], TextStreamItem::Float(5.0f64));
        next_is(
            vec![text_token("saturn")],
            TextStreamItem::Decimal(Decimal::new(55, -1)),
        );
        next_is(
            vec![
                local_sid_token(100),
                local_sid_token(200),
                local_sid_token(300),
            ],
            TextStreamItem::Timestamp(Timestamp::with_ymd(2021, 9, 25).build().unwrap()),
        );
        next_is(
            vec![text_token("uranus")],
            TextStreamItem::Symbol(text_token("foo")),
        );
        next_is(
            vec![text_token("neptune")],
            TextStreamItem::String("hello".to_string()),
        );

        // ===== CONTAINERS =====
        // This part of the test is a bit clunky because the reader does not yet support
        // step_in() and step_out(). We're calling functions like `next_struct_item()` that will
        // eventually be private helper methods.
        // TODO: Replace these calls with step_in(), step_out(), field_name(), and next().
        assert_eq!(
            reader.next().unwrap().unwrap(),
            (vec![local_sid_token(55)], TextStreamItem::StructStart)
        );
        assert_eq!(
            reader.next_struct_field_name().unwrap().unwrap(),
            text_token("foo")
        );
        assert_eq!(
            reader.next_struct_item().unwrap().1,
            TextStreamItem::Symbol(text_token("bar"))
        );
        // There's only one field in the struct, so asking for another field name returns `None`
        assert_eq!(reader.next_struct_field_name(), Ok(None));

        assert_eq!(
            reader.next().unwrap().unwrap(),
            (vec![text_token("pluto")], TextStreamItem::ListStart)
        );
        assert_eq!(
            reader.next_list_item().unwrap().unwrap().1,
            TextStreamItem::Integer(1)
        );
        assert_eq!(
            reader.next_list_item().unwrap().unwrap().1,
            TextStreamItem::Integer(2)
        );
        assert_eq!(
            reader.next_list_item().unwrap().unwrap().1,
            TextStreamItem::Integer(3)
        );
        // There are only three values in the list, so asking for the next one returns `None`
        assert_eq!(reader.next_list_item(), Ok(None));

        assert_eq!(
            reader.next().unwrap().unwrap(),
            (
                vec![
                    text_token("haumea"),
                    text_token("makemake"),
                    text_token("eris"),
                    text_token("ceres"),
                ],
                TextStreamItem::SExpressionStart
            )
        );

        assert_eq!(
            reader.next_s_expression_item().unwrap().unwrap().1,
            TextStreamItem::Symbol(text_token("++"))
        );
        assert_eq!(
            reader.next_s_expression_item().unwrap().unwrap().1,
            TextStreamItem::Symbol(text_token("--"))
        );
        assert_eq!(
            reader.next_s_expression_item().unwrap().unwrap().1,
            TextStreamItem::Symbol(text_token("&&&&&"))
        );
        // There's only three values in the s-expression, so asking for the next one returns `None`
        assert_eq!(reader.next_s_expression_item(), Ok(None));

        // There are no more top level values.
        assert_eq!(reader.next_top_level_item(), Ok(None));

        // Asking for more still results in `None`
        assert_eq!(reader.next_top_level_item(), Ok(None));
    }

    fn top_level_value_test(ion_text: &str, expected: TextStreamItem) {
        let mut reader = TextReader::new(ion_text);
        let item = reader.next().unwrap().unwrap().1;
        assert_eq!(item, expected);
    }

    #[test]
    fn test_read_single_top_level_values() -> IonResult<()> {
        let tlv = top_level_value_test;
        tlv(" null ", TextStreamItem::Null(IonType::Null));
        tlv(" null.string ", TextStreamItem::Null(IonType::String));
        tlv(" true ", TextStreamItem::Boolean(true));
        tlv(" false ", TextStreamItem::Boolean(false));
        tlv(" 738 ", TextStreamItem::Integer(738));
        tlv(" 2.5e0 ", TextStreamItem::Float(2.5));
        tlv(" 2.5 ", TextStreamItem::Decimal(Decimal::new(25, -1)));
        tlv(
            " 2007-07-12T ",
            TextStreamItem::Timestamp(Timestamp::with_ymd(2007, 7, 12).build()?),
        );
        tlv(" foo ", TextStreamItem::Symbol(text_token("foo")));
        tlv(" \"hi!\" ", TextStreamItem::String("hi!".to_owned()));
        tlv(
            " {{ZW5jb2RlZA==}} ",
            TextStreamItem::Blob(Vec::from("encoded".as_bytes())),
        );
        tlv(
            " {{\"hello\"}} ",
            TextStreamItem::Clob(Vec::from("hello".as_bytes())),
        );
        Ok(())
    }
}
