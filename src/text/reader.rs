use nom::Err::Incomplete;

use crate::result::{decoding_error, IonResult};
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
    fn next(&mut self) -> IonResult<(Vec<OwnedSymbolToken>, TextStreamItem)> {
        if self.is_eof {
            return Ok((Vec::new(), TextStreamItem::EndOfStream));
        }

        let (annotations, stream_item) = 'parse: loop {
            // Note the number of bytes currently in the text buffer
            let length_before_parse = self.buffer.remaining_text().len();
            // Invoke the top_level_value() parser; this will attempt to recognize the next item
            // in the stream and return a &str slice containing the remaining, not-yet-parsed text.
            match top_level_stream_item(self.buffer.remaining_text()) {
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
                        return self.parse_stream_item_at_eof();
                    }
                    continue;
                }
                Ok((remaining_text, (annotations, item))) => {
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
                    break 'parse (annotations, item);
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

        Ok((annotations, stream_item))
    }

    // Parses the contents of the text buffer again with the knowledge that we're at the end of the
    // input stream. This allows us to resolve a number of ambiguous cases.
    // For a detailed description of the problem that this addresses, please see:
    // https://github.com/amzn/ion-rust/issues/318
    fn parse_stream_item_at_eof(&mut self) -> IonResult<(Vec<OwnedSymbolToken>, TextStreamItem)> {
        // Get a reference to the buffer's backing String. We're at EOF, so we'll never use this
        // text buffer again; we can modify it without risk. Re-using this buffer avoids allocating
        // a new string for EOF, which is guaranteed to happen once per stream.
        let buffer = self.buffer.inner();
        // Make a note of the buffer's length; we're about to modify it.
        let original_length = buffer.len();
        // Append a newline and an arbitrary value (here: 0) to the buffer.
        buffer.push_str("\n0\n");
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
        match top_level_stream_item(self.buffer.remaining_text()) {
            Ok(("\n", (annotations, TextStreamItem::Integer(0)))) if annotations.len() == 0 => {
                // We found the unannotated zero that we appended to the end of the buffer.
                // The "\n" in this pattern is the unparsed text left in the buffer,
                // which indicates that our 0 was parsed.
                Ok((Vec::new(), TextStreamItem::EndOfStream))
            }
            Ok((_remaining_text, (annotations, item))) => {
                // We found something else. The zero is still in the buffer; we can leave it there.
                // The reader's `is_eof` flag has been set, so the text buffer will never be used
                // again. Return the value we found.
                Ok((annotations, item))
            }
            Err(Incomplete(_needed)) => {
                return decoding_error(format!(
                    "Unexpected end of input on line {}: '{}'",
                    self.buffer.lines_loaded(),
                    &self.buffer.remaining_text()[..original_length] // Don't show the extra `\n0\n`
                ));
            }
            Err(e) => {
                return decoding_error(format!(
                    "Parsing error occurred near line {}: '{}': '{}'",
                    self.buffer.lines_loaded(),
                    &self.buffer.remaining_text()[..original_length], // Don't show the extra `\n0\n`
                    e
                ));
            }
        }
    }
}

#[cfg(test)]
mod reader_tests {
    use crate::result::IonResult;
    use crate::text::parsers::top_level::stream_item;
    use crate::text::parsers::unit_test_support::parse_unwrap;
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
            {}
            []
            ()
        "#;
        let mut reader = TextReader::new(ion_data);
        let mut next_is = |expected| {
            // In this test, none of the stream values are annotated.
            // Compare the stream item and ignore the annotations.
            assert_eq!(reader.next().unwrap().1, expected);
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
        next_is(TextStreamItem::StructStart);
        next_is(TextStreamItem::StructEnd);
        next_is(TextStreamItem::ListStart);
        next_is(TextStreamItem::ListEnd);
        next_is(TextStreamItem::SExpressionStart);
        next_is(TextStreamItem::SExpressionEnd);
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
            $55::{}
            pluto::[]
            haumea::makemake::eris::ceres::()
        "#;
        let mut reader = TextReader::new(ion_data);
        let mut next_is = |expected_annotations, expected_item| {
            let (annotations, item) = reader.next().unwrap();
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
        next_is(vec![local_sid_token(55)], TextStreamItem::StructStart);
        next_is(vec![], TextStreamItem::StructEnd);
        next_is(vec![text_token("pluto")], TextStreamItem::ListStart);
        next_is(vec![], TextStreamItem::ListEnd);
        next_is(
            vec![
                text_token("haumea"),
                text_token("makemake"),
                text_token("eris"),
                text_token("ceres"),
            ],
            TextStreamItem::SExpressionStart,
        );
        next_is(vec![], TextStreamItem::SExpressionEnd);
        // No more values in the stream
        next_is(vec![], TextStreamItem::EndOfStream);
        // Continuing to ask for the next value continues to result in EndOfStream
        next_is(vec![], TextStreamItem::EndOfStream);
        next_is(vec![], TextStreamItem::EndOfStream);
    }

    fn top_level_value_test(ion_text: &str, expected: TextStreamItem) {
        let mut reader = TextReader::new(ion_text);
        let item = reader.next().unwrap().1;
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

    #[test]
    fn test_detect_stream_item_types() {
        let expect_option_type = |text: &str, expected: Option<IonType>| {
            let value = parse_unwrap(stream_item, text);
            assert_eq!(expected, value.ion_type());
        };

        let expect_type = |text: &str, expected_ion_type: IonType| {
            expect_option_type(text, Some(expected_ion_type))
        };

        let expect_no_type = |text: &str| expect_option_type(text, None);

        expect_type("null ", IonType::Null);
        expect_type("null.timestamp ", IonType::Timestamp);
        expect_type("null.list ", IonType::List);
        expect_type("true ", IonType::Boolean);
        expect_type("false ", IonType::Boolean);
        expect_type("5 ", IonType::Integer);
        expect_type("-5 ", IonType::Integer);
        expect_type("5.0 ", IonType::Decimal);
        expect_type("-5.0 ", IonType::Decimal);
        expect_type("5.0d0 ", IonType::Decimal);
        expect_type("-5.0d0 ", IonType::Decimal);
        expect_type("5.0e0 ", IonType::Float);
        expect_type("-5.0e1_024 ", IonType::Float);
        expect_type("\"foo\"", IonType::String);
        expect_type("'''foo''' 1", IonType::String);
        expect_type("foo ", IonType::Symbol);
        expect_type("'foo bar baz' ", IonType::Symbol);
        expect_type("2021T ", IonType::Timestamp);
        expect_type("2021-02T ", IonType::Timestamp);
        expect_type("2021-02-08T ", IonType::Timestamp);
        expect_type("2021-02-08T12:30Z ", IonType::Timestamp);
        expect_type("2021-02-08T12:30:02-00:00 ", IonType::Timestamp);
        expect_type("2021-02-08T12:30:02.111-00:00 ", IonType::Timestamp);
        expect_type("{{\"hello\"}}", IonType::Clob);

        // End of...
        expect_no_type("} "); // struct
        expect_no_type("] "); // list
        expect_no_type(") "); // s-expression
    }
}
