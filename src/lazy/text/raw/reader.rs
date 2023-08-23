use crate::lazy::decoder::LazyRawReader;
use crate::lazy::encoding::TextEncoding;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::AddContext;
use crate::result::IonFailure;
use crate::IonResult;

/// A text Ion 1.0 reader that yields [`RawStreamItem`]s representing the top level values found
/// in the provided input stream.
pub struct LazyRawTextReader<'data> {
    // The current view of the data we're reading from.
    buffer: TextBufferView<'data>,
    // Each time something is parsed from the buffer successfully, the caller will mark the number
    // of bytes that may be skipped the next time the reader advances.
    bytes_to_skip: usize,
}

impl<'data> LazyRawTextReader<'data> {
    /// Constructs a `LazyRawTextReader` positioned at the beginning of the provided input stream.
    pub fn new(data: &'data [u8]) -> LazyRawTextReader<'data> {
        Self::new_with_offset(data, 0)
    }

    /// Constructs a `LazyRawTextReader` positioned at the beginning of the provided input stream.
    /// The provided input stream is itself a slice starting `offset` bytes from the beginning
    /// of a larger data stream. This offset is used for reporting the absolute (stream-level)
    /// position of values encountered in `data`.
    fn new_with_offset(data: &'data [u8], offset: usize) -> LazyRawTextReader<'data> {
        LazyRawTextReader {
            buffer: TextBufferView::new_with_offset(data, offset),
            bytes_to_skip: 0,
        }
    }

    pub fn next<'top>(&'top mut self) -> IonResult<RawStreamItem<'data, TextEncoding>>
    where
        'data: 'top,
    {
        let buffer = self.buffer;
        if buffer.is_empty() {
            return IonResult::incomplete("reading a top-level value", buffer.offset());
        }
        let (buffer_after_whitespace, _whitespace) = buffer
            .match_optional_comments_and_whitespace()
            .with_context(
                "skipping comments and whitespace between top-level values",
                buffer,
            )?;
        let (remaining, matched) = buffer_after_whitespace
            .match_top_level()
            .with_context("reading a top-level value", buffer_after_whitespace)?;
        // If we successfully moved to the next value, store the remaining buffer view
        self.buffer = remaining;
        Ok(matched)
    }
}

impl<'data> LazyRawReader<'data, TextEncoding> for LazyRawTextReader<'data> {
    fn new(data: &'data [u8]) -> Self {
        LazyRawTextReader::new(data)
    }

    fn next<'a>(&'a mut self) -> IonResult<RawStreamItem<'data, TextEncoding>> {
        self.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::decoder::LazyRawValue;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::{IonType, RawSymbolTokenRef};

    #[test]
    fn test_top_level() -> IonResult<()> {
        let mut data = String::new();
        data.push_str(
            r#"
        /*
            This test demonstrates lazily reading top-level values
            of various Ion types. The values are interspersed with
            different kinds of comments and whitespace.
        */
        
        // Typed nulls
        
        null
        null.bool
        null.int
            
        // Booleans

        false
        true
        
        // Integers

        500
        0x20
        0b0101
        
        // Floats

        +inf
        -inf
        nan
        3.6e0
        2.5e008
        -318e-2
            
        // Strings

        "Hello!"
        "foo bar baz"
        "😎😎😎"
        "lol\n\r\0wat"                     // Single-character escapes
        "\x48ello, \x77orld!"              // \x 2-digit hex escape
        "\u0048ello, \u0077orld!"          // \u 4-digit hex escape
        "\U00000048ello, \U00000077orld!"  // \U 8-digit hex escape

        "#,
        );
        // Escaped newlines are discarded
        data.push_str("\"Hello,\\\n world!\"");

        data.push_str(
            r#"
        // Symbols
        
        'foo'
        'Hello, world!'
        '😎😎😎'
        
        firstName
        date_of_birth
        $variable
        
        $0
        $10
        $733
        
        [
            // First item
            1,
            // Second item
            2 /*comment before comma*/,
            // Third item
            3
        ]
        
        "#,
        );

        fn expect_next<'data>(
            reader: &mut LazyRawTextReader<'data>,
            expected: RawValueRef<'data, TextEncoding>,
        ) {
            let lazy_value = reader
                .next()
                .expect("advancing the reader failed")
                .expect_value()
                .expect("expected a value");
            assert_eq!(
                matches!(expected, RawValueRef::Null(_)),
                lazy_value.is_null()
            );
            let value_ref = lazy_value.read().expect("reading failed");
            assert_eq!(value_ref, expected, "{:?} != {:?}", value_ref, expected);
        }

        let reader = &mut LazyRawTextReader::new(data.as_bytes());

        // null
        expect_next(reader, RawValueRef::Null(IonType::Null));
        // null.bool
        expect_next(reader, RawValueRef::Null(IonType::Bool));
        // null.int
        expect_next(reader, RawValueRef::Null(IonType::Int));

        // false
        expect_next(reader, RawValueRef::Bool(false));
        // true
        expect_next(reader, RawValueRef::Bool(true));

        // 500
        expect_next(reader, RawValueRef::Int(500.into()));
        // 0x20
        expect_next(reader, RawValueRef::Int(0x20.into()));
        // 0b0101
        expect_next(reader, RawValueRef::Int(0b0101.into()));

        // +inf
        expect_next(reader, RawValueRef::Float(f64::INFINITY));
        // -inf
        expect_next(reader, RawValueRef::Float(f64::NEG_INFINITY));
        // nan
        // NaN != NaN, so we have to spell this test out a bit more
        assert!(reader
            .next()?
            .expect_value()?
            .read()?
            .expect_float()?
            .is_nan());
        // 3.6e0
        expect_next(reader, RawValueRef::Float(3.6f64));
        // 2.25e23
        expect_next(reader, RawValueRef::Float(2.5f64 * 10f64.powi(8)));
        // -3.18
        expect_next(reader, RawValueRef::Float(-3.18f64));
        // "Hello"
        expect_next(reader, RawValueRef::String("Hello!".into()));
        // "foo bar baz"
        expect_next(reader, RawValueRef::String("foo bar baz".into()));
        // "😎😎😎"
        expect_next(reader, RawValueRef::String("😎😎😎".into()));
        // "lol\n\r\0wat"
        expect_next(reader, RawValueRef::String("lol\n\r\0wat".into()));
        // "\x48ello, \x77orld!"
        expect_next(reader, RawValueRef::String("Hello, world!".into()));
        // "\u0048ello, \u0077orld!"
        expect_next(reader, RawValueRef::String("Hello, world!".into()));
        // "\U00000048ello, \U00000077orld!"
        expect_next(reader, RawValueRef::String("Hello, world!".into()));
        // "\"Hello,\\\n world!\" "
        expect_next(reader, RawValueRef::String("Hello, world!".into()));
        // 'foo'
        expect_next(
            reader,
            RawValueRef::Symbol(RawSymbolTokenRef::Text("foo".into())),
        );
        expect_next(
            reader,
            RawValueRef::Symbol(RawSymbolTokenRef::Text("Hello, world!".into())),
        );
        expect_next(
            reader,
            RawValueRef::Symbol(RawSymbolTokenRef::Text("😎😎😎".into())),
        );
        // firstName
        expect_next(
            reader,
            RawValueRef::Symbol(RawSymbolTokenRef::Text("firstName".into())),
        );
        // date_of_birth
        expect_next(
            reader,
            RawValueRef::Symbol(RawSymbolTokenRef::Text("date_of_birth".into())),
        );
        // $variable
        expect_next(
            reader,
            RawValueRef::Symbol(RawSymbolTokenRef::Text("$variable".into())),
        );
        // $0
        expect_next(reader, RawValueRef::Symbol(RawSymbolTokenRef::SymbolId(0)));
        // $10
        expect_next(reader, RawValueRef::Symbol(RawSymbolTokenRef::SymbolId(10)));
        // $733
        expect_next(
            reader,
            RawValueRef::Symbol(RawSymbolTokenRef::SymbolId(733)),
        );

        let list = reader.next()?.expect_value()?.read()?.expect_list()?;
        let mut sum = 0;
        for value in &list {
            sum += value?.read()?.expect_i64()?;
        }
        assert_eq!(sum, 6);

        Ok(())
    }
}
