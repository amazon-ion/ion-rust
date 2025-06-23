#![allow(non_camel_case_types)]

use crate::lazy::any_encoding::IonEncoding;
use crate::lazy::decoder::LazyRawReader;
use crate::lazy::encoding::TextEncoding_1_0;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem, RawStreamItem};
use crate::lazy::streaming_raw_reader::RawReaderState;
use crate::lazy::text::buffer::TextBuffer;
use crate::lazy::text::parse_result::WithContext;
use crate::{Encoding, IonResult};

/// A text Ion 1.0 reader that yields [`LazyRawStreamItem`]s representing the top level values found
/// in the provided input stream.
pub struct LazyRawTextReader_1_0<'data> {
    input: TextBuffer<'data>,
}

impl<'data> LazyRawTextReader_1_0<'data> {
    /// Constructs a `LazyRawTextReader` positioned at the beginning of the provided input stream.
    pub fn new(
        context: EncodingContextRef<'data>,
        data: &'data [u8],
        is_final_data: bool,
    ) -> LazyRawTextReader_1_0<'data> {
        Self::new_with_offset(context, data, 0, is_final_data)
    }

    /// Constructs a `LazyRawTextReader` positioned at the beginning of the provided input stream.
    /// The provided input stream is itself a slice starting `offset` bytes from the beginning
    /// of a larger data stream. This offset is used for reporting the absolute (stream-level)
    /// position of values encountered in `data`.
    fn new_with_offset(
        context: EncodingContextRef<'data>,
        data: &'data [u8],
        offset: usize,
        is_final_data: bool,
    ) -> LazyRawTextReader_1_0<'data> {
        let input = TextBuffer::with_offset(context, offset, data, is_final_data);
        LazyRawTextReader_1_0 { input }
    }

    pub fn next(&mut self) -> IonResult<LazyRawStreamItem<'data, TextEncoding_1_0>> {
        let _whitespace = self
            .input
            .match_optional_comments_and_whitespace()
            .with_context("reading whitespace/comments at the top level", self.input)?;
        if self.input.is_empty() {
            return Ok(RawStreamItem::EndOfStream(EndPosition::new(
                TextEncoding_1_0.encoding(),
                self.input.offset(),
            )));
        }
        // Consume any trailing whitespace that followed this item. Doing this allows us to check
        // whether this was the last item in the buffer by testing `buffer.is_empty()` afterward.
        let matched_item = self
            .input
            .match_top_level_item_1_0()
            .with_context("reading a top-level value", self.input)?;

        let _trailing_ws = self
            .input
            .match_optional_comments_and_whitespace()
            .with_context("reading trailing top-level whitespace/comments", self.input)?;
        Ok(matched_item)
    }

    pub fn context(&self) -> EncodingContextRef<'data> {
        self.input.context()
    }
}

impl<'data> LazyRawReader<'data, TextEncoding_1_0> for LazyRawTextReader_1_0<'data> {
    fn new(context: EncodingContextRef<'data>, data: &'data [u8], is_final_data: bool) -> Self {
        LazyRawTextReader_1_0::new(context, data, is_final_data)
    }

    fn resume(context: EncodingContextRef<'data>, saved_state: RawReaderState<'data>) -> Self {
        LazyRawTextReader_1_0 {
            input: TextBuffer::with_offset(
                context,
                saved_state.offset(),
                saved_state.data(),
                saved_state.is_final_data(),
            ),
        }
    }

    fn save_state(&self) -> RawReaderState<'data> {
        RawReaderState::new(
            self.input.bytes(),
            self.position(),
            self.input.is_final_data(),
            self.encoding(),
        )
    }

    fn next(&mut self) -> IonResult<LazyRawStreamItem<'data, TextEncoding_1_0>> {
        self.next()
    }

    fn position(&self) -> usize {
        self.input.offset()
    }

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Text_1_0
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::decoder::{HasRange, HasSpan, LazyRawFieldName, LazyRawStruct, LazyRawValue};
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::raw_symbol_ref::AsRawSymbolRef;
    use crate::{Decimal, IonType, RawSymbolRef, RawVersionMarker, Timestamp};

    use super::*;

    struct TestReader<'data> {
        reader: LazyRawTextReader_1_0<'data>,
    }

    impl<'data> TestReader<'data> {
        fn next(&mut self) -> IonResult<LazyRawStreamItem<'data, TextEncoding_1_0>> {
            self.reader.next()
        }
        fn expect_next(&mut self, expected: RawValueRef<'data, TextEncoding_1_0>) {
            let TestReader { reader, .. } = self;
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
    }

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
        
        // Ion version marker
        
        $ion_1_0
        
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
        
        // Decimals
        1.5
        3.14159
        -6d+5
        6d-5

        // Timestamps
        
        2023T
        2023-08-13T
        2023-08-13T21:45:30.993-05:00
            
        // Strings

        '''Long string without escapes'''

        "Hello!"
        
        '''Long string with escaped \''' delimiter''' 

        "foo bar baz"
        "😎😎😎"
        "lol\n\r\0wat"                     // Single-character escapes
        "\x48ello, \x77orld!"              // \x 2-digit hex escape
        "\u0048ello, \u0077orld!"          // \u 4-digit hex escape
        "\U00000048ello, \U00000077orld!"  // \U 8-digit hex escape
        
        '''Mercury '''
        '''Venus '''
        '''Earth '''
        '''Mars '''
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
        
        // Blobs
        {{cmF6emxlIGRhenpsZSByb290IGJlZXI=}}
        
        // Clobs
        {{"foobarbaz"}}
        {{
            '''foo'''
            '''bar'''
            '''baz'''
        }}
        
        // List
        [
            // First item
            1,
            // Second item
            2 /*comment before comma*/,
            // Third item
            3, // Final trailing comma
        ]
        

        // S-Expression
        (
            foo++
            2
            3
        )

        // Struct
        {
            // Identifier 
            foo: 100,
            // Quoted symbol
            'bar': 200,
            // Short-form string
            "baz": mars::earth::300
        }
        
        foo::'bar'::  baz :: 42

        "#,
        );

        let encoding_context = EncodingContext::empty();
        let reader = &mut TestReader {
            reader: LazyRawTextReader_1_0::new(encoding_context.get_ref(), data.as_bytes(), true),
        };

        assert_eq!(reader.next()?.expect_ivm()?.major_minor(), (1, 0));

        // null
        reader.expect_next(RawValueRef::Null(IonType::Null));
        // null.bool
        reader.expect_next(RawValueRef::Null(IonType::Bool));
        // null.int
        reader.expect_next(RawValueRef::Null(IonType::Int));
        // false
        reader.expect_next(RawValueRef::Bool(false));
        // true
        reader.expect_next(RawValueRef::Bool(true));

        // 500
        reader.expect_next(RawValueRef::Int(500.into()));
        // 0x20
        reader.expect_next(RawValueRef::Int(0x20.into()));
        // 0b0101
        reader.expect_next(RawValueRef::Int(0b0101.into()));

        // +inf
        reader.expect_next(RawValueRef::Float(f64::INFINITY));
        // -inf
        reader.expect_next(RawValueRef::Float(f64::NEG_INFINITY));
        // nan
        // NaN != NaN, so we have to spell this test out a bit more
        assert!(reader
            .next()?
            .expect_value()?
            .read()?
            .expect_float()?
            .is_nan());
        // 3.6e0
        reader.expect_next(RawValueRef::Float(3.6f64));
        // 2.25e23
        reader.expect_next(RawValueRef::Float(2.5f64 * 10f64.powi(8)));
        // -3.18
        reader.expect_next(RawValueRef::Float(-3.18f64));
        //         1.5
        reader.expect_next(RawValueRef::Decimal(Decimal::new(15, -1)));
        //         3.14159
        reader.expect_next(RawValueRef::Decimal(Decimal::new(314159, -5)));
        //         -6d+5
        reader.expect_next(RawValueRef::Decimal(Decimal::new(-6, 5)));
        //         6d-5
        reader.expect_next(RawValueRef::Decimal(Decimal::new(6, -5)));
        // 2023T
        reader.expect_next(RawValueRef::Timestamp(Timestamp::with_year(2023).build()?));
        // 2023-08-13T
        reader.expect_next(RawValueRef::Timestamp(
            Timestamp::with_ymd(2023, 8, 13).build()?,
        ));
        // 2023-08-13T21:45:30.993-05:00
        reader.expect_next(RawValueRef::Timestamp(
            Timestamp::with_ymd(2023, 8, 13)
                .with_hms(21, 45, 30)
                .with_milliseconds(993)
                .with_offset(-300)
                .build()?,
        ));

        // '''Long string without escapes'''
        reader.expect_next(RawValueRef::String("Long string without escapes".into()));
        // "Hello"
        reader.expect_next(RawValueRef::String("Hello!".into()));
        // '''Long string with escaped \''' delimiter'''
        reader.expect_next(RawValueRef::String(
            "Long string with escaped ''' delimiter".into(),
        ));
        // "foo bar baz"
        reader.expect_next(RawValueRef::String("foo bar baz".into()));
        // "😎😎😎"
        reader.expect_next(RawValueRef::String("😎😎😎".into()));
        // "lol\n\r\0wat"
        reader.expect_next(RawValueRef::String("lol\n\r\0wat".into()));
        // "\x48ello, \x77orld!"
        reader.expect_next(RawValueRef::String("Hello, world!".into()));
        // "\u0048ello, \u0077orld!"
        reader.expect_next(RawValueRef::String("Hello, world!".into()));
        // "\U00000048ello, \U00000077orld!"
        reader.expect_next(RawValueRef::String("Hello, world!".into()));
        reader.expect_next(RawValueRef::String("Mercury Venus Earth Mars ".into()));
        // "\"Hello,\\\n world!\" "
        reader.expect_next(RawValueRef::String("Hello, world!".into()));
        // 'foo'
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::Text("foo")));
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::Text("Hello, world!")));
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::Text("😎😎😎")));
        // firstName
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::Text("firstName")));
        // date_of_birth
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::Text("date_of_birth")));
        // $variable
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::Text("$variable")));
        // $0
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::SymbolId(0)));
        // $10
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::SymbolId(10)));
        // $733
        reader.expect_next(RawValueRef::Symbol(RawSymbolRef::SymbolId(733)));

        // {{cmF6emxlIGRhenpsZSByb290IGJlZXI=}}
        reader.expect_next(RawValueRef::Blob("razzle dazzle root beer".into()));

        // {{"foobarbaz"}}
        reader.expect_next(RawValueRef::Clob("foobarbaz".into()));
        // {{'''foo''' '''bar''' '''baz'''}}
        reader.expect_next(RawValueRef::Clob("foobarbaz".into()));

        // [1, 2, 3]
        let list = reader.next()?.expect_value()?.read()?.expect_list()?;
        let mut sum = 0;
        for value in &list {
            sum += value?.expect_value()?.read()?.expect_i64()?;
        }
        assert_eq!(sum, 6);
        // (foo++ 1 2)
        let sexp = reader.next()?.expect_value()?.read()?.expect_sexp()?;
        let mut sexp_elements = sexp.iter();
        assert_eq!(
            sexp_elements.next().unwrap()?.expect_value()?.read()?,
            RawValueRef::Symbol("foo".into())
        );
        assert_eq!(
            sexp_elements.next().unwrap()?.expect_value()?.read()?,
            RawValueRef::Symbol("++".into())
        );
        assert_eq!(
            sexp_elements.next().unwrap()?.expect_value()?.read()?,
            RawValueRef::Int(2.into())
        );
        assert_eq!(
            sexp_elements.next().unwrap()?.expect_value()?.read()?,
            RawValueRef::Int(3.into())
        );

        // {foo: 100, bar: 200, baz: 300}
        let item = reader.next()?;
        let value = item.expect_value()?.read()?;
        let strukt = value.expect_struct()?;
        let mut sum = 0;
        let mut fields = strukt.iter();
        sum += {
            let (name, value) = fields.next().unwrap()?.expect_name_value()?;
            assert_eq!(name.read()?, "foo".as_raw_symbol_ref());
            value.read()?.expect_i64()?
        };
        sum += {
            let (name, value) = fields.next().unwrap()?.expect_name_value()?;
            assert_eq!(name.read()?, "bar".as_raw_symbol_ref());
            value.read()?.expect_i64()?
        };
        sum += {
            let (name, value) = fields.next().unwrap()?.expect_name_value()?;
            assert_eq!(name.read()?, "baz".as_raw_symbol_ref());
            value.read()?.expect_i64()?
        };
        assert_eq!(sum, 600);

        let value = reader.next()?.expect_value()?;
        assert_eq!(value.read()?.expect_i64()?, 42);
        let mut annotations = value.annotations();
        assert_eq!(annotations.next().unwrap()?, RawSymbolRef::Text("foo"));
        assert_eq!(annotations.next().unwrap()?, RawSymbolRef::Text("bar"));
        assert_eq!(annotations.next().unwrap()?, RawSymbolRef::Text("baz"));

        Ok(())
    }

    #[test]
    fn ranges_and_spans() -> IonResult<()> {
        let empty_context = EncodingContext::empty();
        let context = empty_context.get_ref();
        let data = b"foo 2024T bar::38 [1, 2, 3]";
        let mut reader = LazyRawTextReader_1_0::new(context, data, true);

        let foo = reader.next()?.expect_value()?;
        assert_eq!(foo.span(), b"foo");
        assert_eq!(foo.range(), 0..3);

        let timestamp = reader.next()?.expect_value()?;
        assert_eq!(timestamp.span(), b"2024T");
        assert_eq!(timestamp.range(), 4..9);

        let annotated_int = reader.next()?.expect_value()?;
        assert_eq!(annotated_int.span(), b"bar::38");
        assert_eq!(annotated_int.range(), 10..17);

        let list_value = reader.next()?.expect_value()?;
        assert_eq!(list_value.span(), b"[1, 2, 3]");
        assert_eq!(list_value.range(), 18..27);

        let list = list_value.read()?.expect_list()?;
        let mut child_values = list.iter();

        let value1 = child_values.next().unwrap()?.expect_value()?;
        assert_eq!(value1.span(), b"1");
        assert_eq!(value1.range(), 19..20);

        let value2 = child_values.next().unwrap()?.expect_value()?;
        assert_eq!(value2.span(), b"2");
        assert_eq!(value2.range(), 22..23);

        let value3 = child_values.next().unwrap()?.expect_value()?;
        assert_eq!(value3.span(), b"3");
        assert_eq!(value3.range(), 25..26);

        Ok(())
    }
}
