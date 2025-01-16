#![allow(non_camel_case_types)]

use crate::lazy::any_encoding::{IonEncoding, IonVersion, LazyRawAnyValue};
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::{LazyRawBinaryFieldName_1_0, LazyRawBinaryStruct_1_0};
use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
use crate::lazy::binary::raw::sequence::{LazyRawBinaryList_1_0, LazyRawBinarySExp_1_0};
use crate::lazy::binary::raw::v1_1::e_expression::BinaryEExpression_1_1;
use crate::lazy::binary::raw::v1_1::r#struct::LazyRawBinaryFieldName_1_1;
use crate::lazy::binary::raw::v1_1::reader::LazyRawBinaryReader_1_1;
use crate::lazy::binary::raw::v1_1::value::LazyRawBinaryVersionMarker_1_1;
use crate::lazy::binary::raw::v1_1::{
    r#struct::LazyRawBinaryStruct_1_1,
    sequence::{LazyRawBinaryList_1_1, LazyRawBinarySExp_1_1},
    value::LazyRawBinaryValue_1_1,
    RawBinaryAnnotationsIterator_1_1,
};
use crate::lazy::binary::raw::value::{LazyRawBinaryValue_1_0, LazyRawBinaryVersionMarker_1_0};
use crate::lazy::decoder::{Decoder, LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::Encoder;
use crate::lazy::never::Never;
use crate::lazy::text::buffer::{whitespace_and_then, IonParser, TextBuffer};
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::matched::MatchedValue;
use crate::lazy::text::raw::r#struct::{LazyRawTextFieldName, RawTextStructIterator};
use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
use crate::lazy::text::raw::sequence::{
    RawTextList, RawTextListIterator, RawTextSExp, RawTextSExpIterator,
};
use crate::lazy::text::raw::v1_1::reader::{
    LazyRawTextReader_1_1, LazyRawTextStruct, TextEExpression_1_1,
};
use crate::lazy::text::value::{
    LazyRawTextValue, LazyRawTextValue_1_0, LazyRawTextValue_1_1, LazyRawTextVersionMarker_1_0,
    LazyRawTextVersionMarker_1_1, RawTextAnnotationsIterator,
};
use crate::{
    AnnotationsEncoding, ContainerEncoding, FieldNameEncoding, HasRange, IonError, IonResult,
    LazyRawFieldExpr, SymbolValueEncoding, TextFormat, ValueWriterConfig, WriteConfig,
};
use std::fmt::Debug;
use std::io;
use winnow::combinator::{alt, cut_err, opt, separated_pair};
use winnow::Parser;

/// Marker trait for types that represent an Ion encoding.
pub trait Encoding: Encoder + Decoder {
    type Output: 'static + OutputFromBytes + AsRef<[u8]>;

    fn encode<V: WriteAsIon>(value: V) -> IonResult<Self::Output> {
        let bytes = Self::encode_to(value, Vec::new())?;
        Ok(Self::Output::from_bytes(bytes))
    }

    fn encode_all<V: WriteAsIon, I: IntoIterator<Item = V>>(values: I) -> IonResult<Self::Output> {
        let bytes = Self::encode_all_to(values, Vec::new())?;
        Ok(Self::Output::from_bytes(bytes))
    }

    fn encode_to<V: WriteAsIon, W: io::Write>(value: V, output: W) -> IonResult<W> {
        Self::default_write_config().encode_to(value, output)
    }

    fn encode_all_to<V: WriteAsIon, I: IntoIterator<Item = V>, W: io::Write>(
        values: I,
        output: W,
    ) -> IonResult<W> {
        Self::default_write_config().encode_all_to(output, values)
    }

    fn encoding(&self) -> IonEncoding;
    fn instance() -> Self;
    fn name() -> &'static str;

    fn is_binary() -> bool {
        Self::instance().encoding().is_binary()
    }

    fn is_text() -> bool {
        Self::instance().encoding().is_text()
    }

    fn ion_version() -> IonVersion {
        Self::instance().encoding().version()
    }

    fn default_write_config() -> WriteConfig<Self>;
    fn default_value_writer_config() -> ValueWriterConfig;
}

// Similar to a simple `From` implementation, but can be defined for both String and Vec<u8> because
// this crate owns the trait.
pub trait OutputFromBytes {
    fn from_bytes(bytes: Vec<u8>) -> Self;
}

impl OutputFromBytes for Vec<u8> {
    fn from_bytes(bytes: Vec<u8>) -> Self {
        bytes
    }
}

impl OutputFromBytes for String {
    fn from_bytes(bytes: Vec<u8>) -> Self {
        String::from_utf8(bytes).expect("writer produced invalid UTF-8 bytes")
    }
}

// These types derive trait implementations in order to allow types that containing them
// to also derive trait implementations.

/// The Ion 1.0 binary encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct BinaryEncoding_1_0;

/// The Ion 1.1 binary encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct BinaryEncoding_1_1;

impl BinaryEncoding<'_> for BinaryEncoding_1_0 {}
impl BinaryEncoding<'_> for BinaryEncoding_1_1 {}

/// The Ion 1.0 text encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct TextEncoding_1_0;

impl TextEncoding_1_0 {
    pub fn with_format(self, format: TextFormat) -> WriteConfig<Self> {
        WriteConfig::<Self>::new(format)
    }
}

/// The Ion 1.1 text encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct TextEncoding_1_1;

impl TextEncoding_1_1 {
    pub fn with_format(self, format: TextFormat) -> WriteConfig<Self> {
        WriteConfig::<Self>::new(format)
    }
}

impl Encoding for BinaryEncoding_1_0 {
    type Output = Vec<u8>;

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Binary_1_0
    }

    fn instance() -> Self {
        BinaryEncoding_1_0
    }

    fn name() -> &'static str {
        "binary Ion v1.0"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new()
    }

    fn default_value_writer_config() -> ValueWriterConfig {
        ValueWriterConfig::binary()
            .with_field_name_encoding(FieldNameEncoding::SymbolIds)
            .with_annotations_encoding(AnnotationsEncoding::SymbolIds)
            .with_container_encoding(ContainerEncoding::LengthPrefixed)
            .with_symbol_value_encoding(SymbolValueEncoding::SymbolIds)
    }
}
impl Encoding for BinaryEncoding_1_1 {
    type Output = Vec<u8>;

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Binary_1_1
    }

    fn instance() -> Self {
        BinaryEncoding_1_1
    }

    fn name() -> &'static str {
        "binary Ion v1.1"
    }

    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new()
    }

    fn default_value_writer_config() -> ValueWriterConfig {
        // By default, use the same settings as binary 1.0
        BinaryEncoding_1_0::default_value_writer_config()
    }
}
impl Encoding for TextEncoding_1_0 {
    type Output = String;

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Text_1_0
    }

    fn instance() -> Self {
        TextEncoding_1_0
    }

    fn name() -> &'static str {
        "text Ion v1.0"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new(<TextFormat as Default>::default())
    }
    fn default_value_writer_config() -> ValueWriterConfig {
        ValueWriterConfig::text()
            .with_field_name_encoding(FieldNameEncoding::InlineText)
            .with_annotations_encoding(AnnotationsEncoding::InlineText)
            .with_container_encoding(ContainerEncoding::Delimited)
            .with_symbol_value_encoding(SymbolValueEncoding::InlineText)
    }
}
impl Encoding for TextEncoding_1_1 {
    type Output = String;

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Text_1_1
    }

    fn instance() -> Self {
        TextEncoding_1_1
    }

    fn name() -> &'static str {
        "text Ion v1.1"
    }
    fn default_write_config() -> WriteConfig<Self> {
        WriteConfig::<Self>::new(<TextFormat as Default>::default())
    }

    fn default_value_writer_config() -> ValueWriterConfig {
        // By default, use the same settings as text 1.0
        TextEncoding_1_0::default_value_writer_config()
    }
}

/// Marker trait for binary encodings of any version.
pub trait BinaryEncoding<'top>: Encoding<Output = Vec<u8>> + Decoder {}

/// Marker trait for text encodings.
pub trait TextEncoding<'top>:
    Encoding<Output = String>
    + Decoder<
        AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>,
        Value<'top> = LazyRawTextValue<'top, Self>,
    >
{
    fn new_value(
        input: TextBuffer<'top>,
        encoded_text_value: EncodedTextValue<'top, Self>,
    ) -> Self::Value<'top>;

    /// Matches an expression that appears in value position.
    fn value_expr_matcher() -> impl IonParser<'top, LazyRawValueExpr<'top, Self>>;

    /// Matches an expression that appears in struct field position. Does NOT match trailing commas.
    fn field_expr_matcher() -> impl IonParser<'top, LazyRawFieldExpr<'top, Self>>;

    fn list_matcher() -> impl IonParser<'top, EncodedTextValue<'top, Self>> {
        let make_iter = |buffer: TextBuffer<'top>| RawTextListIterator::<Self>::new(buffer);
        let end_matcher = (whitespace_and_then(opt(",")), whitespace_and_then("]")).take();
        Self::container_matcher("reading a list", "[", make_iter, end_matcher)
            .map(|nested_expr_cache| EncodedTextValue::new(MatchedValue::List(nested_expr_cache)))
    }

    fn sexp_matcher() -> impl IonParser<'top, EncodedTextValue<'top, Self>> {
        let make_iter = |buffer: TextBuffer<'top>| RawTextSExpIterator::<Self>::new(buffer);
        let end_matcher = whitespace_and_then(")");
        Self::container_matcher("reading an s-expression", "(", make_iter, end_matcher)
            .map(|nested_expr_cache| EncodedTextValue::new(MatchedValue::SExp(nested_expr_cache)))
    }

    fn struct_matcher() -> impl IonParser<'top, EncodedTextValue<'top, Self>> {
        let make_iter = |buffer: TextBuffer<'top>| RawTextStructIterator::new(buffer);
        let end_matcher = (whitespace_and_then(opt(",")), whitespace_and_then("}")).take();
        Self::container_matcher("reading a struct", "{", make_iter, end_matcher)
            .map(|nested_expr_cache| EncodedTextValue::new(MatchedValue::Struct(nested_expr_cache)))
    }

    /// Constructs an `IonParser` implementation using parsing logic common to all container types.
    /// Caches all subexpressions in the bump allocator for future reference.
    fn container_matcher<MakeIterator, Iter, Expr>(
        // Text describing what is being parsed. For example: "a list".
        // This message will be added to any error messages for context.
        label: &'static str,
        // The literal that begins the container. ("[", "(", etc.)
        mut opening_token: &str,
        // A closure or function that will construct an appropriate iterator to parse any child
        // expressions.
        mut make_iterator: MakeIterator,
        // A parser that will match the expected end of the container.
        mut end_matcher: impl IonParser<'top, TextBuffer<'top>>,
    ) -> impl IonParser<'top, &'top [Expr]>
    where
        Expr: HasRange + 'top,
        Iter: Iterator<Item = IonResult<Expr>>,
        MakeIterator: FnMut(TextBuffer<'top>) -> Iter,
    {
        use bumpalo::collections::Vec as BumpVec;
        move |input: &mut TextBuffer<'top>| {
            // Make a copy of the input buffer view so the iterator has one it can consume.
            let mut iterator_input = *input;
            // Confirm that the input begins with the expected opening token, consuming it in the process.
            let _head = opening_token.parse_next(&mut iterator_input)?;
            let iterator = make_iterator(iterator_input);
            // Bump-allocate a space to store any child expressions we encounter as we traverse this
            // container.
            let mut child_expr_cache = BumpVec::new_in(input.context().allocator());
            // Visit each child expression yielded by the parser, reporting any errors.
            for expr_result in iterator {
                let expr = match expr_result {
                    Ok(expr) => expr,
                    Err(IonError::Incomplete(..)) => {
                        return input.incomplete(label);
                    }
                    Err(e) => {
                        return input.invalid(format!("{e}")).context(label).cut();
                    }
                };
                // If there are no errors, add the new child expr to the cache.
                child_expr_cache.push(expr);
            }

            // Take note of where we finished.
            let last_expr_end = child_expr_cache
                .last()
                // If we found child expressions, we'll resume immediately after the last child expression.
                .map(|expr| expr.range().end - input.offset())
                // If we didn't find child expressions, we'll resume immediately after the opening token.
                .unwrap_or(opening_token.len());
            // Advance `input` to the remaining data.
            *input = input.slice_to_end(last_expr_end);
            // Confirm that the last expression is followed by input that `end_matcher` approves of.
            let _matched_end = end_matcher.parse_next(input)?;
            Ok(child_expr_cache.into_bump_slice())
        }
    }
}

impl<'top> TextEncoding<'top> for TextEncoding_1_0 {
    fn new_value(
        input: TextBuffer<'top>,
        encoded_text_value: EncodedTextValue<'top, Self>,
    ) -> Self::Value<'top> {
        LazyRawTextValue_1_0::new(input, encoded_text_value)
    }

    fn value_expr_matcher() -> impl IonParser<'top, LazyRawValueExpr<'top, Self>> {
        TextBuffer::match_annotated_value::<Self>.map(RawValueExpr::ValueLiteral)
    }

    fn field_expr_matcher() -> impl IonParser<'top, LazyRawFieldExpr<'top, Self>> {
        // A (name, eexp) pair
        separated_pair(
            whitespace_and_then(TextBuffer::match_struct_field_name)
                .context("matching a struct field name"),
            whitespace_and_then(":").context("matching a struct field delimiter (`:`)"),
            whitespace_and_then(TextBuffer::match_annotated_value::<Self>)
                .context("matching a struct field value"),
        )
        .map(|(field_name, invocation)| {
            LazyRawFieldExpr::NameValue(LazyRawTextFieldName::new(field_name), invocation)
        })
    }
}
impl<'top> TextEncoding<'top> for TextEncoding_1_1 {
    fn new_value(
        input: TextBuffer<'top>,
        encoded_text_value: EncodedTextValue<'top, Self>,
    ) -> Self::Value<'top> {
        LazyRawTextValue_1_1::new(input, encoded_text_value)
    }

    fn value_expr_matcher() -> impl IonParser<'top, LazyRawValueExpr<'top, Self>> {
        alt((
            TextBuffer::match_e_expression.map(RawValueExpr::EExp),
            TextBuffer::match_annotated_value::<Self>.map(RawValueExpr::ValueLiteral),
        ))
    }

    fn field_expr_matcher() -> impl IonParser<'top, LazyRawFieldExpr<'top, Self>> {
        cut_err(alt((
            // A (name, eexp) pair. Check for this first to prevent `(:` from being considered
            // the beginning of an s-expression.
            separated_pair(
                whitespace_and_then(TextBuffer::match_struct_field_name),
                whitespace_and_then(":"),
                whitespace_and_then(TextBuffer::match_e_expression),
            )
            .map(|(field_name, invocation)| {
                LazyRawFieldExpr::NameEExp(LazyRawTextFieldName::new(field_name), invocation)
            }),
            // A (name, value) pair
            separated_pair(
                whitespace_and_then(TextBuffer::match_struct_field_name),
                whitespace_and_then(":"),
                whitespace_and_then(TextBuffer::match_annotated_value::<Self>),
            )
            .map(move |(field_name, value)| {
                let field_name = LazyRawTextFieldName::new(field_name);
                LazyRawFieldExpr::NameValue(field_name, value)
            }),
            // An e-expression
            TextBuffer::match_e_expression.map(LazyRawFieldExpr::EExp),
        )))
        .context("matching a struct field")
    }
}

/// Marker trait for encodings that support macros.
pub trait EncodingWithMacroSupport {}
impl EncodingWithMacroSupport for TextEncoding_1_1 {}

impl Decoder for BinaryEncoding_1_0 {
    const INITIAL_ENCODING_EXPECTED: IonEncoding = IonEncoding::Binary_1_0;
    type Reader<'data> = LazyRawBinaryReader_1_0<'data>;
    type Value<'top> = LazyRawBinaryValue_1_0<'top>;
    type SExp<'top> = LazyRawBinarySExp_1_0<'top>;
    type List<'top> = LazyRawBinaryList_1_0<'top>;
    type Struct<'top> = LazyRawBinaryStruct_1_0<'top>;
    type FieldName<'top> = LazyRawBinaryFieldName_1_0<'top>;
    type AnnotationsIterator<'top> = RawBinaryAnnotationsIterator<'top>;
    // Macros are not supported in Ion 1.0
    type EExp<'top> = Never;
    type VersionMarker<'top> = LazyRawBinaryVersionMarker_1_0<'top>;
}

impl Decoder for TextEncoding_1_0 {
    const INITIAL_ENCODING_EXPECTED: IonEncoding = IonEncoding::Text_1_0;
    type Reader<'data> = LazyRawTextReader_1_0<'data>;
    type Value<'top> = LazyRawTextValue_1_0<'top>;
    type SExp<'top> = RawTextSExp<'top, Self>;
    type List<'top> = RawTextList<'top, Self>;
    type Struct<'top> = LazyRawTextStruct<'top, Self>;
    type FieldName<'top> = LazyRawTextFieldName<'top, Self>;
    type AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>;
    // Macros are not supported in Ion 1.0
    type EExp<'top> = Never;
    type VersionMarker<'top> = LazyRawTextVersionMarker_1_0<'top>;
}

impl Decoder for TextEncoding_1_1 {
    const INITIAL_ENCODING_EXPECTED: IonEncoding = IonEncoding::Text_1_1;
    type Reader<'data> = LazyRawTextReader_1_1<'data>;
    type Value<'top> = LazyRawTextValue_1_1<'top>;
    type SExp<'top> = RawTextSExp<'top, Self>;
    type List<'top> = RawTextList<'top, Self>;
    type Struct<'top> = LazyRawTextStruct<'top, Self>;
    type FieldName<'top> = LazyRawTextFieldName<'top, Self>;
    type AnnotationsIterator<'top> = RawTextAnnotationsIterator<'top>;
    type EExp<'top> = TextEExpression_1_1<'top>;
    type VersionMarker<'top> = LazyRawTextVersionMarker_1_1<'top>;
}

impl Decoder for BinaryEncoding_1_1 {
    const INITIAL_ENCODING_EXPECTED: IonEncoding = IonEncoding::Binary_1_1;
    type Reader<'data> = LazyRawBinaryReader_1_1<'data>;
    type Value<'top> = &'top LazyRawBinaryValue_1_1<'top>;
    type SExp<'top> = LazyRawBinarySExp_1_1<'top>;
    type List<'top> = LazyRawBinaryList_1_1<'top>;
    type Struct<'top> = LazyRawBinaryStruct_1_1<'top>;
    type FieldName<'top> = LazyRawBinaryFieldName_1_1<'top>;
    type AnnotationsIterator<'top> = RawBinaryAnnotationsIterator_1_1<'top>;
    type EExp<'top> = &'top BinaryEExpression_1_1<'top>;
    type VersionMarker<'top> = LazyRawBinaryVersionMarker_1_1<'top>;
}

/// Marker trait for types that represent value literals in an Ion stream of some encoding.
// This trait is used to provide generic conversion implementation of types used as a
// `LazyDecoder::Value` to `ExpandedValueSource`. That is:
//
//     impl<'top, 'data, V: RawValueLiteral, D: LazyDecoder<'data, Value = V>> From<V>
//         for ExpandedValueSource<'top, D>
//
// If we do not confine the implementation to types with a marker trait, rustc complains that
// someone may someday use `ExpandedValueSource` as a `LazyDecoder::Value`, and then the
// implementation will conflict with the core `impl<T> From<T> for T` implementation.
pub trait RawValueLiteral {}

impl<'top, E: TextEncoding<'top>> RawValueLiteral for LazyRawTextValue<'top, E> {}
impl RawValueLiteral for LazyRawBinaryValue_1_0<'_> {}
impl<'top> RawValueLiteral for &'top LazyRawBinaryValue_1_1<'top> {}
impl RawValueLiteral for LazyRawAnyValue<'_> {}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::lazy::encoding::TextEncoding;
    use crate::{
        ion_list, ion_seq, ion_sexp, ion_struct, v1_0, v1_1, IonResult, Sequence, TextFormat,
        WriteConfig,
    };

    #[rstest]
    #[case::pretty_v1_0(
        v1_0::Text.with_format(TextFormat::Pretty),
        "{\n  foo: 1,\n  bar: 2,\n}\n[\n  1,\n  2,\n]\n(\n  1\n  2\n)\n"
    )]
    #[case::pretty_v1_1(
        v1_1::Text.with_format(TextFormat::Pretty),
        "$ion_1_1\n{\n  foo: 1,\n  bar: 2,\n}\n[\n  1,\n  2,\n]\n(\n  1\n  2\n)\n"
    )]
    #[case::compact_v1_0(
        v1_0::Text.with_format(TextFormat::Compact),
        "{foo: 1, bar: 2, } [1, 2, ] (1 2 ) "
    )]
    #[case::compact_v1_1(
        v1_1::Text.with_format(TextFormat::Compact),
        "$ion_1_1 {foo: 1, bar: 2, } [1, 2, ] (1 2 ) "
    )]
    #[case::lines_v1_0(
        v1_0::Text.with_format(TextFormat::Lines),
        "{foo: 1, bar: 2, }\n[1, 2, ]\n(1 2 )\n"
    )]
    #[case::lines_v1_1(
        v1_1::Text.with_format(TextFormat::Lines),
        "$ion_1_1\n{foo: 1, bar: 2, }\n[1, 2, ]\n(1 2 )\n"
    )]
    fn encode_formatted_text<'a, E: TextEncoding<'a>>(
        #[case] config: impl Into<WriteConfig<E>>,
        #[case] expected: &str,
    ) -> IonResult<()> {
        let sequence: Sequence = ion_seq![
            ion_struct! {
                "foo" : 1,
                "bar" : 2,
            },
            ion_list![1, 2],
            ion_sexp! (1 2),
        ];

        // The goal of this test is to confirm that the value was serialized using the requested text format.
        // This string equality checks are unfortunately specific/fragile and can be modified if/when
        // changes are made to the text formatting.

        let text = sequence.encode_as(config)?;
        assert_eq!(text, expected);
        Ok(())
    }
}
