#![allow(non_camel_case_types)]

use crate::lazy::any_encoding::{IonEncoding, IonVersion, LazyRawAnyValue};
use crate::lazy::binary::binary_buffer::BinaryBuffer;
use crate::lazy::binary::encoded_value::EncodedBinaryValue;
use crate::lazy::binary::raw::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::r#struct::{LazyRawBinaryFieldName_1_0, LazyRawBinaryStruct_1_0};
use crate::lazy::binary::raw::reader::LazyRawBinaryReader_1_0;
use crate::lazy::binary::raw::sequence::{LazyRawBinaryList_1_0, LazyRawBinarySExp_1_0};
use crate::lazy::binary::raw::type_descriptor::Header;
use crate::lazy::binary::raw::value::{LazyRawBinaryValue_1_0, LazyRawBinaryVersionMarker_1_0};
use crate::lazy::decoder::private::DetachableValue;
use crate::lazy::decoder::{Decoder, LazyRawValue};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::Encoder;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::span::Span;
use crate::lazy::text::buffer::{whitespace_and_then, IonParser, TextBuffer};
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::matched::MatchedValue;
use crate::lazy::text::raw::r#struct::{
    LazyRawTextFieldName, LazyRawTextStruct, RawTextStructIterator,
};
use crate::lazy::text::raw::reader::LazyRawTextReader_1_0;
use crate::lazy::text::raw::sequence::{
    RawTextList, RawTextListIterator, RawTextSExp, RawTextSExpIterator,
};
use crate::lazy::text::value::{
    LazyRawTextValue, LazyRawTextValue_1_0, LazyRawTextVersionMarker_1_0,
    RawTextAnnotationsIterator,
};

use crate::{
    AnnotationsEncoding, ContainerEncoding, FieldNameEncoding, HasRange, IonError, IonResult,
    IonType, LazyRawFieldExpr, SymbolValueEncoding, TextFormat, ValueWriterConfig, WriteConfig,
};
use std::fmt::Debug;
use std::io;
use std::mem;
use std::ops::Range;
use winnow::combinator::{opt, separated_pair};
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

impl BinaryEncoding for BinaryEncoding_1_0 {}

/// The Ion 1.0 text encoding.
#[derive(Copy, Clone, Debug, Default)]
pub struct TextEncoding_1_0;

impl TextEncoding_1_0 {
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

/// Marker trait for binary encodings of any version.
pub trait BinaryEncoding: Encoding<Output = Vec<u8>> + Decoder {}

/// Marker trait for text encodings.
pub trait TextEncoding:
    Encoding<Output = String>
    + for<'a> Decoder<
        AnnotationsIterator<'a> = RawTextAnnotationsIterator<'a>,
        Value<'a> = LazyRawTextValue<'a, Self>,
    >
{
    fn new_value<'a>(
        input: TextBuffer<'a>,
        encoded_text_value: EncodedTextValue<'a, Self>,
    ) -> Self::Value<'a>;

    /// Matches a value that appears in value position.
    fn value_expr_matcher<'a>() -> impl IonParser<'a, Self::Value<'a>>;

    /// Matches an expression that appears in struct field position. Does NOT match trailing commas.
    fn field_expr_matcher<'a>() -> impl IonParser<'a, LazyRawFieldExpr<'a, Self>>;

    fn list_matcher<'a>() -> impl IonParser<'a, EncodedTextValue<'a, Self>> {
        let make_iter = |buffer: TextBuffer<'a>| RawTextListIterator::<Self>::new(buffer);
        let end_matcher = (whitespace_and_then(opt(",")), whitespace_and_then("]")).take();
        Self::container_matcher("reading a list", "[", make_iter, end_matcher)
            .map(|nested_expr_cache| EncodedTextValue::new(MatchedValue::List(nested_expr_cache)))
    }

    fn sexp_matcher<'a>() -> impl IonParser<'a, EncodedTextValue<'a, Self>> {
        let make_iter = |buffer: TextBuffer<'a>| RawTextSExpIterator::<Self>::new(buffer);
        let end_matcher = whitespace_and_then(")");
        Self::container_matcher("reading an s-expression", "(", make_iter, end_matcher)
            .map(|nested_expr_cache| EncodedTextValue::new(MatchedValue::SExp(nested_expr_cache)))
    }

    fn struct_matcher<'a>() -> impl IonParser<'a, EncodedTextValue<'a, Self>> {
        let make_iter = |buffer: TextBuffer<'a>| RawTextStructIterator::new(buffer);
        let end_matcher = (whitespace_and_then(opt(",")), whitespace_and_then("}")).take();
        Self::container_matcher("reading a struct", "{", make_iter, end_matcher)
            .map(|nested_expr_cache| EncodedTextValue::new(MatchedValue::Struct(nested_expr_cache)))
    }

    /// Constructs an `IonParser` implementation using parsing logic common to all container types.
    /// Caches all subexpressions in the bump allocator for future reference.
    fn container_matcher<'top, MakeIterator, Iter, Expr>(
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

impl TextEncoding for TextEncoding_1_0 {
    fn new_value<'a>(
        input: TextBuffer<'a>,
        encoded_text_value: EncodedTextValue<'a, Self>,
    ) -> <Self as Decoder>::Value<'a> {
        LazyRawTextValue_1_0::new(encoded_text_value, input)
    }

    fn value_expr_matcher<'a>() -> impl IonParser<'a, Self::Value<'a>> {
        TextBuffer::match_annotated_value::<Self>
    }

    fn field_expr_matcher<'a>() -> impl IonParser<'a, LazyRawFieldExpr<'a, Self>> {
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
impl Decoder for BinaryEncoding_1_0 {
    const INITIAL_ENCODING_EXPECTED: IonEncoding = IonEncoding::Binary_1_0;
    type Reader<'data> = LazyRawBinaryReader_1_0<'data>;
    type Value<'top> = &'top LazyRawBinaryValue_1_0<'top>;
    type SExp<'top> = LazyRawBinarySExp_1_0<'top>;
    type List<'top> = LazyRawBinaryList_1_0<'top>;
    type Struct<'top> = LazyRawBinaryStruct_1_0<'top>;
    type FieldName<'top> = LazyRawBinaryFieldName_1_0<'top>;
    type AnnotationsIterator<'top> = RawBinaryAnnotationsIterator<'top>;
    type VersionMarker<'top> = LazyRawBinaryVersionMarker_1_0<'top>;
}

impl DetachableValue for BinaryEncoding_1_0 {
    // A binary value is `EncodedBinaryValue<Header>`--pure offsets and metadata--plus a
    // `BinaryBuffer<'top>`. Only the buffer is borrowed, and it can be rebuilt from bytes the caller
    // owns, so detaching needs no lifetime erasure.
    type DetachedValue = EncodedBinaryValue<Header>;

    fn detach_value(value: <Self as Decoder>::Value<'_>, _span: Span<'_>) -> Self::DetachedValue {
        // `EncodedBinaryValue` is `Copy` and holds no references; reattaching re-finds `_span`'s
        // bytes from the offsets it carries.
        value.encoded_value
    }

    fn detached_range(detached: &Self::DetachedValue) -> Range<usize> {
        // The same range that `HasRange for &LazyRawBinaryValue_1_0` reports.
        detached.annotated_value_range()
    }

    // The same fields `LazyRawValue for &LazyRawBinaryValue_1_0` reads, without rebuilding it.

    fn detached_ion_type(detached: &Self::DetachedValue) -> IonType {
        detached.ion_type()
    }

    fn detached_is_null(detached: &Self::DetachedValue) -> bool {
        detached.header().is_null()
    }

    fn detached_has_annotations(detached: &Self::DetachedValue) -> bool {
        detached.has_annotations()
    }

    fn reattach_value<'a>(
        detached: &'a Self::DetachedValue,
        context: EncodingContextRef<'a>,
        span: Span<'a>,
    ) -> <Self as Decoder>::Value<'a> {
        // `detached`'s offsets are stream-relative, so the buffer must know its own position.
        let input = BinaryBuffer::new_with_offset(context, span.bytes(), span.offset());
        context.allocator().alloc_with(|| LazyRawBinaryValue_1_0 {
            encoded_value: *detached,
            input,
        })
    }
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
    type VersionMarker<'top> = LazyRawTextVersionMarker_1_0<'top>;
}

impl TextEncoding_1_0 {
    /// Re-points `value` at `span`'s bytes--which must hold the same bytes, at the same stream
    /// offset, as `value`'s own span, but read from storage that outlives the reader--and erases the
    /// result's lifetime.
    ///
    /// # Safety
    ///
    /// The `'static` lifetime on the returned value is a lie. The caller must keep `span`'s storage
    /// alive for as long as the returned value is used, must not expose the `'static` lifetime
    /// (shorten it again with
    /// [`reattach_value_unchecked`](Self::reattach_value_unchecked) before handing the value out),
    /// and must keep alive everything else the value borrows.
    ///
    /// That last requirement cannot be met today: the returned value retains an
    /// `EncodingContextRef` borrowed from the reader. See the `XXX` note on
    /// `impl DetachableValue for TextEncoding_1_0` below.
    unsafe fn detach_value_unchecked(
        value: LazyRawTextValue_1_0<'_>,
        span: Span<'_>,
    ) -> LazyRawTextValue_1_0<'static> {
        // SAFETY: The caller has promised that `span`'s bytes outlive the reader; this widens that
        //         to `'static`.
        let bytes: &'static [u8] = unsafe { mem::transmute::<&[u8], &'static [u8]>(span.bytes()) };
        // Re-point the value at `bytes` (which outlive the reader), reusing its `encoded_value`
        // as-is. `span` must hold the same bytes at the same offset as the value's own span, or the
        // reused `encoded_value` would silently decode the wrong bytes.
        let relocated = LazyRawTextValue {
            input: TextBuffer::from_span(
                value.input.context(),
                Span::with_offset(span.offset(), bytes),
                true,
            ),
            ..value
        };
        // SAFETY: Per this method's contract, which the caller has accepted.
        unsafe {
            mem::transmute::<LazyRawTextValue_1_0<'_>, LazyRawTextValue_1_0<'static>>(relocated)
        }
    }

    /// Shortens a detached value's `'static` lifetime to `'a`.
    ///
    /// # Safety
    ///
    /// `LazyRawTextValue_1_0` is immutable, so handing out a shorter lifetime would be sound on its
    /// own--a plain coercion would do if the type were not lifetime-invariant. What is not sound is
    /// that the value's contents may already be dangling; the caller must guarantee that everything
    /// [`detach_value_unchecked`](Self::detach_value_unchecked) required to stay alive is still
    /// alive.
    unsafe fn reattach_value_unchecked<'a>(
        detached: LazyRawTextValue_1_0<'static>,
    ) -> LazyRawTextValue_1_0<'a> {
        // SAFETY: Per this method's contract, which the caller has accepted.
        unsafe {
            mem::transmute::<LazyRawTextValue_1_0<'static>, LazyRawTextValue_1_0<'a>>(detached)
        }
    }
}

// A text value cannot be stored without a lifetime--`EncodedTextValue<'top>` is lifetime-invariant
// and its container variants borrow the arena--so text keeps the historical approach of erasing it.
//
// XXX: That erasure is unsound. The detached value holds an `EncodingContextRef` (and a byte slice)
//      borrowed from the reader and transmuted to `'static`; once the reader is dropped or advanced,
//      that borrow dangles. This is a genuine use-after-free, not merely a Stacked/Tree Borrows
//      model violation--base Miri flags it--and it survives in practice only because the freed
//      storage still happens to hold the old bytes. Confining it here leaves the binary encoding
//      sound; fixing text needs a lifetime-free `EncodedTextValue`, which is a larger change.
impl DetachableValue for TextEncoding_1_0 {
    type DetachedValue = LazyRawTextValue_1_0<'static>;

    fn detach_value(value: <Self as Decoder>::Value<'_>, span: Span<'_>) -> Self::DetachedValue {
        // SAFETY: `span` is the caller-owned copy of this value's bytes, as this method's contract
        //         requires. The remaining requirements cannot be met; see the `XXX` note above.
        unsafe { Self::detach_value_unchecked(value, span) }
    }

    fn detached_range(detached: &Self::DetachedValue) -> Range<usize> {
        // The input buffer spans exactly the (possibly annotated) value.
        detached.range()
    }

    // These read the detached value's inline `EncodedTextValue`, dereferencing none of its
    // possibly-dangling references, so they add no exposure beyond the `XXX` note above.

    fn detached_ion_type(detached: &Self::DetachedValue) -> IonType {
        LazyRawValue::ion_type(detached)
    }

    fn detached_is_null(detached: &Self::DetachedValue) -> bool {
        LazyRawValue::is_null(detached)
    }

    fn detached_has_annotations(detached: &Self::DetachedValue) -> bool {
        detached.has_annotations() // Inherent impl; identical to the `LazyRawValue` method.
    }

    fn reattach_value<'a>(
        detached: &'a Self::DetachedValue,
        _context: EncodingContextRef<'a>,
        _span: Span<'a>,
    ) -> <Self as Decoder>::Value<'a> {
        // SAFETY: See the `XXX` note above; the requirement that the detached value not already be
        //         dangling cannot be met.
        unsafe { Self::reattach_value_unchecked(*detached) }
    }
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

impl<E: TextEncoding> RawValueLiteral for LazyRawTextValue<'_, E> {}
impl<'top> RawValueLiteral for &'top LazyRawBinaryValue_1_0<'top> {}
impl RawValueLiteral for LazyRawAnyValue<'_> {}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use crate::lazy::encoding::TextEncoding;
    use crate::{
        ion_list, ion_seq, ion_sexp, ion_struct, v1_0, IonResult, Sequence, TextFormat, WriteConfig,
    };

    #[rstest]
    #[case::pretty_v1_0(
        v1_0::Text.with_format(TextFormat::Pretty),
        "{\n  foo: 1,\n  bar: 2,\n}\n[\n  1,\n  2,\n]\n(\n  1\n  2\n)\n"
    )]
    #[case::compact_v1_0(
        v1_0::Text.with_format(TextFormat::Compact),
        "{foo: 1, bar: 2, } [1, 2, ] (1 2 ) "
    )]
    #[case::lines_v1_0(
        v1_0::Text.with_format(TextFormat::Lines),
        "{foo: 1, bar: 2, }\n[1, 2, ]\n(1 2 )\n"
    )]
    fn encode_formatted_text<E: TextEncoding>(
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
