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
use crate::lazy::decoder::Decoder;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::Encoder;
use crate::lazy::expanded::{EncodingContext, EncodingContextRef};
use crate::lazy::span::Span;
use crate::lazy::streaming_raw_reader::IoBuffer;
use crate::lazy::text::buffer::{whitespace_and_then, IonParser, TextBuffer};
use crate::lazy::text::encoded_value::{EncodedTextScalar, EncodedTextValue};
use crate::lazy::text::matched::MatchedValue;
use crate::lazy::text::parse_result::WithContext;
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
use ice_code::ice as cold_path;
use std::cell::OnceCell;
use std::fmt::Debug;
use std::io;
use std::ops::Range;
use std::ptr;
use std::ptr::NonNull;
use std::rc::Rc;
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

    fn detach_value(value: <Self as Decoder>::Value<'_>) -> Self::DetachedValue {
        // `EncodedBinaryValue` is `Copy` and holds no references; reattaching finds the value's
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
    ) -> IonResult<<Self as Decoder>::Value<'a>> {
        // `detached`'s offsets are stream-relative, so the buffer must know its own position.
        let input = BinaryBuffer::new_with_offset(context, span.bytes(), span.offset());
        Ok(context.allocator().alloc_with(|| LazyRawBinaryValue_1_0 {
            encoded_value: *detached,
            input,
        }))
    }

    fn reattach_annotations<'a>(
        detached: &'a Self::DetachedValue,
        context: EncodingContextRef<'a>,
        span: Span<'a>,
    ) -> IonResult<<Self as Decoder>::AnnotationsIterator<'a>> {
        // The iterator borrows only `input`, so the value need not live in the arena.
        let input = BinaryBuffer::new_with_offset(context, span.bytes(), span.offset());
        let value = LazyRawBinaryValue_1_0 {
            encoded_value: *detached,
            input,
        };
        Ok(value.annotations())
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

/// The lifetime-free form of a [`LazyRawTextValue_1_0`]; see
/// [`DetachableValue::DetachedValue`].
#[derive(Debug)]
pub struct DetachedTextValue {
    // The stream offsets of the value, annotations included.
    range: Range<usize>,
    kind: DetachedTextKind,
}

#[derive(Debug)]
enum DetachedTextKind {
    // A scalar's encoding borrows nothing, so it is stored as-is and rebuilt without re-parsing.
    // This also keeps s-expression operators (e.g. `+` in `(+ 1)`) readable; they only match
    // inside an s-expression, so re-parsing one on its own would fail.
    Scalar(EncodedTextScalar),
    // A container's encoding borrows its children from an arena, so it is re-parsed from the
    // stored bytes on first read and cached, unless it was read from another container's cache,
    // in which case `detach_value` fills `parsed` with one that shares it
    // (`ParsedTextContainer::share`). Its annotations are read from the bytes before
    // `data_offset` without re-parsing.
    Container {
        ion_type: IonType,
        data_offset: u16,
        parsed: OnceCell<ParsedTextContainer>,
    },
}

/// A parsed text container: either re-parsed from a `LazyElement`'s bytes
/// ([`parse`](Self::parse)), or a node of another container's parsed tree that shares its owner
/// ([`share`](Self::share)).
///
/// `value` and its children reference only allocations `owner` keeps alive: its encoding context,
/// that context's arena, and the bytes behind its `io_buffer` (a heap `Rc<[u8]>`). Moving the
/// struct moves none of them. The value is held through a raw pointer rather than inline so that
/// no reference into that storage is stored in the struct: a `LazyElement` passed by value would
/// otherwise have those references protected for the duration of a call that may drop it, which
/// Stacked and Tree Borrows reject.
#[derive(Debug)]
struct ParsedTextContainer {
    // Read only by a test probe; owns the storage `value` points into. `Rc` rather than `Box`
    // because moving a `Box` asserts unique access to its pointee, which would invalidate the
    // references the parsed tree holds into it.
    #[allow(dead_code)]
    owner: Rc<ParsedTextOwner>,
    value: NonNull<LazyRawTextValue_1_0<'static>>,
}

/// The storage a [`ParsedTextContainer`]'s value points into.
///
/// `context`'s `parsed_text_owner` points back here, so that a container read from the parsed
/// tree can be stored as a [`ParsedTextContainer`] that shares this owner rather than re-parsing
/// (see [`ParsedTextContainer::share`]). Only `parse` builds a `TextBuffer` over this `context`,
/// from `io_buffer`'s bytes, and every value carrying it is matched from that buffer or a slice of
/// it. A container's `encoded_value` is matched, with its `input`'s context, from bytes inside its
/// `input` (`apply_annotations` widens `input` over the annotations after the match), so its
/// children reference only this context's arena and `io_buffer`'s bytes. `share` asserts the
/// context and bytes of the value it copies but not that pairing, so code that pairs a container's
/// `encoded_value` with an unrelated `input` breaks `share`. A scalar's `encoded_value` borrows
/// nothing, so its pairing does not matter.
#[derive(Debug)]
pub(crate) struct ParsedTextOwner {
    context: EncodingContext,
    // A handle to the same bytes `context` captured. It pins them independently of `context`'s
    // `UnsafeCell<IoBufferSource>`, which `EncodingContext::set_io_buffer_handle` can overwrite
    // through a shared reference.
    io_buffer: IoBuffer,
}

impl ParsedTextContainer {
    /// Re-parses the container at `detached`'s range from a clone of `context` and its bytes.
    fn parse(context: EncodingContextRef<'_>, detached: &DetachedTextValue) -> IonResult<Self> {
        let owner = Rc::new_cyclic(|this| {
            let mut context = context.context.clone();
            context.parsed_text_owner = Some(this.clone());
            let io_buffer = context.save_io_buffer();
            ParsedTextOwner { context, io_buffer }
        });
        let owner_ptr = Rc::as_ptr(&owner);
        // SAFETY: Both references point into heap allocations that `owner` keeps alive and that
        //         are not freed, mutably borrowed, or written while any strong `Rc` to `owner`
        //         lives. Copies of them reach other containers only through
        //         `ParsedTextContainer::share`, and each such container holds its own `Rc` to
        //         `owner`. Other strong `Rc`s exist only briefly, in `detach_value`, while the
        //         container being read holds one. None obtains `&mut` to the pointee, and the
        //         pointee holds only a `Weak` to itself. Its context's `io_buffer_source` is
        //         written only by a reader, on the reader's own context
        //         (`EncodingContext::set_io_buffer_handle`,
        //         `ExpandingReader::between_top_level_expressions`), never on a clone such as this
        //         one. The bytes are `io_buffer`'s `Rc<[u8]>`, which the reader copies on write
        //         rather than mutating while shared. The symbol table reached through `context_ref`
        //         is copied rather than mutated while shared (`EncodingContext::symbol_table_mut`).
        //         The arena is shared with the reader and with other `LazyElement`s, which allocate
        //         in it, but it is never reset while shared (`EncodingContext::make_allocator_mut`
        //         installs a fresh one), so allocations made in it, including this parse's, are not
        //         overwritten or freed while `owner` lives. The `'static` lifetime reaches callers
        //         only through `value` and the copies `share` makes of its descendants; an error
        //         returned below is owned and retains neither reference.
        let (context_ref, bytes): (EncodingContextRef<'static>, &'static [u8]) = unsafe {
            (
                EncodingContextRef::new(&(*owner_ptr).context),
                (*owner_ptr)
                    .io_buffer
                    .bytes_for_stream_range(detached.range.clone()),
            )
        };
        let start = TextBuffer::from_span(
            context_ref,
            Span::with_offset(detached.range.start, bytes),
            true,
        );
        let mut input = start;
        let value = input
            .match_annotated_value::<TextEncoding_1_0>()
            .with_context("re-reading a stored text container", start)?;
        debug_assert!(
            input.is_empty(),
            "re-parsing a stored text container left {} bytes unread",
            input.len()
        );
        debug_assert_eq!(
            TextEncoding_1_0::detached_ion_type(detached),
            value.encoded_value.ion_type()
        );
        if let DetachedTextKind::Container { data_offset, .. } = &detached.kind {
            debug_assert_eq!(*data_offset, value.encoded_value.data_offset_u16());
        }
        let value = NonNull::from(context_ref.allocator().alloc(value));
        Ok(Self { owner, value })
    }

    /// Returns the cache for a container being detached: one that shares the parsed tree `value`
    /// was read from, if any, and otherwise an empty one that `reattach_value` fills.
    // Sharing is outlined with `cold_path!` so that `detach_value`, which `LazyValue::to_owned`
    // inlines for every encoding through `AnyEncoding`, stays small; inlining it measurably slowed
    // binary `to_owned`.
    fn cache_for(value: LazyRawTextValue_1_0<'_>) -> OnceCell<Self> {
        match value.input.context.parsed_text_owner.as_ref() {
            None => OnceCell::new(),
            Some(owner) => cold_path! {
                match owner.upgrade() {
                    Some(owner) => OnceCell::from(Self::share(owner, value)),
                    None => OnceCell::new(),
                }
            },
        }
    }

    /// Returns a cache for `value`, a container read from `owner`'s parsed tree, that shares
    /// `owner` rather than re-parsing `value`'s bytes.
    ///
    /// # Panics
    ///
    /// Panics if `value`'s context is not `owner`'s or its bytes are empty or not in `owner`'s
    /// buffer, which the invariant on [`ParsedTextOwner`] rules out. Such a value's stored range
    /// would not locate it in the stored element's bytes, so there is no correct fallback, and
    /// copying it would extend a borrow `owner` does not keep alive.
    fn share(owner: Rc<ParsedTextOwner>, value: LazyRawTextValue_1_0<'_>) -> Self {
        let owner_bytes = owner.io_buffer.all_bytes().as_ptr_range();
        let value_bytes = value.input.bytes().as_ptr_range();
        // `detach_value` upgrades `owner` from `value`'s context, so the context comparison holds
        // by construction; it guards other ways of obtaining `owner`. The byte comparison is the
        // one a broken invariant fails. A container's input includes its delimiters, so it is
        // never empty; requiring that makes the containment check conclusive.
        assert!(
            ptr::eq(value.input.context.context, &owner.context)
                && !value.input.is_empty()
                && owner_bytes.start <= value_bytes.start
                && value_bytes.end <= owner_bytes.end,
            "a container carrying a parsed text owner's context is not from that owner's parse"
        );
        // `value`'s context and bytes are `owner`'s, and a container's children are matched from
        // inside its input into its input context's arena (see `ParsedTextOwner`), so the copy
        // made here references only storage `owner` keeps alive. The `'static` lifetime given to
        // it reaches callers only through `Self::value` and the copies `share` makes of its
        // descendants, as in `parse`.
        let value = NonNull::from(owner.context.allocator().alloc(value))
            .cast::<LazyRawTextValue_1_0<'static>>();
        Self { owner, value }
    }
}

impl DetachableValue for TextEncoding_1_0 {
    type DetachedValue = DetachedTextValue;

    fn detach_value(value: <Self as Decoder>::Value<'_>) -> Self::DetachedValue {
        let kind = match value.encoded_value.as_scalar() {
            Some(scalar) => DetachedTextKind::Scalar(scalar),
            None => DetachedTextKind::Container {
                ion_type: value.encoded_value.ion_type(),
                data_offset: value.encoded_value.data_offset_u16(),
                parsed: ParsedTextContainer::cache_for(value),
            },
        };
        DetachedTextValue {
            range: value.range(),
            kind,
        }
    }

    fn detached_range(detached: &Self::DetachedValue) -> Range<usize> {
        detached.range.clone()
    }

    fn detached_ion_type(detached: &Self::DetachedValue) -> IonType {
        match &detached.kind {
            DetachedTextKind::Scalar(scalar) => scalar.ion_type(),
            DetachedTextKind::Container { ion_type, .. } => *ion_type,
        }
    }

    fn detached_is_null(detached: &Self::DetachedValue) -> bool {
        match &detached.kind {
            DetachedTextKind::Scalar(scalar) => scalar.is_null(),
            DetachedTextKind::Container { .. } => false,
        }
    }

    fn detached_has_annotations(detached: &Self::DetachedValue) -> bool {
        match &detached.kind {
            DetachedTextKind::Scalar(scalar) => scalar.has_annotations(),
            DetachedTextKind::Container { data_offset, .. } => *data_offset > 0,
        }
    }

    fn reattach_value<'a>(
        detached: &'a Self::DetachedValue,
        context: EncodingContextRef<'a>,
        span: Span<'a>,
    ) -> IonResult<<Self as Decoder>::Value<'a>> {
        // Scalars are rebuilt over `span` without re-parsing. A container's cache is filled when it
        // is stored from another cache, or else re-parsed once, from `context`'s bytes.
        let parsed = match &detached.kind {
            DetachedTextKind::Scalar(scalar) => {
                let input = TextBuffer::from_span(context, span, true);
                return Ok(LazyRawTextValue::new(scalar.to_encoded_value(), input));
            }
            DetachedTextKind::Container { parsed, .. } => match parsed.get() {
                Some(parsed) => parsed,
                None => {
                    let container = ParsedTextContainer::parse(context, detached)?;
                    parsed.get_or_init(|| container)
                }
            },
        };
        // SAFETY: `parsed.value` was allocated in `parsed.owner`'s context's arena and references
        //         only allocations `parsed.owner` keeps alive: that context, its arena, and the
        //         bytes behind its `io_buffer`. `parsed` is built either by
        //         `ParsedTextContainer::parse` or by `ParsedTextContainer::share`, which asserts
        //         that the value's context and bytes are `parsed.owner`'s; see the invariant on
        //         `ParsedTextOwner`. The allocation `value` points to and the bytes it
        //         references are never written or freed while `parsed` lives: the arena only grows
        //         (the reader installs a fresh arena rather than resetting a shared one; see
        //         `EncodingContext::make_allocator_mut`), and the bytes are copied on write while
        //         shared. `parsed` lives in `detached`, which is borrowed for `'a`.
        Ok(unsafe { *parsed.value.cast::<LazyRawTextValue_1_0<'a>>().as_ptr() })
    }

    fn reattach_annotations<'a>(
        detached: &'a Self::DetachedValue,
        context: EncodingContextRef<'a>,
        span: Span<'a>,
    ) -> IonResult<<Self as Decoder>::AnnotationsIterator<'a>> {
        // The annotations are the bytes before `data_offset`, so reading them needs neither a
        // rebuilt value nor a container's cache.
        let data_offset = match &detached.kind {
            DetachedTextKind::Scalar(scalar) => scalar.data_offset(),
            DetachedTextKind::Container { data_offset, .. } => usize::from(*data_offset),
        };
        let input = TextBuffer::from_span(context, span, true);
        Ok(RawTextAnnotationsIterator::new(input.slice(0, data_offset)))
    }

    #[cfg(test)]
    fn detached_parse_owner(detached: &Self::DetachedValue) -> Option<*const ()> {
        match &detached.kind {
            DetachedTextKind::Container { parsed, .. } => {
                parsed.get().map(|p| Rc::as_ptr(&p.owner).cast())
            }
            DetachedTextKind::Scalar(_) => None,
        }
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
    use std::rc::Weak;

    use rstest::rstest;

    use super::{ParsedTextContainer, TextEncoding_1_0};
    use crate::lazy::encoding::TextEncoding;
    use crate::lazy::expanded::lazy_element::LazyElement;
    use crate::lazy::expanded::ExpandedValueSource;
    use crate::lazy::span::Span;
    use crate::lazy::text::buffer::TextBuffer;
    use crate::lazy::text::value::LazyRawTextValue_1_0;
    use crate::{
        ion_list, ion_seq, ion_sexp, ion_struct, v1_0, IonResult, Reader, Sequence, TextFormat,
        WriteConfig,
    };

    /// `share` rejects a container that is not from its owner's parse rather than extending a
    /// borrow the owner does not keep alive. Each case breaks one of its two conditions.
    #[rstest]
    #[case::same_bytes_other_parse(false)]
    #[case::owner_context_foreign_bytes(true)]
    #[should_panic(expected = "is not from that owner's parse")]
    fn share_rejects_a_value_from_another_parse(#[case] foreign_bytes: bool) {
        fn first_child(element: &LazyElement<TextEncoding_1_0>) -> LazyRawTextValue_1_0<'_> {
            let list = element
                .as_lazy_value()
                .unwrap()
                .read()
                .unwrap()
                .expect_list()
                .unwrap();
            let child = list.iter().next().unwrap().unwrap();
            let ExpandedValueSource::ValueLiteral(raw) = child.expanded_value.source;
            raw
        }
        let mut reader = Reader::new(TextEncoding_1_0, b"[[1]] [[2]]".to_vec()).unwrap();
        let a = reader.expect_next().unwrap().to_owned();
        // A second reader's input is a separate allocation, so its bytes are not in `a`'s
        // owner's buffer; the first reader's second value shares that buffer but not the parse.
        let mut other = Reader::new(TextEncoding_1_0, b"[[2]]".to_vec()).unwrap();
        let b = if foreign_bytes {
            &mut other
        } else {
            &mut reader
        }
        .expect_next()
        .unwrap()
        .to_owned();
        let a_child = first_child(&a);
        let mut b_child = first_child(&b);
        let owner = a_child
            .input
            .context
            .parsed_text_owner
            .as_ref()
            .and_then(Weak::upgrade)
            .expect("reading `a` fills its cache");
        if foreign_bytes {
            b_child.input = TextBuffer::from_span(
                a_child.input.context,
                Span::with_offset(b_child.input.offset(), b_child.input.bytes()),
                true,
            );
        }
        let _ = ParsedTextContainer::share(owner, b_child);
    }

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
