#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Display, Formatter};
use std::ops::Range;

use crate::lazy::any_encoding::IonEncoding;
use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    Decoder, HasRange, HasSpan, LazyRawContainer, LazyRawFieldExpr, LazyRawFieldName,
    LazyRawReader, LazyRawSequence, LazyRawStruct, LazyRawValue, LazyRawValueExpr,
};
use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::expanded::macro_table::ION_1_1_SYSTEM_MACROS;
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::raw_stream_item::{EndPosition, LazyRawStreamItem, RawStreamItem};
use crate::lazy::span::Span;
use crate::lazy::streaming_raw_reader::RawReaderState;
use crate::lazy::text::buffer::TextBuffer;
use crate::lazy::text::matched::{MatchedFieldName, MatchedValue};
use crate::lazy::text::parse_result::AddContext;
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, TextEExpArgGroup};
use crate::lazy::text::value::{LazyRawTextValue_1_1, RawTextAnnotationsIterator};
use crate::{v1_1, Encoding, IonResult, IonType, RawSymbolRef};
use bumpalo::collections::Vec as BumpVec;
use winnow::combinator::opt;
use winnow::token::{literal, one_of};
use winnow::Parser;

pub struct LazyRawTextReader_1_1<'data> {
    input: TextBuffer<'data>,
}

impl<'data> LazyRawTextReader_1_1<'data> {
    pub fn context(&self) -> EncodingContextRef<'data> {
        self.input.context
    }
}

impl<'data> LazyRawReader<'data, TextEncoding_1_1> for LazyRawTextReader_1_1<'data> {
    fn new(context: EncodingContextRef<'data>, data: &'data [u8], is_final_data: bool) -> Self {
        Self::resume(
            context,
            RawReaderState::new(data, 0, is_final_data, IonEncoding::Text_1_1),
        )
    }

    fn resume(context: EncodingContextRef<'data>, saved_state: RawReaderState<'data>) -> Self {
        LazyRawTextReader_1_1 {
            input: TextBuffer::new_with_offset(
                context,
                saved_state.data(),
                saved_state.offset(),
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

    fn next(&mut self) -> IonResult<LazyRawStreamItem<'data, TextEncoding_1_1>> {
        let _whitespace = self
            .input
            .match_optional_comments_and_whitespace()
            .with_context(
                "reading v1.1 whitespace/comments at the top level",
                self.input,
            )?;
        if self.input.is_empty() {
            return Ok(RawStreamItem::EndOfStream(EndPosition::new(
                TextEncoding_1_1.encoding(),
                self.input.offset(),
            )));
        }

        // Consume any trailing whitespace that followed this item. Doing this allows us to check
        // whether this was the last item in the buffer by testing `buffer.is_empty()` afterward.
        let matched_item = self
            .input
            .match_top_level_item_1_1()
            .with_context("reading a v1.1 top-level value", self.input)?;

        let _trailing_ws = self
            .input
            .match_optional_comments_and_whitespace()
            .with_context(
                "reading trailing top-level whitespace/comments in v1.1",
                self.input,
            )?;
        Ok(matched_item)
    }

    fn position(&self) -> usize {
        self.input.offset()
    }

    fn encoding(&self) -> IonEncoding {
        IonEncoding::Text_1_1
    }
}

/// The index at which this macro can be found in the macro table.
pub type MacroAddress = usize;

/// An address in the Ion 1.1 system macro table.
/// Guaranteed to fit in a byte.
#[derive(Copy, Clone, Debug, PartialEq)]
pub struct SystemMacroAddress(u8);

impl SystemMacroAddress {
    pub fn new(address: MacroAddress) -> Option<Self> {
        if address < ION_1_1_SYSTEM_MACROS.len() {
            Some(Self(address as u8))
        } else {
            None
        }
    }

    pub const fn new_unchecked(address: MacroAddress) -> Self {
        Self(address as u8)
    }

    pub fn as_usize(&self) -> usize {
        self.0 as usize
    }

    pub fn as_u8(&self) -> u8 {
        self.0
    }
}

pub(crate) mod system_macros {
    use crate::lazy::text::raw::v1_1::reader::SystemMacroAddress;

    pub const NONE: SystemMacroAddress = SystemMacroAddress(0x00);
    pub const VALUES: SystemMacroAddress = SystemMacroAddress(0x01);
    pub const DEFAULT: SystemMacroAddress = SystemMacroAddress(0x02);
    pub const META: SystemMacroAddress = SystemMacroAddress(0x03);
    pub const REPEAT: SystemMacroAddress = SystemMacroAddress(0x04);
    pub const FLATTEN: SystemMacroAddress = SystemMacroAddress(0x05);
    pub const DELTA: SystemMacroAddress = SystemMacroAddress(0x06);
    pub const SUM: SystemMacroAddress = SystemMacroAddress(0x07);
    pub const ANNOTATE: SystemMacroAddress = SystemMacroAddress(0x08);
    pub const MAKE_STRING: SystemMacroAddress = SystemMacroAddress(0x09);
    pub const MAKE_SYMBOL: SystemMacroAddress = SystemMacroAddress(0x0A);
    pub const MAKE_DECIMAL: SystemMacroAddress = SystemMacroAddress(0x0B);
    pub const MAKE_TIMESTAMP: SystemMacroAddress = SystemMacroAddress(0x0C);
    pub const MAKE_BLOB: SystemMacroAddress = SystemMacroAddress(0x0D);
    pub const MAKE_LIST: SystemMacroAddress = SystemMacroAddress(0x0E);
    pub const MAKE_SEXP: SystemMacroAddress = SystemMacroAddress(0x0F);
    pub const MAKE_FIELD: SystemMacroAddress = SystemMacroAddress(0x10);
    pub const MAKE_STRUCT: SystemMacroAddress = SystemMacroAddress(0x11);
    pub const PARSE_ION: SystemMacroAddress = SystemMacroAddress(0x12);
    pub const SET_SYMBOLS: SystemMacroAddress = SystemMacroAddress(0x13);
    pub const ADD_SYMBOLS: SystemMacroAddress = SystemMacroAddress(0x14);
    pub const SET_MACROS: SystemMacroAddress = SystemMacroAddress(0x15);
    pub const ADD_MACROS: SystemMacroAddress = SystemMacroAddress(0x16);
    pub const USE: SystemMacroAddress = SystemMacroAddress(0x17);
}

/// The index at which a value expression can be found within a template's body.
pub type TemplateBodyExprAddress = usize;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum MacroIdRef<'data> {
    LocalName(&'data str),
    LocalAddress(usize),
    SystemAddress(SystemMacroAddress),
    // TODO: Addresses and qualified names
}

impl Display for MacroIdRef<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            MacroIdRef::LocalName(name) => write!(f, "{}", name),
            MacroIdRef::LocalAddress(address) => write!(f, "{}", address),
            MacroIdRef::SystemAddress(address) => {
                write!(f, "$ion::{}", address.as_usize())
            }
        }
    }
}

impl From<usize> for MacroIdRef<'_> {
    fn from(address: usize) -> Self {
        MacroIdRef::LocalAddress(address)
    }
}

impl<'data> From<&'data str> for MacroIdRef<'data> {
    fn from(name: &'data str) -> Self {
        MacroIdRef::LocalName(name)
    }
}

impl From<SystemMacroAddress> for MacroIdRef<'_> {
    fn from(system_macro_address: SystemMacroAddress) -> Self {
        MacroIdRef::SystemAddress(system_macro_address)
    }
}

#[derive(Copy, Clone)]
pub struct TextEExpression_1_1<'top> {
    pub(crate) input: TextBuffer<'top>,
    pub(crate) id: MacroIdRef<'top>,
    pub(crate) arg_cache: &'top [EExpArg<'top, TextEncoding_1_1>],
}

impl<'top> HasSpan<'top> for TextEExpression_1_1<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl HasRange for TextEExpression_1_1<'_> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> RawEExpression<'top, TextEncoding_1_1> for TextEExpression_1_1<'top> {
    type RawArgumentsIterator = TextEExpArgsIterator_1_1<'top>;
    type ArgGroup = TextEExpArgGroup<'top>;

    fn id(self) -> MacroIdRef<'top> {
        self.id
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator {
        TextEExpArgsIterator_1_1::new(self.arg_cache)
    }
}

impl Debug for TextEExpression_1_1<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // This is a text macro and the parser accepted it, so it's valid UTF-8. We can `unwrap()`.
        write!(f, "<macro invocation '{}'>", self.input.as_text().unwrap())
    }
}

impl<'top> TextEExpression_1_1<'top> {
    pub(crate) fn new(
        id: MacroIdRef<'top>,
        input: TextBuffer<'top>,
        arg_cache: &'top [EExpArg<'top, TextEncoding_1_1>],
    ) -> Self {
        Self {
            input,
            id,
            arg_cache,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct EncodedTextMacroInvocation {
    // The ID always begins at index 2 (after the opening `(:`). The parameters follow the ID.
    id_length: u16,
}

impl EncodedTextMacroInvocation {
    pub fn new(id_length: u16) -> Self {
        Self { id_length }
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawTextList_1_1<'top> {
    pub(crate) value: LazyRawTextValue_1_1<'top>,
}

impl Debug for LazyRawTextList_1_1<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "[")?;
        for value in self.iter() {
            write!(f, "{:?}, ", value?.expect_value()?.read()?)?;
        }
        write!(f, "]").unwrap();

        Ok(())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawTextListIterator_1_1<'top> {
    input: TextBuffer<'top>,
    // If this iterator has returned an error, it should return `None` forever afterward
    has_returned_error: bool,
}

impl<'top> RawTextListIterator_1_1<'top> {
    pub(crate) fn new(input: TextBuffer<'top>) -> Self {
        Self {
            input,
            has_returned_error: false,
        }
    }
}

/// Wraps a [`RawTextListIterator_1_1`] (which parses the body of a list) and caches the child
/// expressions the iterator yields along the way. Finally, returns a `Range<usize>` representing
/// the span of input bytes that the list occupies.
pub(crate) struct TextListSpanFinder_1_1<'top> {
    pub(crate) allocator: &'top bumpalo::Bump,
    pub(crate) iterator: RawTextListIterator_1_1<'top>,
}

impl<'top> TextListSpanFinder_1_1<'top> {
    pub(crate) fn find_span(
        &self,
    ) -> IonResult<(
        Range<usize>,
        &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
    )> {
        // The input has already skipped past the opening delimiter.
        let start = self.iterator.input.offset() - 1;
        let mut child_expr_cache = BumpVec::new_in(self.allocator);
        for expr_result in self.iterator {
            let expr = expr_result?;
            child_expr_cache.push(expr);
        }

        let end = child_expr_cache
            .last()
            .map(|e| e.range().end)
            .unwrap_or(self.iterator.input.offset());
        let mut input = self
            .iterator
            .input
            .slice_to_end(end - self.iterator.input.offset());

        let _ws = input
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a list", input)?;

        // Skip an optional comma and more whitespace
        let _ = (
            opt(literal(",")),
            TextBuffer::match_optional_comments_and_whitespace,
        )
            .parse_next(&mut input)
            .with_context("skipping a v1.1 list item's trailing comma", input)?;
        let _end_delimiter = one_of(|c: u8| c == b']')
            .parse_next(&mut input)
            .with_context("seeking the closing delimiter of a list", input)?;
        let end = input.offset();

        let span = start..end;
        Ok((span, child_expr_cache.into_bump_slice()))
    }
    pub fn new(allocator: &'top bumpalo::Bump, iterator: RawTextListIterator_1_1<'top>) -> Self {
        Self {
            allocator,
            iterator,
        }
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawTextSExp_1_1<'top> {
    pub(crate) value: LazyRawTextValue_1_1<'top>,
}

impl Debug for LazyRawTextSExp_1_1<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for value in self.iter() {
            write!(f, "{:?} ", value?.expect_value()?.read()?)?;
        }
        write!(f, ")").unwrap();

        Ok(())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawTextSExpIterator_1_1<'top> {
    input: TextBuffer<'top>,
    // If this iterator has returned an error, it should return `None` forever afterwards
    has_returned_error: bool,
}

impl<'top> RawTextSExpIterator_1_1<'top> {
    pub(crate) fn new(input: TextBuffer<'top>) -> Self {
        Self {
            input,
            has_returned_error: false,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawTextSequenceCacheIterator_1_1<'top> {
    child_exprs: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
    index: usize,
}

impl<'top> RawTextSequenceCacheIterator_1_1<'top> {
    pub fn new(child_exprs: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>]) -> Self {
        Self {
            child_exprs,
            index: 0,
        }
    }
}

impl<'top> Iterator for RawTextSequenceCacheIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.child_exprs.get(self.index)?;
        self.index += 1;
        Some(Ok(*next_expr))
    }
}

#[derive(Debug, Copy, Clone)]
pub struct TextEExpArgsIterator_1_1<'top> {
    arg_exprs: &'top [EExpArg<'top, v1_1::Text>],
    index: usize,
}

impl<'top> TextEExpArgsIterator_1_1<'top> {
    pub fn new(arg_exprs: &'top [EExpArg<'top, v1_1::Text>]) -> Self {
        Self {
            arg_exprs,
            index: 0,
        }
    }
}

impl<'top> Iterator for TextEExpArgsIterator_1_1<'top> {
    type Item = IonResult<EExpArg<'top, v1_1::Text>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.arg_exprs.get(self.index)?;
        self.index += 1;
        Some(Ok(*next_expr))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let num_args = self.arg_exprs.len();
        // Tells the macro evaluator how much space to allocate to hold these arguments
        (num_args, Some(num_args))
    }
}

/// Wraps a [`RawTextSExpIterator_1_1`] (which parses the body of a sexp) and caches the child
/// expressions the iterator yields along the way. Finally, returns a `Range<usize>` representing
/// the span of input bytes that the sexp occupies.
pub(crate) struct TextSExpSpanFinder_1_1<'top> {
    pub(crate) allocator: &'top bumpalo::Bump,
    pub(crate) iterator: RawTextSExpIterator_1_1<'top>,
}

impl<'top> TextSExpSpanFinder_1_1<'top> {
    pub fn new(allocator: &'top bumpalo::Bump, iterator: RawTextSExpIterator_1_1<'top>) -> Self {
        Self {
            allocator,
            iterator,
        }
    }

    /// Scans ahead to find the end of this s-expression and reports the input span that it occupies.
    /// As it scans, it records lazy references to the S-expression's child expressions.
    ///
    /// The `initial_bytes_skipped` parameter indicates how many bytes of input that represented the
    /// beginning of the expression are not in the buffer. For plain s-expressions, this will always
    /// be `1` as they begin with a single open parenthesis `(`. For e-expressions (which are used
    /// to invoke macros from the data stream), it will always be a minimum of `3`: two bytes for
    /// the opening `(:` and at least one for the macro identifier. (For example: `(:foo`.)
    pub(crate) fn find_span(
        &self,
        initial_bytes_skipped: usize,
    ) -> IonResult<(
        Range<usize>,
        &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
    )> {
        // The input has already skipped past the opening delimiter.
        let start = self.iterator.input.offset() - initial_bytes_skipped;
        let mut child_expr_cache = BumpVec::new_in(self.allocator);

        for expr_result in self.iterator {
            let expr = expr_result?;
            child_expr_cache.push(expr);
        }

        let end = child_expr_cache
            .last()
            .map(|e| e.range().end)
            .unwrap_or(self.iterator.input.offset());
        let mut input = self
            .iterator
            .input
            .slice_to_end(end - self.iterator.input.offset());

        let _ws = input
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a sexp", input)?;
        let _end_delimiter = one_of(|c| c == b')')
            .parse_next(&mut input)
            .with_context("seeking the closing delimiter of a sexp", input)?;
        let end = input.offset();

        let range = start..end;
        Ok((range, child_expr_cache.into_bump_slice()))
    }
}

impl<'top> LazyContainerPrivate<'top, TextEncoding_1_1> for LazyRawTextSExp_1_1<'top> {
    fn from_value(value: LazyRawTextValue_1_1<'top>) -> Self {
        LazyRawTextSExp_1_1 { value }
    }
}

impl<'top> LazyRawContainer<'top, TextEncoding_1_1> for LazyRawTextSExp_1_1<'top> {
    fn as_value(&self) -> <TextEncoding_1_1 as Decoder>::Value<'top> {
        self.value
    }
}

impl<'top> LazyRawSequence<'top, TextEncoding_1_1> for LazyRawTextSExp_1_1<'top> {
    type Iterator = RawTextSequenceCacheIterator_1_1<'top>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'top> {
        self.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    fn iter(&self) -> Self::Iterator {
        let MatchedValue::SExp(child_exprs) = self.value.encoded_value.matched() else {
            unreachable!("s-expression contained a matched value of the wrong type")
        };
        RawTextSequenceCacheIterator_1_1::new(child_exprs)
    }
}

impl<'top> Iterator for RawTextSExpIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_sexp_value_1_1() {
            Ok(Some(value)) => Some(Ok(value)),
            Ok(None) => None,
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next sexp value", self.input)
                    .transpose()
            }
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawTextFieldName_1_1<'top> {
    matched: MatchedFieldName<'top>,
}

impl<'top> LazyRawTextFieldName_1_1<'top> {
    pub(crate) fn new(matched: MatchedFieldName<'top>) -> Self {
        Self { matched }
    }
}

impl<'top> HasSpan<'top> for LazyRawTextFieldName_1_1<'top> {
    fn span(&self) -> Span<'top> {
        self.matched.span()
    }
}

impl HasRange for LazyRawTextFieldName_1_1<'_> {
    fn range(&self) -> Range<usize> {
        self.matched.range()
    }
}

impl<'top> LazyRawFieldName<'top, TextEncoding_1_1> for LazyRawTextFieldName_1_1<'top> {
    fn read(&self) -> IonResult<RawSymbolRef<'top>> {
        self.matched.read()
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawTextStruct_1_1<'top> {
    pub(crate) value: LazyRawTextValue_1_1<'top>,
}

impl Debug for LazyRawTextStruct_1_1<'_> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for field_result in self.iter() {
            let field = field_result?;
            use LazyRawFieldExpr::*;
            match field {
                NameValue(name, value) => {
                    write!(f, "{name:?}: {value:?}")
                }
                NameEExp(name, eexp) => {
                    write!(f, "{name:?}: {eexp:?}")
                }
                EExp(eexp) => {
                    write!(f, "{eexp:?}")
                }
            }?;
        }
        write!(f, "}}").unwrap();

        Ok(())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawTextStructIterator_1_1<'top> {
    input: TextBuffer<'top>,
    has_returned_error: bool,
}

impl<'top> RawTextStructIterator_1_1<'top> {
    pub(crate) fn new(input: TextBuffer<'top>) -> Self {
        Self {
            input,
            has_returned_error: false,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawTextStructCacheIterator_1_1<'top> {
    field_exprs: &'top [LazyRawFieldExpr<'top, TextEncoding_1_1>],
    index: usize,
}

impl<'top> RawTextStructCacheIterator_1_1<'top> {
    pub fn new(field_exprs: &'top [LazyRawFieldExpr<'top, TextEncoding_1_1>]) -> Self {
        Self {
            field_exprs,
            index: 0,
        }
    }
}

impl<'top> Iterator for RawTextStructCacheIterator_1_1<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.field_exprs.get(self.index)?;
        self.index += 1;
        // TODO: Remove the result wrapper because these values are already in the cache
        Some(Ok(*next_expr))
    }
}

// ===== Trait implementations =====

impl<'top> LazyContainerPrivate<'top, TextEncoding_1_1> for LazyRawTextList_1_1<'top> {
    fn from_value(value: LazyRawTextValue_1_1<'top>) -> Self {
        LazyRawTextList_1_1 { value }
    }
}

impl<'top> LazyRawContainer<'top, TextEncoding_1_1> for LazyRawTextList_1_1<'top> {
    fn as_value(&self) -> LazyRawTextValue_1_1<'top> {
        self.value
    }
}

impl<'top> LazyRawSequence<'top, TextEncoding_1_1> for LazyRawTextList_1_1<'top> {
    type Iterator = RawTextSequenceCacheIterator_1_1<'top>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'top> {
        self.value.annotations()
    }

    fn ion_type(&self) -> IonType {
        self.value.ion_type()
    }

    fn iter(&self) -> Self::Iterator {
        let MatchedValue::List(child_exprs) = self.value.encoded_value.matched() else {
            unreachable!("list contained a matched value of the wrong type")
        };
        RawTextSequenceCacheIterator_1_1::new(child_exprs)
    }
}

impl<'top> Iterator for RawTextListIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_list_value_1_1() {
            Ok(Some(value_expr)) => Some(Ok(value_expr)),
            Ok(None) => {
                // Don't update `remaining` so subsequent calls will continue to return None
                None
            }
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next list value", self.input)
                    .transpose()
            }
        }
    }
}

impl<'top> LazyContainerPrivate<'top, TextEncoding_1_1> for LazyRawTextStruct_1_1<'top> {
    fn from_value(value: LazyRawTextValue_1_1<'top>) -> Self {
        LazyRawTextStruct_1_1 { value }
    }
}

impl<'top> LazyRawContainer<'top, TextEncoding_1_1> for LazyRawTextStruct_1_1<'top> {
    fn as_value(&self) -> <TextEncoding_1_1 as Decoder>::Value<'top> {
        self.value
    }
}

impl<'top> LazyRawStruct<'top, TextEncoding_1_1> for LazyRawTextStruct_1_1<'top> {
    type Iterator = RawTextStructCacheIterator_1_1<'top>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'top> {
        self.value.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        let MatchedValue::Struct(field_exprs) = self.value.encoded_value.matched() else {
            unreachable!("struct contained a matched value of the wrong type")
        };
        RawTextStructCacheIterator_1_1::new(field_exprs)
    }
}

impl<'top> Iterator for RawTextStructIterator_1_1<'top> {
    type Item = IonResult<LazyRawFieldExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_struct_field_1_1() {
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

/// Wraps a [`RawTextStructIterator_1_1`] (which parses the body of a struct) and caches the field
/// expressions the iterator yields along the way. Finally, returns a `Range<usize>` representing
/// the span of input bytes that the struct occupies.
pub(crate) struct TextStructSpanFinder_1_1<'top> {
    pub(crate) allocator: &'top bumpalo::Bump,
    pub(crate) iterator: RawTextStructIterator_1_1<'top>,
}

impl<'top> TextStructSpanFinder_1_1<'top> {
    pub fn new(allocator: &'top bumpalo::Bump, iterator: RawTextStructIterator_1_1<'top>) -> Self {
        Self {
            allocator,
            iterator,
        }
    }

    /// Scans ahead to find the end of this struct and reports the input span that it occupies.
    /// As it scans, it records lazy references to the struct's field expressions.
    pub(crate) fn find_span(
        &self,
    ) -> IonResult<(
        Range<usize>,
        &'top [LazyRawFieldExpr<'top, TextEncoding_1_1>],
    )> {
        // The input has already skipped past the opening delimiter.
        let start = self.iterator.input.offset() - 1;
        let mut child_expr_cache = BumpVec::new_in(self.allocator);
        for expr_result in self.iterator {
            let expr = expr_result?;
            child_expr_cache.push(expr);
        }

        let end = child_expr_cache
            .last()
            .map(|e| e.range().end)
            .unwrap_or(start + 1);
        let mut input = self
            .iterator
            .input
            .slice_to_end(end - self.iterator.input.offset());

        let _ws = input
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a struct", input)?;
        // Skip an optional comma and more whitespace
        let _ = (
            opt(literal(",")),
            TextBuffer::match_optional_comments_and_whitespace,
        )
            .parse_next(&mut input)
            .with_context("skipping a struct field's trailing comma", input)?;
        let _end_delimiter = one_of(|c: u8| c == b'}')
            .parse_next(&mut input)
            .with_context("seeking the closing delimiter of a struct", input)?;
        let end = input.offset();
        Ok((start..end, child_expr_cache.into_bump_slice()))
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::any_encoding::IonVersion;
    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::raw_value_ref::RawValueRef;
    use crate::RawVersionMarker;

    use super::*;

    fn expect_next<'data>(
        reader: &mut LazyRawTextReader_1_1<'data>,
        expected: RawValueRef<'data, TextEncoding_1_1>,
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

    #[test]
    fn top_level() -> IonResult<()> {
        let data = r#"
            $ion_1_1
            "foo"
            bar
            (baz null.string)
            (:quux quuz)
            77
            false
       "#;

        let mut context = EncodingContext::for_ion_version(IonVersion::v1_1);
        let macro_quux =
            TemplateCompiler::compile_from_source(context.get_ref(), "(macro quux (x) null)")?;
        context.macro_table.add_template_macro(macro_quux)?;
        let reader = &mut LazyRawTextReader_1_1::new(context.get_ref(), data.as_bytes(), true);

        // $ion_1_1
        assert_eq!(reader.next()?.expect_ivm()?.major_minor(), (1, 1));
        // "foo"
        expect_next(reader, RawValueRef::String("foo".into()));
        // bar
        expect_next(reader, RawValueRef::Symbol("bar".into()));
        // (baz null.string)
        let sexp = reader.next()?.expect_value()?.read()?.expect_sexp()?;
        let mut children = sexp.iter();
        assert_eq!(
            children.next().unwrap()?.expect_value()?.read()?,
            RawValueRef::Symbol("baz".into())
        );
        assert_eq!(
            children.next().unwrap()?.expect_value()?.read()?,
            RawValueRef::Null(IonType::String)
        );
        assert!(children.next().is_none());
        // (:quux quuz)
        let macro_invocation = reader.next()?.expect_eexp()?;
        assert_eq!(macro_invocation.id, MacroIdRef::LocalName("quux"));
        expect_next(reader, RawValueRef::Int(77.into()));
        expect_next(reader, RawValueRef::Bool(false));
        Ok(())
    }
}
