#![allow(non_camel_case_types)]

use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::Range;

use nom::character::streaming::satisfy;

use crate::lazy::decoder::private::LazyContainerPrivate;
use crate::lazy::decoder::{
    LazyRawFieldExpr, LazyRawReader, LazyRawSequence, LazyRawStruct, LazyRawValue,
    LazyRawValueExpr, RawFieldExpr, RawValueExpr,
};
use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::raw_stream_item::{LazyRawStreamItem, RawStreamItem};
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::parse_result::{AddContext, ToIteratorOutput};
use crate::lazy::text::value::{LazyRawTextValue_1_1, RawTextAnnotationsIterator};
use crate::result::IonFailure;
use crate::{IonResult, IonType};

use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::text::matched::MatchedValue;
use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;

pub struct LazyRawTextReader_1_1<'data> {
    input: &'data [u8],
    offset: usize,
}

/// The index at which this macro can be found in the macro table.
pub type MacroAddress = usize;

/// The index at which a value expression can be found within a template's body.
pub type TemplateBodyExprAddress = usize;

#[derive(Copy, Clone, Debug, PartialEq)]
pub enum MacroIdRef<'data> {
    LocalName(&'data str),
    LocalAddress(usize),
    // TODO: Addresses and qualified names
}

impl<'data> From<usize> for MacroIdRef<'data> {
    fn from(address: usize) -> Self {
        MacroIdRef::LocalAddress(address)
    }
}

impl<'data> From<&'data str> for MacroIdRef<'data> {
    fn from(name: &'data str) -> Self {
        MacroIdRef::LocalName(name)
    }
}

#[derive(Copy, Clone)]
pub struct RawTextEExpression_1_1<'top> {
    pub(crate) encoded_expr: EncodedTextMacroInvocation,
    pub(crate) input: TextBufferView<'top>,
    pub(crate) id: MacroIdRef<'top>,
    pub(crate) arg_expr_cache: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
}

impl<'top> RawEExpression<'top, TextEncoding_1_1> for RawTextEExpression_1_1<'top> {
    type RawArgumentsIterator<'a> = RawTextSequenceCacheIterator_1_1<'top> where Self: 'a;

    fn id(&self) -> MacroIdRef<'top> {
        self.id
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator<'_> {
        RawTextSequenceCacheIterator_1_1::new(self.arg_expr_cache)
    }
}

impl<'data> Debug for RawTextEExpression_1_1<'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        // This is a text macro and the parser accepted it, so it's valid UTF-8. We can `unwrap()`.
        write!(f, "<macro invocation '{}'>", self.input.as_text().unwrap())
    }
}

impl<'top> RawTextEExpression_1_1<'top> {
    pub(crate) fn new(
        id: MacroIdRef<'top>,
        encoded_expr: EncodedTextMacroInvocation,
        input: TextBufferView<'top>,
        child_expr_cache: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
    ) -> Self {
        Self {
            encoded_expr,
            input,
            id,
            arg_expr_cache: child_expr_cache,
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

impl<'data> LazyRawReader<'data, TextEncoding_1_1> for LazyRawTextReader_1_1<'data> {
    fn new(data: &'data [u8]) -> Self {
        LazyRawTextReader_1_1 {
            input: data,
            offset: 0,
        }
    }

    fn next<'top>(
        &'top mut self,
        allocator: &'top BumpAllocator,
    ) -> IonResult<LazyRawStreamItem<'top, TextEncoding_1_1>>
    where
        'data: 'top,
    {
        let input =
            TextBufferView::new_with_offset(allocator, &self.input[self.offset..], self.offset);
        let (buffer_after_whitespace, _whitespace) = input
            .match_optional_comments_and_whitespace()
            .with_context("reading v1.1 whitespace/comments at the top level", input)?;
        if buffer_after_whitespace.is_empty() {
            return Ok(RawStreamItem::EndOfStream);
        }

        let (remaining, matched_item) = buffer_after_whitespace
            .match_top_level_item_1_1()
            .with_context("reading a v1.1 top-level value", buffer_after_whitespace)?;

        if let RawStreamItem::VersionMarker(major, minor) = matched_item {
            // TODO: It is not the raw reader's responsibility to report this error. It should
            //       surface the IVM to the caller, who can then either create a different reader
            //       for the reported version OR raise an error.
            //       See: https://github.com/amazon-ion/ion-rust/issues/644
            if (major, minor) != (1, 1) {
                return IonResult::decoding_error(format!(
                    "Ion version {major}.{minor} is not supported"
                ));
            }
        }
        // Since we successfully matched the next value, we'll update the buffer
        // so a future call to `next()` will resume parsing the remaining input.
        self.offset = remaining.offset();
        Ok(matched_item)
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawTextList_1_1<'top> {
    pub(crate) value: LazyRawTextValue_1_1<'top>,
}

impl<'a> Debug for LazyRawTextList_1_1<'a> {
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
    input: TextBufferView<'top>,
    // If this iterator has returned an error, it should return `None` forever afterwards
    has_returned_error: bool,
}

impl<'top> RawTextListIterator_1_1<'top> {
    pub(crate) fn new(input: TextBufferView<'top>) -> Self {
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

        let input_after_last_expr = if let Some(value_expr) = child_expr_cache.last() {
            // ...the input slice that follows the last sequence value...
            match value_expr {
                RawValueExpr::ValueLiteral(value) => value
                    .matched
                    .input
                    .slice_to_end(value.matched.encoded_value.total_length()),
                RawValueExpr::MacroInvocation(invocation) => {
                    let end_of_expr = invocation.input.offset() + invocation.input.len();
                    let remaining = self
                        .iterator
                        .input
                        .slice_to_end(end_of_expr - self.iterator.input.offset());
                    remaining
                }
            }
        } else {
            // ...or there weren't any child values, so it's just the input after the opening delimiter.
            self.iterator.input
        };

        let (mut input_after_ws, _ws) = input_after_last_expr
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a list", input_after_last_expr)?;
        // Skip an optional comma and more whitespace
        if input_after_ws.bytes().first() == Some(&b',') {
            (input_after_ws, _) = input_after_ws
                .slice_to_end(1)
                .match_optional_comments_and_whitespace()
                .with_context("skipping a v1.1 list's trailing comma", input_after_ws)?;
        }
        let (input_after_end, _end_delimiter) = satisfy(|c| c == ']')(input_after_ws)
            .with_context("seeking the closing delimiter of a list", input_after_ws)?;
        let end = input_after_end.offset();

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

impl<'a> Debug for LazyRawTextSExp_1_1<'a> {
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
    input: TextBufferView<'top>,
    // If this iterator has returned an error, it should return `None` forever afterwards
    has_returned_error: bool,
}

impl<'top> RawTextSExpIterator_1_1<'top> {
    pub(crate) fn new(input: TextBufferView<'top>) -> Self {
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

        let input_after_last_expr = if let Some(value_expr) = child_expr_cache.last() {
            // ...the input slice that follows the last sequence value...
            match value_expr {
                RawValueExpr::ValueLiteral(value) => value
                    .matched
                    .input
                    .slice_to_end(value.matched.encoded_value.total_length()),
                RawValueExpr::MacroInvocation(invocation) => {
                    let end_of_expr = invocation.input.offset() + invocation.input.len();
                    let remaining = self
                        .iterator
                        .input
                        .slice_to_end(end_of_expr - self.iterator.input.offset());
                    remaining
                }
            }
        } else {
            // ...or there weren't any child values, so it's just the input after the opening delimiter.
            self.iterator.input
        };

        let (input_after_ws, _ws) = input_after_last_expr
            .match_optional_comments_and_whitespace()
            .with_context("seeking the end of a sexp", input_after_last_expr)?;
        let (input_after_end, _end_delimiter) = satisfy(|c| c == ')')(input_after_ws)
            .with_context("seeking the closing delimiter of a sexp", input_after_ws)?;
        let end = input_after_end.offset();

        let span = start..end;
        Ok((span, child_expr_cache.into_bump_slice()))
    }
}

impl<'top> LazyContainerPrivate<'top, TextEncoding_1_1> for LazyRawTextSExp_1_1<'top> {
    fn from_value(value: LazyRawTextValue_1_1<'top>) -> Self {
        LazyRawTextSExp_1_1 { value }
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
        let MatchedValue::SExp(child_exprs) = self.value.matched.encoded_value.matched() else {
            unreachable!("s-expression contained a matched value of the wrong type")
        };
        RawTextSequenceCacheIterator_1_1::new(child_exprs)
    }

    fn as_value(&self) -> LazyRawTextValue_1_1<'top> {
        self.value.matched.into()
    }
}

impl<'top> Iterator for RawTextSExpIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_sexp_value_1_1() {
            Ok((remaining, Some(value))) => {
                self.input = remaining;
                Some(Ok(value))
            }
            Ok((_remaining, None)) => None,
            Err(e) => {
                self.has_returned_error = true;
                e.with_context("reading the next sexp value", self.input)
                    .transpose()
            }
        }
    }
}

#[derive(Copy, Clone)]
pub struct LazyRawTextStruct_1_1<'top> {
    pub(crate) value: LazyRawTextValue_1_1<'top>,
}

impl<'a> Debug for LazyRawTextStruct_1_1<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for field in self.iter() {
            match field? {
                LazyRawFieldExpr::<TextEncoding_1_1>::NameValuePair(
                    name,
                    RawValueExpr::ValueLiteral(value),
                ) => write!(f, "{name:?}: {value:?}, "),
                LazyRawFieldExpr::<TextEncoding_1_1>::NameValuePair(
                    name,
                    RawValueExpr::MacroInvocation(invocation),
                ) => write!(f, "{name:?}: {invocation:?}, "),
                LazyRawFieldExpr::<TextEncoding_1_1>::MacroInvocation(invocation) => {
                    write!(f, "{invocation:?}, ")
                }
            }?;
        }
        write!(f, "}}").unwrap();

        Ok(())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawTextStructIterator_1_1<'top> {
    input: TextBufferView<'top>,
    has_returned_error: bool,
}

impl<'top> RawTextStructIterator_1_1<'top> {
    pub(crate) fn new(input: TextBufferView<'top>) -> Self {
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
        // TODO: Remove the result wrapper
        Some(Ok(next_expr.clone()))
    }
}

// ===== Trait implementations =====

impl<'top> LazyContainerPrivate<'top, TextEncoding_1_1> for LazyRawTextList_1_1<'top> {
    fn from_value(value: LazyRawTextValue_1_1<'top>) -> Self {
        LazyRawTextList_1_1 { value }
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
        let MatchedValue::List(child_exprs) = self.value.matched.encoded_value.matched() else {
            unreachable!("list contained a matched value of the wrong type")
        };
        RawTextSequenceCacheIterator_1_1::new(child_exprs)
    }

    fn as_value(&self) -> LazyRawTextValue_1_1<'top> {
        self.value.matched.into()
    }
}

impl<'top> Iterator for RawTextListIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.has_returned_error {
            return None;
        }
        match self.input.match_list_value_1_1() {
            Ok((remaining, Some(value_expr))) => {
                self.input = remaining;
                Some(Ok(value_expr))
            }
            Ok((_remaining, None)) => {
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

impl<'top> LazyRawStruct<'top, TextEncoding_1_1> for LazyRawTextStruct_1_1<'top> {
    type Iterator = RawTextStructCacheIterator_1_1<'top>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'top> {
        self.value.annotations()
    }

    fn iter(&self) -> Self::Iterator {
        let MatchedValue::Struct(field_exprs) = self.value.matched.encoded_value.matched() else {
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

impl<'top> RawTextStructIterator_1_1<'top> {
    // TODO: DRY with RawTextStructIterator_1_0
    pub(crate) fn find_span(&self) -> IonResult<Range<usize>> {
        // The input has already skipped past the opening delimiter.
        let start = self.input.offset() - 1;
        // We need to find the input slice containing the closing delimiter.
        let input_after_last = if let Some(field_result) = self.last() {
            // If there are any field expressions, we need to isolate the input slice that follows
            // the last one.
            use RawFieldExpr::*;
            match field_result? {
                // foo: bar
                NameValuePair(_name, RawValueExpr::ValueLiteral(value)) => {
                    value.matched.input.slice_to_end(value.matched.encoded_value.total_length())
                },
                // foo: (:bar ...)
                NameValuePair(_, RawValueExpr::MacroInvocation(invocation))
                // (:foo)
                | MacroInvocation(invocation) => {
                    self.input.slice_to_end(invocation.input.len())
                }
            }
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

        // We need to find the input slice containing the closing delimiter.
        let input_after_last = if let Some(field_result) = child_expr_cache.last() {
            // If there are any field expressions, we need to isolate the input slice that follows
            // the last one.
            use RawFieldExpr::*;
            match field_result {
                // foo: bar
                NameValuePair(_name, RawValueExpr::ValueLiteral(value)) => {
                    value.matched.input.slice_to_end(value.matched.encoded_value.total_length())
                },
                // foo: (:bar ...)
                NameValuePair(_, RawValueExpr::MacroInvocation(invocation))
                // (:foo)
                | MacroInvocation(invocation) => {
                    self.iterator.input.slice_to_end(invocation.input.len())
                }
            }
        } else {
            // ...or there aren't fields, so it's just the input after the opening delimiter.
            self.iterator.input
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
                .with_context("skipping a struct's trailing comma", input_after_ws)?;
        }
        let (input_after_end, _end_delimiter) = satisfy(|c| c == b'}' as char)(input_after_ws)
            .with_context("seeking the closing delimiter of a struct", input_after_ws)?;
        let end = input_after_end.offset();
        Ok((start..end, child_expr_cache.into_bump_slice()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::raw_value_ref::RawValueRef;

    fn expect_next<'top, 'data: 'top>(
        allocator: &'top BumpAllocator,
        reader: &'top mut LazyRawTextReader_1_1<'data>,
        expected: RawValueRef<'top, TextEncoding_1_1>,
    ) {
        let lazy_value = reader
            .next(allocator)
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

        let allocator = BumpAllocator::new();
        let reader = &mut LazyRawTextReader_1_1::new(data.as_bytes());

        // $ion_1_1
        assert_eq!(reader.next(&allocator)?.expect_ivm()?, (1, 1));
        // "foo"
        expect_next(&allocator, reader, RawValueRef::String("foo".into()));
        // bar
        expect_next(&allocator, reader, RawValueRef::Symbol("bar".into()));
        // (baz null.string)
        let sexp = reader
            .next(&allocator)?
            .expect_value()?
            .read()?
            .expect_sexp()?;
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
        let macro_invocation = reader.next(&allocator)?.expect_macro_invocation()?;
        assert_eq!(macro_invocation.id, MacroIdRef::LocalName("quux"));
        expect_next(&allocator, reader, RawValueRef::Int(77.into()));
        expect_next(&allocator, reader, RawValueRef::Bool(false));
        Ok(())
    }
}
