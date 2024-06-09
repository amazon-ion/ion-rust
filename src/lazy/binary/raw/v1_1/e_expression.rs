#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::lazy::decoder::LazyRawValueExpr;
use crate::lazy::expanded::macro_evaluator::RawEExpression;
use crate::lazy::text::raw::v1_1::reader::{EncodedTextMacroInvocation, MacroIdRef};
use crate::{v1_1, HasRange, HasSpan, IonResult, Span};

pub struct EncodedBinaryEExp {
    // The number of bytes that were used to encode the e-expression's header (including its ID)
    header_length: u16,
}

impl EncodedBinaryEExp {
    pub fn new(header_length: u16) -> Self {
        Self { header_length }
    }
}

#[derive(Copy, Clone)]
pub struct RawBinaryEExpression_1_1<'top> {
    pub(crate) encoded_expr: EncodedTextMacroInvocation,
    pub(crate) input: ImmutableBuffer<'top>,
    pub(crate) id: MacroIdRef<'top>,
    pub(crate) arg_expr_cache: &'top [LazyRawValueExpr<'top, v1_1::Binary>],
}

impl<'top> HasSpan<'top> for RawBinaryEExpression_1_1<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl<'top> HasRange for RawBinaryEExpression_1_1<'top> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> Debug for RawBinaryEExpression_1_1<'top> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<e-expression invoking id '{}'>", self.id())
    }
}

impl<'top> RawEExpression<'top, v1_1::Binary> for RawBinaryEExpression_1_1<'top> {
    type RawArgumentsIterator<'a> = RawBinarySequenceCacheIterator_1_1<'top>
    where
        Self: 'a;

    fn id(&self) -> MacroIdRef<'top> {
        self.id
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator<'top> {
        RawBinarySequenceCacheIterator_1_1::new(self.arg_expr_cache)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct RawBinarySequenceCacheIterator_1_1<'top> {
    child_exprs: &'top [LazyRawValueExpr<'top, v1_1::Binary>],
    index: usize,
}

impl<'top> RawBinarySequenceCacheIterator_1_1<'top> {
    pub fn new(child_exprs: &'top [LazyRawValueExpr<'top, v1_1::Binary>]) -> Self {
        Self {
            child_exprs,
            index: 0,
        }
    }
}

impl<'top> Iterator for RawBinarySequenceCacheIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, v1_1::Binary>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.child_exprs.get(self.index)?;
        self.index += 1;
        Some(Ok(*next_expr))
    }
}
