#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::lazy::decoder::LazyRawValueExpr;
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::lazy::expanded::e_expression::ArgGroup;
use crate::lazy::expanded::macro_evaluator::{EExpressionArgGroup, RawEExpression};
use crate::lazy::expanded::template::{Parameter, ParameterEncoding};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::text::raw::v1_1::arg_group::EExpArg;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::{v1_1, HasRange, HasSpan, IonResult, Span};

#[derive(Copy, Clone)]
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
    pub(crate) encoded_expr: EncodedBinaryEExp,
    pub(crate) input: ImmutableBuffer<'top>,
    pub(crate) id: MacroIdRef<'top>,
    pub(crate) arg_cache: &'top [EExpArg<'top, v1_1::Binary>],
}

impl<'top> RawBinaryEExpression_1_1<'top> {
    pub fn new(
        id: MacroIdRef<'top>,
        encoded_expr: EncodedBinaryEExp,
        input: ImmutableBuffer<'top>,
        arg_cache: &'top [EExpArg<'top, v1_1::Binary>],
    ) -> Self {
        Self {
            encoded_expr,
            input,
            id,
            arg_cache,
        }
    }
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
    type RawArgumentsIterator<'a> = BinaryEExpArgsIterator_1_1<'top>
    where
        Self: 'a;
    type ArgGroup = BinaryEExpArgGroup<'top>;

    fn id(&self) -> MacroIdRef<'top> {
        self.id
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator<'top> {
        BinaryEExpArgsIterator_1_1::new(self.arg_cache)
    }
}

#[derive(Debug, Copy, Clone)]
pub struct BinaryEExpArgGroup<'top> {
    parameter: &'top Parameter,
    input: ImmutableBuffer<'top>,
    expr_cache: &'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>],
}

impl<'top> BinaryEExpArgGroup<'top> {
    pub fn new(
        parameter: &'top Parameter,
        input: ImmutableBuffer<'top>,
        expr_cache: &'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>],
    ) -> Self {
        Self {
            parameter,
            input,
            expr_cache,
        }
    }
}

impl<'top> HasRange for BinaryEExpArgGroup<'top> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> HasSpan<'top> for BinaryEExpArgGroup<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

#[derive(Debug, Copy, Clone)]
pub struct BinaryEExpArgGroupIterator<'top> {
    expr_cache: &'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>],
    index: usize,
}

impl<'top> Iterator for BinaryEExpArgGroupIterator<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        let child_expr = self.expr_cache.get(self.index)?;
        self.index += 1;
        Some(Ok(*child_expr))
    }
}

impl<'top> IntoIterator for BinaryEExpArgGroup<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;
    type IntoIter = BinaryEExpArgGroupIterator<'top>;

    fn into_iter(self) -> Self::IntoIter {
        BinaryEExpArgGroupIterator {
            expr_cache: self.expr_cache,
            index: 0,
        }
    }
}

impl<'top> EExpressionArgGroup<'top, BinaryEncoding_1_1> for BinaryEExpArgGroup<'top> {
    fn encoding(&self) -> ParameterEncoding {
        self.parameter.encoding()
    }

    fn resolve(self, context: EncodingContextRef<'top>) -> ArgGroup<'top, BinaryEncoding_1_1> {
        ArgGroup::new(self, context)
    }
}

#[derive(Debug, Clone)]
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

#[derive(Debug, Clone)]
pub struct BinaryEExpArgsIterator_1_1<'top> {
    arg_exprs: &'top [EExpArg<'top, v1_1::Binary>],
    index: usize,
}

impl<'top> BinaryEExpArgsIterator_1_1<'top> {
    pub fn new(arg_exprs: &'top [EExpArg<'top, v1_1::Binary>]) -> Self {
        Self {
            arg_exprs,
            index: 0,
        }
    }
}

impl<'top> Iterator for BinaryEExpArgsIterator_1_1<'top> {
    type Item = IonResult<EExpArg<'top, v1_1::Binary>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.arg_exprs.get(self.index)?;
        self.index += 1;
        Some(Ok(*next_expr))
    }
}
