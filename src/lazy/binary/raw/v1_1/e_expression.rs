#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::lazy::binary::raw::v1_1::immutable_buffer::{
    ArgGrouping, ArgGroupingBitmap, ArgGroupingBitmapIterator, ImmutableBuffer,
};
use crate::lazy::decoder::LazyRawValueExpr;
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::lazy::expanded::e_expression::ArgGroup;
use crate::lazy::expanded::macro_evaluator::{EExpressionArgGroup, RawEExpression};
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::template::{MacroSignature, Parameter, ParameterEncoding};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, EExpArgExpr};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::{v1_1, HasRange, HasSpan, IonResult, Span};

#[derive(Copy, Clone)]
pub struct EncodedBinaryEExp {
    // The number of bytes that were used to encode the e-expression's opcode.
    // This is 1+ in tagged contexts, and will be zero when the e-expression is used as a macro-shaped
    // argument.
    address_length: u8,
    // The number of bytes that were used to encode the e-expression's arg grouping bitmap, if any.
    bitmap_length: u8,
}

impl EncodedBinaryEExp {
    pub fn new(opcode_length: u8, bitmap_length: u8) -> Self {
        Self {
            address_length: opcode_length,
            bitmap_length,
        }
    }
    pub fn address_length(&self) -> usize {
        self.address_length as usize
    }
    pub fn bitmap_length(&self) -> usize {
        self.bitmap_length as usize
    }
    pub fn header_length(&self) -> usize {
        self.address_length() + self.bitmap_length()
    }
}

#[derive(Copy, Clone)]
pub struct RawBinaryEExpression_1_1<'top> {
    macro_ref: MacroRef<'top>,
    bitmap: ArgGroupingBitmap,
    pub(crate) input: ImmutableBuffer<'top>,
    encoded_eexp: EncodedBinaryEExp,
}

impl<'top> RawBinaryEExpression_1_1<'top> {
    pub fn new(
        macro_ref: MacroRef<'top>,
        bitmap: ArgGroupingBitmap,
        input: ImmutableBuffer<'top>,
        encoded_eexp: EncodedBinaryEExp,
    ) -> Self {
        Self {
            bitmap,
            input,
            macro_ref,
            encoded_eexp,
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

    fn id(self) -> MacroIdRef<'top> {
        MacroIdRef::LocalAddress(self.macro_ref.address())
    }

    fn raw_arguments(self) -> Self::RawArgumentsIterator<'top> {
        BinaryEExpArgsIterator_1_1::new(
            self.bitmap.iter(),
            self.input.consume(self.encoded_eexp.header_length()),
            self.macro_ref.signature(),
        )
    }
}

/// Early returns `Some(Err(_))` if the provided expression returns an `Err(_)`.
///
/// Acts as an ersatz `?` operator in methods that return `Option<IonResult<T>>`.
macro_rules! try_or_some_err {
    ($expr:expr) => {
        match $expr {
            Ok(v) => v,
            Err(e) => return Some(Err(e)),
        }
    };
}

pub(crate) use try_or_some_err;

#[derive(Debug, Clone)]
pub struct BinaryEExpArgsIterator_1_1<'top> {
    bitmap_iter: ArgGroupingBitmapIterator,
    remaining_args_buffer: ImmutableBuffer<'top>,
    signature: &'top MacroSignature,
    param_index: usize,
}

impl<'top> BinaryEExpArgsIterator_1_1<'top> {
    pub fn new(
        groupings_iter: ArgGroupingBitmapIterator,
        remaining_args_buffer: ImmutableBuffer<'top>,
        signature: &'top MacroSignature,
    ) -> Self {
        Self {
            bitmap_iter: groupings_iter,
            remaining_args_buffer,
            signature,
            param_index: 0,
        }
    }
}

impl<'top> Iterator for BinaryEExpArgsIterator_1_1<'top> {
    type Item = IonResult<EExpArg<'top, v1_1::Binary>>;

    fn next(&mut self) -> Option<Self::Item> {
        let parameter = self.signature.parameters().get(self.param_index)?;
        let arg_grouping = if parameter.is_variadic() {
            try_or_some_err!(self.bitmap_iter.next().unwrap())
        } else {
            ArgGrouping::ValueExprLiteral
        };
        // TODO: This code path actually, fully reads e-expressions. Change the IB.read_e_expr method
        //       to read as little of them as possible and return a BinEExpression
        let (arg_expr, remaining_input) = match arg_grouping {
            ArgGrouping::Empty => {
                let input = self.remaining_args_buffer.slice(0, 0);
                let expr = EExpArgExpr::ArgGroup(BinaryEExpArgGroup::new(parameter, input, 0));
                (EExpArg::new(parameter, expr), self.remaining_args_buffer)
            }
            ArgGrouping::ValueExprLiteral => {
                let (expr, remaining) = try_or_some_err! {
                    self
                        .remaining_args_buffer
                        .expect_eexp_arg_expr("reading tagged e-expr arg")
                };
                (EExpArg::new(parameter, expr), remaining)
            }
            ArgGrouping::ArgGroup => {
                let (group_header_flex_uint, mut remaining_args_input) =
                    try_or_some_err!(self.remaining_args_buffer.read_flex_uint());
                let bytes_to_read = match group_header_flex_uint.value() {
                    0 => todo!("delimited argument groups"),
                    n_bytes => n_bytes as usize,
                };
                let mut bytes_read = 0;
                // skip through the arg group to identify its span without fully reading it
                while bytes_read < bytes_to_read {
                    let (value_repr, remaining) = try_or_some_err! {
                        // remaining_args_input
                        //     .expect_sequence_value_expr("reading arg group, encoding=Tagged")
                        remaining_args_input.match_tagged_value_repr()
                    };
                    // let expr_length = value_expr.range().len();
                    remaining_args_input = remaining;
                    bytes_read += value_repr.len();
                }
                let arg_group_length = group_header_flex_uint.size_in_bytes() + bytes_to_read;
                let arg_group = BinaryEExpArgGroup::new(
                    parameter,
                    self.remaining_args_buffer.slice(0, arg_group_length),
                    group_header_flex_uint.size_in_bytes() as u8,
                );
                (
                    EExpArg::new(parameter, EExpArgExpr::ArgGroup(arg_group)),
                    remaining_args_input,
                )
            }
        };

        self.param_index += 1;
        self.remaining_args_buffer = remaining_input;
        Some(Ok(arg_expr))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let num_args = self.signature.parameters().len();
        // Tells the macro evaluator how much space to allocate to hold these arguments
        (num_args, Some(num_args))
    }
}

#[derive(Debug, Copy, Clone)]
pub struct BinaryEExpArgGroup<'top> {
    parameter: &'top Parameter,
    input: ImmutableBuffer<'top>,
    header_size: u8,
}

impl<'top> BinaryEExpArgGroup<'top> {
    pub fn new(parameter: &'top Parameter, input: ImmutableBuffer<'top>, header_size: u8) -> Self {
        Self {
            parameter,
            input,
            header_size,
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
    parameter: &'top Parameter,
    remaining_args_buffer: ImmutableBuffer<'top>,
}

impl<'top> Iterator for BinaryEExpArgGroupIterator<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.remaining_args_buffer.is_empty() {
            return None;
        }
        let (expr, remaining) = try_or_some_err! {
            // TODO: Other encodings
            self.remaining_args_buffer.expect_sequence_value_expr("eexp arg group subarg")
        };
        self.remaining_args_buffer = remaining;
        Some(Ok(expr))
    }
}

impl<'top> IntoIterator for BinaryEExpArgGroup<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;
    type IntoIter = BinaryEExpArgGroupIterator<'top>;

    fn into_iter(self) -> Self::IntoIter {
        BinaryEExpArgGroupIterator {
            parameter: self.parameter,
            remaining_args_buffer: self.input.consume(self.header_size as usize),
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
