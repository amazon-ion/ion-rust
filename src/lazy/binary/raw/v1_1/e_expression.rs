#![allow(non_camel_case_types)]

use crate::lazy::binary::raw::v1_1::binary_buffer::{
    ArgGrouping, ArgGroupingBitmapIterator, BinaryBuffer,
};
use crate::lazy::binary::raw::v1_1::value::DelimitedContents;
use crate::lazy::decoder::LazyRawValueExpr;
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::lazy::expanded::e_expression::EExpArgGroup;
use crate::lazy::expanded::macro_evaluator::{EExpressionArgGroup, RawEExpression, ValueExpr};
use crate::lazy::expanded::macro_evaluator::{IsExhaustedIterator, MacroExprKind};
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::template::{MacroSignature, Parameter, ParameterEncoding};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, EExpArgExpr};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::{try_or_some_err, v1_1, Environment, HasRange, HasSpan, IonResult, Span};
use std::fmt::{Debug, Formatter};
use std::ops::Range;

/// An e-expression which has been parsed from a binary Ion 1.1 stream.
#[derive(Copy, Clone)]
pub struct BinaryEExpression_1_1<'top> {
    // The arguments to the e-expression are parsed either:
    //
    //   1. when the e-expression is first encountered, if it is not length-prefixed.
    //     OR
    //   2. when the e-expression is being evaluated, to populate its evaluation environment.
    //
    // In case #1, we store the parsed arguments in the bump allocator so that we don't have to
    // re-parse them at evaluation time. We _could_ store the `LazyRawValueExpr<'top, BinaryEncoding_1_1>`
    // representations of the expressions, but then we would need to make a separate array of the
    // resolved versions of those expressions (`ValueExpr<'top, BinaryEncoding_1_1>`) to populate
    // the environment. As an optimization, we store the fully resolved version of the arguments
    // so that populating the environment is very close to a no-op. In the uncommon case that we need
    // to iterate over the raw argument expressions (usually for tooling), we can do so by
    // "unpacking" their resolved representations. See `make_evaluation_environment` for details.
    cache: Option<&'top [ValueExpr<'top, BinaryEncoding_1_1>]>,
    macro_ref: MacroRef<'top>,
    bitmap_bits: u64,
    // This index is the first position after the opcode and address.
    // If the e-expression has a length prefix, it will begin at this position in `input`.
    length_offset: u8,
    // This index is the first position after the opcode, address, and length prefix.
    // If the e-expression has a bitmap, it will begin at this position in `input`.
    bitmap_offset: u8,
    // This index is the first position after the opcode, address, length, and bitmap.
    // If the e-expression has arguments, they will begin at this position in `input`.
    args_offset: u8,

    pub(crate) input: BinaryBuffer<'top>,
}

impl<'top> BinaryEExpression_1_1<'top> {
    pub fn new(
        macro_ref: MacroRef<'top>,
        bitmap_bits: u64,
        input: BinaryBuffer<'top>,
        length_offset: u8,
        bitmap_offset: u8,
        args_offset: u8,
    ) -> Self {
        Self {
            bitmap_bits,
            input,
            macro_ref,
            length_offset,
            bitmap_offset,
            args_offset,
            cache: None,
        }
    }

    pub(crate) fn with_arg_expr_cache(
        mut self,
        cache: &'top [ValueExpr<'top, BinaryEncoding_1_1>],
    ) -> Self {
        self.cache = Some(cache);
        self
    }

    /// Returns a span of bytes representing the opcode and macro address.
    /// Depending on the encoding, these may be distinct (for example, the span: `0xF4 0x01`,
    /// where the `0xF4` is the opcode and the `0x01` is the `FlexUInt` address) or combined
    /// (for example: `0x00` is both an opcode and a macro address).
    pub fn opcode_and_address_span(&self) -> Span<'top> {
        self.input.slice(0, self.length_offset as usize).into()
    }

    /// Returns `true` if this binary e-expression includes a length prefix.
    pub fn has_length_prefix(&self) -> bool {
        // If these offsets are equal, there are no bytes representing the length.
        self.length_offset != self.bitmap_offset
    }

    /// Returns a span of bytes representing the length prefix. If there is no length prefix,
    /// the returned span will be empty.
    pub fn length_prefix_span(&self) -> Span<'top> {
        let num_bytes = (self.bitmap_offset - self.length_offset) as usize;
        self.input
            .slice(self.length_offset as usize, num_bytes)
            .into()
    }

    /// Returns `true` if this binary e-expression includes an argument encoding bitmap.
    pub fn has_bitmap(&self) -> bool {
        // If these offsets are equal, there are no bytes representing the bitmap.
        self.bitmap_offset != self.args_offset
    }

    /// Returns a span of bytes representing the e-expression's argument encoding bitmap.
    /// If there is no argument encoding bitmap, the returned span will be empty.
    pub fn bitmap_span(&self) -> Span<'top> {
        let num_bytes = (self.args_offset - self.bitmap_offset) as usize;
        self.input
            .slice(self.bitmap_offset as usize, num_bytes)
            .into()
    }
}

impl<'top> HasSpan<'top> for &'top BinaryEExpression_1_1<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

impl<'top> HasRange for &'top BinaryEExpression_1_1<'top> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> Debug for &'top BinaryEExpression_1_1<'top> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<e-expression invoking id '{}'>", self.id())
    }
}

impl<'top> RawEExpression<'top, v1_1::Binary> for &'top BinaryEExpression_1_1<'top> {
    type RawArgumentsIterator = BinaryEExpArgsIterator_1_1<'top>;
    type ArgGroup = BinaryEExpArgGroup<'top>;

    fn id(self) -> MacroIdRef<'top> {
        self.macro_ref.id()
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator {
        let signature = self.macro_ref.signature();
        let args_input = self.input.consume(self.args_offset as usize);
        if let Some(cache) = self.cache {
            return BinaryEExpArgsIterator_1_1::for_cache(signature, args_input.offset(), cache);
        }
        let bitmap_iterator = ArgGroupingBitmapIterator::new(signature.len(), self.bitmap_bits);
        BinaryEExpArgsIterator_1_1::for_input(bitmap_iterator, args_input, signature)
    }

    fn context(&self) -> EncodingContextRef<'top> {
        self.input.context()
    }

    fn make_evaluation_environment(
        &self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<Environment<'top, BinaryEncoding_1_1>> {
        // If we've already parsed and resolved the e-expression's arguments, use our cache as the
        // new environment.
        if let Some(cache) = self.cache {
            return Ok(Environment::new(cache));
        }
        // Otherwise, we parse the arguments and add them to a new environment as we go.
        // Note that (as currently designed) we cannot then populate the cache as we do not have
        // a mutable reference to `self` and getting one would be a non-trivial change. However,
        // in the vast majority of use cases, e-expressions are not evaluated more than once, which
        // means that populating the cache would be of little value.
        Environment::for_eexp(context, *self)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum BinaryEExpArgsSource<'top> {
    // If the e-expression arguments were parsed when it was first encountered, their resolved
    // representations are stored in a bump-allocated array. This iterator kind will iterate over
    // the array.
    Cache(BinaryEExpArgsCacheIter<'top>),
    // If the e-expression was length-prefixed, the cache will not be populated. This iterator kind
    // will incrementally parse the contents of the buffer range identified by the length prefix.
    Input(BinaryEExpArgsInputIter<'top>),
}

#[derive(Debug, Copy, Clone)]
pub struct BinaryEExpArgsIterator_1_1<'top> {
    source: BinaryEExpArgsSource<'top>,
}

impl<'top> BinaryEExpArgsIterator_1_1<'top> {
    pub fn for_input(
        groupings_iter: ArgGroupingBitmapIterator,
        remaining_args_buffer: BinaryBuffer<'top>,
        signature: &'top MacroSignature,
    ) -> Self {
        Self {
            source: BinaryEExpArgsSource::Input(BinaryEExpArgsInputIter {
                bitmap_iter: groupings_iter,
                remaining_args_buffer,
                param_index: 0,
                signature,
            }),
        }
    }

    pub fn for_cache(
        signature: &'top MacroSignature,
        initial_offset: usize,
        cache: &'top [ValueExpr<'top, BinaryEncoding_1_1>],
    ) -> Self {
        Self {
            source: BinaryEExpArgsSource::Cache(BinaryEExpArgsCacheIter {
                cache_exprs: cache,
                initial_offset,
                expr_index: 0,
                signature,
            }),
        }
    }

    /// Reports the position of the iterator within the overall stream. Before `next()` has been
    /// called for the first time, the position will be the first offset after the
    /// opcode/address/length/bitmap. When the iterator is exhausted, the position will be
    /// the first offset beyond the end of the e-expression.
    pub fn offset(&self) -> usize {
        match &self.source {
            BinaryEExpArgsSource::Input(i) => i.remaining_args_buffer.offset(),
            // If there weren't any args, then the iterator's position is where it started.
            BinaryEExpArgsSource::Cache(c) if c.cache_exprs.is_empty() => c.initial_offset,
            BinaryEExpArgsSource::Cache(c) => {
                match c.cache_exprs.get(c.expr_index) {
                    Some(value_expr) => value_expr.range().unwrap().end,
                    // If the iterator is exhausted, then its offset is the end of the last arg expr.
                    None => c.cache_exprs[c.expr_index - 1].range().unwrap().end,
                }
            }
        }
    }
}

impl<'top> Iterator for BinaryEExpArgsIterator_1_1<'top> {
    type Item = IonResult<EExpArg<'top, v1_1::Binary>>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        match self.source {
            BinaryEExpArgsSource::Input(ref mut input_iter) => input_iter.next(),
            BinaryEExpArgsSource::Cache(ref mut cache_iter) => cache_iter.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let signature = match self.source {
            BinaryEExpArgsSource::Input(i) => i.signature,
            BinaryEExpArgsSource::Cache(i) => i.signature,
        };
        let num_args = signature.len();
        // Tells the macro evaluator how much space to allocate to hold these arguments
        (num_args, Some(num_args))
    }
}

/// An iterator that incrementally parses e-expression arguments from a provided buffer.
#[derive(Debug, Copy, Clone)]
pub struct BinaryEExpArgsInputIter<'top> {
    bitmap_iter: ArgGroupingBitmapIterator,
    remaining_args_buffer: BinaryBuffer<'top>,
    param_index: usize,
    signature: &'top MacroSignature,
}

impl<'top> Iterator for BinaryEExpArgsInputIter<'top> {
    type Item = IonResult<EExpArg<'top, v1_1::Binary>>;

    #[inline(always)]
    fn next(&mut self) -> Option<IonResult<EExpArg<'top, v1_1::Binary>>> {
        // We cannot read the arguments of a binary e-expression without first looking at the
        // corresponding parameter's encoding and cardinality to know what bytes to expect.
        // First, get the parameter from the signature. If `get` returns `None`, we've reached the
        // end of the signature and can early-return.
        let parameter = self.signature.parameters().get(self.param_index)?;
        let arg_grouping = if parameter.is_variadic() {
            // If it's a variadic parameter (that is: `?`, `*`, or `+`), pull two bits from the
            // argument encoding bitmap to see how it was encoded.
            try_or_some_err!(self.bitmap_iter.next().unwrap())
        } else {
            // If it's a required parameter (`!`, or no modifier), there's no corresponding entry in the
            // argument encoding bitmap.
            ArgGrouping::ValueExprLiteral
        };
        // TODO: More tagless encodings
        let (arg_expr, remaining_input) = match arg_grouping {
            // If the encoding is `empty`, there's nothing to do. Make an empty slice at the current
            // offset and build an empty BinaryEExpArgGroup with it.
            ArgGrouping::Empty => {
                let input = self.remaining_args_buffer.slice(0, 0);
                let expr = EExpArgExpr::ArgGroup(BinaryEExpArgGroup::new(parameter, input, 0));
                (EExpArg::new(parameter, expr), self.remaining_args_buffer)
            }
            // It's a single expression; we'll need to look at the parameter's declared encoding.
            ArgGrouping::ValueExprLiteral => match parameter.encoding() {
                // The encoding starts with an opcode.
                ParameterEncoding::Tagged => {
                    let (expr, remaining) = try_or_some_err! {
                        self
                        .remaining_args_buffer
                        .expect_eexp_arg_expr("reading tagged e-expr arg")
                    };
                    (EExpArg::new(parameter, expr), remaining)
                }
                // It's a FlexUInt.
                ParameterEncoding::FlexUInt => {
                    let (flex_uint_lazy_value, remaining) = try_or_some_err! {
                        self.remaining_args_buffer.read_flex_uint_as_lazy_value()
                    };
                    let value_ref = &*self
                        .remaining_args_buffer
                        .context()
                        .allocator()
                        .alloc_with(|| flex_uint_lazy_value);
                    (
                        EExpArg::new(parameter, EExpArgExpr::ValueLiteral(value_ref)),
                        remaining,
                    )
                }
                ParameterEncoding::UInt8 => {
                    let (fixed_uint_lazy_value, remaining) = try_or_some_err! {
                        self.remaining_args_buffer.read_fixed_uint_as_lazy_value(1)
                    };
                    let value_ref = &*self
                        .remaining_args_buffer
                        .context()
                        .allocator()
                        .alloc_with(|| fixed_uint_lazy_value);
                    (
                        EExpArg::new(parameter, EExpArgExpr::ValueLiteral(value_ref)),
                        remaining,
                    )
                }
                ParameterEncoding::UInt16 => {
                    let (fixed_uint_lazy_value, remaining) = try_or_some_err! {
                        self.remaining_args_buffer.read_fixed_uint_as_lazy_value(2)
                    };
                    let value_ref = &*self
                        .remaining_args_buffer
                        .context()
                        .allocator()
                        .alloc_with(|| fixed_uint_lazy_value);
                    (
                        EExpArg::new(parameter, EExpArgExpr::ValueLiteral(value_ref)),
                        remaining,
                    )
                }
                ParameterEncoding::UInt32 => {
                    let (fixed_uint_lazy_value, remaining) = try_or_some_err! {
                        self.remaining_args_buffer.read_fixed_uint_as_lazy_value(4)
                    };
                    let value_ref = &*self
                        .remaining_args_buffer
                        .context()
                        .allocator()
                        .alloc_with(|| fixed_uint_lazy_value);
                    (
                        EExpArg::new(parameter, EExpArgExpr::ValueLiteral(value_ref)),
                        remaining,
                    )
                }
                ParameterEncoding::UInt64 => {
                    let (fixed_uint_lazy_value, remaining) = try_or_some_err! {
                        self.remaining_args_buffer.read_fixed_uint_as_lazy_value(8)
                    };
                    let value_ref = &*self
                        .remaining_args_buffer
                        .context()
                        .allocator()
                        .alloc_with(|| fixed_uint_lazy_value);
                    (
                        EExpArg::new(parameter, EExpArgExpr::ValueLiteral(value_ref)),
                        remaining,
                    )
                }
                ParameterEncoding::MacroShaped(_macro_ref) => {
                    todo!("macro-shaped parameter encoding")
                } // TODO: The other tagless encodings
            },
            // If it's an argument group...
            ArgGrouping::ArgGroup => {
                //...then it starts with a FlexUInt that indicates whether the group is length-prefixed
                // or delimited.
                let (group_header_flex_uint, remaining_args_input) =
                    try_or_some_err!(self.remaining_args_buffer.read_flex_uint());
                match group_header_flex_uint.value() {
                    // A FlexUInt of `0` indicates that the arg group is delimited.
                    // We need to step through it to determine its span.
                    0 if *parameter.encoding() == ParameterEncoding::Tagged => {
                        // Read the delimited sequence of tagged expressions, caching them as we go.
                        let (delimited_contents, remaining) =
                            try_or_some_err!(remaining_args_input.peek_delimited_sequence_body());
                        let DelimitedContents::Values(delimited_values) = delimited_contents else {
                            unreachable!("parser found a delimited arg group")
                        };
                        // Isolate the part of the input buffer that represented the argument group.
                        let matched_buffer = self
                            .remaining_args_buffer
                            .slice(0, remaining.offset() - self.remaining_args_buffer.offset());
                        let arg_group = BinaryEExpArgGroup::new(
                            parameter,
                            matched_buffer,
                            // Make a note of the leading FlexUInt header size so we can skip it later.
                            group_header_flex_uint.size_in_bytes() as u8,
                        )
                        .with_delimited_values(delimited_values);
                        (
                            EExpArg::new(parameter, EExpArgExpr::ArgGroup(arg_group)),
                            remaining,
                        )
                    }
                    0 => todo!("delimited argument groups for untagged encodings"),
                    // The arg group is length-prefixed; we don't need to inspect its contents yet.
                    // We can build an ArgGroup using the unexamined bytes;
                    // we'll parse them later if they get evaluated.
                    n_bytes => {
                        let bytes_to_read = n_bytes as usize;
                        let arg_group_length =
                            group_header_flex_uint.size_in_bytes() + bytes_to_read;
                        let arg_group = BinaryEExpArgGroup::new(
                            parameter,
                            self.remaining_args_buffer.slice(0, arg_group_length),
                            group_header_flex_uint.size_in_bytes() as u8,
                        );
                        (
                            EExpArg::new(parameter, EExpArgExpr::ArgGroup(arg_group)),
                            self.remaining_args_buffer.consume(arg_group_length),
                        )
                    }
                }
            }
        };

        self.param_index += 1;
        self.remaining_args_buffer = remaining_input;
        Some(Ok(arg_expr))
    }
}

/// An iterator that visits already-resolved `ValueExpr`s stored in an array.
#[derive(Debug, Copy, Clone)]
pub struct BinaryEExpArgsCacheIter<'top> {
    initial_offset: usize,
    cache_exprs: &'top [ValueExpr<'top, BinaryEncoding_1_1>],
    expr_index: usize,
    signature: &'top MacroSignature,
}

impl<'top> BinaryEExpArgsCacheIter<'top> {
    pub fn next(&mut self) -> Option<IonResult<EExpArg<'top, v1_1::Binary>>> {
        let parameter = self.signature.parameters().get(self.expr_index)?;
        let cache_entry = self.cache_exprs.get(self.expr_index).unwrap();
        self.expr_index += 1;
        let next_expr = match cache_entry {
            ValueExpr::ValueLiteral(value) => {
                // We know that every ValueExpr in the cache is the resolved version of a raw value
                // literal, so we can safely `unwrap` here.
                let value_literal = value.expect_value_literal().unwrap();
                EExpArg::new(parameter, EExpArgExpr::ValueLiteral(value_literal))
            }
            ValueExpr::MacroInvocation(invocation) => {
                use MacroExprKind::*;
                let expr = match invocation.source() {
                    TemplateMacro(_) | TemplateArgGroup(_) => {
                        unreachable!("e-expression cannot be a TDL construct")
                    }
                    EExp(eexp) => EExpArgExpr::EExp(eexp.raw_invocation),
                    EExpArgGroup(group) => EExpArgExpr::ArgGroup(group.raw_arg_group()),
                };
                EExpArg::new(parameter, expr)
            }
        };
        Some(Ok(next_expr))
    }
}

#[derive(Debug, Copy, Clone)]
pub struct BinaryEExpArgGroup<'top> {
    parameter: &'top Parameter,
    input: BinaryBuffer<'top>,
    header_size: u8,
    // If this is a delimited arg group, this cache will hold the expressions found during parsing.
    delimited_values: Option<&'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>]>,
}

impl<'top> BinaryEExpArgGroup<'top> {
    pub fn new(parameter: &'top Parameter, input: BinaryBuffer<'top>, header_size: u8) -> Self {
        Self {
            parameter,
            input,
            header_size,
            delimited_values: None,
        }
    }

    pub fn with_delimited_values(
        mut self,
        delimited_values: &'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>],
    ) -> Self {
        self.delimited_values = Some(delimited_values);
        self
    }

    pub fn header_span(&self) -> Span<'_> {
        let header_input = self.input.slice(0, self.header_size as usize);
        Span::from(header_input)
    }
}

impl HasRange for BinaryEExpArgGroup<'_> {
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
    source: BinaryEExpArgGroupIteratorSource<'top>,
}

#[derive(Debug, Copy, Clone)]
enum BinaryEExpArgGroupIteratorSource<'top> {
    /// The iterator is parsing expressions from a slice of the input buffer.
    Input(BinaryBuffer<'top>),
    /// The iterator is iterating over the bump-allocated cache of previously parsed expressions.
    Cache(&'top [LazyRawValueExpr<'top, BinaryEncoding_1_1>]),
}

impl<'top> IsExhaustedIterator<'top, BinaryEncoding_1_1> for BinaryEExpArgGroupIterator<'top> {
    fn is_exhausted(&self) -> bool {
        match self.source {
            BinaryEExpArgGroupIteratorSource::Input(ref input) => input.is_empty(),
            BinaryEExpArgGroupIteratorSource::Cache(cache) => cache.is_empty(),
        }
    }
}

impl<'top> Iterator for BinaryEExpArgGroupIterator<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.source {
            BinaryEExpArgGroupIteratorSource::Input(ref mut input) => {
                if input.is_empty() {
                    return None;
                }
                let (expr, remaining) = try_or_some_err! {
                    // TODO: Other encodings
                    input.expect_sequence_value_expr("eexp arg group subarg")
                };
                *input = remaining;
                Some(Ok(expr))
            }
            BinaryEExpArgGroupIteratorSource::Cache(ref mut cache) => {
                let expr = cache.first()?;
                *cache = &cache[1..];
                Some(Ok(*expr))
            }
        }
    }
}

impl<'top> IntoIterator for BinaryEExpArgGroup<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, BinaryEncoding_1_1>>;
    type IntoIter = BinaryEExpArgGroupIterator<'top>;

    fn into_iter(self) -> Self::IntoIter {
        let source = match self.delimited_values {
            None => BinaryEExpArgGroupIteratorSource::Input(
                self.input.consume(self.header_size as usize),
            ),
            Some(delimited_values) => BinaryEExpArgGroupIteratorSource::Cache(delimited_values),
        };
        BinaryEExpArgGroupIterator { source }
    }
}

impl<'top> EExpressionArgGroup<'top, BinaryEncoding_1_1> for BinaryEExpArgGroup<'top> {
    type Iterator = BinaryEExpArgGroupIterator<'top>;

    fn encoding(&self) -> &ParameterEncoding {
        self.parameter.encoding()
    }

    fn resolve(self, context: EncodingContextRef<'top>) -> EExpArgGroup<'top, BinaryEncoding_1_1> {
        EExpArgGroup::new(self, context)
    }

    fn iter(self) -> Self::Iterator {
        self.into_iter()
    }
}

#[derive(Debug, Clone)]
pub struct RawBinarySequenceCacheIterator_1_1<'top> {
    child_exprs: &'top [LazyRawValueExpr<'top, v1_1::Binary>],
    index: usize,
}

impl<'top> Iterator for RawBinarySequenceCacheIterator_1_1<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, v1_1::Binary>>;

    fn next(&mut self) -> Option<Self::Item> {
        let next_expr = self.child_exprs.get(self.index)?;
        self.index += 1;
        Some(Ok(*next_expr))
    }
}
