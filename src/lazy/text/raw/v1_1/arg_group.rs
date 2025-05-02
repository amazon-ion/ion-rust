use std::ops::Range;

use crate::lazy::decoder::{LazyRawValueExpr, RawValueExpr};
use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::expanded::e_expression::EExpArgGroup;
use crate::lazy::expanded::macro_evaluator::{
    EExpressionArgGroup, IsExhaustedIterator, MacroExpr, RawEExpression, ValueExpr,
};
use crate::lazy::expanded::template::{Parameter, ParameterEncoding};
use crate::lazy::expanded::EncodingContextRef;
use crate::lazy::text::buffer::TextBuffer;
use crate::result::IonFailure;
use crate::{Decoder, HasRange, HasSpan, IonResult, LazyExpandedValue, Span};

#[derive(Copy, Clone, Debug)]
pub struct EExpArg<'top, D: Decoder> {
    parameter: &'top Parameter,
    expr: EExpArgExpr<'top, D>,
}

impl<'top, D: Decoder> EExpArg<'top, D> {
    pub fn new(parameter: &'top Parameter, expr: EExpArgExpr<'top, D>) -> Self {
        Self { parameter, expr }
    }

    pub fn encoding(&self) -> &'top Parameter {
        self.parameter
    }

    pub fn expr(&self) -> &EExpArgExpr<'top, D> {
        &self.expr
    }

    #[inline]
    pub fn resolve(&self, context: EncodingContextRef<'top>) -> IonResult<ValueExpr<'top, D>> {
        let value_expr = match self.expr {
            EExpArgExpr::ValueLiteral(value) => {
                ValueExpr::ValueLiteral(LazyExpandedValue::from_literal(context, value))
            }
            EExpArgExpr::EExp(eexp) => {
                ValueExpr::MacroInvocation(MacroExpr::from_eexp(eexp.resolve(context)?))
            }
            EExpArgExpr::ArgGroup(group) => {
                ValueExpr::MacroInvocation(MacroExpr::from_eexp_arg_group(group.resolve(context)))
            }
        };
        Ok(value_expr)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum EExpArgExpr<'top, D: Decoder> {
    ValueLiteral(<D as Decoder>::Value<'top>),
    EExp(<D as Decoder>::EExp<'top>),
    ArgGroup(<<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup),
}

impl<'top, D: Decoder> EExpArgExpr<'top, D> {
    pub fn expect_value(&self) -> IonResult<<D as Decoder>::Value<'top>> {
        let EExpArgExpr::ValueLiteral(value) = self else {
            return IonResult::decoding_error(format!("expected a value literal, found {self:?}"));
        };
        Ok(*value)
    }

    pub fn expect_eexp(&self) -> IonResult<<D as Decoder>::EExp<'top>> {
        let EExpArgExpr::EExp(eexp) = self else {
            return IonResult::decoding_error(format!("expected an e-expression, found {self:?}"));
        };
        Ok(*eexp)
    }

    pub fn expect_arg_group(
        &self,
    ) -> IonResult<<<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup> {
        let EExpArgExpr::ArgGroup(group) = self else {
            return IonResult::decoding_error(format!("expected an arg group, found {self:?}"));
        };
        Ok(*group)
    }
}

impl<'top, D: Decoder> From<LazyRawValueExpr<'top, D>> for EExpArgExpr<'top, D> {
    fn from(value: LazyRawValueExpr<'top, D>) -> Self {
        match value {
            RawValueExpr::ValueLiteral(v) => EExpArgExpr::ValueLiteral(v),
            RawValueExpr::EExp(e) => EExpArgExpr::EExp(e),
        }
    }
}

impl<D: Decoder> HasRange for EExpArgExpr<'_, D> {
    fn range(&self) -> Range<usize> {
        match self {
            EExpArgExpr::ValueLiteral(v) => v.range(),
            EExpArgExpr::EExp(e) => e.range(),
            EExpArgExpr::ArgGroup(a) => a.range(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TextEExpArgGroup<'top> {
    input: TextBuffer<'top>,
    parameter: &'top Parameter,
    // Notice that the expressions inside an arg group cannot themselves be arg groups,
    // only value literals or e-expressions.
    expr_cache: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
}

impl<'top> TextEExpArgGroup<'top> {
    pub fn new(
        parameter: &'top Parameter,
        input: TextBuffer<'top>,
        child_expr_cache: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
    ) -> Self {
        Self {
            input,
            parameter,
            expr_cache: child_expr_cache,
        }
    }
}

impl HasRange for TextEExpArgGroup<'_> {
    fn range(&self) -> Range<usize> {
        self.input.range()
    }
}

impl<'top> HasSpan<'top> for TextEExpArgGroup<'top> {
    fn span(&self) -> Span<'top> {
        Span::with_offset(self.input.offset(), self.input.bytes())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TextEExpArgGroupIterator<'top> {
    child_expr_cache: &'top [LazyRawValueExpr<'top, TextEncoding_1_1>],
    index: usize,
}

impl<'top> IsExhaustedIterator<'top, TextEncoding_1_1> for TextEExpArgGroupIterator<'top> {
    fn is_exhausted(&self) -> bool {
        self.index == self.child_expr_cache.len()
    }
}

impl<'top> Iterator for TextEExpArgGroupIterator<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;

    fn next(&mut self) -> Option<Self::Item> {
        let child_expr = self.child_expr_cache.get(self.index)?;
        self.index += 1;
        Some(Ok(*child_expr))
    }
}

impl<'top> IntoIterator for TextEExpArgGroup<'top> {
    type Item = IonResult<LazyRawValueExpr<'top, TextEncoding_1_1>>;
    type IntoIter = TextEExpArgGroupIterator<'top>;

    fn into_iter(self) -> Self::IntoIter {
        TextEExpArgGroupIterator {
            child_expr_cache: self.expr_cache,
            index: 0,
        }
    }
}

impl<'top> EExpressionArgGroup<'top, TextEncoding_1_1> for TextEExpArgGroup<'top> {
    type Iterator = TextEExpArgGroupIterator<'top>;

    fn encoding(&self) -> &ParameterEncoding {
        self.parameter.encoding()
    }

    fn resolve(self, context: EncodingContextRef<'top>) -> EExpArgGroup<'top, TextEncoding_1_1> {
        EExpArgGroup::new(self, context)
    }

    fn iter(self) -> Self::Iterator {
        self.into_iter()
    }
}
