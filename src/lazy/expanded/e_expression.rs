//! Types and traits representing an e-expression in an Ion stream.
#![allow(non_camel_case_types)]

use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr};
use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::expanded::macro_evaluator::{ArgumentExpr, MacroExpr, RawEExpression};
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::{EncodingContext, LazyExpandedValue};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::IonResult;
use std::fmt::{Debug, Formatter};

/// An e-expression (in Ion format `D`) that has been resolved in the current encoding context.
#[derive(Copy, Clone)]
pub struct EExpression<'top, 'data, D: LazyDecoder<'data>> {
    pub(crate) context: EncodingContext<'top>,
    pub(crate) raw_invocation: D::EExpression,
    pub(crate) invoked_macro: MacroRef<'top>,
}

impl<'top, 'data, D: LazyDecoder<'data>> Debug for EExpression<'top, 'data, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "EExpression {:?}", self.raw_invocation)
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> EExpression<'top, 'data, D> {
    pub fn new(
        context: EncodingContext<'top>,
        raw_invocation: D::EExpression,
        invoked_macro: MacroRef<'top>,
    ) -> Self {
        Self {
            context,
            raw_invocation,
            invoked_macro,
        }
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> EExpression<'top, 'data, D> {
    pub fn id(&self) -> MacroIdRef<'top> {
        self.raw_invocation.id()
    }

    pub fn arguments(&self) -> EExpressionArgsIterator<'top, 'data, D> {
        EExpressionArgsIterator {
            context: self.context,
            raw_args: self.raw_invocation.raw_arguments(),
        }
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> From<EExpression<'top, 'data, D>>
    for MacroExpr<'top, 'data, D>
{
    fn from(value: EExpression<'top, 'data, D>) -> Self {
        MacroExpr::EExp(value)
    }
}

pub struct EExpressionArgsIterator<'top, 'data, D: LazyDecoder<'data>> {
    context: EncodingContext<'top>,
    raw_args: <D::EExpression as RawEExpression<'data, D>>::RawArgumentsIterator<'data>,
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> Iterator
    for EExpressionArgsIterator<'top, 'data, D>
{
    type Item = IonResult<ArgumentExpr<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_arg: LazyRawValueExpr<'data, D> = match self.raw_args.next()? {
            Ok(arg) => arg,
            Err(e) => return Some(Err(e)),
        };

        let expr = match raw_arg {
            LazyRawValueExpr::<D>::ValueLiteral(value) => {
                ArgumentExpr::ValueLiteral(LazyExpandedValue::from_value(self.context, value))
            }
            LazyRawValueExpr::<D>::MacroInvocation(raw_invocation) => {
                let invocation = match raw_invocation.resolve(self.context) {
                    Ok(invocation) => invocation,
                    Err(e) => return Some(Err(e)),
                };
                ArgumentExpr::MacroInvocation(invocation.into())
            }
        };
        Some(Ok(expr))
    }
}

pub type TextEExpression_1_1<'top, 'data> = EExpression<'top, 'data, TextEncoding_1_1>;
