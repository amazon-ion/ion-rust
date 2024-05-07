//! Types and traits representing an e-expression in an Ion stream.
#![allow(non_camel_case_types)]

use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr};
use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::expanded::macro_evaluator::{MacroExpr, RawEExpression, ValueExpr};
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::{EncodingContext, LazyExpandedValue};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::IonResult;
use std::fmt::{Debug, Formatter};

/// An e-expression (in Ion format `D`) that has been resolved in the current encoding context.
#[derive(Copy, Clone)]
pub struct EExpression<'top, D: LazyDecoder> {
    pub(crate) context: EncodingContext<'top>,
    pub(crate) raw_invocation: D::EExp<'top>,
    pub(crate) invoked_macro: MacroRef<'top>,
}

impl<'top, D: LazyDecoder> EExpression<'top, D> {
    pub fn raw_invocation(&self) -> D::EExp<'top> {
        self.raw_invocation
    }
    pub fn invoked_macro(&self) -> MacroRef<'top> {
        self.invoked_macro
    }
}

impl<'top, D: LazyDecoder> Debug for EExpression<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "EExpression {:?}", self.raw_invocation)
    }
}

impl<'top, D: LazyDecoder> EExpression<'top, D> {
    pub fn new(
        context: EncodingContext<'top>,
        raw_invocation: D::EExp<'top>,
        invoked_macro: MacroRef<'top>,
    ) -> Self {
        Self {
            context,
            raw_invocation,
            invoked_macro,
        }
    }
}

impl<'top, D: LazyDecoder> EExpression<'top, D> {
    pub fn id(&self) -> MacroIdRef<'top> {
        self.raw_invocation.id()
    }

    pub fn arguments(&self) -> EExpressionArgsIterator<'top, D> {
        EExpressionArgsIterator {
            context: self.context,
            raw_args: self.raw_invocation.raw_arguments(),
        }
    }
}

impl<'top, D: LazyDecoder> From<EExpression<'top, D>> for MacroExpr<'top, D> {
    fn from(value: EExpression<'top, D>) -> Self {
        MacroExpr::EExp(value)
    }
}

pub struct EExpressionArgsIterator<'top, D: LazyDecoder> {
    context: EncodingContext<'top>,
    raw_args: <D::EExp<'top> as RawEExpression<'top, D>>::RawArgumentsIterator<'top>,
}

impl<'top, D: LazyDecoder> Iterator for EExpressionArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_arg: LazyRawValueExpr<'top, D> = match self.raw_args.next()? {
            Ok(arg) => arg,
            Err(e) => return Some(Err(e)),
        };

        let expr = match raw_arg {
            LazyRawValueExpr::<D>::ValueLiteral(value) => {
                ValueExpr::ValueLiteral(LazyExpandedValue::from_literal(self.context, value))
            }
            LazyRawValueExpr::<D>::MacroInvocation(raw_invocation) => {
                let invocation = match raw_invocation.resolve(self.context) {
                    Ok(invocation) => invocation,
                    Err(e) => return Some(Err(e)),
                };
                ValueExpr::MacroInvocation(invocation.into())
            }
        };
        Some(Ok(expr))
    }
}

pub type TextEExpression_1_1<'top> = EExpression<'top, TextEncoding_1_1>;
