//! Types and traits representing an e-expression in an Ion stream.
#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};
use std::ops::Range;

use bumpalo::collections::Vec as BumpVec;

use crate::lazy::decoder::{Decoder, RawValueExpr};
use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::expanded::compiler::{ExpansionAnalysis, ExpansionSingleton};
use crate::lazy::expanded::macro_evaluator::{
    EExpressionArgGroup, MacroEvaluator, MacroExpansionKind, MacroExpansionStep, MacroExpr,
    RawEExpression, ValueExpr,
};
use crate::lazy::expanded::macro_table::{MacroKind, MacroRef};
use crate::lazy::expanded::{EncodingContextRef, LazyExpandedValue};
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, EExpArgExpr};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::{Environment, HasRange, HasSpan, IonResult, Span};

#[derive(Copy, Clone)]
pub struct ArgGroup<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    raw_arg_group: <D::EExp<'top> as RawEExpression<'top, D>>::ArgGroup,
    invoked_macro: MacroRef<'top>,
}

// TODO: Explain link between ArgGroup and `values` macro
impl<'top, D: Decoder> ArgGroup<'top, D> {
    pub fn new(
        raw_arg_group: <D::EExp<'top> as RawEExpression<'top, D>>::ArgGroup,
        context: EncodingContextRef<'top>,
    ) -> Self {
        // TODO: Fully qualified, unambiguous ID
        const VALUES_MACRO_ID: MacroIdRef<'static> = MacroIdRef::LocalAddress(1);
        let invoked_macro = context
            .macro_table()
            .macro_with_id(VALUES_MACRO_ID)
            .expect("`values` must be available");
        Self {
            context,
            raw_arg_group,
            invoked_macro,
        }
    }
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
    pub fn raw_arg_group(&self) -> <D::EExp<'top> as RawEExpression<'top, D>>::ArgGroup {
        self.raw_arg_group
    }
    pub fn invoked_macro(&self) -> MacroRef<'top> {
        self.invoked_macro
    }
    pub fn expressions(&self) -> ArgGroupIterator<'top, D> {
        ArgGroupIterator::new(self.context, self.raw_arg_group())
    }
    pub fn new_evaluation_environment(&self) -> IonResult<Environment<'top, D>> {
        let allocator = self.context.allocator();
        let num_args = self.invoked_macro().signature().parameters().len();
        let mut env_exprs = BumpVec::with_capacity_in(num_args, allocator);
        // Populate the environment by parsing the arguments from input
        for expr in self.raw_arg_group() {
            let value_expr = match expr? {
                RawValueExpr::ValueLiteral(value) => {
                    ValueExpr::ValueLiteral(LazyExpandedValue::from_literal(self.context, value))
                }
                RawValueExpr::EExp(eexp) => {
                    ValueExpr::MacroInvocation(MacroExpr::from_eexp(eexp.resolve(self.context)?))
                }
            };
            env_exprs.push(value_expr);
        }
        Ok(Environment::new(env_exprs.into_bump_slice()))
    }
}

impl<'top, D: Decoder> HasRange for ArgGroup<'top, D> {
    fn range(&self) -> Range<usize> {
        self.raw_arg_group.range()
    }
}

impl<'top, D: Decoder> HasSpan<'top> for ArgGroup<'top, D> {
    fn span(&self) -> Span<'top> {
        self.raw_arg_group.span()
    }
}

impl<'top, D: Decoder> Debug for ArgGroup<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "ArgGroup {:?}", self.raw_arg_group)
    }
}

/// An e-expression (in Ion format `D`) that has been resolved in the current encoding context.
#[derive(Copy, Clone)]
pub struct EExpression<'top, D: Decoder> {
    pub(crate) context: EncodingContextRef<'top>,
    pub(crate) raw_invocation: D::EExp<'top>,
    pub(crate) invoked_macro: MacroRef<'top>,
}

impl<'top, D: Decoder> EExpression<'top, D> {
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
    pub fn raw_invocation(&self) -> D::EExp<'top> {
        self.raw_invocation
    }
    pub fn invoked_macro(&self) -> MacroRef<'top> {
        self.invoked_macro
    }

    pub(crate) fn new_evaluation_environment(&self) -> IonResult<Environment<'top, D>> {
        self.raw_invocation
            .make_evaluation_environment(self.context)
    }

    pub(crate) fn expand_to_single_value(&self) -> IonResult<LazyExpandedValue<'top, D>> {
        let (env, mut expansion) = match MacroEvaluator::expansion_for_singleton_template(*self) {
            Ok(expansion) => expansion,
            Err(e) => return Err(e),
        };
        match expansion.next(env) {
            Ok(MacroExpansionStep::FinalStep(Some(ValueExpr::ValueLiteral(value)))) => Ok(value),
            Err(e) => Err(e),
            _ => unreachable!("e-expression-backed lazy values must yield a single value literal"),
        }
    }

    pub fn expansion_analysis(&self) -> Option<ExpansionAnalysis> {
        if let MacroKind::Template(body) = self.invoked_macro().kind() {
            Some(body.expansion_analysis())
        } else {
            None
        }
    }

    pub fn expansion_singleton(&self) -> Option<ExpansionSingleton> {
        self.expansion_analysis()?.expansion_singleton()
    }
    /// Caller must guarantee that this e-expression invokes a template and that the template
    /// has a `ExpansionSingleton`. If these prerequisites are not met, this method will panic.
    pub fn require_expansion_singleton(&self) -> ExpansionSingleton {
        self.expansion_singleton().unwrap()
    }
}

impl<'top, D: Decoder> Debug for EExpression<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "EExpression {:?}", self.raw_invocation)
    }
}

impl<'top, D: Decoder> HasRange for EExpression<'top, D> {
    fn range(&self) -> Range<usize> {
        self.raw_invocation.range()
    }
}

impl<'top, D: Decoder> HasSpan<'top> for EExpression<'top, D> {
    fn span(&self) -> Span<'top> {
        self.raw_invocation.span()
    }
}

impl<'top, D: Decoder> EExpression<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
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

impl<'top, D: Decoder> EExpression<'top, D> {
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

impl<'top, D: Decoder> From<EExpression<'top, D>> for MacroExpr<'top, D> {
    fn from(value: EExpression<'top, D>) -> Self {
        MacroExpr::from_eexp(value)
    }
}

pub struct EExpressionArgsIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    raw_args: <D::EExp<'top> as RawEExpression<'top, D>>::RawArgumentsIterator,
}

impl<'top, D: Decoder> Iterator for EExpressionArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_arg: EExpArg<'top, D> = match self.raw_args.next()? {
            Ok(arg) => arg,
            Err(e) => return Some(Err(e)),
        };

        let expr = match raw_arg.expr() {
            EExpArgExpr::<D>::ValueLiteral(value) => {
                ValueExpr::ValueLiteral(LazyExpandedValue::from_literal(self.context, *value))
            }
            EExpArgExpr::<D>::EExp(raw_invocation) => {
                let invocation = match raw_invocation.resolve(self.context) {
                    Ok(invocation) => invocation,
                    Err(e) => return Some(Err(e)),
                };
                ValueExpr::MacroInvocation(invocation.into())
            }
            EExpArgExpr::<D>::ArgGroup(group) => {
                let arg_group = group.resolve(self.context);
                ValueExpr::MacroInvocation(MacroExpr::from_eexp_arg_group(arg_group))
            }
        };
        Some(Ok(expr))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.raw_args.size_hint()
    }
}

pub type TextEExpression_1_1<'top> = EExpression<'top, TextEncoding_1_1>;

pub struct ArgGroupIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    expressions: <<<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup as IntoIterator>::IntoIter,
}

impl<'top, D: Decoder> ArgGroupIterator<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        arg_group: <<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup,
    ) -> Self {
        Self {
            context,
            expressions: arg_group.into_iter(),
        }
    }
}

impl<'top, D: Decoder> Iterator for ArgGroupIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let expr = match self.expressions.next() {
            None => return None,
            Some(Err(e)) => return Some(Err(e)),
            Some(Ok(expr)) => expr,
        };
        match expr {
            RawValueExpr::ValueLiteral(v) => Some(Ok(ValueExpr::ValueLiteral(
                LazyExpandedValue::from_literal(self.context, v),
            ))),
            RawValueExpr::EExp(e) => {
                let resolved_eexp = match e.resolve(self.context) {
                    Ok(eexp) => eexp,
                    Err(e) => return Some(Err(e)),
                };
                Some(Ok(ValueExpr::MacroInvocation(MacroExpr::from_eexp(
                    resolved_eexp,
                ))))
            }
        }
    }
}
