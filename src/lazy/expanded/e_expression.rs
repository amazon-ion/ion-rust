//! Types and traits representing an e-expression in an Ion stream.
#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::lazy::decoder::{Decoder, RawValueExpr};
use crate::lazy::encoding::TextEncoding_1_1;
use crate::lazy::expanded::compiler::{ExpansionAnalysis, ExpansionSingleton};
use crate::lazy::expanded::macro_evaluator::{
    AnnotateExpansion, EExpArgGroupIterator, EExpressionArgGroup, MacroExpansion,
    MacroExpansionKind, MacroExpr, MacroExprArgsIterator, MakeStringExpansion, RawEExpression,
    TemplateExpansion, ValueExpr, ValuesExpansion,
};
use crate::lazy::expanded::macro_table::{MacroKind, MacroRef};
use crate::lazy::expanded::template::TemplateMacroRef;
use crate::lazy::expanded::{EncodingContextRef, LazyExpandedValue};
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, EExpArgExpr};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::{try_next, Environment, HasRange, HasSpan, IonResult, Span};

/// An `ArgGroup` is a collection of expressions found in e-expression argument position.
/// They can only appear in positions that correspond with variadic parameters.
#[derive(Copy, Clone)]
pub struct ArgGroup<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    raw_arg_group: <D::EExp<'top> as RawEExpression<'top, D>>::ArgGroup,
    invoked_macro: MacroRef<'top>,
}

impl<'top, D: Decoder> ArgGroup<'top, D> {
    pub fn new(
        raw_arg_group: <D::EExp<'top> as RawEExpression<'top, D>>::ArgGroup,
        context: EncodingContextRef<'top>,
    ) -> Self {
        // While an `ArgGroup` is a distinct syntactic entity with its own role to play in the grammar,
        // once it has been read off the wire it behaves identically to a call to `(:values ...)`.
        // Each expression in the group is expanded and the resulting stream is concatenated to that
        // of the expression that proceeded it.
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
    pub fn expand(&self, environment: Environment<'top, D>) -> IonResult<MacroExpansion<'top, D>> {
        let context = self.context();
        let arguments = MacroExprArgsIterator::from_arg_group(self.expressions());
        let expansion_kind = MacroExpansionKind::Values(ValuesExpansion::new(arguments));
        Ok(MacroExpansion::new(context, environment, expansion_kind))
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

    pub(crate) fn expand(&self) -> IonResult<MacroExpansion<'top, D>> {
        let invoked_macro = self.invoked_macro;
        let arguments = MacroExprArgsIterator::from_eexp(self.arguments());

        let mut environment = Environment::empty();
        // Initialize a `MacroExpansionKind` with the state necessary to evaluate the requested
        // macro.
        let expansion_kind = match invoked_macro.kind() {
            MacroKind::Void => MacroExpansionKind::Void,
            MacroKind::Values => MacroExpansionKind::Values(ValuesExpansion::new(arguments)),
            MacroKind::MakeString => {
                MacroExpansionKind::MakeString(MakeStringExpansion::new(arguments))
            }
            MacroKind::Annotate => MacroExpansionKind::Annotate(AnnotateExpansion::new(arguments)),
            MacroKind::Template(template_body) => {
                let template_ref = TemplateMacroRef::new(invoked_macro, template_body);
                environment = self.new_evaluation_environment()?;
                MacroExpansionKind::Template(TemplateExpansion::new(template_ref))
            }
        };
        Ok(MacroExpansion::new(
            self.context(),
            environment,
            expansion_kind,
        ))
    }

    pub(crate) fn expand_to_single_value(&self) -> IonResult<LazyExpandedValue<'top, D>> {
        let environment = self.new_evaluation_environment()?;
        MacroExpansion::expand_singleton(MacroExpansion::initialize(
            environment,
            MacroExpr::from_eexp(*self),
        )?)
    }

    pub fn expansion_analysis(&self) -> ExpansionAnalysis {
        self.invoked_macro.expansion_analysis()
    }

    pub fn expansion_singleton(&self) -> Option<ExpansionSingleton> {
        self.expansion_analysis().expansion_singleton()
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
            num_args: self.invoked_macro.signature().len() as u32,
            index: 0,
        }
    }
}

impl<'top, D: Decoder> From<EExpression<'top, D>> for MacroExpr<'top, D> {
    fn from(value: EExpression<'top, D>) -> Self {
        MacroExpr::from_eexp(value)
    }
}

#[derive(Copy, Clone, Debug)]
pub struct EExpressionArgsIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    raw_args: <D::EExp<'top> as RawEExpression<'top, D>>::RawArgumentsIterator,
    // The number of argument expressions that the e-expr expects
    num_args: u32,
    // The index of the next argument to consider
    index: u32,
}

impl<'top, D: Decoder> EExpressionArgsIterator<'top, D> {
    pub fn is_exhausted(&self) -> bool {
        self.index == self.num_args
    }
}

impl<'top, D: Decoder> Iterator for EExpressionArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_arg: EExpArg<'top, D> = match self.raw_args.next()? {
            Ok(arg) => {
                debug_assert!(self.index < self.num_args);
                arg
            }
            Err(e) => {
                debug_assert!(self.index == self.num_args);
                return Some(Err(e));
            }
        };
        self.index += 1;

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

#[derive(Copy, Clone, Debug)]
pub struct ArgGroupIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    expressions: <<<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup as EExpressionArgGroup<'top, D>>::Iterator,
}

impl<'top, D: Decoder> ArgGroupIterator<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        arg_group: <<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup,
    ) -> Self {
        Self {
            context,
            expressions: arg_group.iter(),
        }
    }

    pub fn is_exhausted(&self) -> bool {
        self.expressions.is_exhausted()
    }
}

impl<'top, D: Decoder> Iterator for ArgGroupIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let expr = try_next!(self.expressions.next());
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
