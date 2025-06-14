//! Types and traits representing an e-expression in an Ion stream.
#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};
use std::ops::Range;

use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::{Decoder, RawValueExpr};
use crate::lazy::expanded::compiler::{ExpansionAnalysis, ExpansionSingleton};
use crate::lazy::expanded::macro_evaluator::{
    AnnotateExpansion, ConditionalExpansion, EExpressionArgGroup, ExprGroupExpansion,
    FlattenExpansion, IsExhaustedIterator, MacroExpansion, MacroExpansionKind, MacroExpr,
    MacroExprArgsIterator, MakeFieldExpansion, MakeStructExpansion, MakeTextExpansion,
    RawEExpression, RepeatExpansion, TemplateExpansion, ValueExpr,
};
use crate::lazy::expanded::macro_table::{MacroKind, MacroRef};
use crate::lazy::expanded::template::TemplateMacroRef;
use crate::lazy::expanded::{EncodingContextRef, LazyExpandedValue};
use crate::lazy::text::raw::v1_1::arg_group::{EExpArg, EExpArgExpr};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::{try_next, try_or_some_err, Environment, HasRange, HasSpan, IonResult, Span};

/// An `ArgGroup` is a collection of expressions found in e-expression argument position.
/// They can only appear in positions that correspond with variadic parameters.
#[derive(Copy, Clone)]
pub struct EExpArgGroup<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    raw_arg_group: <D::EExp<'top> as RawEExpression<'top, D>>::ArgGroup,
}

impl<'top, D: Decoder> EExpArgGroup<'top, D> {
    pub fn new(
        raw_arg_group: <D::EExp<'top> as RawEExpression<'top, D>>::ArgGroup,
        context: EncodingContextRef<'top>,
    ) -> Self {
        Self {
            context,
            raw_arg_group,
        }
    }
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
    pub fn raw_arg_group(&self) -> <D::EExp<'top> as RawEExpression<'top, D>>::ArgGroup {
        self.raw_arg_group
    }
    pub fn expressions(&self) -> EExpArgGroupIterator<'top, D> {
        EExpArgGroupIterator::new(self.context, self.raw_arg_group())
    }
    pub fn expand(&self) -> IonResult<MacroExpansion<'top, D>> {
        let context = self.context();
        let arguments = MacroExprArgsIterator::from_eexp_arg_group(self.expressions());
        let expansion_kind = MacroExpansionKind::ExprGroup(ExprGroupExpansion::new(arguments));
        Ok(MacroExpansion::new(
            context,
            Environment::empty(),
            expansion_kind,
        ))
    }
}

impl<D: Decoder> HasRange for EExpArgGroup<'_, D> {
    fn range(&self) -> Range<usize> {
        self.raw_arg_group.range()
    }
}

impl<'top, D: Decoder> HasSpan<'top> for EExpArgGroup<'top, D> {
    fn span(&self) -> Span<'top> {
        self.raw_arg_group.span()
    }
}

impl<D: Decoder> Debug for EExpArgGroup<'_, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "(: {:?}", self.raw_arg_group)?;
        for expr in self.expressions() {
            write!(f, " {:?}", expr)?;
        }
        write!(f, ")")
    }
}

/// An e-expression (in Ion format `D`) that has been resolved in the current encoding context.
#[derive(Copy, Clone)]
pub struct EExpression<'top, D: Decoder> {
    pub(crate) raw_invocation: D::EExp<'top>,
    pub(crate) invoked_macro: MacroRef<'top>,
}

impl<'top, D: Decoder> EExpression<'top, D> {
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.raw_invocation().context()
    }
    pub fn raw_invocation(&self) -> D::EExp<'top> {
        self.raw_invocation
    }
    pub fn invoked_macro(&self) -> MacroRef<'top> {
        self.invoked_macro
    }

    pub(crate) fn new_evaluation_environment(&self) -> IonResult<Environment<'top, D>> {
        self.raw_invocation
            .make_evaluation_environment(self.context())
    }

    pub(crate) fn expand(&self) -> IonResult<MacroExpansion<'top, D>> {
        let invoked_macro = self.invoked_macro;
        let arguments = MacroExprArgsIterator::from_eexp(self.arguments());

        let mut environment = Environment::empty();
        // Initialize a `MacroExpansionKind` with the state necessary to evaluate the requested
        // macro.
        let expansion_kind = match invoked_macro.kind() {
            MacroKind::None => MacroExpansionKind::None,
            MacroKind::ExprGroup => {
                MacroExpansionKind::ExprGroup(ExprGroupExpansion::new(arguments))
            }
            MacroKind::MakeString => {
                MacroExpansionKind::MakeString(MakeTextExpansion::string_maker(arguments))
            }
            MacroKind::MakeSymbol => {
                MacroExpansionKind::MakeSymbol(MakeTextExpansion::symbol_maker(arguments))
            }
            MacroKind::MakeStruct => {
                MacroExpansionKind::MakeStruct(MakeStructExpansion::new(arguments))
            }
            MacroKind::MakeField => {
                MacroExpansionKind::MakeField(MakeFieldExpansion::new(arguments))
            }
            MacroKind::Annotate => MacroExpansionKind::Annotate(AnnotateExpansion::new(arguments)),
            MacroKind::Flatten => MacroExpansionKind::Flatten(FlattenExpansion::new(
                self.context(),
                environment,
                arguments,
            )),
            MacroKind::Template(template_body) => {
                let template_ref = TemplateMacroRef::new(invoked_macro.definition(), template_body);
                environment = self.new_evaluation_environment()?;
                MacroExpansionKind::Template(TemplateExpansion::new(template_ref))
            }
            MacroKind::ToDo => todo!("system macro {}", invoked_macro.name().unwrap()),
            MacroKind::IfNone => {
                MacroExpansionKind::Conditional(ConditionalExpansion::if_none(arguments))
            }
            MacroKind::IfSome => {
                MacroExpansionKind::Conditional(ConditionalExpansion::if_some(arguments))
            }
            MacroKind::IfSingle => {
                MacroExpansionKind::Conditional(ConditionalExpansion::if_single(arguments))
            }
            MacroKind::IfMulti => {
                MacroExpansionKind::Conditional(ConditionalExpansion::if_multi(arguments))
            }
            MacroKind::Repeat => {
                MacroExpansionKind::Repeat(RepeatExpansion::new(arguments))
            }
        };
        Ok(MacroExpansion::new(
            self.context(),
            environment,
            expansion_kind,
        ))
    }

    pub(crate) fn expand_to_single_value(&self) -> IonResult<LazyExpandedValue<'top, D>> {
        MacroExpr::from_eexp(*self).expand()?.expand_singleton()
    }

    pub fn expansion_analysis(&self) -> ExpansionAnalysis {
        self.invoked_macro.expansion_analysis()
    }

    /// Returns `true` if this `EExpression` was statically determined to always return exactly
    /// one value. If this method returns `false`, no assertion about the expansion's cardinality
    /// is made--the evaluation may still produce one value.
    pub fn is_singleton(&self) -> bool {
        self.expansion_singleton().is_some()
    }

    pub fn expansion_singleton(&self) -> Option<ExpansionSingleton> {
        self.expansion_analysis().expansion_singleton()
    }

    /// Returns the `ExpansionSingleton` describing the template expansion information that was
    /// inferred from the macro compilation process.
    ///
    /// Caller must guarantee that this e-expression invokes a template and that the template
    /// has a `ExpansionSingleton`. If these prerequisites are not met, this method will panic.
    pub fn require_expansion_singleton(&self) -> ExpansionSingleton {
        self.expansion_singleton().unwrap()
    }

    /// Returns the annotations that this template expansion will produce, as inferred from the
    /// macro compilation process.
    ///
    /// Caller must guarantee that this e-expression invokes a template and that the template
    /// has a `ExpansionSingleton`. If these prerequisites are not met, this method will panic.
    pub fn require_singleton_annotations(&self) -> SymbolsIterator<'top> {
        let storage = self
            .invoked_macro
            .require_template()
            .body()
            .annotations_storage();
        self.expansion_singleton().unwrap().annotations(storage)
    }
}

impl<D: Decoder> Debug for EExpression<'_, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "(:{}",
            self.invoked_macro().name().unwrap_or("<anonymous>")
        )?;
        for arg in self.arguments() {
            write!(f, " {:?}", arg?)?;
        }
        write!(f, ")")
    }
}

impl<D: Decoder> HasRange for EExpression<'_, D> {
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
    pub fn new(raw_invocation: D::EExp<'top>, invoked_macro: MacroRef<'top>) -> Self {
        Self {
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
            context: self.context(),
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

impl<D: Decoder> EExpressionArgsIterator<'_, D> {
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

#[derive(Copy, Clone, Debug)]
pub struct EExpArgGroupIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    expressions: <<<D as Decoder>::EExp<'top> as RawEExpression<'top, D>>::ArgGroup as EExpressionArgGroup<'top, D>>::Iterator,
}

impl<'top, D: Decoder> EExpArgGroupIterator<'top, D> {
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

impl<'top, D: Decoder> Iterator for EExpArgGroupIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_expr: RawValueExpr<_, _> = try_next!(self.expressions.next());
        let expr = try_or_some_err!(raw_expr.resolve(self.context));
        Some(Ok(expr))
    }
}
