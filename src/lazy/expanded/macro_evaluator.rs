//! Traits and types to evaluate e-expressions and template macro invocations.
//!
//! Macro invocations can appear in two different contexts:
//!   1. As an *encoding expression* (e-expression) in the data stream. In text Ion, this is written
//!      out using `(:macro_id param1 param2 [...] paramN)` syntax. E-expressions can be found
//!      anywhere that an Ion value literal can appear, including nested within containers or as
//!      arguments to other e-expressions.
//!   2. As an unquoted s-expression within the body of a template macro.
//!
//! The evaluation logic is the same for macros in both contexts, though there are differences in
//! encoding and argument handling that must be considered. For more information, see the
//! documentation for the types below.
#![allow(non_camel_case_types)]

use std::fmt::{Debug, Formatter};
use std::mem;
use std::ops::Range;

use bumpalo::collections::{String as BumpString, Vec as BumpVec};

use crate::lazy::decoder::{Decoder, HasSpan, LazyRawValueExpr};
use crate::lazy::expanded::compiler::ExpansionAnalysis;
use crate::lazy::expanded::e_expression::{
    EExpArgGroup, EExpArgGroupIterator, EExpression, EExpressionArgsIterator,
};
use crate::lazy::expanded::sequence::{Environment, ExpandedSequenceIterator};
use crate::lazy::expanded::template::{
    ParameterEncoding, TemplateExprGroup, TemplateMacroInvocation,
    TemplateMacroInvocationArgsIterator, TemplateMacroRef,
};
use crate::lazy::expanded::LazyExpandedValue;
use crate::lazy::expanded::{EncodingContextRef, TemplateVariableReference};
use crate::lazy::str_ref::StrRef;
use crate::lazy::text::raw::v1_1::arg_group::EExpArg;
use crate::lazy::text::raw::v1_1::reader::{MacroIdLike, MacroIdRef};
use crate::result::IonFailure;
use crate::{
    Decimal, ExpandedValueRef, ExpandedValueSource, Int, IonError, IonResult,
    LazyExpandedField, LazyExpandedFieldName, LazyExpandedStruct, LazyStruct,
    LazyValue, Span, SymbolRef, ValueRef
};
use crate::types::{HasDay, HasFractionalSeconds, HasHour, HasMinute, HasMonth, HasOffset, HasSeconds, HasYear, Timestamp, TimestampBuilder};

pub trait IsExhaustedIterator<'top, D: Decoder>:
    Copy + Clone + Debug + Iterator<Item = IonResult<LazyRawValueExpr<'top, D>>>
{
    /// Returns `true` if the iterator is known to be out of arguments to return.
    /// Implementations are permitted to return `false` if they are uncertain whether more arguments
    /// are available. After the iterator returns `None` for the first time, this method must return
    /// `true` when called.
    fn is_exhausted(&self) -> bool;
}

pub trait EExpressionArgGroup<'top, D: Decoder>:
    HasSpan<'top>
    + Debug
    + Copy
    + Clone
    + IntoIterator<Item = IonResult<LazyRawValueExpr<'top, D>>, IntoIter = Self::Iterator>
{
    type Iterator: IsExhaustedIterator<'top, D>;

    fn encoding(&self) -> &ParameterEncoding;
    fn resolve(self, context: EncodingContextRef<'top>) -> EExpArgGroup<'top, D>;

    fn iter(self) -> Self::Iterator {
        self.into_iter()
    }
}

/// The syntactic entity in format `D` that represents an e-expression. This expression has not
/// yet been resolved in the current encoding context.
pub trait RawEExpression<'top, D: Decoder<EExp<'top> = Self>>:
    HasSpan<'top> + Debug + Copy + Clone
where
    Self: 'top,
{
    /// An iterator that yields the macro invocation's arguments in order.
    type RawArgumentsIterator: Debug + Copy + Clone + Iterator<Item = IonResult<EExpArg<'top, D>>>;

    /// A type that represents an argument group--several expressions that form a stream
    /// passed as a single argument.
    type ArgGroup: EExpressionArgGroup<'top, D>;

    /// The macro name or address specified at the head of this macro invocation.
    fn id(self) -> MacroIdRef<'top>;

    /// The arguments that follow the macro name or address in this macro invocation.
    fn raw_arguments(&self) -> Self::RawArgumentsIterator;

    fn context(&self) -> EncodingContextRef<'top>;

    /// Looks up the macro invoked by this E-expression in the given `EncodingContext`.
    /// If the lookup is successful, returns an `Ok` containing a resolved `EExpression` that holds
    /// a reference to the macro being invoked.
    /// If the ID cannot be found in the `EncodingContext`, returns `Err`.
    #[inline]
    fn resolve(self, context: EncodingContextRef<'top>) -> IonResult<EExpression<'top, D>> {
        let invoked_macro = self.id().resolve(context.macro_table())?;
        Ok(EExpression::new(self, invoked_macro))
    }

    /// Returns an array of resolved [`ValueExpr`] instances that can be evaluated and/or passed
    /// as arguments to other macro invocations.
    fn make_evaluation_environment(
        &self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<Environment<'top, D>> {
        Environment::for_eexp(context, *self)
    }
}

/// An invocation of a macro found in either the data stream or in the body of a template.
/// This invocation has been resolved in the current encoding context, and holds a reference to
/// the definition of the macro being invoked.
#[derive(Copy, Clone)]
pub struct MacroExpr<'top, D: Decoder> {
    kind: MacroExprKind<'top, D>,
    pub(crate) variable: Option<TemplateVariableReference<'top>>,
}

impl<D: Decoder> Debug for MacroExpr<'_, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}

impl<'top, D: Decoder> MacroExpr<'top, D> {
    pub fn kind(&self) -> MacroExprKind<'top, D> {
        self.kind
    }
}

impl<'top, D: Decoder> MacroExpr<'top, D> {
    pub fn new(source: MacroExprKind<'top, D>) -> Self {
        Self {
            kind: source,
            variable: None,
        }
    }

    pub fn via_variable(mut self, variable_ref: Option<TemplateVariableReference<'top>>) -> Self {
        self.variable = variable_ref;
        self
    }

    pub fn expand(&self) -> IonResult<MacroExpansion<'top, D>> {
        match self.kind {
            MacroExprKind::TemplateMacro(t) => t.expand(),
            MacroExprKind::TemplateArgGroup(g) => g.expand(),
            MacroExprKind::EExp(e) => e.expand(),
            MacroExprKind::EExpArgGroup(g) => g.expand(),
        }
        .map(|expansion| expansion.via_variable(self.variable))
    }

    pub fn range(&self) -> Option<Range<usize>> {
        self.span().as_ref().map(Span::range)
    }

    /// If this `ValueExpr` represents an entity encoded in the data stream, returns `Some(range)`.
    /// If it represents an ephemeral value produced by a macro evaluation, returns `None`.
    pub fn span(&self) -> Option<Span<'top>> {
        use MacroExprKind::*;
        match self.kind {
            TemplateMacro(_) | TemplateArgGroup(_) => None,
            EExp(eexp) => Some(eexp.span()),
            EExpArgGroup(group) => Some(group.span()),
        }
    }

    pub fn is_eexp(&self) -> bool {
        matches!(self.kind, MacroExprKind::EExp(_))
    }

    pub fn is_tdl_macro(&self) -> bool {
        matches!(self.kind, MacroExprKind::TemplateMacro(_))
    }

    pub fn is_singleton(&self) -> bool {
        match &self.kind {
            MacroExprKind::TemplateMacro(m) => m.invoked_macro().must_produce_exactly_one_value(),
            MacroExprKind::EExp(e) => e.invoked_macro().must_produce_exactly_one_value(),
            _ => false,
        }
    }
}

#[derive(Copy, Clone)]
pub enum MacroExprKind<'top, D: Decoder> {
    /// A macro invocation found in the body of a template.
    TemplateMacro(TemplateMacroInvocation<'top, D>),
    /// An argument group found in the body of a template.
    TemplateArgGroup(TemplateExprGroup<'top, D>),
    /// A macro invocation found in the data stream.
    EExp(EExpression<'top, D>),
    /// An e-expression argument group. (A `values` call with special encoding.)
    EExpArgGroup(EExpArgGroup<'top, D>),
}

impl<D: Decoder> Debug for MacroExprKind<'_, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            MacroExprKind::TemplateMacro(t) => write!(f, "{t:?}"),
            MacroExprKind::TemplateArgGroup(g) => write!(f, "{g:?}"),
            MacroExprKind::EExp(e) => write!(f, "{e:?}"),
            MacroExprKind::EExpArgGroup(g) => write!(f, "{g:?}"),
        }
    }
}

impl<'top, D: Decoder> MacroExpr<'top, D> {
    pub fn from_template_macro(invocation: TemplateMacroInvocation<'top, D>) -> Self {
        MacroExpr::new(MacroExprKind::TemplateMacro(invocation))
    }

    pub fn from_template_expr_group(template_arg_group: TemplateExprGroup<'top, D>) -> Self {
        MacroExpr::new(MacroExprKind::TemplateArgGroup(template_arg_group))
    }

    pub fn from_eexp(eexp: EExpression<'top, D>) -> Self {
        MacroExpr::new(MacroExprKind::EExp(eexp))
    }

    pub fn from_eexp_arg_group(group: EExpArgGroup<'top, D>) -> Self {
        MacroExpr::new(MacroExprKind::EExpArgGroup(group))
    }

    pub fn variable(&self) -> Option<TemplateVariableReference<'top>> {
        self.variable
    }

    pub fn source(&self) -> MacroExprKind<'top, D> {
        self.kind
    }

    pub fn arguments(&self) -> MacroExprArgsIterator<'top, D> {
        use MacroExprKind::*;
        let args_kind = match &self.kind {
            TemplateMacro(m) => MacroExprArgsKind::<'top, D>::TemplateMacro(m.arguments()),
            TemplateArgGroup(g) => MacroExprArgsKind::<'top, D>::TemplateArgGroup(g.arguments()),
            EExp(e) => MacroExprArgsKind::<'top, D>::EExp(e.arguments()),
            EExpArgGroup(group) => MacroExprArgsKind::<'top, D>::EExpArgGroup(group.expressions()),
        };
        MacroExprArgsIterator { source: args_kind }
    }

    pub(crate) fn expansion_analysis(&self) -> ExpansionAnalysis {
        use MacroExprKind::*;
        match &self.kind {
            TemplateMacro(m) => m.invoked_macro().expansion_analysis(),
            EExp(e) => e.invoked_macro().definition().expansion_analysis(),
            // Argument groups are a low-level construct; they do not invoke a proper macro.
            // They always produce the default expansion analysis.
            TemplateArgGroup(_) | EExpArgGroup(_) => ExpansionAnalysis::default(),
        }
    }

    /// Returns an [`ExpansionCardinality`] indicating whether this macro invocation will expand
    /// to a stream that is empty, a singleton, or multiple values.
    pub(crate) fn expansion_cardinality(
        &self,
        environment: Environment<'top, D>,
    ) -> IonResult<ExpansionCardinality> {
        // If we've statically determined this to produce exactly one value,
        // the expansion cardinality must be `Single`.
        if self.expansion_analysis().must_produce_exactly_one_value() {
            return Ok(ExpansionCardinality::Single);
        }
        // If it's an empty arg group, the expansion cardinality is `None`.
        let is_empty = match self.kind() {
            MacroExprKind::EExpArgGroup(group) => group.expressions().next().is_none(),
            MacroExprKind::TemplateArgGroup(group) => group.arg_expressions().is_empty(),
            _ => false,
        };
        if is_empty {
            return Ok(ExpansionCardinality::None);
        }

        // Otherwise, we need to begin expanding the invocation to see how many values it will produce.
        let mut evaluator = MacroEvaluator::new_with_environment(environment);
        evaluator.push(self.expand()?);
        if evaluator.next()?.is_none() {
            return Ok(ExpansionCardinality::None);
        }
        if evaluator.next()?.is_none() {
            return Ok(ExpansionCardinality::Single);
        }
        Ok(ExpansionCardinality::Multi)
    }
}

#[derive(Copy, Clone, Debug)]
pub enum MacroExprArgsKind<'top, D: Decoder> {
    TemplateMacro(TemplateMacroInvocationArgsIterator<'top, D>),
    TemplateArgGroup(TemplateMacroInvocationArgsIterator<'top, D>),
    EExp(EExpressionArgsIterator<'top, D>),
    EExpArgGroup(EExpArgGroupIterator<'top, D>),
}

#[derive(Copy, Clone, Debug)]
pub struct MacroExprArgsIterator<'top, D: Decoder> {
    source: MacroExprArgsKind<'top, D>,
}

impl<'top, D: Decoder> MacroExprArgsIterator<'top, D> {
    pub fn from_eexp(args: EExpressionArgsIterator<'top, D>) -> Self {
        MacroExprArgsIterator {
            source: MacroExprArgsKind::EExp(args),
        }
    }

    pub fn from_template_macro(args: TemplateMacroInvocationArgsIterator<'top, D>) -> Self {
        MacroExprArgsIterator {
            source: MacroExprArgsKind::TemplateMacro(args),
        }
    }

    pub fn from_template_arg_group(args: TemplateMacroInvocationArgsIterator<'top, D>) -> Self {
        MacroExprArgsIterator {
            source: MacroExprArgsKind::TemplateArgGroup(args),
        }
    }

    pub fn from_eexp_arg_group(args: EExpArgGroupIterator<'top, D>) -> Self {
        MacroExprArgsIterator {
            source: MacroExprArgsKind::EExpArgGroup(args),
        }
    }

    pub fn is_exhausted(&self) -> bool {
        match self.source {
            MacroExprArgsKind::TemplateMacro(ref args) => args.is_exhausted(),
            MacroExprArgsKind::TemplateArgGroup(ref args) => args.is_exhausted(),
            MacroExprArgsKind::EExp(ref args) => args.is_exhausted(),
            MacroExprArgsKind::EExpArgGroup(ref args) => args.is_exhausted(),
        }
    }
}

impl<'top, D: Decoder> Iterator for MacroExprArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.source {
            MacroExprArgsKind::TemplateMacro(m) => m.next(),
            MacroExprArgsKind::TemplateArgGroup(g) => g.next(),
            MacroExprArgsKind::EExp(e) => e.next(),
            MacroExprArgsKind::EExpArgGroup(g) => g.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.source {
            MacroExprArgsKind::TemplateMacro(m) => m.size_hint(),
            MacroExprArgsKind::TemplateArgGroup(g) => g.size_hint(),
            MacroExprArgsKind::EExp(e) => e.size_hint(),
            MacroExprArgsKind::EExpArgGroup(g) => g.size_hint(),
        }
    }
}

/// A value expression (i.e. value literal or macro invocation) found in any context.
///
/// A `ValueExpr` is a resolved value. It cannot be a variable reference. If it is a macro
/// invocation, it holds a reference to the definition of the macro it invokes.
#[derive(Copy, Clone)]
pub enum ValueExpr<'top, D: Decoder> {
    /// An Ion value that requires no further evaluation.
    // `LazyExpandedValue` can be backed by either a stream value or a template value, so it covers
    // both contexts.
    ValueLiteral(LazyExpandedValue<'top, D>),
    /// A macro invocation that requires evaluation.
    MacroInvocation(MacroExpr<'top, D>),
}

impl<D: Decoder> Debug for ValueExpr<'_, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ValueExpr::ValueLiteral(v) => write!(f, "value={v:?}"),
            ValueExpr::MacroInvocation(i) => write!(f, "invocation={i:?}"),
        }
    }
}

impl<'top, D: Decoder> ValueExpr<'top, D> {
    pub fn via_variable(
        self,
        template_variable_ref: Option<TemplateVariableReference<'top>>,
    ) -> Self {
        use ValueExpr::*;
        match self {
            ValueLiteral(value) => ValueLiteral(value.via_variable(template_variable_ref)),
            MacroInvocation(invocation) => {
                MacroInvocation(invocation.via_variable(template_variable_ref))
            }
        }
    }

    /// Like [`evaluate_singleton_in`](Self::evaluate_singleton_in), but uses an empty environment.
    pub fn evaluate_singleton(&self) -> IonResult<LazyExpandedValue<'top, D>> {
        self.evaluate_singleton_in(Environment::empty())
    }

    /// Evaluates this `ValueExpr` in the context of the provided `environment`, producing either
    /// an `Ok` containing the expansion's sole `LazyExpandedValue`, or an `Err` indicating that
    /// this expression expanded to zero or two+ values.
    pub fn evaluate_singleton_in(
        &self,
        environment: Environment<'top, D>,
    ) -> IonResult<LazyExpandedValue<'top, D>> {
        let invocation = match self {
            // If it's a single value, we're already done.
            ValueExpr::ValueLiteral(v) => return Ok(*v),
            ValueExpr::MacroInvocation(i) => *i,
        };
        let expansion = invocation.expand()?;
        // If it's a macro that we know will produce exactly one value, evaluate it without a stack.
        if invocation
            .expansion_analysis()
            .must_produce_exactly_one_value()
        {
            return expansion.expand_singleton();
        }
        // Otherwise, use the general case macro evaluator.
        let mut evaluator = MacroEvaluator::new_with_environment(environment);
        evaluator.push(expansion);
        let Some(value) = evaluator.next()? else {
            return IonResult::decoding_error(
                "expected macro to produce exactly one value but it produced none",
            );
        };
        if evaluator.next()?.is_some() {
            return IonResult::decoding_error(
                "expected macro to produce exactly one value but it produced more than one",
            );
        }
        Ok(value)
    }

    pub fn expect_value_literal(&self) -> IonResult<LazyExpandedValue<'top, D>> {
        match self {
            ValueExpr::ValueLiteral(value) => Ok(*value),
            _ => {
                IonResult::decoding_error("expected a value literal, but found a macro invocation")
            }
        }
    }

    pub fn expect_macro_invocation(&self) -> IonResult<MacroExpr<'top, D>> {
        match self {
            ValueExpr::MacroInvocation(invocation) => Ok(*invocation),
            _ => {
                IonResult::decoding_error("expected a macro invocation, but found a value literal")
            }
        }
    }

    /// Returns `true` if this expression was produced by evaluating a macro. Otherwise, returns `false`.
    pub fn is_ephemeral(&self) -> bool {
        match self {
            ValueExpr::ValueLiteral(value) => value.is_ephemeral(),
            ValueExpr::MacroInvocation(invocation) => {
                use MacroExprKind::*;
                match invocation.kind() {
                    TemplateMacro(_) | TemplateArgGroup(_) => true,
                    EExp(_) | EExpArgGroup(_) => false,
                }
            }
        }
    }

    /// If this `ValueExpr` represents an entity encoded in the data stream, returns `Some(range)`.
    /// If it represents a template value or a constructed value, returns `None`.
    pub fn range(&self) -> Option<Range<usize>> {
        self.span().as_ref().map(Span::range)
    }

    /// If this `ValueExpr` represents an entity encoded in the data stream, returns `Some(range)`.
    /// If it represents an ephemeral value produced by a macro evaluation, returns `None`.
    pub fn span(&self) -> Option<Span<'top>> {
        match self {
            ValueExpr::ValueLiteral(value) => {
                use ExpandedValueSource::*;
                match value.source {
                    SingletonEExp(eexp) => Some(eexp.span()),
                    ValueLiteral(literal) => Some(literal.span()),
                    Template(_, _) | Constructed(_, _) => None,
                }
            }
            ValueExpr::MacroInvocation(e) => {
                use MacroExprKind::*;
                match e.source() {
                    TemplateMacro(_) | TemplateArgGroup(_) => None,
                    EExp(e) => Some(e.span()),
                    EExpArgGroup(g) => Some(g.span()),
                }
            }
        }
    }
}

/// Indicates which of the supported macros this represents and stores the state necessary to
/// continue evaluating that macro.
#[derive(Debug)]
pub enum MacroExpansionKind<'top, D: Decoder> {
    None, // `(.none)` returns the empty stream
    ExprGroup(ExprGroupExpansion<'top, D>),
    MakeDecimal(MakeDecimalExpansion<'top, D>),
    MakeString(MakeTextExpansion<'top, D>),
    MakeSymbol(MakeTextExpansion<'top, D>),
    MakeStruct(MakeStructExpansion<'top, D>),
    MakeTimestamp(MakeTimestampExpansion<'top, D>),
    MakeField(MakeFieldExpansion<'top, D>),
    Annotate(AnnotateExpansion<'top, D>),
    Flatten(FlattenExpansion<'top, D>),
    Template(TemplateExpansion<'top>),
    // `if_none`, `if_single`, `if_multi`
    Conditional(ConditionalExpansion<'top, D>),
    Delta(DeltaExpansion<'top, D>),
    Repeat(RepeatExpansion<'top, D>),
    Sum(SumExpansion<'top, D>),
}

pub enum ExpansionCardinality {
    None,
    Single,
    Multi,
}

/// A macro in the process of being evaluated. Stores both the state of the evaluation and the
/// syntactic element that represented the macro invocation.
pub struct MacroExpansion<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    kind: MacroExpansionKind<'top, D>,
    environment: Environment<'top, D>,
    is_complete: bool,
    variable_ref: Option<TemplateVariableReference<'top>>,
}

impl<'top, D: Decoder> MacroExpansion<'top, D> {
    pub fn via_variable(mut self, variable_ref: Option<TemplateVariableReference<'top>>) -> Self {
        self.variable_ref = variable_ref;
        self
    }

    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }

    /// Expands the current macro with the expectation that it will produce exactly one value.
    /// For more information about singleton macros, see
    /// [`ExpansionSingleton`](crate::lazy::expanded::compiler::ExpansionSingleton).
    #[inline(always)]
    pub(crate) fn expand_singleton(mut self) -> IonResult<LazyExpandedValue<'top, D>> {
        // We don't need to construct an evaluator because this is guaranteed to produce exactly
        // one value.
        match self.next_step()? {
            MacroExpansionStep::FinalStep(Some(ValueExpr::ValueLiteral(value))) => Ok(value),
            // If the expansion produces anything other than a final value, there's a bug.
            _ => unreachable!("expansion of {self:?} was required to produce exactly one value"),
        }
    }

    pub(crate) fn new(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        kind: MacroExpansionKind<'top, D>,
    ) -> Self {
        Self {
            environment,
            kind,
            context,
            is_complete: false,
            variable_ref: None,
        }
    }

    /// Continues evaluating this macro until it:
    ///   * produces another value.
    ///   * encounters another macro or variable that needs to be expanded.
    ///   * is completed.
    #[inline(always)]
    pub fn next_step(&mut self) -> IonResult<MacroExpansionStep<'top, D>> {
        use MacroExpansionKind::*;
        let context = self.context;
        let environment = self.environment;
        // Delegate the call to `next()` based on the macro kind.
        match &mut self.kind {
            Template(template_expansion) => template_expansion.next(context, environment),
            ExprGroup(expr_group_expansion) => expr_group_expansion.next(context, environment),
            MakeDecimal(make_decimal_expansion) => make_decimal_expansion.next(context, environment),
            MakeString(expansion) | MakeSymbol(expansion) => expansion.make_text_value(context),
            MakeField(make_field_expansion) => make_field_expansion.next(context, environment),
            MakeStruct(make_struct_expansion) => make_struct_expansion.next(context, environment),
            MakeTimestamp(make_timestamp_expansion) => make_timestamp_expansion.next(context, environment),
            Annotate(annotate_expansion) => annotate_expansion.next(context, environment),
            Flatten(flatten_expansion) => flatten_expansion.next(),
            Conditional(cardinality_test_expansion) => cardinality_test_expansion.next(environment),
            Delta(delta_expansion) => delta_expansion.next(context),
            Repeat(repeat_expansion) => repeat_expansion.next(environment),
            Sum(sum_expansion) => sum_expansion.next(context, environment),
            // `none` is trivial and requires no delegation
            None => Ok(MacroExpansionStep::FinalStep(Option::None)),
        }
        .map(|expansion| expansion.via_variable(self.variable_ref))
    }
}

impl<D: Decoder> Debug for MacroExpansion<'_, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let name = match &self.kind {
            MacroExpansionKind::None => "none",
            MacroExpansionKind::ExprGroup(_) => "[internal] expr_group",
            MacroExpansionKind::MakeDecimal(_) => "make_decimal",
            MacroExpansionKind::MakeString(_) => "make_string",
            MacroExpansionKind::MakeSymbol(_) => "make_symbol",
            MacroExpansionKind::MakeField(_) => "make_field",
            MacroExpansionKind::MakeStruct(_) => "make_struct",
            MacroExpansionKind::MakeTimestamp(_) => "make_timestamp",
            MacroExpansionKind::Annotate(_) => "annotate",
            MacroExpansionKind::Flatten(_) => "flatten",
            MacroExpansionKind::Delta(_) => "delta",
            MacroExpansionKind::Repeat(_) => "repeat",
            MacroExpansionKind::Sum(_) => "sum",
            MacroExpansionKind::Conditional(test) => test.name(),
            MacroExpansionKind::Template(t) => {
                return if let Some(name) = t.template.name() {
                    write!(f, "<expansion of template '{name}'>")
                } else {
                    write!(f, "<expansion of anonymous template>")
                }
            }
        };
        write!(f, "<expansion of {name}>")
    }
}

#[derive(Copy, Clone, Debug)]
pub enum MacroExpansionStep<'top, D: Decoder> {
    Step(ValueExpr<'top, D>),
    FinalStep(Option<ValueExpr<'top, D>>),
}

impl<'top, D: Decoder> MacroExpansionStep<'top, D> {
    pub fn value_expr(&self) -> Option<ValueExpr<'top, D>> {
        match self {
            MacroExpansionStep::Step(expr) => Some(*expr),
            MacroExpansionStep::FinalStep(maybe_expr) => *maybe_expr,
        }
    }

    pub fn is_final(&self) -> bool {
        matches!(self, MacroExpansionStep::FinalStep(_))
    }

    pub fn via_variable(mut self, variable_ref: Option<TemplateVariableReference<'top>>) -> Self {
        use MacroExpansionStep::*;
        match &mut self {
            Step(expr) => Step(expr.via_variable(variable_ref)),
            FinalStep(Some(expr)) => FinalStep(Some(expr.via_variable(variable_ref))),
            FinalStep(None) => FinalStep(None),
        }
    }
}

/// The internal bookkeeping representation used by a [`MacroEvaluator`].
#[derive(Debug)]
pub enum EvaluatorState<'top, D: Decoder> {
    /// The evaluator is empty; it does not currently have any expansions in progress.
    Empty,
    /// The evaluator has a single expansion in progress. It does not own any bump-allocated
    /// resources.
    Stackless(MacroExpansion<'top, D>),
    /// The evaluator has several expansions in progress. It holds a bump-allocated `MacroStack`
    /// that it pushes to and pops from.
    Stacked(StackedMacroEvaluator<'top, D>),
}

impl<D: Decoder> Default for EvaluatorState<'_, D> {
    fn default() -> Self {
        Self::Empty
    }
}

/// A general-purpose macro evaluator that waits to allocate resources until it is clear that they
/// are necessary.
#[derive(Debug, Default)]
pub struct MacroEvaluator<'top, D: Decoder> {
    root_environment: Environment<'top, D>,
    state: EvaluatorState<'top, D>,
}

impl<'top, D: Decoder> MacroEvaluator<'top, D> {
    pub fn is_empty(&self) -> bool {
        use EvaluatorState::*;
        match self.state {
            Empty => true,
            Stacked(ref evaluator) => evaluator.macro_stack_depth() == 0,
            _ => false,
        }
    }

    /// The core macro evaluation logic.
    #[inline]
    #[allow(clippy::should_implement_trait)] // Clippy complains this looks like Iterator::next
    pub fn next(&mut self) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
        use EvaluatorState::*;
        // This happens in a loop in case the next item produced is another macro to evaluate.
        // In most cases, we never return to the top of the loop.
        loop {
            let expansion = match self.state {
                // If the evaluator is empty, there's nothing to do.
                Empty => return Ok(None),
                // If the evaluator is processing several expansions (not common), we delegate the
                // evaluation and bookkeeping to the `StackedMacroEvaluator` type.
                Stacked(ref mut stack_evaluator) => return stack_evaluator.next(),
                // If the evaluator is stackless, there's only one expansion in progress.
                Stackless(ref mut expansion) => expansion,
            };

            // At this point, we have a reference to the only expansion in progress.
            //
            // If the next thing it produces is another macro, we would push it onto the stack.
            // However, this would cause the stack to grow to a depth of 2 and require us to
            // bump-allocate a proper stack.
            // Instead, as an optimization, we'll get the next step in the expansion...
            let step = expansion.next_step()?;
            // ...and, if this was the _last_ step in the expansion, pop it off the stack-of-one
            // by setting the state back to `Empty`.
            if step.is_final() {
                self.state = Empty;
            }
            // Now the stack has a depth of zero or one.
            match step.value_expr() {
                // No more expressions means we're done. (It also means the stack is empty because
                // it is not possible to return a non-final step that is `None`.)
                None => return Ok(None),
                // If it's a value, then regardless of stack depth we return that value.
                Some(ValueExpr::ValueLiteral(value)) => return Ok(Some(value)),
                // If it's another macro to evaluate, then we'll push it onto the stack and continue
                // at the top of the loop looking for our next value-or-nothing.
                Some(ValueExpr::MacroInvocation(invocation)) => {
                    // If the evaluator state is `Empty`, this sets it back to `Stackless`, which
                    // is an important optimization. We avoid bump-allocating in the lion's share
                    // of evaluations.
                    // If the state is `Stackless` (i.e. there's still an expansion in progress),
                    // this will upgrade the state to `Stacked` and allocate the necessary
                    // resources.
                    self.push(invocation.expand()?)
                    // This "tail eval" optimization--eagerly popping completed expansions off the
                    // stack to keep it flat--avoids allocations in many evaluations, e.g.:
                    // (:none)
                    // (:values)
                    // (:values 1 2 3)
                    // (:values 1 2 3 /*POP*/ (:values 1 2 3))
                    // (:values 1 2 3 /*POP*/ (:values 1 2 3 /*POP*/ (:values 1 2 3)))
                    //
                    // TODO: Use `invocation.invoked_macro().must_produce_exactly_one_value()`
                    //       to see if we can avoid pushing the new invocation and instead
                    //       eagerly evaluating it.
                }
            }
        }
    }

    pub fn new() -> Self {
        Self {
            root_environment: Environment::empty(),
            state: EvaluatorState::Empty,
        }
    }

    pub fn new_with_environment(environment: Environment<'top, D>) -> Self {
        Self {
            root_environment: environment,
            state: EvaluatorState::Empty,
        }
    }

    pub fn for_eexp(eexp: EExpression<'top, D>) -> IonResult<Self> {
        let macro_expr = MacroExpr::from_eexp(eexp);
        Self::for_macro_expr(macro_expr)
    }

    pub fn for_macro_expr(macro_expr: MacroExpr<'top, D>) -> IonResult<Self> {
        let expansion = macro_expr.expand()?;
        Ok(Self::for_expansion(expansion))
    }

    fn for_expansion(expansion: MacroExpansion<'top, D>) -> Self {
        Self {
            root_environment: expansion.environment,
            state: EvaluatorState::Stackless(expansion),
        }
    }

    pub fn environment(&self) -> Environment<'top, D> {
        use EvaluatorState::*;
        match self.state {
            Empty => self.root_environment,
            Stackless(ref expansion) => expansion.environment,
            Stacked(ref stack) => stack.environment(),
        }
    }

    #[inline]
    pub fn push(&mut self, new_expansion: MacroExpansion<'top, D>) {
        if self.is_empty() {
            // Going from zero expansions to one expansion is cheap.
            self.state = EvaluatorState::Stackless(new_expansion);
        } else {
            // Going from 1 to 2 or more is more expensive and less common,
            // so we don't inline this case.
            self.push_general_case(new_expansion)
        }
    }

    #[inline(never)]
    pub fn push_general_case(&mut self, new_expansion: MacroExpansion<'top, D>) {
        match mem::take(&mut self.state) {
            // Going from zero expansions to one expansion
            EvaluatorState::Empty => self.state = EvaluatorState::Stackless(new_expansion),
            // Going from one expansion to two
            EvaluatorState::Stackless(original_expansion) => {
                let mut stacked_evaluator = StackedMacroEvaluator::new_with_environment(
                    new_expansion.context(),
                    self.root_environment,
                );
                stacked_evaluator
                    .macro_stack
                    .extend([original_expansion, new_expansion]);
                self.state = EvaluatorState::Stacked(stacked_evaluator)
            }
            // Going from 2+ up
            EvaluatorState::Stacked(ref mut stacked_evaluator) => {
                stacked_evaluator.macro_stack.push(new_expansion)
            }
        };
    }

    pub fn set_root_environment(&mut self, environment: Environment<'top, D>) {
        self.root_environment = environment;
    }
}

pub type MacroStack<'top, D> = BumpVec<'top, MacroExpansion<'top, D>>;

/// Evaluates macro invocations recursively, yielding a single expanded value at a time.
///
/// The evaluator supports the cross product of three use case dimensions:
///
///   {e-expression, template macro invocation}
///   x {text, binary}
///   x {eager, lazy}
///
/// For incremental/lazy evaluation, push a macro invocation onto the stack using
/// [`StackedMacroEvaluator::push`] and then use [`StackedMacroEvaluator::next`] to evaluate the next value.
///
/// For eager evaluation, use [`StackedMacroEvaluator::evaluate`], which returns an iterator that will
/// yield the expanded values.
#[derive(Debug)]
pub struct StackedMacroEvaluator<'top, D: Decoder> {
    // A stack with the most recent macro invocations at the top. This stack grows each time a macro
    // of any kind begins evaluation.
    macro_stack: MacroStack<'top, D>,
    root_environment: Environment<'top, D>,
}

impl<'top, D: Decoder> StackedMacroEvaluator<'top, D> {
    #[inline]
    pub fn new(context: EncodingContextRef<'top>) -> Self {
        const INITIAL_MACRO_STACK_CAPACITY: usize = 8;
        let macro_stack =
            BumpVec::with_capacity_in(INITIAL_MACRO_STACK_CAPACITY, context.allocator());
        Self {
            macro_stack,
            root_environment: Environment::empty(),
        }
    }

    pub fn new_with_environment(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> Self {
        let mut evaluator = Self::new(context);
        evaluator.root_environment = environment;
        evaluator
    }

    /// Returns the number of macros that are currently being evaluated.
    pub fn macro_stack_depth(&self) -> usize {
        self.macro_stack.len()
    }

    /// Returns the current environment (i.e. the one used by the top of the macro stack.)
    pub fn environment(&self) -> Environment<'top, D> {
        self.macro_stack
            .last()
            .map(|expansion| expansion.environment)
            .unwrap_or(self.root_environment)
    }

    /// Given a syntactic element representing a macro invocation, attempt to resolve it with the
    /// current encoding context and push the resulting `MacroExpansion` onto the stack.
    pub fn push(&mut self, invocation: impl Into<MacroExpr<'top, D>>) -> IonResult<()> {
        let macro_expr = invocation.into();
        let expansion = macro_expr.expand()?;
        self.macro_stack.push(expansion);
        Ok(())
    }

    /// Continues evaluating the macro at the top of the stack until either:
    ///   * a value is yielded
    ///   * the macro stack is empty (that is: all macro evaluations are complete)
    ///
    /// This is equivalent to calling [`next_at_or_above_depth`](Self::next_at_or_above_depth)
    /// with a `depth_to_exhaust` of `0`; see that method's documentation for more details.
    // Clippy complains that `next` will be confused for the iterator method of the same name.
    #[allow(clippy::should_implement_trait)]
    pub fn next(&mut self) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
        self.next_at_or_above_depth(0)
    }

    /// Continues evaluating the macro at the top of the stack until either:
    ///   * a value is yielded
    ///   * the evaluation of the macro at stack depth `depth_to_exhaust` is completed
    ///
    /// If a macro invocation is encountered in the process of expanding the next value, that
    /// invocation will be pushed onto the stack. This means that the stack's depth can grow
    /// by any number of levels in a single call to `next()`. (Note though that macros do not
    /// support recursion, so it is not trivial to grow the stack to great depths.)
    ///
    /// If `depth_to_exhaust` is the stack's current depth, `next()` will return `None` when the
    /// macro at the top of the stack is completed/popped off the stack. If `depth_to_exhaust`
    /// is `0`, `next()` will return `None` when all macros on the stack are exhausted.
    ///
    /// The caller must verify that the stack's depth is greater than or equal to `depth_to_exhaust`
    /// before calling `next_at_or_above_depth()`.
    pub fn next_at_or_above_depth(
        &mut self,
        depth_to_exhaust: usize,
    ) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
        loop {
            // Get the expansion at the top of the stack.
            let current_expansion = match self.macro_stack.last_mut() {
                None => return Ok(None),
                Some(expansion) => expansion,
            };
            // Ask that expansion to continue its evaluation by one step.
            let step = current_expansion.next_step()?;
            current_expansion.is_complete = step.is_final();
            use ValueExpr::*;
            let maybe_output_value = match step.value_expr() {
                Some(MacroInvocation(invocation)) => {
                    self.push(invocation)?;
                    continue;
                }
                Some(ValueLiteral(value)) => Some(value),
                None => None,
            };

            if current_expansion.is_complete {
                self.pop_completed_macros();
            }
            if self.macro_stack.len() < depth_to_exhaust {
                return Ok(maybe_output_value);
            }
            if maybe_output_value.is_none() && !self.macro_stack.is_empty() {
                continue;
            }
            return Ok(maybe_output_value);
        }
    }

    fn pop_completed_macros(&mut self) {
        loop {
            // Pop the top macro, which we know to be completed.
            self.macro_stack.truncate(self.macro_stack.len() - 1);
            // See if the new top macro is also complete and ready to be popped.
            match self.macro_stack.last() {
                Some(expansion) if expansion.is_complete => continue,
                _ => break,
            }
        }
    }

    /// Attempts to resolve the provided `invocation` in the specified `context`. Upon success,
    /// returns an iterator that lazily computes the expansion of the macro invocation and yields
    /// its values.
    #[allow(dead_code)]
    pub fn evaluate<'iter>(
        &'iter mut self,
        invocation: impl Into<MacroExpr<'top, D>>,
    ) -> IonResult<EvaluatingIterator<'iter, 'top, D>>
    where
        Self: Sized,
    {
        self.push(invocation)?;
        Ok(EvaluatingIterator::new(self))
    }
}

/// Yields the values produced by incrementally evaluating the macro that was at the top of the
/// evaluator's stack when the iterator was created.
#[allow(dead_code)]
pub struct EvaluatingIterator<'iter, 'top, D: Decoder> {
    evaluator: &'iter mut StackedMacroEvaluator<'top, D>,
    initial_stack_depth: usize,
}

impl<'iter, 'top, D: Decoder> EvaluatingIterator<'iter, 'top, D> {
    #[allow(dead_code)]
    pub fn new(evaluator: &'iter mut StackedMacroEvaluator<'top, D>) -> Self {
        let initial_stack_depth = evaluator.macro_stack_depth();
        Self {
            evaluator,
            initial_stack_depth,
        }
    }
}

impl<'top, D: Decoder> Iterator for EvaluatingIterator<'_, 'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.evaluator
            .next_at_or_above_depth(self.initial_stack_depth)
            .transpose()
    }
}

// ===== Implementation of the `values` macro =====

/// The evaluation state of the `values` macro.
///
/// `(:values ...)` expands each of its arguments in turn, yielding individual values to the caller.
///
/// This allows a writer to group several expressions' output together into a single expression.
///
/// Examples:
///   (:values 1)                 => 1
///   (:values 1 2 3)             => 1 2 3
///   (:values 1 2 (:values 3 4)) => 1 2 3 4
#[derive(Copy, Clone, Debug)]
pub struct ExprGroupExpansion<'top, D: Decoder> {
    // Which argument the macro is in the process of expanding
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> ExprGroupExpansion<'top, D> {
    pub fn new(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self { arguments }
    }

    /// Yields the next [`ValueExpr`] in this macro's evaluation.
    #[inline(always)]
    pub fn next(
        &mut self,
        _context: EncodingContextRef<'top>,
        _environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        let arg_result = self.arguments.next();
        let is_last_arg = self.arguments.is_exhausted();
        // We visit the argument expressions in the invocation in order from left to right.
        match arg_result {
            // This is known to be the last argument; there will be no other steps after it is returned.
            Some(Ok(expr)) if is_last_arg => Ok(MacroExpansionStep::FinalStep(Some(expr))),
            // This is not known to be the last argument--if it _is_ the last one, the iterator was not
            // able to tell that it was. We'll treat it as though it is not. False positives result
            // in a future call to `next` to get a `FinalStep(None)` and can cause the evaluator
            // to allocate more resources than necessary.
            Some(Ok(expr)) => Ok(MacroExpansionStep::Step(expr)),
            None => Ok(MacroExpansionStep::FinalStep(None)),
            Some(Err(e)) => Err(e),
        }
    }
}

// ===== Implementation of `if_none`, `if_some`, `if_single`, `if_multi` =====
#[derive(Debug)]
pub struct ConditionalExpansion<'top, D: Decoder> {
    test_kind: CardinalityTestKind,
    arguments: MacroExprArgsIterator<'top, D>,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
// The compiler objects to each variant having the same prefix (`If`) because this is often a sign
// that the enum name is being repeated. In this case, removing the prefix causes `None` and `Some`
// to collide with the `Option` variants that are already in the prelude.
#[allow(clippy::enum_variant_names)]
pub enum CardinalityTestKind {
    IfNone,
    IfSome,
    IfSingle,
    IfMulti,
}

impl<'top, D: Decoder> ConditionalExpansion<'top, D> {
    pub fn new(kind: CardinalityTestKind, arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self {
            test_kind: kind,
            arguments,
        }
    }

    pub fn if_none(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self::new(CardinalityTestKind::IfNone, arguments)
    }

    pub fn if_some(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self::new(CardinalityTestKind::IfSome, arguments)
    }

    pub fn if_single(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self::new(CardinalityTestKind::IfSingle, arguments)
    }

    pub fn if_multi(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self::new(CardinalityTestKind::IfMulti, arguments)
    }

    pub fn name(&self) -> &str {
        use CardinalityTestKind::*;
        match self.test_kind {
            IfNone => "if_none",
            IfSome => "if_some",
            IfSingle => "if_single",
            IfMulti => "if_multi",
        }
    }

    pub fn next(
        &mut self,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        // These are errors are `unreachable!` because all three arguments are zero-or-more.
        // In text, `(.if_none)` would be passing three empty streams due to rest syntax.
        // In binary, not passing arguments at all would be invalid data. Setting the empty stream
        // bits in the bitmap would be close, but then you'd still have three empty streams.
        let expr_to_test = self.arguments.next().transpose()?.unwrap_or_else(|| {
            unreachable!(
                "macro `{}` was not given an expression to test",
                self.name()
            )
        });
        let true_expr = self.arguments.next().transpose()?.unwrap_or_else(|| {
            unreachable!("macro `{}` was not given a `true` expression", self.name())
        });
        let true_result = Ok(MacroExpansionStep::FinalStep(Some(true_expr)));

        let cardinality = match expr_to_test {
            ValueExpr::ValueLiteral(_) => ExpansionCardinality::Single,
            ValueExpr::MacroInvocation(invocation) => {
                invocation.expansion_cardinality(environment)?
            }
        };
        use CardinalityTestKind::*;
        use ExpansionCardinality as EC;
        match (self.test_kind, cardinality) {
            (IfNone, EC::None)
            | (IfSome, EC::Single | EC::Multi)
            | (IfSingle, EC::Single)
            | (IfMulti, EC::Multi) => true_result,
            _ => {
                let false_expr = self.arguments.next().transpose()?.unwrap_or_else(|| {
                    unreachable!("macro `{}` was not given a `false` expression", self.name())
                });
                Ok(MacroExpansionStep::FinalStep(Some(false_expr)))
            }
        }
    }
}

macro_rules! sysmacro_arg_info {
    (enum $name:ident {
        $($variant:ident = $val:expr),*,
    }) => {
        #[derive(PartialEq)]
        enum $name {
            $($variant = $val),*
        }

        impl AsRef<str> for $name {
            fn as_ref(&self) -> &str {
                match self {
                    $($name::$variant => stringify!($variant)),*
                }
            }
        }
    }
}

// A simple wrapper for a system macros's known arguments. Provides context for error reporting, and
// functionality to expand e-exp and validate integer types. Can be expanded for more types as
// needed.
struct SystemMacroArgument<'top, A: AsRef<str>, D: Decoder>(A, ValueExpr<'top, D>);
impl <'top, A: AsRef<str>, D: Decoder> SystemMacroArgument<'top, A, D> {
    /// Expands the current [`ValueExpr`] for the argument and verifies that it expands to 0 or 1
    /// value. Returns the value as a ValueRef.
    fn try_get_valueref(&self, env: Environment<'top, D>) -> IonResult<Option<ValueRef<'top, D>>> {
        let argument_name= self.0.as_ref();

        let arg = match self.1 {
            ValueExpr::ValueLiteral(value_literal) => {
                Some(value_literal.read_resolved()?)
            }
            ValueExpr::MacroInvocation(invocation) => {
                let mut evaluator = MacroEvaluator::new_with_environment(env);
                evaluator.push(invocation.expand()?);
                let int_arg = match evaluator.next()? {
                    None => None,
                    Some(value) => {
                        Some(value.read_resolved()?)
                    }
                };

                if !evaluator.is_empty() && evaluator.next()?.is_some() {
                    return IonResult::decoding_error(format!("expected integer value for '{argument_name}' parameter but the provided argument contained multiple values."));
                }
                int_arg
            }
        };
        Ok(arg)
    }

    /// Given a [`ValueExpr`], this function will expand it into its underlying value; An
    /// error is return if the value does not expand to exactly one Int.
    fn get_integer(&self, env: Environment<'top, D>) -> IonResult<Int> {
        let argument_name= self.0.as_ref();
        let value_ref = self.try_get_valueref(env)?;
        value_ref
            .ok_or_else(|| IonError::decoding_error(format!("expected integer value for '{argument_name}' parameter but the provided argument contained no value.")))?
            .expect_int()
    }

}

// ===== Implementation of the `make_decimal` macro ===
#[derive(Copy, Clone, Debug)]
pub struct MakeDecimalExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> MakeDecimalExpansion<'top, D> {
    pub fn new(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self { arguments }
    }

    pub fn next(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        #[inline(never)]
        fn error_context(err: IonError) -> IonError {
            IonError::decoding_error(format!("`make_decimal`: {err}"))
        }
        // Arguments should be: (coefficient exponent)
        //   Both coefficient and exponent should evaluate to a single integer value.
        let coeff_expr = self.arguments.next().ok_or(IonError::decoding_error("`make_decimal` takes 2 integer arguments; found 0 arguments"))?;
        let coefficient = SystemMacroArgument("Coefficient", coeff_expr?).get_integer(environment).map_err(error_context)?;

        let expo_expr = self.arguments.next().ok_or(IonError::decoding_error("`make_decimal` takes 2 integer arguments; found only 1 argument"))?;
        let exponent = SystemMacroArgument("Exponent", expo_expr?).get_integer(environment).map_err(error_context)?;

        let decimal = Decimal::new(coefficient, exponent.as_i64().ok_or_else(|| IonError::decoding_error("Exponent does not fit within the range supported by this implementation."))?);

        let value_ref = context
            .allocator()
            .alloc_with(|| ValueRef::Decimal(decimal));
        let lazy_expanded_value = LazyExpandedValue::from_constructed(context, &[], value_ref);

        Ok(MacroExpansionStep::FinalStep(Some(
            ValueExpr::ValueLiteral(lazy_expanded_value)
        )))
    }
}

// ===== Implementation of the `make_timestamp` macro ====

/// This wrapper wraps a [`TimestampBuilder`] and allows us to treat it as an unchanging type to
/// more easily pass it around while evaluating the make_timestamp macro arguments.
#[derive(Clone, Default)]
#[allow(clippy::enum_variant_names)]
enum TimestampBuilderWrapper {
    #[default]
    None,
    WithYear(TimestampBuilder<HasYear>),
    WithMonth(TimestampBuilder<HasMonth>),
    WithDay(TimestampBuilder<HasDay>),
    WithHour(TimestampBuilder<HasHour>),
    WithMinute(TimestampBuilder<HasMinute>),
    WithSecond(TimestampBuilder<HasSeconds>),
    WithFractionalSeconds(TimestampBuilder<HasFractionalSeconds>),
    WithOffset(TimestampBuilder<HasOffset>),
}

sysmacro_arg_info! { enum MakeTimestampArgs { Month = 0, Day = 1, Hour = 2, Minute = 3, Second = 4, Offset = 5, } }
impl TimestampBuilderWrapper {

    fn process<'top, D: Decoder>(&mut self, env: Environment<'top, D>, arg: &SystemMacroArgument<'top, MakeTimestampArgs, D>) -> IonResult<()> {
        use TimestampBuilderWrapper::*;
        match self {
            WithYear(_) => self.process_with_year(env, arg),
            WithMonth(_) => self.process_with_month(env, arg),
            WithDay(_) => self.process_with_day(env, arg),
            WithHour(_) => self.process_with_hour(env, arg),
            WithMinute(_) => self.process_with_minute(env, arg),
            WithSecond(_) => {
                let Some(value) = arg.try_get_valueref(env)? else {
                    return Ok(());
                };
                self.process_offset(value)
            }
            WithFractionalSeconds(ref _builder) => {
                let Some(value) = arg.try_get_valueref(env)? else {
                    return Ok(());
                };
                self.process_offset(value)
            }
            _ => unreachable!(), // offset is the last argument, there won't be any
                                 // more after.
        }
    }

    fn build(self) -> IonResult<Timestamp> {
        use TimestampBuilderWrapper::*;
        match self {
            WithYear(builder) => builder.build(),
            WithMonth(builder) => builder.build(),
            WithDay(builder) => builder.build(),
            WithHour(_builder) => IonResult::decoding_error("no value provided for 'Minute'"),
            WithMinute(builder) => builder.build(),
            WithSecond(builder) => builder.build(),
            WithFractionalSeconds(builder) => builder.build(),
            WithOffset(builder) => builder.build(),
            _ => IonResult::decoding_error("attempt to build timestamp while in unconstructed state"),
        }
    }

    /// Intended for internal use, so that we can take ownership of the TimestampBuilder while
    /// processing arguments that will ultimately lead to a new builder being created and forming
    /// the new TimestampBuidlerWrapper state.
    fn take(&mut self) -> Self {
        mem::take(self)
    }

    /// Process the next provided argument after we've added the year to the timestamp.
    fn process_with_year<'top, D: Decoder>(&mut self, env: Environment<'top, D>, arg: &SystemMacroArgument<'top, MakeTimestampArgs, D>) -> IonResult<()> {
        // We have a year, only option for a value is the month.
        let parameter = arg.0.as_ref();

        // Check to see if we actually have a value.
        let Some(value_ref) = arg.try_get_valueref(env)? else {
            return Ok(());
        };

        // We have a value, if it is anything other than Month it is invalid.
        if arg.0 != MakeTimestampArgs::Month {
            return IonResult::decoding_error(format!("value provided for '{parameter}', but no month specified."));
        }

        let month_i64= value_ref
            .expect_int()?
            .as_u32()
            .ok_or_else(|| IonError::decoding_error("value provided for 'Month' does not fit within a 32bit unsigned integer"))?;

        let TimestampBuilderWrapper::WithYear(builder) = self.take() else { unreachable!() };
        let new_builder = builder.with_month(month_i64);
        *self = new_builder.into();

        Ok(())
    }

    /// Process the next provided argument, after we have added the month to the timestamp.
    fn process_with_month<'top, D: Decoder>(&mut self, env: Environment<'top, D>, arg: &SystemMacroArgument<'top, MakeTimestampArgs, D>) -> IonResult<()> {
        // If we have a new value, it has to be a day, nothing else is valid.
        let parameter = arg.0.as_ref();

        // Check to see if we actually have a value.
        let Some(value_ref) = arg.try_get_valueref(env)? else {
            return Ok(())
        };

        // We have a value, if it is anything other than Day then it is invalid.
        if arg.0 != MakeTimestampArgs::Day {
            return IonResult::decoding_error(format!("value provided for '{parameter}', but no day specified."));
        }

        let day= value_ref
            .expect_int()?
            .as_u32()
            .ok_or_else(|| IonError::decoding_error("value provided for 'Day' parameter cannot be represented as a unsigned 32bit value."))?;

        let TimestampBuilderWrapper::WithMonth(builder) = self.take() else { unreachable!() };
        let new_builder = builder.with_day(day);
        *self = new_builder.into();

        Ok(())
    }

    /// Process the next provided argument, after we have added the day to the timestamp.
    fn process_with_day<'top, D: Decoder>(&mut self, env: Environment<'top, D>, arg: &SystemMacroArgument<'top, MakeTimestampArgs, D>) -> IonResult<()> {
        // We have a day, and a new value.. the only valid option is hour.
        let parameter = arg.0.as_ref();

        // Check to see if we actually have a value.
        let Some(value_ref) = arg.try_get_valueref(env)? else {
            return Ok(())
        };

        // We have a value, if it is anything other than Hour then it is invalid.
        if arg.0 != MakeTimestampArgs::Hour {
            return IonResult::decoding_error(format!("value provided for '{parameter}', but no hour specified."));
        }

        let hour = value_ref
            .expect_int()?
            .as_u32()
            .ok_or_else(|| IonError::decoding_error("value provided for 'Hour' cannot be represented as an unsigned 32bit value"))?;

        let TimestampBuilderWrapper::WithDay(builder) = self.take() else { unreachable!() };
        let new_builder = builder.with_hour(hour);
        *self = new_builder.into();

        Ok(())
    }

    /// Process the next provided argument after we have added the hour to the timestamp.
    fn process_with_hour<'top, D: Decoder>(&mut self, env: Environment<'top, D>, arg: &SystemMacroArgument<'top, MakeTimestampArgs, D>) -> IonResult<()> {
        // We have an hour, the only valid argument is Minute.
        let parameter_name = arg.0.as_ref();

        // Check if we have a value.
        let Some(value_ref) = arg.try_get_valueref(env)? else {
            return Ok(());
        };

        if arg.0 != MakeTimestampArgs::Minute {
            return IonResult::decoding_error(format!("value provided for '{parameter_name}', but no minute specified."));
        }

        let minute = value_ref
            .expect_int()?
            .as_u32()
            .ok_or_else(|| IonError::decoding_error("value provided for 'Minute' cannot be represented as an unsigned 32bit value"))?;

        let TimestampBuilderWrapper::WithHour(builder) = self.take() else { unreachable!() };
        let new_builder = builder.with_minute(minute);
        *self = new_builder.into();

        Ok(())
    }

    /// Process the next provided argument after we have added the minute to the timestamp.
    fn process_with_minute<'top, D: Decoder>(&mut self, env: Environment<'top, D>, arg: &SystemMacroArgument<'top, MakeTimestampArgs, D>) -> IonResult<()> {
        // We have a minute, we have 2 options for args now: Seconds, and Offset.
        let parameter_name = arg.0.as_ref();

        // Check if we have a value.
        let Some(value_ref) = arg.try_get_valueref(env)? else {
            return Ok(());
        };

        if arg.0 == MakeTimestampArgs::Second {
            self.process_second(value_ref)
        } else if arg.0 == MakeTimestampArgs::Offset {
            self.process_offset(value_ref)
        } else {
            return IonResult::decoding_error(format!("value provided for '{parameter_name}', but no value for 'second' specified."));
        }
    }

    /// Process the value for the timestamp's second field. The second can be provided as either an
    /// Int or a Decimal with sub-second precision.
    fn process_second<'top, D: Decoder>(&mut self, value: ValueRef<'top, D>) -> IonResult<()> {
        use crate::IonType;

        *self = match value.ion_type() {
            IonType::Decimal => {
                let second_dec = value.expect_decimal()?;

                let whole_seconds = second_dec.trunc();
                let fractional_seconds = second_dec.fract();

                // The whole value should be between 0 and 60, tested above.
                let whole_seconds_i64 = whole_seconds
                    .coefficient()
                    .as_int()
                    .and_then(|v| v.as_i64())
                    .ok_or_else(|| {
                        IonError::decoding_error("value provided for 'Second' did not contain a coefficient representable by an unsigned 64bit value")
                    })?;
                // Correct with the exponent jic the value is normalized to 5x10^1 or something.
                let whole_seconds_i64 = whole_seconds_i64 * 10i64.pow(whole_seconds.exponent() as u32);

                let TimestampBuilderWrapper::WithMinute(builder) = self.take() else { unreachable!() };
                let builder = builder.with_second(whole_seconds_i64 as u32);
                let builder = builder.with_fractional_seconds(fractional_seconds);

                builder.into()
            }
            IonType::Int  => {
                let second_i64 = value
                    .expect_int()?
                    .as_i64()
                    .ok_or_else(|| {
                        IonError::decoding_error("value provided for 'Second' could not be represented in a 64bit integer.")
                    })?;

                let TimestampBuilderWrapper::WithMinute(builder) = self.take() else { unreachable!() };
                builder
                    .with_second(second_i64 as u32)
                    .into()
            }
            _ => IonResult::decoding_error("value provided for 'Second' is an unexpected type; should be an integer or decimal")?,
        };

        Ok(())
    }

    /// Process the provided ValueRef as the offset parameter for the timestamp.
    fn process_offset<'top, D: Decoder>(&mut self, value: ValueRef<'top, D>) -> IonResult<()> {
        let offset = value
            .expect_int()?
            .as_i64()
            .ok_or_else(|| IonError::decoding_error("value provided for 'Offset' is not representable by a 64bit integer"))?;

        let new_builder = match self.take() {
            Self::WithMinute(builder) => builder.with_offset(offset as i32),
            Self::WithSecond(builder) => builder.with_offset(offset as i32),
            Self::WithFractionalSeconds(builder) => builder.with_offset(offset as i32),
            _ => return IonResult::decoding_error("Invalid state while building timestamp; tried to set field 'Offset' without setting time"),
        };

        *self = new_builder.into();

        Ok(())
    }
}

macro_rules! impl_froms_timestampbuilders {
    ($($state:ident => $wrapper:ident),*) => {
        $(
            impl From<TimestampBuilder<$state>> for TimestampBuilderWrapper {
                fn from(value: TimestampBuilder<$state>) -> Self {
                    Self::$wrapper(value)
                }
            }
        )*
    }
}
impl_froms_timestampbuilders!(
    HasYear => WithYear, HasMonth => WithMonth, HasDay => WithDay, HasHour => WithHour, HasMinute => WithMinute,
    HasSeconds => WithSecond, HasFractionalSeconds => WithFractionalSeconds, HasOffset =>  WithOffset
);



#[derive(Copy, Clone, Debug)]
pub struct MakeTimestampExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> MakeTimestampExpansion<'top, D> {

    pub fn new(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self { arguments }
    }

    fn next(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        // make_timestamp (year month? day? hour? minute? second? offset_minutes?)
        use crate::types::Timestamp;

        #[inline(never)]
        fn error_context(err: IonError) -> IonError {
            IonError::decoding_error(format!("`make_timestamp`: {err}"))
        }

        // Year is required, so we have to ensure that it is available. Our arguments iterator will
        // always have an item for each defined parameter, even if it is not present at the callsite.
        // But we still check here, JIC that ever changes.
        let year_expr = self.arguments
            .next()
            .ok_or(IonError::decoding_error("`make_timestamp` takes 1 to 7 arguments; found 0 arguments"))?;
        let year = SystemMacroArgument("year", year_expr?)
            .get_integer(environment)
            .map_err(error_context)?;

        // Validate year range.
        let year_i64 = year
            .as_i64()
            .filter(|v| *v >= 1 && *v <= 9999)
            .ok_or_else(|| IonError::decoding_error("`make_timestamp`: value provided for 'year' parameter is out of range [1, 9999]"))?;

        // Now that we know that Year is provided, we can evaluate all of the arguments.
        // TimestampBuilderWrapper handles the tracking of state, and which arguments need to be
        // present and which are optional.
        let args= [
            SystemMacroArgument(MakeTimestampArgs::Month, self.arguments.next().unwrap()?),
            SystemMacroArgument(MakeTimestampArgs::Day, self.arguments.next().unwrap()?),
            SystemMacroArgument(MakeTimestampArgs::Hour, self.arguments.next().unwrap()?),
            SystemMacroArgument(MakeTimestampArgs::Minute, self.arguments.next().unwrap()?),
            SystemMacroArgument(MakeTimestampArgs::Second, self.arguments.next().unwrap()?),
            SystemMacroArgument(MakeTimestampArgs::Offset, self.arguments.next().unwrap()?),
        ];

        let mut builder = TimestampBuilderWrapper::WithYear(Timestamp::with_year(year_i64 as u32));
        args
            .iter()
            .try_for_each(|arg| builder.process(environment, arg))
            // .try_fold(TimestampBuilderWrapper::WithYear(Timestamp::with_year(year_i64 as u32)), |builder, arg| {
            //     builder.process(environment, arg)
            // })
            .map_err(error_context)?;

        let timestamp = builder.build()?;

        let value_ref = context
            .allocator()
            .alloc_with(|| ValueRef::Timestamp(timestamp));
        let lazy_expanded_value = LazyExpandedValue::from_constructed(context, &[], value_ref);

        Ok(MacroExpansionStep::FinalStep(Some(
            ValueExpr::ValueLiteral(lazy_expanded_value)
        )))
    }
}

// ===== Implementation of the `make_field` macro =====

#[derive(Copy, Clone, Debug)]
pub struct MakeFieldExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> MakeFieldExpansion<'top, D> {
    pub fn new(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self { arguments }
    }

    pub fn next(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        // The parser will have confirmed that two argument expressions
        // were passed in: a field name and value.
        let name_expr = self.arguments.next().unwrap()?;
        let value_expr = self.arguments.next().unwrap()?;

        let name = name_expr
            .evaluate_singleton_in(environment)?
            .read_resolved()?
            .expect_text()
            .map_err(|_| {
                IonError::decoding_error("`make_field`'s first argument must be a text value")
            })
            .map(SymbolRef::with_text)?;
        let value = value_expr.evaluate_singleton_in(environment)?;
        let field = LazyExpandedField::new(LazyExpandedFieldName::MakeField(name), value);
        let lazy_expanded_struct = LazyExpandedStruct::from_make_field(context, field);
        let lazy_struct = LazyStruct::new(lazy_expanded_struct);
        let value_ref = context
            .allocator()
            .alloc_with(|| ValueRef::Struct(lazy_struct));
        let lazy_expanded_value = LazyExpandedValue::from_constructed(context, &[], value_ref);
        Ok(MacroExpansionStep::FinalStep(Some(
            ValueExpr::ValueLiteral(lazy_expanded_value),
        )))
    }
}

// ===== Implementation of the `make_struct` macro =====
#[derive(Copy, Clone, Debug)]
pub struct MakeStructExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> MakeStructExpansion<'top, D> {
    pub fn new(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self { arguments }
    }

    fn next(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        // The `make_struct` macro always produces a single struct value. When `next()` is called
        // to begin its evaluation, it immediately returns a lazy value representing the (not yet
        // computed) struct. If/when the application tries to iterate over its fields,
        // the iterator will evaluate the field expressions incrementally.
        let lazy_expanded_struct =
            LazyExpandedStruct::from_make_struct(context, environment, self.arguments);
        let lazy_struct = LazyStruct::new(lazy_expanded_struct);
        // Store the `Struct` in the bump so it's guaranteed to be around as long as the reader is
        // positioned on this top-level value.
        let value_ref = context
            .allocator()
            .alloc_with(|| ValueRef::Struct(lazy_struct));
        let lazy_expanded_value = LazyExpandedValue::from_constructed(context, &[], value_ref);
        Ok(MacroExpansionStep::FinalStep(Some(
            ValueExpr::ValueLiteral(lazy_expanded_value),
        )))
    }
}
// ===== Implementation of the `make_string` macro =====

#[derive(Copy, Clone, Debug)]
enum TextValueType {
    String,
    Symbol,
}

/// Evaluation logic shared by the `make_string` and `make_symbol` macros.
#[derive(Copy, Clone, Debug)]
pub struct MakeTextExpansion<'top, D: Decoder> {
    value_type: TextValueType,
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> MakeTextExpansion<'top, D> {
    pub fn string_maker(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self {
            value_type: TextValueType::String,
            arguments,
        }
    }

    pub fn symbol_maker(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self {
            value_type: TextValueType::Symbol,
            arguments,
        }
    }

    /// Concatenates all of the macro's arguments into a single bump-allocated string.
    /// If any of the arguments are not text values, returns `Err`.
    fn concatenate_text_arguments(
        &mut self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<&'top str> {
        // Create a bump-allocated buffer to hold our constructed string
        const INITIAL_CAPACITY: usize = 32;
        let mut buffer = BumpString::with_capacity_in(INITIAL_CAPACITY, context.allocator());

        // We need to eagerly evaluate all of the arguments to `make_string` to produce its next
        // (and only) value. However, because `&mut self` (the expansion state) lives in a stack
        // inside the evaluator, we cannot get a simultaneous mutable reference to the evaluator
        // itself. Instead, we use the bump allocator the make a transient macro evaluator
        // whose resources can be trivially reclaimed when the expansion is done.
        let mut evaluator = MacroEvaluator::<'top, D>::new();

        for arg_result in &mut self.arguments {
            let arg_expr = arg_result?;
            match arg_expr {
                ValueExpr::ValueLiteral(expanded_value) => {
                    let text = expanded_value.read_resolved()?.expect_text()?;
                    buffer.push_str(text);
                }
                ValueExpr::MacroInvocation(invocation) => {
                    evaluator.push(invocation.expand()?);
                    while let Some(value) = evaluator.next()? {
                        let text = value.read_resolved()?.expect_text()?;
                        buffer.push_str(text);
                    }
                }
            }
        }

        // Convert our BumpString<'bump> into a &'bump str and return it
        Ok(buffer.into_bump_str())
    }

    fn make_text_value(
        &mut self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        let constructed_text = self.concatenate_text_arguments(context)?;
        let value_ref: &'top ValueRef<'top, _> =
            context.allocator().alloc_with(|| match self.value_type {
                TextValueType::String => ValueRef::String(StrRef::from(constructed_text)),
                TextValueType::Symbol => ValueRef::Symbol(SymbolRef::from(constructed_text)),
            });
        static EMPTY_ANNOTATIONS: &[SymbolRef<'_>] = &[];

        Ok(MacroExpansionStep::FinalStep(Some(
            ValueExpr::ValueLiteral(LazyExpandedValue::from_constructed(
                context,
                EMPTY_ANNOTATIONS,
                value_ref,
            )),
        )))
    }
}

// ====== Implementation of the `sum` macro
#[derive(Debug)]
pub struct SumExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
}

impl <'top, D: Decoder> SumExpansion<'top, D> {
    pub fn new(
        arguments: MacroExprArgsIterator<'top, D>,
    ) -> Self {

        Self {
            arguments,
        }
    }

    /// Given a [`ValueExpr`], this function will expand it into its underlying value; An
    /// error is returned if the value does not expand to exactly one Int.
    fn get_integer(&self, env: Environment<'top, D>, value: ValueExpr<'top, D>) -> IonResult<Int> {
        match value {
            ValueExpr::ValueLiteral(value_literal) => {
                value_literal
                    .read_resolved()?
                    .expect_int()
            }
            ValueExpr::MacroInvocation(invocation) => {
                let mut evaluator = MacroEvaluator::new_with_environment(env);
                evaluator.push(invocation.expand()?);
                let int_arg = match evaluator.next()? {
                    None => IonResult::decoding_error("`sum` takes two integers as arguments; empty value found"),
                    Some(value) => value
                        .read_resolved()?
                        .expect_int(),
                };

                // Ensure that we don't have any other values in the argument's stream.
                if !evaluator.is_empty() && evaluator.next()?.is_some() {
                    return IonResult::decoding_error("`sum` takes two integers as arguments; multiple values found");
                }

                int_arg
            }
        }
    }

    fn next(
        &mut self,
        context: EncodingContextRef<'top>,
        env: Environment<'top, D>
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        let mut sum = Int::new(0);
        // Walk each of our arguments..
        for value in self.arguments {
            let value = value?;
            let i = self.get_integer(env, value)?;
            sum = sum + i;
        }

        let value_ref = context
            .allocator()
            .alloc_with(|| ValueRef::Int(sum));
        let lazy_expanded_value = LazyExpandedValue::from_constructed(context, &[], value_ref);

        Ok(MacroExpansionStep::FinalStep(Some(
                ValueExpr::ValueLiteral(lazy_expanded_value)
        )))
    }
}

// ====== Implementation of the `repeat` macro
#[derive(Debug)]
pub struct RepeatExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
    repeat_iterations: Option<usize>,
    content: Option<ValueExpr<'top, D>>,
}

impl<'top, D: Decoder> RepeatExpansion<'top, D> {
    pub fn new(
        arguments: MacroExprArgsIterator<'top, D>,
    ) -> Self {
        Self {
            arguments,
            repeat_iterations: None,
            content: None,
        }
    }

    // Extracts the first argument from `arguments` and verifies that it is a single integer value
    // >= 0 that can be used as the repeat count. Any other value will return an error.
    fn get_number_to_repeat(&mut self, arguments: &mut MacroExprArgsIterator<'top, D>, environment: Environment<'top, D>) -> IonResult<usize> {
        let count_expr = arguments
            .next()
            .unwrap_or(IonResult::decoding_error("`repeat` takes 2 or more parameters"))?;

        let repeat_count = match count_expr {
            ValueExpr::ValueLiteral(value_literal) => value_literal
                .read_resolved()?
                .expect_int()?,

            ValueExpr::MacroInvocation(invocation) => {
                let mut evaluator = MacroEvaluator::new_with_environment(environment);
                evaluator.push(invocation.expand()?);
                match evaluator.next()? {
                    None => return IonResult::decoding_error("`repeat` takes a single integer value >= 0 as the first parameter; found empty value"),
                    Some(value) => {
                        let num = value
                            .read_resolved()?
                            .expect_int()?;

                        if !evaluator.is_empty() && evaluator.next()?.is_some() {
                            return IonResult::decoding_error("`repeat` takes a single integer value >= 0 as the first parameter; found multiple values");
                        }
                        num
                    }
                }
            }
        };

        if repeat_count.is_negative() {
            return IonResult::decoding_error("`repeat` takes a single integer value >= 0 as the first parameter; found negative value");
        }

        let repeat_count = repeat_count
            .as_usize().ok_or(IonError::decoding_error("`repeat` takes a single value >= 0 as the first parameter; found a value that exceeded usize"))?;

        Ok(repeat_count)
    }

    pub fn next(
        &mut self,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        // If we haven't yet, evaluate the first argument, to find out how many iterations we have.
        if self.repeat_iterations.is_none() {
            let mut arguments = self.arguments;
            self.repeat_iterations = Some(self.get_number_to_repeat(&mut arguments, environment)?);
            self.content= match arguments.next() {
                None => None,
                Some(Err(e)) => return Err(e),
                Some(Ok(expr)) => Some(expr),
            };
        }

        // Check if we've reached our desired number of iterations, or if we have empty content.
        if Some(0) == self.repeat_iterations || self.content.is_none() {
            return Ok(MacroExpansionStep::FinalStep(None)) // End early.
        }

        if let Some(ref mut repeat_iterations) = self.repeat_iterations {
            *repeat_iterations = repeat_iterations.saturating_sub(1);
            match self.content {
                Some(value_arg_expr) => {
                    if *repeat_iterations == 0 {
                        Ok(MacroExpansionStep::FinalStep(Some(value_arg_expr)))
                    } else {
                        Ok(MacroExpansionStep::Step(value_arg_expr))
                    }
                }
                None => unreachable!(), // Handled above.
            }
        } else {
            unreachable!();
        }
    }
}

// ====== Implementation of the `flatten` macro

#[derive(Debug)]
pub struct FlattenExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
    evaluator: &'top mut MacroEvaluator<'top, D>,
    // This is &mut Option<_> instead of Option<&mut _> because it allows us to do a single
    // bump-allocation up front and re-use that space to hold each of the iterators we'll
    // work with over the course of evaluation.
    // In plainer terms: we _always_ have an allocated space that may or may not contain an iterator.
    // We can put iterators into that space or remove them.
    // If this were Option<&mut _>, we _might_ have a space with an iterator in it. If we set a new
    // iterator, we would have to allocate a space for that iterator.
    current_sequence: &'top mut Option<ExpandedSequenceIterator<'top, D>>,
}

impl<'top, D: Decoder> FlattenExpansion<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        arguments: MacroExprArgsIterator<'top, D>,
    ) -> Self {
        let allocator = context.allocator();
        let evaluator = allocator.alloc_with(|| MacroEvaluator::new_with_environment(environment));
        let current_sequence = allocator.alloc_with(|| None);
        Self {
            evaluator,
            arguments,
            current_sequence,
        }
    }

    fn set_current_sequence(&mut self, value: LazyExpandedValue<'top, D>) -> IonResult<()> {
        *self.current_sequence = match value.read()? {
            ExpandedValueRef::List(list) => Some(ExpandedSequenceIterator::List(list.iter())),
            ExpandedValueRef::SExp(sexp) => Some(ExpandedSequenceIterator::SExp(sexp.iter())),
            other => {
                return IonResult::decoding_error(format!(
                    "`flatten` only accepts sequences, received {other:?}"
                ))
            }
        };
        Ok(())
    }

    /// Yields the next [`ValueExpr`] in this `flatten` macro's evaluation.
    fn next(&mut self) -> IonResult<MacroExpansionStep<'top, D>> {
        loop {
            // If we're already flattening a sequence, get the next nested value from it.
            if let Some(current_sequence) = self.current_sequence {
                // First, get the next nested sequence value result from the iterator.
                match current_sequence.next() {
                    // If we get `Some(IonResult)`, return it even if it's an Err.
                    Some(Ok(result)) => {
                        return Ok(MacroExpansionStep::Step(ValueExpr::ValueLiteral(result)))
                    }
                    Some(Err(e)) => return Err(e),
                    // If we get `None`, the iterator is exhausted and we should continue on to the next sequence.
                    None => *self.current_sequence = None,
                }
            }

            // If we reach this point, we don't have a current sequence.
            // We've either just started evaluation and haven't set one yet or
            // we just finished flattening a sequence and need to set a new one.

            // See if the evaluator has an expansion in progress.
            let mut next_seq = self.evaluator.next()?;

            if next_seq.is_none() {
                // If we don't get anything from the evaluator, we'll get our sequence from the
                // next argument expression.
                next_seq = match self.arguments.next().transpose()? {
                    // If the expression is a value literal, that's our new sequence.
                    Some(ValueExpr::ValueLiteral(value)) => Some(value),
                    // If the expression is a macro invocation, we'll start evaluating it
                    // and return to the top of the loop.
                    Some(ValueExpr::MacroInvocation(invocation)) => {
                        self.evaluator.push(invocation.expand()?);
                        continue;
                    }
                    // If there isn't a next argument expression, then evaluation is complete.
                    None => return Ok(MacroExpansionStep::FinalStep(None)),
                }
            }

            // At this point, `next_seq` is definitely populated, so we can safely unwrap it.
            let next_seq = next_seq.unwrap();

            // Set it as our new current sequence. This step also type-checks the value to confirm
            // that it is either a list or an s-expression.
            self.set_current_sequence(next_seq)?;
        }
    }
}

// ===== Implementation of the `delta` macro ====
#[derive(Debug)]
pub struct DeltaExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
    evaluator: &'top mut MacroEvaluator<'top, D>,
    current_base: Option<Int>,
}

impl<'top, D: Decoder> DeltaExpansion<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        arguments: MacroExprArgsIterator<'top, D>,
    ) -> Self {
        let allocator = context.allocator();
        let evaluator = allocator.alloc_with(|| MacroEvaluator::new_with_environment(environment));
        Self {
            arguments,
            evaluator,
            current_base: None,
        }
    }

    /// Returns the next [`Int`] to be used in the delta encoding by querying the macro evaluator
    /// used for expanding the expression group.
    fn get_next_delta(&mut self) -> IonResult<Option<Int>> {
        // First, check if we have anything going on in the evaluator..
        match self.evaluator.next()? {
            // If we get a None, then we're done evaluating our expression group.
            None => Ok(None),
            // When we do get a value, we just need to expand it and ensure it is an Int
            Some(value) => {
                let i = value.read_resolved()?.expect_int()?;
                Ok(Some(i))
            }
        }
    }

    pub fn next(&mut self, context: EncodingContextRef<'top>) -> IonResult<MacroExpansionStep<'top, D>> {
        // If we haven't evaluated any of the deltas yet, we need to grab our expression group and
        // load it into the evaluator.
        if self.current_base.is_none() {
            // If we've already done this, but we have no values to populate current_base with,
            // we'll exhaust the arguments and return FinalStep here.
            match self.arguments.next() {
                None => return Ok(MacroExpansionStep::FinalStep(None)),
                Some(Err(e)) => return Err(e),
                Some(Ok(expr)) => match expr {
                    // If we have an exp group, we have to evaluate it in order to get all of our
                    // arguments.
                    ValueExpr::MacroInvocation(invocation) => {
                        self.evaluator.push(invocation.expand()?)
                    }
                    // If a single value is provided for the delta parameter, it can be encoded as
                    // a single non-grouped value.
                    ValueExpr::ValueLiteral(_) => {
                        return Ok(MacroExpansionStep::FinalStep(Some(expr)));
                    }
                },
            }
            self.current_base = Some(Int::new(0));
        }

        let Some(delta) = self.get_next_delta()? else {
            return Ok(MacroExpansionStep::FinalStep(None));
        };

        if let Some(ref mut current_base) = self.current_base {
            *current_base = *current_base + delta;
            let value_ref = context
                .allocator()
                .alloc_with(|| ValueRef::Int(self.current_base.unwrap()));
            let lazy_expanded_value =
                LazyExpandedValue::from_constructed(context, &[], value_ref);

            Ok(MacroExpansionStep::Step(ValueExpr::ValueLiteral(
                lazy_expanded_value,
            )))
        } else {
            unreachable!()
        }
    }
}

// ===== Implementation of the `annotate` macro =====
#[derive(Copy, Clone, Debug)]
pub struct AnnotateExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> AnnotateExpansion<'top, D> {
    pub fn new(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self { arguments }
    }

    pub fn next(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        let annotations_arg = match self.arguments.next() {
            None => {
                return IonResult::decoding_error("`annotate` takes two parameters, received none")
            }
            Some(Err(e)) => return Err(e),
            Some(Ok(expr)) => expr,
        };

        // Collect all of the annotations (Strings/Symbols) from the output of the first arg expr
        let mut annotations = BumpVec::new_in(context.allocator());
        match annotations_arg {
            ValueExpr::ValueLiteral(value_literal) => {
                annotations.push(value_literal.read_resolved()?.expect_text()?.into())
            }
            ValueExpr::MacroInvocation(invocation) => {
                let mut evaluator = MacroEvaluator::new_with_environment(environment);
                evaluator.push(invocation.expand()?);
                while !evaluator.is_empty() {
                    match evaluator.next()? {
                        None => {}
                        Some(value) => {
                            let symbol_text = value.read_resolved()?.expect_text()?.into();
                            annotations.push(symbol_text);
                        }
                    }
                }
            }
        }

        // Get the second argument, which represents the value to annotate
        let value_arg = match self.arguments.next() {
            None => {
                return IonResult::decoding_error("`annotate` takes two parameters, received one")
            }
            Some(Err(e)) => return Err(e),
            Some(Ok(expr)) => expr,
        };

        // If there are more arguments in the iterator, there's an arity mismatch.
        if !self.arguments.is_exhausted() {
            return IonResult::decoding_error(
                "`annotate` takes two parameters, received three or more",
            );
        }

        // Evaluate the value argument if needed to get the value we'll be annotating further.
        let expanded_value_to_annotate = match value_arg {
            ValueExpr::ValueLiteral(value_literal) => value_literal,
            ValueExpr::MacroInvocation(invocation) => invocation.expand()?.expand_singleton()?,
        };

        // If the value to annotate already has annotations, append them to the end of our vec.
        let value_to_annotate = LazyValue::new(expanded_value_to_annotate);
        for annotation in value_to_annotate.annotations() {
            annotations.push(annotation?);
        }

        // Read the value and store the resulting ValueRef in the bump.
        let data = value_to_annotate.read()?;
        let value_ref = context.allocator().alloc_with(|| data);

        // Combine our annotations vec and our value_ref to make a 'Constructed' value.
        let annotated_value =
            LazyExpandedValue::from_constructed(context, annotations.into_bump_slice(), value_ref);
        Ok(MacroExpansionStep::FinalStep(Some(
            ValueExpr::ValueLiteral(annotated_value),
        )))
    }
}

// ===== Implementation of template macro expansion =====

/// The evaluation state of a template expansion.
#[derive(Copy, Clone, Debug)]
pub struct TemplateExpansion<'top> {
    // A reference to the template definition
    template: TemplateMacroRef<'top>,
    // The current 'step' of the expansion being processed.
    step_index: usize,
}

impl<'top> TemplateExpansion<'top> {
    pub fn new(template: TemplateMacroRef<'top>) -> Self {
        Self {
            template,
            step_index: 0,
        }
    }

    #[inline]
    pub(crate) fn next<'data: 'top, D: Decoder>(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        let expressions = self.template.body().expressions();
        let value_tdl_expr = match expressions.get(self.step_index) {
            None => return Ok(MacroExpansionStep::FinalStep(None)),
            Some(expr) => expr,
        };
        let value_expr = value_tdl_expr.to_value_expr(context, environment, self.template);

        self.step_index += value_tdl_expr.num_expressions();
        if self.step_index >= expressions.len() {
            Ok(MacroExpansionStep::FinalStep(Some(value_expr)))
        } else {
            Ok(MacroExpansionStep::Step(value_expr))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{v1_1, ElementReader, Int, IonResult, MacroTable, Reader, Sequence};
    use rstest::*;

    /// Reads `input` and `expected` and asserts that their output is Ion-equivalent.
    fn stream_eq<'data>(input: &'data str, expected: &'data str) -> IonResult<()> {
        let mut actual_reader = Reader::new(v1_1::Text, input)?;
        let actual = actual_reader.read_all_elements()?;

        assert_eq_expected(&actual, expected)
    }

    fn bin_stream_eq(input: &[u8], expected: &str) -> IonResult<()> {
        let mut actual_reader = Reader::new(v1_1::Binary, input)?;
        let actual = actual_reader.read_all_elements()?;

        assert_eq_expected(&actual, expected)
    }

    fn assert_eq_expected(actual: &Sequence, expected: &str) -> IonResult<()> {
        let mut expected_reader = Reader::new(v1_1::Text, expected)?;
        let expected = expected_reader.read_all_elements()?;
        assert_eq!(
            actual, &expected,
            "actual\n{actual:?}\nwas not equal to expected\n{expected:?}\n",
        );
        Ok(())
    }

    /// Manually registers a macro with `template_definition` as its source, evaluates `invocation`,
    /// and confirms that its expansion produces the same Ion stream as `expected`.
    fn eval_template_invocation(
        template_definition: &str,
        invocation: &str,
        expected: &str,
    ) -> IonResult<()> {
        let mut reader = Reader::new(v1_1::Text, invocation.as_bytes())?;
        let _macro_address = reader.register_template_src(template_definition)?;
        let actual = reader.read_all_elements()?;
        let mut expected_reader = Reader::new(v1_1::Text, expected.as_bytes())?;
        let expected = expected_reader.read_all_elements()?;
        assert_eq!(actual, expected);
        assert!(matches!(expected_reader.next(), Ok(None)));

        Ok(())
    }

    #[test]
    fn read_system_eexp() -> IonResult<()> {
        bin_stream_eq(
            &[
                0xEF, // System macro, address follows as 1-byte FixedUInt
                0x09, // make_string
                0x02, // Argument group
                0x11, // FlexUInt 8: 8-byte group
                0x93, // Opcode: 3-byte string follows
                0x66, 0x6F, 0x6F, // "foo"
                0x93, // Opcode: 3-byte string follows
                0x62, 0x61, 0x72, // "bar"
            ],
            r#""foobar""#,
        )
    }

    #[test]
    fn read_system_eexp_with_delimited_tagged_arg_group() -> IonResult<()> {
        // Empty delimited argument group
        bin_stream_eq(
            &[
                0xEF, // System macro, address follows as 1-byte FixedUInt
                0x09, // make_string
                0x02, // Argument group
                0x01, // FlexUInt 0: delimited group
                0xF0, // Delimited END
            ],
            r#" "" // <-- empty string "#,
        )?;
        // Populated delimited argument group
        bin_stream_eq(
            &[
                0xEF, // System macro, address follows as 1-byte FixedUInt
                0x09, // make_string
                0x02, // Argument group
                0x01, // FlexUInt 0: delimited group
                0x93, // Opcode: 3-byte string follows
                0x66, 0x6F, 0x6F, // "foo"
                0x93, // Opcode: 3-byte string follows
                0x62, 0x61, 0x72, // "bar"
                0xF0, // Delimited END
            ],
            r#" "foobar" "#,
        )
    }

    #[test]
    fn multiple_top_level_values() -> IonResult<()> {
        eval_template_invocation(
            "(macro foo () (.values 1 2 3 4 5))",
            r#"
                (:foo)
            "#,
            r#"
                1 2 3 4 5
            "#,
        )
    }

    #[test]
    fn macros_close_over_dependencies() -> IonResult<()> {
        stream_eq(
            r#"
                // Define macro `double`
                $ion::
                (module _
                    (macro_table
                        $ion
                        (macro double (x) (.$ion::values (%x) (%x)))
                    )
                )

                // `double` exists until the *end* of the encoding directive below. Define a new
                // macro that depends on `double`.
                $ion::
                (module _
                    (macro_table
                        (macro quadruple (y)
                            (.$ion::values
                                // Because `double` is in the active encoding module, we can refer
                                // to it without qualification.
                                (.double (%y))
                                // We could also refer to it with a qualification.
                                (._::double (%y))))
                    )
                )

                // At this point, only `quadruple` is accessible/addressable, but it still works.
                (:quadruple "foo")
            "#,
            r#"
                "foo"
                "foo"
                "foo"
                "foo"
            "#,
        )
    }

    #[test]
    fn reexporting_ion_encoding_makes_macros_local() -> IonResult<()> {
        stream_eq(
            r#"
                // Define macro `double`
                $ion::
                (module _
                    (macro_table
                        _
                        (macro double (x) (.values (%x) (%x)))
                    )
                )

                $ion::
                (module _
                    (macro_table
                        _ // Re-export the active encoding module's macros
                        (macro quadruple (y)
                            (.$ion::values
                                // Because `double` has been added to the local namespace,
                                // we can refer to it without a qualified reference.
                                (.double (%y))
                                // However, we can also refer to it using a qualified reference.
                                (._::double (%y))))
                    )
                )

                // At this point, only `quadruple` is accessible/addressable, but it still works.
                (:quadruple "foo")
            "#,
            r#"
                "foo"
                "foo"
                "foo"
                "foo"
            "#,
        )
    }

    #[test]
    fn make_sexp() -> IonResult<()> {
        eval_template_invocation(
            r#"(macro foo (x) (.make_sexp [1, (%x), 3] [a, (%x), c]))"#,
            r#"
                (:foo 5)
                (:foo quuz)
                (:foo {a: 1, b: 2})
                (:foo [])
            "#,
            r#"
                (1 5 3 a 5 c)
                (1 quuz 3 a quuz c)
                (1 {a: 1, b: 2} 3 a {a: 1, b: 2} c)
                (1 [] 3 a [] c)
            "#,
        )
    }

    #[test]
    fn tdl_arg_expr_group() -> IonResult<()> {
        eval_template_invocation(
            r#"(macro abc () (.make_string (.. "a" "b" "c")))"#,
            r#"
                (:abc)
            "#,
            r#"
                "abc"
            "#,
        )
    }

    #[test]
    fn multiple_arg_expr_groups() -> IonResult<()> {
        stream_eq(
            r#"
                $ion::
                (module _
                    (macro_table
                        (macro foo (x+ y* z+)
                            (.make_string (.. (%x) "-" (%y) "-" (%z))))
                        (macro letters ()
                            (.foo
                                (.. "a" "b" "c")
                                (.. "d" "e" "f")
                                (.. "g" "h" "i")))
                    )
                )
                (:letters)
            "#,
            r#"
                "abc-def-ghi"
            "#,
        )
    }

    #[test]
    fn explicit_expr_group_arg() -> IonResult<()> {
        stream_eq(
            r#"
                (:add_macros
                    (macro greet (x) (.make_string (.. "Hello, " (%x))))
                )
                (:greet "Gary")
            "#,
            r#"
                "Hello, Gary"
            "#,
        )
    }

    #[test]
    fn built_in_set_symbols() -> IonResult<()> {
        stream_eq(
            r#"
                // Define some symbols
                (:set_symbols foo bar) // $1, $2

                // Use them
                $1
                $2
            "#,
            r#"
                foo
                bar
            "#,
        )
    }

    #[test]
    fn set_symbols_drops_prior_definitions() -> IonResult<()> {
        stream_eq(
            r#"
                // Define some symbols
                (:set_symbols foo bar) // $1, $2

                // Use them
                $1
                $2

                // Define new symbols
                (:set_symbols baz qux) // $1, $2

                // Use them
                $1
                $2
            "#,
            r#"
                foo
                bar
                baz
                qux
            "#,
        )
    }

    #[test]
    fn built_in_add_symbols() -> IonResult<()> {
        stream_eq(
            r#"
                // Define some symbols
                $ion::
                (module _
                    (symbol_table ["foo", "bar"]) // $1, $2
                )
                // Use them
                $1
                $2

                // Define new symbols
                (:add_symbols baz quux) // $3, $4
                $3
                $4
            "#,
            r#"
                foo
                bar
                baz
                quux
            "#,
        )
    }

    #[test]
    fn built_in_set_macros() -> IonResult<()> {
        stream_eq(
            r#"
                // Define a macro which calls a system macro
                (:set_macros
                    (macro greet (x) (.make_string "Hello, " (%x) ))
                )
                // Invoke it
                (:greet "Waldo")
            "#,
            r#"
                "Hello, Waldo"
            "#,
        )
    }

    #[test]
    #[should_panic]
    fn set_macros_drops_previous_macros() {
        stream_eq(
            r#"
                // Define a macro which calls a system macro
                (:set_macros
                    (macro greet (x) (.make_string "Hello, " (%x) ))
                )
                // Invoke it
                (:greet "Waldo")

                // Drop our user-defined macros
                (:set_macros)
                // This invocation should error
                (:greet "Waldo")
            "#,
            r#"
                "Hello, Waldo"
                // should raise an error
            "#,
        )
        .unwrap()
    }

    #[test]
    fn set_macros_preserves_symbols() -> IonResult<()> {
        // TODO: update symbol IDs when reading and writing system symbols are implemented
        stream_eq(
            r#"
                $ion::
                (module _
                    (symbol_table ["foo", "bar", "baz"]) // $1, $2, $3
                )
                $1
                $2
                $3

                // Define a new macro
                (:set_macros
                    (macro greet (x)
                        (.make_string "Hello, " (%x))
                    )
                    (macro greet_foo()
                        (.greet $1)
                    )
                )

                (:greet "Gary")
                (:greet_foo)
                $1
                $2
                $3
            "#,
            r#"
                foo
                bar
                baz
                "Hello, Gary"
                "Hello, foo"
                foo
                bar
                baz
            "#,
        )
    }

    #[test]
    fn built_in_add_macros() -> IonResult<()> {
        stream_eq(
            r#"
                // Define two macros that call system macros
                (:add_macros
                    (macro greet (x) (.make_string "Hello, " (%x) ))
                    (macro twice (x) (.values (%x) (%x)))
                )
                // Invoke them
                (:greet "Waldo")
                (:twice "foo")

                // Define a new macro
                (:add_macros
                    (macro greet_twice (x)
                        (.twice (.greet (%x)))
                    )
                )

                // // The original macros are still available
                (:greet "Sally")
                (:twice "bar")
                //
                // // And so is the new one
                (:greet_twice "Gary")
            "#,
            r#"
                "Hello, Waldo"
                "foo" "foo"
                "Hello, Sally"
                "bar" "bar"
                "Hello, Gary" "Hello, Gary"
            "#,
        )
    }

    #[test]
    fn add_macros_preserves_symbols() -> IonResult<()> {
        // TODO: update symbol IDs when reading and writing system symbols are implemented
        stream_eq(
            r#"
                $ion::
                (module _
                    (symbol_table ["foo", "bar", "baz"]) // $1, $2, $3
                )
                $1
                $2
                $3

                // Define a new macro
                (:add_macros
                    (macro greet (x)
                        (.make_string "Hello, " (%x))
                    )
                    (macro greet_foo()
                        (.greet $1)
                    )
                )

                (:greet "Gary")
                (:greet_foo)
                $1
                $2
                $3
            "#,
            r#"
                foo
                bar
                baz
                "Hello, Gary"
                "Hello, foo"
                foo
                bar
                baz
            "#,
        )
    }

    #[test]
    fn produce_system_value() -> IonResult<()> {
        eval_template_invocation(
            r#"
                (macro def_macros (macros*)
                    $ion::
                    (module _
                        (macro_table (%macros))
                    )
                )"#,
            r#"
                (:def_macros
                    (macro foo () 1)
                    (macro bar () 2)
                    (macro baz () 3)
                )
                (:foo)
                (:bar)
                (:baz)
            "#,
            r#"
                1 2 3
            "#,
        )
    }

    #[test]
    fn annotate() -> IonResult<()> {
        eval_template_invocation(
            r#"(macro foo (x) (.annotate (.values "bar" "baz" "quux") (%x)))"#,
            r#"
                (:foo 5)
                (:foo quuz)
                (:foo {a: 1, b: 2})
                (:foo already::annotated::5)
            "#,
            r#"
                bar::baz::quux::5
                bar::baz::quux::quuz
                bar::baz::quux::{a: 1, b: 2}
                bar::baz::quux::already::annotated::5
            "#,
        )
    }

    mod cardinality {
        mod exactly_one {
            use crate::lazy::expanded::macro_evaluator::tests::{
                eval_template_invocation, stream_eq,
            };

            #[test]
            #[should_panic]
            fn does_not_accept_empty_rest() {
                eval_template_invocation(
                    "(macro foo (x) (.make_string (%x) (%x)))",
                    r#"
                (:foo)
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn does_not_accept_empty_arg_group() {
                eval_template_invocation(
                    "(macro foo (x) (.make_string (%x) (%x)))",
                    r#"
                        (:foo (::))
                    "#,
                    r#"
                        // should raise an error
                    "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn does_not_accept_empty_tdl_arg_group() {
                stream_eq(
                    r#"
                        (:add_macros
                            (macro foo (x) (.make_string x x))
                            (macro bar () (.foo (..)))
                        )
                        (:bar)
                    "#,
                    r#"
                        // should raise an error
                    "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn does_not_accept_populated_arg_group() {
                eval_template_invocation(
                    "(macro foo (x) (.make_string x x))",
                    r#"
                (:foo (::))
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn does_not_accept_populated_tdl_arg_group() {
                stream_eq(
                    r#"
                        (:add_macros
                            (macro foo (x) (.make_string x x))
                            (macro bar () (.foo (:: "Hi")))
                        )
                        (:bar)
                    "#,
                    r#"
                        // should raise an error
                    "#,
                )
                .unwrap()
            }
        }

        mod zero_or_one {
            use crate::lazy::expanded::macro_evaluator::tests::{
                eval_template_invocation, stream_eq,
            };
            use crate::IonResult;

            #[test]
            fn accepts_empty_or_expr() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x?) (.make_string (%x) (%x)))",
                    r#"
                (:foo)           // x is implicitly empty
                (:foo (::))      // x is explicitly empty
                (:foo (::   ))   // x is explicitly empty with extra whitespace
                (:foo "a")       // x is "a"
                (:foo (:foo a))  // x is `(:foo a)`
            "#,
                    r#"
                ""
                ""
                ""
                "aa"
                "aaaa"
            "#,
                )
            }

            #[test]
            fn accepts_tdl_empty_or_expr() -> IonResult<()> {
                stream_eq(
                    r#"
                        (:add_macros
                            (macro foo (x?) (.make_string (%x) (%x)))
                            (macro  bar () (.foo (..)))    // Explicit empty group
                            (macro  baz () (.foo)    )     // Implicit empty group
                            (macro quux () (.foo "hello")) // Single expression
                        )
                        (:bar)
                        (:baz)
                        (:quux)
                    "#,
                    r#"
                        ""
                        ""
                        "hellohello"
                    "#,
                )
            }

            #[test]
            #[should_panic]
            fn does_not_accept_populated_arg_groups() {
                eval_template_invocation(
                    "(macro foo (x?) (.make_string (%x) (%x)))",
                    r#"
                (:foo (:: "a"))
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn does_not_accept_populated_tdl_arg_groups() {
                stream_eq(
                    r#"
                    (:add_macros
                        (macro foo (x?) (make_string (%x) (%x)))
                        (macro bar () (foo (.. "a"))))
                (:bar)
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }
        }

        mod zero_or_more {
            use crate::lazy::expanded::macro_evaluator::tests::eval_template_invocation;
            use crate::IonResult;

            #[test]
            fn accepts_groups() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x y*) (.make_string (%x) (%y)))",
                    r#"
                (:foo "hello" (:: " there " "friend!" ))
            "#,
                    r#"
                "hello there friend!"
            "#,
                )
            }

            #[test]
            fn accepts_rest() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x y*) (.make_string (%x) (%y)))",
                    r#"
                //     x       y1        y2
                (:foo "hello" " there " "friend!")
            "#,
                    r#"
                "hello there friend!"
            "#,
                )
            }

            #[test]
            fn accepts_value_literal() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x y* z*) (.make_string (%x) (%y) (%z)))",
                    r#"
                //    x       y         z
                (:foo "hello" " there " "friend!")
            "#,
                    r#"
                "hello there friend!"
            "#,
                )
            }

            #[test]
            fn omit_trailing_star() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x y*) (.make_string (%x) (%y)))",
                    r#"
                (:foo "hello") // pass one arg, `y` will be an empty stream
            "#,
                    r#"
                "hello"
            "#,
                )
            }

            #[test]
            #[should_panic]
            fn omit_only_last_trailing_star() {
                eval_template_invocation(
                    "(macro foo (x y* z*) (.make_string x y))",
                    r#"
                (:foo "hello") // pass one arg, y and z cannot both be omitted
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }
        }

        mod one_or_more {
            use crate::lazy::expanded::macro_evaluator::tests::{
                eval_template_invocation, stream_eq,
            };

            #[test]
            #[should_panic]
            fn does_not_accept_empty_arg_group() {
                eval_template_invocation(
                    "(macro foo (x+) (make_string (%x) (%x))",
                    r#"
                (:foo (::))
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn does_not_accept_empty_rest() {
                eval_template_invocation(
                    "(macro foo (x+) (make_string (%x) (%x)))",
                    r#"
                (:foo)
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn does_not_accept_empty_tdl_arg_group() {
                stream_eq(
                    r#"
                        (:add_macros
                            (macro foo (x+) (make_string (%x) (%x)))
                            (macro bar () (foo (..)))
                        )
                        (:bar)
                    "#,
                    r#"
                        // should raise an error
                    "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn does_not_accept_empty_tdl_rest() {
                stream_eq(
                    r#"
                        (:add_macros
                            (macro foo (x+) (make_string (%x) (%x)))
                            (macro bar () (foo))
                        )
                        (:bar)
                    "#,
                    r#"
                        // should raise an error
                    "#,
                )
                .unwrap()
            }
        }
    }

    #[test]
    #[should_panic]
    fn too_many_args() {
        eval_template_invocation(
            "(macro foo (x y) (make_string (%x) (%y)))",
            r#"
                (:foo "a" "b" "c")
            "#,
            r#"
                // should raise an error
            "#,
        )
        .unwrap()
    }

    #[test]
    fn flex_uint_parameters() -> IonResult<()> {
        let template_definition =
            "(macro int_pair (flex_uint::x flex_uint::y) (.values (%x) (%y))))";
        let macro_id = MacroTable::FIRST_USER_MACRO_ID as u8;
        let tests: &[(&[u8], (u64, u64))] = &[
            // invocation+args, expected arg values
            (&[macro_id, 0x01, 0x01], (0, 0)),
            (&[macro_id, 0x09, 0x03], (4, 1)),
            (&[macro_id, 0x0B, 0x0D], (5, 6)), // TODO: non-required cardinalities
        ];

        for (stream, (num1, num2)) in tests.iter().copied() {
            let mut reader = Reader::new(v1_1::Binary, stream)?;
            reader.register_template_src(template_definition)?;
            assert_eq!(
                reader.next()?.unwrap().read()?.expect_int()?,
                Int::from(num1)
            );
            assert_eq!(
                reader.next()?.unwrap().read()?.expect_int()?,
                Int::from(num2)
            );
        }
        Ok(())
    }

    #[test]
    fn it_takes_all_kinds() -> IonResult<()> {
        eval_template_invocation(
            r#"(macro foo () 
                (.values
                    null 
                    true
                    1
                    1e0
                    1.0
                    2023T
                    "1"
                    '1'
                    {{MQ==}}
                    {{"1"}}
                    [1]
                    (1)
                    {'1':1}))"#,
            r#"
                (:foo)
            "#,
            r#"
                null 
                true
                1
                1e0
                1.0
                2023T
                "1"
                '1'
                {{MQ==}}
                {{"1"}}
                [1]
                (1)
                {'1':1}
            "#,
        )
    }

    #[test]
    fn emit_symbol_table() -> IonResult<()> {
        eval_template_invocation(
            r#"
                (macro lst (symbols) 
                    $ion_symbol_table::{
                        symbols: (%symbols)
                    }
                )
            "#,
            r#"
                (:lst ["foo", "bar", "baz"]) $1 $2 $3
            "#,
            r#"
                foo bar baz
            "#,
        )
    }

    #[test]
    fn context_changes_happen_between_top_level_expressions() -> IonResult<()> {
        eval_template_invocation(
            r#"
                (macro lst (symbols) 
                    (.values
                        $ion_symbol_table::{
                            symbols: (%symbols)
                        }
                    )
                )
            "#,
            r#"
                $ion_symbol_table::{
                    symbols: ["foo", "bar"]
                }

                // These symbols refer to the symtab defined above
                $1
                $2
                
                // The $10 and $11 here _also_ refer to the symtab above because the
                // new LST won't be applied until after this top-level expression.
                (:values (:lst ["baz", "quux"]) $1 $2)
                
                // These refer to the new LST
                $1 $2
            "#,
            r#"
                foo bar foo bar baz quux
            "#,
        )
    }

    #[test]
    fn swap() -> IonResult<()> {
        eval_template_invocation(
            "(macro swap (x y) (.values (%y) (%x)))",
            r#"
                [
                    (:swap 1 2),
                    (:swap foo bar),
                    (:swap (:values 1 2 3) (:values 4 5 6))
                ]
            "#,
            r#"
                [
                    2, 1,
                    bar, foo,
                    4, 5, 6, 1, 2, 3,
                ]
            "#,
        )
    }

    #[test]
    fn new_yorkers() -> IonResult<()> {
        eval_template_invocation(
            r#"
                (macro new_yorker (first last)
                    {
                        name: {
                            first: (%first),
                            last: (%last),
                        },
                        state: "New York",
                        country: "USA"
                    }
                )
            "#,
            r#"
                [
                    (:new_yorker "Aaron" "Aaronson"),
                    (:new_yorker "Bettie" "Benowitz"),
                    (:new_yorker "Carol" "Canterbury"),
                ]
                "#,
            r#"
                [
                    {
                        name: {
                            first: "Aaron",
                            last: "Aaronson",
                        },
                        state: "New York",
                        country: "USA"
                    },
                    {
                        name: {
                            first: "Bettie",
                            last: "Benowitz",
                        },
                        state: "New York",
                        country: "USA"
                    },
                    {
                        name: {
                            first: "Carol",
                            last: "Canterbury",
                        },
                        state: "New York",
                        country: "USA"
                    }
                ]    
            "#,
        )
    }

    #[test]
    fn application_log_event() -> IonResult<()> {
        eval_template_invocation(
            // Template definition
            r#"
                (macro event (timestamp thread_id thread_name client_num host_id parameters) 
                    {
                        'timestamp': (%timestamp),
                        'threadId': (%thread_id),
                        'threadName': (.make_string "scheduler-thread-" (%thread_name)),
                        'loggerName': "com.example.organization.product.component.ClassName",
                        'logLevel': INFO,
                        'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
                        'parameters': [
                            "SUCCESS",
                            (.make_string "example-client-" (%client_num)),
                            (.make_string "aws-us-east-5f-" (%host_id)),
                            (%parameters)
                        ]
                    }
                )
            "#,
            // Template invocation
            r#"
                (:event
                    1670446800245
                    418
                    "6"
                    "1"
                    "abc-123"
                    (:values
                        "region 4"
                        "2022-12-07T20:59:59.744000Z"))
            "#,
            // Equivalent output
            r#"
                    {
                        'timestamp': 1670446800245,
                        'threadId': 418,
                        'threadName': "scheduler-thread-6",
                        'loggerName': "com.example.organization.product.component.ClassName",
                        'logLevel': INFO,
                        'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
                        'parameters': [
                            "SUCCESS",
                            "example-client-1",
                            "aws-us-east-5f-abc-123",
                            "region 4",
                            "2022-12-07T20:59:59.744000Z",
                        ]
                    }
            "#,
        )
    }

    #[test]
    fn annotated_template_value() -> IonResult<()> {
        eval_template_invocation(
            "(macro foo () bar::baz::quux::5)",
            r#"
                (:foo)
            "#,
            r#"
                bar::baz::quux::5
            "#,
        )
    }

    #[test]
    fn values_tdl_macro_invocation() -> IonResult<()> {
        eval_template_invocation(
            r"(macro foo () (.values 1 2 (.values 3 4 (.values 5 6) 7 8) 9 10))",
            "(:foo)",
            "1 2 3 4 5 6 7 8 9 10",
        )
    }

    #[test]
    fn values_e_expression() -> IonResult<()> {
        stream_eq(
            r"(:values 1 2 (:values 3 4 (:values 5 6) 7 8) 9 10)",
            "1 2 3 4 5 6 7 8 9 10",
        )
    }

    #[test]
    fn none_e_expression() -> IonResult<()> {
        stream_eq(r"(:values (:none) (:none) (:none) )", "/* nothing */")
    }

    #[test]
    fn none_tdl_macro_invocation() -> IonResult<()> {
        eval_template_invocation(
            r"(macro foo () (.values (.none) (.none) (.none)))",
            "(:foo)",
            "/* nothing */",
        )
    }

    #[test]
    fn make_string_e_expression() -> IonResult<()> {
        let e_expression = r#"
        (:values
            (:make_string foo bar baz)
            (:make_string "foo" '''bar''' baz)
            (:make_string "first " $4)
            (:make_string "Hello" ", " "world!"))
        "#;
        stream_eq(
            e_expression,
            r#" "foobarbaz" "foobarbaz" "first name" "Hello, world!" "#,
        )
    }

    #[test]
    fn make_symbol_e_expression() -> IonResult<()> {
        stream_eq(
            r#"
                (:make_symbol foo bar baz)
                (:make_symbol "foo" '''bar''' baz)
                (:make_symbol (:values foo "bar" baz))
                (:make_symbol "first " $4)
                (:make_symbol "Hello" ", " "world!")
            "#,
            r#"
                foobarbaz
                foobarbaz
                foobarbaz
                'first name'
                'Hello, world!'
             "#,
        )
    }

    #[test]
    fn flatten_e_expression() -> IonResult<()> {
        stream_eq(
            r#"
                (:flatten
                    [1, 2, 3]
                    []
                    []
                    (4 5 6)
                    ()
                    ()
                    (7))
            "#,
            r#" 1 2 3 4 5 6 7 "#,
        )
    }

    #[test]
    fn make_sexp_e_expression() -> IonResult<()> {
        let e_expression = r#"
        (:make_sexp
            [1, 2, 3]
            []
            []
            (4 5 6)
            ()
            ()
            (7))
        "#;
        stream_eq(e_expression, r#" (1 2 3 4 5 6 7) "#)
    }

    #[test]
    fn make_list_e_expression() -> IonResult<()> {
        let e_expression = r#"
        (:make_list
            [1, 2, 3]
            []
            []
            (4 5 6)
            ()
            ()
            (7))
        "#;
        stream_eq(e_expression, r#" [1, 2, 3, 4, 5, 6, 7] "#)
    }

    #[test]
    fn make_list_with_nested_eexp() -> IonResult<()> {
        let e_expression = r#"
        (:make_list
            [1, 2, 3]
            []
            []
            ((:values 4 (:values 5 6)))
            ()
            ()
            (7))
        "#;
        stream_eq(e_expression, r#" [1, 2, 3, 4, 5, 6, 7] "#)
    }

    #[test]
    fn default_eexp() -> IonResult<()> {
        stream_eq(
            r#"
            (:add_macros
                (macro foo (x?)
                    (.make_string "Hello, " (.default (%x) "world!"))))
            (:foo "Gary")
            (:foo)
        "#,
            r#"
            "Hello, Gary"
            "Hello, world!"
        "#,
        )
    }

    #[test]
    fn special_form_if_none() -> IonResult<()> {
        stream_eq(
            r#"
            (:add_macros
                (macro foo (x*)
                    (.make_string "Hello, " (.if_none (%x) "world!" (%x)))))
            (:foo "Gary")
            (:foo "Gary" " and " "Susan")
            (:foo (:flatten ["Tina", " and ", "Lisa"]))
            (:foo)
        "#,
            r#"
            "Hello, Gary"
            "Hello, Gary and Susan"
            "Hello, Tina and Lisa"
            "Hello, world!"
        "#,
        )
    }

    #[test]
    fn special_form_if_some() -> IonResult<()> {
        stream_eq(
            r#"
            (:add_macros
                (macro foo (x*)
                    (.make_string "Hello, " (.if_some (%x) (%x) "world!" ))))
            (:foo "Gary")
            (:foo "Gary" " and " "Susan")
            (:foo (:flatten ["Tina", " and ", "Lisa"]))
            (:foo)
        "#,
            r#"
            "Hello, Gary"
            "Hello, Gary and Susan"
            "Hello, Tina and Lisa"
            "Hello, world!"
        "#,
        )
    }

    #[test]
    fn special_form_if_single() -> IonResult<()> {
        stream_eq(
            r#"
            (:add_macros
                (macro snack (x*)
                    {
                        fruit: (.if_single (%x) (%x) [(%x)] )
                    }))
            (:snack)
            (:snack "apple")
            (:snack "apple" "banana" "cherry")
        "#,
            r#"
            {fruit: []}
            {fruit: "apple"}
            {fruit: ["apple", "banana", "cherry"]}
        "#,
        )
    }

    #[test]
    fn special_form_if_multi() -> IonResult<()> {
        stream_eq(
            r#"
            (:add_macros
                (macro snack (x*)
                    {
                        fruit: (.if_multi (%x) [(%x)] (%x) )
                    }))
            (:snack)
            (:snack "apple")
            (:snack "apple" "banana" "cherry")
        "#,
            r#"
            {}
            {fruit: "apple"}
            {fruit: ["apple", "banana", "cherry"]}
        "#,
        )
    }

    #[test]
    fn make_struct_eexp() -> IonResult<()> {
        stream_eq(
            r#"
            (:make_struct)
            (:make_struct {a: 1})
            (:make_struct {a: 1} {})
            (:make_struct {a: 1} {b: 2})
            (:make_struct {a: 1} {b: 2} {a: 3, d: 4})
            (:make_struct {a: 1} {b: 2} {a: 3, d: 4} (:make_struct {e: 5} {f: 6}))
        "#,
            r#"
            {}
            {a: 1}
            {a: 1}
            {a: 1, b: 2}
            {a: 1, b: 2, a: 3, d: 4}
            {a: 1, b: 2, a: 3, d: 4, e: 5, f: 6}
        "#,
        )
    }

    #[test]
    fn make_field_eexp() -> IonResult<()> {
        stream_eq(
            r#"
            (:make_field a 1)
            (:make_field "a" 1)
            (:make_field "foo" [1, 2, 3])
            (:make_field "bar" (:make_field baz 4) )
        "#,
            r#"
            {a: 1}
            {a: 1}
            {foo: [1, 2, 3]}
            {bar: {baz: 4}}
        "#,
        )
    }

    #[test]
    fn delta_eexp() -> IonResult<()> {
        stream_eq(
            r#"
           (:delta )
           (:delta 1)
           (:delta 0 1 2 3)
           (:delta (:: 1000 1 2 3 -2))
           (:delta 0 2 (:values 2 3))
           (:delta 1 4 (:none))
           (:delta (:repeat 4 1))
           (:delta (::))
           (:delta a::1 b::2)
        "#,
            r#"

           1
           0 1 3 6
           1000 1001 1003 1006 1004
           0 2 4 7
           1 5
           1 2 3 4
           
           1 3
        "#,
        )
    }

    #[test]
    fn delta_eexp_invalid_args() -> IonResult<()> {
        let source = "(:delta foo foo)";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        let source = "(:delta 1 3 foo)";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        Ok(())
    }

    #[test]
    fn sum_eexp() -> IonResult<()> {
        stream_eq(
            r#"
            (:sum 1 2)
            (:sum (:sum 1 2) 2)
            "#,
            r#"
            3
            5
            "#,
        )
    }

    #[test]
    fn make_decimal_eexp() -> IonResult<()> {
        stream_eq(
        r#"
        (:make_decimal 1 1)
        (:make_decimal -2 2)
        (:make_decimal (:values 3) 3)
        (:make_decimal (:values 4) (:values 4))
        (:make_decimal 199 -2)
        "#,
        r#"
        1d1
        -2d2
        3d3
        4d4
        1.99
        "#,
        )
    }

    #[test]
    fn make_decimal_arg_errors() -> IonResult<()> {
        // Test non-integer in first parameter
        let source = "(:make_decimal foo 0)";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        // Test non-integer in second parameter
        let source = "(:make_decimal 0 foo)";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        // Test multiple values in first parameter
        let source = "(:make_decimal (:values 0 1 2) 0)";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        // Test multiple values in second parameter
        let source = "(:make_decimal 0 (:values 0 1 2))";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        // Test empty value in first parameter
        let source = "(:make_decimal (:none) 0)";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        // Test empty value in second parameter
        let source = "(:make_decimal 0 (:none))";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");
        Ok(())
    }

    #[test]
    fn make_timestamp_eexp() -> IonResult<()> {
        stream_eq(
          r#"
            (:make_timestamp 2025)
            (:make_timestamp 2025 5)
            (:make_timestamp 2025 5 2)
            (:make_timestamp 2025 5 2 1 3)
            (:make_timestamp 2025 5 2 1 3 5)
            (:make_timestamp 2025 5 2 1 3 1.25)
            (:make_timestamp 2025 5 2 1 3 10.00)
            (:make_timestamp 2025 5 2 1 3 1.25 8)
            (:make_timestamp 2025 5 2 1 3 (:none) 8)
            (:make_timestamp 2025 5 2 1 3 5d1)
            (:make_timestamp 2025 5 2 1 3 5 8)
          "#,
          r#"
            2025T
            2025-05T
            2025-05-02T
            2025-05-02T01:03Z
            2025-05-02T01:03:05Z
            2025-05-02T01:03:01.25Z
            2025-05-02T01:03:10.00Z
            2025-05-02T01:03:01.25+00:08
            2025-05-02T01:03+00:08
            2025-05-02T01:03:50Z
            2025-05-02T01:03:05+00:08
          "#,
        )
    }

    #[rstest]
    #[case("(:make_timestamp)",                                    "no year specified")]
    #[case("(:make_timestamp 2025 (:none) 2)",                     "month empty, day provided")]
    #[case("(:make_timestamp 2025 5 2 1)",                         "no minute provided")]
    #[case("(:make_timestamp 2025 5 2 (:none) (:none) (:none) 5)", "offset provided with no minute")]
    #[case("(:make_timestamp 2025 5 2 (:none) (:none) 4",          "second provided with no minute")]
    #[case("(:make_timestamp 2025 100000)",                        "year out of range")]
    #[case("(:make_timestamp 2025 1 2 1 70)",                      "minute out of range")]
    #[case("(:make_timestamp 2025 1 2 1 40 -1)",                   "second out of range")]
    #[case("(:make_timestamp asdf)",                               "invalid type for year")]
    #[case("(:make_timestamp 2025 asdf)",                          "invalid type for month")]
    #[case("(:make_timestamp 2025 1 asdf)",                        "invalid type for day")]
    #[case("(:make_timestamp 2025 1 2 asdf 4)",                    "invalid type for hour")]
    #[case("(:make_timestamp 2025 1 2 3 asdf)",                    "invalid type for minute")]
    #[case("(:make_timestamp 2025 1 2 3 4 asdf)",                  "invalid type for second")]
    #[case("(:make_timestamp 2025 1 2 3 4 5 asdf)",                "invalid type for offset")]
    fn make_timestamp_errors(#[case] source: &str, #[case] message: &str) -> IonResult<()> {
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err(message);
        Ok(())
    }

    #[test]
    fn sum_eexp_arg_non_int() -> IonResult<()> {
        // Test non-integer in first parameter
        let source = "(:sum foo foo)";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");


        // Test non-integer in second parameter
        let source = "(:sum 1 foo)";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        // Test no-value argument
        let source = "(:sum 1 (:none))";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        // Test multi-value in second argument
        let source = "(:sum 1 (:values 1 3))";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        // Test multi-value in second argument
        let source = "(:sum 1 (:values 1 3))";
        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        actual_reader
            .read_all_elements()
            .expect_err("Unexpected success");

        Ok(())
    }

    #[test]
    fn combine_make_struct_with_make_field() -> IonResult<()> {
        stream_eq(
            r#"
            (:add_macros
                (macro new_yorker (name occupation)
                    (.make_struct
                        (.make_field "name" (%name))
                        (.make_field "occupation" (%occupation))
                        {city: "New York", state: NY})))
            (:new_yorker "Grace" "Author")
            (:new_yorker "Ravi" "Painter")
            (:new_yorker "Otis" "Musician")

        "#,
            r#"
            {
                name: "Grace",
                occupation: "Author",
                city: "New York",
                state: NY,
            }
            {
                name: "Ravi",
                occupation: "Painter",
                city: "New York",
                state: NY,
            }
            {
                name: "Otis",
                occupation: "Musician",
                city: "New York",
                state: NY,
            }
        "#,
        )
    }

    #[test]
    fn make_string_tdl_macro_invocation() -> IonResult<()> {
        let invocation = r#"
        (macro foo ()
          (.values
            (.make_string "foo" '''bar''' "\x62\u0061\U0000007A")
            (.make_string
                '''Hello'''
                ''', '''
                "world!"))
        )
        "#;
        eval_template_invocation(invocation, "(:foo)", r#" "foobarbaz" "Hello, world!" "#)
    }

    #[test]
    fn repeat_eexp() -> IonResult<()> {
        stream_eq(
            r#"
            (:repeat 1 )
            (:repeat 0 A)
            (:repeat 2 a)
            (:repeat 3 {foo: bar})
            (:repeat 2 (:repeat 2 a))
            "#,
            r#"

            a a
            {foo: bar} {foo: bar} {foo: bar}
            a a a a
            "#,
        )
    }

    #[test]
    fn repeat_eexp_numeric_arg() -> IonResult<()> {
        use crate::IonError;

        let source = "(:repeat foo a)";

        let mut actual_reader = Reader::new(v1_1::Text, source)?;
        let result= actual_reader.read_all_elements();

        if let Err(IonError::Decoding(_)) = result {
            Ok(())
        } else {
            panic!("unexpected success");
        }
    }


    #[test]
    fn e_expressions_inside_a_list() -> IonResult<()> {
        stream_eq(
            "[1, 2, (:values 3 4), 5, 6, (:make_string (:values foo bar) baz), 7]",
            r#"[1, 2, 3, 4, 5, 6, "foobarbaz", 7]"#,
        )?;
        Ok(())
    }

    #[test]
    fn macros_inside_a_tdl_list() -> IonResult<()> {
        eval_template_invocation(
            r#"
            (macro foo () 
                (.values [
                    1,
                    2,
                    (.values 3 4),
                    5,
                    (.none),
                    (.none),
                    6,
                    (.make_string "foo" "bar" "baz"),
                    7
                ])
            )
            "#,
            "(:foo)",
            "[1, 2, 3, 4, 5, 6, \"foobarbaz\", 7]",
        )?;
        Ok(())
    }

    #[test]
    fn e_expressions_inside_a_sexp() -> IonResult<()> {
        stream_eq(
            "(1 2 (:values 3 4) 5 6 (:make_string (:values foo bar) baz) 7)",
            r#"(1 2 3 4 5 6 "foobarbaz" 7)"#,
        )?;
        Ok(())
    }

    #[test]
    fn macros_inside_a_tdl_sexp() -> IonResult<()> {
        eval_template_invocation(
            r#"
            (macro foo ()
                (.make_sexp [
                    1,
                    2,
                    (.values 3 4),
                    5,
                    (.none),
                    (.none),
                    6,
                    (.make_string "foo" "bar" "baz"),
                    7
                ])
            )
            "#,
            "(:foo)",
            "(1 2 3 4 5 6 \"foobarbaz\" 7)",
        )?;
        Ok(())
    }

    #[test]
    fn e_expressions_inside_a_struct() -> IonResult<()> {
        stream_eq(
            r#"
            {
                a: 1,
                
                // When a macro in field value position produces more than one value,
                // a field will be emitted for each value. The same field name will be used for
                // each one.
                b: (:values 2 3),
                
                c: 4,
                
                // If the value-position-macro doesn't produce any values, the field will not
                // appear in the expansion.
                d: (:none),
                
                // If a single value is produced, a single field with that value will appear in the
                // output.
                e: (:make_string foo bar baz),
                
                f: 5,

                // If a macro appears in field name position, it MUST produce a single struct (which
                // may be empty). That struct's fields will be merged into the host struct.
                (:values {g: 6, h: 7}),
                
                g: 8
            }
            "#,
            r#"
            {
                a: 1,
                b: 2,
                b: 3,
                c: 4,
                // no 'd',
                e: "foobarbaz",
                f: 5,
                g: 6,
                h: 7,
                g: 8
            }
            "#,
        )?;
        Ok(())
    }

    #[test]
    fn macros_inside_a_tdl_struct() -> IonResult<()> {
        eval_template_invocation(
            r#"
            (macro foo () 
            (.values {
                a: 1,
                
                // When a macro in field value position produces more than one value,
                // a field will be emitted for each value. The same field name will be used for
                // each one.
                b: (.values 2 3),
                
                c: 4,
                
                // If the value-position-macro doesn't produce any values, the field will not
                // appear in the expansion.
                d: (.none),
                
                // If a single value is produced, a single field with that value will appear in the
                // output.
                e: (.make_string "foo" "bar" "baz"),
                
                // Nested struct to demonstrate recursive expansion
                f: {
                    quux: 5,
                    quuz: (.values true false),
                },
                
                g: 6
            })
            )
            "#,
            "(:foo)",
            r#"
            {
                a: 1,
                b: 2,
                b: 3,
                c: 4,
                // no 'd',
                e: "foobarbaz",
                f: {
                    quux: 5,
                    quuz: true,
                    quuz: false,
                },
                g: 6,
            }
           
            "#,
        )?;
        Ok(())
    }
}
