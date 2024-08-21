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
use std::ops::Range;

use bumpalo::collections::{String as BumpString, Vec as BumpVec};

use crate::lazy::decoder::{Decoder, HasSpan, LazyRawValueExpr};
use crate::lazy::expanded::e_expression::{
    ArgGroup, ArgGroupIterator, EExpression, EExpressionArgsIterator,
};
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{
    ParameterEncoding, TemplateBodyExprKind, TemplateBodyVariableReference, TemplateElement,
    TemplateMacroInvocation, TemplateMacroInvocationArgsIterator, TemplateMacroRef,
};
use crate::lazy::expanded::LazyExpandedValue;
use crate::lazy::expanded::{EncodingContextRef, TemplateVariableReference};
use crate::lazy::str_ref::StrRef;
use crate::lazy::text::raw::v1_1::arg_group::EExpArg;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::result::IonFailure;
use crate::{ExpandedValueSource, IonError, IonResult, LazyValue, Span, SymbolRef, ValueRef};

pub trait EExpArgGroupIterator<'top, D: Decoder>:
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
    type Iterator: EExpArgGroupIterator<'top, D>;

    fn encoding(&self) -> ParameterEncoding;
    fn resolve(self, context: EncodingContextRef<'top>) -> ArgGroup<'top, D>;

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

    /// Looks up the macro invoked by this E-expression in the given `EncodingContext`.
    /// If the lookup is successful, returns an `Ok` containing a resolved `EExpression` that holds
    /// a reference to the macro being invoked.
    /// If the ID cannot be found in the `EncodingContext`, returns `Err`.
    fn resolve(self, context: EncodingContextRef<'top>) -> IonResult<EExpression<'top, D>> {
        let invoked_macro = context.macro_table().macro_with_id(self.id()).ok_or_else(
            #[inline(never)]
            || IonError::decoding_error(format!("unrecognized macro ID {:?}", self.id())),
        )?;
        Ok(EExpression::new(context, self, invoked_macro))
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
#[derive(Copy, Clone, Debug)]
pub struct MacroExpr<'top, D: Decoder> {
    kind: MacroExprKind<'top, D>,
    variable: Option<TemplateVariableReference<'top>>,
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

    pub fn via_variable(mut self, variable_ref: TemplateVariableReference<'top>) -> Self {
        self.variable = Some(variable_ref);
        self
    }

    pub fn expand(&self, environment: Environment<'top, D>) -> IonResult<MacroExpansion<'top, D>> {
        match self.kind {
            MacroExprKind::TemplateMacro(t) => t.expand(environment),
            MacroExprKind::EExp(e) => e.expand(),
            MacroExprKind::EExpArgGroup(g) => g.expand(environment),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum MacroExprKind<'top, D: Decoder> {
    /// A macro invocation found in the body of a template.
    TemplateMacro(TemplateMacroInvocation<'top>),
    /// A macro invocation found in the data stream.
    EExp(EExpression<'top, D>),
    /// An e-expression argument group. (A `values` call with special encoding.)
    EExpArgGroup(ArgGroup<'top, D>),
}

impl<'top, D: Decoder> MacroExpr<'top, D> {
    pub fn from_template_macro(invocation: TemplateMacroInvocation<'top>) -> Self {
        MacroExpr::new(MacroExprKind::TemplateMacro(invocation))
    }

    pub fn from_eexp(eexp: EExpression<'top, D>) -> Self {
        MacroExpr::new(MacroExprKind::EExp(eexp))
    }

    pub fn from_eexp_arg_group(group: ArgGroup<'top, D>) -> Self {
        MacroExpr::new(MacroExprKind::EExpArgGroup(group))
    }

    pub fn variable(&self) -> Option<TemplateVariableReference<'top>> {
        self.variable
    }

    pub fn source(&self) -> MacroExprKind<'top, D> {
        self.kind
    }

    fn id(&self) -> MacroIdRef {
        use MacroExprKind::*;
        match &self.kind {
            TemplateMacro(m) => m.id(),
            EExp(e) => e.id(),
            EExpArgGroup(_) => MacroIdRef::LocalAddress(1), // `values`
        }
    }

    fn arguments(&self, environment: Environment<'top, D>) -> MacroExprArgsIterator<'top, D> {
        use MacroExprKind::*;
        let args_kind = match &self.kind {
            TemplateMacro(m) => {
                MacroExprArgsKind::<'top, D>::TemplateMacro(m.arguments(environment))
            }
            EExp(e) => MacroExprArgsKind::<'top, D>::EExp(e.arguments()),
            EExpArgGroup(group) => MacroExprArgsKind::<'top, D>::ArgGroup(group.expressions()),
        };
        MacroExprArgsIterator { source: args_kind }
    }

    pub(crate) fn invoked_macro(&self) -> MacroRef<'top> {
        use MacroExprKind::*;
        match &self.kind {
            TemplateMacro(m) => m.invoked_macro(),
            EExp(e) => e.invoked_macro(),
            EExpArgGroup(g) => g.invoked_macro(),
        }
    }

    pub(crate) fn context(&self) -> EncodingContextRef<'top> {
        use MacroExprKind::*;
        match self.kind {
            TemplateMacro(t) => t.context(),
            EExp(e) => e.context(),
            EExpArgGroup(g) => g.context(),
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub enum MacroExprArgsKind<'top, D: Decoder> {
    TemplateMacro(TemplateMacroInvocationArgsIterator<'top, D>),
    EExp(EExpressionArgsIterator<'top, D>),
    ArgGroup(ArgGroupIterator<'top, D>),
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

    pub fn from_arg_group(args: ArgGroupIterator<'top, D>) -> Self {
        MacroExprArgsIterator {
            source: MacroExprArgsKind::ArgGroup(args),
        }
    }

    fn is_exhausted(&self) -> bool {
        match self.source {
            MacroExprArgsKind::TemplateMacro(ref args) => args.is_exhausted(),
            MacroExprArgsKind::EExp(ref args) => args.is_exhausted(),
            MacroExprArgsKind::ArgGroup(ref args) => args.is_exhausted(),
        }
    }
}

impl<'top, D: Decoder> Iterator for MacroExprArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.source {
            MacroExprArgsKind::TemplateMacro(m) => m.next(),
            MacroExprArgsKind::EExp(e) => e.next(),
            MacroExprArgsKind::ArgGroup(g) => g.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.source {
            MacroExprArgsKind::TemplateMacro(m) => m.size_hint(),
            MacroExprArgsKind::EExp(e) => e.size_hint(),
            MacroExprArgsKind::ArgGroup(g) => g.size_hint(),
        }
    }
}

/// A single expression appearing in argument position within a macro invocation.
#[derive(Debug, Copy, Clone)]
pub enum ArgExpr<'top, D: Decoder> {
    /// An Ion value that requires no further evaluation.
    // `LazyExpandedValue` can be backed by either a stream value or a template value, so it covers
    // both contexts.
    ValueLiteral(LazyExpandedValue<'top, D>),
    /// A variable name that requires expansion.
    // Variable references can only appear in template macro invocations.
    Variable(TemplateBodyVariableReference),
    /// A macro invocation that requires evaluation.
    MacroInvocation(MacroExpr<'top, D>),
}

impl<'top, D: Decoder> ArgExpr<'top, D> {
    /// If this `ArgExpr` is a variable reference, resolves it to an expression from its originating
    /// environment. Returns an `ArgValueExpr` which is the value literal or macro invocation to
    /// which the variable referred.
    /// Otherwise, passes through the value literal or macro invocation.
    pub(crate) fn resolve(&self, environment: Environment<'top, D>) -> ValueExpr<'top, D> {
        match self {
            ArgExpr::ValueLiteral(value) => ValueExpr::ValueLiteral(*value),
            ArgExpr::Variable(variable) => environment.require_expr(variable.signature_index()),
            ArgExpr::MacroInvocation(invocation) => ValueExpr::MacroInvocation(*invocation),
        }
    }
}

/// A value expression (i.e. value literal or macro invocation) found in any context.
///
/// A `ValueExpr` is a resolved value. It cannot be a variable reference. If it is a macro
/// invocation, it holds a reference to the definition of the macro it invokes.
#[derive(Debug, Copy, Clone)]
pub enum ValueExpr<'top, D: Decoder> {
    /// An Ion value that requires no further evaluation.
    // `LazyExpandedValue` can be backed by either a stream value or a template value, so it covers
    // both contexts.
    ValueLiteral(LazyExpandedValue<'top, D>),
    /// A macro invocation that requires evaluation.
    MacroInvocation(MacroExpr<'top, D>),
}

impl<'top, D: Decoder> ValueExpr<'top, D> {
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
                    TemplateMacro(_) => true,
                    EExp(_) => false,
                    EExpArgGroup(_) => false,
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
                    SingletonEExp(_) => todo!(),
                    ValueLiteral(literal) => Some(literal.span()),
                    Template(_, _) => None,
                    Constructed(_, _) => None,
                }
            }
            ValueExpr::MacroInvocation(e) => {
                use MacroExprKind::*;
                match e.source() {
                    TemplateMacro(_) => None,
                    EExp(e) => Some(e.span()),
                    EExpArgGroup(g) => Some(g.span()),
                }
            }
        }
    }
}

/// Indicates which of the supported macros this represents and stores the state necessary to
/// continue evaluating that macro.
#[derive(Copy, Clone, Debug)]
pub enum MacroExpansionKind<'top, D: Decoder> {
    Void,
    Values(ValuesExpansion<'top, D>),
    MakeString(MakeStringExpansion<'top, D>),
    Annotate(AnnotateExpansion<'top, D>),
    Template(TemplateExpansion<'top>),
}

/// A macro in the process of being evaluated. Stores both the state of the evaluation and the
/// syntactic element that represented the macro invocation.
#[derive(Copy, Clone)]
pub struct MacroExpansion<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    kind: MacroExpansionKind<'top, D>,
    environment: Environment<'top, D>,
    is_complete: bool,
}

impl<'top, D: Decoder> MacroExpansion<'top, D> {
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

    /// Construct a new `MacroExpansion` and populate its evaluation environment as needed.
    pub(crate) fn initialize(
        environment: Environment<'top, D>,
        invocation_to_evaluate: MacroExpr<'top, D>,
    ) -> IonResult<MacroExpansion<'top, D>> {
        match invocation_to_evaluate.source() {
            MacroExprKind::TemplateMacro(t) => t.expand(environment),
            MacroExprKind::EExp(e) => e.expand(),
            MacroExprKind::EExpArgGroup(g) => g.expand(environment),
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
            Values(values_expansion) => values_expansion.next(context, environment),
            MakeString(make_string_expansion) => make_string_expansion.next(context, environment),
            Annotate(annotate_expansion) => annotate_expansion.next(context, environment),
            // `void` is trivial and requires no delegation
            Void => Ok(MacroExpansionStep::FinalStep(None)),
        }
    }

    // Calculate the next step in this macro expansion without advancing the expansion.
    pub fn peek_next_step(&self) -> IonResult<MacroExpansionStep<'top, D>> {
        let mut expansion_copy = *self;
        expansion_copy.next_step()
    }
}

impl<'top, D: Decoder> Debug for MacroExpansion<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let name = match &self.kind {
            MacroExpansionKind::Void => "void",
            MacroExpansionKind::Values(_) => "values",
            MacroExpansionKind::MakeString(_) => "make_string",
            MacroExpansionKind::Annotate(_) => "annotate",
            MacroExpansionKind::Template(t) => {
                return if let Some(name) = t.template.name() {
                    write!(f, "<expansion of template '{}'>", name)
                } else {
                    write!(f, "<expansion of anonymous template>")
                }
            }
        };
        write!(f, "<expansion of {name}>")
    }
}

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

impl<'top, D: Decoder> Default for EvaluatorState<'top, D> {
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

    #[inline]
    #[allow(clippy::should_implement_trait)]
    // ^-- Clippy complains this looks like Iterator::next().
    pub fn next(&mut self) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
        // This inlineable method checks whether the evaluator is empty to avoid a more expensive
        // method invocation when possible.
        if self.is_empty() {
            return Ok(None);
        }
        self.next_general_case()
    }

    /// The core macro evaluation logic.
    #[inline]
    fn next_general_case(&mut self) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
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
            // bump-allocate a proper stack. Instead, we take note of the environment this expansion
            // was using...
            let environment = expansion.environment;
            // ...get the next step in the expansion...
            let step = expansion.next_step()?;
            // ...and, if this was the last step in the expansion, pop it off the stack-of-one
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
                    self.push(invocation.expand(environment)?)
                    // This "tail eval" optimization--eagerly popping completed expansions off the
                    // stack to keep it flat--avoids allocations in many evaluations, e.g.:
                    // (:void)
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
        Self::for_macro_expr(Environment::empty(), macro_expr)
    }

    pub fn for_macro_expr(
        environment: Environment<'top, D>,
        macro_expr: MacroExpr<'top, D>,
    ) -> IonResult<Self> {
        let expansion = MacroExpansion::initialize(environment, macro_expr)?;
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
        match self.state {
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
                    .extend_from_slice_copy(&[original_expansion, new_expansion]);
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
        let expansion = match MacroExpansion::initialize(self.environment(), macro_expr) {
            Ok(expansion) => expansion,
            Err(e) => return Err(e),
        };
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
            let step = match current_expansion.next_step() {
                Ok(step) => step,
                Err(e) => return Err(e),
            };
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
pub struct EvaluatingIterator<'iter, 'top, D: Decoder> {
    evaluator: &'iter mut StackedMacroEvaluator<'top, D>,
    initial_stack_depth: usize,
}

impl<'iter, 'top, D: Decoder> EvaluatingIterator<'iter, 'top, D> {
    pub fn new(evaluator: &'iter mut StackedMacroEvaluator<'top, D>) -> Self {
        let initial_stack_depth = evaluator.macro_stack_depth();
        Self {
            evaluator,
            initial_stack_depth,
        }
    }
}

impl<'iter, 'top, D: Decoder> Iterator for EvaluatingIterator<'iter, 'top, D> {
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
pub struct ValuesExpansion<'top, D: Decoder> {
    // Which argument the macro is in the process of expanding
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> ValuesExpansion<'top, D> {
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

// ===== Implementation of the `make_string` macro =====

/// The evaluation state of the `make_string` macro.
///
/// `(:make_string ...)` eagerly expands each of its arguments in turn, concatenating the resulting
/// string and symbol values in order to make a single string.
///
/// This allows a writer to construct a string from fragments, some or all of which may reside
/// in the symbol or macro tables.
///
/// If any of the arguments expand to a non-text value, `make_string` will return an error.
///
/// Examples:
///   (:make_string "foo" "bar")              => "foobar"
///   (:make_string foo bar)                  => "foobar"
///   (:make_string "foo" bar)                => "foobar"
///   (:make_string "first_" $4)              => "first_name"
///   (:make_string (:values "first" "_") $4) => "first_name"
///   (:make_string)                          => ""
///   (:make_string "foo" 7)                  => Error
#[derive(Copy, Clone, Debug)]
pub struct MakeStringExpansion<'top, D: Decoder> {
    arguments: MacroExprArgsIterator<'top, D>,
}

impl<'top, D: Decoder> MakeStringExpansion<'top, D> {
    pub fn new(arguments: MacroExprArgsIterator<'top, D>) -> Self {
        Self { arguments }
    }

    /// Yields the next [`ValueExpr`] in this `make_string` macro's evaluation.
    pub fn next(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
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
                    let expansion = MacroExpansion::initialize(environment, invocation)?;
                    evaluator.push(expansion);
                    while let Some(value) = evaluator.next()? {
                        let text = value.read_resolved()?.expect_text()?;
                        buffer.push_str(text);
                    }
                }
            }
        }

        // Convert our BumpString<'bump> into a &'bump str that we can wrap in an `ExpandedValueRef`
        let constructed_text = buffer.into_bump_str();
        let value_ref: &'top ValueRef<'top, _> = context
            .allocator()
            .alloc_with(|| ValueRef::String(StrRef::from(constructed_text)));
        static EMPTY_ANNOTATIONS: &[SymbolRef] = &[];

        Ok(MacroExpansionStep::FinalStep(Some(
            ValueExpr::ValueLiteral(LazyExpandedValue::from_constructed(
                context,
                EMPTY_ANNOTATIONS,
                value_ref,
            )),
        )))
    }
}

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
                evaluator.push(invocation.expand(environment)?);
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
            ValueExpr::MacroInvocation(invocation) => {
                invocation.expand(environment)?.expand_singleton()?
            }
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

    pub(crate) fn next<'data: 'top, D: Decoder>(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        let expressions = self.template.body().expressions();
        let value_expr = match expressions.get(self.step_index) {
            None => return Ok(MacroExpansionStep::FinalStep(None)),
            Some(expr) => expr,
        };

        self.step_index += value_expr.num_expressions();
        let value_expr = match value_expr.kind() {
            TemplateBodyExprKind::Element(e) => {
                ValueExpr::ValueLiteral(LazyExpandedValue::from_template(
                    context,
                    environment,
                    TemplateElement::new(self.template.macro_ref(), e, value_expr.expr_range()),
                ))
            }
            TemplateBodyExprKind::Variable(variable) => {
                environment.require_expr(variable.signature_index())
            }
            TemplateBodyExprKind::MacroInvocation(raw_invocation) => {
                let invocation = raw_invocation.resolve(
                    context,
                    self.template.address(),
                    value_expr.expr_range(),
                );
                ValueExpr::MacroInvocation(invocation.into())
            }
        };

        if self.step_index >= expressions.len() {
            Ok(MacroExpansionStep::FinalStep(Some(value_expr)))
        } else {
            Ok(MacroExpansionStep::Step(value_expr))
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{v1_1, ElementReader, Int, IonResult, Reader};

    /// Reads `input` and `expected` using an expanding reader and asserts that their output
    /// is the same.
    fn eval_enc_expr<'data>(input: &'data str, expected: &'data str) -> IonResult<()> {
        let mut actual_reader = Reader::new(v1_1::Text, input.as_bytes())?;
        let actual = actual_reader.read_all_elements()?;

        let mut expected_reader = Reader::new(v1_1::Text, expected.as_bytes())?;
        // For the moment, this is using the old reader impl.
        let expected = expected_reader.read_all_elements()?;

        assert_eq!(actual, expected);
        Ok(())
    }

    /// Constructs a TdlTemplateEvaluator and evaluates the TDL macro invocation.
    /// Note that the current implementation of TDL template evaluation is very limited; templates
    /// cannot:
    /// * Be defined by an encoding directive
    /// * Be invoked by an e-expression (that is: from a data stream)
    /// * Have parameters
    /// * Expand variables
    ///
    /// This test exists to demonstrate that macro evaluation within the TDL context works the
    /// same as evaluation in the data stream.
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
    fn multiple_top_level_values() -> IonResult<()> {
        eval_template_invocation(
            "(macro foo () (values 1 2 3 4 5))",
            r#"
                (:foo)
            "#,
            r#"
                1 2 3 4 5
            "#,
        )
    }

    #[test]
    fn annotate() -> IonResult<()> {
        eval_template_invocation(
            r#"(macro foo (x) (annotate (values "bar" "baz" "quux") x))"#,
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

        mod bang {
            use crate::lazy::expanded::macro_evaluator::tests::eval_template_invocation;

            #[test]
            #[should_panic]
            fn required_does_not_accept_empty_rest() {
                eval_template_invocation(
                    "(macro foo (x) (make_string x x))",
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
            fn required_does_not_accept_empty_arg_group() {
                eval_template_invocation(
                    "(macro foo (x) (make_string x x))",
                    r#"
                        (:foo (:))
                    "#,
                    r#"
                        // should raise an error
                    "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn required_does_not_accept_populated_arg_group() {
                eval_template_invocation(
                    "(macro foo (x) (make_string x x))",
                    r#"
                (:foo (:))
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }
        }

        mod optional {
            use crate::lazy::expanded::macro_evaluator::tests::eval_template_invocation;
            use crate::IonResult;

            #[test]
            fn optional_accepts_empty_or_expr() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x?) (make_string x x))",
                    r#"
                (:foo)           // x is implicitly empty
                (:foo (:))       // x is explicitly empty
                (:foo (:   ))    // x is explicitly empty with extra whitespace
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
            #[should_panic]
            fn optional_does_not_accept_populated_arg_groups() {
                eval_template_invocation(
                    "(macro foo (x?) (make_string x x))",
                    r#"
                (:foo (: "a"))
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }
        }

        mod star {
            use crate::lazy::expanded::macro_evaluator::tests::eval_template_invocation;
            use crate::IonResult;

            #[test]
            fn star_accepts_groups() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x y*) (make_string x y))",
                    r#"
                (:foo "hello" (: " there " "friend!" ))
            "#,
                    r#"
                "hello there friend!"
            "#,
                )
            }

            #[test]
            fn trailing_star_accepts_rest() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x y*) (make_string x y))",
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
            fn star_accepts_value_literal() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x y* z*) (make_string x y z))",
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
                    "(macro foo (x y*) (make_string x y))",
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
                    "(macro foo (x y* z*) (make_string x y))",
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

        mod plus {
            use crate::lazy::expanded::macro_evaluator::tests::eval_template_invocation;

            #[test]
            #[should_panic]
            fn plus_does_not_accept_empty_arg_group() {
                eval_template_invocation(
                    "(macro foo (x+) (make_string x x))",
                    r#"
                (:foo (:))
            "#,
                    r#"
                // should raise an error
            "#,
                )
                .unwrap()
            }

            #[test]
            #[should_panic]
            fn plus_does_not_accept_empty_rest() {
                eval_template_invocation(
                    "(macro foo (x+) (make_string x x))",
                    r#"
                (:foo)
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
            "(macro foo (x y) (make_string x y))",
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
        let template_definition = "(macro int_pair (flex_uint::$x flex_uint::$y) (values $x $y)))";
        let tests: &[(&[u8], (u64, u64))] = &[
            // invocation+args, expected arg values
            (&[0x04, 0x01, 0x01], (0, 0)),
            (&[0x04, 0x09, 0x03], (4, 1)),
            (&[0x04, 0x0B, 0x0D], (5, 6)), // TODO: non-required cardinalities
        ];

        for test in tests {
            let mut stream = vec![0xE0, 0x01, 0x00, 0xEA];
            stream.extend_from_slice(test.0);
            println!(
                "stream {:02X?} -> pair ({}, {})",
                test.0, test.1 .0, test.1 .1
            );
            let mut reader = Reader::new(v1_1::Binary, stream.as_slice())?;
            reader.register_template_src(template_definition)?;
            assert_eq!(
                reader.next()?.unwrap().read()?.expect_int()?,
                Int::from(test.1 .0)
            );
            assert_eq!(
                reader.next()?.unwrap().read()?.expect_int()?,
                Int::from(test.1 .1)
            );
        }
        Ok(())
    }

    #[test]
    fn it_takes_all_kinds() -> IonResult<()> {
        eval_template_invocation(
            r#"(macro foo () 
                (values 
                    null 
                    true
                    1
                    1e0
                    1.0
                    2023T
                    "1"
                    (literal '1') // TODO: Only treat identifiers as variables
                    {{MQ==}}
                    {{"1"}}
                    [1]
                    (literal (1)) // Prevent the sexp from being considered a macro invocation
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
                        symbols: symbols
                    }
                )
            "#,
            r#"
                (:lst ["foo", "bar", "baz"]) $10 $11 $12
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
                    (values
                        $ion_symbol_table::{
                            symbols: symbols
                        }
                    )
                )
            "#,
            r#"
                $ion_symbol_table::{
                    symbols: ["foo", "bar"]
                }
                
                // These symbols refer to the symtab defined above
                $10
                $11
                
                // The $10 and $11 here _also_ refer to the symtab above because the
                // new LST won't be applied until after this top-level expression.
                (:values (:lst ["baz", "quux"]) $10 $11)
                
                // These refer to the new LST
                $10 $11
            "#,
            r#"
                foo bar foo bar baz quux
            "#,
        )
    }

    #[test]
    fn swap() -> IonResult<()> {
        eval_template_invocation(
            "(macro swap (x y) (values y x))",
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
                            first: first,
                            last: last,
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
                        'timestamp': timestamp,
                        'threadId': thread_id,
                        'threadName': (make_string "scheduler-thread-" thread_name),
                        'loggerName': "com.example.organization.product.component.ClassName",
                        'logLevel': (literal INFO),
                        'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
                        'parameters': [
                            "SUCCESS",
                            (make_string "example-client-" client_num),
                            (make_string "aws-us-east-5f-" host_id),
                            parameters
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
            r"(macro foo () (values 1 2 (values 3 4 (values 5 6) 7 8) 9 10))",
            "(:foo)",
            "1 2 3 4 5 6 7 8 9 10",
        )
    }

    #[test]
    fn values_e_expression() -> IonResult<()> {
        eval_enc_expr(
            r"(:values 1 2 (:values 3 4 (:values 5 6) 7 8) 9 10)",
            "1 2 3 4 5 6 7 8 9 10",
        )
    }

    #[test]
    fn void_e_expression() -> IonResult<()> {
        eval_enc_expr(r"(:values (:void) (:void) (:void) )", "/* nothing */")
    }

    #[test]
    fn void_tdl_macro_invocation() -> IonResult<()> {
        eval_template_invocation(
            r"(macro foo () (values (void) (void) (void)))",
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
        eval_enc_expr(
            e_expression,
            r#" "foobarbaz" "foobarbaz" "first name" "Hello, world!" "#,
        )
    }

    #[test]
    fn make_string_tdl_macro_invocation() -> IonResult<()> {
        let invocation = r#"
        (macro foo ()
          (values
            (make_string "foo" '''bar''' "\x62\u0061\U0000007A")
            (make_string 
                '''Hello'''
                ''', '''
                "world!"))
        )
        "#;
        eval_template_invocation(invocation, "(:foo)", r#" "foobarbaz" "Hello, world!" "#)
    }

    #[test]
    fn e_expressions_inside_a_list() -> IonResult<()> {
        eval_enc_expr(
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
                (values [
                    1,
                    2,
                    (values 3 4),
                    5,
                    (void),
                    (void),
                    6,
                    (make_string "foo" "bar" "baz"),
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
        eval_enc_expr(
            "(1 2 (:values 3 4) 5 6 (:make_string (:values foo bar) baz) 7)",
            r#"(1 2 3 4 5 6 "foobarbaz" 7)"#,
        )?;
        Ok(())
    }

    // TODO: macros_inside_a_tdl_sexp()
    // This requires an implementation of TDL's `(make_sexp)`.

    #[test]
    fn e_expressions_inside_a_struct() -> IonResult<()> {
        eval_enc_expr(
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
                d: (:void),
                
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
            (values {
                a: 1,
                
                // When a macro in field value position produces more than one value,
                // a field will be emitted for each value. The same field name will be used for
                // each one.
                b: (values 2 3),
                
                c: 4,
                
                // If the value-position-macro doesn't produce any values, the field will not
                // appear in the expansion.
                d: (void),
                
                // If a single value is produced, a single field with that value will appear in the
                // output.
                e: (make_string "foo" "bar" "baz"),
                
                // Nested struct to demonstrate recursive expansion
                f: {
                    quux: 5,
                    quuz: (values true false),
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
