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
use crate::lazy::expanded::macro_table::{MacroKind, MacroRef};
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{
    ParameterEncoding, TemplateBody, TemplateBodyValueExpr, TemplateBodyVariableReference,
    TemplateElement, TemplateMacroInvocation, TemplateMacroInvocationArgsIterator,
    TemplateMacroRef, TemplateValue,
};
use crate::lazy::expanded::{EncodingContextRef, TemplateVariableReference};
use crate::lazy::expanded::{ExpandedValueRef, LazyExpandedValue};
use crate::lazy::str_ref::StrRef;
use crate::lazy::text::raw::v1_1::arg_group::EExpArg;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::result::IonFailure;
use crate::{ExpandedValueSource, HasRange, IonError, IonResult, LazyValue};

pub trait EExpressionArgGroup<'top, D: Decoder>:
    HasSpan<'top> + Debug + Copy + Clone + IntoIterator<Item = IonResult<LazyRawValueExpr<'top, D>>>
{
    fn encoding(&self) -> ParameterEncoding;
    fn resolve(self, context: EncodingContextRef<'top>) -> ArgGroup<'top, D>;

    fn iter(self) -> Self::IntoIter {
        self.into_iter()
    }
}

/// The syntactic entity in format `D` that represents an e-expression. This expression has not
/// yet been resolved in the current encoding context.
pub trait RawEExpression<'top, D: Decoder<EExp<'top> = Self>>:
    HasSpan<'top> + Debug + Copy + Clone
{
    /// An iterator that yields the macro invocation's arguments in order.
    type RawArgumentsIterator: Iterator<Item = IonResult<EExpArg<'top, D>>>;

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

    fn make_evaluation_environment(
        &self,
        context: EncodingContextRef<'top>,
    ) -> IonResult<Environment<'top, D>> {
        let allocator = context.allocator();
        let raw_args = self.raw_arguments();
        let capacity_hint = raw_args.size_hint().0;
        let mut env_exprs = BumpVec::with_capacity_in(capacity_hint, allocator);
        // Populate the environment by parsing the arguments from input
        for expr in self.raw_arguments() {
            env_exprs.push(expr?.resolve(context)?);
        }

        Ok(Environment::new(env_exprs.into_bump_slice()))
    }
}

/// An invocation of a macro found in either the data stream or in the body of a template.
/// This invocation has been resolved in the current encoding context, and holds a reference to
/// the definition of the macro being invoked.
#[derive(Copy, Clone, Debug)]
pub struct MacroExpr<'top, D: Decoder> {
    source: MacroExprSource<'top, D>,
    variable: Option<TemplateVariableReference<'top>>,
}

impl<'top, D: Decoder> MacroExpr<'top, D> {
    pub fn new(source: MacroExprSource<'top, D>) -> Self {
        Self {
            source,
            variable: None,
        }
    }

    pub fn via_variable(mut self, variable_ref: TemplateVariableReference<'top>) -> Self {
        self.variable = Some(variable_ref);
        self
    }
}

#[derive(Copy, Clone, Debug)]
pub enum MacroExprSource<'top, D: Decoder> {
    /// A macro invocation found in the body of a template.
    TemplateMacro(TemplateMacroInvocation<'top>),
    /// A macro invocation found in the data stream.
    EExp(EExpression<'top, D>),
    /// An e-expression argument group. (A `values` call with special encoding.)
    EExpArgGroup(ArgGroup<'top, D>),
}

impl<'top, D: Decoder> MacroExpr<'top, D> {
    pub fn from_template_macro(invocation: TemplateMacroInvocation<'top>) -> Self {
        MacroExpr::new(MacroExprSource::TemplateMacro(invocation))
    }

    pub fn from_eexp(eexp: EExpression<'top, D>) -> Self {
        MacroExpr::new(MacroExprSource::EExp(eexp))
    }

    pub fn from_eexp_arg_group(group: ArgGroup<'top, D>) -> Self {
        MacroExpr::new(MacroExprSource::EExpArgGroup(group))
    }

    pub fn variable(&self) -> Option<TemplateVariableReference<'top>> {
        self.variable
    }

    pub fn source(&self) -> MacroExprSource<'top, D> {
        self.source
    }

    fn id(&self) -> MacroIdRef {
        use MacroExprSource::*;
        match &self.source {
            TemplateMacro(m) => m.id(),
            EExp(e) => e.id(),
            EExpArgGroup(_) => MacroIdRef::LocalAddress(1), // `values`
        }
    }

    fn arguments(&self, environment: Environment<'top, D>) -> MacroExprArgsIterator<'top, D> {
        use MacroExprSource::*;
        let args_kind = match &self.source {
            TemplateMacro(m) => MacroExprArgsKind::<'top, D>::Macro(m.arguments(environment)),
            EExp(e) => MacroExprArgsKind::<'top, D>::EExp(e.arguments()),
            EExpArgGroup(group) => MacroExprArgsKind::<'top, D>::ArgGroup(group.expressions()),
        };
        MacroExprArgsIterator { source: args_kind }
    }

    fn invoked_macro(&self) -> MacroRef<'top> {
        use MacroExprSource::*;
        match &self.source {
            TemplateMacro(m) => m.invoked_macro(),
            EExp(e) => e.invoked_macro(),
            EExpArgGroup(g) => g.invoked_macro(),
        }
    }

    pub(crate) fn context(&self) -> EncodingContextRef<'top> {
        use MacroExprSource::*;
        match self.source {
            TemplateMacro(t) => t.context(),
            EExp(e) => e.context(),
            EExpArgGroup(g) => g.context(),
        }
    }

    fn new_evaluation_environment(
        &self,
        parent_environment: Environment<'top, D>,
    ) -> IonResult<Environment<'top, D>> {
        use MacroExprSource::*;
        let allocator = self.context().allocator();
        let arguments = match self.source {
            TemplateMacro(_) => self.arguments(parent_environment),
            EExpArgGroup(g) => return g.new_evaluation_environment(),
            EExp(e) => return e.new_evaluation_environment(),
        };
        // Use the iterator's size hint to determine an initial capacity to aim for.
        let num_args_hint = arguments.size_hint();
        let capacity_hint = num_args_hint.1.unwrap_or(num_args_hint.0);
        let mut env_exprs = BumpVec::with_capacity_in(capacity_hint, allocator);
        for arg in arguments {
            env_exprs.push(arg?);
        }
        Ok(Environment::new(env_exprs.into_bump_slice()))
    }
}

pub enum MacroExprArgsKind<'top, D: Decoder> {
    Macro(TemplateMacroInvocationArgsIterator<'top, D>),
    EExp(EExpressionArgsIterator<'top, D>),
    ArgGroup(ArgGroupIterator<'top, D>),
}

pub struct MacroExprArgsIterator<'top, D: Decoder> {
    source: MacroExprArgsKind<'top, D>,
}

impl<'top, D: Decoder> Iterator for MacroExprArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.source {
            MacroExprArgsKind::Macro(m) => m.next(),
            MacroExprArgsKind::EExp(e) => e.next(),
            MacroExprArgsKind::ArgGroup(g) => g.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match &self.source {
            MacroExprArgsKind::Macro(m) => m.size_hint(),
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
    /// If this `ValueExpr` represents an entity encoded in te data stream, returns `Some(range)`.
    /// If it represents a template value or a constructed value, returns `None`.
    pub fn range(&self) -> Option<Range<usize>> {
        match self {
            ValueExpr::ValueLiteral(value) => {
                use ExpandedValueSource::*;
                match value.source {
                    ValueLiteral(literal) => Some(literal.range()),
                    Template(_, _) => None,
                    Constructed(_, _) => None,
                }
            }
            ValueExpr::MacroInvocation(e) => {
                use MacroExprSource::*;
                match e.source() {
                    TemplateMacro(_) => None,
                    EExp(e) => Some(e.range()),
                    EExpArgGroup(g) => Some(g.range()),
                }
            }
        }
    }
}

/// Indicates which of the supported macros this represents and stores the state necessary to
/// continue evaluating that macro.
pub enum MacroExpansionKind<'top, D: Decoder> {
    Void,
    Values(ValuesExpansion<'top, D>),
    MakeString(MakeStringExpansion<'top, D>),
    Template(TemplateExpansion<'top>),
}

/// A macro in the process of being evaluated. Stores both the state of the evaluation and the
/// syntactic element that represented the macro invocation.
pub struct MacroExpansion<'top, D: Decoder> {
    kind: MacroExpansionKind<'top, D>,
    invocation: MacroExpr<'top, D>,
    is_complete: bool,
}

impl<'top, D: Decoder> MacroExpansion<'top, D> {
    pub(crate) fn new(kind: MacroExpansionKind<'top, D>, invocation: MacroExpr<'top, D>) -> Self {
        Self {
            kind,
            invocation,
            is_complete: false,
        }
    }
}

impl<'top, D: Decoder> Debug for MacroExpansion<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let name = match &self.kind {
            MacroExpansionKind::Void => "void",
            MacroExpansionKind::Values(_) => "values",
            MacroExpansionKind::MakeString(_) => "make_string",
            MacroExpansionKind::Template(t) => {
                return if let Some(name) = t.template.name() {
                    write!(f, "<expansion of template '{}'>", name)
                } else {
                    write!(
                        f,
                        "<expansion of anonymous template at address {}>",
                        t.template.address()
                    )
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

impl<'top, D: Decoder> MacroExpansion<'top, D> {
    /// Continues evaluating this macro until it:
    ///   * produces another value.
    ///   * encounters another macro or variable that needs to be expanded.
    ///   * is completed.
    fn next(
        &mut self,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        use MacroExpansionKind::*;
        let context = self.invocation.context();
        // Delegate the call to `next()` based on the macro kind.
        match &mut self.kind {
            Template(template_expansion) => template_expansion.next(context, environment),
            Values(values_expansion) => values_expansion.next(context, environment),
            MakeString(make_string_expansion) => make_string_expansion.next(context, environment),
            // `void` is trivial and requires no delegation
            Void => Ok(MacroExpansionStep::FinalStep(None)),
        }
    }
}

pub type MacroStack<'top, D> = BumpVec<'top, MacroExpansion<'top, D>>;
pub type EnvironmentStack<'top, D> = BumpVec<'top, Environment<'top, D>>;

/// Evaluates macro invocations recursively, yielding a single expanded value at a time.
///
/// The evaluator supports the cross product of three use case dimensions:
///
///   {e-expression, template macro invocation}
///   x {text, binary}
///   x {eager, lazy}
///
/// For incremental/lazy evaluation, push a macro invocation onto the stack using
/// [`MacroEvaluator::push`] and then use [`MacroEvaluator::next`] to evaluate the next value.
///
/// For eager evaluation, use [`MacroEvaluator::evaluate`], which returns an iterator that will
/// yield the expanded values.
pub struct MacroEvaluator<'top, D: Decoder> {
    // A stack with the most recent macro invocations at the top. This stack grows each time a macro
    // of any kind begins evaluation.
    macro_stack: MacroStack<'top, D>,
    // A stack of _template_ macro invocation environments. This stack only grows when a template
    // macro is invoked from any context. For example, given these template definitions:
    //     (macro foo (x) (values 1 2 x))
    //     (macro bar (y) (foo y))
    // and this invocation:
    //     (:bar 3)
    // A new environment [/*y=*/ 3] would be pushed for the invocation of `bar`, and another
    // environment [/*x=y=*/ 3] would be pushed for the invocation of `foo` within `bar`. However,
    // no environment would be created/pushed for the invocation of the `values` macro within `foo`.
    // For any macro being evaluated, the current environment is always the one at the top of the
    // environment stack.
    env_stack: EnvironmentStack<'top, D>,
}

impl<'top, D: Decoder> MacroEvaluator<'top, D> {
    #[inline]
    pub fn new(context: EncodingContextRef<'top>, environment: Environment<'top, D>) -> Self {
        const INITIAL_MACRO_STACK_CAPACITY: usize = 8;
        const INITIAL_ENV_STACK_CAPACITY: usize = 8;
        let macro_stack =
            BumpVec::with_capacity_in(INITIAL_MACRO_STACK_CAPACITY, context.allocator());
        let mut env_stack =
            BumpVec::with_capacity_in(INITIAL_ENV_STACK_CAPACITY, context.allocator());
        env_stack.push(environment);
        Self {
            macro_stack,
            env_stack,
        }
    }

    /// Returns the number of macros that are currently being evaluated.
    pub fn macro_stack_depth(&self) -> usize {
        self.macro_stack.len()
    }

    /// Returns the current environment (i.e. the one at the top of the macro stack.)
    pub fn environment(&self) -> Environment<'top, D> {
        // The stack is never completely empty; the 'root' evaluator is created with an empty
        // environment at the base of the stack.
        *self.env_stack.last().unwrap()
    }

    /// Initializes a [`MacroExpansion`] that contains the necessary state to incrementally evaluate
    /// the provided macro invocation.
    ///
    /// Returns an error if the invocation is invalid due to missing or malformed arguments.
    fn initialize_expansion(
        &mut self,
        invocation_to_evaluate: MacroExpr<'top, D>,
    ) -> IonResult<MacroExpansion<'top, D>> {
        // Initialize a `MacroExpansionKind` with the state necessary to evaluate the requested
        // macro.
        let macro_ref: MacroRef<'top> = invocation_to_evaluate.invoked_macro();
        let environment = self.environment();
        let arguments = invocation_to_evaluate.arguments(environment);
        let expansion_kind = match macro_ref.kind() {
            MacroKind::Void => MacroExpansionKind::Void,
            MacroKind::Values => MacroExpansionKind::Values(ValuesExpansion::new(
                arguments,
                self.macro_stack_depth(),
            )),
            MacroKind::MakeString => {
                MacroExpansionKind::MakeString(MakeStringExpansion::new(arguments))
            }
            MacroKind::Template(template_body) => self.initialize_template_macro_expansion(
                environment,
                macro_ref,
                &invocation_to_evaluate,
                template_body,
            )?,
        };
        Ok(MacroExpansion {
            kind: expansion_kind,
            invocation: invocation_to_evaluate,
            is_complete: false,
        })
    }

    fn initialize_template_macro_expansion(
        &mut self,
        parent_environment: Environment<'top, D>,
        macro_ref: MacroRef<'top>,
        invocation: &MacroExpr<'top, D>,
        template_body: &'top TemplateBody,
    ) -> IonResult<MacroExpansionKind<'top, D>> {
        let template_ref = TemplateMacroRef::new(macro_ref, template_body);
        let new_environment = invocation.new_evaluation_environment(parent_environment)?;
        self.env_stack.push(new_environment);
        Ok(MacroExpansionKind::Template(TemplateExpansion::new(
            template_ref,
        )))
    }

    /// Given a syntactic element representing a macro invocation, attempt to resolve it with the
    /// current encoding context and push the resulting `MacroExpansion` onto the stack.
    pub fn push(&mut self, invocation: impl Into<MacroExpr<'top, D>>) -> IonResult<()> {
        let macro_expr = invocation.into();
        let expansion = match self.initialize_expansion(macro_expr) {
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
    #[inline(always)]
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
            let environment = self.environment();

            // Get the expansion at the top of the stack.
            let current_expansion = match self.macro_stack.last_mut() {
                None => return Ok(None),
                Some(expansion) => expansion,
            };

            // Ask that expansion to continue its evaluation by one step.
            let step = current_expansion.next(environment)?;
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
            self.pop_completed_macro();
            match self.macro_stack.last() {
                Some(expansion) if expansion.is_complete => continue,
                _ => break,
            }
        }
    }

    fn pop_completed_macro(&mut self) {
        // Check to see if the completed value was a template. If so, discard its environment.
        let completed_kind = &self.macro_stack.last().unwrap().kind;
        if matches!(completed_kind, MacroExpansionKind::Template(_)) {
            // NB: Here and below, we use `truncate()` instead of `pop()` so the value can
            // be dropped in place without incurring a move. That move runs afoul of the
            // aliasing requirements that `miri` looks for, though I'm unsure why.
            // Once Polonius lands and we are able to remove the `unsafe` usages in
            // the LazyExpandingReader, this will be unnecessary.
            self.env_stack.truncate(self.env_stack.len() - 1);
        }
        self.macro_stack.truncate(self.macro_stack.len() - 1);
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
    evaluator: &'iter mut MacroEvaluator<'top, D>,
    initial_stack_depth: usize,
}

impl<'iter, 'top, D: Decoder> EvaluatingIterator<'iter, 'top, D> {
    pub fn new(evaluator: &'iter mut MacroEvaluator<'top, D>) -> Self {
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
pub struct ValuesExpansion<'top, D: Decoder> {
    // Which argument the macro is in the process of expanding
    arguments: MacroExprArgsIterator<'top, D>,
    // The stack depth where this `values` call lives. When the stack shrinks below this depth,
    // evaluation is complete.
    initial_eval_stack_depth: usize,
}

impl<'top, D: Decoder> ValuesExpansion<'top, D> {
    pub fn new(arguments: MacroExprArgsIterator<'top, D>, initial_eval_stack_depth: usize) -> Self {
        Self {
            arguments,
            initial_eval_stack_depth,
        }
    }

    /// Yields the next [`ValueExpr`] in this macro's evaluation.
    pub fn next(
        &mut self,
        _context: EncodingContextRef<'top>,
        _environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        // We visit the argument expressions in the invocation in order from left to right.
        match self.arguments.next() {
            None => Ok(MacroExpansionStep::FinalStep(None)),
            Some(Ok(expr)) => Ok(MacroExpansionStep::Step(expr)),
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
        let mut maybe_evaluator: Option<MacroEvaluator<'top, D>> = None;

        for arg_result in &mut self.arguments {
            let arg_expr = arg_result?;
            match arg_expr {
                ValueExpr::ValueLiteral(expanded_value) => {
                    let value = LazyValue::new(expanded_value);
                    let text = value.read()?.expect_text()?;
                    buffer.push_str(text);
                }
                ValueExpr::MacroInvocation(invocation) => {
                    let evaluator = match &mut maybe_evaluator {
                        Some(inner) => inner,
                        None => maybe_evaluator.insert(MacroEvaluator::new(context, environment)),
                    };
                    for value_result in evaluator.evaluate(invocation)? {
                        let value = LazyValue::new(value_result?);
                        let text = value.read()?.expect_text()?;
                        buffer.push_str(text);
                    }
                }
            }
        }

        // Convert our BumpString<'bump> into a &'bump str that we can wrap in an `ExpandedValueRef`
        let constructed_text = buffer.into_bump_str();
        let expanded_value_ref: &'top ExpandedValueRef<'top, D> = context
            .allocator()
            .alloc_with(|| ExpandedValueRef::String(StrRef::from(constructed_text)));
        static EMPTY_ANNOTATIONS: &[&str] = &[];

        Ok(MacroExpansionStep::FinalStep(Some(
            ValueExpr::ValueLiteral(LazyExpandedValue::from_constructed(
                context,
                EMPTY_ANNOTATIONS,
                expanded_value_ref,
            )),
        )))
    }
}

// ===== Implementation of template macro expansion =====

/// The evaluation state of a template expansion.
#[derive(Clone, Debug)]
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

    fn next<'data: 'top, D: Decoder>(
        &mut self,
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
    ) -> IonResult<MacroExpansionStep<'top, D>> {
        let expressions = self.template.body().expressions();
        let value_expr = match expressions.get(self.step_index) {
            None => return Ok(MacroExpansionStep::FinalStep(None)),
            Some(expr) => expr,
        };
        self.step_index += 1;

        let value_expr = match value_expr {
            TemplateBodyValueExpr::Element(e) => {
                match e.value() {
                    TemplateValue::List(range)
                    | TemplateValue::SExp(range)
                    | TemplateValue::Struct(range, _) => self.step_index += range.len(),
                    _ => {}
                }
                ValueExpr::ValueLiteral(LazyExpandedValue::from_template(
                    context,
                    environment,
                    TemplateElement::new(self.template, e),
                ))
            }
            TemplateBodyValueExpr::Variable(variable) => {
                environment.require_expr(variable.signature_index())
            }
            TemplateBodyValueExpr::MacroInvocation(raw_invocation) => {
                let invocation = raw_invocation.resolve(self.template, context);
                self.step_index += invocation.arg_expressions().len();
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
    use crate::{v1_1, ElementReader, IonResult, Reader};
    use criterion::black_box;
    use std::hint;

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
            fn narrow() -> IonResult<()> {
                eval_template_invocation(
                    "(macro foo (x?) (make_string x x))",
                    r#"
                (:foo (:foo a))  // x is `(:foo a)`
            "#,
                    r#"
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
                    (quote '1') // TODO: Only treat identifiers as variables
                    {{MQ==}}
                    {{"1"}}
                    [1]
                    (quote (1)) // Prevent the sexp from being considered a macro invocation
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
                        'logLevel': (quote INFO),
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
                    "18b4fa"
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
                            "aws-us-east-5f-18b4fa",
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
    fn check_check() -> IonResult<()> {
        eval_enc_expr(r"(:values 1 (:values 2 3) 4)", "1 2 3 4")
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

    #[test]
    fn x() -> IonResult<()> {
        const NUM_VALUES: usize = 10_000;

        let template_definition_text = r#"
            (macro event (timestamp thread_id thread_name client_num host_id parameters*)
                {
                    'timestamp': timestamp,
                    'threadId': thread_id,
                    'threadName': thread_name,
                    'loggerName': "com.example.organization.product.component.ClassName",
                    'logLevel': (quote INFO),
                    'format': "Request status: {} Client ID: {} Client Host: {} Client Region: {} Timestamp: {}",
                    'parameters': [
                        "SUCCESS",
                        client_num,
                        host_id,
                        parameters
                    ]
                }
            )
        "#;

        #[rustfmt::skip]
        let mut binary_1_1_data_body: Vec<u8> = vec![
            0x03, // Macro ID 3
            0b10, // [NOTE: `0b` prefix] `parameters*` arg is an arg group
            0x66, // 6-byte integer (`timestamp` param)
            0x75, 0x5D, 0x63, 0xEE, 0x84, 0x01,
            0x62, // 2-byte integer (`thread_id` param)
            0xA2, 0x01,
            0xF9, // long-form string (`thread_name` param)
            0x25, // FlexUInt byte length 18
            // "scheduler-thread-6"
            0x73, 0x63, 0x68, 0x65, 0x64, 0x75, 0x6C, 0x65, 0x72, 0x2D, 0x74, 0x68, 0x72, 0x65, 0x61, 0x64, 0x2D, 0x36,
            0xF9, // 1-byte string (`client_num` param)
            0x21, // FlexUInt byte length 16
            // "example-client-1"
            0x65, 0x78, 0x61, 0x6D, 0x70, 0x6C, 0x65, 0x2D, 0x63, 0x6C, 0x69, 0x65, 0x6E, 0x74, 0x2D, 0x31,
            0xF9, // long-form string (`host_id` param)
            0x2B, // FlexUInt byte length 21
            // "aws-us-east-5f-18b4fa"
            0x61, 0x77, 0x73, 0x2D, 0x75, 0x73,
            0x2D, 0x65, 0x61, 0x73, 0x74, 0x2D,
            0x35, 0x66, 0x2D, 0x31, 0x38, 0x62,
            0x34, 0x66, 0x61,
            0x4D, // Arg group length prefix
            0x98, // 8-byte string
            0x72, 0x65, 0x67, 0x69,
            0x6F, 0x6E, 0x20, 0x34,
            0xF9, // Long-form, 27-byte string
            0x37, 0x32, 0x30, 0x32,
            0x32, 0x2D, 0x31, 0x32,
            0x2D, 0x30, 0x37, 0x54,
            0x32, 0x30, 0x3A, 0x35,
            0x39, 0x3A, 0x35, 0x39,
            0x2E, 0x37, 0x34, 0x34,
            0x30, 0x30, 0x30, 0x5A,
        ].repeat(NUM_VALUES);

        // Ion v1.1 Version Marker
        let mut binary_1_1_data = vec![0xE0u8, 0x01, 0x01, 0xEA];
        binary_1_1_data.append(&mut binary_1_1_data_body);

        let mut reader = Reader::new(v1_1::Binary, binary_1_1_data.as_slice()).unwrap();
        reader
            .register_template_src(template_definition_text)
            .unwrap();
        let mut num_values = 0usize;
        while let Some(value) = reader.next().unwrap() {
            let s = value.read().unwrap().expect_struct().unwrap();
            let format_field_value = s.find_expected("format").unwrap();
            hint::black_box(format_field_value.read()?);
            num_values += 1;
        }
        let _ = black_box(num_values);
        Ok(())
    }
}
