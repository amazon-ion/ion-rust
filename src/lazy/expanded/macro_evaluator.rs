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
use std::marker::PhantomData;

use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr};
use crate::lazy::expanded::macro_table::MacroKind;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{
    TemplateBodyValueExpr, TemplateBodyVariableReference, TemplateElement, TemplateMacroInvocation,
    TemplateMacroInvocationArgsIterator, TemplateMacroRef, TemplateValue,
};
use crate::lazy::expanded::EncodingContext;
use crate::lazy::expanded::{ExpandedValueRef, ExpandedValueSource, LazyExpandedValue};
use crate::lazy::str_ref::StrRef;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::result::IonFailure;
use crate::{IonError, IonResult, RawSymbolTokenRef};
use bumpalo::collections::{String as BumpString, Vec as BumpVec};

/// A syntactic entity that represents the invocation of a macro in some context.
///
/// This entity may be an item from a binary stream, a text stream, or a template definition.
/// Implementors must specify how their type can be mapped to a macro ID and a sequence of arguments.
pub trait RawMacroInvocation<'data, D: LazyDecoder<'data>>: Debug + Copy + Clone {
    /// An iterator that yields the macro invocation's arguments in order.
    type RawArgumentsIterator<'a>: Iterator<Item = IonResult<LazyRawValueExpr<'data, D>>>
    where
        Self: 'a;

    type MacroInvocation<'top>: MacroInvocation<'top, 'data, D>
    where
        'data: 'top;

    /// The macro name or address specified at the head of this macro invocation.
    fn id(&self) -> MacroIdRef<'data>;

    /// The arguments that follow the macro name or address in this macro invocation.
    fn raw_arguments(&self) -> Self::RawArgumentsIterator<'data>;

    fn resolve<'top>(
        self,
        context: EncodingContext<'top>,
    ) -> IonResult<Self::MacroInvocation<'top>>
    where
        'data: 'top;
}

pub trait MacroInvocation<'top, 'data: 'top, D: LazyDecoder<'data>>:
    Debug + Copy + Clone + Into<MacroExpr<'top, 'data, D>>
{
    type ArgumentsIterator: Iterator<Item = IonResult<ArgumentExpr<'top, 'data, D>>>;

    fn id(&self) -> MacroIdRef<'top>;
    fn arguments(&self, environment: Environment<'top, 'data, D>) -> Self::ArgumentsIterator;
}

#[derive(Copy, Clone, Debug)]
pub enum MacroExpr<'top, 'data: 'top, D: LazyDecoder<'data>> {
    TemplateMacro(TemplateMacroInvocation<'top>),
    EExp(D::MacroInvocation<'top>),
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroExpr<'top, 'data, D> {
    fn id(&self) -> MacroIdRef {
        match &self {
            MacroExpr::TemplateMacro(m) => {
                <TemplateMacroInvocation<'top> as MacroInvocation<'top, 'data, D>>::id(m)
            }
            MacroExpr::EExp(e) => e.id(),
        }
    }

    fn arguments(
        &self,
        environment: Environment<'top, 'data, D>,
    ) -> MacroExprArgsIterator<'top, 'data, D> {
        let args_kind = match &self {
            MacroExpr::TemplateMacro(m) => {
                MacroExprArgsKind::<'top, 'data, D>::Macro(m.arguments(environment))
            }
            MacroExpr::EExp(e) => {
                MacroExprArgsKind::<'top, 'data, D>::EExp(e.arguments(Environment::empty()))
            }
        };
        MacroExprArgsIterator { source: args_kind }
    }
}

pub enum MacroExprArgsKind<'top, 'data: 'top, D: LazyDecoder<'data>> {
    Macro(TemplateMacroInvocationArgsIterator<'top, 'data, D>),
    EExp(<D::MacroInvocation<'top> as MacroInvocation<'top, 'data, D>>::ArgumentsIterator),
}

pub struct MacroExprArgsIterator<'top, 'data: 'top, D: LazyDecoder<'data>> {
    source: MacroExprArgsKind<'top, 'data, D>,
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> Iterator for MacroExprArgsIterator<'top, 'data, D> {
    type Item = IonResult<ArgumentExpr<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        match &mut self.source {
            MacroExprArgsKind::Macro(m) => m.next(),
            MacroExprArgsKind::EExp(e) => e.next(),
        }
    }
}

/// A single expression appearing in argument position within a macro invocation.
#[derive(Debug, Clone)]
pub enum ArgumentExpr<'top, 'data: 'top, D: LazyDecoder<'data>> {
    /// An Ion value that requires no further evaluation.
    // `LazyExpandedValue` can be backed by either a stream value or a template value, so it covers
    // both contexts.
    ValueLiteral(LazyExpandedValue<'top, 'data, D>),
    /// A variable name that requires expansion.
    Variable(TemplateBodyVariableReference),
    /// A template macro invocation that requires evaluation.
    MacroInvocation(MacroExpr<'top, 'data, D>),
}

/// Indicates which of the supported macros this represents and stores the state necessary to
/// continue evaluating that macro.
pub enum MacroExpansionKind<'top, 'data, D: LazyDecoder<'data>> {
    Void,
    Values(ValuesExpansion<'top, 'data, D>),
    MakeString(MakeStringExpansion<'top, 'data, D>),
    Template(TemplateExpansion<'top>),
}

#[derive(Clone, Debug)]
pub struct TemplateExpansion<'top> {
    template: TemplateMacroRef<'top>,
    step_index: usize,
}

impl<'top> TemplateExpansion<'top> {
    pub fn new(template: TemplateMacroRef<'top>) -> Self {
        Self {
            template,
            step_index: 0,
        }
    }

    fn next<'data: 'top, D: LazyDecoder<'data>>(
        &mut self,
        context: EncodingContext<'top>,
        environment: Environment<'top, 'data, D>,
    ) -> IonResult<MacroExpansionStep<'top, 'data, D>> {
        let value_expr = match self.template.body().expressions().get(self.step_index) {
            None => return Ok(MacroExpansionStep::Complete),
            Some(expr) => expr,
        };
        self.step_index += 1;

        let step = match value_expr {
            TemplateBodyValueExpr::Element(e) => {
                match e.value() {
                    TemplateValue::List(range)
                    | TemplateValue::SExp(range)
                    | TemplateValue::Struct(range) => self.step_index += range.len(),
                    _ => {}
                }
                MacroExpansionStep::Value(LazyExpandedValue::from_template(
                    context,
                    environment,
                    TemplateElement::new(self.template, e),
                ))
            }
            TemplateBodyValueExpr::Variable(variable) => MacroExpansionStep::Variable(*variable),
            TemplateBodyValueExpr::MacroInvocation(raw_invocation) => {
                let invocation = raw_invocation.resolve(self.template, context)?;
                self.step_index += invocation.arg_expressions().len();
                MacroExpansionStep::Macro(invocation.into())
            }
        };

        Ok(step)
    }
}

/// A macro in the process of being evaluated. Stores both the state of the evaluation and the
/// syntactic element that represented the macro invocation.
pub struct MacroExpansion<'top, 'data, D: LazyDecoder<'data>> {
    kind: MacroExpansionKind<'top, 'data, D>,
    // Not every macro expansion is initiated by an expression in the input; the evaluator itself
    // can add expansions to the stack as an implementation detail (e.g. for variable expansion).
    // In such cases, the `kind` stores any information needed to perform the expansion.
    invocation: Option<MacroExpr<'top, 'data, D>>,
}

impl<'top, 'data, D: LazyDecoder<'data>> MacroExpansion<'top, 'data, D> {
    pub(crate) fn new(
        kind: MacroExpansionKind<'top, 'data, D>,
        invocation: Option<MacroExpr<'top, 'data, D>>,
    ) -> Self {
        Self { kind, invocation }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> Debug for MacroExpansion<'top, 'data, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let name = match &self.kind {
            MacroExpansionKind::Void => "void",
            MacroExpansionKind::Values(_) => "values",
            MacroExpansionKind::MakeString(_) => "make_string",
            MacroExpansionKind::Template(t) => {
                return write!(f, "<expansion of template '{}'>", t.template.name())
            }
        };
        write!(f, "<expansion of macro '{name}'>")
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroExpansion<'top, 'data, D> {
    /// Continues evaluating this macro until it:
    ///   * produces another value.
    ///   * encounters another macro or variable that needs to be expanded.
    ///   * is completed.
    fn next(
        &mut self,
        context: EncodingContext<'top>,
        environment: Environment<'top, 'data, D>,
    ) -> IonResult<MacroExpansionStep<'top, 'data, D>> {
        use MacroExpansionKind::*;
        // Delegate the call to `next()` based on the macro kind.
        match &mut self.kind {
            MakeString(make_string_expansion) => make_string_expansion.next(context, environment),
            Values(values_expansion) => values_expansion.next(context, environment),
            // `void` is trivial and requires no delegation
            Void => Ok(MacroExpansionStep::Complete),
            Template(template_expansion) => template_expansion.next(context, environment),
        }
    }
}

/// Represents a single step in the process of evaluating a macro.
pub enum MacroExpansionStep<'top, 'data, D: LazyDecoder<'data>> {
    /// The next value produced by continuing the macro evaluation.
    Value(LazyExpandedValue<'top, 'data, D>),
    /// Another macro that will need to be evaluated before an expanded value can be returned.
    Macro(MacroExpr<'top, 'data, D>),
    /// A variable that needs to be resolved
    Variable(TemplateBodyVariableReference),
    /// This macro will not produce any further values.
    Complete,
}

impl<'top, 'data, D: LazyDecoder<'data>> MacroExpansionStep<'top, 'data, D> {
    pub(crate) fn substitute_variables(
        self,
        environment: Environment<'top, 'data, D>,
    ) -> IonResult<MacroExpansionStep<'top, 'data, D>> {
        if let MacroExpansionStep::Variable(variable) = self {
            let arg_expr = environment.get_expected(variable.signature_index())?;
            match arg_expr {
                ArgumentExpr::ValueLiteral(expansion) => {
                    println!("expand variable to {expansion:?}");
                    Ok(MacroExpansionStep::Value(*expansion))
                }
                ArgumentExpr::Variable(_) => {
                    unreachable!(
                        "environment contained a variable reference instead of an expression"
                    )
                }
                ArgumentExpr::MacroInvocation(invocation) => {
                    println!("expand variable to {:?}", invocation);
                    Ok(MacroExpansionStep::Macro(*invocation))
                }
            }
        } else {
            Ok(self)
        }
    }
}

pub type MacroStack<'top, 'data, D> = BumpVec<'top, MacroExpansion<'top, 'data, D>>;
pub type EnvironmentStack<'top, 'data, D> = BumpVec<'top, Environment<'top, 'data, D>>;

/// Evaluates macro invocations recursively, yielding a single expanded value at a time.
///
/// This trait describes evaluation in a variety of contexts. It supports the cross product of three
/// use case dimensions:
///
///   {e-expression, template macro invocation}
///   x {text, binary}
///   x {eager, lazy}
pub struct MacroEvaluator<'top, 'data: 'top, D: LazyDecoder<'data>> {
    // TODO: Describe how macro stack and environment stack do not grow at the same rate
    macro_stack: MacroStack<'top, 'data, D>,
    context: EncodingContext<'top>,
    env_stack: EnvironmentStack<'top, 'data, D>,
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroEvaluator<'top, 'data, D> {
    pub fn new(context: EncodingContext<'top>, environment: Environment<'top, 'data, D>) -> Self {
        let macro_stack = BumpVec::new_in(context.allocator);
        let mut env_stack = BumpVec::new_in(context.allocator);
        env_stack.push(environment);
        Self {
            macro_stack,
            env_stack,
            context,
        }
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroEvaluator<'top, 'data, D> {
    pub fn macro_stack_depth(&self) -> usize {
        self.macro_stack.len()
    }

    pub fn environment(&self) -> Environment<'top, 'data, D> {
        // The stack is never completely empty.
        *self.env_stack.last().unwrap()
    }

    fn make_eval_env(
        &mut self,
        context: EncodingContext<'top>,
        invocation: MacroExpr<'top, 'data, D>,
    ) -> IonResult<Environment<'top, 'data, D>> {
        // Using the current environment, make a new environment for the next invocation.
        // TODO: Explain better
        let mut args = BumpVec::new_in(context.allocator);
        for arg in invocation.arguments(self.environment()) {
            args.push(arg?);
        }
        let environment = Environment::new(args);
        Ok(environment)
    }

    /// Finds the macro corresponding to the invocation's ID in the specified encoding context.
    /// Returns an error if the macro cannot be found. Otherwise, returns a [`MacroExpansion`]
    /// containing the original invocation and the initialized state needed to evaluate it.
    fn resolve_invocation(
        &mut self,
        context: EncodingContext<'top>,
        invocation_to_evaluate: MacroExpr<'top, 'data, D>,
    ) -> IonResult<MacroExpansion<'top, 'data, D>> {
        // Get the `MacroKind` corresponding to the given ID.
        let macro_kind = match self
            .context
            .macro_table
            .macro_with_id(invocation_to_evaluate.id())
        {
            Some(kind) => kind,
            None => {
                return IonResult::decoding_error(format!(
                    "found unrecognized macro id {:?}",
                    invocation_to_evaluate.id()
                ))
            }
        };
        // Initialize a `MacroExpansionKind` with the state necessary to evaluate the requested
        // macro.
        let expansion_kind = match macro_kind.kind() {
            MacroKind::Void => MacroExpansionKind::Void,
            MacroKind::Values => MacroExpansionKind::Values(ValuesExpansion {
                arguments: invocation_to_evaluate.arguments(self.environment()),
                initial_eval_stack_depth: self.macro_stack_depth(),
            }),
            MacroKind::MakeString => MacroExpansionKind::MakeString(MakeStringExpansion::new(
                invocation_to_evaluate.arguments(self.environment()),
            )),
            MacroKind::Template(template) => {
                let template_address = macro_kind.address();
                let template_ref = TemplateMacroRef::new(template_address, template);
                let new_environment = self.make_eval_env(context, invocation_to_evaluate)?;
                println!("push {new_environment:?}");
                self.env_stack.push(new_environment);
                MacroExpansionKind::Template(TemplateExpansion::new(template_ref))
            }
        };
        Ok(MacroExpansion {
            kind: expansion_kind,
            invocation: Some(invocation_to_evaluate),
        })
    }

    /// Given a syntactic element representing a macro invocation, attempt to resolve it with the
    /// current encoding context and push the resulting `MacroExpansion` onto the stack.
    pub fn push(
        &mut self,
        context: EncodingContext<'top>,
        invocation: impl Into<MacroExpr<'top, 'data, D>>,
    ) -> IonResult<()> {
        let macro_expr = invocation.into();
        println!("push {macro_expr:?}");
        let expansion = self.resolve_invocation(context, macro_expr)?;
        self.macro_stack.push(expansion);
        Ok(())
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
    /// before calling `next()`.
    pub fn next(
        &mut self,
        context: EncodingContext<'top>,
        depth_to_exhaust: usize,
    ) -> IonResult<Option<LazyExpandedValue<'top, 'data, D>>> {
        debug_assert!(
            self.macro_stack_depth() >= depth_to_exhaust,
            "asked to exhaust a macro at an invalid depth"
        );

        loop {
            let environment = self.environment();
            // Get the expansion at the top of the stack.
            let current_expansion = match self.macro_stack.last_mut() {
                // NOTE: If the user specifies a `depth_to_exhaust` of 0, this is where the loop
                //       will end. Behaviorally, this is identical to a `depth_to_exhaust` of 1,
                //       which would return `Ok(None)` at the bottom of this method. It is always
                //       legal to call `next()` with a `depth_to_exhaust` of 0; however, it is
                //       illegal to call it with a `depth_to_exhaust` of 1 when the stack is empty.
                None => return Ok(None),
                Some(expansion) => expansion,
            };

            // Ask that expansion to continue its evaluation by one step.
            use MacroExpansionStep::*;
            match current_expansion
                .next(context, environment)?
                .substitute_variables(environment)?
            {
                // If we get a value, return it to the caller.
                Value(value) => {
                    println!("yield {value:?}");
                    return Ok(Some(value));
                }
                // If we get another macro, push it onto the stack and continue evaluation.
                Macro(invocation) => {
                    // If we encounter another macro invocation, put it on top of the stack.
                    self.push(context, invocation)?;
                    continue;
                }
                // If we find a variable name, it could expand to any number of values.
                Variable(_) => {
                    unreachable!("variables already substituted")
                }
                // If the current macro reports that its expansion is complete...
                Complete => {
                    // ...pop it off the stack...
                    let completed = self.macro_stack.pop().unwrap();
                    println!(
                        "pop {completed:?}, macro stack depth={}, top={:?}",
                        self.macro_stack_depth(),
                        self.macro_stack.last(),
                    );
                    if matches!(completed.kind, MacroExpansionKind::Template(_)) {
                        let popped_env = self.env_stack.pop().unwrap();
                        println!("pop {popped_env:?}");
                    }
                    // ...and see that was the macro the caller was interested in evaluating.
                    if self.macro_stack.len() < depth_to_exhaust {
                        // If so, there are no more values to yield, even though there may still
                        // be macros on the stack.
                        return Ok(None);
                    }
                    // Otherwise, the caller is interested in one of the previously invoked macros.
                    continue;
                }
            }
        }
    }

    /// Attempts to resolve the provided `invocation` in the specified `context`. Upon success,
    /// returns an iterator that lazily computes the expansion of the macro invocation and yields
    /// its values.
    pub fn evaluate<'iter>(
        &'iter mut self,
        context: EncodingContext<'top>,
        invocation: impl Into<MacroExpr<'top, 'data, D>>,
    ) -> IonResult<EvaluatingIterator<'iter, 'top, 'data, D>>
    where
        'data: 'top,
        Self: Sized,
    {
        self.push(context, invocation.into())?;
        Ok(EvaluatingIterator::new(self, context))
    }
}

/// Yields the values produced by incrementally evaluating the macro that was at the top of the
/// evaluator's stack when the iterator was created.
pub struct EvaluatingIterator<'iter, 'top, 'data: 'top, D: LazyDecoder<'data>> {
    evaluator: &'iter mut MacroEvaluator<'top, 'data, D>,
    context: EncodingContext<'top>,
    initial_stack_depth: usize,
    spooky: PhantomData<&'data D>,
}

impl<'iter, 'top, 'data, D: LazyDecoder<'data>> EvaluatingIterator<'iter, 'top, 'data, D> {
    pub fn new(
        evaluator: &'iter mut MacroEvaluator<'top, 'data, D>,
        context: EncodingContext<'top>,
    ) -> Self {
        let initial_stack_depth = evaluator.macro_stack_depth();
        Self {
            evaluator,
            context,
            initial_stack_depth,
            spooky: PhantomData,
        }
    }
}

impl<'iter, 'top, 'data: 'top, D: LazyDecoder<'data>> Iterator
    for EvaluatingIterator<'iter, 'top, 'data, D>
{
    type Item = IonResult<LazyExpandedValue<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.evaluator
            .next(self.context, self.initial_stack_depth)
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
pub struct ValuesExpansion<'top, 'data, D: LazyDecoder<'data>> {
    // Which argument the macro is in the process of expanding
    arguments: MacroExprArgsIterator<'top, 'data, D>,
    // The stack depth where this `values` call lives. When the stack shrinks below this depth,
    // evaluation is complete.
    initial_eval_stack_depth: usize,
}

impl<'top, 'data, D: LazyDecoder<'data>> ValuesExpansion<'top, 'data, D> {
    pub fn new(
        arguments: MacroExprArgsIterator<'top, 'data, D>,
        initial_eval_stack_depth: usize,
    ) -> Self {
        Self {
            arguments,
            initial_eval_stack_depth,
        }
    }

    /// Yields the next [`MacroExpansionStep`] in this macro's evaluation.
    pub fn next(
        &mut self,
        _context: EncodingContext<'top>,
        _environment: Environment<'top, 'data, D>,
    ) -> IonResult<MacroExpansionStep<'top, 'data, D>> {
        // We visit the argument expressions in the invocation in order from left to right.
        let arg_expr = match self.arguments.next() {
            Some(Err(e)) => return Err(e),
            Some(Ok(arg)) => arg,
            None => return Ok(MacroExpansionStep::Complete),
        };

        match arg_expr {
            // If the argument is a value, return it.
            ArgumentExpr::ValueLiteral(value) => Ok(MacroExpansionStep::Value(value)),
            ArgumentExpr::Variable(variable) => Ok(MacroExpansionStep::Variable(variable)),
            // If the argument is a macro invocation, yield it that so the evaluator can push it onto the stack.
            ArgumentExpr::MacroInvocation(invocation) => Ok(MacroExpansionStep::Macro(invocation)),
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
pub struct MakeStringExpansion<'top, 'data, D: LazyDecoder<'data>> {
    arguments: MacroExprArgsIterator<'top, 'data, D>,
    is_complete: bool,
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MakeStringExpansion<'top, 'data, D> {
    pub fn new(arguments: MacroExprArgsIterator<'top, 'data, D>) -> Self {
        Self {
            arguments,
            is_complete: false,
        }
    }

    /// Yields the next [`MacroExpansionStep`] in this `make_string` macro's evaluation.
    pub fn next(
        &mut self,
        context: EncodingContext<'top>,
        environment: Environment<'top, 'data, D>,
    ) -> IonResult<MacroExpansionStep<'top, 'data, D>> {
        // `make_string` always produces a single value. Once that value has been returned, it needs
        // to report `Complete` on the following call to `next()`.
        if self.is_complete {
            return Ok(MacroExpansionStep::Complete);
        }

        // Create a bump-allocated buffer to hold our constructed string
        let mut buffer = BumpString::new_in(context.allocator);

        // We need to eagerly evaluate all of the arguments to `make_string` to produce its next
        // (and only) value. However, because `&mut self` (the expansion state) lives in a stack
        // inside the evaluator, we cannot get a simultaneous mutable reference to the evaluator
        // itself. Instead, we use the bump allocator the make a transient macro evaluator
        // whose resources can be trivially reclaimed when the expansion is done.
        let mut evaluator = MacroEvaluator::new(context, environment);

        for arg_result in &mut self.arguments {
            let arg_expr = arg_result?;
            match arg_expr {
                ArgumentExpr::ValueLiteral(value) => {
                    Self::append_expanded_raw_text_value(context, &mut buffer, value.read()?)?
                }
                ArgumentExpr::Variable(_variable) => todo!("variable expansion"),
                ArgumentExpr::MacroInvocation(invocation) => {
                    for value_result in evaluator.evaluate(context, invocation)? {
                        let value = value_result?;
                        let expanded = value.read()?;
                        Self::append_expanded_raw_text_value(context, &mut buffer, expanded)?
                    }
                }
            }
        }

        // Convert our BumpString<'bump> into a &'bump str that we can wrap in an `ExpandedValueRef`
        let constructed_text = buffer.into_bump_str();
        let expanded_value_ref: &'top ExpandedValueRef<'top, 'data, D> = context
            .allocator
            .alloc_with(|| ExpandedValueRef::String(StrRef::from(constructed_text)));
        static EMPTY_ANNOTATIONS: &[&str] = &[];

        self.is_complete = true;
        Ok(MacroExpansionStep::Value(LazyExpandedValue {
            context,
            source: ExpandedValueSource::Constructed(EMPTY_ANNOTATIONS, expanded_value_ref),
        }))
    }

    /// Appends a string fragment to the `BumpString` being constructed.
    fn append_expanded_raw_text_value(
        context: EncodingContext<'_>,
        buffer: &mut BumpString,
        value: ExpandedValueRef<'_, 'data, D>,
    ) -> IonResult<()> {
        match value {
            ExpandedValueRef::String(text) => buffer.push_str(text.as_ref()),
            ExpandedValueRef::Symbol(RawSymbolTokenRef::Text(text)) => {
                buffer.push_str(text.as_ref())
            }
            ExpandedValueRef::Symbol(RawSymbolTokenRef::SymbolId(sid)) => {
                let symbol = context.symbol_table.symbol_for(sid).ok_or_else(|| {
                    IonError::decoding_error(format!(
                        "found unknown symbol ID {sid} in call to `make_string`"
                    ))
                })?;
                if let Some(text) = symbol.text() {
                    buffer.push_str(text);
                } else {
                    return IonResult::decoding_error(format!(
                        "found a symbol ID {sid} with unknown text in call to `make_string`"
                    ));
                }
            }
            other => {
                return IonResult::decoding_error(format!(
                    "found a non-text parameter to `make_string`: {:?}",
                    other
                ))
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::expanded::compiler::TemplateCompiler;
    use crate::lazy::reader::LazyTextReader_1_1;
    use crate::{Element, ElementReader, IonResult};

    /// Reads `input` and `expected` using an expanding reader and asserts that their output
    /// is the same.
    fn eval_enc_expr<'data>(input: &'data str, expected: &'data str) -> IonResult<()> {
        let mut actual_reader = LazyTextReader_1_1::new(input.as_bytes())?;
        let actual = actual_reader.read_all_elements()?;

        let mut expected_reader = LazyTextReader_1_1::new(expected.as_bytes())?;
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
    fn eval_template_invocation(template: &str, invocation: &str, expected: &str) -> IonResult<()> {
        let mut reader = LazyTextReader_1_1::new(invocation.as_bytes())?;
        let template_macro = dbg!(TemplateCompiler::compile_from_text(
            reader.context(),
            template
        )?);
        let _macro_address = reader.register_template(template_macro)?;
        let actuals = reader.read_all_elements()?;
        let mut expected_reader = LazyTextReader_1_1::new(expected.as_bytes())?;
        for actual in actuals {
            // Read the next expected value as a raw value, then wrap it in an `ExpandedRawValueRef`
            // so it can be directly compared to the actual.
            println!("actual: {}", actual);
            let expected: Element = expected_reader.next()?.unwrap().read()?.try_into()?;
            assert_eq!(actual, expected);
        }
        assert!(matches!(expected_reader.next(), Ok(None)));

        Ok(())
    }

    #[test]
    fn application_log_event() -> IonResult<()> {
        eval_template_invocation(
            // Template definition
            r#"
                (macro event (timestamp thread_id thread_name parameters) 
                    {
                        'timestamp': timestamp,
                        'threadId': thread_id,
                        'threadName': thread_name,
                        'loggerName': "com.amazon.sable.request.interceptor.RequestLoggerTask",
                        'logLevel': (quote INFO),
                        'format': "Request:: {} Client ID: {} Client Host: {} Client Scope: {} Timestamp: {}",
                        'parameters': ["SUCCESS", "sable-back-acceptance", parameters]
                    }
                )
            "#,
            // A symbol table we can refer to in our invocation
            r#"
                $ion_symbol_table::{
                    symbols: [
                        "UniversalRouterBackgroundScheduler-", // $10
                        "yfw-sable-back-acceptance-",          // $11
                        ".us-east-1.amazon.com"                // $12
                    ]
                }
                
                (:event                 // <---- The template invocation
                    1670446800245
                    418
                    (:make_string $10 "0")
                    (:values 
                        (:make_string $11 "1d-627f7f84" $12)
                        "scope0"
                        "2022-12-07T20:59:59.744000Z"))
            "#,
            // The equivalent output
            r#"
                    {
                        'timestamp': 1670446800245,
                        'threadId': 418,
                        'threadName': "UniversalRouterBackgroundScheduler-0",
                        'loggerName': "com.amazon.sable.request.interceptor.RequestLoggerTask",
                        'logLevel': INFO,
                        'format': "Request:: {} Client ID: {} Client Host: {} Client Scope: {} Timestamp: {}",
                        'parameters': [
                            "SUCCESS",
                            "sable-back-acceptance",
                            "yfw-sable-back-acceptance-1d-627f7f84.us-east-1.amazon.com",
                            "scope0",
                            "2022-12-07T20:59:59.744000Z",
                        ]
                    }
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
    // This requires an implementation of TDL's `(make_sexp)` or `(quote)`. Without these,
    // a sexp is always considered a TDL macro invocation.

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
