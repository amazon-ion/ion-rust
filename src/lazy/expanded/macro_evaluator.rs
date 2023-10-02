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

use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;

use bumpalo::collections::{String as BumpString, Vec as BumpVec};

use crate::lazy::decoder::LazyDecoder;
use crate::lazy::expanded::macro_table::MacroKind;
use crate::lazy::expanded::stack::Stack;
use crate::lazy::expanded::EncodingContext;
use crate::lazy::expanded::{ExpandedValueRef, ExpandedValueSource, LazyExpandedValue};
use crate::lazy::str_ref::StrRef;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::result::IonFailure;
use crate::{IonError, IonResult, RawSymbolTokenRef, Sequence};

/// A syntactic entity that represents the invocation of a macro in some context.
///
/// This entity may be an item from a binary stream, a text stream, or a template definition.
/// Implementors must specify how their type can be mapped to a macro ID and a sequence of arguments.
pub trait MacroInvocation<'data, D: LazyDecoder<'data>>: Copy + Clone + Debug {
    /// A syntax-specific type that represents an argument in this macro invocation.
    type ArgumentExpr: ToArgumentKind<'data, D, Self>;

    /// An iterator that yields the macro invocation's arguments in order.
    type ArgumentsIterator: Iterator<Item = IonResult<Self::ArgumentExpr>>;

    type TransientEvaluator<'top>: MacroEvaluator<
        'top,
        'data,
        D,
        MacroInvocation = Self,
        Stack = BumpVec<'top, MacroExpansion<'data, D, Self>>,
    >
    where
        'data: 'top,
        Self: 'top;

    /// The macro name or address specified at the head of this macro invocation.
    fn id(&self) -> MacroIdRef;

    /// The arguments that follow the macro name or address in this macro invocation.
    fn arguments(&self) -> Self::ArgumentsIterator;

    fn make_transient_evaluator<'top>(
        context: EncodingContext<'top>,
    ) -> Self::TransientEvaluator<'top>
    where
        'data: 'top,
        Self: 'top;
}

/// A single expression appearing in argument position within a macro invocation.
pub enum ArgumentKind<'top, 'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> {
    /// An Ion value that requires no further evaluation.
    ValueLiteral(LazyExpandedValue<'top, 'data, D>),
    /// A variable name that requires expansion.
    Variable(RawSymbolTokenRef<'top>),
    /// A macro invocation that requires evaluation.
    MacroInvocation(M),
}

/// Converts a syntactic element appearing in argument position into an [`ArgumentKind`] using the
/// provided [`EncodingContext`].
pub trait ToArgumentKind<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> {
    fn to_arg_expr<'top>(self, context: EncodingContext<'top>) -> ArgumentKind<'top, 'data, D, M>
    where
        Self: 'top;
}

/// Indicates which of the supported macros this represents and stores the state necessary to
/// continue evaluating that macro.
pub enum MacroExpansionKind<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> {
    Void,
    Values(ValuesExpansion<'data, D, M>),
    MakeString(MakeStringExpansion<'data, D, M>),
    Template(String),
    // TODO: The others, including template macros.
    // TODO: Treat variables as a special kind of macro invocation, similar to `values` but without
    //       an accessible entry in the macro table.
}

/// A macro in the process of being evaluated. Stores both the state of the evaluation and the
/// syntactic element that represented the macro invocation.
pub struct MacroExpansion<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> {
    kind: MacroExpansionKind<'data, D, M>,
    invocation: M,
}

impl<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> Debug
    for MacroExpansion<'data, D, M>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "<expansion of {:?}>", self.invocation)
    }
}

impl<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> MacroExpansion<'data, D, M> {
    /// Continues evaluating this macro until it:
    ///   * produces another value.
    ///   * encounters another macro or variable that needs to be expanded.
    ///   * is completed.
    fn next<'top>(
        &mut self,
        context: EncodingContext<'top>,
    ) -> IonResult<MacroExpansionStep<'top, 'data, D, M>>
    where
        'data: 'top,
        M: 'top,
    {
        use MacroExpansionKind::*;
        // Delegate the call to `next()` based on the macro kind.
        match &mut self.kind {
            MakeString(make_string_expansion) => make_string_expansion.next(context),
            Values(values_expansion) => values_expansion.next(context),
            // `void` is trivial and requires no delegation
            Void => Ok(MacroExpansionStep::Complete),
            Template(_template) => todo!("support {_template}"),
        }
    }
}

/// Represents a single step in the process of evaluating a macro.
pub enum MacroExpansionStep<'top, 'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> {
    /// The next value produced by continuing the macro evaluation.
    ExpandedValue(LazyExpandedValue<'top, 'data, D>),
    /// Another macro that will need to be evaluated before an expanded value can be returned.
    AnotherMacroToEvaluate(M),
    /// This macro will not produce any further values.
    Complete,
}

/// Evaluates macro invocations recursively, yielding a single expanded value at a time.
///
/// This trait describes evaluation in a variety of contexts. It supports the cross product of three
/// use case dimensions:
///
///   {e-expression, template macro invocation}
///   x {text, binary}
///   x {eager, lazy}
pub trait MacroEvaluator<'stack, 'data: 'stack, D: LazyDecoder<'data>> {
    type Stack: Stack<MacroExpansion<'data, D, Self::MacroInvocation>> + 'stack;
    type MacroInvocation: MacroInvocation<'data, D>;

    fn stack(&self) -> &Self::Stack;
    fn stack_mut(&mut self) -> &mut Self::Stack;
    fn stack_depth(&self) -> usize {
        self.stack().len()
    }

    /// Finds the macro corresponding to the invocation's ID in the specified encoding context.
    /// Returns an error if the macro cannot be found. Otherwise, returns a [`MacroExpansion`]
    /// containing the original invocation and the initialized state needed to evaluate it.
    fn resolve_invocation<'top>(
        &mut self,
        context: EncodingContext<'top>,
        invocation_to_evaluate: Self::MacroInvocation,
    ) -> IonResult<MacroExpansion<'data, D, Self::MacroInvocation>> {
        // Get the `MacroKind` corresponding to the given ID. It contains either a name (`&str`) or
        // an address (`usize`).
        let macro_kind = match invocation_to_evaluate.id() {
            MacroIdRef::LocalName(name) => {
                context.macro_table.macro_with_name(name).ok_or_else(|| {
                    IonError::decoding_error(format!(
                        "unrecognized macro name '{name}' in {:?}",
                        invocation_to_evaluate
                    ))
                })
            }
            MacroIdRef::LocalAddress(address) => context
                .macro_table
                .macro_at_address(address)
                .ok_or_else(|| {
                    IonError::decoding_error(format!(
                        "invalid macro address '{address}' in {:?}",
                        invocation_to_evaluate
                    ))
                }),
        }?;
        // Initialize a `MacroExpansionKind` with the state necessary to evaluate the requested
        // macro.
        let expansion_kind = match macro_kind {
            MacroKind::Void => MacroExpansionKind::Void,
            MacroKind::Values => MacroExpansionKind::Values(ValuesExpansion {
                arguments: invocation_to_evaluate.arguments(),
                initial_eval_stack_depth: self.stack_depth(),
            }),
            MacroKind::MakeString => MacroExpansionKind::MakeString(MakeStringExpansion::new(
                invocation_to_evaluate.arguments(),
            )),
            MacroKind::Template(_template) => todo!("template expansion init"),
        };
        Ok(MacroExpansion {
            kind: expansion_kind,
            invocation: invocation_to_evaluate,
        })
    }

    /// Given a syntactic element representing a macro invocation, attempt to resolve it with the
    /// current encoding context and push the resulting `MacroExpansion` onto the stack.
    fn push<'top>(
        &mut self,
        context: EncodingContext<'top>,
        invocation: Self::MacroInvocation,
    ) -> IonResult<()> {
        let expansion = self.resolve_invocation(context, invocation)?;
        self.stack_mut().push(expansion);
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
    fn next<'top>(
        &mut self,
        context: EncodingContext<'top>,
        depth_to_exhaust: usize,
    ) -> IonResult<Option<LazyExpandedValue<'top, 'data, D>>>
    where
        'data: 'top,
        Self::MacroInvocation: 'top,
    {
        debug_assert!(
            self.stack_depth() >= depth_to_exhaust,
            "asked to exhaust a macro at an invalid depth"
        );
        loop {
            // Get the expansion at the top of the stack.
            let current_expansion = match self.stack_mut().peek_mut() {
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
            match current_expansion.next(context)? {
                // If we get a value, return it to the caller.
                ExpandedValue(value) => return Ok(Some(value)),
                // If we get another macro, push it onto the stack and continue evaluation.
                AnotherMacroToEvaluate(invocation) => {
                    // If we encounter another macro invocation, put it on top of the stack.
                    self.push(context, invocation)?;
                    continue;
                }
                // If the current macro reports that its expansion is complete...
                Complete => {
                    // ...pop it off the stack...
                    let _popped = self.stack_mut().pop().unwrap();
                    // ...and see that was the macro the caller was interested in evaluating.
                    if self.stack().len() < depth_to_exhaust {
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
    fn evaluate<'iter>(
        &'iter mut self,
        context: EncodingContext<'stack>,
        invocation: Self::MacroInvocation,
    ) -> IonResult<EvaluatingIterator<'iter, 'stack, 'data, D, Self>>
    where
        Self: Sized,
    {
        self.push(context, invocation)?;
        Ok(EvaluatingIterator::new(self, context))
    }
}

/// Yields the values produced by incrementally evaluating the macro that was at the top of the
/// evaluator's stack when the iterator was created.
pub struct EvaluatingIterator<
    'iter,
    'top,
    'data: 'top,
    D: LazyDecoder<'data>,
    E: MacroEvaluator<'top, 'data, D>,
> {
    evaluator: &'iter mut E,
    context: EncodingContext<'top>,
    initial_stack_depth: usize,
    spooky: PhantomData<&'data D>,
}

impl<'iter, 'top, 'data, D: LazyDecoder<'data>, E: MacroEvaluator<'top, 'data, D>>
    EvaluatingIterator<'iter, 'top, 'data, D, E>
{
    pub fn new(evaluator: &'iter mut E, context: EncodingContext<'top>) -> Self {
        let initial_stack_depth = evaluator.stack_depth();
        Self {
            evaluator,
            context,
            initial_stack_depth,
            spooky: PhantomData,
        }
    }
}

impl<'iter, 'top, 'data: 'top, D: LazyDecoder<'data>, E: MacroEvaluator<'top, 'data, D> + 'top>
    Iterator for EvaluatingIterator<'iter, 'top, 'data, D, E>
{
    type Item = IonResult<LazyExpandedValue<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.evaluator
            .next(self.context, self.initial_stack_depth)
            .transpose()
    }
}

/// A [`MacroEvaluator`] for expanding e-expressions found in a data stream of the format `D`.
pub struct EExpEvaluator<'data, D: LazyDecoder<'data>> {
    macro_stack: Vec<MacroExpansion<'data, D, D::MacroInvocation>>,
}

impl<'data, D: LazyDecoder<'data>> EExpEvaluator<'data, D> {
    pub fn new() -> Self {
        Self {
            macro_stack: Vec::new(),
        }
    }
}

impl<'data, D: LazyDecoder<'data>> MacroEvaluator<'data, 'data, D> for EExpEvaluator<'data, D> {
    type Stack = Vec<MacroExpansion<'data, D, Self::MacroInvocation>>;
    type MacroInvocation = D::MacroInvocation;

    fn stack(&self) -> &Self::Stack {
        &self.macro_stack
    }
    fn stack_mut(&mut self) -> &mut Self::Stack {
        &mut self.macro_stack
    }
}

/// Like [`EExpEvaluator`], but can only be used for the duration of the lifetime `'top`. This is
/// used when a macro expansion needs to perform expansions of its own without yielding flow control
/// to the primary evaluator.
///
/// For example, the `(:make_string ...)` macro needs to evaluate each of its arguments to produce
/// a series of text values that it can concatenate. Those arguments may themselves be macro
/// invocations. However, we need to eagerly evaluate them to return `:make_string`'s only output
/// value:
///
/// ```ion_1_1
///     (:make_string
///         (:values a b c)      // Macro invocation argument
///         (:make_string d e)   // Macro invocation argument
///         f)                   // => "abcdef"
/// ```
///
/// The MacroExpansion holding `:make_string`'s mutable state lives in the stack of the primary
/// evaluator, making it (practically) impossible to modify the stack by pushing another
/// MacroExpansion onto it. Instead, it creates an evaluator of its own using short-lived,
/// bump-allocated storage and fully evaluates each argument.
pub struct TransientEExpEvaluator<'top, 'data, D: LazyDecoder<'data>> {
    macro_stack: BumpVec<'top, MacroExpansion<'data, D, D::MacroInvocation>>,
}

impl<'top, 'data, D: LazyDecoder<'data>> TransientEExpEvaluator<'top, 'data, D> {
    pub fn new(context: EncodingContext<'top>) -> Self {
        Self {
            macro_stack: BumpVec::new_in(context.allocator),
        }
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroEvaluator<'top, 'data, D>
    for TransientEExpEvaluator<'top, 'data, D>
{
    type Stack = BumpVec<'top, MacroExpansion<'data, D, Self::MacroInvocation>>;
    type MacroInvocation = D::MacroInvocation;

    fn stack(&self) -> &Self::Stack {
        &self.macro_stack
    }
    fn stack_mut(&mut self) -> &mut Self::Stack {
        &mut self.macro_stack
    }
}

/// A [`MacroEvaluator`] for expanding macro invocations found in a template, all in the context
/// of a data stream in the format `D`.
pub struct TemplateEvaluator<'template, 'top, 'data: 'template, D: LazyDecoder<'data>> {
    argument_stack: BumpVec<'top, LazyExpandedValue<'top, 'data, D>>,
    macro_stack: BumpVec<'top, MacroExpansion<'data, D, &'template Sequence>>,
}

impl<'template, 'top, 'data, D: LazyDecoder<'data>> TemplateEvaluator<'template, 'top, 'data, D> {
    pub fn new(context: EncodingContext<'top>) -> Self {
        Self {
            argument_stack: BumpVec::new_in(context.allocator),
            macro_stack: BumpVec::new_in(context.allocator),
        }
    }
}

impl<'template, 'top, 'data, D: LazyDecoder<'data>> MacroEvaluator<'top, 'data, D>
    for TemplateEvaluator<'template, 'top, 'data, D>
{
    type Stack = BumpVec<'top, MacroExpansion<'data, D, Self::MacroInvocation>>;
    type MacroInvocation = &'template Sequence;

    fn stack(&self) -> &Self::Stack {
        &self.macro_stack
    }
    fn stack_mut(&mut self) -> &mut Self::Stack {
        &mut self.macro_stack
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
pub struct ValuesExpansion<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> {
    // Which argument the macro is in the process of expanding
    arguments: M::ArgumentsIterator,
    // The stack depth where this `values` call lives. When the stack shrinks below this depth,
    // evaluation is complete.
    initial_eval_stack_depth: usize,
}

impl<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> ValuesExpansion<'data, D, M> {
    pub fn new(arguments: M::ArgumentsIterator, initial_eval_stack_depth: usize) -> Self {
        Self {
            arguments,
            initial_eval_stack_depth,
        }
    }

    /// Yields the next [`MacroExpansionStep`] in this macro's evaluation.
    pub fn next<'top>(
        &mut self,
        context: EncodingContext<'top>,
    ) -> IonResult<MacroExpansionStep<'top, 'data, D, M>>
    where
        'data: 'top,
        M: 'top,
    {
        // We visit the argument expressions in the invocation in order from left to right.
        let arg_expr = match self.arguments.next() {
            Some(Err(e)) => return Err(e),
            Some(Ok(arg)) => arg.to_arg_expr(context),
            None => return Ok(MacroExpansionStep::Complete),
        };

        match arg_expr {
            // If the argument is a value, return it.
            ArgumentKind::ValueLiteral(value) => Ok(MacroExpansionStep::ExpandedValue(value)),
            ArgumentKind::Variable(_variable) => todo!("variable expansion"),
            // If the argument is a macro invocation, yield it that so the evaluator can push it onto the stack.
            ArgumentKind::MacroInvocation(invocation) => {
                Ok(MacroExpansionStep::AnotherMacroToEvaluate(invocation))
            }
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
pub struct MakeStringExpansion<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> {
    arguments: M::ArgumentsIterator,
    is_complete: bool,
    spooky: PhantomData<M>,
}

impl<'data, D: LazyDecoder<'data>, M: MacroInvocation<'data, D>> MakeStringExpansion<'data, D, M> {
    pub fn new(arguments: M::ArgumentsIterator) -> Self {
        Self {
            arguments,
            is_complete: false,
            spooky: Default::default(),
        }
    }

    /// Yields the next [`MacroExpansionStep`] in this macro's evaluation.
    pub fn next<'top>(
        &mut self,
        context: EncodingContext<'top>,
    ) -> IonResult<MacroExpansionStep<'top, 'data, D, M>>
    where
        'data: 'top,
        M: 'top,
    {
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
        let mut evaluator = M::make_transient_evaluator(context);

        for arg in self.arguments.by_ref() {
            let arg_expr: ArgumentKind<D, M> = arg?.to_arg_expr(context);
            match arg_expr {
                ArgumentKind::ValueLiteral(value) => {
                    Self::append_expanded_raw_text_value(context, &mut buffer, value.read()?)?
                }
                ArgumentKind::Variable(_variable) => todo!("variable expansion"),
                ArgumentKind::MacroInvocation(invocation) => {
                    for value_result in evaluator.evaluate(context, invocation)? {
                        let value = value_result?;
                        let expanded = value.read()?;
                        Self::append_expanded_raw_text_value(context, &mut buffer, expanded)?
                    }
                }
            }
        }

        let empty_annotations = BumpVec::new_in(context.allocator);

        // Convert our BumpString<'bump> into a &'bump str that we can wrap in an `ExpandedValueRef`
        let constructed_text = buffer.into_bump_str();
        let expanded_value_ref = ExpandedValueRef::String(StrRef::from(constructed_text));

        self.is_complete = true;

        Ok(MacroExpansionStep::ExpandedValue(LazyExpandedValue {
            context,
            source: ExpandedValueSource::Constructed((empty_annotations, expanded_value_ref)),
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
    use bumpalo::Bump as BumpAllocator;

    use crate::lazy::encoding::TextEncoding_1_1;
    use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, TemplateEvaluator};
    use crate::lazy::expanded::macro_table::MacroTable;
    use crate::lazy::expanded::EncodingContext;
    use crate::lazy::reader::LazyTextReader_1_1;
    use crate::lazy::value::LazyValue;
    use crate::{Element, ElementReader, IonResult, SymbolTable};

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
    fn eval_tdl_template_invocation(invocation: &str, expected: &str) -> IonResult<()> {
        let macro_table = MacroTable::new();
        let symbol_table = SymbolTable::new();
        let allocator = BumpAllocator::new();
        let context = EncodingContext::new(&macro_table, &symbol_table, &allocator);
        let invocation = Element::read_one(invocation)?;
        let mut evaluator = TemplateEvaluator::<TextEncoding_1_1>::new(context);
        let actuals = evaluator.evaluate(context, invocation.expect_sexp()?)?;
        let mut expected_reader = LazyTextReader_1_1::new(expected.as_bytes())?;
        for actual_result in actuals {
            // Read the next expected value as a raw value, then wrap it in an `ExpandedRawValueRef`
            // so it can be directly compared to the actual.
            let expected: Element = expected_reader.next()?.unwrap().read()?.try_into()?;
            let actual: Element = LazyValue::from(actual_result?).try_into()?;
            assert_eq!(actual, expected);
        }
        assert!(matches!(expected_reader.next(), Ok(None)));

        Ok(())
    }

    #[test]
    fn values_tdl_macro_invocation() -> IonResult<()> {
        eval_tdl_template_invocation(
            r"(values 1 2 (values 3 4 (values 5 6) 7 8) 9 10)",
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
        eval_tdl_template_invocation(r"(values (void) (void) (void))", "/* nothing */")
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
        (values
            (make_string "foo" '''bar''' "\x62\u0061\U0000007A")
            (make_string 
                '''Hello'''  
                ''', '''
                "world!"))
        "#;
        eval_tdl_template_invocation(invocation, r#" "foobarbaz" "Hello, world!" "#)
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
        eval_tdl_template_invocation(
            r#"
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
            "#,
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
        eval_tdl_template_invocation(
            r#"
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
            "#,
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
