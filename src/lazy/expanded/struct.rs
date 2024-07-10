use std::ops::ControlFlow;

use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::private::{LazyRawStructPrivate, RawStructUnexpandedFieldsIterator};
use crate::lazy::decoder::{Decoder, LazyRawFieldName, LazyRawStruct};
use crate::lazy::expanded::macro_evaluator::{
    MacroEvaluator, MacroExpansion, MacroExpr, ValueExpr,
};
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{
    TemplateBodyExprKind, TemplateElement, TemplateMacroRef, TemplateStructIndex,
    TemplateStructUnexpandedFieldsIterator,
};
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, ExpandedValueRef,
    LazyExpandedValue,
};
use crate::result::IonFailure;
use crate::symbol_ref::AsSymbolRef;
use crate::{IonError, IonResult, RawSymbolRef, SymbolRef};

/// A unified type embodying all possible field representations coming from both input data
/// (i.e. raw structs of some encoding) and template bodies.
// LazyRawStruct implementations have a `unexpanded_fields` method that lifts its raw fields into
// `UnexpandedField` instances. Similarly, the `TemplateStructUnexpandedFieldsIterator` turns a
// template's struct body into `UnexpandedField` instances. The `ExpandedStructIterator` unpacks
// and expands the field as part of its iteration process.
#[derive(Debug, Clone, Copy)]
pub enum UnexpandedField<'top, D: Decoder> {
    NameValue(LazyExpandedFieldName<'top, D>, LazyExpandedValue<'top, D>),
    NameMacro(LazyExpandedFieldName<'top, D>, MacroExpr<'top, D>),
    Macro(MacroExpr<'top, D>),
}

#[derive(Debug, Clone, Copy)]
pub struct LazyExpandedField<'top, D: Decoder> {
    name: LazyExpandedFieldName<'top, D>,
    value: LazyExpandedValue<'top, D>,
}

impl<'top, D: Decoder> LazyExpandedField<'top, D> {}

impl<'top, D: Decoder> LazyExpandedField<'top, D> {
    pub fn new(name: LazyExpandedFieldName<'top, D>, value: LazyExpandedValue<'top, D>) -> Self {
        Self { name, value }
    }

    pub fn value(&self) -> LazyExpandedValue<'top, D> {
        self.value
    }

    pub fn name(&self) -> LazyExpandedFieldName<'top, D> {
        self.name
    }
}

impl<'top, D: Decoder> LazyExpandedField<'top, D> {
    fn from_raw_field(
        context: EncodingContextRef<'top>,
        name: D::FieldName<'top>,
        value: impl Into<LazyExpandedValue<'top, D>>,
    ) -> Self {
        Self {
            name: LazyExpandedFieldName::RawName(context, name),
            value: value.into(),
        }
    }

    fn from_template(
        template: TemplateMacroRef<'top>,
        name: SymbolRef<'top>,
        value: impl Into<LazyExpandedValue<'top, D>>,
    ) -> Self {
        Self {
            name: LazyExpandedFieldName::TemplateName(template, name),
            value: value.into(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum LazyExpandedFieldName<'top, D: Decoder> {
    RawName(EncodingContextRef<'top>, D::FieldName<'top>),
    TemplateName(TemplateMacroRef<'top>, SymbolRef<'top>),
    // TODO: `Constructed` needed for names in `(make_struct ...)`
}

impl<'top, D: Decoder> LazyExpandedFieldName<'top, D> {
    pub(crate) fn read(&self) -> IonResult<SymbolRef<'top>> {
        match self {
            LazyExpandedFieldName::RawName(context, name) => match name.read()? {
                RawSymbolRef::Text(text) => Ok(text.into()),
                RawSymbolRef::SymbolId(sid) => context
                    .symbol_table()
                    .symbol_for(sid)
                    .map(AsSymbolRef::as_symbol_ref)
                    .ok_or_else(|| {
                        IonError::decoding_error(format!(
                            "field name with sid ${sid} has unknown text"
                        ))
                    }),
            },
            LazyExpandedFieldName::TemplateName(_template_ref, symbol_ref) => Ok(*symbol_ref),
        }
    }

    pub(crate) fn read_raw(&self) -> IonResult<RawSymbolRef<'top>> {
        match self {
            LazyExpandedFieldName::RawName(_, name) => name.read(),
            LazyExpandedFieldName::TemplateName(_, name) => Ok((*name).into()),
        }
    }
}

#[derive(Copy, Clone)]
pub enum ExpandedStructSource<'top, D: Decoder> {
    ValueLiteral(D::Struct<'top>),
    Template(
        Environment<'top, D>,
        TemplateElement<'top>,
        &'top TemplateStructIndex,
    ),
    // TODO: Constructed
}

impl<'top, D: Decoder> ExpandedStructSource<'top, D> {
    fn environment(&self) -> Environment<'top, D> {
        match self {
            ExpandedStructSource::ValueLiteral(_) => Environment::empty(),
            ExpandedStructSource::Template(environment, _, _) => *environment,
        }
    }
}

#[derive(Copy, Clone)]
pub struct LazyExpandedStruct<'top, D: Decoder> {
    pub(crate) context: EncodingContextRef<'top>,
    pub(crate) source: ExpandedStructSource<'top, D>,
}

#[cfg(feature = "experimental-tooling-apis")]
impl<'top, D: Decoder> LazyExpandedStruct<'top, D> {
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
    pub fn source(&self) -> ExpandedStructSource<'top, D> {
        self.source
    }
}

impl<'top, D: Decoder> LazyExpandedStruct<'top, D> {
    pub fn from_literal(
        context: EncodingContextRef<'top>,
        sexp: D::Struct<'top>,
    ) -> LazyExpandedStruct<'top, D> {
        let source = ExpandedStructSource::ValueLiteral(sexp);
        Self { source, context }
    }

    pub fn from_template(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        element: &TemplateElement<'top>,
        index: &'top TemplateStructIndex,
    ) -> LazyExpandedStruct<'top, D> {
        let source = ExpandedStructSource::Template(environment, *element, index);
        Self { source, context }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        match &self.source {
            ExpandedStructSource::ValueLiteral(value) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            },
            ExpandedStructSource::Template(_environment, element, _index) => {
                let annotations = element.annotations();
                ExpandedAnnotationsIterator {
                    source: ExpandedAnnotationsSource::Template(SymbolsIterator::new(annotations)),
                }
            }
        }
    }

    pub fn iter(&self) -> ExpandedStructIterator<'top, D> {
        let source = match &self.source {
            ExpandedStructSource::ValueLiteral(raw_struct) => {
                ExpandedStructIteratorSource::ValueLiteral(
                    self.context
                        .allocator()
                        .alloc_with(|| MacroEvaluator::new()),
                    raw_struct.unexpanded_fields(self.context),
                )
            }
            ExpandedStructSource::Template(environment, element, _index) => {
                let evaluator = self
                    .context
                    .allocator()
                    .alloc_with(|| MacroEvaluator::new_with_environment(*environment));
                let template = element.template();
                ExpandedStructIteratorSource::Template(
                    evaluator,
                    TemplateStructUnexpandedFieldsIterator::new(
                        self.context,
                        *environment,
                        template,
                        template
                            .body()
                            .expressions
                            .get(element.expr_range().tail())
                            .unwrap(),
                    ),
                )
            }
        };
        ExpandedStructIterator {
            source,
            state: ExpandedStructIteratorState::ReadingFieldFromSource,
        }
    }

    fn environment(&self) -> Environment<'top, D> {
        self.source.environment()
    }

    pub fn bump_iter(&self) -> &'top mut ExpandedStructIterator<'top, D> {
        self.context.allocator().alloc_with(|| self.iter())
    }

    pub fn find(&self, name: &str) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
        match &self.source {
            // If we're reading from a struct literal, do a linear scan over its fields until we
            // encounter one with the requested name.
            ExpandedStructSource::ValueLiteral(_) => {
                for field_result in self.iter() {
                    let field = field_result?;
                    if field.name().read()?.text() == Some(name) {
                        return Ok(Some(field.value));
                    }
                }
                // If there is no such field, return None.
                Ok(None)
            }
            // If we're reading from a struct in a template, consult its field index to see if one or
            // more fields with the requested name exist.
            ExpandedStructSource::Template(environment, element, index) => {
                let Some(value_expr_addresses) = index.get(name) else {
                    // If the field name is not in the index, it's not in the struct.
                    return Ok(None);
                };
                // If there are fields with the requested name, return the first one.
                // TODO: This is a starting point. There's room for an API that returns an iterator
                //       over all matching entries. Note, however, that it would be difficult to
                //       offer an efficient implementation of 'get last' because that could require
                //       fully evaluating one or more macros to find the last value.
                let first_result_address = value_expr_addresses[0];
                let first_result_expr = element
                    .template()
                    .body()
                    .expressions()
                    .get(first_result_address)
                    .unwrap();
                match first_result_expr.kind() {
                    // If the expression is a value literal, wrap it in a LazyExpandedValue and return it.
                    TemplateBodyExprKind::Element(body_element) => {
                        let value = LazyExpandedValue::from_template(
                            self.context,
                            *environment,
                            TemplateElement::new(
                                element.template().macro_ref(),
                                body_element,
                                first_result_expr.expr_range(),
                            ),
                        );
                        Ok(Some(value))
                    }
                    // If the expression is a variable, resolve it in the current environment.
                    TemplateBodyExprKind::Variable(variable_ref) => {
                        let value_expr = environment
                            .expressions()
                            .get(variable_ref.signature_index())
                            .unwrap();
                        match value_expr {
                            // If the variable maps to a value literal, return it.
                            ValueExpr::ValueLiteral(value) => Ok(Some(*value)),
                            // If the variable maps to a macro invocation, evaluate it until we get
                            // the first value back.
                            ValueExpr::MacroInvocation(invocation) => {
                                let mut evaluator =
                                    MacroEvaluator::for_macro_expr(*environment, *invocation)?;
                                evaluator.next()
                            }
                        }
                    }
                    TemplateBodyExprKind::MacroInvocation(body_invocation) => {
                        let invocation = body_invocation.resolve(
                            self.context,
                            element.template().address(),
                            first_result_expr.expr_range(),
                        );
                        let mut evaluator = MacroEvaluator::new_with_environment(*environment);
                        let expansion =
                            MacroExpansion::initialize(*environment, invocation.into())?;
                        evaluator.push(expansion);
                        evaluator.next()
                    }
                }
            }
        }
    }

    pub fn get(&self, name: &str) -> IonResult<Option<ExpandedValueRef<'top, D>>> {
        self.find(name)?.map(|f| f.read()).transpose()
    }

    pub fn get_expected(&self, name: &str) -> IonResult<ExpandedValueRef<'top, D>> {
        if let Some(value) = self.get(name)? {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("did not find expected struct field '{}'", name))
        }
    }
}

pub enum ExpandedStructIteratorSource<'top, D: Decoder> {
    // The struct we're iterating over is a literal in the data stream. It may contain
    // e-expressions that need to be evaluated.
    ValueLiteral(
        // Giving the struct iterator its own evaluator means that we can abandon the iterator
        // at any time without impacting the evaluation state of its parent container.
        &'top mut MacroEvaluator<'top, D>,
        RawStructUnexpandedFieldsIterator<'top, D>,
    ),
    // The struct we're iterating over is a value in a TDL template. It may contain macro
    // invocations that need to be evaluated.
    Template(
        &'top mut MacroEvaluator<'top, D>,
        TemplateStructUnexpandedFieldsIterator<'top, D>,
    ),
    // TODO: Constructed
}

pub struct ExpandedStructIterator<'top, D: Decoder> {
    // Each variant of 'source' below holds its own encoding context reference
    source: ExpandedStructIteratorSource<'top, D>,
    // Stores information about any operations that are still in progress.
    state: ExpandedStructIteratorState<'top, D>,
}

/// Ion 1.1's struct is very versatile, and supports a variety of expansion operations. This
/// types indicates which operation is in the process of being carried out.
enum ExpandedStructIteratorState<'top, D: Decoder> {
    // The iterator is not performing any operations. It is ready to pull the next field from its
    // source.
    ReadingFieldFromSource,
    // The iterator is expanding a macro invocation that was found in value position; for example:
    //     foo: (:values 1 2 3)
    // would be expanded to:
    //     foo: 1,
    //     foo: 2,
    //     foo: 3,
    // This variant holds the field name that will be repeated for every value in the macro's
    // expansion.
    ExpandingValueExpr(LazyExpandedFieldName<'top, D>),
    // The iterator is in the process of incrementally inlining a macro found in field name
    // position that expands to a struct; for example:
    //     (:values {foo: 1, bar: 2})
    // would expand to:
    //     foo: 1,
    //     bar: 2,
    // This variant holds a pointer to that struct's iterator living in the
    // EncodingContext's bump allocator.
    InliningAStruct(
        &'top mut LazyExpandedStruct<'top, D>,
        &'top mut ExpandedStructIterator<'top, D>,
    ),
}

impl<'top, D: Decoder> Iterator for ExpandedStructIterator<'top, D> {
    type Item = IonResult<LazyExpandedField<'top, D>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            ref mut source,
            ref mut state,
        } = *self;
        match source {
            ExpandedStructIteratorSource::Template(tdl_macro_evaluator, template_iterator) => {
                Self::next_field_from(state, *tdl_macro_evaluator, template_iterator)
            }
            ExpandedStructIteratorSource::ValueLiteral(e_exp_evaluator, raw_struct_iter) => {
                Self::next_field_from(state, *e_exp_evaluator, raw_struct_iter)
            }
        }
    }
}

// Struct expansion is rather complex, and we need to perform it in text Ion, binary Ion, and in
// the body of templates. This implementation covers all of those use cases, but involves some
// potentially intimidating generics as a result. We'll walk through them as they're introduced.
//
//  'top: The lifetime associated with the top-level value we're currently reading at some depth.
//     D: The decoder being used to read the Ion data stream. For example: `TextEncoding_1_1`
impl<'top, D: Decoder> ExpandedStructIterator<'top, D> {
    /// Pulls the next expanded field from the raw source struct. The field returned may correspond
    /// to a `(name, value literal)` pair in the raw struct, or it may be the product of a macro
    /// evaluation.
    fn next_field_from<
        // The lifetime of this method invocation.
        'a,
        // An iterator over the struct we're expanding. It may be the fields iterator from a
        // LazyRawStruct, or it could be a `TemplateStructRawFieldsIterator`.
        I: Iterator<Item = IonResult<UnexpandedField<'top, D>>>,
    >(
        state: &'a mut ExpandedStructIteratorState<'top, D>,
        evaluator: &'a mut MacroEvaluator<'top, D>,
        iter: &'a mut I,
    ) -> Option<IonResult<LazyExpandedField<'top, D>>> {
        // This method begins by pulling raw field expressions from the source iterator.
        // If the expression is a (name, value literal) pair, we can wrap it in an LazyExpandedField
        // and return it immediately. However, if it is a (name, macro) pair or (macro) expression,
        // then an unknown amount of evaluation will need to happen before we can return our next
        // field.
        loop {
            use ControlFlow::{Break, Continue};
            use ExpandedStructIteratorState::*;
            match state {
                // This is the initial state. We're reading a raw field expression from our source
                // iterator.
                ReadingFieldFromSource => {
                    // We'll see what kind of expression it is.
                    match Self::next_from_iterator(state, evaluator, iter) {
                        // The iterator found a (name, value literal) pair.
                        Break(maybe_result) => return maybe_result,
                        // The iterator found a (name, macro) pair or a macro; further evaluation
                        // is needed to yield a (name, value) pair.
                        Continue(_) => continue,
                    }
                }
                // The iterator previously encountered a macro in field-name position. That macro
                // yielded a struct, and now we're merging that expanded struct's fields into our
                // own one at a time.
                InliningAStruct(_struct, struct_iter) => {
                    if let Some(inlined_field) = struct_iter.next() {
                        // We pulled another field from the struct we're inlining.
                        return Some(inlined_field);
                    } else {
                        // We're done inlining this struct. Switch back to reading from the source.
                        *state = ReadingFieldFromSource;
                        continue;
                    }
                }
                // The iterator previously encountered a (name, macro) pair. We're evaluating the
                // macro in field value position, emitting (name, value) pairs for each value
                // in the expansion, one at a time.
                ExpandingValueExpr(field_name) => {
                    match evaluator.next() {
                        Err(e) => return Some(Err(e)),
                        Ok(Some(next_value)) => {
                            let field_name = *field_name;
                            if evaluator.is_empty() {
                                *state = ReadingFieldFromSource;
                            }
                            // We got another value from the macro we're evaluating. Emit
                            // it as another field using the same field_name.
                            return Some(Ok(LazyExpandedField::new(field_name, next_value)));
                        }
                        Ok(None) => {
                            // The macro in the value position is no longer emitting values. Switch
                            // back to reading from the source.
                            *state = ReadingFieldFromSource;
                        }
                    }
                }
            }
        }
    }

    /// Pulls a single unexpanded field expression from the source iterator and sets `state` according to
    /// the expression's kind.
    fn next_from_iterator<I: Iterator<Item = IonResult<UnexpandedField<'top, D>>>>(
        state: &mut ExpandedStructIteratorState<'top, D>,
        evaluator: &mut MacroEvaluator<'top, D>,
        iter: &mut I,
    ) -> ControlFlow<Option<IonResult<LazyExpandedField<'top, D>>>> {
        // Because this helper function is always being invoked from within a loop, it uses
        // the `ControlFlow` enum to signal whether its return value should cause the loop to
        // terminate (`ControlFlow::Break`) or continue (`ControlFlow::Continue`).
        use ControlFlow::*;

        // If the iterator is empty, we're done.
        let unexpanded_field = match iter.next() {
            Some(Ok(field_expr)) => field_expr,
            Some(Err(error)) => {
                return Break(Some(Err::<LazyExpandedField<'top, D>, IonError>(error)))
            }
            None => return Break(None),
        };

        use UnexpandedField::*;
        match unexpanded_field {
            NameValue(name, value) => Break(Some(Ok(LazyExpandedField::new(name, value)))),
            NameMacro(name, invocation) => {
                let environment = evaluator.environment();
                let expansion = match MacroExpansion::initialize(environment, invocation) {
                    Ok(expansion) => expansion,
                    Err(e) => return Break(Some(Err(e))),
                };
                // If the macro is guaranteed to expand to exactly one value, we can evaluate it
                // in place.
                if invocation
                    .invoked_macro()
                    .expansion_analysis()
                    .must_produce_exactly_one_value()
                {
                    let value = match expansion.expand_singleton() {
                        Ok(value) => value,
                        Err(e) => return Break(Some(Err(e))),
                    };
                    return Break(Some(Ok(LazyExpandedField::new(name, value))));
                }
                // Otherwise, we'll add it to the evaluator's stack and return to the top of the loop.
                evaluator.push(expansion);
                *state = ExpandedStructIteratorState::ExpandingValueExpr(name);
                // We've pushed the macro invocation onto the evaluator's stack, but further evaluation
                // is needed to get our next field.
                Continue(())
            }
            Macro(invocation) => {
                // The next expression from the iterator was a macro. We expect it to expand to a
                // single struct whose fields will be merged into the one we're iterating over. For example:
                //     {a: 1, (:make_struct b 2 c 3), d: 4}
                // expands to:
                //     {a: 1, b: 2, c: 3, d: 4}
                match Self::begin_inlining_struct_from_macro(state, evaluator, invocation) {
                    // If the macro expanded to a struct as expected, continue the evaluation
                    // until we get a field to return.
                    Ok(_) => Continue(()),
                    // If something went wrong, surface the error.
                    Err(e) => Break(Some(Err(e))),
                }
            }
        }
    }

    /// Pulls the next value from the evaluator, confirms that it's a struct, and then switches
    /// the iterator state to `InliningAStruct` so it can begin merging its fields.
    fn begin_inlining_struct_from_macro<'a, 'name: 'top>(
        state: &mut ExpandedStructIteratorState<'top, D>,
        evaluator: &mut MacroEvaluator<'top, D>,
        invocation: MacroExpr<'top, D>,
    ) -> IonResult<()> {
        let environment = evaluator.environment();
        let expansion = MacroExpansion::initialize(environment, invocation)?;
        evaluator.push(expansion);
        let expanded_value = match evaluator.next()? {
            Some(item) => item,
            None => return IonResult::decoding_error(format!("macros in field name position must produce a single struct; '{:?}' produced nothing", invocation)),
        };
        let struct_ = match expanded_value.read()? {
            ExpandedValueRef::Struct(s) => s,
            other => {
                return IonResult::decoding_error(format!(
                    "macros in field name position must produce structs; '{:?}' produced: {:?}",
                    invocation, other
                ))
            }
        };
        let iter: &'top mut ExpandedStructIterator<'top, D> = struct_.bump_iter();
        let struct_ref = invocation.context().allocator().alloc_with(|| struct_);
        *state = ExpandedStructIteratorState::InliningAStruct(struct_ref, iter);
        Ok(())
    }
}
