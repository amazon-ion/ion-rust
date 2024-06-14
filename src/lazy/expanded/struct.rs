use std::ops::ControlFlow;

use crate::element::iterators::SymbolsIterator;
use crate::lazy::decoder::private::{LazyRawStructPrivate, RawStructUnexpandedFieldsIterator};
use crate::lazy::decoder::{Decoder, LazyRawFieldName, LazyRawStruct};
use crate::lazy::expanded::macro_evaluator::{
    MacroEvaluator, MacroExpr, RawEExpression, ValueExpr,
};
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::template::{
    AnnotationsRange, ExprRange, TemplateBodyValueExpr, TemplateElement, TemplateMacroInvocation,
    TemplateMacroRef, TemplateStructIndex, TemplateStructUnexpandedFieldsIterator,
};
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, ExpandedValueRef,
    LazyExpandedValue, TemplateVariableReference,
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
    RawNameValue(EncodingContextRef<'top>, D::FieldName<'top>, D::Value<'top>),
    RawNameEExp(EncodingContextRef<'top>, D::FieldName<'top>, D::EExp<'top>),
    RawEExp(EncodingContextRef<'top>, D::EExp<'top>),
    TemplateNameValue(SymbolRef<'top>, TemplateElement<'top>),
    TemplateNameMacro(SymbolRef<'top>, TemplateMacroInvocation<'top>),
    TemplateNameVariable(
        SymbolRef<'top>,
        // The variable name and the expression to which it referred.
        // The expression may be either a raw value or a template element, so it's represented
        // as a `ValueExpr`, which can accommodate both.
        (TemplateVariableReference<'top>, ValueExpr<'top, D>),
    ),
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
        TemplateMacroRef<'top>,
        AnnotationsRange,
        ExprRange,
        &'top TemplateStructIndex,
    ),
    // TODO: Constructed
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
        template: TemplateMacroRef<'top>,
        annotations: AnnotationsRange,
        expressions: ExprRange,
        index: &'top TemplateStructIndex,
    ) -> LazyExpandedStruct<'top, D> {
        let source =
            ExpandedStructSource::Template(environment, template, annotations, expressions, index);
        Self { source, context }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        match &self.source {
            ExpandedStructSource::ValueLiteral(value) => ExpandedAnnotationsIterator {
                source: ExpandedAnnotationsSource::ValueLiteral(value.annotations()),
            },
            ExpandedStructSource::Template(
                _environment,
                template,
                annotations,
                _expressions,
                _index,
            ) => {
                let annotations = template
                    .body
                    .annotations_storage()
                    .get(annotations.ops_range())
                    .unwrap();
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
                    MacroEvaluator::new(self.context, Environment::empty()),
                    raw_struct.unexpanded_fields(self.context),
                )
            }
            ExpandedStructSource::Template(
                environment,
                template,
                _annotations,
                expressions,
                _index,
            ) => {
                let evaluator = MacroEvaluator::new(self.context, *environment);
                ExpandedStructIteratorSource::Template(
                    evaluator,
                    TemplateStructUnexpandedFieldsIterator::new(
                        self.context,
                        *environment,
                        *template,
                        &template.body.expressions[expressions.ops_range()],
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
        match &self.source {
            ExpandedStructSource::ValueLiteral(_) => Environment::empty(),
            ExpandedStructSource::Template(environment, _, _, _, _) => *environment,
        }
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
            ExpandedStructSource::Template(environment, template, _, _, index) => {
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
                let first_result_expr =
                    template.body.expressions.get(first_result_address).unwrap();
                match first_result_expr {
                    // If the expression is a value literal, wrap it in a LazyExpandedValue and return it.
                    TemplateBodyValueExpr::Element(element) => {
                        let value = LazyExpandedValue::from_template(
                            self.context,
                            *environment,
                            TemplateElement::new(*template, element),
                        );
                        Ok(Some(value))
                    }
                    // If the expression is a variable, resolve it in the current environment.
                    TemplateBodyValueExpr::Variable(variable_ref) => {
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
                                let mut evaluator = MacroEvaluator::new(self.context, *environment);
                                evaluator.push(*invocation)?;
                                evaluator.next()
                            }
                        }
                    }
                    TemplateBodyValueExpr::MacroInvocation(body_invocation) => {
                        let invocation = body_invocation.resolve(*template, self.context);
                        let mut evaluator = MacroEvaluator::new(self.context, *environment);
                        evaluator.push(invocation)?;
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
        MacroEvaluator<'top, D>,
        RawStructUnexpandedFieldsIterator<'top, D>,
    ),
    // The struct we're iterating over is a value in a TDL template. It may contain macro
    // invocations that need to be evaluated.
    Template(
        MacroEvaluator<'top, D>,
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
        LazyExpandedStruct<'top, D>,
        &'top mut ExpandedStructIterator<'top, D>,
    ),
}

impl<'top, D: Decoder> Iterator for ExpandedStructIterator<'top, D> {
    type Item = IonResult<LazyExpandedField<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let Self {
            ref mut source,
            ref mut state,
        } = *self;
        match source {
            ExpandedStructIteratorSource::Template(tdl_macro_evaluator, template_iterator) => {
                Self::next_field_from(
                    template_iterator.context(),
                    state,
                    tdl_macro_evaluator,
                    template_iterator,
                )
            }
            ExpandedStructIteratorSource::ValueLiteral(e_exp_evaluator, raw_struct_iter) => {
                Self::next_field_from(
                    raw_struct_iter.context(),
                    state,
                    e_exp_evaluator,
                    raw_struct_iter,
                )
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
        context: EncodingContextRef<'top>,
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
                    match Self::next_from_iterator(context, state, evaluator, iter) {
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
                            // We got another value from the macro we're evaluating. Emit
                            // it as another field using the same field_name.
                            return Some(Ok(LazyExpandedField::new(*field_name, next_value)));
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
        context: EncodingContextRef<'top>,
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
            RawNameValue(context, name, value) => {
                Break(Some(Ok(LazyExpandedField::from_raw_field(
                    context,
                    name,
                    LazyExpandedValue::from_literal(context, value),
                ))))
            }
            TemplateNameValue(name, value) => Break(Some(Ok(LazyExpandedField::from_template(
                value.template(),
                name,
                LazyExpandedValue::from_template(context, evaluator.environment(), value),
            )))),
            // (name, macro invocation) pair. For example: `foo: (:bar)`
            RawNameEExp(context, raw_name, raw_eexp) => {
                let eexp = match raw_eexp.resolve(context) {
                    Ok(eexp) => eexp,
                    Err(e) => return Break(Some(Err(e))),
                };
                if let Err(e) = evaluator.push(eexp) {
                    return Break(Some(Err(e)));
                }
                let name = LazyExpandedFieldName::RawName(context, raw_name);
                *state = ExpandedStructIteratorState::ExpandingValueExpr(name);
                // We've pushed the macro invocation onto the evaluator's stack, but further evaluation
                // is needed to get our next field.
                Continue(())
            }
            RawEExp(context, eexp) => {
                let invocation = match eexp.resolve(context) {
                    Ok(invocation) => invocation,
                    Err(e) => return Break(Some(Err(e))),
                };
                // The next expression from the iterator was a macro. We expect it to expand to a
                // single struct whose fields will be merged into the one we're iterating over. For example:
                //     {a: 1, (:make_struct b 2 c 3), d: 4}
                // expands to:
                //     {a: 1, b: 2, c: 3, d: 4}
                match Self::begin_inlining_struct_from_macro(state, evaluator, invocation.into()) {
                    // If the macro expanded to a struct as expected, continue the evaluation
                    // until we get a field to return.
                    Ok(_) => Continue(()),
                    // If something went wrong, surface the error.
                    Err(e) => Break(Some(Err(e))),
                }
            }
            TemplateNameMacro(name_symbol, invocation) => {
                if let Err(e) = evaluator.push(invocation) {
                    return Break(Some(Err(e)));
                }
                let name =
                    LazyExpandedFieldName::TemplateName(invocation.host_template(), name_symbol);
                *state = ExpandedStructIteratorState::ExpandingValueExpr(name);
                // We've pushed the macro invocation onto the evaluator's stack, but further evaluation
                // is needed to get our next field.
                Continue(())
            }
            TemplateNameVariable(name_symbol, (variable_ref, value_expr)) => {
                use ValueExpr::*;
                let name = LazyExpandedFieldName::TemplateName(variable_ref.template, name_symbol);
                match value_expr {
                    ValueLiteral(value) => {
                        return Break(Some(Ok(LazyExpandedField::from_template(
                            variable_ref.template,
                            name_symbol,
                            value.via_variable(variable_ref),
                        ))))
                    }
                    MacroInvocation(MacroExpr::EExp(eexp)) => {
                        if let Err(e) = evaluator.push(eexp) {
                            return Break(Some(Err(e)));
                        }
                        *state = ExpandedStructIteratorState::ExpandingValueExpr(name);
                        // We've pushed the macro invocation onto the evaluator's stack, but further evaluation
                        // is needed to get our next field.
                        Continue(())
                    }
                    MacroInvocation(MacroExpr::TemplateMacro(invocation)) => {
                        if let Err(e) = evaluator.push(invocation) {
                            return Break(Some(Err(e)));
                        }
                        *state = ExpandedStructIteratorState::ExpandingValueExpr(name);
                        // We've pushed the macro invocation onto the evaluator's stack, but further evaluation
                        // is needed to get our next field.
                        Continue(())
                    }
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
        let mut evaluation = evaluator.evaluate(invocation)?;
        let expanded_value = match evaluation.next() {
            Some(Ok(item)) => item,
            Some(Err(e)) => return Err(e),
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
        *state = ExpandedStructIteratorState::InliningAStruct(struct_, iter);
        Ok(())
    }
}
