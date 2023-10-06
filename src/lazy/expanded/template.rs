use std::marker::PhantomData;
use std::ops::{Deref, Range};

use crate::lazy::decoder::{LazyDecoder, RawFieldExpr, RawValueExpr};
use crate::lazy::expanded::macro_evaluator::{
    ArgumentKind, MacroEvaluator, MacroInvocation, TemplateEvaluator, ToArgumentKind,
};
use crate::lazy::expanded::macro_table::MacroKind;
use crate::lazy::expanded::{
    EncodingContext, ExpandedValueRef, ExpandedValueSource, LazyExpandedValue,
};
use crate::lazy::text::raw::v1_1::reader::{MacroAddress, MacroIdRef, TemplateBodyExprAddress};
use crate::result::IonFailure;
use crate::{Bytes, Decimal, Int, IonResult, IonType, Str, Symbol, Timestamp};

#[derive(Debug, Clone)]
pub enum ParameterEncoding {
    /// A 'tagged' type is one whose binary encoding begins with an opcode (sometimes called a 'tag'.)
    Tagged,
    // TODO: tagless types
}
#[derive(Debug, Clone)]
pub struct Parameter {
    name: String,
    encoding: ParameterEncoding,
    // TODO: Grouping
}

impl Parameter {
    pub fn new(name: String, encoding: ParameterEncoding) -> Self {
        Self { name, encoding }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }
}

#[derive(Debug, Clone)]
pub struct MacroSignature {
    parameters: Vec<Parameter>,
}

impl MacroSignature {
    fn with_parameter(mut self, name: impl Into<String>, encoding: ParameterEncoding) -> Self {
        self.parameters.push(Parameter {
            name: name.into(),
            encoding,
        });
        self
    }

    pub fn parameters(&self) -> &[Parameter] {
        &self.parameters
    }
    pub fn new(parameters: Vec<Parameter>) -> Self {
        Self { parameters }
    }
}

/// A pairing of a template reference and the address in the macro table at which it was found.
/// This type implements Deref to allow easy access to the methods on the template.
#[derive(Debug, Clone, Copy)]
pub struct TemplateMacroRef<'top> {
    template_address: MacroAddress,
    template: &'top TemplateMacro,
}

impl<'top> TemplateMacroRef<'top> {
    pub fn new(template_address: MacroAddress, template: &'top TemplateMacro) -> Self {
        Self {
            template_address,
            template,
        }
    }
    pub fn address(&self) -> MacroAddress {
        self.template_address
    }
}

impl<'top> Deref for TemplateMacroRef<'top> {
    type Target = &'top TemplateMacro;

    fn deref(&self) -> &Self::Target {
        &self.template
    }
}

#[derive(Debug, Clone)]
pub struct TemplateMacro {
    // TODO: Make the name optional
    pub(crate) name: Symbol,
    pub(crate) signature: MacroSignature,
    pub(crate) body: TemplateBody,
}

impl TemplateMacro {
    pub fn name(&self) -> &str {
        self.name.text().expect("template names cannot be $0")
    }
    pub fn signature(&self) -> &MacroSignature {
        &self.signature
    }
    pub fn body(&self) -> &TemplateBody {
        &self.body
    }
}

pub struct TemplateSequenceIterator<'top, 'data, D: LazyDecoder<'data>> {
    context: EncodingContext<'top>,
    template: TemplateMacroRef<'top>,
    evaluator: TemplateEvaluator<'top, 'data, D>,
    value_expressions: &'top [TemplateBodyValueExpr],
    index: usize,
}

impl<'top, 'data, D: LazyDecoder<'data>> TemplateSequenceIterator<'top, 'data, D> {
    pub fn new(
        context: EncodingContext<'top>,
        template: TemplateMacroRef<'top>,
        evaluator: TemplateEvaluator<'top, 'data, D>,
        value_expressions: &'top [TemplateBodyValueExpr],
    ) -> Self {
        Self {
            context,
            template,
            evaluator,
            value_expressions,
            index: 0,
        }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> Iterator for TemplateSequenceIterator<'top, 'data, D> {
    type Item = IonResult<LazyExpandedValue<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // If the evaluator's stack is not empty, give it the opportunity to yield a value.
            if self.evaluator.stack_depth() > 0 {
                match self.evaluator.next(self.context, 0).transpose() {
                    Some(value) => return Some(value),
                    None => {
                        // The stack did not produce values and is empty, pull
                        // the next expression from `self.sequence`
                    }
                }
            }
            let step_address = self.index;
            // We didn't get a value from the evaluator, so pull the next expansion step.
            let step = self.value_expressions.get(step_address)?;
            self.index += 1;
            return match step {
                TemplateBodyValueExpr::Element(element) => Some(Ok(LazyExpandedValue {
                    context: self.context,
                    source: ExpandedValueSource::Template(TemplateElement::new(
                        self.template,
                        element,
                    )),
                })),
                TemplateBodyValueExpr::MacroInvocation(body_invocation) => {
                    // ...it's a TDL macro invocation. Push it onto the evaluator's stack and return
                    // to the top of the loop.
                    let invocation_address = TemplateMacroInvocationAddress::new(
                        self.template.address(),
                        body_invocation.macro_address,
                        step_address,
                        body_invocation.arg_expr_range.len(),
                    );
                    match self.evaluator.push(self.context, invocation_address) {
                        Ok(_) => continue,
                        Err(e) => return Some(Err(e)),
                    };
                }
                TemplateBodyValueExpr::Variable(_) => {
                    todo!("TemplateSequenceIterator: variable expansion");
                }
            };
        }
    }
}

// An iterator that pulls values from a template body and wraps them in a `RawFieldExpr` to
// mimic reading them from input. The LazyExpandedStruct handles evaluating any macros that this
// yields.
pub struct TemplateStructRawFieldsIterator<'top, 'data, D: LazyDecoder<'data>> {
    context: EncodingContext<'top>,
    template: TemplateMacroRef<'top>,
    expressions: &'top [TemplateBodyValueExpr],
    index: usize,
    spooky: PhantomData<&'data D>,
}

impl<'top, 'data, D: LazyDecoder<'data>> TemplateStructRawFieldsIterator<'top, 'data, D> {
    pub fn new(
        context: EncodingContext<'top>,
        template: TemplateMacroRef<'top>,
        expressions: &'top [TemplateBodyValueExpr],
    ) -> Self {
        Self {
            context,
            template,
            expressions,
            index: 0,
            spooky: PhantomData,
        }
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> Iterator
    for TemplateStructRawFieldsIterator<'top, 'data, D>
{
    type Item =
        IonResult<RawFieldExpr<'top, TemplateElement<'top>, TemplateMacroInvocationAddress>>;

    fn next(&mut self) -> Option<Self::Item> {
        let name_expr_address = self.index;
        let name_element = self
            .expressions
            .get(name_expr_address)?
            .expect_element()
            .expect("field name must be a literal");
        let name_token = match LazyExpandedValue::<D>::from_template(
            self.context,
            TemplateElement::new(self.template, name_element),
        )
        .read()
        {
            Ok(ExpandedValueRef::Symbol(token)) => token,
            Ok(ExpandedValueRef::String(str_ref)) => str_ref.into(),
            Ok(_) => {
                return Some(IonResult::decoding_error(
                    "template struct had a non-text field name",
                ))
            }
            Err(e) => return Some(Err(e)),
        };
        let value_expr_address = name_expr_address + 1;
        let value = match self.expressions.get(value_expr_address) {
            None => {
                return Some(IonResult::decoding_error(
                    "template struct had field name with no value",
                ))
            }
            Some(TemplateBodyValueExpr::Element(element)) => {
                RawValueExpr::ValueLiteral(TemplateElement::new(self.template, element))
            }
            Some(TemplateBodyValueExpr::MacroInvocation(invocation)) => {
                RawValueExpr::MacroInvocation(TemplateMacroInvocationAddress::new(
                    self.template.address(),
                    invocation.macro_address(),
                    value_expr_address,
                    invocation.arg_expr_range().len(),
                ))
            }
            Some(TemplateBodyValueExpr::Variable(_)) => {
                todo!("variable expansion in template structs")
            }
        };
        self.index += 2;
        Some(Ok(RawFieldExpr::NameValuePair(name_token, value)))
    }
}

/// Stores a sequence of expansion steps that need to be evaluated in turn.
///
/// See [`TemplateBodyValueExpr`] for details.
#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBody {
    pub(crate) expressions: Vec<TemplateBodyValueExpr>,
    pub(crate) annotations_storage: Vec<Symbol>,
}

impl TemplateBody {
    pub fn expressions(&self) -> &Vec<TemplateBodyValueExpr> {
        &self.expressions
    }
    pub fn annotations_storage(&self) -> &Vec<Symbol> {
        &self.annotations_storage
    }

    pub fn push_element(&mut self, element: TemplateBodyElement) {
        self.expressions
            .push(TemplateBodyValueExpr::Element(element))
    }

    pub fn push_variable(&mut self, signature_index: usize) {
        self.expressions.push(TemplateBodyValueExpr::Variable(
            TemplateBodyVariableReference::new(signature_index),
        ))
    }

    pub fn push_macro_invocation(&mut self, address: usize, expr_range: ExprRange) {
        self.expressions
            .push(TemplateBodyValueExpr::MacroInvocation(
                TemplateBodyMacroInvocation::new(address, expr_range),
            ))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TemplateValueExpr<'top> {
    template: TemplateMacroRef<'top>,
    value_expr: &'top TemplateBodyValueExpr,
}

impl<'top> TemplateValueExpr<'top> {
    pub fn new(template: TemplateMacroRef<'top>, value_expr: &'top TemplateBodyValueExpr) -> Self {
        Self {
            template,
            value_expr,
        }
    }
    pub fn template(&self) -> TemplateMacroRef<'top> {
        self.template
    }
    pub fn value_expr(&self) -> &'top TemplateBodyValueExpr {
        self.value_expr
    }
}

/// An expression appearing in value position in a template body.
#[derive(Debug, Clone, PartialEq)]
pub enum TemplateBodyValueExpr {
    /// A potentially annotated value literal.
    Element(TemplateBodyElement),
    /// A reference to a variable that needs to be expanded.
    Variable(TemplateBodyVariableReference),
    /// A macro invocation that needs to be expanded.
    MacroInvocation(TemplateBodyMacroInvocation),
}

#[derive(Debug, Clone)]
pub struct TemplateMacroArgExpr {
    // The address of the template macro in which this argument expression appears
    host_template_address: MacroAddress,
    value_expr_address: TemplateBodyExprAddress,
}

impl TemplateMacroArgExpr {
    pub fn new(
        host_template_address: MacroAddress,
        value_expr_address: TemplateBodyExprAddress,
    ) -> Self {
        Self {
            host_template_address,
            value_expr_address,
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBodyMacroInvocation {
    macro_address: MacroAddress,
    arg_expr_range: ExprRange,
}

impl TemplateBodyMacroInvocation {
    pub fn new(macro_address: MacroAddress, arg_expr_range: ExprRange) -> Self {
        Self {
            macro_address,
            arg_expr_range,
        }
    }
    pub fn macro_address(&self) -> MacroAddress {
        self.macro_address
    }
    pub fn arg_expr_range(&self) -> ExprRange {
        self.arg_expr_range
    }
}

impl TemplateBodyValueExpr {
    /// Returns `Ok(&element)` if this expression is an annotated value. Otherwise, returns
    /// `Err(IonError)`.
    pub fn expect_element(&self) -> IonResult<&TemplateBodyElement> {
        match self {
            TemplateBodyValueExpr::Element(e) => Ok(e),
            TemplateBodyValueExpr::Variable(variable_reference) => {
                let index = variable_reference.signature_index();
                IonResult::decoding_error(format!(
                    "expected an element, found reference variable with signature index '{index}'"
                ))
            }
            TemplateBodyValueExpr::MacroInvocation(invocation) => {
                let address = invocation.macro_address();
                IonResult::decoding_error(format!(
                    "expected an element, found macro at address {address}"
                ))
            }
        }
    }
}

impl<'data, D: LazyDecoder<'data>> ToArgumentKind<'data, D, TemplateMacroInvocationAddress>
    for TemplateMacroArgExpr
{
    fn to_arg_expr<'top>(
        self,
        context: EncodingContext<'top>,
    ) -> ArgumentKind<'top, 'data, D, TemplateMacroInvocationAddress>
    where
        TemplateBodyValueExpr: 'top,
        Self: 'top,
    {
        let Some(macro_ref) = &context
            .macro_table
            .macro_at_address(self.host_template_address)
        else {
            unreachable!(
                "template address {} was not valid",
                self.host_template_address
            );
        };

        let MacroKind::Template(template) = macro_ref.kind() else {
            unreachable!(
                "macro at address {} was not a template: {:?}",
                self.host_template_address,
                macro_ref.kind()
            );
        };

        let template_ref = TemplateMacroRef::new(macro_ref.address(), template);

        let invocation_expr = template
            .body()
            .expressions()
            .get(self.value_expr_address)
            .unwrap();
        match invocation_expr {
            TemplateBodyValueExpr::Element(element) => {
                let template_element = TemplateElement::new(template_ref, element);
                ArgumentKind::ValueLiteral(LazyExpandedValue::from_template(
                    context,
                    template_element,
                ))
            }
            TemplateBodyValueExpr::Variable(_variable) => {
                todo!("variable expansion")
            }
            TemplateBodyValueExpr::MacroInvocation(invocation) => {
                ArgumentKind::MacroInvocation(TemplateMacroInvocationAddress {
                    host_template_address: template_ref.address(),
                    invoked_macro_address: invocation.macro_address,
                    invocation_expression_address: self.value_expr_address,
                    num_arguments: invocation.arg_expr_range.len(),
                })
            }
        }
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TemplateMacroInvocationAddress {
    // The template where the invocation appeared
    host_template_address: MacroAddress,
    // The address of the macro being invoked
    invoked_macro_address: MacroAddress,
    // The address (Vec index) of the TemplateValueExpr::MacroInvocation, which enables an
    // arguments iterator to visit each argument expression in the template.
    invocation_expression_address: TemplateBodyExprAddress,
    num_arguments: usize,
}

impl TemplateMacroInvocationAddress {
    pub fn new(
        host_template_address: MacroAddress,
        invoked_macro_address: MacroAddress,
        invocation_expression_address: TemplateBodyExprAddress,
        num_arguments: usize,
    ) -> Self {
        Self {
            host_template_address,
            invoked_macro_address,
            invocation_expression_address,
            num_arguments,
        }
    }
    pub fn host_template_address(&self) -> MacroAddress {
        self.host_template_address
    }
    pub fn invocation_expression_address(&self) -> usize {
        self.invocation_expression_address
    }

    pub fn arguments(&self) -> TemplateMacroInvocationArgsIterator {
        TemplateMacroInvocationArgsIterator::new(*self)
    }
}

/// A macro invocation in a template body.
#[derive(Debug, Copy, Clone)]
pub struct TemplateMacroInvocation<'top> {
    // The address of the template in which this macro invocation appears
    host_template_address: MacroAddress,
    // The definition of the template in which this macro invocation appears
    host_template: &'top TemplateMacro,
    // The address of the the macro invocation expression within the host template's body
    invocation_expression_address: TemplateBodyExprAddress,
    // The address of the macro being invoked
    invoked_macro_address: MacroAddress,
    // The range of value expressions in the host template's body that are arguments to the
    // macro being invoked
    arg_expressions: &'top [TemplateBodyValueExpr],
}

impl<'top> TemplateMacroInvocation<'top> {
    pub fn new(
        host_template_address: MacroAddress,
        host_template: &'top TemplateMacro,
        invocation_expression_address: TemplateBodyExprAddress,
        invoked_macro_address: MacroAddress,
        arg_expressions: &'top [TemplateBodyValueExpr],
    ) -> Self {
        Self {
            host_template_address,
            host_template,
            invocation_expression_address,
            invoked_macro_address,
            arg_expressions,
        }
    }
    pub fn invocation_address(&self) -> TemplateMacroInvocationAddress {
        TemplateMacroInvocationAddress {
            host_template_address: self.host_template_address,
            invoked_macro_address: self.invoked_macro_address,
            invocation_expression_address: 0,
            num_arguments: self.arg_expressions.len(),
        }
    }

    pub fn macro_address(&self) -> MacroAddress {
        self.invoked_macro_address
    }
    pub fn args(&self) -> TemplateMacroInvocationArgsIterator {
        TemplateMacroInvocationArgsIterator::new(self.invocation_address())
    }

    pub fn template(&self) -> &'top TemplateMacro {
        self.host_template
    }
    pub fn arg_expressions(&self) -> &'top [TemplateBodyValueExpr] {
        self.arg_expressions
    }
}

// TODO: note about why this can't hold a 'top lifetime
pub struct TemplateMacroInvocationArgsIterator {
    invocation_address: TemplateMacroInvocationAddress,
    arg_index: usize,
}

impl TemplateMacroInvocationArgsIterator {
    pub fn new(invocation_address: TemplateMacroInvocationAddress) -> Self {
        Self {
            invocation_address,
            arg_index: 0,
        }
    }
}

impl Iterator for TemplateMacroInvocationArgsIterator {
    type Item = IonResult<TemplateMacroArgExpr>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.arg_index >= self.invocation_address.num_arguments {
            return None;
        }
        let arg_expr = TemplateMacroArgExpr::new(
            self.invocation_address.host_template_address(),
            self.arg_index,
        );
        self.arg_index += 1;
        Some(Ok(arg_expr))
    }
}

// TODO: Explain why this is on the address and not the resolved invocation
impl<'data, D: LazyDecoder<'data>> MacroInvocation<'data, D> for TemplateMacroInvocationAddress {
    type ArgumentExpr = TemplateMacroArgExpr;
    type ArgumentsIterator = TemplateMacroInvocationArgsIterator;
    type TransientEvaluator<'context> = TemplateEvaluator<'context, 'data, D> where Self: 'context, 'data: 'context;

    fn id(&self) -> MacroIdRef {
        MacroIdRef::LocalAddress(self.invoked_macro_address)
    }

    fn arguments(&self) -> Self::ArgumentsIterator {
        self.arguments()
    }

    fn make_transient_evaluator<'context>(
        context: EncodingContext<'context>,
    ) -> Self::TransientEvaluator<'context>
    where
        'data: 'context,
        Self: 'context,
    {
        Self::TransientEvaluator::new(context)
    }
}

/// A reference to a variable in a template body.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct TemplateBodyVariableReference {
    signature_index: usize,
}

impl TemplateBodyVariableReference {
    pub fn new(signature_index: usize) -> Self {
        Self { signature_index }
    }
    pub fn signature_index(&self) -> usize {
        self.signature_index
    }
}

#[derive(Clone, Copy, Debug)]
pub struct TemplateElement<'top> {
    template: TemplateMacroRef<'top>,
    element: &'top TemplateBodyElement,
}

impl<'top> TemplateElement<'top> {
    pub fn new(template: TemplateMacroRef<'top>, element: &'top TemplateBodyElement) -> Self {
        Self { template, element }
    }
    pub fn annotations(&self) -> &'top [Symbol] {
        self.template
            .body()
            .annotations_storage()
            .get(self.element.annotations_range().ops_range())
            .unwrap()
    }

    pub fn annotations_range(&self) -> AnnotationsRange {
        self.element.annotations_range
    }

    pub fn value(&self) -> &'top TemplateValue {
        &self.element.value
    }
    pub fn template(&self) -> TemplateMacroRef<'top> {
        self.template
    }
}

/// An annotated value in a template body.
#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBodyElement {
    // To minimize allocations, all annotations live in a single `Vec` in the `TemplateBody`.
    // Each element holds a range pointing to its annotation sequence.
    pub(crate) annotations_range: AnnotationsRange,
    pub(crate) value: TemplateValue,
}

impl TemplateBodyElement {
    pub fn with_value(value: TemplateValue) -> Self {
        Self {
            annotations_range: AnnotationsRange::empty(),
            value,
        }
    }
    pub fn with_annotations(mut self, range: Range<usize>) -> Self {
        self.annotations_range = AnnotationsRange::new(range);
        self
    }

    pub fn value(&self) -> &TemplateValue {
        &self.value
    }
    pub fn annotations_range(&self) -> AnnotationsRange {
        self.annotations_range
    }

    pub fn annotations<'a>(&self, template: &'a TemplateMacro) -> &'a [Symbol] {
        template
            .body()
            .annotations_storage()
            .get(self.annotations_range().ops_range())
            // If the annotations range is invalid, that's a bug; we cannot return an error.
            .unwrap()
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TemplateValue {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    Symbol(Symbol),
    String(Str),
    Clob(Bytes),
    Blob(Bytes),
    // The number of ensuing TemplateElements that are nested.
    List(ExprRange),
    SExp(ExprRange),
    // The number of fields in the struct. Each field is made up of a pair of TemplateExpansionSteps,
    // a name (always a symbol, never has annotations), and a value (any element).
    Struct(ExprRange),
}

impl TemplateValue {
    pub fn is_null(&self) -> bool {
        matches!(self, TemplateValue::Null(_))
    }

    pub fn ion_type(&self) -> IonType {
        // TODO: Implement this with a Rust macro instead.
        //       See: https://github.com/amazon-ion/ion-rust/issues/650
        use TemplateValue::*;
        match self {
            Null(ion_type) => *ion_type,
            Bool(_) => IonType::Bool,
            Int(_) => IonType::Int,
            Float(_) => IonType::Float,
            Decimal(_) => IonType::Decimal,
            Timestamp(_) => IonType::Timestamp,
            Symbol(_) => IonType::Symbol,
            String(_) => IonType::String,
            Clob(_) => IonType::Clob,
            Blob(_) => IonType::Blob,
            List(_) => IonType::List,
            SExp(_) => IonType::SExp,
            Struct(_) => IonType::Struct,
        }
    }
}

/// A slice of a `TemplateBody`'s sequence of `TemplateExpansionStep`. This type can be used to
/// represent containers (list, sexp, struct) or macro invocations, all of which use an evaluator
/// to iteratively evaluate a series of `TemplateExpansionStep`s. This type does not hold a reference
/// to the template definition itself.
pub type ExprRange = SmallRange;
pub type AnnotationsRange = SmallRange;

/// A range that takes 8 bytes instead of Range<usize>'s 16. This is useful for cases like
/// annotations where a capacity of 4 billion+ is more than enough. It also implements `Copy`,
/// making it possible for enclosing types to also implement `Copy`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct SmallRange {
    start: u32,
    end: u32,
}

impl SmallRange {
    pub fn empty() -> Self {
        Self { start: 0, end: 0 }
    }

    pub fn new(range: Range<usize>) -> Self {
        debug_assert!(u32::try_from(range.start).is_ok());
        debug_assert!(u32::try_from(range.end).is_ok());
        Self {
            start: range.start as u32,
            end: range.end as u32,
        }
    }

    pub fn ops_range(&self) -> Range<usize> {
        self.start as usize..self.end as usize
    }

    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
