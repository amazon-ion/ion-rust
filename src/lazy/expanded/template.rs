use std::fmt;
use std::fmt::{Debug, Formatter};
use std::marker::PhantomData;
use std::ops::{Deref, Range};

use crate::lazy::decoder::{LazyDecoder, RawFieldExpr, RawValueExpr};
use crate::lazy::expanded::macro_evaluator::{
    ArgumentExpr, MacroEvaluator, MacroExpr, MacroInvocation,
};
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::sequence::Environment;
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

#[derive(Clone)]
pub struct TemplateMacro {
    // TODO: Make the name optional
    pub(crate) name: Symbol,
    pub(crate) signature: MacroSignature,
    pub(crate) body: TemplateBody,
}

impl Debug for TemplateMacro {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.fmt_template(f)
    }
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

    pub(crate) fn fmt_template(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Template {}", self.name())?;
        for param in self.signature().parameters() {
            writeln!(f, "  {param:?}")?;
        }
        writeln!(f, "  body:")?;
        let indentation = &mut String::from("    ");
        let mut index = 0usize;
        while let Some(expr) = self.body().expressions().get(index) {
            index += TemplateBodyValueExpr::fmt_expr(f, indentation, expr, self)?;
        }

        Ok(())
    }
}

#[derive(Copy, Clone, Debug)]
pub struct TemplateMacroRef<'top> {
    address: MacroAddress,
    template: &'top TemplateMacro,
}

impl<'top> TemplateMacroRef<'top> {
    pub fn new(address: MacroAddress, template: &'top TemplateMacro) -> Self {
        Self { address, template }
    }
    pub fn address(&self) -> MacroAddress {
        self.address
    }
}

impl<'top> Deref for TemplateMacroRef<'top> {
    type Target = &'top TemplateMacro;

    fn deref(&self) -> &Self::Target {
        &self.template
    }
}

pub struct TemplateSequenceIterator<'top, 'data, D: LazyDecoder<'data>> {
    context: EncodingContext<'top>,
    template: TemplateMacroRef<'top>,
    evaluator: MacroEvaluator<'top, 'data, D>,
    value_expressions: &'top [TemplateBodyValueExpr],
    index: usize,
}

impl<'top, 'data, D: LazyDecoder<'data>> TemplateSequenceIterator<'top, 'data, D> {
    pub fn new(
        context: EncodingContext<'top>,
        evaluator: MacroEvaluator<'top, 'data, D>,
        template: TemplateMacroRef<'top>,
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
            if self.evaluator.macro_stack_depth() > 0 {
                match self.evaluator.next(self.context, 0).transpose() {
                    Some(value) => return Some(value),
                    None => {
                        // The stack did not produce values and is empty, pull
                        // the next expression from `self.value_expressions`
                    }
                }
            }
            // We didn't get a value from the evaluator, so pull the next expansion step.
            let step = self.value_expressions.get(self.index)?;
            self.index += 1;
            return match step {
                TemplateBodyValueExpr::Element(element) => {
                    let value = LazyExpandedValue {
                        context: self.context,
                        source: ExpandedValueSource::Template(
                            self.evaluator.environment(),
                            TemplateElement::new(self.template, element),
                        ),
                    };
                    println!("yield {value:?} from list");
                    Some(Ok(value))
                }
                TemplateBodyValueExpr::MacroInvocation(body_invocation) => {
                    // ...it's a TDL macro invocation. Push it onto the evaluator's stack and return
                    // to the top of the loop.
                    let invoked_macro = self
                        .context
                        .macro_table
                        .macro_at_address(body_invocation.invoked_macro_address)
                        .unwrap();
                    let invocation = TemplateMacroInvocation::new(
                        self.context,
                        self.template,
                        invoked_macro,
                        self.template
                            .body
                            .expressions()
                            .get(body_invocation.arg_expr_range().ops_range())
                            .unwrap(),
                    );
                    self.index += invocation.arg_expressions.len();
                    match self.evaluator.push(self.context, invocation) {
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
    environment: Environment<'top, 'data, D>,
    template: TemplateMacroRef<'top>,
    expressions: &'top [TemplateBodyValueExpr],
    index: usize,
    spooky: PhantomData<&'data D>,
}

impl<'top, 'data, D: LazyDecoder<'data>> TemplateStructRawFieldsIterator<'top, 'data, D> {
    pub fn new(
        context: EncodingContext<'top>,
        environment: Environment<'top, 'data, D>,
        template: TemplateMacroRef<'top>,
        expressions: &'top [TemplateBodyValueExpr],
    ) -> Self {
        Self {
            context,
            environment,
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
    type Item = IonResult<
        RawFieldExpr<'top, ExpandedValueSource<'top, 'data, D>, MacroExpr<'top, 'data, D>>,
    >;

    fn next(&mut self) -> Option<Self::Item> {
        let name_expr_address = self.index;
        let name_element = self
            .expressions
            .get(name_expr_address)?
            .expect_element()
            .expect("field name must be a literal");
        let name_token = match LazyExpandedValue::<D>::from_template(
            self.context,
            Environment::empty(),
            TemplateElement::new(self.template, name_element),
        )
        // because the name token must be a literal, the env is irrelevant
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
        let value_source = match self.expressions.get(value_expr_address) {
            None => {
                return Some(IonResult::decoding_error(
                    "template struct had field name with no value",
                ))
            }
            Some(TemplateBodyValueExpr::Element(element)) => {
                match element.value() {
                    TemplateValue::List(range)
                    | TemplateValue::SExp(range)
                    | TemplateValue::Struct(range) => self.index += range.len(),
                    _ => {}
                };
                RawValueExpr::ValueLiteral(ExpandedValueSource::Template(
                    self.environment,
                    TemplateElement::new(self.template, element),
                ))
            }
            Some(TemplateBodyValueExpr::MacroInvocation(body_invocation)) => {
                let invoked_macro = self
                    .context
                    .macro_table
                    .macro_at_address(body_invocation.invoked_macro_address)
                    .unwrap();
                let invocation = TemplateMacroInvocation::new(
                    self.context,
                    self.template,
                    invoked_macro,
                    self.template
                        .body
                        .expressions()
                        .get(body_invocation.arg_expr_range().ops_range())
                        .unwrap(),
                );
                self.index += invocation.arg_expressions.len();
                RawValueExpr::MacroInvocation(MacroExpr::TemplateMacro(invocation))
            }
            Some(TemplateBodyValueExpr::Variable(_)) => {
                todo!("variable expansion in template structs")
            }
        };
        self.index += 2;
        Some(Ok(RawFieldExpr::NameValuePair(name_token, value_source)))
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

    pub fn push_macro_invocation(&mut self, invoked_macro_address: usize, expr_range: ExprRange) {
        let expression_address = self.expressions.len();
        self.expressions
            .push(TemplateBodyValueExpr::MacroInvocation(
                TemplateBodyMacroInvocation::new(
                    expression_address,
                    invoked_macro_address,
                    expr_range,
                ),
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

impl TemplateBodyValueExpr {
    pub(crate) fn fmt_expr(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        expr: &TemplateBodyValueExpr,
        host_template: &TemplateMacro,
    ) -> Result<usize, fmt::Error> {
        match &expr {
            TemplateBodyValueExpr::Element(e) => {
                // TODO: Annotations
                writeln!(f, "{}{:?}", indentation, e.value)?;
                Ok(1)
            }
            TemplateBodyValueExpr::Variable(v) => {
                writeln!(f, "{}{:?}", indentation, v)?;
                Ok(1)
            }
            TemplateBodyValueExpr::MacroInvocation(m) => {
                Self::fmt_invocation(f, indentation, host_template, m)
            }
        }
    }

    pub(crate) fn fmt_invocation(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        invocation: &TemplateBodyMacroInvocation,
    ) -> Result<usize, fmt::Error> {
        writeln!(
            f,
            "{}invoke address {}",
            indentation, invocation.invoked_macro_address
        )?;
        let args = host_template
            .body
            .expressions
            .get(invocation.arg_expr_range.ops_range())
            .unwrap();

        indentation.push_str("    ");
        let mut expr_index: usize = 0;
        while let Some(arg) = args.get(expr_index) {
            expr_index += Self::fmt_expr(f, indentation, arg, host_template)?;
        }
        indentation.truncate(indentation.len() - 4);
        Ok(1 + args.len())
    }
}

#[derive(Debug, Clone, Copy)]
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

#[derive(Debug, Copy, Clone)]
pub struct RawTemplateMacroInvocationArg {
    host_template_address: MacroAddress,
    template_body_expr_address: TemplateBodyExprAddress,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct TemplateBodyMacroInvocation {
    invocation_expr_address: TemplateBodyExprAddress,
    invoked_macro_address: MacroAddress,
    arg_expr_range: ExprRange,
}

impl TemplateBodyMacroInvocation {
    pub fn new(
        invocation_expr_address: TemplateBodyExprAddress,
        invoked_macro_address: MacroAddress,
        arg_expr_range: ExprRange,
    ) -> Self {
        Self {
            invocation_expr_address,
            invoked_macro_address,
            arg_expr_range,
        }
    }
    pub fn macro_address(&self) -> MacroAddress {
        self.invoked_macro_address
    }
    pub fn arg_expr_range(&self) -> ExprRange {
        self.arg_expr_range
    }
    pub fn invocation_expr_address(&self) -> TemplateBodyExprAddress {
        self.invocation_expr_address
    }

    pub fn resolve<'top>(
        self,
        host_template: TemplateMacroRef<'top>,
        context: EncodingContext<'top>,
    ) -> IonResult<TemplateMacroInvocation<'top>> {
        let invoked_macro = context
            .macro_table
            .macro_at_address(self.invoked_macro_address)
            .unwrap();

        let arg_expressions = host_template
            .body
            .expressions()
            .get(self.arg_expr_range.ops_range())
            .unwrap();

        Ok(TemplateMacroInvocation {
            context,
            host_template,
            invoked_macro,
            arg_expressions,
        })
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

/// A macro invocation in a template body.
#[derive(Copy, Clone)]
pub struct TemplateMacroInvocation<'top> {
    context: EncodingContext<'top>,
    // The definition of the template in which this macro invocation appears
    host_template: TemplateMacroRef<'top>,
    // The address of the macro being invoked
    invoked_macro: MacroRef<'top>,
    // The range of value expressions in the host template's body that are arguments to the
    // macro being invoked
    arg_expressions: &'top [TemplateBodyValueExpr],
}

impl<'top> Debug for TemplateMacroInvocation<'top> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "TemplateMacroInvocation <target macro address={}>",
            self.invoked_macro.address()
        )
    }
}

impl<'top> TemplateMacroInvocation<'top> {
    pub fn new(
        context: EncodingContext<'top>,
        host_template: TemplateMacroRef<'top>,
        invoked_macro: MacroRef<'top>,
        arg_expressions: &'top [TemplateBodyValueExpr],
    ) -> Self {
        Self {
            context,
            host_template,
            invoked_macro,
            arg_expressions,
        }
    }
    pub fn arguments<'data, D: LazyDecoder<'data>>(
        &self,
        environment: Environment<'top, 'data, D>,
    ) -> TemplateMacroInvocationArgsIterator<'top, 'data, D> {
        TemplateMacroInvocationArgsIterator::new(environment, *self)
    }
    pub fn template(&self) -> TemplateMacroRef<'top> {
        self.host_template
    }
    pub fn arg_expressions(&self) -> &'top [TemplateBodyValueExpr] {
        self.arg_expressions
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> From<TemplateMacroInvocation<'top>>
    for MacroExpr<'top, 'data, D>
{
    fn from(value: TemplateMacroInvocation<'top>) -> Self {
        MacroExpr::TemplateMacro(value)
    }
}

// TODO: This should hold an Environment<'top, 'data, D> instead of holding a PhantomData
pub struct TemplateMacroInvocationArgsIterator<'top, 'data, D: LazyDecoder<'data>> {
    environment: Environment<'top, 'data, D>,
    invocation: TemplateMacroInvocation<'top>,
    arg_index: usize,
}

impl<'top, 'data, D: LazyDecoder<'data>> TemplateMacroInvocationArgsIterator<'top, 'data, D> {
    pub fn new(
        environment: Environment<'top, 'data, D>,
        invocation: TemplateMacroInvocation<'top>,
    ) -> Self {
        Self {
            environment,
            invocation,
            arg_index: 0,
        }
    }
}

impl<'top, 'data, D: LazyDecoder<'data>> Iterator
    for TemplateMacroInvocationArgsIterator<'top, 'data, D>
{
    type Item = IonResult<ArgumentExpr<'top, 'data, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let arg = self.invocation.arg_expressions().get(self.arg_index)?;
        self.arg_index += 1;
        let arg_expr = match arg {
            TemplateBodyValueExpr::Element(e) => {
                // If it's a container, skip over its contents when this iterator resumes
                match e.value() {
                    TemplateValue::List(range)
                    | TemplateValue::SExp(range)
                    | TemplateValue::Struct(range) => {
                        self.arg_index += range.len();
                    }
                    _ => {}
                };
                ArgumentExpr::ValueLiteral(LazyExpandedValue::from_template(
                    self.invocation.context,
                    self.environment,
                    TemplateElement::new(self.invocation.template(), e),
                ))
            }
            TemplateBodyValueExpr::Variable(_v) => {
                todo!("variable expansion")
            }
            TemplateBodyValueExpr::MacroInvocation(body_invocation) => {
                let invocation = match body_invocation
                    .resolve(self.invocation.template(), self.invocation.context)
                {
                    Ok(invocation) => {
                        // Skip over all of the expressions that belong to this invocation.
                        self.arg_index += invocation.arg_expressions.len();
                        invocation
                    }
                    Err(e) => return Some(Err(e)),
                };
                ArgumentExpr::MacroInvocation(invocation.into())
            }
        };

        Some(Ok(arg_expr))
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroInvocation<'top, 'data, D>
    for TemplateMacroInvocation<'top>
{
    type ArgumentsIterator = TemplateMacroInvocationArgsIterator<'top, 'data, D>;

    fn id(&self) -> MacroIdRef<'data> {
        MacroIdRef::LocalAddress(self.invoked_macro.address())
    }

    fn arguments(&self, environment: Environment<'top, 'data, D>) -> Self::ArgumentsIterator {
        // Delegate to the inherent impl on TemplateMacroInvocation
        self.arguments(environment)
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
