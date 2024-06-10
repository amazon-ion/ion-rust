use std::collections::HashMap;
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, Range};

use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, MacroExpr, ValueExpr};
use crate::lazy::expanded::macro_table::MacroRef;
use crate::lazy::expanded::r#struct::UnexpandedField;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedValueSource, LazyExpandedValue, TemplateVariableReference,
};
use crate::lazy::text::raw::v1_1::reader::{MacroAddress, MacroIdRef};
use crate::result::IonFailure;
use crate::{Bytes, Decimal, Int, IonResult, IonType, Str, Symbol, SymbolRef, Timestamp, Value};

/// A parameter in a user-defined macro's signature.
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
    pub fn encoding(&self) -> &ParameterEncoding {
        &self.encoding
    }
}

/// The encoding used to serialize and deserialize the associated parameter.
#[derive(Debug, Clone)]
pub enum ParameterEncoding {
    /// A 'tagged' type is one whose binary encoding begins with an opcode (sometimes called a 'tag'.)
    Tagged,
    // TODO: tagless types, including fixed-width types and macros
}

/// The sequence of parameters for which callers must pass expressions when invoking the macro.
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

/// A user-defined macro which expands the parameters in the signature into a series of Ion values
/// according to a template.
///
/// Macros can be made anonymous by passing `null` in the definition's name position.
/// ```ion_1_1
///     (macro null (x y z) [x, y, z])
/// ```
/// This simplifies the use of machine-authored macros, which are always invoked by their address
/// in the macro table rather than by a human-friendly name.
#[derive(Clone)]
pub struct TemplateMacro {
    pub(crate) name: Option<String>,
    pub(crate) signature: MacroSignature,
    pub(crate) body: TemplateBody,
}

impl Debug for TemplateMacro {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "Template {}", self.name())?;
        writeln!(f, "    signature:")?;
        // Writes each parameter in the signature on its own indented line
        for param in self.signature().parameters() {
            let name = param.name();
            let encoding = param.encoding();
            writeln!(f, "        {name} ({encoding:?})")?;
        }
        writeln!(f, "    body:")?;
        let indentation = &mut String::from("        ");
        let mut index = 0usize;
        while let Some(expr) = self.body().expressions().get(index) {
            index += TemplateBodyValueExpr::fmt_expr(f, indentation, self, expr)?;
        }

        Ok(())
    }
}

impl TemplateMacro {
    pub fn name(&self) -> &str {
        self.name.as_deref().unwrap_or("<anonymous>")
    }
    pub fn signature(&self) -> &MacroSignature {
        &self.signature
    }
    pub fn body(&self) -> &TemplateBody {
        &self.body
    }
}

/// A reference to a template macro definition paired with the macro table address at which it was found.
#[derive(Copy, Clone, Debug)]
pub struct TemplateMacroRef<'top> {
    // This field is only stored as a source of information for debugging. (For example, when showing
    // a macro evaluator stack trace.)
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

/// Steps over the child expressions of a list or s-expression found in the body of a template.
pub struct TemplateSequenceIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    template: TemplateMacroRef<'top>,
    evaluator: MacroEvaluator<'top, D>,
    value_expressions: &'top [TemplateBodyValueExpr],
    index: usize,
}

impl<'top, D: Decoder> TemplateSequenceIterator<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        evaluator: MacroEvaluator<'top, D>,
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

impl<'top, D: Decoder> Iterator for TemplateSequenceIterator<'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // If the evaluator's stack is not empty, give it the opportunity to yield a value.
            if self.evaluator.macro_stack_depth() > 0 {
                match self.evaluator.next().transpose() {
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
                        variable: None,
                    };
                    Some(Ok(value))
                }
                TemplateBodyValueExpr::MacroInvocation(body_invocation) => {
                    // ...it's a TDL macro invocation. Push it onto the evaluator's stack and return
                    // to the top of the loop.
                    let invoked_macro = self
                        .context
                        .macro_table()
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
                    match self.evaluator.push(invocation) {
                        Ok(_) => continue,
                        Err(e) => Some(Err(e)),
                    }
                }
                TemplateBodyValueExpr::Variable(variable_ref) => {
                    let arg_expr = self
                        .evaluator
                        .environment()
                        .expressions()
                        .get(variable_ref.signature_index())
                        .unwrap();
                    match arg_expr {
                        ValueExpr::ValueLiteral(value) => Some(Ok(*value)),
                        ValueExpr::MacroInvocation(invocation) => {
                            match self.evaluator.push(*invocation) {
                                Ok(_) => continue,
                                Err(e) => Some(Err(e)),
                            }
                        }
                    }
                }
            };
        }
    }
}

/// An iterator that pulls expressions from a template body and wraps them in a [`UnexpandedField`] to
/// mimic reading them from input. The [`LazyExpandedStruct`](crate::lazy::expanded::struct) handles
/// evaluating any macro invocations that this yields.
pub struct TemplateStructUnexpandedFieldsIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    environment: Environment<'top, D>,
    template: TemplateMacroRef<'top>,
    expressions: &'top [TemplateBodyValueExpr],
    index: usize,
}

impl<'top, D: Decoder> TemplateStructUnexpandedFieldsIterator<'top, D> {
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
}

impl<'top, D: Decoder> TemplateStructUnexpandedFieldsIterator<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        environment: Environment<'top, D>,
        template: TemplateMacroRef<'top>,
        expressions: &'top [TemplateBodyValueExpr],
    ) -> Self {
        Self {
            context,
            environment,
            template,
            expressions,
            index: 0,
        }
    }
}

impl<'top, D: Decoder> Iterator for TemplateStructUnexpandedFieldsIterator<'top, D> {
    type Item = IonResult<UnexpandedField<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let name_expr_address = self.index;
        let name_element = self
            .expressions
            .get(name_expr_address)?
            .expect_element()
            .expect("field name must be a literal");
        let name: SymbolRef = match &name_element.value {
            TemplateValue::Symbol(s) => s.into(),
            TemplateValue::String(s) => s.text().into(),
            _ => unreachable!("template struct field had a non-text field name"),
        };
        let value_expr_address = name_expr_address + 1;
        let value_expr = self
            .expressions
            .get(value_expr_address)
            .expect("template struct had field name with no value");
        let unexpanded_field = match value_expr {
            TemplateBodyValueExpr::Element(element) => {
                match element.value() {
                    TemplateValue::List(range)
                    | TemplateValue::SExp(range)
                    | TemplateValue::Struct(range, _) => self.index += range.len(),
                    _ => {
                        // Otherwise, the value is a scalar and is exactly one expression. We already
                        // accounted for the first expression, so there's nothing else to do here.
                    }
                };
                UnexpandedField::TemplateNameValue(
                    name,
                    TemplateElement::new(self.template, element),
                )
            }
            TemplateBodyValueExpr::MacroInvocation(body_invocation) => {
                let invoked_macro = self
                    .context
                    .macro_table()
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
                UnexpandedField::TemplateNameMacro(name, invocation)
            }
            TemplateBodyValueExpr::Variable(variable) => {
                let arg_expr = self
                    .environment
                    .get_expected(variable.signature_index())
                    .expect("reference to non-existent parameter");
                let variable_ref = variable.resolve(self.template);
                UnexpandedField::TemplateNameVariable(name, (variable_ref, arg_expr))
            }
        };
        self.index += 2;
        Some(Ok(unexpanded_field))
    }
}

/// Stores a sequence of expansion steps that need to be evaluated in turn.
///
/// See [`TemplateBodyValueExpr`] for details.
#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBody {
    pub(crate) expressions: Vec<TemplateBodyValueExpr>,
    // All of the elements stored in the Vec above share the Vec below for storing their annotations.
    // This allows us to avoid allocating a `Vec<Symbol>` for every value in the template, saving
    // a small amount of time and memory during compilation. Each values hold an index range
    // into this `Vec`.
    pub(crate) annotations_storage: Vec<Symbol>,
}

impl TemplateBody {
    pub fn expressions(&self) -> &[TemplateBodyValueExpr] {
        &self.expressions
    }
    pub fn annotations_storage(&self) -> &[Symbol] {
        &self.annotations_storage
    }

    pub fn push_element(&mut self, element: TemplateBodyElement) {
        self.expressions
            .push(TemplateBodyValueExpr::Element(element))
    }

    pub fn push_variable(&mut self, signature_index: u16) {
        self.expressions.push(TemplateBodyValueExpr::Variable(
            TemplateBodyVariableReference::new(signature_index),
        ))
    }

    pub fn push_macro_invocation(&mut self, invoked_macro_address: usize, expr_range: ExprRange) {
        self.expressions
            .push(TemplateBodyValueExpr::MacroInvocation(
                TemplateBodyMacroInvocation::new(invoked_macro_address, expr_range),
            ))
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

    /// This helper method is invoked by the `Debug` implementation of `TemplateMacro`, which provides
    /// a neatly indented, recursive printout of the compiled form of a template definition.
    ///
    /// `TemplateBodyValueExpr` also provides its own "shallow" implementation of `Debug` that simply
    /// prints the contents of each field in the data of its variant.
    pub(crate) fn fmt_expr(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        expr: &TemplateBodyValueExpr,
    ) -> Result<usize, fmt::Error> {
        match &expr {
            TemplateBodyValueExpr::Element(e) => {
                Self::fmt_element(f, indentation, host_template, e)
            }
            TemplateBodyValueExpr::Variable(v) => {
                Self::fmt_variable(f, indentation, host_template, v)
            }
            TemplateBodyValueExpr::MacroInvocation(m) => {
                Self::fmt_invocation(f, indentation, host_template, m)
            }
        }
    }

    /// A helper method to recursively print the 'compiled' form of a `TemplateBodyValueExpr::Element(_)`.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_element(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        element: &TemplateBodyElement,
    ) -> Result<usize, fmt::Error> {
        let annotations_range = element.annotations_range.ops_range();
        let annotations = host_template
            .body()
            .annotations_storage()
            .get(annotations_range)
            .unwrap();
        write!(f, "{indentation}")?;
        for annotation in annotations {
            write!(f, "{}::", annotation.text().unwrap_or("$0"))?;
        }
        use TemplateValue::*;
        match element.value() {
            List(l) => {
                writeln!(f, "list")?;
                return Self::fmt_sequence_body(f, indentation, host_template, *l);
            }
            SExp(s) => {
                writeln!(f, "sexp")?;
                return Self::fmt_sequence_body(f, indentation, host_template, *s);
            }
            Struct(s, _) => {
                writeln!(f, "struct")?;
                return Self::fmt_struct(f, indentation, host_template, *s);
            }
            Null(n) => writeln!(f, "{}", Value::Null(*n)),
            Bool(b) => writeln!(f, "{b}"),
            Int(i) => writeln!(f, "{i}"),
            Float(float) => writeln!(f, "{}", *float),
            Decimal(d) => writeln!(f, "{d}"),
            Timestamp(t) => writeln!(f, "{t}"),
            String(s) => writeln!(f, "{s}"),
            Symbol(s) => writeln!(f, "{s}"),
            Blob(b) => writeln!(f, "blob {:x?}", &b.as_ref()[..16]),
            Clob(c) => writeln!(f, "clob {:x?}", &c.as_ref()[..16]),
        }?;
        Ok(1)
    }

    /// A helper method to recursively print the 'compiled' form of lists, s-expressions, and
    /// macro invocation argument sequences.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_sequence_body(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        expr_range: ExprRange,
    ) -> Result<usize, fmt::Error> {
        let range = expr_range.ops_range();
        let expressions = host_template.body().expressions().get(range).unwrap();
        indentation.push_str("    ");
        let mut expr_index: usize = 0;
        while expr_index < expressions.len() {
            let expr = &expressions[expr_index];
            expr_index += Self::fmt_expr(f, indentation, host_template, expr)?;
        }
        indentation.truncate(indentation.len() - 4);
        Ok(1 + expressions.len())
    }

    /// A helper method to recursively print the 'compiled' form of a struct.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_struct(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        expr_range: ExprRange,
    ) -> Result<usize, fmt::Error> {
        let range = expr_range.ops_range();
        let expressions = host_template.body().expressions().get(range).unwrap();
        indentation.push_str("    ");
        let mut expr_index: usize = 0;
        while expr_index < expressions.len() {
            let TemplateBodyValueExpr::Element(name_element) = &expressions[expr_index] else {
                unreachable!(
                    "non-element field name in template struct: {:?}",
                    &expressions[expr_index]
                )
            };
            let name = match name_element.value() {
                TemplateValue::String(s) => s.text(),
                TemplateValue::Symbol(s) => s.text().unwrap_or("$0"),
                unexpected => unreachable!(
                    "non-string, non-symbol field name in template struct: {:?}",
                    unexpected
                ),
            };
            let value = &expressions[expr_index + 1];
            writeln!(f, "{indentation}'{name}':")?;
            indentation.push_str("    ");
            expr_index += 1 + Self::fmt_expr(f, indentation, host_template, value)?;
            indentation.truncate(indentation.len() - 4);
        }
        indentation.truncate(indentation.len() - 4);
        Ok(1 + expressions.len())
    }

    /// A helper method to recursively print the 'compiled' form of a macro invocation within a template.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_invocation(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        invocation: &TemplateBodyMacroInvocation,
    ) -> Result<usize, fmt::Error> {
        writeln!(
            f,
            "{indentation}<invoke macro @ address {}>",
            invocation.invoked_macro_address
        )?;
        let args = host_template
            .body
            .expressions
            .get(invocation.arg_expr_range.ops_range())
            .unwrap();

        indentation.push_str("    ");
        let mut expr_index: usize = 0;
        while let Some(arg) = args.get(expr_index) {
            expr_index += Self::fmt_expr(f, indentation, host_template, arg)?;
        }
        indentation.truncate(indentation.len() - 4);
        Ok(1 + args.len())
    }

    /// A helper method to recursively print the 'compiled' form of a variable reference in the
    /// body of a template.
    ///
    /// This method is transitively invoked by [`TemplateMacro`]'s `Debug` implementation.
    pub(crate) fn fmt_variable(
        f: &mut Formatter<'_>,
        indentation: &mut String,
        host_template: &TemplateMacro,
        variable: &TemplateBodyVariableReference,
    ) -> Result<usize, fmt::Error> {
        let index = variable.signature_index();
        let name = host_template
            .signature()
            .parameters()
            .get(index)
            .unwrap()
            .name();
        writeln!(f, "{indentation}<param {name}>")?;
        Ok(1)
    }
}

/// A macro invocation found in the body of a template.
///
/// Because the template definition lives in the macro table (which may need to grow in the process
/// of evaluating a stream), this type holds the address of the invoked macro rather than a
/// reference to it.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct TemplateBodyMacroInvocation {
    invoked_macro_address: MacroAddress,
    arg_expr_range: ExprRange,
}

impl TemplateBodyMacroInvocation {
    pub fn new(invoked_macro_address: MacroAddress, arg_expr_range: ExprRange) -> Self {
        Self {
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

    /// Finds the definition of the macro being invoked in the provided `context`'s macro table.
    ///
    /// It is a logic error for this method to be called with an [`EncodingContextRef`] that does not
    /// contain the necessary information; doing so will cause this method to panic.
    pub(crate) fn resolve<'top>(
        self,
        host_template: TemplateMacroRef<'top>,
        context: EncodingContextRef<'top>,
    ) -> TemplateMacroInvocation<'top> {
        let invoked_macro = context
            .macro_table()
            .macro_at_address(self.invoked_macro_address)
            .unwrap();

        let arg_expressions = host_template
            .body
            .expressions()
            .get(self.arg_expr_range.ops_range())
            .unwrap();

        TemplateMacroInvocation {
            context,
            host_template,
            invoked_macro,
            arg_expressions,
        }
    }
}

/// A resolved version of [`TemplateBodyMacroInvocation`]; instead of holding addresses, this type
/// holds references to the invoked macro and its argument expressions.
#[derive(Copy, Clone)]
pub struct TemplateMacroInvocation<'top> {
    context: EncodingContextRef<'top>,
    // The definition of the template in which this macro invocation appears. This is useful as
    // debugging information / viewing in stack traces.
    host_template: TemplateMacroRef<'top>,
    // The macro being invoked
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
        context: EncodingContextRef<'top>,
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

    pub fn id(&self) -> MacroIdRef<'top> {
        MacroIdRef::LocalAddress(self.invoked_macro.address())
    }
    pub fn arguments<D: Decoder>(
        &self,
        environment: Environment<'top, D>,
    ) -> TemplateMacroInvocationArgsIterator<'top, D> {
        TemplateMacroInvocationArgsIterator::new(environment, *self)
    }
    pub fn host_template(&self) -> TemplateMacroRef<'top> {
        self.host_template
    }
    pub fn arg_expressions(&self) -> &'top [TemplateBodyValueExpr] {
        self.arg_expressions
    }
    pub fn invoked_macro(&self) -> MacroRef<'top> {
        self.invoked_macro
    }
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
}

impl<'top, D: Decoder> From<TemplateMacroInvocation<'top>> for MacroExpr<'top, D> {
    fn from(value: TemplateMacroInvocation<'top>) -> Self {
        MacroExpr::TemplateMacro(value)
    }
}

/// Steps over the argument expressions passed to a macro invocation found in a template body.
pub struct TemplateMacroInvocationArgsIterator<'top, D: Decoder> {
    environment: Environment<'top, D>,
    invocation: TemplateMacroInvocation<'top>,
    arg_index: usize,
}

impl<'top, D: Decoder> TemplateMacroInvocationArgsIterator<'top, D> {
    pub fn new(
        environment: Environment<'top, D>,
        invocation: TemplateMacroInvocation<'top>,
    ) -> Self {
        Self {
            environment,
            invocation,
            arg_index: 0,
        }
    }
}

impl<'top, D: Decoder> Iterator for TemplateMacroInvocationArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let arg = self.invocation.arg_expressions().get(self.arg_index)?;
        self.arg_index += 1;
        let arg_expr = match arg {
            TemplateBodyValueExpr::Element(e) => {
                // If it's a container, skip over its contents when this iterator resumes
                match e.value() {
                    TemplateValue::List(range)
                    | TemplateValue::SExp(range)
                    | TemplateValue::Struct(range, _) => {
                        self.arg_index += range.len();
                    }
                    _ => {
                        // If it's a scalar, it has already been accounted for.
                    }
                };
                ValueExpr::ValueLiteral(LazyExpandedValue::from_template(
                    self.invocation.context,
                    self.environment,
                    TemplateElement::new(self.invocation.host_template(), e),
                ))
            }
            TemplateBodyValueExpr::Variable(variable_ref) => match self
                .environment
                .get_expected(variable_ref.signature_index())
            {
                Ok(expr) => expr,
                Err(e) => return Some(Err(e)),
            },
            TemplateBodyValueExpr::MacroInvocation(body_invocation) => {
                let invocation = body_invocation
                    .resolve(self.invocation.host_template(), self.invocation.context);
                // Skip over all of the expressions that belong to this invocation.
                self.arg_index += invocation.arg_expressions.len();
                ValueExpr::MacroInvocation(invocation.into())
            }
        };

        Some(Ok(arg_expr))
    }
}

/// A reference to a variable in a template body.
#[derive(Debug, Copy, Clone, PartialEq)]
pub struct TemplateBodyVariableReference {
    signature_index: u16,
}

impl TemplateBodyVariableReference {
    pub fn new(signature_index: u16) -> Self {
        Self { signature_index }
    }
    pub fn signature_index(&self) -> usize {
        self.signature_index as usize
    }
    pub fn name<'a>(&self, signature: &'a MacroSignature) -> &'a str {
        signature
            .parameters()
            .get(self.signature_index())
            .unwrap()
            .name()
    }
    /// Pairs this variable reference with the given template macro reference, allowing information
    /// about the template definition to be retrieved later.
    pub(crate) fn resolve<'top>(
        &self,
        template: TemplateMacroRef<'top>,
    ) -> TemplateVariableReference<'top> {
        TemplateVariableReference {
            template,
            signature_index: self.signature_index,
        }
    }
}

/// A value literal found in the body of a template.
///
/// This type is similar to [`TemplateBodyElement`], but holds resolved references rather than
/// addresses.
#[derive(Clone, Copy, Debug)]
pub struct TemplateElement<'top> {
    // This type holds a reference to the host template macro, which contains some shared resources
    // like a `Vec` of annotation definitions.
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

/// A value literal found int he body of a template. This type is similar to [`Value`], but its
/// container types hold ranges of expression addresses rather than a materialized tree of data.
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
    // The range of ensuing `TemplateBodyValueExpr`s that belong to this container.
    List(ExprRange),
    SExp(ExprRange),
    // A 'closed' struct quasi-literal. All field names are known at compile time.
    Struct(ExprRange, TemplateStructIndex),
    // TODO: Implementation of a `make_struct` macro requires an 'open' struct whose fields will
    //       often not be known at compile time.
}

/// A mapping of struct field names to one or more template body addresses that have that
/// field name. This type is used to allow field lookups within a template struct to happen in
/// constant rather than linear time.
pub type TemplateStructIndex = HashMap<Symbol, Vec<usize>>;

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
            Struct(_, _) => IonType::Struct,
        }
    }
}

/// A slice of a [`TemplateBody`]'s sequence of `TemplateExpansionStep`. This type can be used to
/// represent containers (list, sexp, struct) or macro invocations, all of which use an evaluator
/// to iteratively evaluate a series of `TemplateExpansionStep`s. This type does not hold a reference
/// to the template definition itself.
pub type ExprRange = SmallRange;

/// A slice of a [`TemplateBody`]'s shared `Vec` of annotation definitions. Each value in the
/// template body holds an `AnnotationsRange` that indicates which annotations in the shared
/// collections apply to it.
pub type AnnotationsRange = SmallRange;

/// A range that takes 8 bytes instead of `Range<usize>`'s 16. This is useful for cases like
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

    pub fn start(&self) -> usize {
        self.start as usize
    }

    pub fn end(&self) -> usize {
        self.end as usize
    }

    /// Produces an equivalent [`std::ops::Range`].
    ///
    /// `std::ops::Range` is twice as large as `SmallRange` on 64 bit machines and does not
    /// implement the `Copy` trait. This method is a convenience that allows a `SmallRange` to be
    /// used as a collection index.
    // We are not able to implement `std::ops::Index<SmallRange>` for the stdlib's collections as
    // this crate owns neither the `Index` trait nor the collections themselves.
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
