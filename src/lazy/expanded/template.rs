use std::fmt;
use std::fmt::{Debug, Formatter};
use std::ops::{Deref, Range};

use bumpalo::collections::Vec as BumpVec;
use rustc_hash::FxHashMap;

use crate::{Bytes, Decimal, Int, IonResult, IonType, LazyExpandedFieldName, Str, Symbol, SymbolRef, Timestamp, try_or_some_err, Value};
use crate::lazy::binary::raw::v1_1::immutable_buffer::ArgGroupingBitmap;
use crate::lazy::decoder::Decoder;
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedValueSource, LazyExpandedValue, TemplateVariableReference,
};
use crate::lazy::expanded::compiler::ExpansionAnalysis;
use crate::lazy::expanded::macro_evaluator::{AnnotateExpansion, MacroEvaluator, MacroExpansion, MacroExpansionKind, MacroExpr, MacroExprArgsIterator, MakeStringExpansion, TemplateExpansion, ValueExpr, ValuesExpansion};
use crate::lazy::expanded::macro_table::{Macro, MacroKind, MacroRef};
use crate::lazy::expanded::r#struct::UnexpandedField;
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::text::raw::v1_1::reader::{MacroAddress, MacroIdRef};
use crate::result::IonFailure;

/// A parameter in a user-defined macro's signature.
#[derive(Debug, Clone, PartialEq)]
pub struct Parameter {
    name: String,
    encoding: ParameterEncoding,
    cardinality: ParameterCardinality,
    rest_syntax_policy: RestSyntaxPolicy,
}

impl Parameter {
    pub fn new(name: impl Into<String>, encoding: ParameterEncoding, cardinality: ParameterCardinality, rest_syntax_policy: RestSyntaxPolicy) -> Self {
        Self { name: name.into(), encoding, cardinality, rest_syntax_policy }
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }
    pub fn encoding(&self) -> ParameterEncoding {
        self.encoding
    }
    pub fn cardinality(&self) -> ParameterCardinality {
        self.cardinality
    }
    pub fn rest_syntax_policy(&self) -> RestSyntaxPolicy {
        self.rest_syntax_policy
    }
    /// Returns true if this parameter is of any cardinality other than `ExactlyOne` (`!`).
    pub fn is_variadic(&self) -> bool {
        !matches!(self.cardinality, ParameterCardinality::ExactlyOne)
    }
}

/// The encoding used to serialize and deserialize the associated parameter.
#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ParameterEncoding {
    /// A 'tagged' type is one whose binary encoding begins with an opcode (sometimes called a 'tag'.)
    Tagged,
    FlexUInt,
    // TODO: tagless types, including fixed-width types and macros
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum ParameterCardinality {
    ExactlyOne, // !
    ZeroOrOne,  // ?
    ZeroOrMore, // *
    OneOrMore,  // +
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub enum RestSyntaxPolicy {
    NotAllowed,
    Allowed
}

/// The sequence of parameters for which callers must pass expressions when invoking the macro.
#[derive(Debug, Clone, PartialEq)]
pub struct MacroSignature {
    parameters: Vec<Parameter>,
    num_variadic_params: usize,
}

impl MacroSignature {
    fn with_parameter(mut self, name: impl Into<String>, encoding: ParameterEncoding, cardinality: ParameterCardinality) -> IonResult<Self> {
        // We're adding a new parameter, so the previous "final position" parameter is no longer in the final position.
        // Disable rest syntax for that parameter.
        if let Some(final_position_param) = self.parameters.last_mut() {
            final_position_param.rest_syntax_policy = RestSyntaxPolicy::NotAllowed;
        }
        let rest_syntax_policy = if cardinality == ParameterCardinality::ExactlyOne {
            RestSyntaxPolicy::NotAllowed
        } else {
            self.num_variadic_params += 1;
            if self.num_variadic_params > ArgGroupingBitmap::MAX_VARIADIC_PARAMS {
                return IonResult::decoding_error(format!(
                    "macro found with {} variadic parameters; the max supported is {}",
                    self.num_variadic_params,
                    ArgGroupingBitmap::MAX_VARIADIC_PARAMS,
                ));
            };
            RestSyntaxPolicy::Allowed
        };
        let param = Parameter::new(name.into(), encoding, cardinality, rest_syntax_policy);
        self.parameters.push(param);
        Ok(self)
    }

    /// Constructs a new instance of a signature with no arguments (the signature of a "constant" template).
    fn constant() -> Self {
        Self::new(Vec::new()).unwrap()
    }

    pub fn len(&self) -> usize {
        self.parameters().len()
    }
    pub fn parameters(&self) -> &[Parameter] {
        self.parameters.as_slice()
    }
    pub fn new(parameters: Vec<Parameter>) -> IonResult<Self> {
        let num_variadic_params = parameters.iter().filter(|p| p.cardinality != ParameterCardinality::ExactlyOne).count();
        if num_variadic_params > ArgGroupingBitmap::MAX_VARIADIC_PARAMS {
            return IonResult::decoding_error(format!(
                "macro found with {num_variadic_params} variadic parameters; the max supported is {}",
                ArgGroupingBitmap::MAX_VARIADIC_PARAMS
            ));
        };
        Ok(Self { parameters, num_variadic_params })
    }
    pub fn num_variadic_params(&self) -> usize {
        self.num_variadic_params
    }
    pub fn bitmap_size_in_bytes(&self) -> usize {
        const BITS_PER_VARIADIC_PARAM: usize = 2;
        const BITS_PER_BYTE: usize = 8;
        ((self.num_variadic_params * BITS_PER_VARIADIC_PARAM) + 7) / 8
    }
}

#[cfg(test)]
mod macro_signature_tests {
    use crate::IonResult;
    use crate::lazy::expanded::template::{MacroSignature, ParameterCardinality, ParameterEncoding};

    #[test]
    fn bitmap_sizes() -> IonResult<()> {
        let signature = MacroSignature::constant();
        assert_eq!(signature.num_variadic_params(), 0);
        assert_eq!(signature.bitmap_size_in_bytes(), 0);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter("foo", ParameterEncoding::Tagged, ParameterCardinality::ExactlyOne)?;
        assert_eq!(signature.num_variadic_params(), 0);
        assert_eq!(signature.bitmap_size_in_bytes(), 0);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter("foo", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?;
        assert_eq!(signature.num_variadic_params(), 1);
        assert_eq!(signature.bitmap_size_in_bytes(), 1);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter("foo", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("bar", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?;
        assert_eq!(signature.num_variadic_params(), 2);
        assert_eq!(signature.bitmap_size_in_bytes(), 1);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter("foo", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("bar", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrMore)?
            .with_parameter("baz", ParameterEncoding::Tagged, ParameterCardinality::OneOrMore)?;
        assert_eq!(signature.num_variadic_params(), 3);
        assert_eq!(signature.bitmap_size_in_bytes(), 1);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter("foo", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("bar", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("baz", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("quux", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?;
        assert_eq!(signature.num_variadic_params(), 4);
        assert_eq!(signature.bitmap_size_in_bytes(), 1);

        let signature = MacroSignature::new(Vec::new())?
            .with_parameter("foo", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("bar", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("baz", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("quux", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?
            .with_parameter("quuz", ParameterEncoding::Tagged, ParameterCardinality::ZeroOrOne)?;
        assert_eq!(signature.num_variadic_params(), 5);
        assert_eq!(signature.bitmap_size_in_bytes(), 2);

        Ok(())
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
#[derive(Clone, PartialEq)]
pub struct TemplateMacro {
    pub(crate) name: Option<String>,
    pub(crate) signature: MacroSignature,
    pub(crate) body: TemplateBody,
    pub(crate) expansion_analysis: ExpansionAnalysis,
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
            index += TemplateBodyExprKind::fmt_expr(f, indentation, self, expr)?;
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
    macro_ref: MacroRef<'top>,
    template_body: &'top TemplateBody,
}

impl<'top> TemplateMacroRef<'top> {
    pub fn new(macro_ref: MacroRef<'top>, template_body: &'top TemplateBody) -> Self {
        Self { macro_ref, template_body }
    }
    pub fn body(&self) -> &'top TemplateBody {
        self.template_body
    }

    pub fn macro_ref(&self) -> MacroRef<'top> {
        self.macro_ref
    }
}

impl<'top> Deref for TemplateMacroRef<'top> {
    type Target = MacroRef<'top>;

    fn deref(&self) -> &Self::Target {
        &self.macro_ref
    }
}

/// Steps over the child expressions of a list or s-expression found in the body of a template.
pub struct TemplateSequenceIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    template: TemplateMacroRef<'top>,
    evaluator: MacroEvaluator<'top, D>,
    value_expressions: &'top [TemplateBodyExpr],
    index: usize,
}

impl<'top, D: Decoder> TemplateSequenceIterator<'top, D> {
    pub fn new(
        context: EncodingContextRef<'top>,
        evaluator: MacroEvaluator<'top, D>,
        template: TemplateMacroRef<'top>,
        nested_expressions: &'top [TemplateBodyExpr],
    ) -> Self {
        Self {
            context,
            template,
            evaluator,
            value_expressions: nested_expressions,
            index: 0,
        }
    }
}

impl<'top, D: Decoder> Iterator for TemplateSequenceIterator<'top, D> {
    type Item = IonResult<LazyExpandedValue<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            // If the evaluator's stack is not empty, give it the opportunity to yield a value.
            if let Some(value) = try_or_some_err!(self.evaluator.next()) {
                return Some(Ok(value));
            }
            // The stack did not produce values and is empty, pull the next expression from `self.value_expressions`
            // and start expanding it.
            let current_expr = self.value_expressions.get(self.index)?;
            let environment = self.evaluator.environment();
            self.index += current_expr.num_expressions();
            break match current_expr.kind() {
                TemplateBodyExprKind::Element(element) => {
                    let value = LazyExpandedValue {
                        context: self.context,
                        source: ExpandedValueSource::Template(
                            environment,
                            TemplateElement::new(self.template.macro_ref, element, current_expr.expr_range()),
                        ),
                        variable: None,
                    };
                    Some(Ok(value))
                }
                TemplateBodyExprKind::MacroInvocation(body_invocation) => {
                    // ...it's a TDL macro invocation. Resolve the invocation to get a reference to the
                    // macro being invoked.
                    let invoked_macro = self
                        .context
                        .macro_table()
                        .macro_at_address(body_invocation.invoked_macro_address)
                        .unwrap();
                    let invocation = TemplateMacroInvocation::new(
                        self.context,
                        self.template.address(),
                        invoked_macro,
                        ExprRange::new(current_expr.expr_range().tail())
                    );
                    // If the macro is guaranteed to expand to exactly one value, we can evaluate it
                    // in place.
                    let new_expansion = try_or_some_err!(MacroExpansion::initialize(environment, invocation.into()));
                    if invoked_macro.expansion_analysis().must_produce_exactly_one_value() {
                        Some(new_expansion.expand_singleton())
                    } else {
                        // Otherwise, add it to the evaluator's stack and return to the top of the loop.
                        self.evaluator.push(new_expansion);
                        continue;
                    }
                }
                TemplateBodyExprKind::Variable(variable_ref) => {
                    let arg_expr = self.evaluator.environment().require_expr(variable_ref.signature_index());
                    match arg_expr {
                        ValueExpr::ValueLiteral(value) => Some(Ok(value)),
                        ValueExpr::MacroInvocation(invocation) => {
                            let new_expansion = try_or_some_err!(MacroExpansion::initialize(environment, invocation));
                            if invocation.invoked_macro().expansion_analysis().must_produce_exactly_one_value() {
                                Some(new_expansion.expand_singleton())
                            } else {
                                // Otherwise, add it to the evaluator's stack and return to the top of the loop.
                                self.evaluator.push(new_expansion);
                                continue;
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
    nested_expressions: &'top [TemplateBodyExpr],
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
        nested_expressions: &'top [TemplateBodyExpr],
    ) -> Self {
        Self {
            context,
            environment,
            template,
            nested_expressions,
            index: 0,
        }
    }
}

impl<'top, D: Decoder> Iterator for TemplateStructUnexpandedFieldsIterator<'top, D> {
    type Item = IonResult<UnexpandedField<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        let name_expr_address = self.index;
        let name_element = self
            .nested_expressions
            .get(name_expr_address)?
            .kind()
            .require_element();
        let name: SymbolRef = match &name_element.value {
            TemplateValue::Symbol(s) => s.into(),
            TemplateValue::String(s) => s.text().into(),
            _ => unreachable!("template struct field had a non-text field name"),
        };
        let value_expr_address = name_expr_address + 1;
        let value_expr = self
            .nested_expressions
            .get(value_expr_address)
            .expect("template struct had field name with no value");
        let unexpanded_field = match value_expr.kind() {
            TemplateBodyExprKind::Element(element) => {
                UnexpandedField::NameValue(
                    LazyExpandedFieldName::TemplateName(self.template, name),
                    LazyExpandedValue::from_template(self.context, self.environment, TemplateElement::new(self.template.macro_ref(), element, value_expr.expr_range())),
                )
            }
            TemplateBodyExprKind::MacroInvocation(body_invocation) => {
                let invoked_macro = self
                    .context
                    .macro_table()
                    .macro_at_address(body_invocation.invoked_macro_address)
                    .unwrap();
                let invocation = TemplateMacroInvocation::new(
                    self.context,
                    self.template.address(),
                    invoked_macro,
                    ExprRange::new(value_expr.expr_range().tail())
                );
                UnexpandedField::NameMacro(
                    LazyExpandedFieldName::TemplateName(self.template, name),
                    MacroExpr::from_template_macro(invocation)
                )
            }
            TemplateBodyExprKind::Variable(variable) => {
                let arg_expr = self
                    .environment
                    .require_expr(variable.signature_index());
                let variable_ref = variable.resolve(self.template.macro_ref.reference());
                let field_name = LazyExpandedFieldName::TemplateName(self.template, name);
                let field = match arg_expr {
                    ValueExpr::ValueLiteral(value) => UnexpandedField::NameValue(field_name, value.via_variable(variable_ref)),
                    ValueExpr::MacroInvocation(invocation) => UnexpandedField::NameMacro(field_name, invocation)
                };
                field
            }
        };
        self.index += /* name expr count -> */ 1 + value_expr.num_expressions();
        Some(Ok(unexpanded_field))
    }
}

/// Stores a sequence of expansion steps that need to be evaluated in turn.
///
/// See [`TemplateBodyExprKind`] for details.
#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBody {
    // A vector of expressions that will be visited in turn during expansion.
    pub(crate) expressions: Vec<TemplateBodyExpr>,
    // All of the elements stored in the Vec above share the Vec below for storing their annotations.
    // This allows us to avoid allocating a `Vec<Symbol>` for every value in the template, saving
    // a small amount of time and memory during compilation. Each values hold an index range
    // into this `Vec`.
    pub(crate) annotations_storage: Vec<Symbol>,
}

impl TemplateBody {
    pub fn expressions(&self) -> &[TemplateBodyExpr] {
        self.expressions.as_slice()
    }
    pub fn annotations_storage(&self) -> &[Symbol] {
        &self.annotations_storage
    }

    pub fn push_element(&mut self, element: TemplateBodyElement, expr_range: ExprRange) {
        self.expressions
            .push(TemplateBodyExpr::element(element, expr_range))
    }

    pub fn push_variable(&mut self, signature_index: u16) {
        let index = self.expressions.len();
        self.expressions.push(TemplateBodyExpr::variable(signature_index, ExprRange::new(index..index+1)))
    }

    pub fn push_macro_invocation(&mut self, invoked_macro_address: usize, expr_range: ExprRange) {
        self.expressions
            .push(TemplateBodyExpr::macro_invocation(invoked_macro_address, expr_range))
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBodyExpr {
    kind: TemplateBodyExprKind,
    expr_range: ExprRange,
}

impl TemplateBodyExpr {
    pub fn new(kind: TemplateBodyExprKind, expr_range: ExprRange) -> Self {
        Self { kind, expr_range }
    }

    pub fn element(element: TemplateBodyElement, expr_range: ExprRange) -> Self {
        Self {
            kind: TemplateBodyExprKind::Element(element),
            expr_range
        }
    }

    pub fn variable(signature_index: u16, expr_range: ExprRange) -> Self {
        Self {
            kind: TemplateBodyExprKind::Variable(TemplateBodyVariableReference::new(signature_index)),
            expr_range
        }
    }

    pub fn macro_invocation(invoked_macro_address: MacroAddress, expr_range: ExprRange) -> Self {
        Self {
            kind: TemplateBodyExprKind::MacroInvocation(TemplateBodyMacroInvocation::new(invoked_macro_address)),
            expr_range
        }
    }

    pub fn kind(&self) -> &TemplateBodyExprKind {
        &self.kind
    }

    pub fn num_expressions(&self) -> usize {
        self.expr_range.len()
    }

    pub fn expr_range(&self) -> ExprRange {
        self.expr_range
    }
}

/// An expression appearing in value position in a template body.
#[derive(Debug, Clone, PartialEq)]
pub enum TemplateBodyExprKind {
    /// A potentially annotated value literal.
    Element(TemplateBodyElement),
    /// A reference to a variable that needs to be expanded.
    Variable(TemplateBodyVariableReference),
    /// A macro invocation that needs to be expanded.
    MacroInvocation(TemplateBodyMacroInvocation),
}

impl TemplateBodyExprKind {
    /// Confirms that this value expression is a value literal and panics if it is not.
    ///
    /// When this method is called, it is because the rules of the template compiler have
    /// dictated that an element in this position be a value literal.
    #[inline]
    pub fn require_element(&self) -> &TemplateBodyElement {
        if let TemplateBodyExprKind::Element(e) = self {
            return e;
        }
        unreachable!("The compiled template contained a non-element in element position");
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
        expr: &TemplateBodyExpr,
    ) -> Result<usize, fmt::Error> {
        match &expr.kind() {
            TemplateBodyExprKind::Element(e) => {
                Self::fmt_element(f, indentation, host_template, e, expr.expr_range())
            }
            TemplateBodyExprKind::Variable(v) => {
                Self::fmt_variable(f, indentation, host_template, v)
            }
            TemplateBodyExprKind::MacroInvocation(m) => {
                Self::fmt_invocation(f, indentation, host_template, m, expr.expr_range())
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
        expr_range: ExprRange,
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
            List => {
                writeln!(f, "list")?;
                return Self::fmt_sequence_body(f, indentation, host_template, expr_range);
            }
            SExp => {
                writeln!(f, "sexp")?;
                return Self::fmt_sequence_body(f, indentation, host_template, expr_range);
            }
            Struct(_) => {
                writeln!(f, "struct")?;
                return Self::fmt_struct(f, indentation, host_template, expr_range);
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
            let TemplateBodyExprKind::Element(name_element) = &expressions[expr_index].kind() else {
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
        expr_range: ExprRange,
    ) -> Result<usize, fmt::Error> {
        writeln!(
            f,
            "{indentation}<invoke macro @ address {}>",
            invocation.invoked_macro_address
        )?;
        let args = host_template
            .body
            .expressions
            .get(expr_range.tail())
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
}

impl TemplateBodyMacroInvocation {
    pub fn new(invoked_macro_address: MacroAddress) -> Self {
        Self {
            invoked_macro_address,
        }
    }
    pub fn macro_address(&self) -> MacroAddress {
        self.invoked_macro_address
    }

    /// Finds the definition of the macro being invoked in the provided `context`'s macro table.
    ///
    /// It is a logic error for this method to be called with an [`EncodingContextRef`] that does not
    /// contain the necessary information; doing so will cause this method to panic.
    pub(crate) fn resolve(
        self,
        context: EncodingContextRef,
        host_template_address: MacroAddress,
        expr_range: ExprRange
    ) -> TemplateMacroInvocation {
        let invoked_macro = context
            .macro_table()
            .macro_at_address(self.invoked_macro_address)
            .unwrap();

        let arg_expr_range = ExprRange::new(expr_range.tail());

        TemplateMacroInvocation::new(context, host_template_address, invoked_macro, arg_expr_range)
    }
}

/// A resolved version of [`TemplateBodyMacroInvocation`]; instead of holding addresses, this type
/// holds references to the invoked macro and its argument expressions.
#[derive(Copy, Clone)]
pub struct TemplateMacroInvocation<'top> {
    context: EncodingContextRef<'top>,
    // We store the address of the host template (8 bytes) rather than a full TemplateMacroRef (24)
    host_template_address: MacroAddress,
    // The macro being invoked
    invoked_macro: MacroRef<'top>,
    // The range of value expressions in the host template's body that are arguments to the
    // macro being invoked
    arg_expressions_range: ExprRange,
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
        host_template_address: MacroAddress,
        invoked_macro: MacroRef<'top>,
        arg_expressions_range: ExprRange,
    ) -> Self {
        Self {
            context,
            host_template_address,
            invoked_macro,
            arg_expressions_range,
        }
    }

    pub fn id(&self) -> MacroIdRef<'top> {
        MacroIdRef::LocalAddress(self.invoked_macro.address())
    }
    pub fn arguments<D: Decoder>(
        &self,
        environment: Environment<'top, D>,
    ) -> TemplateMacroInvocationArgsIterator<'top, D> {
        TemplateMacroInvocationArgsIterator::new(self.context, environment, self.arg_expressions(), self.host_macro_ref())
    }
    pub fn host_template_address(&self) -> MacroAddress {
        self.host_template_address
    }

    /// Helper method to access the definition of the host template. Useful for debugging,
    /// but not required for macro expansion.
    pub fn host_macro_ref(&self) -> MacroRef<'top> {
        self.context().macro_table().macro_at_address(self.host_template_address).unwrap()
    }

    /// Helper method to access the definition of the host template. Useful for debugging,
    /// but not required for macro expansion.
    pub fn host_template(&self) -> TemplateMacroRef<'top> {
        // We only store the macro address (8 bytes) instead of the full `TemplateMacroRef` (24 bytes)
        // for size savings. Because the address was copied from a resolved `TemplateMacroRef` in the
        // constructor and the encoding context is frozen for the duration of `'top`, we can safely
        // assume that the address maps to a template macro in the current encoding context. This
        // allows us to call `unwrap()` freely.
        let macro_ref = self.host_macro_ref();
        macro_ref.require_template()
    }

    pub fn arg_expressions(&self) -> &'top [TemplateBodyExpr] {
        self.host_template().body().expressions().get(self.arg_expressions_range.ops_range()).unwrap()
    }
    pub fn invoked_macro(&self) -> MacroRef<'top> {
        self.invoked_macro
    }
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }

    pub fn new_evaluation_environment<D: Decoder>(&self, parent_environment: Environment<'top, D>) -> IonResult<Environment<'top, D>> {
        let arguments = self.arguments(parent_environment);
        let allocator = self.context().allocator();
        // Use the iterator's size hint to determine an initial capacity to aim for.
        let num_args_hint = arguments.size_hint();
        let capacity_hint = num_args_hint.1.unwrap_or(num_args_hint.0);
        let mut env_exprs = BumpVec::with_capacity_in(capacity_hint, allocator);
        for arg in arguments {
            env_exprs.push(arg?);
        }
        Ok(Environment::new(env_exprs.into_bump_slice()))
    }

    pub fn expand<D: Decoder>(&self, mut environment: Environment<'top, D>) -> IonResult<MacroExpansion<'top, D>> {
        // Initialize a `MacroExpansionKind` with the state necessary to evaluate the requested
        // macro.
        let macro_ref: MacroRef<'top> = self.invoked_macro();
        let arguments = MacroExprArgsIterator::from_template_macro(self.arguments(environment));
        let expansion_kind = match macro_ref.kind() {
            MacroKind::Void => MacroExpansionKind::Void,
            MacroKind::Values => MacroExpansionKind::Values(ValuesExpansion::new(arguments)),
            MacroKind::MakeString => {
                MacroExpansionKind::MakeString(MakeStringExpansion::new(arguments))
            }
            MacroKind::Annotate => MacroExpansionKind::Annotate(AnnotateExpansion::new(arguments)),
            MacroKind::Template(template_body) => {
                let template_ref = TemplateMacroRef::new(macro_ref, template_body);
                environment = self.new_evaluation_environment(environment)?;
                MacroExpansionKind::Template(TemplateExpansion::new(template_ref))
            }
        };
        Ok(MacroExpansion::new(self.context(), environment, expansion_kind))
    }
}

impl<'top, D: Decoder> From<TemplateMacroInvocation<'top>> for MacroExpr<'top, D> {
    fn from(value: TemplateMacroInvocation<'top>) -> Self {
        MacroExpr::from_template_macro(value)
    }
}

/// Steps over the argument expressions passed to a macro invocation found in a template body.
#[derive(Copy, Clone, Debug)]
pub struct TemplateMacroInvocationArgsIterator<'top, D: Decoder> {
    context: EncodingContextRef<'top>,
    environment: Environment<'top, D>,
    host_template: MacroRef<'top>,
    // The range of value expressions in the host template's body that are arguments to the
    // macro being invoked
    arg_expressions: &'top [TemplateBodyExpr],
    arg_index: usize,
}

impl<'top, D: Decoder> TemplateMacroInvocationArgsIterator<'top, D> {
    pub fn new(context: EncodingContextRef<'top>, environment: Environment<'top, D>, arg_expressions: &'top [TemplateBodyExpr], host_template: MacroRef<'top>) -> Self {
        Self {
            environment,
            context,
            arg_expressions,
            host_template,
            arg_index: 0
        }
    }

    pub fn is_exhausted(&self) -> bool {
        let current = self.arg_index;
        let max = self.arg_expressions.len();
        current == max
    }
}

impl<'top, D: Decoder> Iterator for TemplateMacroInvocationArgsIterator<'top, D> {
    type Item = IonResult<ValueExpr<'top, D>>;

    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        let arg = self.arg_expressions.get(self.arg_index)?;
        let arg_expr = match arg.kind() {
            TemplateBodyExprKind::Element(e) => {
                ValueExpr::ValueLiteral(LazyExpandedValue::from_template(
                    self.context,
                    self.environment,
                    TemplateElement::new(self.host_template, e, arg.expr_range()),
                ))
            }
            TemplateBodyExprKind::Variable(variable_ref) => {
                self
                    .environment
                    .require_expr(variable_ref.signature_index())
            },
            TemplateBodyExprKind::MacroInvocation(body_invocation) => {
                let invocation = body_invocation
                    .resolve(self.context, self.host_template.address(), arg.expr_range());
                ValueExpr::MacroInvocation(invocation.into())
            }
        };
        self.arg_index += arg.num_expressions();

        Some(Ok(arg_expr))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let num_args = self.arg_expressions.len();
        (num_args, Some(num_args))
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
        host_macro: &'top Macro,
    ) -> TemplateVariableReference<'top> {
        TemplateVariableReference::new(
            host_macro,
            self.signature_index,
        )
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
    template: MacroRef<'top>,
    element: &'top TemplateBodyElement,
    expr_range: ExprRange,
}

impl<'top> TemplateElement<'top> {
    pub fn new(template: MacroRef<'top>, element: &'top TemplateBodyElement, expr_range: ExprRange) -> Self {
        Self { template, element, expr_range }
    }
    pub fn annotations(&self) -> &'top [Symbol] {
        self.template
            .require_template()
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
        self.template.require_template()
    }
    pub fn expr_range(&self) -> ExprRange {
        self.expr_range
    }
    pub fn nested_expressions(&self) -> &'top [TemplateBodyExpr] {
        self.template().body().expressions().get(self.expr_range.tail()).unwrap()
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
    List,
    SExp,
    // A 'closed' struct quasi-literal. All field names are known at compile time.
    Struct(TemplateStructIndex),
    // TODO: Implementation of a `make_struct` macro requires an 'open' struct whose fields will
    //       often not be known at compile time.
}

/// A mapping of struct field names to one or more template body addresses that have that
/// field name. This type is used to allow field lookups within a template struct to happen in
/// constant rather than linear time.
pub type TemplateStructIndex = FxHashMap<Symbol, Vec<usize>>;

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
            List => IonType::List,
            SExp => IonType::SExp,
            Struct(_) => IonType::Struct,
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

    pub fn tail(&self) -> Range<usize> {
        self.start as usize + 1 .. self.end as usize
    }

    pub fn len(&self) -> usize {
        (self.end - self.start) as usize
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
}
