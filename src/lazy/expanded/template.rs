use std::ops::Range;

use crate::lazy::decoder::{LazyDecoder, RawFieldExpr, RawValueExpr};
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, TemplateEvaluator};
use crate::lazy::expanded::{EncodingContext, ExpandedValueSource, LazyExpandedValue};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::IonFailure;
use crate::{
    Bytes, Decimal, Element, Int, IonResult, IonType, Sequence, Str, Struct, Symbol, Timestamp,
    Value,
};

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
    evaluator: TemplateEvaluator<'top, 'top, 'data, D>,
    // The list element over which we're iterating
    sequence: &'top Sequence,
    index: usize,
}

impl<'top, 'data, D: LazyDecoder<'data>> TemplateSequenceIterator<'top, 'data, D> {
    pub fn new(
        context: EncodingContext<'top>,
        evaluator: TemplateEvaluator<'top, 'top, 'data, D>,
        sequence: &'top Sequence,
    ) -> Self {
        Self {
            sequence,
            index: 0,
            context,
            evaluator,
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
            // We didn't get a value from the evaluator, so pull the next expression from the
            // sequence.
            let element = self.sequence.get(self.index)?;
            self.index += 1;
            // If the expression is an s-expression...
            if let Value::SExp(sequence) = element.value() {
                // ...it's a TDL macro invocation. Push it onto the evaluator's stack and return
                // to the top of the loop.
                match self.evaluator.push(self.context, sequence) {
                    Ok(_) => continue,
                    Err(e) => return Some(Err(e)),
                }
            }
            // Otherwise, it's our next value.
            return Some(Ok(LazyExpandedValue {
                context: self.context,
                source: ExpandedValueSource::Template(element),
            }));
        }
    }
}

// An iterator that pulls values from a template body and wraps them in a `RawFieldExpr` to
// mimic reading them from input. The LazyExpandedStruct handles evaluating any macros that this
// yields.
pub struct TemplateStructRawFieldsIterator<'top> {
    // The struct element over whose fields we're iterating
    struct_: &'top Struct,
    index: usize,
}

impl<'top> TemplateStructRawFieldsIterator<'top> {
    pub fn new(struct_: &'top Struct) -> Self {
        Self { struct_, index: 0 }
    }
}

impl<'top> Iterator for TemplateStructRawFieldsIterator<'top> {
    type Item = IonResult<RawFieldExpr<'top, &'top Element, &'top Sequence>>;

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((name, element)) = self.struct_.get_index(self.index) {
            self.index += 1;
            let name = name.as_raw_symbol_token_ref();
            let value = if let Value::SExp(sequence) = element.value() {
                RawValueExpr::MacroInvocation(sequence)
            } else {
                RawValueExpr::ValueLiteral(element)
            };
            Some(Ok(RawFieldExpr::NameValuePair(name, value)))
        } else {
            None
        }
    }
}

/// Stores a sequence of expansion steps that need to be evaluated in turn.
///
/// See [`TemplateExpansionStep`] for details.
#[derive(Debug, Clone, PartialEq)]
pub struct TemplateBody {
    pub(crate) expansion_steps: Vec<TemplateExpansionStep>,
    pub(crate) annotations_storage: Vec<Symbol>,
}

impl TemplateBody {
    pub fn expansion_steps(&self) -> &Vec<TemplateExpansionStep> {
        &self.expansion_steps
    }
    pub fn annotations_storage(&self) -> &Vec<Symbol> {
        &self.annotations_storage
    }

    pub fn push_element(&mut self, element: TemplateElement) {
        self.expansion_steps
            .push(TemplateExpansionStep::Element(element))
    }

    pub fn push_variable(&mut self, name: impl Into<String>, signature_index: usize) {
        self.expansion_steps.push(TemplateExpansionStep::Variable(
            name.into(),
            signature_index,
        ))
    }

    pub fn push_macro_invocation(&mut self, address: usize, num_child_expressions: usize) {
        self.expansion_steps
            .push(TemplateExpansionStep::MacroInvocation(
                address,
                num_child_expressions,
            ))
    }
}

/// A single step in the expansion (i.e. evaluation) of a template.
#[derive(Debug, Clone, PartialEq)]
pub enum TemplateExpansionStep {
    /// A potentially annotated value literal.
    Element(TemplateElement),
    /// A reference to a variable that needs to be expanded.
    /// Stores the variable's name and its index within the macro's signature.
    Variable(String, usize),
    /// A macro invocation that needs to be expanded.
    /// Stores the macro address and the number of argument expressions.
    MacroInvocation(usize, usize),
}

impl TemplateExpansionStep {
    /// Returns `Ok(&element)` if this expansion step is an annotated value. Otherwise, returns
    /// `Err(IonError)`.
    pub fn expect_element(&self) -> IonResult<&TemplateElement> {
        match self {
            TemplateExpansionStep::Element(e) => Ok(e),
            TemplateExpansionStep::Variable(name, _) => {
                IonResult::decoding_error(format!("expected an element, found variable '{name}'"))
            }
            TemplateExpansionStep::MacroInvocation(address, _) => IonResult::decoding_error(
                format!("expected an element, found macro at address {address}"),
            ),
        }
    }
}

/// An annotated value in a template body.
#[derive(Debug, Clone, PartialEq)]
pub struct TemplateElement {
    // To minimize allocations, all annotations live in a single `Vec` in the `TemplateBody`.
    // Each element holds a range pointing to its annotation sequence.
    pub(crate) annotations_range: Range<u32>,
    pub(crate) value: TemplateValue,
}

impl TemplateElement {
    pub fn with_value(value: TemplateValue) -> Self {
        Self {
            annotations_range: 0..0,
            value,
        }
    }
    pub fn with_annotations(mut self, range: Range<usize>) -> Self {
        self.annotations_range = range.start as u32..range.end as u32;
        self
    }

    pub fn value(&self) -> &TemplateValue {
        &self.value
    }
    pub fn annotations(&self) -> Range<usize> {
        self.annotations_range.start as usize..self.annotations_range.end as usize
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
    List(usize),
    SExp(usize),
    // The number of fields in the struct. Each field is made up of a pair of TemplateElements,
    // a name (always a symbol, never has annotations), and a value (any element).
    Struct(usize),
}
