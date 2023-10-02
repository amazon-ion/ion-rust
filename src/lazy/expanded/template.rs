use crate::lazy::decoder::{LazyDecoder, RawFieldExpr, RawValueExpr};
use crate::lazy::expanded::macro_evaluator::{MacroEvaluator, TemplateEvaluator};
use crate::lazy::expanded::{EncodingContext, ExpandedValueSource, LazyExpandedValue};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{Element, IonResult, Sequence, Struct, Value};
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

    fn parameters(&self) -> &[Parameter] {
        &self.parameters
    }
}

#[derive(Debug, Clone)]
pub struct TemplateMacro {
    // TODO: Make the name optional
    name: String,
    signature: MacroSignature,
    // For now, the body is just the materialized tree of the source. Eventually, this will be
    // a purpose-built type designed for evaluation efficiency.
    body: Element,
}

impl TemplateMacro {
    pub fn name(&self) -> &str {
        &self.name
    }
    pub fn signature(&self) -> &MacroSignature {
        &self.signature
    }
    pub fn body(&self) -> &Element {
        &self.body
    }
}

pub type TdlMacroInvocation<'top> = &'top Element;

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
