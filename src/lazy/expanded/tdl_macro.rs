//! Types and traits representing a macro invocation within a template.

use crate::element::iterators::SequenceIterator;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::expanded::macro_evaluator::{ArgumentKind, MacroInvocation, ToArgumentKind};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;

use crate::lazy::expanded::{EncodingContext, ExpandedValueSource, LazyExpandedValue};
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{Element, IonResult, Sequence, Value};

impl<'top, 'data, D: LazyDecoder<'data>> MacroInvocation<'data, D> for &'top Sequence {
    type ArgumentExpr = &'top Element;
    type ArgumentsIterator = OkAdapter<SequenceIterator<'top>>;

    // TODO: This dummy implementation using `&'top Sequence` will be replaced by a purpose-built
    //       type that validates the invocation before reaching this method. For now, this method can
    //       panic if the input is malformed.
    fn id(&self) -> MacroIdRef {
        match self.get(0).expect("TDL macro call missing ID").value() {
            Value::Int(address) => MacroIdRef::LocalAddress(
                usize::try_from(address.expect_i64().unwrap())
                    .expect("macro address int out of bounds for usize"),
            ),
            Value::Symbol(name) => {
                MacroIdRef::LocalName(name.text().expect("cannot use $0 as macro name"))
            }
            _ => panic!("macro IDs must be an int or symbol"),
        }
    }

    fn arguments(&self) -> Self::ArgumentsIterator {
        let mut children = self.elements();
        let _id = children.next().unwrap();
        OkAdapter { iterator: children }
    }
}

/// Wraps an infallible iterator's output items in `Result::Ok`.
pub struct OkAdapter<I>
where
    I: Iterator,
{
    iterator: I,
}

impl<I> OkAdapter<I>
where
    I: Iterator,
{
    pub fn new(iterator: I) -> Self {
        Self { iterator }
    }
}

impl<I: Iterator> Iterator for OkAdapter<I> {
    type Item = IonResult<<I as Iterator>::Item>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iterator.next().map(Ok)
    }
}

// When an `&Element` appears in macro argument position within a template, this trait implementation
// recognizes whether the `&Element` represents a value, a variable, or another template invocation.
impl<'element, 'data, D: LazyDecoder<'data>> ToArgumentKind<'data, D, &'element Sequence>
    for &'element Element
{
    fn to_arg_expr<'top>(
        self,
        context: EncodingContext<'top>,
    ) -> ArgumentKind<'top, 'data, D, &'element Sequence>
    where
        Self: 'top,
    {
        // In this implementation, we are reading the arguments to a template macro invocation.
        // For example:
        //
        //     (macro twice (a)
        //        // Inside a template definition, calling the `values` macro with two arguments
        //        (values a a)
        //     )
        // In this context, there are named variables to consider. If we encounter a symbol like `a`
        // in argument position, we must flag it as a variable so the caller has the opportunity to
        // resolve it to a value stream.
        match self.value() {
            Value::SExp(sequence) => ArgumentKind::MacroInvocation(sequence),
            Value::Symbol(variable) => ArgumentKind::Variable(variable.as_raw_symbol_token_ref()),
            _ => ArgumentKind::ValueLiteral(LazyExpandedValue {
                context,
                source: ExpandedValueSource::Template(self),
            }),
        }
    }
}
