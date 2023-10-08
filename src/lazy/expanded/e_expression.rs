//! Types and traits representing an e-expression in an Ion stream.

use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr, RawArgumentExpr, RawValueExpr};
use crate::lazy::expanded::macro_evaluator::{ArgumentKind, ToArgumentKind};
use crate::lazy::expanded::{EncodingContext, ExpandedValueSource, LazyExpandedValue};

// When a `LazyRawValueExpr` appears in argument position within an e-expression, this trait
// implementation recognizes it as either a value or another macro invocation.
impl<'data, D: LazyDecoder<'data>> ToArgumentKind<'data, D, D::MacroInvocation>
    for LazyRawValueExpr<'data, D>
{
    fn to_arg_expr<'top>(
        self,
        context: EncodingContext<'top>,
    ) -> ArgumentKind<'top, 'data, D, D::MacroInvocation>
    where
        D::MacroInvocation: 'top,
        Self: 'top,
    {
        match self {
            // In this implementation, we're reading arguments to an E-expression in the data stream.
            // Because e-expressions appear in the data stream (and not in a template), there is no
            // environment of named variables. We do not attempt to resolve symbols as though they
            // were variable names and instead pass them along as value literals.
            RawValueExpr::ValueLiteral(value) => ArgumentKind::ValueLiteral(LazyExpandedValue {
                context,
                source: ExpandedValueSource::ValueLiteral(value),
            }),
            RawValueExpr::MacroInvocation(invocation) => ArgumentKind::MacroInvocation(invocation),
        }
    }
}
