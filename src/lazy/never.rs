use crate::lazy::decoder::LazyDecoder;
use crate::lazy::expanded::macro_evaluator::{
    ArgumentKind, MacroEvaluator, MacroExpansion, MacroInvocation, ToArgumentKind,
};
use crate::lazy::expanded::EncodingContext;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::IonResult;
use std::fmt::Debug;

use bumpalo::collections::Vec as BumpVec;

/// An uninhabited type that signals to the compiler that related code paths are not reachable.
#[derive(Debug, Copy, Clone)]
pub enum Never {
    // Has no variants, cannot be instantiated.
}

// Ion 1.0 uses `Never` as a placeholder type for MacroInvocation.
// The compiler should optimize these methods away.
impl<'data, D: LazyDecoder<'data>> MacroInvocation<'data, D> for Never {
    type ArgumentExpr = Never;
    // This uses a Box<dyn> to avoid defining yet another placeholder type.
    type ArgumentsIterator = Box<dyn Iterator<Item = IonResult<Never>>>;

    type TransientEvaluator<'context> = Never  where Self: 'context, 'data: 'context;

    fn id(&self) -> MacroIdRef<'_> {
        unreachable!("macro in Ion 1.0 (method: id)")
    }

    fn arguments(&self) -> Self::ArgumentsIterator {
        unreachable!("macro in Ion 1.0 (method: arguments)")
    }

    fn make_transient_evaluator<'context>(
        _context: EncodingContext<'context>,
    ) -> Self::TransientEvaluator<'context>
    where
        'data: 'context,
        Self: 'context,
    {
        unreachable!("macro in Ion 1.0 (method: make_transient_evaluator)")
    }
}

impl<'data, D: LazyDecoder<'data>> ToArgumentKind<'data, D, Self> for Never {
    fn to_arg_expr<'top>(
        self,
        _context: EncodingContext<'top>,
    ) -> ArgumentKind<'top, 'data, D, Never>
    where
        Never: 'top,
        Self: 'top,
    {
        unreachable!("macro in Ion 1.0 (method: to_arg_expr)")
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroEvaluator<'top, 'data, D> for Never {
    type Stack = BumpVec<'top, MacroExpansion<'data, D, Never>>;
    type MacroInvocation = Never;

    fn stack(&self) -> &Self::Stack {
        unreachable!("macro in Ion 1.0 (method: stack)")
    }

    fn stack_mut(&mut self) -> &mut Self::Stack {
        unreachable!("macro in Ion 1.0 (method: stack_mut)")
    }
}
