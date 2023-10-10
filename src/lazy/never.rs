use std::fmt::Debug;

use crate::lazy::decoder::{LazyDecoder, RawArgumentExpr};
use crate::lazy::expanded::macro_evaluator::{
    ArgumentKind, MacroEvaluator, MacroExpansion, MacroInvocation, MacroStack, ToArgumentKind,
};
use crate::lazy::expanded::sequence::Environment;
use crate::lazy::expanded::stack::{BumpVecStack, Stack};
use crate::lazy::expanded::EncodingContext;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::IonResult;

/// An uninhabited type that signals to the compiler that related code paths are not reachable.
#[derive(Debug, Copy, Clone)]
pub enum Never {
    // Has no variants, cannot be instantiated.
}

// Ion 1.0 uses `Never` as a placeholder type for MacroInvocation.
// The compiler should optimize these methods away.
impl<'data, D: LazyDecoder<'data>> MacroInvocation<'data, D> for Never {
    type ArgumentExpr = Never;
    // These use Box<dyn> to avoid defining yet another placeholder type.
    type ArgumentsIterator = Box<dyn Iterator<Item = IonResult<Never>>>;
    type RawArgumentsIterator = Box<dyn Iterator<Item = RawArgumentExpr<'data, D>>>;

    type TransientEvaluator<'context> = Never  where Self: 'context, 'data: 'context;

    fn id(&self) -> MacroIdRef<'_> {
        unreachable!("macro in Ion 1.0 (method: id)")
    }

    fn arguments(&self) -> Self::ArgumentsIterator {
        unreachable!("macro in Ion 1.0 (method: arguments)")
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator {
        unreachable!("macro in Ion 1.0 (method: raw_arguments)")
    }

    fn make_transient_evaluator<'context>(
        _context: EncodingContext<'context>,
        _environment: Environment<'context, 'data, D>,
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
        _environment: Environment<'top, 'data, D>,
    ) -> ArgumentKind<'top, 'data, D, Never>
    where
        Never: 'top,
        Self: 'top,
    {
        unreachable!("macro in Ion 1.0 (method: to_arg_expr)")
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroEvaluator<'top, 'data, D> for Never {
    type MacroInvocation = Never;
    fn macro_stack(&self) -> &MacroStack<'top, 'data, D, Never> {
        unreachable!("macro in Ion 1.0 (method: macro_stack)")
    }

    fn macro_stack_mut(&mut self) -> &mut MacroStack<'top, 'data, D, Never> {
        unreachable!("macro in Ion 1.0 (method: macro_stack_mut)")
    }

    fn environment(&self) -> Environment<'top, 'data, D> {
        unreachable!("macro in Ion 1.0 (method: environment)")
    }

    fn environment_mut(&mut self) -> &mut Environment<'top, 'data, D> {
        unreachable!("macro in Ion 1.0 (method: environment_mut)")
    }

    // fn arg_stack(&self) -> &<Self::Stack as Stack>::Storage<'top, RawArgumentExpr<'data, D>> {
    //     unreachable!("macro in Ion 1.0 (method: arg_stack)")
    // }
    //
    // fn arg_stack_mut(
    //     &mut self,
    // ) -> &mut <Self::Stack as Stack>::Storage<'top, RawArgumentExpr<'data, D>> {
    //     unreachable!("macro in Ion 1.0 (method: arg_stack_mut)")
    // }
}
