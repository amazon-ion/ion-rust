use std::fmt::Debug;

use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr};
use crate::lazy::expanded::macro_evaluator::{
    ArgumentExpr, MacroExpr, MacroInvocation, RawMacroInvocation,
};
use crate::lazy::expanded::sequence::Environment;
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
impl<'data, D: LazyDecoder<'data>> RawMacroInvocation<'data, D> for Never {
    // These use Box<dyn> to avoid defining yet another placeholder type.
    type RawArgumentsIterator<'a> = Box<dyn Iterator<Item = IonResult<LazyRawValueExpr<'data, D>>>>;
    type MacroInvocation<'top> = Never where 'data: 'top;

    fn id(&self) -> MacroIdRef<'data> {
        unreachable!("macro in Ion 1.0 (method: id)")
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator<'_> {
        unreachable!("macro in Ion 1.0 (method: arguments)")
    }

    fn resolve<'top>(
        self,
        _context: EncodingContext<'top>,
    ) -> IonResult<Self::MacroInvocation<'top>>
    where
        'data: 'top,
    {
        unreachable!("macro in Ion 1.0 (method: resolve)")
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> From<Never> for MacroExpr<'top, 'data, D> {
    fn from(_value: Never) -> Self {
        unreachable!("macro in Ion 1.0 (method: into)")
    }
}

impl<'top, 'data: 'top, D: LazyDecoder<'data>> MacroInvocation<'top, 'data, D> for Never {
    type ArgumentsIterator = Box<dyn Iterator<Item = IonResult<ArgumentExpr<'top, 'data, D>>>>;

    fn id(&self) -> MacroIdRef<'data> {
        unreachable!("macro in Ion 1.0 (method: id)");
    }

    fn arguments(&self, _environment: Environment<'top, 'data, D>) -> Self::ArgumentsIterator {
        unreachable!("macro in Ion 1.0 (method: arguments)");
    }
}
