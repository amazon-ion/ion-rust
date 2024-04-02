use std::fmt::Debug;

use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr};
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{delegate_value_writer_to_self, ValueWriter};
use crate::lazy::encoder::value_writer::{EExpWriter, SequenceWriter, StructWriter};
use crate::lazy::expanded::macro_evaluator::{MacroExpr, RawEExpression};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{Decimal, Int, IonResult, IonType, Timestamp};

/// An uninhabited type that signals to the compiler that related code paths are not reachable.
#[derive(Debug, Copy, Clone)]
pub enum Never {
    // Has no variants, cannot be instantiated.
}

// Ion 1.0 uses `Never` as a placeholder type for MacroInvocation.
// The compiler should optimize these methods away.
impl<'top, D: LazyDecoder<EExpression<'top> = Self>> RawEExpression<'top, D> for Never {
    // These use Box<dyn> to avoid defining yet another placeholder type.
    type RawArgumentsIterator<'a> = Box<dyn Iterator<Item = IonResult<LazyRawValueExpr<'top, D>>>>;

    fn id(&self) -> MacroIdRef<'top> {
        unreachable!("macro in Ion 1.0 (method: id)")
    }

    fn raw_arguments(&self) -> Self::RawArgumentsIterator<'_> {
        unreachable!("macro in Ion 1.0 (method: arguments)")
    }
}

impl<'top, D: LazyDecoder> From<Never> for MacroExpr<'top, D> {
    fn from(_value: Never) -> Self {
        unreachable!("macro in Ion 1.0 (method: into)")
    }
}

impl SequenceWriter for Never {
    type End = ();

    fn end(self) -> IonResult<()> {
        unreachable!("SequenceWriter::end() in Never")
    }
}

impl FieldEncoder for Never {
    fn encode_field_name(&mut self, _name: impl AsRawSymbolTokenRef) -> IonResult<()> {
        unreachable!("FieldEncoder::encode_field_name in Never")
    }
}

impl StructWriter for Never {
    fn end(self) -> IonResult<()> {
        unreachable!("StructWriter::end in Never")
    }
}

impl MakeValueWriter for Never {
    type ValueWriter<'a> = Never where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        unreachable!("MakeValueWriter::value_writer in Never")
    }
}

impl EExpWriter for Never {}

impl ValueWriter for Never {
    type AnnotatedValueWriter<'a, SymbolType: AsRawSymbolTokenRef + 'a> = Never where Self: 'a;
    type ListWriter = Never;
    type SExpWriter = Never;
    type StructWriter = Never;
    type EExpWriter = Never;

    delegate_value_writer_to_self!();

    fn with_annotations<'a, SymbolType: 'a + AsRawSymbolTokenRef>(
        self,
        _annotations: &'a [SymbolType],
    ) -> Self::AnnotatedValueWriter<'a, SymbolType>
    where
        Self: 'a,
    {
        unreachable!("Never as MutRefValueWriter")
    }
}
