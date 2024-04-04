use std::fmt::Debug;

use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr};
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::{
    AnnotatableValueWriter, MacroArgsWriter, SequenceWriter, StructWriter,
};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::expanded::macro_evaluator::{MacroExpr, RawEExpression};
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::raw_symbol_token_ref::{RawSymbolTokenRef, AsRawSymbolTokenRef};
use crate::IonResult;

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

impl Iterator for Never {
    type Item = IonResult<RawSymbolTokenRef<'static>>;

    fn next(&mut self) -> Option<Self::Item> {
        unreachable!("Never implementation cannot iterate")
    }
}

impl AnnotatableValueWriter for Never {
    type ValueWriter = Never;
    type AnnotatedValueWriter<'a, SymbolType: AsRawSymbolTokenRef + 'a> = Never where Self: 'a;

    fn with_annotations<'a, SymbolType: AsRawSymbolTokenRef>(
        self,
        _annotations: &'a [SymbolType],
    ) -> Self::AnnotatedValueWriter<'a, SymbolType>
    where
        Self: 'a,
    {
        unreachable!("AnnotatableValueWriter::with_annotations in Never")
    }

    fn without_annotations(self) -> Self::ValueWriter {
        unreachable!("AnnotatableValueWriter::without_annotations in Never")
    }
}

impl SequenceWriter for Never {}

impl StructWriter for Never {
    fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        _name: A,
        _value: V,
    ) -> IonResult<&mut Self> {
        unreachable!("StructWriter::write in Never")
    }
}

impl MakeValueWriter for Never {
    type ValueWriter<'a> = Never where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        unreachable!("MakeValueWriter::value_writer in Never")
    }
}

impl MacroArgsWriter for Never {}
