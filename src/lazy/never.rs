use std::fmt::Debug;

use crate::lazy::decoder::{LazyDecoder, LazyRawValueExpr};
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::{
    AnnotatableValueWriter, MacroArgsWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
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

impl ValueWriter for Never {
    type ListWriter<'a> = Never;
    type SExpWriter<'a> = Never;
    type StructWriter<'a> = Never;
    type MacroArgsWriter<'a> = Never;

    fn write_null(self, _ion_type: IonType) -> IonResult<()> {
        unreachable!("ValueWriter::write_null in Never")
    }

    fn write_bool(self, _value: bool) -> IonResult<()> {
        unreachable!("ValueWriter::write_bool in Never")
    }

    fn write_i64(self, _value: i64) -> IonResult<()> {
        unreachable!("ValueWriter::write_i64 in Never")
    }

    fn write_int(self, _value: &Int) -> IonResult<()> {
        unreachable!("ValueWriter::write_int in Never")
    }

    fn write_f32(self, _value: f32) -> IonResult<()> {
        unreachable!("ValueWriter::write_f32 in Never")
    }

    fn write_f64(self, _value: f64) -> IonResult<()> {
        unreachable!("ValueWriter::write_f64 in Never")
    }

    fn write_decimal(self, _value: &Decimal) -> IonResult<()> {
        unreachable!("ValueWriter::write_decimal in Never")
    }

    fn write_timestamp(self, _value: &Timestamp) -> IonResult<()> {
        unreachable!("ValueWriter::write_timestamp in Never")
    }

    fn write_string(self, _value: impl AsRef<str>) -> IonResult<()> {
        unreachable!("ValueWriter::write_string in Never")
    }

    fn write_symbol(self, _value: impl AsRawSymbolTokenRef) -> IonResult<()> {
        unreachable!("ValueWriter::write_symbol in Never")
    }

    fn write_clob(self, _value: impl AsRef<[u8]>) -> IonResult<()> {
        unreachable!("ValueWriter::write_clob in Never")
    }

    fn write_blob(self, _value: impl AsRef<[u8]>) -> IonResult<()> {
        unreachable!("ValueWriter::write_blob in Never")
    }

    fn write_list<F: for<'a> FnOnce(&mut Self::ListWriter<'a>) -> IonResult<()>>(
        self,
        _list_fn: F,
    ) -> IonResult<()> {
        unreachable!("ValueWriter::write_list in Never")
    }

    fn write_sexp<F: for<'a> FnOnce(&mut Self::SExpWriter<'a>) -> IonResult<()>>(
        self,
        _sexp_fn: F,
    ) -> IonResult<()> {
        unreachable!("ValueWriter::write_sexp in Never")
    }

    fn write_struct<F: for<'a> FnOnce(&mut Self::StructWriter<'a>) -> IonResult<()>>(
        self,
        _struct_fn: F,
    ) -> IonResult<()> {
        unreachable!("ValueWriter::write_struct in Never")
    }

    fn write_eexp<'macro_id, F: for<'a> FnOnce(&mut Self::MacroArgsWriter<'a>) -> IonResult<()>>(
        self,
        _macro_id: impl Into<MacroIdRef<'macro_id>>,
        _macro_fn: F,
    ) -> IonResult<()> {
        unreachable!("ValueWriter::write_eexp in Never")
    }
}
