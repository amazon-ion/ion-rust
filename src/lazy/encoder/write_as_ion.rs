//! Defines traits that allow Rust values to be serialized as Ion.
//!
//! In order for a [`LazyRawWriter`](crate::lazy::encoder::LazyRawWriter) to serialize a Rust value
//! as Ion, that Rust type must implement [`WriteAsIonValue`] and may optionally also
//! implement [`WriteAsIon`].
//!
//! [`WriteAsIonValue`] allows the implementor to map the Rust value to an unannotated Ion value.
//!
//! [`WriteAsIon`] builds on [`WriteAsIonValue`], offering a staged writer that requires the
//! implementor to specify what annotations to write before delegating to [`WriteAsIonValue`]
//! to serialize the value itself.
//!
//! Types that do not explicitly implement [`WriteAsIon`] will fall back to a blanket implementation
//! that uses an empty annotations sequence. A custom annotations sequence can be set on a per-value
//! basis by using the [`annotate`](crate::lazy::encoder::annotate::Annotate::annotate) method
//! provided by the [`Annotate`](crate::lazy::encoder::annotate::Annotate) trait.
use crate::lazy::encoder::{AnnotatedValueWriter, LazyEncoder, SequenceWriter, ValueWriter};
use crate::{
    Blob, Clob, Decimal, Int, IonResult, Null, RawSymbolToken, RawSymbolTokenRef, Symbol,
    SymbolRef, Timestamp,
};
use std::io::Write;

/// Defines how a Rust type should be serialized as Ion in terms of the methods available
/// on [`ValueWriter`].
pub trait WriteAsIonValue {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()>;
}

/// Defines how a Rust type should be serialized as Ion in terms of the methods available
/// on [`AnnotatedValueWriter`] and [`ValueWriter`].
pub trait WriteAsIon {
    fn write_as_ion<'a, W: Write + 'a, E: LazyEncoder<W>, V: AnnotatedValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()>;
}

// Any type that does not define `WriteAsIon` itself will use this blanket implementation that does
// not write any annotations.
impl<T> WriteAsIon for T
where
    T: WriteAsIonValue,
{
    fn write_as_ion<'a, W: Write + 'a, E: LazyEncoder<W>, V: AnnotatedValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        self.write_as_ion_value(writer.no_annotations())
    }
}

// ===== WriteAsIonValue implementations for common types =====

impl WriteAsIonValue for Null {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_null(self.0)
    }
}

impl WriteAsIonValue for bool {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_bool(*self)
    }
}

impl WriteAsIonValue for i32 {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_i64(*self as i64)
    }
}

impl WriteAsIonValue for i64 {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_i64(*self)
    }
}

impl WriteAsIonValue for usize {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_int(&Int::from(*self))
    }
}

impl WriteAsIonValue for f32 {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_f32(*self)
    }
}

impl WriteAsIonValue for f64 {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_f64(*self)
    }
}

impl WriteAsIonValue for Decimal {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_decimal(self)
    }
}

impl WriteAsIonValue for Timestamp {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_timestamp(self)
    }
}

impl WriteAsIonValue for Symbol {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_symbol(self)
    }
}

impl<'b> WriteAsIonValue for RawSymbolTokenRef<'b> {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_symbol(self)
    }
}

impl<'b> WriteAsIonValue for SymbolRef<'b> {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_symbol(self)
    }
}

impl WriteAsIonValue for RawSymbolToken {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_symbol(self)
    }
}

impl<'b> WriteAsIonValue for &'b str {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_string(self)
    }
}

impl WriteAsIonValue for String {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_string(self)
    }
}

impl<'b> WriteAsIonValue for &'b [u8] {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_blob(self)
    }
}

impl<const N: usize> WriteAsIonValue for [u8; N] {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_blob(self)
    }
}

impl WriteAsIonValue for Blob {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_blob(self)
    }
}

impl WriteAsIonValue for Clob {
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        writer.write_clob(self)
    }
}

impl<T> WriteAsIonValue for &T
where
    T: WriteAsIonValue,
{
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        (*self).write_as_ion_value(writer)
    }
}

impl<T> WriteAsIonValue for &[T]
where
    for<'x> &'x T: WriteAsIon,
{
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        let mut list = writer.list_writer()?;
        for value in *self {
            list.write(value)?;
        }
        list.end()?;
        Ok(())
    }
}

impl<T, const N: usize> WriteAsIonValue for [T; N]
where
    T: WriteAsIonValue,
{
    fn write_as_ion_value<'a, W: Write + 'a, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<()> {
        let mut list = writer.list_writer()?;
        for value in self {
            list.write(value)?;
        }
        list.end()?;
        Ok(())
    }
}
