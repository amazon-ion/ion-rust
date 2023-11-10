#![allow(non_camel_case_types)]

use delegate::delegate;
use std::fmt::Debug;
use std::io::Write;

use crate::lazy::encoding::TextEncoding_1_0;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::text::raw_text_writer::{WhitespaceConfig, PRETTY_WHITESPACE_CONFIG};
use crate::{
    Blob, Clob, Decimal, Int, IonResult, IonType, RawSymbolToken, RawSymbolTokenRef, RawTextWriter,
    Symbol, SymbolRef, Timestamp,
};

// XXX: This is named 'Lazy' for symmetry with the `LazyDecoder`. In reality, there's nothing
//      lazy about it. We should revisit the Lazy* naming scheme, as eventually it will be the
//      only implementation of a reader and won't need the word 'Lazy' to distinguish itself.
pub trait LazyEncoder<W: Write>: 'static + Sized + Debug + Clone + Copy {
    type Writer: LazyRawWriter<W, Self>;
    type ValueWriter<'a>: ValueWriter<'a, W, Self>
    where
        W: 'a;
    type ListWriter<'a>: SequenceWriter<'a, W, Self>
    where
        W: 'a;
    // type SExpWriter<'a>: SequenceWriter<'a, W, Self>;
    // type StructWriter<'a>: StructWriter<'a, W, Self>;
    // type AnnotationsWriter<'a>: AnnotationsWriter<'a, W, Self>;
    // type EExpressionWriter; // TODO: Trait for this

    type SExpWriter<'a>;
    type StructWriter<'a>;
    type AnnotationsWriter<'a>;
    type EExpressionWriter<'a>;
}

impl<W: Write> LazyEncoder<W> for TextEncoding_1_0 {
    type Writer = LazyRawTextWriter_1_0<W>;
    type ValueWriter<'a> = TextValueWriter_1_0<'a, W> where W: 'a;
    type ListWriter<'a> = TextListWriter_1_0<'a, W> where W: 'a;
    type SExpWriter<'a> = ();
    type StructWriter<'a> = ();
    type AnnotationsWriter<'a> = ();
    type EExpressionWriter<'a> = ();
}

pub trait ValueWriter<'a, W: Write, E: LazyEncoder<W>> {
    type Output;

    fn write_null(self, ion_type: IonType) -> IonResult<Self::Output>;
    fn write_bool(self, value: bool) -> IonResult<Self::Output>;
    fn write_i64(self, value: i64) -> IonResult<Self::Output>;
    fn write_int(self, value: &Int) -> IonResult<Self::Output>;
    fn write_f32(self, value: f32) -> IonResult<Self::Output>;
    fn write_f64(self, value: f64) -> IonResult<Self::Output>;
    fn write_decimal(self, value: &Decimal) -> IonResult<Self::Output>;
    fn write_timestamp(self, value: &Timestamp) -> IonResult<Self::Output>;
    fn write_string<A: AsRef<str>>(self, value: A) -> IonResult<Self::Output>;
    fn write_symbol<A: AsRawSymbolTokenRef>(self, value: A) -> IonResult<Self::Output>;
    fn write_clob<A: AsRef<[u8]>>(self, value: A) -> IonResult<Self::Output>;
    fn write_blob<A: AsRef<[u8]>>(self, value: A) -> IonResult<Self::Output>;
    fn list_writer(self) -> IonResult<E::ListWriter<'a>>;
    fn sexp_writer(self) -> IonResult<E::StructWriter<'a>>;
    fn struct_writer(self) -> IonResult<E::StructWriter<'a>>;
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoder::{LazyRawTextWriter_1_0, LazyRawWriter, SequenceWriter, ValueWriter};
    use crate::symbol_ref::AsSymbolRef;
    use crate::{IonResult, Timestamp};

    #[test]
    fn write_scalars() -> IonResult<()> {
        let mut buffer = Vec::new();
        let writer = LazyRawTextWriter_1_0::new(&mut buffer)
            .write(1)?
            .write(false)?
            .write(3f32)?
            .write("foo")?
            .write("bar".as_symbol_ref())?
            .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
            .write(&[0xE0u8, 0x01, 0x00, 0xEA][..])?
            .flush()?;
        let text = String::from_utf8(buffer).unwrap();
        println!("// output:\n{text}");
        Ok(())
    }

    #[test]
    fn write_list() -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut writer = LazyRawTextWriter_1_0::new(&mut buffer);
        let mut list = writer.list_writer()?;
        list.write(1)?
            .write(false)?
            .write(3f32)?
            .write("foo")?
            .write("bar".as_symbol_ref())?
            .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
            .write(&[0xE0u8, 0x01, 0x00, 0xEA][..])?;
        list.end()?;
        writer.flush()?;
        let text = String::from_utf8(buffer).unwrap();
        println!("// output:\n{text}");
        Ok(())
    }
}

pub trait AnnotationsWriter<'a, W: Write, E: LazyEncoder<W>> {}

pub trait LazyRawWriter<W: Write, E: LazyEncoder<W>> {
    fn new(output: W) -> Self;
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;

    fn value_writer(&mut self) -> E::ValueWriter<'_>;

    fn list_writer(&mut self) -> IonResult<E::ListWriter<'_>> {
        self.value_writer().list_writer()
    }
    fn flush(&mut self) -> IonResult<()>;
}

pub trait StructWriter<'a, W: Write, E: LazyEncoder<W>> {
    type Output;

    fn write_field<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        name: A,
        value: &V,
    ) -> Self::Output;
    fn end(self) -> IonResult<()>;
}

pub trait SequenceWriter<'a, W: Write, E: LazyEncoder<W>>: Sized {
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
    fn end(self) -> IonResult<()>;
}

pub struct LazyRawTextWriter_1_0<W: Write> {
    output: W,
    whitespace_config: &'static WhitespaceConfig,
}

impl<W: Write> LazyRawTextWriter_1_0<W> {
    #[inline]
    fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W> {
        TextValueWriter_1_0 {
            writer: self,
            depth: 0,
        }
    }

    fn list_writer(&mut self) -> IonResult<TextListWriter_1_0<'_, W>> {
        self.value_writer().list_writer()
    }

    fn new(output: W) -> Self {
        Self {
            output,
            whitespace_config: &PRETTY_WHITESPACE_CONFIG,
        }
    }

    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        value.write_as_ion(self.value_writer())?;
        write!(
            self.output,
            "{}",
            self.whitespace_config.space_between_top_level_values
        )?;
        Ok(self)
    }

    fn flush(&mut self) -> IonResult<()> {
        self.output.flush()?;
        Ok(())
    }
}

impl<W: Write> LazyRawWriter<W, TextEncoding_1_0> for LazyRawTextWriter_1_0<W> {
    fn new(output: W) -> Self {
        LazyRawTextWriter_1_0::new(output)
    }
    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
            fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W>;
            fn flush(&mut self) -> IonResult<()>;
        }
    }
}

pub struct TextListWriter_1_0<'a, W: Write> {
    writer: &'a mut LazyRawTextWriter_1_0<W>,
    depth: usize,
    // The compiler prevents the list writer from being used after `end()` is called.
    // However, if the user does not call `end()` and the writer goes out of scope, the output
    // buffer may be left with invalid Ion. This flag is checked in the `Drop` impl to prevent that
    // from happening quietly.
    has_been_closed: bool,
}

impl<'a, W: Write> TextListWriter_1_0<'a, W> {
    pub fn new(writer: &'a mut LazyRawTextWriter_1_0<W>, depth: usize) -> IonResult<Self> {
        let space_after_container_start = writer.whitespace_config.space_after_container_start;
        write!(writer.output, "[{space_after_container_start}")?;
        Ok(Self {
            writer,
            depth,
            has_been_closed: false,
        })
    }
}

impl<'a, W: Write> TextListWriter_1_0<'a, W> {
    fn output(&mut self) -> &mut W {
        &mut self.writer.output
    }

    fn whitespace_config(&self) -> &WhitespaceConfig {
        &self.writer.whitespace_config
    }

    #[inline]
    fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W> {
        TextValueWriter_1_0 {
            writer: self.writer,
            depth: self.depth,
        }
    }

    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let indentation = self.whitespace_config().indentation;
        if !indentation.is_empty() {
            for _ in 0..self.depth {
                write!(self.output(), "{indentation}")?;
            }
        }
        value.write_as_ion(self.value_writer())?;
        let space_between_nested_values = self.whitespace_config().space_between_nested_values;
        write!(self.output(), ",{space_between_nested_values}")?;
        Ok(self)
    }

    fn end(mut self) -> IonResult<()> {
        let space_between_top_level_values =
            self.whitespace_config().space_between_top_level_values;
        write!(self.output(), "]{space_between_top_level_values}")?;
        self.has_been_closed = true;
        Ok(())
    }
}

impl<'a, W: Write> Drop for TextListWriter_1_0<'a, W> {
    fn drop(&mut self) {
        // If the user didn't call `end`, the closing delimiter was not written to output.
        // It's too late to call it here because we can't return a Result.
        if !self.has_been_closed {
            panic!("List writer was dropped without calling `end()`.");
        }
    }
}

impl<'a, W: Write, E: LazyEncoder<W>> SequenceWriter<'a, W, E> for TextListWriter_1_0<'a, W> {
    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
            fn end(mut self) -> IonResult<()>;
        }
    }
}

pub struct TextValueWriter_1_0<'a, W: Write> {
    writer: &'a mut LazyRawTextWriter_1_0<W>,
    depth: usize,
}

impl<'a, W: Write> TextValueWriter_1_0<'a, W> {
    fn output(&mut self) -> &mut W {
        &mut self.writer.output
    }

    fn whitespace_config(&self) -> &WhitespaceConfig {
        &self.writer.whitespace_config
    }
}

impl<'a, W: Write> ValueWriter<'a, W, TextEncoding_1_0> for TextValueWriter_1_0<'a, W> {
    type Output = ();

    fn write_null(mut self, ion_type: IonType) -> IonResult<Self::Output> {
        use IonType::*;
        let null_text = match ion_type {
            Null => "null",
            Bool => "null.bool",
            Int => "null.int",
            Float => "null.float",
            Decimal => "null.decimal",
            Timestamp => "null.timestamp",
            Symbol => "null.symbol",
            String => "null.string",
            Blob => "null.blob",
            Clob => "null.clob",
            List => "null.list",
            SExp => "null.sexp",
            Struct => "null.struct",
        };
        write!(self.output(), "{null_text}")?;
        Ok(())
    }

    fn write_bool(mut self, value: bool) -> IonResult<Self::Output> {
        let bool_text = match value {
            true => "true",
            false => "false",
        };
        write!(self.output(), "{bool_text}")?;
        Ok(())
    }

    fn write_i64(mut self, value: i64) -> IonResult<Self::Output> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_int(mut self, value: &Int) -> IonResult<Self::Output> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_f32(mut self, value: f32) -> IonResult<Self::Output> {
        self.write_f64(value as f64)
    }

    fn write_f64(mut self, value: f64) -> IonResult<Self::Output> {
        if value.is_nan() {
            write!(self.output(), "nan")?;
            return Ok(());
        }

        if value.is_infinite() {
            if value.is_sign_positive() {
                write!(self.output(), "+inf")?;
            } else {
                write!(self.output(), "-inf")?;
            }
            return Ok(());
        }

        // The {:e} formatter provided by the Display trait writes floats using scientific
        // notation. It works for all floating point values except -0.0 (it drops the sign).
        // See: https://github.com/rust-lang/rust/issues/20596
        if value == 0.0f64 && value.is_sign_negative() {
            write!(self.output(), "-0e0")?;
            return Ok(());
        }

        write!(self.output(), "{value:e}")?;
        Ok(())
    }

    fn write_decimal(mut self, value: &Decimal) -> IonResult<Self::Output> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_timestamp(mut self, value: &Timestamp) -> IonResult<Self::Output> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_string<A: AsRef<str>>(mut self, value: A) -> IonResult<Self::Output> {
        write!(self.output(), "\"")?;
        RawTextWriter::<W>::write_escaped_text_body(self.output(), value)?;
        write!(self.output(), "\"")?;
        Ok(())
    }

    fn write_symbol<A: AsRawSymbolTokenRef>(mut self, value: A) -> IonResult<Self::Output> {
        RawTextWriter::<W>::write_symbol_token(self.output(), value)?;
        Ok(())
    }

    fn write_clob<A: AsRef<[u8]>>(self, _value: A) -> IonResult<Self::Output> {
        todo!()
    }

    fn write_blob<A: AsRef<[u8]>>(mut self, value: A) -> IonResult<Self::Output> {
        // Rust format strings escape curly braces by doubling them. The following string is:
        // * The opening {{ from a text Ion blob, with each brace doubled to escape it.
        // * A {} pair used by the format string to indicate where the base64-encoded bytes
        //   should be inserted.
        // * The closing }} from a text Ion blob, with each brace doubled to escape it.
        write!(self.output(), "{{{{{}}}}}", base64::encode(value))?;
        Ok(())
    }

    fn list_writer(self) -> IonResult<<TextEncoding_1_0 as LazyEncoder<W>>::ListWriter<'a>> {
        TextListWriter_1_0::new(self.writer, self.depth + 1)
    }

    fn sexp_writer(mut self) -> IonResult<<TextEncoding_1_0 as LazyEncoder<W>>::StructWriter<'a>> {
        todo!()
    }

    fn struct_writer(
        mut self,
    ) -> IonResult<<TextEncoding_1_0 as LazyEncoder<W>>::StructWriter<'a>> {
        todo!()
    }
}

pub trait WriteAsIon {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output>;
}

// TODO: impl WithAnnotations for T where T: WriteAsIon

pub struct Null(IonType);

impl WriteAsIon for Null {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_null(self.0)
    }
}

impl WriteAsIon for bool {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_bool(*self)
    }
}

impl WriteAsIon for i32 {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_i64(*self as i64)
    }
}

impl WriteAsIon for i64 {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_i64(*self)
    }
}

impl WriteAsIon for usize {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_int(&Int::from(*self))
    }
}

impl WriteAsIon for f32 {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_f32(*self)
    }
}

impl WriteAsIon for f64 {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_f64(*self)
    }
}

impl WriteAsIon for Decimal {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_decimal(self)
    }
}

impl WriteAsIon for Timestamp {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_timestamp(self)
    }
}

impl WriteAsIon for Symbol {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_symbol(self)
    }
}

impl<'b> WriteAsIon for RawSymbolTokenRef<'b> {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_symbol(self)
    }
}

impl<'b> WriteAsIon for SymbolRef<'b> {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_symbol(self)
    }
}

impl WriteAsIon for RawSymbolToken {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_symbol(self)
    }
}

impl<'b> WriteAsIon for &'b str {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_string(self)
    }
}

impl<'b> WriteAsIon for String {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_string(self)
    }
}

impl<'b> WriteAsIon for &'b [u8] {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_blob(self)
    }
}

impl<'b> WriteAsIon for Blob {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_blob(self)
    }
}

impl<'b> WriteAsIon for Clob {
    fn write_as_ion<'a, W: Write, E: LazyEncoder<W>, V: ValueWriter<'a, W, E>>(
        &self,
        writer: V,
    ) -> IonResult<V::Output> {
        writer.write_clob(self)
    }
}
