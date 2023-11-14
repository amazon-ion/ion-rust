#![allow(non_camel_case_types)]

pub mod annotate;
pub mod write_as_ion;

use delegate::delegate;
use std::fmt::Debug;
use std::io::Write;
use write_as_ion::WriteAsIon;

use crate::lazy::encoding::TextEncoding_1_0;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::text::raw_text_writer::{WhitespaceConfig, PRETTY_WHITESPACE_CONFIG};
use crate::{Decimal, Int, IonResult, IonType, RawSymbolTokenRef, RawTextWriter, Timestamp};

/// A family of types that collectively comprise the writer API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
// Implementations of this trait are typically unit structs that are never instantiated.
// However, many types are generic over some `E: LazyEncoder`, and having this trait
// extend 'static, Sized, Debug, Clone and Copy means that those types can #[derive(...)]
// those traits themselves without boilerplate `where` clauses.
pub trait LazyEncoder<W: Write>: 'static + Sized + Debug + Clone + Copy {
    // XXX: ^-- This is named 'Lazy' for symmetry with the `LazyDecoder`. In reality, there's nothing
    //      lazy about it. We should revisit the Lazy* naming scheme, as eventually it will be the
    //      only implementation of a reader and won't need the word 'Lazy' to distinguish itself.

    /// A writer that serializes Rust values as Ion, emitting the resulting data to an implementation
    /// of [`Write`].
    type Writer: LazyRawWriter<W, Self>;

    /// A single-use type that can emit an Ion value.
    type ValueWriter<'a>: ValueWriter<'a, W, Self>
    where
        W: 'a;

    /// A single-use type that can emit a sequence of annotations and then return a [`ValueWriter`].
    type AnnotatedValueWriter<'a>: AnnotatedValueWriter<'a, W, Self>
    where
        W: 'a;

    /// Allows the application to write a (potentially heterogeneously typed) list without necessarily
    /// having all of its child values in memory.
    type ListWriter<'a>: SequenceWriter<'a, W, Self>
    where
        W: 'a;

    // TODO: Apply trait constraints to the following associated types

    type SExpWriter<'a>;
    type StructWriter<'a>;
    type EExpressionWriter<'a>;
}

impl<W: Write> LazyEncoder<W> for TextEncoding_1_0 {
    type Writer = LazyRawTextWriter_1_0<W>;
    type ValueWriter<'a> = TextValueWriter_1_0<'a, W> where W: 'a;
    type AnnotatedValueWriter<'a> = TextAnnotatedValueWriter_1_0<'a, W> where W: 'a;
    type ListWriter<'a> = TextListWriter_1_0<'a, W> where W: 'a;
    type SExpWriter<'a> = ();
    type StructWriter<'a> = ();
    type EExpressionWriter<'a> = ();
}

/// One-shot methods that take a (possibly empty) sequence of annotations to encode and return a ValueWriter.
pub trait AnnotatedValueWriter<'a, W: Write, E: LazyEncoder<W>> {
    /// Writes the provided annotations to the output stream and returns a [`ValueWriter`] that can
    /// be used to serialize the value itself.
    ///
    /// If there are no annotations, use [`Self::no_annotations`] instead. This method will loop
    /// over the empty sequence, incurring minor performance overhead while `no_annotations`
    /// is a true no-op.
    fn write_annotations<
        SymbolType: AsRawSymbolTokenRef,
        IterType: Iterator<Item = SymbolType> + Clone,
    >(
        self,
        annotations: IterType,
    ) -> IonResult<E::ValueWriter<'a>>;

    /// Performs no operations and returns a [`ValueWriter`].
    fn no_annotations(self) -> E::ValueWriter<'a>;
}

pub trait ValueWriter<'a, W: Write, E: LazyEncoder<W>> {
    fn write_null(self, ion_type: IonType) -> IonResult<()>;
    fn write_bool(self, value: bool) -> IonResult<()>;
    fn write_i64(self, value: i64) -> IonResult<()>;
    fn write_int(self, value: &Int) -> IonResult<()>;
    fn write_f32(self, value: f32) -> IonResult<()>;
    fn write_f64(self, value: f64) -> IonResult<()>;
    fn write_decimal(self, value: &Decimal) -> IonResult<()>;
    fn write_timestamp(self, value: &Timestamp) -> IonResult<()>;
    fn write_string<A: AsRef<str>>(self, value: A) -> IonResult<()>;
    fn write_symbol<A: AsRawSymbolTokenRef>(self, value: A) -> IonResult<()>;
    fn write_clob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()>;
    fn write_blob<A: AsRef<[u8]>>(self, value: A) -> IonResult<()>;
    fn list_writer(self) -> IonResult<E::ListWriter<'a>>;
    fn sexp_writer(self) -> IonResult<E::StructWriter<'a>>;
    fn struct_writer(self) -> IonResult<E::StructWriter<'a>>;
}

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
    /// Writes a struct field using the provided name/value pair.
    fn write_field<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        name: A,
        value: &V,
    ) -> IonResult<()>;

    /// Finalizes the struct, preventing further fields from being written.
    fn end(self) -> IonResult<()>;
}

pub trait SequenceWriter<'a, W: Write, E: LazyEncoder<W>>: Sized {
    /// Writes a nested value within the list.
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;

    /// Finalizes the list, preventing further nested values from being written.
    fn end(self) -> IonResult<()>;
}

/// A raw text Ion 1.0 writer.
pub struct LazyRawTextWriter_1_0<W: Write> {
    output: W,
    whitespace_config: &'static WhitespaceConfig,
}

impl<W: Write> LazyRawTextWriter_1_0<W> {
    /// Constructs a new writer that will emit encoded data to the specified `output`.
    pub fn new(output: W) -> Self {
        Self {
            output,
            whitespace_config: &PRETTY_WHITESPACE_CONFIG,
        }
    }

    /// Writes the provided data as a top-level value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        value.write_as_ion(self.annotated_value_writer())?;
        write!(
            self.output,
            "{}",
            self.whitespace_config.space_between_top_level_values
        )?;
        Ok(self)
    }

    /// Writes any pending data to the output stream and then calls [`Write::flush`] on it.
    pub fn flush(&mut self) -> IonResult<()> {
        self.output.flush()?;
        Ok(())
    }

    /// Helper method to construct this format's `ValueWriter` implementation.
    #[inline]
    fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W> {
        TextValueWriter_1_0 {
            writer: self,
            depth: 0,
        }
    }

    /// Helper method to construct this format's `AnnotatedValueWriter` implementation.
    #[inline]
    fn annotated_value_writer(&mut self) -> TextAnnotatedValueWriter_1_0<'_, W> {
        TextAnnotatedValueWriter_1_0 {
            value_writer: self.value_writer(),
        }
    }

    #[inline]
    pub fn list_writer(&mut self) -> IonResult<TextListWriter_1_0<'_, W>> {
        self.value_writer().list_writer()
    }
}

impl<W: Write> LazyRawWriter<W, TextEncoding_1_0> for LazyRawTextWriter_1_0<W> {
    fn new(output: W) -> Self {
        LazyRawTextWriter_1_0::new(output)
    }
    // Delegate the trait methods to the inherent methods; this allows a version of these
    // methods to be called on the concrete type even when the trait is not in scope.
    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
            fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W>;
            fn flush(&mut self) -> IonResult<()>;
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
        self.writer.whitespace_config
    }
}

pub struct TextAnnotatedValueWriter_1_0<'a, W: Write> {
    value_writer: TextValueWriter_1_0<'a, W>,
}

impl<'a, W: Write> AnnotatedValueWriter<'a, W, TextEncoding_1_0>
    for TextAnnotatedValueWriter_1_0<'a, W>
{
    fn write_annotations<
        SymbolType: AsRawSymbolTokenRef,
        IterType: Iterator<Item = SymbolType> + Clone,
    >(
        self,
        annotations: IterType,
    ) -> IonResult<TextValueWriter_1_0<'a, W>> {
        let output = &mut self.value_writer.writer.output;
        let annotations = annotations.into_iter();
        for annotation in annotations {
            match annotation.as_raw_symbol_token_ref() {
                RawSymbolTokenRef::Text(token) => write!(output, "{}::", token.as_ref()),
                RawSymbolTokenRef::SymbolId(sid) => write!(output, "${sid}::"),
            }?;
        }
        Ok(self.value_writer)
    }

    fn no_annotations(self) -> TextValueWriter_1_0<'a, W> {
        self.value_writer
    }
}

impl<'a, W: Write> ValueWriter<'a, W, TextEncoding_1_0> for TextValueWriter_1_0<'a, W> {
    fn write_null(mut self, ion_type: IonType) -> IonResult<()> {
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

    fn write_bool(mut self, value: bool) -> IonResult<()> {
        let bool_text = match value {
            true => "true",
            false => "false",
        };
        write!(self.output(), "{bool_text}")?;
        Ok(())
    }

    fn write_i64(mut self, value: i64) -> IonResult<()> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_int(mut self, value: &Int) -> IonResult<()> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_f32(self, value: f32) -> IonResult<()> {
        self.write_f64(value as f64)
    }

    fn write_f64(mut self, value: f64) -> IonResult<()> {
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

    fn write_decimal(mut self, value: &Decimal) -> IonResult<()> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_timestamp(mut self, value: &Timestamp) -> IonResult<()> {
        write!(self.output(), "{value}")?;
        Ok(())
    }

    fn write_string<A: AsRef<str>>(mut self, value: A) -> IonResult<()> {
        write!(self.output(), "\"")?;
        RawTextWriter::<W>::write_escaped_text_body(self.output(), value)?;
        write!(self.output(), "\"")?;
        Ok(())
    }

    fn write_symbol<A: AsRawSymbolTokenRef>(mut self, value: A) -> IonResult<()> {
        RawTextWriter::<W>::write_symbol_token(self.output(), value)?;
        Ok(())
    }

    fn write_clob<A: AsRef<[u8]>>(self, _value: A) -> IonResult<()> {
        todo!()
    }

    fn write_blob<A: AsRef<[u8]>>(mut self, value: A) -> IonResult<()> {
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

    fn sexp_writer(self) -> IonResult<<TextEncoding_1_0 as LazyEncoder<W>>::StructWriter<'a>> {
        todo!()
    }

    fn struct_writer(self) -> IonResult<<TextEncoding_1_0 as LazyEncoder<W>>::StructWriter<'a>> {
        todo!()
    }
}

/// Incrementally encodes a potentially homogeneously typed Ion list.
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
    /// Writes the provided data as a nested value.
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let indentation = self.whitespace_config().indentation;
        if !indentation.is_empty() {
            for _ in 0..self.depth {
                write!(self.output(), "{indentation}")?;
            }
        }
        value.write_as_ion(self.annotated_value_writer())?;
        let space_between_nested_values = self.whitespace_config().space_between_nested_values;
        write!(self.output(), ",{space_between_nested_values}")?;
        Ok(self)
    }

    /// Finalizes the list, preventing further values from being written.
    fn end(mut self) -> IonResult<()> {
        let space_between_top_level_values =
            self.whitespace_config().space_between_top_level_values;
        write!(self.output(), "]{space_between_top_level_values}")?;
        self.has_been_closed = true;
        Ok(())
    }

    fn output(&mut self) -> &mut W {
        &mut self.writer.output
    }

    fn whitespace_config(&self) -> &WhitespaceConfig {
        self.writer.whitespace_config
    }

    #[inline]
    fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W> {
        TextValueWriter_1_0 {
            writer: self.writer,
            depth: self.depth,
        }
    }

    #[inline]
    fn annotated_value_writer(&mut self) -> TextAnnotatedValueWriter_1_0<'_, W> {
        TextAnnotatedValueWriter_1_0 {
            value_writer: self.value_writer(),
        }
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
            fn end(self) -> IonResult<()>;
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoder::annotate::Annotate;
    use crate::lazy::encoder::LazyRawTextWriter_1_0;
    use crate::symbol_ref::AsSymbolRef;
    use crate::{Element, IonData, IonResult, Timestamp};

    fn writer_test(
        expected: &str,
        mut test: impl FnMut(&mut LazyRawTextWriter_1_0<&mut Vec<u8>>) -> IonResult<()>,
    ) -> IonResult<()> {
        let expected = Element::read_all(expected)?;
        let mut buffer = Vec::new();
        let mut writer = LazyRawTextWriter_1_0::new(&mut buffer);
        test(&mut writer)?;
        writer.flush()?;
        let actual = Element::read_all(buffer)?;
        assert!(IonData::eq(&expected, &actual));
        Ok(())
    }

    #[test]
    fn write_scalars() -> IonResult<()> {
        let expected = r#"
            1
            false
            3e0
            "foo"
            bar
            2023-11-09T
            {{4AEA6g==}}
            [1, 2, 3]
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            writer
                .write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write("bar".as_symbol_ref())?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write([0xE0u8, 0x01, 0x00, 0xEA])?
                .write([1, 2, 3])?;
            Ok(())
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_annotated_scalars() -> IonResult<()> {
        let expected = r#"
            foo::bar::1
            quux::quuz::gary::false
            Mercury::Venus::3e0
            Earth::"foo"
            Mars::Jupiter::bar
            Saturn::2023-11-09T
            Uranus::{{4AEA6g==}}
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            writer
                .write(1.annotate(&["foo", "bar"]))?
                .write(false.annotate(&["quux", "quuz", "gary"]))?
                .write(3f32.annotate(&["Mercury", "Venus"]))?
                .write("foo".annotate(&["Earth"]))?
                .write("bar".as_symbol_ref().annotate(&["Mars", "Jupiter"]))?
                .write(
                    Timestamp::with_ymd(2023, 11, 9)
                        .build()?
                        .annotate(&["Saturn"]),
                )?
                .write((&[0xE0u8, 0x01, 0x00, 0xEA][..]).annotate(&["Uranus"]))?;
            Ok(())
        };
        writer_test(expected, test)
    }

    #[test]
    fn write_list() -> IonResult<()> {
        let expected = r#"
            [
              1,
              false,
              3e0,
              "foo",
              bar,
              2023-11-09T,
              {{4AEA6g==}},
            ]
        "#;
        let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
            let mut list = writer.list_writer()?;
            list.write(1)?
                .write(false)?
                .write(3f32)?
                .write("foo")?
                .write("bar".as_symbol_ref())?
                .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
                .write(&[0xE0u8, 0x01, 0x00, 0xEA][..])?;
            list.end()?;
            Ok(())
        };
        writer_test(expected, test)
    }
}
