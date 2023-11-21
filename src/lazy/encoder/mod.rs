#![allow(non_camel_case_types)]

use std::fmt::Debug;
use std::io::Write;

use delegate::delegate;
use value_writer::{AnnotatableValueWriter, MakeValueWriter, SequenceWriter, StructWriter};

use write_as_ion::WriteAsIon;

use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoding::TextEncoding_1_0;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::text::raw_text_writer::{WhitespaceConfig, PRETTY_WHITESPACE_CONFIG};
use crate::{IonResult, IonType, RawSymbolTokenRef, RawTextWriter};

pub mod annotate;
pub mod binary;
mod value_writer;
pub mod write_as_ion;

/// A family of types that collectively comprise the writer API for an Ion serialization
/// format. These types operate at the 'raw' level; they do not attempt to resolve symbols
/// using the active symbol table.
// Implementations of this trait are typically unit structs that are never instantiated.
// However, many types are generic over some `E: LazyEncoder`, and having this trait
// extend 'static, Sized, Debug, Clone and Copy means that those types can #[derive(...)]
// those traits themselves without boilerplate `where` clauses.
pub trait LazyEncoder: 'static + Sized + Debug + Clone + Copy {
    // XXX: ^-- This is named 'Lazy' for symmetry with the `LazyDecoder`. In reality, there's nothing
    //      lazy about it. We should revisit the Lazy* naming scheme, as eventually it will be the
    //      only implementation of a reader and won't need the word 'Lazy' to distinguish itself.

    /// A writer that serializes Rust values as Ion, emitting the resulting data to an implementation
    /// of [`Write`].
    type Writer<W: Write>: LazyRawWriter<W>;
}

impl LazyEncoder for TextEncoding_1_0 {
    type Writer<W: Write> = LazyRawTextWriter_1_0<W>;
}

pub(crate) mod private {
    /// Prevents types outside the crate from implementing traits that extend it.
    pub trait Sealed {}
}

pub trait LazyRawWriter<W: Write>: SequenceWriter {
    fn new(output: W) -> IonResult<Self>
    where
        Self: Sized;
    fn flush(&mut self) -> IonResult<()>;
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
        value.write_as_ion(self.annotatable_value_writer())?;
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
    fn annotatable_value_writer(&mut self) -> TextAnnotatableValueWriter_1_0<'_, W> {
        TextAnnotatableValueWriter_1_0 {
            value_writer: self.value_writer(),
        }
    }
}

impl<W: Write> SequenceWriter for LazyRawTextWriter_1_0<W> {
    // All default method impls
}

impl<W: Write> MakeValueWriter for LazyRawTextWriter_1_0<W> {
    type ValueWriter<'a> = TextAnnotatableValueWriter_1_0<'a, W>
    where
        Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        let value_writer = TextValueWriter_1_0 {
            writer: self,
            depth: 0,
        };
        TextAnnotatableValueWriter_1_0 { value_writer }
    }
}

impl<W: Write> LazyRawWriter<W> for LazyRawTextWriter_1_0<W> {
    fn new(output: W) -> IonResult<Self> {
        Ok(LazyRawTextWriter_1_0::new(output))
    }

    // Delegate the trait methods to the inherent methods; this allows a version of these
    // methods to be called on the concrete type even when the trait is not in scope.
    delegate! {
        to self {
            fn flush(&mut self) -> IonResult<()>;
        }
    }
}

pub struct TextValueWriter_1_0<'value, W: Write + 'value> {
    writer: &'value mut LazyRawTextWriter_1_0<W>,
    depth: usize,
}

impl<'value, W: Write> TextValueWriter_1_0<'value, W> {
    fn output(&mut self) -> &mut W {
        &mut self.writer.output
    }

    fn whitespace_config(&self) -> &WhitespaceConfig {
        self.writer.whitespace_config
    }
}

pub struct TextAnnotatableValueWriter_1_0<'value, W: Write> {
    value_writer: TextValueWriter_1_0<'value, W>,
}

impl<'value, W: Write> AnnotatableValueWriter for TextAnnotatableValueWriter_1_0<'value, W> {
    type ValueWriter = TextValueWriter_1_0<'value, W>;
    type AnnotatedValueWriter<'a, SymbolType: AsRawSymbolTokenRef + 'a> =
    TextAnnotatedValueWriter_1_0<'a, W, SymbolType> where Self: 'a;
    fn with_annotations<'a, SymbolType: AsRawSymbolTokenRef>(
        self,
        annotations: &'a [SymbolType],
    ) -> Self::AnnotatedValueWriter<'a, SymbolType>
    where
        Self: 'a,
    {
        TextAnnotatedValueWriter_1_0 {
            annotations,
            value_writer: self.value_writer,
        }
    }

    fn without_annotations(self) -> TextValueWriter_1_0<'value, W> {
        self.value_writer
    }
}

pub struct TextAnnotatedValueWriter_1_0<'value, W: Write, SymbolType: AsRawSymbolTokenRef + 'value>
{
    annotations: &'value [SymbolType],
    value_writer: TextValueWriter_1_0<'value, W>,
}

impl<'value, W: Write, SymbolType: AsRawSymbolTokenRef>
    TextAnnotatedValueWriter_1_0<'value, W, SymbolType>
{
    fn encode_annotations(self) -> IonResult<TextValueWriter_1_0<'value, W>> {
        let output = &mut self.value_writer.writer.output;
        for annotation in self.annotations {
            match annotation.as_raw_symbol_token_ref() {
                RawSymbolTokenRef::Text(token) => write!(output, "{}::", token.as_ref()),
                RawSymbolTokenRef::SymbolId(sid) => write!(output, "${sid}::"),
            }?;
        }

        Ok(self.value_writer)
    }
}

impl<'value, W: Write + 'value, SymbolType: AsRawSymbolTokenRef> Sealed
    for TextAnnotatedValueWriter_1_0<'value, W, SymbolType>
{
}

impl<'value, W: Write> Sealed for TextValueWriter_1_0<'value, W> {}

/// Helper type that is home to information and behavior common to the list writer, s-expression writer,
/// and struct writer.
struct TextContainerWriter_1_0<'a, W: Write> {
    // Holds a reference to the output stream and a whitespace config
    writer: &'a mut LazyRawTextWriter_1_0<W>,
    // The depth at which this container's child values appear. This value is used for formatting
    // indentation where applicable.
    depth: usize,
    // Tracks whether the `end()` method was called (thereby emitting a closing delimiter) before
    // this value was dropped. This scenario is a contract violation and results in a panic.
    has_been_closed: bool,
    // The Ion type of the container using this TextContainerWriter_1_0. This value is only
    // used for more informative error messages.
    ion_type: IonType,
}

impl<'a, W: Write> Drop for TextContainerWriter_1_0<'a, W> {
    fn drop(&mut self) {
        // If the user didn't call `end`, the closing delimiter was not written to output.
        // It's too late to call it here because we can't return a `Result`.
        if !self.has_been_closed {
            panic!(
                "Container writer ({}) was dropped without calling `end()`.",
                self.ion_type
            );
        }
    }
}

impl<'a, W: Write> TextContainerWriter_1_0<'a, W> {
    pub fn new(
        writer: &'a mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        ion_type: IonType,
        opening_delimiter: &str,
    ) -> IonResult<Self> {
        let space_after_container_start = writer.whitespace_config.space_after_container_start;
        write!(
            writer.output,
            "{opening_delimiter}{space_after_container_start}"
        )?;
        Ok(Self {
            writer,
            depth,
            ion_type,
            has_been_closed: false,
        })
    }

    /// Writes the `indentation` string set in the whitespace config to output `depth` times.
    fn write_indentation(&mut self) -> IonResult<()> {
        let indentation = self.whitespace_config().indentation;
        if !indentation.is_empty() {
            for _ in 0..self.depth {
                write!(self.output(), "{indentation}")?;
            }
        }
        Ok(())
    }

    /// Writes the provided value to output using its implementation of `WriteAsIon`, then writes
    /// the whitespace config's `space_between_nested_values`.
    fn write_value<V: WriteAsIon>(
        &mut self,
        value: V,
        delimiter_between_values: &str,
    ) -> IonResult<&mut Self> {
        self.write_indentation()?;
        value.write_as_ion(self.annotatable_value_writer())?;
        let space_between_nested_values = self.whitespace_config().space_between_nested_values;
        write!(
            self.output(),
            "{delimiter_between_values}{space_between_nested_values}"
        )?;
        Ok(self)
    }

    /// Finalizes the container, preventing further values from being written.
    fn end(mut self, closing_delimiter: &str) -> IonResult<()> {
        let space_between_top_level_values =
            self.whitespace_config().space_between_top_level_values;
        write!(
            self.output(),
            "{closing_delimiter}{space_between_top_level_values}"
        )?;
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
    fn annotatable_value_writer(&mut self) -> TextAnnotatableValueWriter_1_0<'_, W> {
        TextAnnotatableValueWriter_1_0 {
            value_writer: self.value_writer(),
        }
    }
}

/// A superset of the functionality offered by the user-facing `TextListWriter_1_0`. In particular,
/// this type exposes an `end` function that MUST be called to guarantee correct output.
pub struct TextListWriter_1_0<'top, W: Write> {
    container_writer: TextContainerWriter_1_0<'top, W>,
}

impl<'top, W: Write> TextListWriter_1_0<'top, W> {
    pub(crate) fn new(writer: &'top mut LazyRawTextWriter_1_0<W>, depth: usize) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(writer, depth, IonType::List, "[")?;
        Ok(Self { container_writer })
    }

    /// Writes the provided data as a nested value.
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write_value(value, ",")?;
        Ok(self)
    }

    /// Finalizes the list, preventing further values from being written.
    pub(crate) fn end(self) -> IonResult<()> {
        self.container_writer.end("]")?;
        Ok(())
    }
}

impl<'top, W: Write> MakeValueWriter for TextListWriter_1_0<'top, W> {
    type ValueWriter<'a> = TextAnnotatableValueWriter_1_0<'a, W> where Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        self.container_writer.annotatable_value_writer()
    }
}

impl<'top, W: Write> SequenceWriter for TextListWriter_1_0<'top, W> {
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.write(value)
    }
}

/// Incrementally encodes a potentially heterogeneously typed Ion s-expression.
pub struct TextSExpWriter_1_0<'a, W: Write> {
    container_writer: TextContainerWriter_1_0<'a, W>,
}

impl<'a, W: Write> TextSExpWriter_1_0<'a, W> {
    pub(crate) fn new(writer: &'a mut LazyRawTextWriter_1_0<W>, depth: usize) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(writer, depth, IonType::SExp, "(")?;
        Ok(Self { container_writer })
    }

    /// Writes the provided data as a nested value.
    pub(crate) fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write_value(value, " ")?;
        Ok(self)
    }

    /// Finalizes the sexp, preventing further values from being written.
    pub(crate) fn end(self) -> IonResult<()> {
        self.container_writer.end(")")?;
        Ok(())
    }
}

impl<'value, W: Write> MakeValueWriter for TextSExpWriter_1_0<'value, W> {
    type ValueWriter<'a> = TextAnnotatableValueWriter_1_0<'a, W> where Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        self.container_writer.annotatable_value_writer()
    }
}

impl<'a, W: Write> SequenceWriter for TextSExpWriter_1_0<'a, W> {
    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
        }
    }
}

/// Incrementally encodes an Ion struct.
pub struct TextStructWriter_1_0<'a, W: Write> {
    container_writer: TextContainerWriter_1_0<'a, W>,
}

impl<'a, W: Write> TextStructWriter_1_0<'a, W> {
    pub(crate) fn new(writer: &'a mut LazyRawTextWriter_1_0<W>, depth: usize) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(writer, depth, IonType::Struct, "{")?;
        Ok(Self { container_writer })
    }

    pub(crate) fn end(self) -> IonResult<()> {
        self.container_writer.end("}")?;
        Ok(())
    }
}

impl<'a, W: Write> StructWriter for TextStructWriter_1_0<'a, W> {
    fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        name: A,
        value: V,
    ) -> IonResult<&mut Self> {
        // Write the field name
        RawTextWriter::<W>::write_symbol_token(self.container_writer.output(), name)?;

        let space_after_field_name = self
            .container_writer
            .whitespace_config()
            .space_after_field_name;
        // Write a `:` and configured trailing whitespace
        write!(self.container_writer.output(), ":{space_after_field_name}",)?;
        // Write the field value
        self.container_writer.write_value(value, ",")?;
        Ok(self)
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
        assert!(
            IonData::eq(&expected, &actual),
            "expected:\n{expected:?}\nwas not Ion equal to actual:\n{actual:?}\n"
        );
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
                .write(1.annotated_with(&["foo", "bar"]))?
                .write(false.annotated_with(&["quux", "quuz", "gary"]))?
                .write(3f32.annotated_with(&["Mercury", "Venus"]))?
                .write("foo".annotated_with(&["Earth"]))?
                .write("bar".as_symbol_ref().annotated_with(&["Mars", "Jupiter"]))?
                .write(
                    Timestamp::with_ymd(2023, 11, 9)
                        .build()?
                        .annotated_with(&["Saturn"]),
                )?
                .write((&[0xE0u8, 0x01, 0x00, 0xEA][..]).annotated_with(&["Uranus"]))?;
            Ok(())
        };
        writer_test(expected, test)
    }

    // #[test]
    // fn write_list() -> IonResult<()> {
    //     let expected = r#"
    //         [
    //           1,
    //           false,
    //           3e0,
    //           "foo",
    //           bar,
    //           2023-11-09T,
    //           {{4AEA6g==}},
    //         ]
    //     "#;
    //     let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
    //         writer.value_writer().write_list(|list| {
    //             list.write(1)?
    //                 .write(false)?
    //                 .write(3f32)?
    //                 .write("foo")?
    //                 .write("bar".as_symbol_ref())?
    //                 .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
    //                 .write(&[0xE0u8, 0x01, 0x00, 0xEA][..])?;
    //             Ok(())
    //         })
    //     };
    //     writer_test(expected, test)
    // }
    //
    // #[test]
    // fn write_sexp() -> IonResult<()> {
    //     let expected = r#"
    //         (
    //           1
    //           false
    //           3e0
    //           "foo"
    //           bar
    //           2023-11-09T
    //           {{4AEA6g==}}
    //           // Nested list
    //           [1, 2, 3]
    //         )
    //     "#;
    //     let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
    //         writer.value_writer().write_sexp(|sexp| {
    //             sexp.write(1)?
    //                 .write(false)?
    //                 .write(3f32)?
    //                 .write("foo")?
    //                 .write("bar".as_symbol_ref())?
    //                 .write(Timestamp::with_ymd(2023, 11, 9).build()?)?
    //                 .write([0xE0u8, 0x01, 0x00, 0xEA])?
    //                 .write([1, 2, 3])?;
    //             Ok(())
    //         })
    //     };
    //     writer_test(expected, test)
    // }
    //
    // #[test]
    // fn write_struct() -> IonResult<()> {
    //     let expected = r#"
    //         {
    //           a: 1,
    //           b: false,
    //           c: 3e0,
    //           d: "foo",
    //           e: bar,
    //           f: 2023-11-09T,
    //           g: {{4AEA6g==}},
    //         }
    //     "#;
    //     let test = |writer: &mut LazyRawTextWriter_1_0<&mut Vec<u8>>| {
    //         writer.value_writer().write_struct(|struct_| {
    //             struct_
    //                 .write("a", 1)?
    //                 .write("b", false)?
    //                 .write("c", 3f32)?
    //                 .write("d", "foo")?
    //                 .write("e", "bar".as_symbol_ref())?
    //                 .write("f", Timestamp::with_ymd(2023, 11, 9).build()?)?
    //                 .write("g", [0xE0u8, 0x01, 0x00, 0xEA])?;
    //             Ok(())
    //         })
    //     };
    //     writer_test(expected, test)
    // }
}
