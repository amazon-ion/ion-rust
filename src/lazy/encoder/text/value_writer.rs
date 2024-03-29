use crate::lazy::encoder::container_fn::{ListFn, MacroArgsFn, SExpFn, StructFn};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::text::LazyRawTextWriter_1_0;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::{
    delegate_value_writer_to, AnnotatableValueWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::never::Never;
use crate::lazy::text::raw::v1_1::reader::MacroIdRef;
use crate::raw_symbol_token_ref::{AsRawSymbolTokenRef, RawSymbolTokenRef};
use crate::result::{IonFailure, IonResult};
use crate::text::raw_text_writer::{RawTextWriter, WhitespaceConfig};
use crate::text::text_formatter::IonValueFormatter;
use crate::types::IonType;
use crate::{Decimal, Int, Timestamp};
use delegate::delegate;
use std::fmt::Formatter;
use std::io::Write;

pub struct TextValueWriter_1_0<'value, W: Write + 'value> {
    writer: &'value mut LazyRawTextWriter_1_0<W>,
    depth: usize,
}

impl<'value, W: Write + 'value> TextValueWriter_1_0<'value, W> {
    pub fn new(writer: &'value mut LazyRawTextWriter_1_0<W>, depth: usize) -> Self {
        Self { writer, depth }
    }
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

impl<'value, W: Write> TextAnnotatableValueWriter_1_0<'value, W> {
    pub fn new(value_writer: TextValueWriter_1_0<'value, W>) -> Self {
        Self { value_writer }
    }
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

/// Writes Ion 1.0 lists and implements the `SequenceWriter` trait.
pub struct TextListWriter_1_0<'top, W: Write> {
    container_writer: TextContainerWriter_1_0<'top, W>,
}

impl<'top, W: Write> TextListWriter_1_0<'top, W> {
    pub fn new(writer: &'top mut LazyRawTextWriter_1_0<W>, depth: usize) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(writer, depth, IonType::List, "[")?;
        Ok(Self { container_writer })
    }

    /// Writes the provided data as a nested value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write_value(value, ",")?;
        Ok(self)
    }

    /// Finalizes the list, preventing further values from being written.
    pub fn end(self) -> IonResult<()> {
        self.container_writer.end("]")?;
        Ok(())
    }
}

impl<'top, W: Write> MakeValueWriter for TextListWriter_1_0<'top, W> {
    type ValueWriter<'a> = TextAnnotatableValueWriter_1_0<'a, W> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
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
    pub fn new(writer: &'a mut LazyRawTextWriter_1_0<W>, depth: usize) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(writer, depth, IonType::SExp, "(")?;
        Ok(Self { container_writer })
    }

    /// Writes the provided data as a nested value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write_value(value, " ")?;
        Ok(self)
    }

    /// Finalizes the sexp, preventing further values from being written.
    pub fn end(self) -> IonResult<()> {
        self.container_writer.end(")")?;
        Ok(())
    }
}

impl<'value, W: Write> MakeValueWriter for TextSExpWriter_1_0<'value, W> {
    type ValueWriter<'a> = TextAnnotatableValueWriter_1_0<'a, W> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
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
    pub fn new(writer: &'a mut LazyRawTextWriter_1_0<W>, depth: usize) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(writer, depth, IonType::Struct, "{")?;
        Ok(Self { container_writer })
    }

    pub fn end(self) -> IonResult<()> {
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

impl<'value, W: Write + 'value, SymbolType: AsRawSymbolTokenRef> ValueWriter
    for TextAnnotatedValueWriter_1_0<'value, W, SymbolType>
{
    type ListWriter = TextListWriter_1_0<'value, W>;
    type SExpWriter = TextSExpWriter_1_0<'value, W>;
    type StructWriter = TextStructWriter_1_0<'value, W>;

    // Ion 1.0 does not support macros
    type MacroArgsWriter = Never;

    delegate_value_writer_to!(fallible closure |self_: Self| self_.encode_annotations());
}

impl<'value, W: Write> ValueWriter for TextValueWriter_1_0<'value, W> {
    type ListWriter = TextListWriter_1_0<'value, W>;
    type SExpWriter = TextSExpWriter_1_0<'value, W>;
    type StructWriter = TextStructWriter_1_0<'value, W>;

    // Ion 1.0 does not support macros
    type MacroArgsWriter = Never;
    fn write_null(mut self, ion_type: IonType) -> IonResult<()> {
        use crate::IonType::*;
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

    fn write_string(mut self, value: impl AsRef<str>) -> IonResult<()> {
        write!(self.output(), "\"")?;
        RawTextWriter::<W>::write_escaped_text_body(self.output(), value)?;
        write!(self.output(), "\"")?;
        Ok(())
    }

    fn write_symbol(mut self, value: impl AsRawSymbolTokenRef) -> IonResult<()> {
        RawTextWriter::<W>::write_symbol_token(self.output(), value)?;
        Ok(())
    }

    fn write_clob(mut self, value: impl AsRef<[u8]>) -> IonResult<()> {
        // This type exists solely to enable using the IonValueFormatter (which operates on
        // `std::fmt::Write`) to write to a `std::io::Write`.
        struct ClobShim<'a>(&'a [u8]);
        impl<'a> std::fmt::Display for ClobShim<'a> {
            fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
                let mut formatter = IonValueFormatter { output: f };
                formatter.format_clob(self.0)?;
                Ok(())
            }
        }

        write!(self.output(), "{}", ClobShim(value.as_ref()))?;
        Ok(())
    }

    fn write_blob(mut self, value: impl AsRef<[u8]>) -> IonResult<()> {
        // Rust format strings escape curly braces by doubling them. The following string is:
        // * The opening {{ from a text Ion blob, with each brace doubled to escape it.
        // * A {} pair used by the format string to indicate where the base64-encoded bytes
        //   should be inserted.
        // * The closing }} from a text Ion blob, with each brace doubled to escape it.
        write!(self.output(), "{{{{{}}}}}", base64::encode(value))?;
        Ok(())
    }

    fn write_list(self, list_fn: impl ListFn<Self>) -> IonResult<()> {
        let mut list_writer = TextListWriter_1_0::new(self.writer, self.depth + 1)?;
        list_fn(&mut list_writer)?;
        list_writer.end()
    }
    fn write_sexp(self, sexp_fn: impl SExpFn<Self>) -> IonResult<()> {
        let mut sexp_writer = TextSExpWriter_1_0::new(self.writer, self.depth + 1)?;
        sexp_fn(&mut sexp_writer)?;
        sexp_writer.end()
    }
    fn write_struct(self, struct_fn: impl StructFn<Self>) -> IonResult<()> {
        let mut struct_writer = TextStructWriter_1_0::new(self.writer, self.depth + 1)?;
        struct_fn(&mut struct_writer)?;
        struct_writer.end()
    }

    fn write_eexp<'macro_id>(
        self,
        macro_id: impl Into<MacroIdRef<'macro_id>>,
        _macro_fn: impl MacroArgsFn<Self>,
    ) -> IonResult<()> {
        let id = macro_id.into();
        IonResult::encoding_error(format!(
            "attempted to call macro {id:?}; macros are not supported in Ion 1.0"
        ))
    }
}
