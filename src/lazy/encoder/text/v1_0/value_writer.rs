use std::io::Write;

use delegate::delegate;

use crate::lazy::encoder::annotation_seq::{AnnotationSeq, AnnotationsVec};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{
    delegate_value_writer_to, AnnotatableWriter, SequenceWriter, StructWriter, ValueWriter,
};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::raw_symbol_ref::AsRawSymbolRef;
use crate::text::text_formatter::{FmtValueFormatter, IoValueFormatter};
use crate::text::whitespace_config::WhitespaceConfig;
use crate::types::{ContainerType, ParentType};
use crate::{
    v1_0, ContextWriter, Decimal, Encoding, Int, IonResult, IonType, Timestamp, ValueWriterConfig,
};

pub struct TextValueWriter_1_0<'value, W: Write> {
    pub(crate) writer: &'value mut LazyRawTextWriter_1_0<W>,
    pub(crate) depth: usize,
    value_delimiter: &'static str,
    // This allows us to detect cases where a value writer is being used inside a struct
    // (i.e. following an indented field name) which is the only time we don't write
    // indentation before the value.
    pub(crate) parent_type: ParentType,
    // If `true`, this value had annotations and so should not write its own indentation.
    pub(crate) has_annotations: bool,
}

/// Runs `format` with a value formatter that writes to `output`. If an I/O error interrupted the
/// formatter, that error is returned rather than the formatter's less specific one.
#[inline]
fn format_to<O: Write>(
    output: &mut O,
    format: impl FnOnce(&mut FmtValueFormatter<'_, IoValueFormatter<&mut O>>) -> IonResult<()>,
) -> IonResult<()> {
    let mut io_shim = IoValueFormatter::new(output);
    let format_result = format(&mut io_shim.value_formatter());
    io_shim.into_result()?;
    format_result
}

impl<'value, W: Write + 'value> TextValueWriter_1_0<'value, W> {
    pub(crate) fn new(
        writer: &'value mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        delimiter: &'static str,
        parent_type: ParentType,
    ) -> Self {
        Self {
            writer,
            depth,
            value_delimiter: delimiter,
            parent_type,
            has_annotations: false,
        }
    }

    /// Writes the `indentation` string set in the whitespace config to output `depth` times.
    fn write_indentation(&mut self) -> IonResult<()> {
        let indentation = self.whitespace_config().indentation;
        if self.parent_type == ParentType::Struct || self.has_annotations {
            // If this value is part of a struct field, the indentation was written before the
            // field name.
            // If this value has annotations, the indentation was written before the annotations.
            // Either way, there's nothing to do here.
            return Ok(());
        }
        if !indentation.is_empty() {
            for _ in 0..self.depth {
                write!(self.output(), "{indentation}")?;
            }
        }
        Ok(())
    }
}

impl<W: Write> TextValueWriter_1_0<'_, W> {
    fn output(&mut self) -> &mut W {
        &mut self.writer.output
    }

    fn whitespace_config(&self) -> &WhitespaceConfig {
        self.writer.whitespace_config
    }

    pub fn delimiter(&self) -> &'static str {
        self.value_delimiter
    }

    #[inline]
    fn write_delimiter_text(&mut self) -> IonResult<()> {
        let space_between = match self.depth {
            0 => self.whitespace_config().space_between_top_level_values,
            _ => self.whitespace_config().space_between_nested_values,
        };
        let value_delimiter = self.value_delimiter;
        write!(self.output(), "{value_delimiter}{space_between}")?;
        Ok(())
    }

    /// Writes indentation, then the text `format` produces, then the delimiter text that follows
    /// the value.
    #[inline]
    fn write_scalar(
        mut self,
        format: impl FnOnce(&mut FmtValueFormatter<'_, IoValueFormatter<&mut W>>) -> IonResult<()>,
    ) -> IonResult<()> {
        self.write_indentation()?;
        format_to(self.output(), format)?;
        self.write_delimiter_text()
    }
}

pub struct TextAnnotatedValueWriter_1_0<'value, W: Write> {
    pub(crate) annotations: AnnotationsVec<'value>,
    pub(crate) value_writer: TextValueWriter_1_0<'value, W>,
}

impl<'value, W: Write> TextAnnotatedValueWriter_1_0<'value, W> {
    fn encode_annotations(self) -> IonResult<TextValueWriter_1_0<'value, W>> {
        let Self {
            annotations,
            mut value_writer,
        } = self;
        // The inner ValueWriter knows the indentation depth; we'll have it write the indentation
        // before we write the value.
        value_writer.write_indentation()?;
        // After indenting, we set the `has_annotations` flag to `true` so the value won't write
        // indentation a second time.
        value_writer.has_annotations = !annotations.is_empty();
        format_to(value_writer.output(), |formatter| {
            for annotation in annotations {
                formatter.format_annotation(annotation)?;
            }
            Ok(())
        })?;

        Ok(value_writer)
    }
}

impl<'value, W: Write + 'value> Sealed for TextAnnotatedValueWriter_1_0<'value, W> {}

impl<W: Write> Sealed for TextValueWriter_1_0<'_, W> {}

/// Helper type that is home to information and behavior common to the list writer, s-expression writer,
/// and struct writer.
pub(crate) struct TextContainerWriter_1_0<'a, W: Write> {
    // Holds a reference to the output stream and a whitespace config
    pub(crate) writer: &'a mut LazyRawTextWriter_1_0<W>,
    // The depth at which this container's child values appear. This value is used for formatting
    // indentation where applicable.
    pub(crate) depth: usize,
    // Tracks whether the `end()` method was called (thereby emitting a closing delimiter) before
    // this value was dropped. This scenario is a contract violation and results in a panic.
    has_been_closed: bool,
    // The Ion type of the container using this TextContainerWriter_1_0. This value is only
    // used for more informative error messages.
    pub(crate) container_type: ContainerType,
    value_delimiter: &'static str,
    trailing_delimiter: &'static str,
}

impl<'a, W: Write> TextContainerWriter_1_0<'a, W> {
    pub fn new(
        writer: &'a mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        container_type: ContainerType,
        opening_delimiter: &str,
        value_delimiter: &'static str,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let mut container_writer = Self {
            writer,
            depth,
            container_type,
            has_been_closed: false,
            value_delimiter,
            trailing_delimiter,
        };
        if parent_type != ParentType::Struct {
            container_writer.write_indentation(depth)?;
        }
        let space_after_container_start = container_writer
            .writer
            .whitespace_config
            .space_after_container_start;
        write!(
            container_writer.writer.output,
            "{opening_delimiter}{space_after_container_start}"
        )?;
        Ok(container_writer)
    }

    /// Writes the `indentation` string set in the whitespace config to output `depth` times.
    fn write_indentation(&mut self, depth: usize) -> IonResult<()> {
        let indentation = self.whitespace_config().indentation;
        if !indentation.is_empty() {
            for _ in 0..depth {
                write!(self.output(), "{indentation}")?;
            }
        }
        Ok(())
    }

    /// Writes the provided value to output using its implementation of `WriteAsIon`, then writes
    /// the whitespace config's `space_between_nested_values`.
    fn write_value<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.write_indentation(self.depth)?;
        value.write_as_ion(self.value_writer())?;
        Ok(self)
    }

    /// Finalizes the container, preventing further values from being written.
    pub fn close(mut self, closing_delimiter: &str) -> IonResult<()> {
        let space_between = match self.depth {
            0 => self.whitespace_config().space_between_top_level_values,
            _ => self.whitespace_config().space_between_nested_values,
        };
        let trailing_delimiter = self.trailing_delimiter;
        self.write_indentation(self.depth)?;
        write!(
            self.output(),
            "{closing_delimiter}{trailing_delimiter}{space_between}"
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
    pub fn value_writer(&mut self) -> TextValueWriter_1_0<'_, W> {
        TextValueWriter_1_0 {
            writer: self.writer,
            depth: self.depth + 1,
            value_delimiter: self.value_delimiter,
            parent_type: self.container_type.into(),
            has_annotations: false,
        }
    }
}

/// Writes Ion 1.0 lists and implements the `SequenceWriter` trait.
pub struct TextListWriter_1_0<'top, W: Write> {
    container_writer: TextContainerWriter_1_0<'top, W>,
}

impl<'top, W: Write> TextListWriter_1_0<'top, W> {
    pub(crate) fn new(
        writer: &'top mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::List,
            "[",
            ",",
            trailing_delimiter,
        )?;
        Ok(Self { container_writer })
    }

    /// Writes the provided data as a nested value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write_value(value)?;
        Ok(self)
    }

    /// Finalizes the list, preventing further values from being written.
    pub fn end(self) -> IonResult<()> {
        self.container_writer.close("]")?;
        Ok(())
    }
}

impl<W: Write> ContextWriter for TextListWriter_1_0<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_0<'a, W>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for TextListWriter_1_0<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        self.container_writer.value_writer()
    }
}

impl<W: Write> SequenceWriter for TextListWriter_1_0<'_, W> {
    type Resources = ();

    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.write(value)
    }

    fn close(self) -> IonResult<Self::Resources> {
        self.end()
    }
}

/// Incrementally encodes a potentially heterogeneously typed Ion s-expression.
pub struct TextSExpWriter_1_0<'a, W: Write> {
    container_writer: TextContainerWriter_1_0<'a, W>,
}

impl<'a, W: Write> TextSExpWriter_1_0<'a, W> {
    pub(crate) fn new(
        writer: &'a mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::SExp,
            "(",
            "",
            trailing_delimiter,
        )?;
        Ok(Self { container_writer })
    }

    /// Writes the provided data as a nested value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write_value(value)?;
        Ok(self)
    }

    /// Finalizes the sexp, preventing further values from being written.
    pub fn end(self) -> IonResult<()> {
        self.container_writer.close(")")?;
        Ok(())
    }
}

impl<W: Write> ContextWriter for TextSExpWriter_1_0<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_0<'a, W>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for TextSExpWriter_1_0<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        self.container_writer.value_writer()
    }
}

impl<W: Write> SequenceWriter for TextSExpWriter_1_0<'_, W> {
    type Resources = ();

    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
        }
    }

    fn close(self) -> IonResult<Self::Resources> {
        self.end()
    }
}

/// Incrementally encodes an Ion struct.
pub struct TextStructWriter_1_0<'a, W: Write> {
    container_writer: TextContainerWriter_1_0<'a, W>,
}

impl<'a, W: Write> TextStructWriter_1_0<'a, W> {
    pub(crate) fn new(
        writer: &'a mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        trailing_delimiter: &'static str,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::Struct,
            "{",
            ",",
            trailing_delimiter,
        )?;
        Ok(Self { container_writer })
    }

    pub fn end(self) -> IonResult<()> {
        self.container_writer.close("}")?;
        Ok(())
    }
}

impl<W: Write> FieldEncoder for TextStructWriter_1_0<'_, W> {
    #[inline]
    fn encode_field_name(&mut self, name: impl AsRawSymbolRef) -> IonResult<()> {
        // Leading indentation for the current depth
        self.container_writer
            .write_indentation(self.container_writer.depth + 1)?;
        // Write the field name
        format_to(self.container_writer.output(), |formatter| {
            formatter.format_symbol_token(name)
        })?;
        let space_after_field_name = self
            .container_writer
            .whitespace_config()
            .space_after_field_name;
        // Write a `:` and configured trailing whitespace
        write!(self.container_writer.output(), ":{space_after_field_name}",)?;
        Ok(())
    }
}

impl<W: Write> ContextWriter for TextStructWriter_1_0<'_, W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_0<'a, W>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for TextStructWriter_1_0<'_, W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        TextValueWriter_1_0 {
            writer: self.container_writer.writer,
            depth: self.container_writer.depth + 1,
            value_delimiter: ",",
            parent_type: ParentType::Struct,
            has_annotations: false,
        }
    }
}

impl<W: Write> StructWriter for TextStructWriter_1_0<'_, W> {
    fn close(self) -> IonResult<()> {
        self.end()
    }

    fn config(&self) -> ValueWriterConfig {
        v1_0::Text::default_value_writer_config()
    }
}

impl<'value, W: Write + 'value> AnnotatableWriter for TextAnnotatedValueWriter_1_0<'value, W> {
    type AnnotatedValueWriter<'a>
        = TextAnnotatedValueWriter_1_0<'a, W>
    where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(TextAnnotatedValueWriter_1_0 {
            annotations: annotations.into_annotations_vec(),
            value_writer: self.value_writer,
        })
    }
}

impl<'value, W: Write + 'value> ValueWriter for TextAnnotatedValueWriter_1_0<'value, W> {
    type Encoding = v1_0::Text;
    type ListWriter = TextListWriter_1_0<'value, W>;
    type SExpWriter = TextSExpWriter_1_0<'value, W>;
    type StructWriter = TextStructWriter_1_0<'value, W>;

    delegate_value_writer_to!(fallible closure |self_: Self| self_.encode_annotations());
}

impl<W: Write> AnnotatableWriter for TextValueWriter_1_0<'_, W> {
    type AnnotatedValueWriter<'a>
        = TextAnnotatedValueWriter_1_0<'a, W>
    where
        Self: 'a;

    fn with_annotations<'a>(
        self,
        annotations: impl AnnotationSeq<'a>,
    ) -> IonResult<Self::AnnotatedValueWriter<'a>>
    where
        Self: 'a,
    {
        Ok(TextAnnotatedValueWriter_1_0 {
            annotations: annotations.into_annotations_vec(),
            value_writer: self,
        })
    }
}

impl<'value, W: Write> ValueWriter for TextValueWriter_1_0<'value, W> {
    type Encoding = v1_0::Text;
    type ListWriter = TextListWriter_1_0<'value, W>;
    type SExpWriter = TextSExpWriter_1_0<'value, W>;
    type StructWriter = TextStructWriter_1_0<'value, W>;

    fn write_null(self, ion_type: IonType) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_null(ion_type))
    }

    fn write_bool(self, value: bool) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_bool(value))
    }

    fn write_i64(self, value: i64) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_i64(value))
    }

    fn write_int(self, value: &Int) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_integer(value))
    }

    fn write_f32(self, value: f32) -> IonResult<()> {
        self.write_f64(value as f64)
    }

    fn write_f64(self, value: f64) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_float(value))
    }

    fn write_decimal(self, value: &Decimal) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_decimal(value))
    }

    fn write_timestamp(self, value: &Timestamp) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_timestamp(value))
    }

    fn write_string(self, value: impl AsRef<str>) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_string(value))
    }

    fn write_symbol(self, value: impl AsRawSymbolRef) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_symbol_token(value))
    }

    fn write_clob(self, value: impl AsRef<[u8]>) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_clob(value))
    }

    fn write_blob(self, value: impl AsRef<[u8]>) -> IonResult<()> {
        self.write_scalar(|formatter| formatter.format_blob(value))
    }

    fn list_writer(self) -> IonResult<Self::ListWriter> {
        TextListWriter_1_0::new(
            self.writer,
            self.depth,
            self.parent_type,
            self.value_delimiter,
        )
    }
    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        TextSExpWriter_1_0::new(
            self.writer,
            self.depth,
            self.parent_type,
            self.value_delimiter,
        )
    }
    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        TextStructWriter_1_0::new(
            self.writer,
            self.depth,
            self.parent_type,
            self.value_delimiter,
        )
    }
}
