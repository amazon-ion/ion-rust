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

/// The delimiter (if any) and whitespace written after a value.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Separator {
    /// `space_between_top_level_values`: follows each top-level value.
    TopLevel,
    /// `comma_separator`: follows each value in a list or struct.
    Comma,
    /// `space_between_nested_values`: follows each value in an s-expression.
    Space,
}

impl Separator {
    /// Writes this separator to `writer`'s output.
    #[inline]
    pub(crate) fn write<W: Write>(self, writer: &mut LazyRawTextWriter_1_0<W>) -> IonResult<()> {
        let whitespace = writer.whitespace_config;
        match self {
            Separator::TopLevel => write_layout(
                &mut writer.output,
                whitespace.space_between_top_level_values,
            ),
            Separator::Comma => write_layout(&mut writer.output, whitespace.comma_separator),
            Separator::Space => {
                write_layout(&mut writer.output, whitespace.space_between_nested_values)
            }
        }
    }
}

/// Writes `layout`, one of the strings of a `WhitespaceConfig`, to `output`. Every layout string is
/// at most two bytes long; matching on its length lets a layout be written with byte stores rather
/// than a variable-length copy.
#[inline(always)]
fn write_layout<W: Write>(output: &mut W, layout: &'static str) -> IonResult<()> {
    match *layout.as_bytes() {
        [] => {}
        [byte] => output.write_all(&[byte])?,
        [first, second] => output.write_all(&[first, second])?,
        _ => output.write_all(layout.as_bytes())?,
    }
    Ok(())
}

pub struct TextValueWriter_1_0<'value, W: Write> {
    pub(crate) writer: &'value mut LazyRawTextWriter_1_0<W>,
    pub(crate) depth: usize,
    // Written after this value.
    separator: Separator,
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

/// Writes `indentation` to `output` `depth` times.
// Always inlined so that every call site tests for no indentation itself, rather than calling out
// to find there is nothing to write; only the loop is left to the inliner.
#[inline(always)]
fn write_indentation_to<W: Write>(
    output: &mut W,
    indentation: &'static str,
    depth: usize,
) -> IonResult<()> {
    if indentation.is_empty() || depth == 0 {
        return Ok(());
    }
    write_indentation_levels(output, indentation, depth)
}

/// Writes `indentation` to `output` `depth` times; the loop of [`write_indentation_to`].
#[inline]
fn write_indentation_levels<W: Write>(
    output: &mut W,
    indentation: &'static str,
    depth: usize,
) -> IonResult<()> {
    for _ in 0..depth {
        write_layout(output, indentation)?;
    }
    Ok(())
}

impl<'value, W: Write + 'value> TextValueWriter_1_0<'value, W> {
    pub(crate) fn new(
        writer: &'value mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        separator: Separator,
        parent_type: ParentType,
    ) -> Self {
        Self {
            writer,
            depth,
            separator,
            parent_type,
            has_annotations: false,
        }
    }

    /// Writes the `indentation` string set in the whitespace config to output `depth` times.
    #[inline(always)]
    fn write_indentation(&mut self) -> IonResult<()> {
        if self.parent_type == ParentType::Struct || self.has_annotations {
            // If this value is part of a struct field, the indentation was written before the
            // field name.
            // If this value has annotations, the indentation was written before the annotations.
            // Either way, there's nothing to do here.
            return Ok(());
        }
        let indentation = self.whitespace_config().indentation;
        let depth = self.depth;
        write_indentation_to(self.output(), indentation, depth)
    }
}

impl<W: Write> TextValueWriter_1_0<'_, W> {
    fn output(&mut self) -> &mut W {
        &mut self.writer.output
    }

    fn whitespace_config(&self) -> &WhitespaceConfig {
        self.writer.whitespace_config
    }

    #[inline]
    fn write_separator(&mut self) -> IonResult<()> {
        self.separator.write(self.writer)
    }

    /// Writes indentation, then the text `format` produces, then the separator that follows the
    /// value.
    #[inline]
    fn write_scalar(
        mut self,
        format: impl FnOnce(&mut FmtValueFormatter<'_, IoValueFormatter<&mut W>>) -> IonResult<()>,
    ) -> IonResult<()> {
        self.write_indentation()?;
        format_to(self.output(), format)?;
        self.write_separator()
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
    // The Ion type of the container using this TextContainerWriter_1_0. This value is only
    // used for more informative error messages.
    pub(crate) container_type: ContainerType,
    // Written after each child value.
    child_separator: Separator,
    // Written after the closing delimiter: the separator the parent assigned to this container.
    trailing_separator: Separator,
}

impl<'a, W: Write> TextContainerWriter_1_0<'a, W> {
    /// Writes the indentation for the container's depth (unless it is a struct field's value,
    /// whose field name was already indented) and the opening delimiter of a container of
    /// `container_type`. `trailing_separator` is written after the closing delimiter.
    pub fn new(
        writer: &'a mut LazyRawTextWriter_1_0<W>,
        depth: usize,
        parent_type: ParentType,
        container_type: ContainerType,
        trailing_separator: Separator,
    ) -> IonResult<Self> {
        let whitespace = writer.whitespace_config;
        let (container_start, child_separator) = match container_type {
            ContainerType::List => (whitespace.list_start, Separator::Comma),
            ContainerType::SExp => (whitespace.sexp_start, Separator::Space),
            ContainerType::Struct => (whitespace.struct_start, Separator::Comma),
        };
        let mut container_writer = Self {
            writer,
            depth,
            container_type,
            child_separator,
            trailing_separator,
        };
        if parent_type != ParentType::Struct {
            container_writer.write_indentation(depth)?;
        }
        write_layout(container_writer.output(), container_start)?;
        Ok(container_writer)
    }

    /// Writes the `indentation` string set in the whitespace config to output `depth` times.
    #[inline(always)]
    fn write_indentation(&mut self, depth: usize) -> IonResult<()> {
        let indentation = self.whitespace_config().indentation;
        write_indentation_to(self.output(), indentation, depth)
    }

    /// Writes the provided value to output using its implementation of `WriteAsIon`; the value
    /// writer then writes this container's `child_separator`.
    fn write_value<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.write_indentation(self.depth)?;
        value.write_as_ion(self.value_writer())?;
        Ok(self)
    }

    /// Finalizes the container, preventing further values from being written.
    pub fn close(mut self, closing_delimiter: &str) -> IonResult<()> {
        self.write_indentation(self.depth)?;
        self.output().write_all(closing_delimiter.as_bytes())?;
        self.trailing_separator.write(self.writer)?;
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
            separator: self.child_separator,
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
        trailing_separator: Separator,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::List,
            trailing_separator,
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
        trailing_separator: Separator,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::SExp,
            trailing_separator,
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
        trailing_separator: Separator,
    ) -> IonResult<Self> {
        let container_writer = TextContainerWriter_1_0::new(
            writer,
            depth,
            parent_type,
            ContainerType::Struct,
            trailing_separator,
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
        // Write a `:` and configured trailing whitespace
        let field_name_separator = self
            .container_writer
            .whitespace_config()
            .field_name_separator;
        write_layout(self.container_writer.output(), field_name_separator)
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
            separator: self.container_writer.child_separator,
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
        TextListWriter_1_0::new(self.writer, self.depth, self.parent_type, self.separator)
    }
    fn sexp_writer(self) -> IonResult<Self::SExpWriter> {
        TextSExpWriter_1_0::new(self.writer, self.depth, self.parent_type, self.separator)
    }
    fn struct_writer(self) -> IonResult<Self::StructWriter> {
        TextStructWriter_1_0::new(self.writer, self.depth, self.parent_type, self.separator)
    }
}

#[cfg(test)]
mod tests {
    use rstest::rstest;

    use super::write_layout;
    use crate::IonResult;

    /// `write_layout` writes the whole layout string, whichever length it has.
    #[rstest]
    #[case::empty("")]
    #[case::one_byte(" ")]
    #[case::two_bytes(", ")]
    #[case::longer(",\n  ")]
    fn write_layout_writes_the_layout(#[case] layout: &'static str) -> IonResult<()> {
        let mut output = Vec::new();
        write_layout(&mut output, layout)?;
        assert_eq!(output, layout.as_bytes());
        Ok(())
    }
}
