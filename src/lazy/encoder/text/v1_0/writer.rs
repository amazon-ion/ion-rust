use std::io::Write;

use delegate::delegate;

use crate::lazy::encoder::text::v1_0::value_writer::TextValueWriter_1_0;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::LazyRawWriter;
use crate::lazy::encoding::{Encoding, TextEncoding_1_0};
use crate::text::whitespace_config::{
    WhitespaceConfig, COMPACT_WHITESPACE_CONFIG, LINES_WHITESPACE_CONFIG, PRETTY_WHITESPACE_CONFIG,
};
use crate::types::ParentType;
use crate::write_config::WriteConfigKind;
use crate::{ContextWriter, IonResult, TextFormat, WriteConfig};

/// A raw text Ion 1.0 writer.
pub struct LazyRawTextWriter_1_0<W: Write> {
    pub(crate) output: W,
    pub(crate) whitespace_config: &'static WhitespaceConfig,
}

impl<W: Write> LazyRawTextWriter_1_0<W> {
    /// Constructs a new writer that will emit encoded data to the specified `output`.
    pub fn new(output: W) -> IonResult<Self> {
        <Self as LazyRawWriter<W>>::new(output)
    }

    /// Writes the provided data as a top-level value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        value.write_as_ion(self.value_writer())?;
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
        TextValueWriter_1_0::new(
            self,
            0,
            "", // No delimiter between values at the top level
            ParentType::TopLevel,
        )
    }
}

impl<W: Write> SequenceWriter for LazyRawTextWriter_1_0<W> {
    type Resources = W;

    fn close(mut self) -> IonResult<Self::Resources> {
        self.flush()?;
        Ok(self.output)
    }
}

impl<W: Write> ContextWriter for LazyRawTextWriter_1_0<W> {
    type NestedValueWriter<'a>
        = TextValueWriter_1_0<'a, W>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for LazyRawTextWriter_1_0<W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
        self.value_writer()
    }
}

impl<W: Write> LazyRawWriter<W> for LazyRawTextWriter_1_0<W> {
    fn new(output: W) -> IonResult<Self> {
        Self::build(
            WriteConfig::<TextEncoding_1_0>::new(TextFormat::default()),
            output,
        )
    }

    /// Build text writer based on given writer configuration
    fn build<E: Encoding>(config: WriteConfig<E>, output: W) -> IonResult<Self> {
        match &config.kind {
            WriteConfigKind::Text(text_config) => {
                let whitespace_config = match text_config.text_kind {
                    TextFormat::Compact => &COMPACT_WHITESPACE_CONFIG,
                    TextFormat::Lines => &LINES_WHITESPACE_CONFIG,
                    TextFormat::Pretty => &PRETTY_WHITESPACE_CONFIG,
                };
                Ok(LazyRawTextWriter_1_0 {
                    output,
                    whitespace_config,
                })
            }
            WriteConfigKind::Binary(_) => {
                unreachable!("Binary writer can not be created from text encoding")
            }
        }
    }

    // Delegate the trait methods to the inherent methods; this allows a version of these
    // methods to be called on the concrete type even when the trait is not in scope.
    delegate! {
        to self {
            fn flush(&mut self) -> IonResult<()>;
        }
    }

    fn output(&self) -> &W {
        &self.output
    }

    fn output_mut(&mut self) -> &mut W {
        &mut self.output
    }

    fn write_version_marker(&mut self) -> IonResult<()> {
        let space_between = self.whitespace_config.space_between_top_level_values;
        write!(self.output, "$ion_1_0{space_between}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::encoder::text::v1_0::writer::LazyRawTextWriter_1_0;
    use crate::{v1_1, Annotatable, ElementReader, IonData, IonResult, Reader, SequenceWriter};

    #[test]
    fn write_annotated_values() -> IonResult<()> {
        const NO_ANNOTATIONS: [&str; 0] = [];
        let mut writer = LazyRawTextWriter_1_0::new(vec![])?;
        writer
            .write(1)?
            // Explicitly setting an empty annotations sequence
            .write(2.annotated_with(NO_ANNOTATIONS))?
            .write(3.annotated_with("foo"))?
            .write(4.annotated_with(["foo", "bar", "baz"]))?;
        let encoded_bytes = writer.close()?;
        let encoded_text = String::from_utf8(encoded_bytes).unwrap();
        println!("{encoded_text}");

        let expected_ion = r#"
            1
            2 // An explicitly empty annotations sequence results in an unannotated value
            foo::3
            foo::bar::baz::4
        "#;

        let mut reader = Reader::new(v1_1::Text, encoded_text)?;
        let actual = reader.read_all_elements()?;

        let mut reader = Reader::new(v1_1::Text, expected_ion)?;
        let expected = reader.read_all_elements()?;

        assert!(IonData::eq(&expected, &actual));
        Ok(())
    }
}
