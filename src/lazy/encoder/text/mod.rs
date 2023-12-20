use crate::lazy::encoder::text::value_writer::{
    TextAnnotatableValueWriter_1_0, TextValueWriter_1_0,
};
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::{LazyEncoder, LazyRawWriter};
use crate::lazy::encoding::TextEncoding_1_0;
use crate::text::raw_text_writer::{WhitespaceConfig, PRETTY_WHITESPACE_CONFIG};
use crate::IonResult;
use delegate::delegate;
use std::io::Write;

pub mod value_writer;

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
        TextValueWriter_1_0::new(self, 0)
    }

    /// Helper method to construct this format's `AnnotatedValueWriter` implementation.
    #[inline]
    fn annotatable_value_writer(&mut self) -> TextAnnotatableValueWriter_1_0<'_, W> {
        TextAnnotatableValueWriter_1_0::new(self.value_writer())
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
        let value_writer = TextValueWriter_1_0::new(self, 0);
        TextAnnotatableValueWriter_1_0::new(value_writer)
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

impl LazyEncoder for TextEncoding_1_0 {
    type Writer<W: Write> = LazyRawTextWriter_1_0<W>;
}
