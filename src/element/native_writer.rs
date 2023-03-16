use crate::element::owned::Element;
use crate::element::writer::ElementWriter;
use crate::{IonResult, IonType, IonWriter, RawSymbolTokenRef};

/// Writes [`Element`] instances to the underlying [`IonWriter`] implementation.
pub struct NativeElementWriter<W: IonWriter> {
    writer: W,
}

impl<W: IonWriter> ElementWriter for NativeElementWriter<W> {
    type Output = W;

    fn write(&mut self, element: &Element) -> IonResult<()> {
        self.write_element(None, element)
    }

    fn finish(mut self) -> IonResult<Self::Output> {
        self.writer.flush()?;
        Ok(self.writer)
    }
}

impl<W: IonWriter> NativeElementWriter<W> {
    /// Constructs a new `NativeElementWriter` that wraps the provided [`IonWriter`] implementation.
    pub fn new(writer: W) -> Self {
        NativeElementWriter { writer }
    }

    /// Recursively writes the given `element` and its child elements (if any) to the underlying
    /// writer.
    fn write_element(&mut self, field_name: Option<&str>, element: &Element) -> IonResult<()> {
        if let Some(field_name) = field_name {
            self.writer.set_field_name(field_name);
        }

        let element_annotations = element.annotations().map(|token| {
            if let Some(text) = token.text() {
                RawSymbolTokenRef::Text(text)
            } else {
                // If the text is unknown, serialize it as $0.
                RawSymbolTokenRef::SymbolId(0)
            }
        });
        self.writer.set_annotations(element_annotations);

        if element.is_null() {
            return self.writer.write_null(element.ion_type());
        }

        match element.ion_type() {
            IonType::Null => unreachable!("element has IonType::Null but is_null() was false"),
            IonType::Bool => self.writer.write_bool(element.as_bool().unwrap()),
            IonType::Int => self.writer.write_int(element.as_int().unwrap()),
            IonType::Float => self.writer.write_f64(element.as_float().unwrap()),
            IonType::Decimal => self.writer.write_decimal(element.as_decimal().unwrap()),
            IonType::Timestamp => self.writer.write_timestamp(element.as_timestamp().unwrap()),
            IonType::Symbol => self
                .writer
                .write_symbol(element.as_symbol().unwrap().text().unwrap()),
            IonType::String => self.writer.write_string(element.as_text().unwrap()),
            IonType::Clob => self.writer.write_clob(element.as_lob().unwrap()),
            IonType::Blob => self.writer.write_blob(element.as_lob().unwrap()),
            IonType::List | IonType::SExp => {
                self.writer.step_in(element.ion_type())?;
                for value in element.as_sequence().unwrap().iter() {
                    self.write(value)?;
                }
                self.writer.step_out()
            }
            IonType::Struct => {
                self.writer.step_in(IonType::Struct)?;
                for (field, value) in element.as_struct().unwrap().iter() {
                    self.write_element(Some(field.text().unwrap()), value)?;
                }
                self.writer.step_out()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::element::native_writer::NativeElementWriter;
    use crate::element::owned::Element;
    use crate::element::writer::ElementWriter;
    use crate::ion_eq::IonEq;
    use crate::text::text_writer::TextWriterBuilder;

    use crate::IonResult;
    use nom::AsBytes;

    #[test]
    fn element_roundtrip() -> IonResult<()> {
        let mut buffer = Vec::new();
        let writer = TextWriterBuilder::new().build(&mut buffer)?;
        let mut element_writer = NativeElementWriter::new(writer);

        let ion = r#"
            null true 0 1e0 2.0 2022T foo "bar" (foo bar baz) [foo, bar, baz] {foo: true, bar: false}
        "#;
        let expected_elements = Element::read_all(ion.as_bytes())?;
        element_writer.write_all(&expected_elements)?;
        let _ = element_writer.finish()?;
        let actual_elements = Element::read_all(buffer.as_bytes())?;
        assert!(expected_elements.ion_eq(&actual_elements));
        Ok(())
    }
}
