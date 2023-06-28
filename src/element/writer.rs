// Copyright Amazon.com, Inc. or its affiliates.

//! Provides utility to serialize Ion data from [`Element`](super::Element) into common targets
//! such as byte buffers or files.

use crate::result::IonResult;

use crate::element::{Element, Value};
use crate::ion_writer::IonWriter;
pub use crate::Format::*;
use crate::IonType;
pub use crate::TextKind::*;

/// Serializes [`Element`] instances into some kind of output sink.
pub trait ElementWriter {
    /// Serializes a single [`Element`] at the current depth of the writer.
    fn write_element(&mut self, element: &Element) -> IonResult<()>;

    /// Serializes a single [`Value`] at the current depth of the writer.
    // TODO: consider extracting this to a ValueWriter trait.
    fn write_value(&mut self, value: &Value) -> IonResult<()>;

    /// Serializes a collection of [`Element`].
    ///
    /// Most commonly used to serialize a series of top-level values, but can be used to write
    /// [`Element`]s to an Ion `list` or `sexp` as well.
    ///
    /// This will return [`Err`] if writing any element causes a failure.
    fn write_elements<'a, I: IntoIterator<Item = &'a Element>>(
        &'a mut self,
        elements: I,
    ) -> IonResult<()> {
        for element in elements.into_iter() {
            self.write_element(element)?;
        }
        Ok(())
    }
}

impl<W> ElementWriter for W
where
    W: IonWriter,
{
    fn write_element(&mut self, element: &Element) -> IonResult<()> {
        self.set_annotations(element.annotations());
        self.write_value(element.value())
    }

    fn write_value(&mut self, value: &Value) -> IonResult<()> {
        match value {
            Value::Null(ion_type) => self.write_null(*ion_type),
            Value::Int(i) => self.write_int(i),
            Value::Float(f) => {
                let f = *f;
                let small_float = f as f32;
                if (small_float as f64) == f {
                    self.write_f32(small_float)
                } else {
                    self.write_f64(f)
                }
            }
            Value::Decimal(d) => self.write_decimal(d),
            Value::Timestamp(t) => self.write_timestamp(t),
            Value::String(s) => self.write_string(s),
            Value::Symbol(s) => self.write_symbol(s),
            Value::Bool(b) => self.write_bool(*b),
            Value::Blob(b) => self.write_blob(b),
            Value::Clob(c) => self.write_clob(c),
            Value::SExp(s) => {
                self.step_in(IonType::SExp)?;
                self.write_elements(s.elements())?;
                self.step_out()
            }
            Value::List(l) => {
                self.step_in(IonType::List)?;
                self.write_elements(l.elements())?;
                self.step_out()
            }
            Value::Struct(s) => {
                self.step_in(IonType::Struct)?;
                for (name, value) in s.fields() {
                    self.set_field_name(name);
                    self.write_element(value)?;
                }
                self.step_out()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::element::writer::ElementWriter;
    use crate::element::{Element, List};
    use crate::ion_data::IonEq;
    use crate::text::text_writer::TextWriterBuilder;

    use crate::ion_writer::IonWriter;
    use crate::{IonResult, IonType};
    use nom::AsBytes;

    #[test]
    fn element_roundtrip() -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut writer = TextWriterBuilder::default().build(&mut buffer)?;

        let ion = r#"
            null true 0 1e0 2.0 2022T foo "bar" (foo bar baz) [foo, bar, baz] {foo: true, bar: false} annotated::value
        "#;
        let expected_elements = Element::read_all(ion.as_bytes())?;
        writer.write_elements(&expected_elements)?;
        writer.flush()?;
        let actual_elements = Element::read_all(writer.output().as_bytes())?;
        assert!(expected_elements.ion_eq(&actual_elements));
        Ok(())
    }

    #[test]
    fn write_nested_element() -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut writer = TextWriterBuilder::default().build(&mut buffer)?;

        let ion = r#"
            null true 0 1e0 2.0 2022T foo "bar" (foo bar baz) [foo, bar, baz] {foo: true, bar: false} annotated::value
        "#;
        let expected_list_elements = Element::read_all(ion.as_bytes())?;
        writer.step_in(IonType::List)?;
        writer.write_elements(&expected_list_elements)?;
        writer.step_out()?;
        writer.flush()?;
        // This should be an Ion List containing all of the above elements.
        let actual_list = Element::read_one(writer.output().as_bytes())?;
        let expected_list: Element = List::from(expected_list_elements).into();
        assert!(expected_list.ion_eq(&actual_list));
        Ok(())
    }

    #[test]
    fn write_value() -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut writer = TextWriterBuilder::default().build(&mut buffer)?;

        let ion = r#"
            null true 0 1e0 2.0 2022T foo "bar" (foo bar baz) [foo, bar, baz] {foo: true, bar: false}
        "#;
        let expected_elements = Element::read_all(ion.as_bytes())?;
        for e in &expected_elements {
            writer.write_value(e.value())?;
        }
        writer.flush()?;
        let actual_elements = Element::read_all(writer.output().as_bytes())?;
        assert!(expected_elements.ion_eq(&actual_elements));
        Ok(())
    }
}
