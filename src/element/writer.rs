// Copyright Amazon.com, Inc. or its affiliates.

//! Provides utility to serialize Ion data from [`Element`](super::Element) into common targets
//! such as byte buffers or files.

use crate::result::IonResult;

use crate::element::{Element, Value};
use crate::{IonType, IonWriter};
pub use Format::*;
pub use TextKind::*;

/// Serializes [`Element`] instances into some kind of output sink.
pub trait ElementWriter {
    /// Serializes a single [`Element`] as a top-level value.
    fn write_element(&mut self, element: &Element) -> IonResult<()>;

    /// Serializes a collection of [`Element`] as a series of top-level values.
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

        match element.value() {
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

/// Whether or not the text is pretty printed or serialized in a more compact representation.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum TextKind {
    Compact,
    Lines,
    Pretty,
}

/// Basic configuration options for [`ElementWriter`] instances.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Format {
    Text(TextKind),
    Binary,
    // TODO a mode for Json(TextKind)
}

#[cfg(test)]
mod tests {
    use crate::element::writer::ElementWriter;
    use crate::element::Element;
    use crate::ion_data::IonEq;
    use crate::text::text_writer::TextWriterBuilder;

    use crate::{IonResult, IonWriter};
    use nom::AsBytes;

    #[test]
    fn element_roundtrip() -> IonResult<()> {
        let mut buffer = Vec::new();
        let mut writer = TextWriterBuilder::new().build(&mut buffer)?;

        let ion = r#"
            null true 0 1e0 2.0 2022T foo "bar" (foo bar baz) [foo, bar, baz] {foo: true, bar: false}
        "#;
        let expected_elements = Element::read_all(ion.as_bytes())?;
        writer.write_elements(&expected_elements)?;
        writer.flush()?;
        let actual_elements = Element::read_all(writer.output().as_bytes())?;
        assert!(expected_elements.ion_eq(&actual_elements));
        Ok(())
    }
}
