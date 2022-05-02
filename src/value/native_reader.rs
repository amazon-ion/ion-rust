use crate::raw_reader::RawReader;
use crate::result::IonResult;
use crate::text::raw_text_reader::RawTextReader;
use crate::value::owned;
use crate::value::owned::{OwnedElement, OwnedSequence, OwnedStruct, OwnedValue};
use crate::value::reader::ElementReader;
use crate::{IonType, RawBinaryReader, Reader, StreamItem, StreamReader};

/// Provides an implementation of [ElementReader] that is backed by a native Rust [Reader].
pub struct NativeElementReader;

struct NativeElementIterator<R: RawReader> {
    reader: Reader<R>,
}

impl<R: RawReader> Iterator for NativeElementIterator<R> {
    type Item = IonResult<OwnedElement>;

    fn next(&mut self) -> Option<Self::Item> {
        self.materialize_next().transpose()
    }
}

impl ElementReader for NativeElementReader {
    fn iterate_over<'a, 'b>(
        &'a self,
        data: &'b [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<OwnedElement>> + 'b>> {
        // Match against the slice to see if it starts with the binary IVM
        match data {
            &[0xe0, 0x01, 0x00, 0xea, ..] => {
                // It's binary! Construct a binary Reader.
                let raw_reader = RawBinaryReader::new(data);
                let reader = Reader::new(raw_reader);
                let iterator = NativeElementIterator { reader };
                Ok(Box::new(iterator))
            }
            _ => {
                // It's not binary! Construct a text Reader.
                let raw_reader = RawTextReader::new(data);
                let reader = Reader::new(raw_reader);
                let iterator = NativeElementIterator { reader };
                Ok(Box::new(iterator))
            }
        }
    }
}


impl<R: RawReader> NativeElementIterator<R> {
    /// Recursively materialize the next Ion value in the stream and return it as `Ok(Some(element))`.
    /// If there are no more values at this level, returns `Ok(None)`.
    /// If an error occurs while materializing the value, returns an `Err`.
    fn materialize_next(&mut self) -> IonResult<Option<OwnedElement>> {
        // Advance the reader to the next value
        let current_item = self.reader.next()?;

        // Collect this item's annotations into a Vec. We have to do this before materializing the
        // value itself because materializing a collection requires advancing the reader further.
        let mut annotations = Vec::new();
        for annotation in self.reader.annotations() {
            // If the annotation couldn't be resolved to text, early return the error.
            let annotation = annotation?;
            let symbol = owned::text_token(annotation.as_ref());
            annotations.push(symbol);
        }

        let value = match current_item {
            // No more values at this level of the stream
            StreamItem::Nothing => return Ok(None),
            // This is a typed null
            StreamItem::Null(ion_type) => OwnedValue::Null(ion_type),
            // This is a non-null value
            StreamItem::Value(ion_type) => {
                use IonType::*;
                match ion_type {
                    Null => unreachable!("non-null value had IonType::Null"),
                    Boolean => OwnedValue::Boolean(self.reader.read_bool()?),
                    Integer => OwnedValue::Integer(self.reader.read_integer()?),
                    Float => OwnedValue::Float(self.reader.read_f64()?),
                    Decimal => OwnedValue::Decimal(self.reader.read_decimal()?),
                    Timestamp => OwnedValue::Timestamp(self.reader.read_timestamp()?),
                    Symbol => {
                        OwnedValue::Symbol(owned::text_token(self.reader.read_symbol()?.as_ref()))
                    }
                    String => OwnedValue::String(self.reader.read_string()?),
                    Clob => OwnedValue::Clob(self.reader.read_clob()?),
                    Blob => OwnedValue::Blob(self.reader.read_blob()?),
                    // It's a collection; recursively materialize all of this value's children
                    List => OwnedValue::List(self.materialize_sequence()?),
                    SExpression => OwnedValue::SExpression(self.materialize_sequence()?),
                    Struct => OwnedValue::Struct(self.materialize_struct()?),
                }
            }
        };

        Ok(Some(OwnedElement::new(annotations, value)))
    }

    /// Steps into the current sequence and materializes each of its children to construct
    /// an [OwnedSequence]. When all of the the children have been materialized, steps out.
    /// The reader MUST be positioned over a list or s-expression when this is called.
    fn materialize_sequence(&mut self) -> IonResult<OwnedSequence> {
        let mut child_elements = Vec::new();
        self.reader.step_in()?;
        while let Some(element) = self.materialize_next()? {
            child_elements.push(element);
        }
        self.reader.step_out()?;
        Ok(OwnedSequence::new(child_elements))
    }

    /// Steps into the current struct and materializes each of its fields to construct
    /// an [OwnedStruct]. When all of the the fields have been materialized, steps out.
    /// The reader MUST be positioned over a struct when this is called.
    fn materialize_struct(&mut self) -> IonResult<OwnedStruct> {
        let mut child_elements = Vec::new();
        self.reader.step_in()?;
        while let Some(element) = self.materialize_next()? {
            let field = self.reader.field_name()?;
            child_elements.push((owned::text_token(field.as_ref()), element));
        }
        self.reader.step_out()?;
        Ok(OwnedStruct::from_iter(child_elements.into_iter()))
    }
}
