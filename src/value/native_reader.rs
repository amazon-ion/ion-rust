use crate::binary::constants::v1_0::IVM;
use crate::binary::non_blocking::raw_binary_reader::RawBinaryBufferReader;
use crate::raw_reader::RawReader;
use crate::reader::ReaderBuilder;
use crate::result::IonResult;
use crate::text::non_blocking::raw_text_reader::RawTextReader;
use crate::value::owned;
use crate::value::owned::{Element, Struct, Value};
use crate::value::reader::ElementReader;
use crate::{IonReader, IonType, StreamItem, UserReader};

struct NativeElementIterator<R: RawReader> {
    reader: UserReader<R>,
}

impl<R: RawReader> Iterator for NativeElementIterator<R> {
    type Item = IonResult<Element>;

    fn next(&mut self) -> Option<Self::Item> {
        self.materialize_next().transpose()
    }
}

impl<R: RawReader> NativeElementIterator<R> {
    /// Advances the reader to the next value in the stream and uses [Self::materialize_current]
    /// to materialize it.
    fn materialize_next(&mut self) -> IonResult<Option<Element>> {
        // Advance the reader to the next value
        let _ = self.reader.next()?;
        self.materialize_current()
    }

    /// Recursively materialize the reader's current Ion value and returns it as `Ok(Some(element))`.
    /// If there are no more values at this level, returns `Ok(None)`.
    /// If an error occurs while materializing the value, returns an `Err`.
    /// Calling this method advances the reader and consumes the current value.
    fn materialize_current(&mut self) -> IonResult<Option<Element>> {
        // Collect this item's annotations into a Vec. We have to do this before materializing the
        // value itself because materializing a collection requires advancing the reader further.
        let mut annotations = Vec::new();
        // Current API limitations require `self.reader.annotations()` to heap allocate its
        // iterator even if there aren't annotations. `self.reader.has_annotations()` is trivial
        // and allows us to skip the heap allocation in the common case.
        if self.reader.has_annotations() {
            for annotation in self.reader.annotations() {
                annotations.push(annotation?);
            }
        }

        let value = match self.reader.current() {
            // No more values at this level of the stream
            StreamItem::Nothing => return Ok(None),
            // This is a typed null
            StreamItem::Null(ion_type) => Value::Null(ion_type),
            // This is a non-null value
            StreamItem::Value(ion_type) => {
                use IonType::*;
                match ion_type {
                    Null => unreachable!("non-null value had IonType::Null"),
                    Boolean => Value::Boolean(self.reader.read_bool()?),
                    Integer => Value::Integer(self.reader.read_integer()?),
                    Float => Value::Float(self.reader.read_f64()?),
                    Decimal => Value::Decimal(self.reader.read_decimal()?),
                    Timestamp => Value::Timestamp(self.reader.read_timestamp()?),
                    Symbol => Value::Symbol(self.reader.read_symbol()?),
                    String => Value::String(self.reader.read_string()?),
                    Clob => Value::Clob(self.reader.read_clob()?),
                    Blob => Value::Blob(self.reader.read_blob()?),
                    // It's a collection; recursively materialize all of this value's children
                    List => Value::List(owned::List::new(self.materialize_sequence()?)),
                    SExpression => {
                        Value::SExpression(owned::SExp::new(self.materialize_sequence()?))
                    }
                    Struct => Value::Struct(self.materialize_struct()?),
                }
            }
        };
        Ok(Some(Element::new(annotations, value)))
    }

    /// Steps into the current sequence and materializes each of its children to construct
    /// an [OwnedSequence]. When all of the the children have been materialized, steps out.
    /// The reader MUST be positioned over a list or s-expression when this is called.
    fn materialize_sequence(&mut self) -> IonResult<Vec<Element>> {
        let mut child_elements = Vec::new();
        self.reader.step_in()?;
        while let Some(element) = self.materialize_next()? {
            child_elements.push(element);
        }
        self.reader.step_out()?;
        Ok(child_elements)
    }

    /// Steps into the current struct and materializes each of its fields to construct
    /// an [OwnedStruct]. When all of the the fields have been materialized, steps out.
    /// The reader MUST be positioned over a struct when this is called.
    fn materialize_struct(&mut self) -> IonResult<Struct> {
        let mut child_elements = Vec::new();
        self.reader.step_in()?;
        while let StreamItem::Value(_) | StreamItem::Null(_) = self.reader.next()? {
            let field_name = self.reader.field_name()?;
            let value = self
                .materialize_current()?
                .expect("materialize_current() returned None for user data");
            child_elements.push((field_name, value));
        }
        self.reader.step_out()?;
        Ok(Struct::from_iter(child_elements.into_iter()))
    }
}

/// Provides an implementation of [ElementReader] that is backed by a native Rust [Reader](crate::reader::Reader).
pub struct NativeElementReader;

impl ElementReader for NativeElementReader {
    fn iterate_over<'a, 'b>(
        &'a self,
        data: &'b [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<Element>> + 'b>> {
        let reader = ReaderBuilder::new().build(data)?;
        let iterator = NativeElementIterator { reader };
        Ok(Box::new(iterator))
    }
}

pub struct NonBlockingNativeElementReader;

impl ElementReader for NonBlockingNativeElementReader {
    fn iterate_over<'a, 'b>(
        &'a self,
        data: &'b [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<Element>> + 'b>> {
        // If the data is binary, create a non-blocking binary reader.
        if data.starts_with(&IVM) {
            let raw_reader = RawBinaryBufferReader::new(data);
            let reader = UserReader::new(raw_reader);
            let iterator = NativeElementIterator { reader };
            return Ok(Box::new(iterator));
        }

        let mut raw_reader = RawTextReader::new(data);
        raw_reader.stream_complete();
        let reader = UserReader::new(raw_reader);
        let iterator = NativeElementIterator { reader };
        Ok(Box::new(iterator))
    }
}
