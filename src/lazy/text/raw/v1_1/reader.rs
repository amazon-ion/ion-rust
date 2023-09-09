#![allow(non_camel_case_types)]

use crate::lazy::decoder::private::{
    LazyContainerPrivate, LazyRawFieldPrivate, LazyRawValuePrivate,
};
use crate::lazy::decoder::{
    LazyDecoder, LazyMacroInvocation, LazyRawField, LazyRawReader, LazyRawSequence, LazyRawStruct,
    LazyRawValue,
};
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::text::buffer::TextBufferView;
use crate::lazy::text::encoded_value::EncodedTextValue;
use crate::lazy::text::raw::r#struct::{
    LazyRawTextField_1_0, LazyRawTextStruct_1_0, RawTextStructIterator_1_0,
};
use crate::lazy::text::raw::sequence::{
    LazyRawTextList_1_0, LazyRawTextSExp_1_0, RawTextListIterator_1_0, RawTextSExpIterator_1_0,
};
use crate::lazy::text::value::{LazyRawTextValue_1_0, RawTextAnnotationsIterator};
use crate::{IonResult, IonType, RawSymbolTokenRef};

pub struct LazyRawTextReader_1_1<'data> {
    // The current view of the data we're reading from.
    buffer: TextBufferView<'data>,
    // Each time something is parsed from the buffer successfully, the caller will mark the number
    // of bytes that may be skipped the next time the reader advances.
    bytes_to_skip: usize,
}

// The Ion 1.1 text encoding.
#[derive(Clone, Debug)]
struct TextEncoding_1_1;

impl<'data> LazyDecoder<'data> for TextEncoding_1_1 {
    // TODO: Each of these associated types is currently a wrapper around the Ion 1.0 text impl's types.
    //       These impls will be replaced by a proper v1.1 impl over time.
    type Reader = LazyRawTextReader_1_1<'data>;
    type Value = LazyRawTextValue_1_1<'data>;
    type SExp = LazyRawTextSExp_1_1<'data>;
    type List = LazyRawTextList_1_1<'data>;
    type Struct = LazyRawTextStruct_1_1<'data>;
    type AnnotationsIterator = RawTextAnnotationsIterator<'data>;
    type MacroInvocation = LazyRawTextMacroInvocation<'data>;
}

#[derive(Debug, Copy, Clone)]
pub struct LazyRawTextMacroInvocation<'data> {
    pub(crate) encoded_expr: EncodedTextMacroInvocation,
    pub(crate) input: TextBufferView<'data>,
}

impl<'data, D: LazyDecoder<'data>> LazyMacroInvocation<'data, D>
    for LazyRawTextMacroInvocation<'data>
{
    // Nothing for now.
}

#[derive(Debug, Copy, Clone)]
pub struct EncodedTextMacroInvocation {
    length: usize,
}

impl<'data> LazyRawReader<'data, TextEncoding_1_1> for LazyRawTextReader_1_1<'data> {
    fn new(data: &'data [u8]) -> Self {
        LazyRawTextReader_1_1 {
            buffer: TextBufferView::new(data),
            bytes_to_skip: 0,
        }
    }

    fn next<'a>(&'a mut self) -> IonResult<RawStreamItem<'data, TextEncoding_1_1>> {
        todo!()
    }
}

// ===== Placeholder implementations =====

// In Ion 1.1, each of the 1.0 container types will be replaced by versions that know to look for
// and expand macro invocations. For now, we're re-using the 1.0 types. The implementations below
// implement the necessary traits for TextEncoding_1_1 by forwarding to the corresponding
// TextEncoding_1_0 impl.

#[derive(Debug, Copy, Clone)]
pub struct LazyRawTextValue_1_1<'data> {
    pub(crate) encoded_value: EncodedTextValue,
    pub(crate) input: TextBufferView<'data>,
}

#[derive(Debug)]
pub struct LazyRawTextList_1_1<'data> {
    delegate: LazyRawTextList_1_0<'data>,
}

#[derive(Debug)]
pub struct RawTextListIterator_1_1<'data> {
    delegate: RawTextListIterator_1_0<'data>,
}

#[derive(Debug)]
pub struct LazyRawTextSExp_1_1<'data> {
    delegate: LazyRawTextSExp_1_0<'data>,
}

#[derive(Debug)]
pub struct RawTextSExpIterator_1_1<'data> {
    delegate: RawTextSExpIterator_1_0<'data>,
}

#[derive(Debug)]
pub struct LazyRawTextStruct_1_1<'data> {
    delegate: LazyRawTextStruct_1_0<'data>,
}

#[derive(Debug)]
pub struct LazyRawTextField_1_1<'data> {
    delegate: LazyRawTextField_1_0<'data>,
}

#[derive(Debug)]
pub struct RawTextStructIterator_1_1<'data> {
    delegate: RawTextStructIterator_1_0<'data>,
}

impl<'data> LazyRawValuePrivate<'data> for LazyRawTextValue_1_1<'data> {
    fn field_name(&self) -> IonResult<RawSymbolTokenRef<'data>> {
        self.encoded_value.field_name(self.input)
    }
}

impl<'data> LazyRawValue<'data, TextEncoding_1_1> for LazyRawTextValue_1_1<'data> {
    fn ion_type(&self) -> IonType {
        self.encoded_value.ion_type()
    }

    fn is_null(&self) -> bool {
        self.encoded_value.is_null()
    }

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        let span = self
            .encoded_value
            .annotations_range()
            .unwrap_or(self.input.offset()..self.input.offset());
        let annotations_bytes = self
            .input
            .slice(span.start - self.input.offset(), span.len());
        RawTextAnnotationsIterator::new(annotations_bytes)
    }

    fn read(&self) -> IonResult<RawValueRef<'data, TextEncoding_1_1>> {
        let matched_input = self.input.slice(
            self.encoded_value.data_offset() - self.input.offset(),
            self.encoded_value.data_length(),
        );
        use crate::lazy::text::matched::MatchedValue::*;
        let value_ref = match self.encoded_value.matched() {
            Null(ion_type) => RawValueRef::Null(ion_type),
            Bool(b) => RawValueRef::Bool(b),
            Int(i) => RawValueRef::Int(i.read(matched_input)?),
            Float(f) => RawValueRef::Float(f.read(matched_input)?),
            Decimal(d) => RawValueRef::Decimal(d.read(matched_input)?),
            Timestamp(t) => RawValueRef::Timestamp(t.read(matched_input)?),
            String(s) => RawValueRef::String(s.read(matched_input)?),
            Symbol(s) => RawValueRef::Symbol(s.read(matched_input)?),
            Blob(b) => RawValueRef::Blob(b.read(matched_input)?),
            Clob(c) => RawValueRef::Clob(c.read(matched_input)?),
            List => RawValueRef::List(LazyRawTextList_1_1::from_value(*self)),
            SExp => RawValueRef::SExp(LazyRawTextSExp_1_1::from_value(*self)),
            Struct => RawValueRef::Struct(LazyRawTextStruct_1_1::from_value(*self)),
        };
        Ok(value_ref)
    }
}

// ===== Convert 1.0 lazy values to 1.1 lazy values and vice versa ======
// These conversions are only necessary for the placeholder implementations that pass through to
// existing 1.0 parsing logic.

impl<'data> From<LazyRawTextValue_1_1<'data>> for LazyRawTextValue_1_0<'data> {
    fn from(value: LazyRawTextValue_1_1<'data>) -> Self {
        LazyRawTextValue_1_0 {
            encoded_value: value.encoded_value,
            input: value.input,
        }
    }
}

impl<'data> From<LazyRawTextValue_1_0<'data>> for LazyRawTextValue_1_1<'data> {
    fn from(value: LazyRawTextValue_1_0<'data>) -> Self {
        LazyRawTextValue_1_1 {
            encoded_value: value.encoded_value,
            input: value.input,
        }
    }
}

// ===== Trait implementations =====

impl<'data> LazyContainerPrivate<'data, TextEncoding_1_1> for LazyRawTextList_1_1<'data> {
    fn from_value(value: LazyRawTextValue_1_1<'data>) -> Self {
        LazyRawTextList_1_1 {
            delegate: LazyRawTextList_1_0::from_value(LazyRawTextValue_1_0::from(value)),
        }
    }
}

impl<'data> LazyRawSequence<'data, TextEncoding_1_1> for LazyRawTextList_1_1<'data> {
    type Iterator = RawTextListIterator_1_1<'data>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.delegate.annotations()
    }

    fn ion_type(&self) -> IonType {
        self.delegate.ion_type()
    }

    fn iter(&self) -> Self::Iterator {
        RawTextListIterator_1_1 {
            delegate: LazyRawTextList_1_0::iter(&self.delegate),
        }
    }

    fn as_value(&self) -> LazyRawTextValue_1_1<'data> {
        self.delegate.value.into()
    }
}

impl<'data> Iterator for RawTextListIterator_1_1<'data> {
    type Item = IonResult<LazyRawTextValue_1_1<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate
            .next()
            .map(|result| result.map(|value| value.into()))
    }
}

impl<'data> LazyContainerPrivate<'data, TextEncoding_1_1> for LazyRawTextSExp_1_1<'data> {
    fn from_value(value: LazyRawTextValue_1_1<'data>) -> Self {
        LazyRawTextSExp_1_1 {
            delegate: LazyRawTextSExp_1_0::from_value(LazyRawTextValue_1_0::from(value)),
        }
    }
}

impl<'data> LazyRawSequence<'data, TextEncoding_1_1> for LazyRawTextSExp_1_1<'data> {
    type Iterator = RawTextSExpIterator_1_1<'data>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.delegate.annotations()
    }

    fn ion_type(&self) -> IonType {
        self.delegate.ion_type()
    }

    fn iter(&self) -> Self::Iterator {
        RawTextSExpIterator_1_1 {
            delegate: LazyRawTextSExp_1_0::iter(&self.delegate),
        }
    }

    fn as_value(&self) -> LazyRawTextValue_1_1<'data> {
        self.delegate.value.into()
    }
}

impl<'data> Iterator for RawTextSExpIterator_1_1<'data> {
    type Item = IonResult<LazyRawTextValue_1_1<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate
            .next()
            .map(|result| result.map(|value| value.into()))
    }
}

impl<'data> LazyContainerPrivate<'data, TextEncoding_1_1> for LazyRawTextStruct_1_1<'data> {
    fn from_value(value: LazyRawTextValue_1_1<'data>) -> Self {
        LazyRawTextStruct_1_1 {
            delegate: LazyRawTextStruct_1_0::from_value(LazyRawTextValue_1_0::from(value)),
        }
    }
}

impl<'data> LazyRawStruct<'data, TextEncoding_1_1> for LazyRawTextStruct_1_1<'data> {
    type Field = LazyRawTextField_1_1<'data>;
    type Iterator = RawTextStructIterator_1_1<'data>;

    fn annotations(&self) -> RawTextAnnotationsIterator<'data> {
        self.delegate.annotations()
    }

    fn find(&self, name: &str) -> IonResult<Option<LazyRawTextValue_1_1<'data>>> {
        self.delegate
            .find(name)
            .map(|option| option.map(|value| value.into()))
    }

    fn iter(&self) -> Self::Iterator {
        RawTextStructIterator_1_1 {
            delegate: self.delegate.iter(),
        }
    }
}

impl<'data> LazyRawFieldPrivate<'data, TextEncoding_1_1> for LazyRawTextField_1_1<'data> {
    fn into_value(self) -> LazyRawTextValue_1_1<'data> {
        self.delegate.value.into()
    }
}

impl<'data> LazyRawField<'data, TextEncoding_1_1> for LazyRawTextField_1_1<'data> {
    fn name(&self) -> RawSymbolTokenRef<'data> {
        self.delegate.name()
    }

    fn value(&self) -> LazyRawTextValue_1_1<'data> {
        self.delegate.value().into()
    }
}

impl<'data> Iterator for RawTextStructIterator_1_1<'data> {
    type Item = IonResult<LazyRawTextField_1_1<'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        self.delegate
            .next()
            .map(|result| result.map(|field| LazyRawTextField_1_1 { delegate: field }))
    }
}
