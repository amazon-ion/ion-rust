#![allow(non_camel_case_types)]

// use crate::lazy::binary::encoded_value::EncodedValue;
// use crate::lazy::raw_value_ref::RawValueRef;
// use crate::lazy::r#struct::LazyStruct;
use crate::lazy::binary::raw::v1_1::annotations_iterator::RawBinaryAnnotationsIterator;
use crate::lazy::binary::raw::v1_1::immutable_buffer::ImmutableBuffer;
use crate::lazy::binary::raw::v1_1::r#struct::RawBinaryStructIterator_1_1 as RawBinaryStructIterator;
use crate::lazy::binary::raw::v1_1::value::LazyRawBinaryValue_1_1;
use crate::lazy::decoder::private::{LazyContainerPrivate, LazyRawValuePrivate};
use crate::lazy::decoder::{
    LazyDecoder, LazyRawReader, LazyRawSequence, LazyRawStruct, LazyRawValue, LazyRawValueExpr,
};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoding::BinaryEncoding_1_1;
use crate::lazy::raw_stream_item::{LazyRawStreamItem, RawStreamItem};
use crate::result::IonFailure;
use crate::{IonResult, IonType, RawSymbolTokenRef};

use bumpalo::Bump as BumpAllocator;

pub struct LazyRawBinaryReader_1_1<'data> {
    data: ImmutableBuffer<'data>,
}

impl<'data> LazyRawBinaryReader_1_1<'data> {
    fn new(data: &'data [u8]) -> Self {
        Self::new_with_offset(data, 0)
    }

    fn new_with_offset(data: &'data [u8], offset: usize) -> Self {
        let data = ImmutableBuffer::new_with_offset(data, offset);
        Self { data }
    }

    fn read_ivm<'top>(
        &mut self,
        buffer: ImmutableBuffer<'data>,
    ) -> IonResult<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    where
        'data: 'top,
    {
        let ((major, minor), _buffer_after_ivm) = buffer.read_ivm()?;
        if (major, minor) != (1, 1) {
            return IonResult::decoding_error(format!(
                "unsupported version of Ion: v{}.{}; only 1.1 is supported by this reader",
                major, minor,
            ));
        }
        self.data = buffer;
        self.data.bytes_to_skip = 4;
        Ok(LazyRawStreamItem::<BinaryEncoding_1_1>::VersionMarker(1, 1))
    }

    fn read_value<'top>(
        &mut self,
        buffer: ImmutableBuffer<'data>,
    ) -> IonResult<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    where
        'data: 'top,
    {
        let lazy_value = match ImmutableBuffer::peek_sequence_value(buffer)? {
            Some(lazy_value) => lazy_value,
            None => return Ok(LazyRawStreamItem::<BinaryEncoding_1_1>::EndOfStream),
        };
        self.data = buffer;
        self.data.bytes_to_skip = lazy_value.encoded_value.total_length();
        Ok(RawStreamItem::Value(lazy_value))
    }

    pub fn next<'top>(&'top mut self) -> IonResult<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    where
        'data: 'top,
    {
        let mut buffer = self.data.advance_to_next_item()?;
        if buffer.is_empty() {
            return Ok(LazyRawStreamItem::<BinaryEncoding_1_1>::EndOfStream);
        }

        let mut type_descriptor = buffer.peek_type_descriptor()?;
        if type_descriptor.is_nop() {
            println!("Nop, reading sled");
            (_, buffer) = buffer.consume_nop_padding(type_descriptor)?;
            if buffer.is_empty() {
                println!("Reached end of stream");
                return Ok(LazyRawStreamItem::<BinaryEncoding_1_1>::EndOfStream);
            }
        }
        if type_descriptor.is_ivm_start() {
            return self.read_ivm(buffer);
        }
        println!("Reading value");
        self.read_value(buffer)
    }
}

impl<'data> Sealed for LazyRawBinaryReader_1_1<'data> {}

impl<'data> LazyRawReader<'data, BinaryEncoding_1_1> for LazyRawBinaryReader_1_1<'data> {
    fn new(data: &'data [u8]) -> Self {
        Self::new(data)
    }

    fn next<'top>(
        &'top mut self,
        allocator: &'top BumpAllocator,
    ) -> IonResult<LazyRawStreamItem<'top, BinaryEncoding_1_1>>
    where
        'data: 'top,
    {
        self.next()
    }

    fn resume_at_offset(data: &'data [u8], offset: usize, _saved_state: <BinaryEncoding_1_1 as LazyDecoder>::ReaderSavedState)
        -> Self
    {
        Self::new_with_offset(data, offset)
    }

    fn position(&self) -> usize {
        self.data.offset() + self.data.bytes_to_skip
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::raw::v1_1::reader::LazyRawBinaryReader_1_1;
    use crate::{IonResult, IonType};

    #[test]
    fn nop() -> IonResult<()> {
        let data: Vec<u8> = vec![
            0xe0, 0x01, 0x01, 0xea, // IVM
            0xEC, // 1-Byte NOP
            0xEC, 0xEC, // 2-Byte NOP
            0xEC, 0xEC, 0xEC, // 3-Byte Nop
            0xED, 0x05, 0x00, 0x00, // 4-Byte NOP
            0xea, // null.null
        ];

        let mut reader = LazyRawBinaryReader_1_1::new(&data);
        let _ivm = reader.next()?.expect_ivm()?;

        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_null()?,
            IonType::Null
        );

        Ok(())
    }
}
