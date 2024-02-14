use crate::binary::var_uint::VarUInt;
use crate::lazy::encoder::binary::v1_0::value_writer::{
    BinaryAnnotatableValueWriter_1_0, MAX_INLINE_LENGTH,
};
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::EncodingError;
use crate::{IonError, IonResult, RawSymbolTokenRef};
use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;

/// A helper type that holds fields and logic that is common to [`BinaryListWriter_1_0`],
/// [`BinarySExpWriter_1_0`], and [`BinaryStructWriter_1_0`].
pub struct BinaryContainerWriter_1_0<'value, 'top> {
    // A byte containing the high nibble of the encoded container's type descriptor.
    type_code: u8,
    // An allocator reference that can be shared with nested container writers
    allocator: &'top BumpAllocator,
    // The buffer containing the parent's encoded body. When this list writer is finished encoding
    // its own data, a header will be written to the parent and then the list body will be copied
    // over.
    parent_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryContainerWriter_1_0<'value, 'top> {
    pub fn new(
        type_code: u8,
        allocator: &'top BumpAllocator,
        parent_buffer: &'value mut BumpVec<'top, u8>,
    ) -> Self {
        Self {
            type_code,
            allocator,
            parent_buffer,
        }
    }

    pub fn write_values<'a, F>(mut self, write_fn: F) -> IonResult<()>
    where
        'top: 'a,
        F: FnOnce(BinaryContainerValuesWriter_1_0<'a>) -> IonResult<BumpVec<'a, u8>>,
    {
        let container_values_writer = BinaryContainerValuesWriter_1_0::new(self.allocator);
        let encoded_values = write_fn(container_values_writer)?;
        self.write_header_and_encoded_body(encoded_values.as_slice())
    }

    fn write_header_and_encoded_body(&mut self, body: &[u8]) -> IonResult<()> {
        let body_length = body.len();
        if body_length <= MAX_INLINE_LENGTH {
            let type_descriptor = self.type_code | (body_length as u8);
            self.parent_buffer.push(type_descriptor);
        } else {
            self.parent_buffer.push(self.type_code | 0xE);
            VarUInt::write_u64(&mut self.parent_buffer, body_length as u64)?;
        }
        self.parent_buffer.extend_from_slice_copy(body);
        Ok(())
    }
}

pub struct BinaryContainerValuesWriter_1_0<'value> {
    allocator: &'value BumpAllocator,
    buffer: BumpVec<'value, u8>,
}

// This value was chosen somewhat arbitrarily and can be modified as needed. Choosing a value that
// is too low will lead to performance degradation as the buffer will require multiple
// reallocations/copies.
const DEFAULT_CONTAINER_BUFFER_SIZE: usize = 512;

impl<'value> BinaryContainerValuesWriter_1_0<'value> {
    pub fn new(allocator: &'value BumpAllocator) -> Self {
        let buffer = BumpVec::with_capacity_in(DEFAULT_CONTAINER_BUFFER_SIZE, allocator);
        Self { allocator, buffer }
    }

    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let annotated_value_writer =
            BinaryAnnotatableValueWriter_1_0::new(self.allocator, &mut self.buffer);
        value.write_as_ion(annotated_value_writer)?;
        Ok(self)
    }
}

pub struct BinaryListValuesWriter_1_0<'value> {
    values_writer: BinaryContainerValuesWriter_1_0<'value>,
}

impl<'value> BinaryListValuesWriter_1_0<'value> {
    pub fn new(values_writer: BinaryContainerValuesWriter_1_0<'value>) -> Self {
        Self { values_writer }
    }
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.values_writer.write(value)?;
        Ok(self)
    }
}

impl<'value> MakeValueWriter for BinaryListValuesWriter_1_0<'value> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_0<'a, 'value> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_0::new(
            self.values_writer.allocator,
            &mut self.values_writer.buffer,
        )
    }
}

impl<'value> SequenceWriter for BinaryListValuesWriter_1_0<'value> {
    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
        }
    }
}

pub struct BinaryListWriter_1_0<'value, 'top> {
    container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinaryListWriter_1_0<'value, 'top> {
    pub fn new(container_writer: BinaryContainerWriter_1_0<'value, 'top>) -> Self {
        Self { container_writer }
    }

    pub fn write_values<'a, F>(self, write_fn: F) -> IonResult<()>
    where
        'top: 'a,
        F: FnOnce(&mut BinaryListValuesWriter_1_0<'a>) -> IonResult<()>,
    {
        self.container_writer
            .write_values(|container_values_writer| {
                let mut list_values_writer =
                    BinaryListValuesWriter_1_0::new(container_values_writer);
                write_fn(&mut list_values_writer)?;
                Ok(list_values_writer.values_writer.buffer)
            })
    }
}

pub struct BinarySExpValuesWriter_1_0<'value> {
    values_writer: BinaryContainerValuesWriter_1_0<'value>,
}

impl<'value> BinarySExpValuesWriter_1_0<'value> {
    pub fn new(values_writer: BinaryContainerValuesWriter_1_0<'value>) -> Self {
        Self { values_writer }
    }
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.values_writer.write(value)?;
        Ok(self)
    }
}

impl<'value> MakeValueWriter for BinarySExpValuesWriter_1_0<'value> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_0<'a, 'value> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_0::new(
            self.values_writer.allocator,
            &mut self.values_writer.buffer,
        )
    }
}

impl<'value> SequenceWriter for BinarySExpValuesWriter_1_0<'value> {
    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
        }
    }
}

pub struct BinarySExpWriter_1_0<'value, 'top> {
    container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinarySExpWriter_1_0<'value, 'top> {
    pub fn new(sequence_writer: BinaryContainerWriter_1_0<'value, 'top>) -> Self {
        Self {
            container_writer: sequence_writer,
        }
    }

    pub fn write_values<'a, F>(self, write_fn: F) -> IonResult<()>
    where
        'top: 'a,
        F: FnOnce(&mut BinarySExpValuesWriter_1_0<'a>) -> IonResult<()>,
    {
        self.container_writer
            .write_values(|container_values_writer| {
                let mut sexp_values_writer =
                    BinarySExpValuesWriter_1_0::new(container_values_writer);
                write_fn(&mut sexp_values_writer)?;
                Ok(sexp_values_writer.values_writer.buffer)
            })
    }
}

pub struct BinaryStructFieldsWriter_1_0<'value> {
    container_values_writer: BinaryContainerValuesWriter_1_0<'value>,
}

impl<'value> BinaryStructFieldsWriter_1_0<'value> {
    pub fn new(container_values_writer: BinaryContainerValuesWriter_1_0<'value>) -> Self {
        Self {
            container_values_writer,
        }
    }

    pub fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        name: A,
        value: V,
    ) -> IonResult<&mut Self> {
        // Write the field name
        let sid = match name.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => sid,
            RawSymbolTokenRef::Text(text) => {
                return Err(IonError::Encoding(EncodingError::new(format!(
                    "tried to write a text literal using the v1.0 raw binary writer: '{text}'"
                ))));
            }
        };
        VarUInt::write_u64(&mut self.container_values_writer.buffer, sid as u64)?;

        // Write the field value
        self.container_values_writer.write(value)?;
        Ok(self)
    }
}

impl<'value> StructWriter for BinaryStructFieldsWriter_1_0<'value> {
    delegate! {
        to self {
            fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
                &mut self,
                name: A,
                value: V,
            ) -> IonResult<&mut Self>;
        }
    }
}

pub struct BinaryStructWriter_1_0<'value, 'top> {
    container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinaryStructWriter_1_0<'value, 'top> {
    pub fn new(container: BinaryContainerWriter_1_0<'value, 'top>) -> Self {
        Self {
            container_writer: container,
        }
    }

    pub fn write_fields<'a, F>(self, write_fn: F) -> IonResult<()>
    where
        'top: 'a,
        F: FnOnce(&mut BinaryStructFieldsWriter_1_0<'a>) -> IonResult<()>,
    {
        self.container_writer
            .write_values(|container_values_writer| {
                let mut struct_fields_writer =
                    BinaryStructFieldsWriter_1_0::new(container_values_writer);
                write_fn(&mut struct_fields_writer)?;
                Ok(struct_fields_writer.container_values_writer.buffer)
            })
    }
}
