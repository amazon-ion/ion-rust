use bumpalo::Bump as BumpAllocator;
use bumpalo::collections::Vec as BumpVec;

use crate::{IonError, IonResult, RawSymbolTokenRef};
use crate::binary::var_uint::VarUInt;
use crate::lazy::encoder::binary::v1_0::value_writer::BinaryAnnotatableValueWriter_1_0;
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::EncodingError;

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
    buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryContainerWriter_1_0<'value, 'top> {
    pub fn new(
        type_code: u8,
        allocator: &'top BumpAllocator,
        buffer: &'value mut BumpVec<'top, u8>,
    ) -> Self {
        Self {
            type_code,
            allocator,
            buffer,
        }
    }

    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let annotated_value_writer =
            BinaryAnnotatableValueWriter_1_0::new(self.allocator, self.buffer);
        value.write_as_ion(annotated_value_writer)?;
        Ok(self)
    }

    pub fn buffer(&self) -> &[u8] {
        self.buffer.as_slice()
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

pub struct BinaryListWriter_1_0<'value, 'top> {
    pub(crate) container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinaryListWriter_1_0<'value, 'top> {
    pub fn new(container_writer: BinaryContainerWriter_1_0<'value, 'top>) -> Self {
        Self { container_writer }
    }

    pub fn buffer(&self) -> &[u8] {
        self.container_writer.buffer()
    }
}

impl<'value, 'top> MakeValueWriter for BinaryListWriter_1_0<'value, 'top> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_0<'a, 'top> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_0::new(
            self.container_writer.allocator,
            self.container_writer.buffer,
        )
    }
}

impl<'value, 'top> SequenceWriter for BinaryListWriter_1_0<'value, 'top> {
    // All default methods
}

impl<'value, 'top> MakeValueWriter for BinarySExpWriter_1_0<'value, 'top> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_0<'a, 'top> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_0::new(
            self.container_writer.allocator,
            self.container_writer.buffer,
        )
    }
}

impl<'value, 'top> SequenceWriter for BinarySExpWriter_1_0<'value, 'top> {
    // All default methods
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

    pub fn buffer(&self) -> &[u8] {
        self.container_writer.buffer()
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

    pub fn buffer(&self) -> &[u8] {
        self.container_writer.buffer()
    }
}

impl<'value, 'top> StructWriter for BinaryStructWriter_1_0<'value, 'top> {
    fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
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
        VarUInt::write_u64(&mut self.container_writer.buffer, sid as u64)?;

        // Write the field value
        self.container_writer.write(value)?;
        Ok(self)
    }
}
