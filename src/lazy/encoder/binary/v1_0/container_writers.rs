use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use ice_code::ice as cold_path;

use crate::binary::var_uint::VarUInt;
use crate::lazy::encoder::binary::v1_0::value_writer::{BinaryValueWriter_1_0, MAX_INLINE_LENGTH};
use crate::lazy::encoder::value_writer::internal::{FieldEncoder, MakeValueWriter};
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::{EncodingError, IonFailure};
use crate::{IonError, IonResult, RawSymbolTokenRef, SymbolId};

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
    child_values_buffer: BumpVec<'top, u8>,
    parent_buffer: &'value mut BumpVec<'top, u8>,
    // In binary Ion 1.0, only symbol IDs can be used as annotations.
    annotations: Option<BumpVec<'top, SymbolId>>,
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
            child_values_buffer: BumpVec::with_capacity_in(
                DEFAULT_CONTAINER_BUFFER_SIZE,
                allocator,
            ),
            parent_buffer: buffer,
            annotations: None,
        }
    }

    pub fn with_annotations<S: AsRawSymbolTokenRef, I: IntoIterator<Item = S>>(
        mut self,
        annotations: I,
    ) -> IonResult<Self> {
        let iterator = annotations.into_iter();
        let mut symbol_ids = BumpVec::with_capacity_in(iterator.size_hint().0, self.allocator);
        for annotation in iterator {
            match annotation.as_raw_symbol_token_ref() {
                RawSymbolTokenRef::SymbolId(symbol_id) => symbol_ids.push(symbol_id),
                RawSymbolTokenRef::Text(text) => {
                    return cold_path! {
                        IonResult::encoding_error(
                            format!("binary Ion 1.0 does not support text annotation literals (received '{}')", text)
                        )
                    };
                }
            }
        }
        self.annotations = Some(symbol_ids);
        Ok(self)
    }

    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let value_writer =
            BinaryValueWriter_1_0::new(self.allocator, &mut self.child_values_buffer);
        value.write_as_ion(value_writer)?;
        Ok(self)
    }

    pub fn child_values_buffer(&self) -> &[u8] {
        self.child_values_buffer.as_slice()
    }

    pub fn end(mut self) -> IonResult<()> {
        match self.annotations.take() {
            None => self.write_unannotated_value_to_parent_buffer(),
            Some(annotations) => self.write_annotated_value_to_parent_buffer(annotations),
        }
    }

    /// Encodes the container's annotations wrapper and copies the completed value to the parent
    /// encoding buffer.
    pub fn write_annotated_value_to_parent_buffer(
        &mut self,
        annotations: BumpVec<'top, SymbolId>,
    ) -> IonResult<()> {
        // The sequence of VarUInt-encoded symbol IDs
        let mut encoded_sequence = BumpVec::new_in(self.allocator);
        for annotation in annotations {
            VarUInt::write_u64(&mut encoded_sequence, annotation as u64)?;
        }

        // The VarUInt-encoded length of the above sequence
        let mut encoded_sequence_length = BumpVec::new_in(self.allocator);
        VarUInt::write_u64(&mut encoded_sequence_length, encoded_sequence.len() as u64)?;

        // The encoded body of the container
        let container_body_length = self.child_values_buffer.len();
        // The method `write_annotated_value_to_parent_buffer` encodes the container's header
        // (including the length) to the parent buffer. In this step, we calculate how big that
        // header will be, so we can factor it into the annotations wrapper's declared length.
        let container_header_length = match container_body_length {
            0..=MAX_INLINE_LENGTH => 1,
            length => 1 + VarUInt::encoded_size_of(length as u64),
        };

        let envelope_length = encoded_sequence_length.len()
            + encoded_sequence.len()
            + container_header_length
            + container_body_length;
        match envelope_length {
            0..=MAX_INLINE_LENGTH => self.parent_buffer.push(0xE0u8 | envelope_length as u8),
            _ => {
                self.parent_buffer.push(0xEE); // Annotations wrapper w/VarUInt-encoded length
                VarUInt::write_u64(self.parent_buffer, envelope_length as u64)?;
            }
        }

        self.parent_buffer.extend_from_slices_copy(&[
            encoded_sequence_length.as_slice(),
            encoded_sequence.as_slice(),
        ]);

        // At this point, the parent container has the complete encoding of the annotations wrapper
        // that prefixes the encoding of the value itself. Now we delegate the value's encoding
        // to `write_unannotated...` to handle.
        self.write_unannotated_value_to_parent_buffer()
    }

    /// Encodes the container's header, then copies the header and body bytes to the parent buffer.
    pub fn write_unannotated_value_to_parent_buffer(&mut self) -> IonResult<()> {
        // Write the appropriate opcode for a container of this length.
        let encoded_length = self.child_values_buffer.len();
        match encoded_length {
            0..=MAX_INLINE_LENGTH => {
                let opcode = self.type_code | encoded_length as u8;
                self.parent_buffer.push(opcode);
            }
            _ => {
                let opcode = self.type_code | 0x0E; // Container w/VarUInt length
                self.parent_buffer.push(opcode);
                VarUInt::write_u64(self.parent_buffer, encoded_length as u64)?;
            }
        }
        self.parent_buffer
            .extend_from_slice_copy(self.child_values_buffer.as_slice());
        Ok(())
    }
}

// This value was chosen somewhat arbitrarily and can be modified as needed. Choosing a value that
// is too low will lead to performance degradation as the buffer will require multiple
// reallocations/copies.
const DEFAULT_CONTAINER_BUFFER_SIZE: usize = 512;

pub struct BinaryListWriter_1_0<'value, 'top> {
    pub(crate) container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinaryListWriter_1_0<'value, 'top> {
    pub(crate) fn with_container_writer(
        container_writer: BinaryContainerWriter_1_0<'value, 'top>,
    ) -> Self {
        Self { container_writer }
    }

    pub(crate) fn new(
        allocator: &'top BumpAllocator,
        buffer: &'value mut BumpVec<'top, u8>,
    ) -> Self {
        const LIST_TYPE_CODE: u8 = 0xB0;
        BinaryListWriter_1_0::with_container_writer(BinaryContainerWriter_1_0::new(
            LIST_TYPE_CODE,
            allocator,
            buffer,
        ))
    }

    pub(crate) fn with_annotations<S: AsRawSymbolTokenRef, I: IntoIterator<Item = S>>(
        mut self,
        annotations: I,
    ) -> IonResult<Self> {
        self.container_writer = self.container_writer.with_annotations(annotations)?;
        Ok(self)
    }

    pub(crate) fn child_values_buffer(&self) -> &[u8] {
        self.container_writer.child_values_buffer()
    }
}

impl<'value, 'top> MakeValueWriter for BinaryListWriter_1_0<'value, 'top> {
    type ValueWriter<'a> = BinaryValueWriter_1_0<'a, 'top> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryValueWriter_1_0::new(
            self.container_writer.allocator,
            &mut self.container_writer.child_values_buffer,
        )
    }
}

impl<'value, 'top> SequenceWriter for BinaryListWriter_1_0<'value, 'top> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.end()
    }
}

impl<'value, 'top> MakeValueWriter for BinarySExpWriter_1_0<'value, 'top> {
    type ValueWriter<'a> = BinaryValueWriter_1_0<'a, 'top> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryValueWriter_1_0::new(
            self.container_writer.allocator,
            &mut self.container_writer.child_values_buffer,
        )
    }
}

impl<'value, 'top> SequenceWriter for BinarySExpWriter_1_0<'value, 'top> {
    type Resources = ();

    fn close(self) -> IonResult<Self::Resources> {
        self.container_writer.end()
    }
}

pub struct BinarySExpWriter_1_0<'value, 'top> {
    container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinarySExpWriter_1_0<'value, 'top> {
    pub(crate) fn with_container_writer(
        container_writer: BinaryContainerWriter_1_0<'value, 'top>,
    ) -> Self {
        Self { container_writer }
    }

    pub(crate) fn new(
        allocator: &'top BumpAllocator,
        buffer: &'value mut BumpVec<'top, u8>,
    ) -> Self {
        const SEXP_TYPE_CODE: u8 = 0xC0;
        let container_writer = BinaryContainerWriter_1_0::new(SEXP_TYPE_CODE, allocator, buffer);
        Self::with_container_writer(container_writer)
    }

    pub(crate) fn with_annotations<S: AsRawSymbolTokenRef, I: IntoIterator<Item = S>>(
        mut self,
        annotations: I,
    ) -> IonResult<Self> {
        self.container_writer = self.container_writer.with_annotations(annotations)?;
        Ok(self)
    }

    pub fn buffer(&self) -> &[u8] {
        self.container_writer.child_values_buffer()
    }
}

pub struct BinaryStructWriter_1_0<'value, 'top> {
    container_writer: BinaryContainerWriter_1_0<'value, 'top>,
}

impl<'value, 'top> BinaryStructWriter_1_0<'value, 'top> {
    pub(crate) fn with_container_writer(
        container: BinaryContainerWriter_1_0<'value, 'top>,
    ) -> Self {
        Self {
            container_writer: container,
        }
    }

    pub(crate) fn new(
        allocator: &'top BumpAllocator,
        buffer: &'value mut BumpVec<'top, u8>,
    ) -> Self {
        const STRUCT_TYPE_CODE: u8 = 0xD0;
        Self::with_container_writer(BinaryContainerWriter_1_0::new(
            STRUCT_TYPE_CODE,
            allocator,
            buffer,
        ))
    }

    pub(crate) fn with_annotations<S: AsRawSymbolTokenRef, I: IntoIterator<Item = S>>(
        mut self,
        annotations: I,
    ) -> IonResult<Self> {
        self.container_writer = self.container_writer.with_annotations(annotations)?;
        Ok(self)
    }

    pub fn buffer(&self) -> &[u8] {
        self.container_writer.child_values_buffer()
    }
}

impl<'value, 'top> FieldEncoder for BinaryStructWriter_1_0<'value, 'top> {
    fn encode_field_name(&mut self, name: impl AsRawSymbolTokenRef) -> IonResult<()> {
        // Write the field name
        let sid = match name.as_raw_symbol_token_ref() {
            RawSymbolTokenRef::SymbolId(sid) => sid,
            RawSymbolTokenRef::Text(text) => {
                return Err(IonError::Encoding(EncodingError::new(format!(
                    "tried to write a text literal using the v1.0 raw binary writer: '{text}'"
                ))));
            }
        };
        VarUInt::write_u64(&mut self.container_writer.child_values_buffer, sid as u64)?;
        Ok(())
    }
}

impl<'value, 'top> MakeValueWriter for BinaryStructWriter_1_0<'value, 'top> {
    type ValueWriter<'a> = BinaryValueWriter_1_0<'a, 'top>
    where
        Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryValueWriter_1_0::new(
            self.container_writer.allocator,
            &mut self.container_writer.child_values_buffer,
        )
    }
}

impl<'value, 'top> StructWriter for BinaryStructWriter_1_0<'value, 'top> {
    fn close(self) -> IonResult<()> {
        self.container_writer.end()
    }
}
