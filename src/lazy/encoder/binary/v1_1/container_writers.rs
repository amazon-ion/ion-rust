use std::mem;

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;

use crate::lazy::encoder::binary::v1_1::value_writer::BinaryAnnotatableValueWriter_1_1;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::{FlexUInt, IonResult, RawSymbolTokenRef};

/// A helper type that holds fields and logic that is common to [`BinaryListWriter_1_1`],
/// [`BinarySExpWriter_1_1`], and [`BinaryStructWriter_1_1`].
///
/// The [`BinaryContainerWriter_1_1`] does not know which type of container it is writing or whether that container
/// is length-prefixed or delimited. It only encodes provided values to its buffer. The owner of the
/// [`BinaryContainerWriter_1_1`] is responsible for:
///   * writing the correct opcode.
///   * copying the encoded data to the parent buffer (in the case of a length-prefixed container).
///   * writing field names to the [`BinaryContainerWriter_1_1`]'s buffer before each value (in the case of a struct).
pub(crate) struct BinaryContainerWriter_1_1<'value, 'top> {
    // An allocator reference that can be shared with nested container writers
    allocator: &'top BumpAllocator,
    // The buffer to which child values will be encoded. In the case of:
    //   1. a length-prefixed container, this will be a new buffer bump-allocated specifically for this
    //      container.
    //   2. a delimited container, this will be the parent's own encoding buffer, to which the delimited
    //      container start opcode has already been written.
    buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryContainerWriter_1_1<'value, 'top> {
    pub fn new(allocator: &'top BumpAllocator, buffer: &'value mut BumpVec<'top, u8>) -> Self {
        Self { allocator, buffer }
    }

    /// Constructs a new [`BinaryAnnotatableValueWriter_1_1`] using this [`BinaryContainerWriter_1_1`]'s
    /// allocator and targeting its buffer.
    fn value_writer<'a>(&'a mut self) -> BinaryAnnotatableValueWriter_1_1<'a, 'top> {
        BinaryAnnotatableValueWriter_1_1::new(self.allocator, self.buffer())
    }

    /// Encodes the provided `value` to the [`BinaryContainerWriter_1_1`]'s buffer.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let annotated_value_writer = self.value_writer();
        value.write_as_ion(annotated_value_writer)?;
        Ok(self)
    }
    pub fn allocator(&self) -> &'top BumpAllocator {
        self.allocator
    }
    pub fn buffer(&mut self) -> &'_ mut BumpVec<'top, u8> {
        self.buffer
    }
}

pub struct BinaryListWriter_1_1<'value, 'top> {
    pub(crate) container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinaryListWriter_1_1<'value, 'top> {
    pub(crate) fn new(container_writer: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self { container_writer }
    }
}

impl<'value, 'top> MakeValueWriter for BinaryListWriter_1_1<'value, 'top> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_1<'a, 'top> where Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        self.container_writer.value_writer()
    }
}

impl<'value, 'top> SequenceWriter for BinaryListWriter_1_1<'value, 'top> {
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write(value)?;
        Ok(self)
    }
}

pub struct BinarySExpWriter_1_1<'value, 'top> {
    pub(crate) container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinarySExpWriter_1_1<'value, 'top> {
    pub(crate) fn new(sequence_writer: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self {
            container_writer: sequence_writer,
        }
    }
}

impl<'value, 'top> MakeValueWriter for BinarySExpWriter_1_1<'value, 'top> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_1<'a, 'top> where Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_1::new(
            self.container_writer.allocator(),
            self.container_writer.buffer(),
        )
    }
}

impl<'value, 'top> SequenceWriter for BinarySExpWriter_1_1<'value, 'top> {
    fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.container_writer.write(value)?;
        Ok(self)
    }
}

pub struct BinaryStructWriter_1_1<'value, 'top> {
    container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinaryStructWriter_1_1<'value, 'top> {
    pub(crate) fn new(container_writer: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self { container_writer }
    }

    pub fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        _name: A,
        _value: V,
    ) -> IonResult<&mut Self> {
        todo!()
    }
}

impl<'value, 'top> StructWriter for BinaryStructWriter_1_1<'value, 'top> {
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
