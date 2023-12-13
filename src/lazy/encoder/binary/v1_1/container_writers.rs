use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;

use crate::lazy::encoder::binary::v1_1::value_writer::BinaryAnnotatableValueWriter_1_1;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::IonResult;

/// A helper type that holds fields and logic that is common to [`BinaryListWriter_1_1`],
/// [`BinarySExpWriter_1_1`], and [`BinaryStructWriter_1_1`].
pub struct BinaryContainerWriter_1_1<'value, 'top> {
    // A byte containing the high nibble of the encoded container's type descriptor.
    type_code: u8,
    // An allocator reference that can be shared with nested container writers
    allocator: &'top BumpAllocator,
    // The buffer containing the parent's encoded body. When this list writer is finished encoding
    // its own data, a header will be written to the parent and then the list body will be copied
    // over.
    parent_buffer: &'value mut BumpVec<'top, u8>,
}

impl<'value, 'top> BinaryContainerWriter_1_1<'value, 'top> {
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

    pub fn write_values<'a, F>(self, _write_fn: F) -> IonResult<()>
    where
        'top: 'a,
        F: FnOnce(BinaryContainerValuesWriter_1_1<'a>) -> IonResult<BumpVec<'a, u8>>,
    {
        todo!()
    }

    fn write_header_and_encoded_body(&mut self, _body: &[u8]) -> IonResult<()> {
        todo!()
    }
}

pub struct BinaryContainerValuesWriter_1_1<'value> {
    allocator: &'value BumpAllocator,
    buffer: BumpVec<'value, u8>,
}

impl<'value> BinaryContainerValuesWriter_1_1<'value> {
    pub fn new(allocator: &'value BumpAllocator) -> Self {
        let buffer = BumpVec::new_in(allocator);
        Self { allocator, buffer }
    }

    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let annotated_value_writer =
            BinaryAnnotatableValueWriter_1_1::new(self.allocator, &mut self.buffer);
        value.write_as_ion(annotated_value_writer)?;
        Ok(self)
    }
}

pub struct BinaryListValuesWriter_1_1<'value> {
    values_writer: BinaryContainerValuesWriter_1_1<'value>,
}

impl<'value> BinaryListValuesWriter_1_1<'value> {
    pub fn new(values_writer: BinaryContainerValuesWriter_1_1<'value>) -> Self {
        Self { values_writer }
    }
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.values_writer.write(value)?;
        Ok(self)
    }
}

impl<'value> MakeValueWriter for BinaryListValuesWriter_1_1<'value> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_1<'a, 'value> where Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_1::new(
            self.values_writer.allocator,
            &mut self.values_writer.buffer,
        )
    }
}

impl<'value> SequenceWriter for BinaryListValuesWriter_1_1<'value> {
    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
        }
    }
}

pub struct BinaryListWriter_1_1<'value, 'top> {
    container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinaryListWriter_1_1<'value, 'top> {
    pub fn new(container_writer: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self { container_writer }
    }

    pub fn write_values<'a, F>(self, write_fn: F) -> IonResult<()>
    where
        'top: 'a,
        F: FnOnce(&mut BinaryListValuesWriter_1_1<'a>) -> IonResult<()>,
    {
        self.container_writer
            .write_values(|container_values_writer| {
                let mut list_values_writer =
                    BinaryListValuesWriter_1_1::new(container_values_writer);
                write_fn(&mut list_values_writer)?;
                Ok(list_values_writer.values_writer.buffer)
            })
    }
}

pub struct BinarySExpValuesWriter_1_1<'value> {
    values_writer: BinaryContainerValuesWriter_1_1<'value>,
}

impl<'value> BinarySExpValuesWriter_1_1<'value> {
    pub fn new(values_writer: BinaryContainerValuesWriter_1_1<'value>) -> Self {
        Self { values_writer }
    }
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.values_writer.write(value)?;
        Ok(self)
    }
}

impl<'value> MakeValueWriter for BinarySExpValuesWriter_1_1<'value> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_1<'a, 'value> where Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_1::new(
            self.values_writer.allocator,
            &mut self.values_writer.buffer,
        )
    }
}

impl<'value> SequenceWriter for BinarySExpValuesWriter_1_1<'value> {
    delegate! {
        to self {
            fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self>;
        }
    }
}

pub struct BinarySExpWriter_1_1<'value, 'top> {
    container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinarySExpWriter_1_1<'value, 'top> {
    pub fn new(sequence_writer: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self {
            container_writer: sequence_writer,
        }
    }

    pub fn write_values<'a, F>(self, write_fn: F) -> IonResult<()>
    where
        'top: 'a,
        F: FnOnce(&mut BinarySExpValuesWriter_1_1<'a>) -> IonResult<()>,
    {
        self.container_writer
            .write_values(|container_values_writer| {
                let mut sexp_values_writer =
                    BinarySExpValuesWriter_1_1::new(container_values_writer);
                write_fn(&mut sexp_values_writer)?;
                Ok(sexp_values_writer.values_writer.buffer)
            })
    }
}

pub struct BinaryStructFieldsWriter_1_1<'value> {
    container_values_writer: BinaryContainerValuesWriter_1_1<'value>,
}

impl<'value> BinaryStructFieldsWriter_1_1<'value> {
    pub fn new(container_values_writer: BinaryContainerValuesWriter_1_1<'value>) -> Self {
        Self {
            container_values_writer,
        }
    }

    pub fn write<A: AsRawSymbolTokenRef, V: WriteAsIon>(
        &mut self,
        _name: A,
        _value: V,
    ) -> IonResult<&mut Self> {
        todo!()
    }
}

impl<'value> StructWriter for BinaryStructFieldsWriter_1_1<'value> {
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

pub struct BinaryStructWriter_1_1<'value, 'top> {
    container_writer: BinaryContainerWriter_1_1<'value, 'top>,
}

impl<'value, 'top> BinaryStructWriter_1_1<'value, 'top> {
    pub fn new(container: BinaryContainerWriter_1_1<'value, 'top>) -> Self {
        Self {
            container_writer: container,
        }
    }

    pub fn write_fields<'a, F>(self, write_fn: F) -> IonResult<()>
    where
        'top: 'a,
        F: FnOnce(&mut BinaryStructFieldsWriter_1_1<'a>) -> IonResult<()>,
    {
        self.container_writer
            .write_values(|container_values_writer| {
                let mut struct_fields_writer =
                    BinaryStructFieldsWriter_1_1::new(container_values_writer);
                write_fn(&mut struct_fields_writer)?;
                Ok(struct_fields_writer.container_values_writer.buffer)
            })
    }
}
