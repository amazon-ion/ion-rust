use std::io::Write;

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;

use crate::binary::var_uint::VarUInt;
use crate::lazy::encoder::binary::value_writer::{
    BinaryAnnotatableValueWriter_1_0, MAX_INLINE_LENGTH,
};
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::{SequenceWriter, StructWriter};
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::{LazyEncoder, LazyRawWriter};
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::EncodingError;
use crate::{IonError, IonResult, RawSymbolTokenRef};

mod value_writer;

impl LazyEncoder for BinaryEncoding_1_0 {
    type Writer<W: Write> = LazyRawBinaryWriter_1_0<W>;
}

/// A "raw"-level streaming binary Ion writer. This writer does not provide symbol table
/// management; symbol-related operations (e.g. setting field IDs and annotations or writing symbol
/// values) require a valid symbol ID to be provided by the caller.
pub struct LazyRawBinaryWriter_1_0<W: Write> {
    // The sink to which all of the writer's encoded data will be written.
    output: W,
    // A bump allocator that can be used to cheaply create scratch buffers for nested container
    // encoding.
    allocator: BumpAllocator,
    // A pointer to the bump-allocated top-level encoding buffer, if set.
    //
    // This buffer is constructed in `allocator` above, a region of memory over which we have
    // complete control. When the allocator creates a buffer, the buffer has a lifetime equivalent to
    // the lifetime of the function in which it was created. However, we know that the data it contains
    // will continue to be valid even after that method is complete and any return values are dropped.
    // Thus, we store a raw pointer to the buffer and use an `Option` to track whether the pointer
    // is set to a meaningful address. This allows us to refer to the contents of the buffer across
    // multiple mutable calls of `write` and `value_writer()`.
    encoding_buffer_ptr: Option<*mut ()>,
}

impl<W: Write> LazyRawBinaryWriter_1_0<W> {
    /// Constructs a new binary writer and writes an Ion 1.0 Version Marker to output.
    pub fn new(mut output: W) -> IonResult<Self> {
        // Write the Ion 1.0 IVM
        output.write_all(&[0xE0, 0x01, 0x00, 0xEA])?;
        // Construct the writer
        Ok(Self {
            output,
            allocator: BumpAllocator::new(),
            encoding_buffer_ptr: None,
        })
    }

    /// Helper function that turns a raw pointer into a mutable reference of the specified type.
    unsafe fn ptr_to_mut_ref<'a, T>(ptr: *mut ()) -> &'a mut T {
        let typed_ptr: *mut T = ptr.cast();
        &mut *typed_ptr
    }

    /// Helper function that turns a mutable reference into a raw pointer.
    fn mut_ref_to_ptr<T>(reference: &mut T) -> *mut () {
        let ptr: *mut T = reference;
        let untyped_ptr: *mut () = ptr.cast();
        untyped_ptr
    }

    /// Writes the given Rust value to the output stream as a top-level value.
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        value.write_as_ion(self.value_writer())?;
        Ok(self)
    }

    /// Flushes any encoded bytes that have not already been written to the output sink.
    ///
    /// Calling `flush` also releases memory used for bookkeeping and storage, but calling it
    /// frequently can reduce overall throughput.
    pub fn flush(&mut self) -> IonResult<()> {
        // Temporarily break apart `self` to get simultaneous references to its innards.
        let Self {
            output,
            allocator,
            encoding_buffer_ptr,
        } = self;

        let encoding_buffer = match encoding_buffer_ptr {
            // If `encoding_buffer_ptr` is set, get the slice of bytes to which it refers.
            Some(ptr) => unsafe { Self::ptr_to_mut_ref::<'_, BumpVec<'_, u8>>(*ptr).as_slice() },
            // Otherwise, there's nothing in the buffer. Use an empty slice.
            None => &[],
        };
        // Write our top level encoding buffer's contents to the output sink.
        output.write_all(encoding_buffer)?;
        // Flush the output sink, which may have its own buffers.
        output.flush()?;
        // Clear the allocator. A new encoding buffer will be allocated on the next write.
        allocator.reset();
        Ok(())
    }

    fn value_writer(&mut self) -> BinaryAnnotatableValueWriter_1_0<'_, '_> {
        let top_level = match self.encoding_buffer_ptr {
            // If the `encoding_buffer_ptr` is set, we already allocated an encoding buffer on
            // a previous call to `value_writer()`. Dereference the pointer and continue encoding
            // to that buffer.
            Some(ptr) => unsafe { Self::ptr_to_mut_ref::<'_, BumpVec<'_, u8>>(ptr) },
            // Otherwise, allocate a new encoding buffer and set the pointer to refer to it.
            None => {
                let buffer = self
                    .allocator
                    .alloc_with(|| BumpVec::new_in(&self.allocator));
                self.encoding_buffer_ptr = Some(Self::mut_ref_to_ptr(buffer));
                buffer
            }
        };
        let annotated_value_writer =
            BinaryAnnotatableValueWriter_1_0::new(&self.allocator, top_level);
        annotated_value_writer
    }
}

impl<W: Write> Sealed for LazyRawBinaryWriter_1_0<W> {}

impl<W: Write> LazyRawWriter<W> for LazyRawBinaryWriter_1_0<W> {
    fn new(output: W) -> IonResult<Self> {
        Self::new(output)
    }

    delegate! {
        to self {
            fn flush(&mut self) -> IonResult<()>;
        }
    }
}

impl<W: Write> MakeValueWriter for LazyRawBinaryWriter_1_0<W> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_0<'a, 'a> where Self: 'a;

    delegate! {
        to self {
            fn value_writer(&mut self) -> Self::ValueWriter<'_>;
        }
    }
}

impl<W: Write> SequenceWriter for LazyRawBinaryWriter_1_0<W> {
    // Uses the default method implementations from SequenceWriter
}

/// A helper type that holds fields and logic that is common to [`BinaryListWriter_1_0`],
/// [`BinarySExpWriter_1_0`], and [`BinaryStructWriter_1_0`].
pub(crate) struct BinaryContainerWriter_1_0<'value, 'top> {
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
    pub(crate) fn new(
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
        self.parent_buffer.extend_from_slice(body);
        Ok(())
    }
}

pub(crate) struct BinaryContainerValuesWriter_1_0<'value> {
    allocator: &'value BumpAllocator,
    buffer: BumpVec<'value, u8>,
}

impl<'value> BinaryContainerValuesWriter_1_0<'value> {
    pub(crate) fn new(allocator: &'value BumpAllocator) -> Self {
        let buffer = BumpVec::new_in(allocator);
        Self { allocator, buffer }
    }

    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        let annotated_value_writer =
            BinaryAnnotatableValueWriter_1_0::new(&self.allocator, &mut self.buffer);
        value.write_as_ion(annotated_value_writer)?;
        Ok(self)
    }
}

pub struct BinaryListValuesWriter_1_0<'value> {
    values_writer: BinaryContainerValuesWriter_1_0<'value>,
}

impl<'value> BinaryListValuesWriter_1_0<'value> {
    pub(crate) fn new(values_writer: BinaryContainerValuesWriter_1_0<'value>) -> Self {
        Self { values_writer }
    }
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.values_writer.write(value)?;
        Ok(self)
    }
}

impl<'value> MakeValueWriter for BinaryListValuesWriter_1_0<'value> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_0<'a, 'value> where Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_0::new(
            &*self.values_writer.allocator,
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
    pub(crate) fn new(container_writer: BinaryContainerWriter_1_0<'value, 'top>) -> Self {
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
    pub(crate) fn new(values_writer: BinaryContainerValuesWriter_1_0<'value>) -> Self {
        Self { values_writer }
    }
    pub fn write<V: WriteAsIon>(&mut self, value: V) -> IonResult<&mut Self> {
        self.values_writer.write(value)?;
        Ok(self)
    }
}

impl<'value> MakeValueWriter for BinarySExpValuesWriter_1_0<'value> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_0<'a, 'value> where Self: 'a;

    fn value_writer(&mut self) -> Self::ValueWriter<'_> {
        BinaryAnnotatableValueWriter_1_0::new(
            &*self.values_writer.allocator,
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
    pub(crate) fn new(sequence_writer: BinaryContainerWriter_1_0<'value, 'top>) -> Self {
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
    pub(crate) fn new(container_values_writer: BinaryContainerValuesWriter_1_0<'value>) -> Self {
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
    pub(crate) fn new(container: BinaryContainerWriter_1_0<'value, 'top>) -> Self {
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
