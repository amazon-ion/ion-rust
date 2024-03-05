use crate::element::writer::WriteConfigKind;
use crate::lazy::encoder::binary::v1_1::value_writer::BinaryAnnotatableValueWriter_1_1;
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::LazyRawWriter;
use crate::lazy::encoding::Encoding;
use crate::unsafe_helpers::{mut_ref_to_ptr, ptr_to_mut_ref};
use crate::{IonResult, WriteConfig};
use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;
use std::io::Write;

/// A "raw"-level streaming binary Ion 1.1 writer. This writer does not provide encoding module
/// management; symbol- and macro- related operations require the caller to perform their own
/// correctness checking and provide valid IDs.
pub struct LazyRawBinaryWriter_1_1<W: Write> {
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

/// The initial size of the backing array for the writer's bump allocator.
// This value was chosen somewhat arbitrarily and can be changed as needed.
const DEFAULT_BUMP_SIZE: usize = 16 * 1024;

impl<W: Write> LazyRawBinaryWriter_1_1<W> {
    /// Constructs a new binary writer and writes an Ion 1.1 Version Marker to output.
    pub fn new(mut output: W) -> IonResult<Self> {
        // Write the Ion 1.1 IVM
        output.write_all(&[0xE0, 0x01, 0x01, 0xEA])?;
        // Construct the writer
        Ok(Self {
            output,
            allocator: BumpAllocator::with_capacity(DEFAULT_BUMP_SIZE),
            encoding_buffer_ptr: None,
        })
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
            Some(ptr) => unsafe { ptr_to_mut_ref::<'_, BumpVec<'_, u8>>(*ptr).as_slice() },
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

    // All methods called on the writer are inherently happening at the top level. At the top level,
    // the lifetimes `'value` and `'top` are identical. In this method signature, '_ is used for both.
    pub(crate) fn value_writer(&mut self) -> BinaryAnnotatableValueWriter_1_1<'_, '_> {
        let top_level = match self.encoding_buffer_ptr {
            // If the `encoding_buffer_ptr` is set, we already allocated an encoding buffer on
            // a previous call to `value_writer()`. Dereference the pointer and continue encoding
            // to that buffer.
            Some(ptr) => unsafe { ptr_to_mut_ref::<'_, BumpVec<'_, u8>>(ptr) },
            // Otherwise, allocate a new encoding buffer and set the pointer to refer to it.
            None => {
                let buffer = self.allocator.alloc_with(|| {
                    // Use half of the bump allocator's backing array as an encoding space for this
                    // top level value. The other half of the bump can be used for incidental
                    // bookkeeping.
                    BumpVec::with_capacity_in(DEFAULT_BUMP_SIZE / 2, &self.allocator)
                });
                self.encoding_buffer_ptr = Some(mut_ref_to_ptr(buffer));
                buffer
            }
        };
        let annotated_value_writer =
            BinaryAnnotatableValueWriter_1_1::new(&self.allocator, top_level);
        annotated_value_writer
    }
}

impl<W: Write> Sealed for LazyRawBinaryWriter_1_1<W> {}

impl<W: Write> LazyRawWriter<W> for LazyRawBinaryWriter_1_1<W> {
    fn new(output: W) -> IonResult<Self> {
        Self::new(output)
    }

    fn build<E: Encoding>(config: WriteConfig<E>, output: W) -> IonResult<Self>
    where
        Self: Sized,
    {
        match &config.kind {
            WriteConfigKind::Text(_) => {
                unreachable!("Text writer can not be created from binary encoding")
            }
            WriteConfigKind::Binary(_) => LazyRawBinaryWriter_1_1::new(output),
        }
    }

    delegate! {
        to self {
            fn flush(&mut self) -> IonResult<()>;
        }
    }
}

impl<W: Write> MakeValueWriter for LazyRawBinaryWriter_1_1<W> {
    type ValueWriter<'a> = BinaryAnnotatableValueWriter_1_1<'a, 'a> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        self.value_writer()
    }
}

impl<W: Write> SequenceWriter for LazyRawBinaryWriter_1_1<W> {
    // Uses the default method implementations from SequenceWriter
}
