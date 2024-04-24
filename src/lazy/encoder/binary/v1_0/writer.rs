use std::io::Write;

use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;

use crate::lazy::encoder::binary::v1_0::value_writer::BinaryValueWriter_1_0;
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::LazyRawWriter;
use crate::lazy::encoding::Encoding;
use crate::unsafe_helpers::{mut_ref_to_ptr, ptr_to_mut_ref};
use crate::write_config::{WriteConfig, WriteConfigKind};
use crate::IonResult;

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

/// The initial size of the backing array for the writer's bump allocator.
// This value was chosen somewhat arbitrarily and can be changed as needed.
const DEFAULT_BUMP_SIZE: usize = 16 * 1024;

impl<W: Write> LazyRawBinaryWriter_1_0<W> {
    /// Constructs a new binary writer and writes an Ion 1.0 Version Marker to output.
    pub fn new(mut output: W) -> IonResult<Self> {
        // Write the Ion 1.0 IVM
        output.write_all(&[0xE0, 0x01, 0x00, 0xEA])?;
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
        // Now that we've written the encoding buffer's contents to output, clear it.
        self.encoding_buffer_ptr = None;
        // Clear the allocator. A new encoding buffer will be allocated on the next write.
        allocator.reset();
        Ok(())
    }

    pub(crate) fn value_writer(&mut self) -> BinaryValueWriter_1_0<'_, '_> {
        let top_level = match self.encoding_buffer_ptr {
            // If the `encoding_buffer_ptr` is set, we already allocated an encoding buffer on
            // a previous call to `value_writer()`. Dereference the pointer and continue encoding
            // to that buffer.
            Some(ptr) => unsafe { ptr_to_mut_ref::<'_, BumpVec<'_, u8>>(ptr) },
            // Otherwise, allocate a new encoding buffer and set the pointer to refer to it.
            None => {
                let buffer = self
                    .allocator
                    .alloc_with(|| BumpVec::new_in(&self.allocator));
                self.encoding_buffer_ptr = Some(mut_ref_to_ptr(buffer));
                buffer
            }
        };
        let annotated_value_writer = BinaryValueWriter_1_0::new(&self.allocator, top_level);
        annotated_value_writer
    }
}

impl<W: Write> Sealed for LazyRawBinaryWriter_1_0<W> {}

impl<W: Write> LazyRawWriter<W> for LazyRawBinaryWriter_1_0<W> {
    fn new(output: W) -> IonResult<Self> {
        Self::new(output)
    }

    /// Build binary writer based on given writer configuration
    fn build<E: Encoding>(config: WriteConfig<E>, output: W) -> IonResult<Self> {
        match &config.kind {
            WriteConfigKind::Text(_) => {
                unreachable!("Text writer can not be created from binary encoding")
            }
            WriteConfigKind::Binary(_) => LazyRawBinaryWriter_1_0::new(output),
        }
    }

    delegate! {
        to self {
            fn flush(&mut self) -> IonResult<()>;
        }
    }

    fn output(&self) -> &W {
        &self.output
    }

    fn output_mut(&mut self) -> &mut W {
        &mut self.output
    }
}

impl<W: Write> MakeValueWriter for LazyRawBinaryWriter_1_0<W> {
    type ValueWriter<'a> = BinaryValueWriter_1_0<'a, 'a> where Self: 'a;

    fn make_value_writer(&mut self) -> Self::ValueWriter<'_> {
        self.value_writer()
    }
}

impl<W: Write> SequenceWriter for LazyRawBinaryWriter_1_0<W> {
    type Resources = W;

    fn close(mut self) -> IonResult<Self::Resources> {
        self.flush()?;
        Ok(self.output)
    }
    // Uses the default method implementations from SequenceWriter
}
