use bumpalo::collections::Vec as BumpVec;
use bumpalo::Bump as BumpAllocator;
use delegate::delegate;
use std::io::Write;

use crate::binary::constants::v1_0::IVM as IVM_1_0;
use crate::lazy::encoder::binary::v1_0::value_writer::BinaryValueWriter_1_0;
use crate::lazy::encoder::binary::AliasableBump;
use crate::lazy::encoder::private::Sealed;
use crate::lazy::encoder::value_writer::internal::MakeValueWriter;
use crate::lazy::encoder::value_writer::SequenceWriter;
use crate::lazy::encoder::write_as_ion::WriteAsIon;
use crate::lazy::encoder::writer::WriterMacroTable;
use crate::lazy::encoder::{
    cap_retained_buffer, LazyRawWriter, Recycle, Reusable, WriterRole, IDLE_RETAIN_CAP,
};
use crate::lazy::encoding::Encoding;
use crate::lazy::expanded::macro_table::EMPTY_MACRO_TABLE;
use crate::unsafe_helpers::{mut_ref_to_ptr, ptr_to_mut_ref, ptr_to_ref};
use crate::write_config::{BinaryWriteConfig, WriteConfig, WriteConfigKind};
use crate::{ContextWriter, IonResult};

/// A "raw"-level streaming binary Ion writer. This writer does not provide symbol table
/// management; symbol-related operations (e.g. setting field IDs and annotations or writing symbol
/// values) require a valid symbol ID to be provided by the caller.
pub struct LazyRawBinaryWriter_1_0<W: Write> {
    // The sink to which all of the writer's encoded data will be written.
    output: W,
    // A bump allocator that can be used to cheaply create scratch buffers for nested container
    // encoding.
    //
    // Held via `AliasableBump` (not `Box`) so the `Bump` has a stable heap address AND deref does
    // not assert unique access: the top-level encoding buffer (a `BumpVec` referenced by
    // `encoding_buffer_ptr`) captures a `&Bump` into this allocator, and that reference must stay
    // valid when the writer is moved. See `AliasableBump` for the full rationale.
    allocator: AliasableBump,
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
pub(crate) const DEFAULT_BUMP_SIZE: usize = 16 * 1024;

// Implemented only for the `Vec<u8>` instantiation: that is the only one the managed writer's
// reusable-writer API needs (`E::Writer<Vec<u8>>: Reusable`), and it is what makes re-seeding the IVM
// below infallible.
impl Reusable for LazyRawBinaryWriter_1_0<Vec<u8>> {}

impl Recycle for LazyRawBinaryWriter_1_0<Vec<u8>> {
    /// Returns this writer to its freshly-built state so it can encode another document, discarding
    /// any buffered (unflushed) content: the output buffer and the scratch arena are emptied, either
    /// is released if it has grown oversized, and -- for [`WriterRole::System`] -- the Ion 1.0 IVM
    /// that `new` emits is re-seeded.
    ///
    /// Nothing is written to any sink here, so bytes the caller wanted emitted must have been
    /// `flush`ed beforehand.
    fn recycle(&mut self, role: WriterRole) {
        // Clear the pointer to the top-level encoding buffer FIRST. The buffer lives inside
        // `allocator`; if the arena below is dropped or rewound while this pointer is still set, the
        // next `value_writer()` call would dereference a dangling pointer.
        self.encoding_buffer_ptr = None;
        if self.allocator.allocated_bytes() > IDLE_RETAIN_CAP {
            // Bound retained memory: drop an oversized arena in favor of a fresh small one.
            self.allocator = AliasableBump::new(BumpAllocator::with_capacity(DEFAULT_BUMP_SIZE));
        } else {
            // Keep the arena warm; `reset` rewinds it without releasing its chunks.
            // SAFETY: `encoding_buffer_ptr` was set to `None` above, so the `&Bump` that
            // `AliasableBump::reset` invalidates has no remaining users.
            unsafe { self.allocator.reset() };
        }
        // Discard anything still buffered. Doing this here rather than in the caller is what makes
        // the "discards unflushed content" contract self-enforcing: capping the buffer below may
        // replace it outright, and the IVM re-seed must land in an otherwise empty buffer.
        self.output.clear();
        // Bound the output buffer too; it grew to hold the largest document this writer encoded.
        // This must precede the IVM below, because replacing the buffer would drop it.
        cap_retained_buffer(&mut self.output);
        if role == WriterRole::System {
            // A freshly built binary writer emits the IVM (see `new`); re-seed it so the reused
            // writer starts a new stream exactly as a fresh one would. Written straight to the `Vec`
            // rather than through the fallible `write_version_marker` to keep `recycle` infallible.
            // Only the system writer carries the prologue -- emitting it on the application writer
            // would corrupt the stream (<IVM><symtab><IVM><data>).
            self.output.extend_from_slice(&IVM_1_0);
        }
    }

    /// Nothing to do: a binary writer derives no state from its [`WriteConfig`]; `build` only
    /// validates that the config is a binary one.
    fn apply_config<E: Encoding>(&mut self, config: &WriteConfig<E>) {
        match config.kind() {
            // Destructured rather than matched with `_` so that a `BinaryWriteConfig` which grows a
            // field stops compiling here instead of silently leaving this writer configured for the
            // previous caller's document.
            WriteConfigKind::Binary(BinaryWriteConfig) => {}
            // Same as `build`'s: an `E`'s writer type and its config kind are chosen together, so a
            // text config can never reach the binary writer.
            WriteConfigKind::Text(_) => {
                unreachable!("Binary writer can not be configured from text encoding")
            }
        }
    }
}

impl<W: Write> LazyRawBinaryWriter_1_0<W> {
    /// Constructs a new binary writer and writes an Ion 1.0 Version Marker to output.
    pub fn new(mut output: W) -> IonResult<Self> {
        // Write the Ion 1.0 IVM
        output.write_all(&IVM_1_0)?;
        // Construct the writer
        Ok(Self {
            output,
            allocator: AliasableBump::new(BumpAllocator::with_capacity(DEFAULT_BUMP_SIZE)),
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
            ..
        } = self;
        if let Some(ptr) = encoding_buffer_ptr {
            let encoding_buffer = unsafe { ptr_to_ref::<'_, BumpVec<'_, u8>>(*ptr).as_slice() };
            // Write our top level encoding buffer's contents to the output sink.
            output.write_all(encoding_buffer)?;
            // Flush the output sink, which may have its own buffers.
            output.flush()?;
        }
        // Now that we've written the encoding buffer's contents to output, clear it.
        self.encoding_buffer_ptr = None;
        // Clear the allocator. A new encoding buffer will be allocated on the next write.
        // SAFETY: the encoding buffer pointer was just set to `None` above, so the `&Bump` that
        // `AliasableBump::reset` invalidates has no remaining users.
        unsafe { allocator.reset() };
        Ok(())
    }

    /// The number of bytes of memory currently held by this writer's scratch arena.
    // Exposed for the reuse tests, which confirm that recycling releases an oversized arena.
    #[cfg(test)]
    pub(crate) fn allocated_bytes(&self) -> usize {
        self.allocator.allocated_bytes()
    }

    fn get_or_allocate_encoding_buffer<'value, 'top>(
        encoding_buffer_ptr: &'value mut Option<*mut ()>,
        allocator: &'top BumpAllocator,
    ) -> &'value mut BumpVec<'top, u8> {
        match encoding_buffer_ptr {
            // If the `encoding_buffer_ptr` is set, we already allocated an encoding buffer on
            // a previous call to `value_writer()`. Dereference the pointer and continue encoding
            // to that buffer.
            Some(ptr) => {
                let new_ptr = *ptr;
                unsafe { ptr_to_mut_ref::<'_, BumpVec<'_, u8>>(new_ptr) }
            }
            None => {
                let encoding_buffer = allocator.alloc_with(|| BumpVec::<u8>::new_in(allocator));
                let ptr = mut_ref_to_ptr(encoding_buffer);
                // SAFETY: We cannot both store `ptr` in `encoding_buffer_ptr` AND turn it into
                //         a mutable BumVec reference to return because this (briefly) constructs
                //         two mutable references. Instead, we store it in `encoding_buffer_ptr`
                //         and then read it from its new location.
                *encoding_buffer_ptr = Some(ptr);
                unsafe { ptr_to_mut_ref::<'_, BumpVec<'_, u8>>(encoding_buffer_ptr.unwrap()) }
            }
        }
    }

    pub(crate) fn value_writer(&mut self) -> BinaryValueWriter_1_0<'_, '_> {
        let Self {
            ref allocator,
            ref mut encoding_buffer_ptr,
            ..
        } = *self;
        // Deref `&AliasableBump` to `&BumpAllocator` for the calls below. What lets the captured
        // `&Bump` survive writer moves is `AliasableBump` itself (a non-uniqueness-asserting handle
        // over a heap-stable `Bump`), not where this coercion is written.
        let allocator: &BumpAllocator = allocator;
        let top_level = Self::get_or_allocate_encoding_buffer(encoding_buffer_ptr, allocator);
        let annotated_value_writer = BinaryValueWriter_1_0::new(allocator, top_level);
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
        match config.kind() {
            WriteConfigKind::Text(_) => {
                unreachable!("Text writer can not be created from binary encoding")
            }
            WriteConfigKind::Binary(_) => LazyRawBinaryWriter_1_0::new(output),
        }
    }

    fn output(&self) -> &W {
        &self.output
    }

    delegate! {
        to self {
            fn flush(&mut self) -> IonResult<()>;
        }
    }

    fn output_mut(&mut self) -> &mut W {
        &mut self.output
    }

    fn write_version_marker(&mut self) -> IonResult<()> {
        self.output.write_all(&IVM_1_0)?;
        Ok(())
    }

    fn macro_table(&self) -> &WriterMacroTable {
        &EMPTY_MACRO_TABLE
    }

    fn macro_table_mut(&mut self) -> Option<&mut WriterMacroTable> {
        None
    }
}

impl<W: Write> ContextWriter for LazyRawBinaryWriter_1_0<W> {
    type NestedValueWriter<'a>
        = BinaryValueWriter_1_0<'a, 'a>
    where
        Self: 'a;
}

impl<W: Write> MakeValueWriter for LazyRawBinaryWriter_1_0<W> {
    fn make_value_writer(&mut self) -> Self::NestedValueWriter<'_> {
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

#[cfg(test)]
mod tests {
    use super::LazyRawBinaryWriter_1_0;
    use crate::lazy::encoder::LazyRawWriter;
    use crate::IonResult;
    use rstest::rstest;

    #[inline(never)]
    fn relocate<T>(value: T) -> T {
        // Pass-by-value forces the value to a new address (a plain move), the scenario the writer
        // must tolerate (`let w2 = w;`). Under Miri -- which is where these tests actually detect
        // the bug -- arguments and return values are copied to fresh allocations, so this is a
        // genuine relocation; in optimized native builds the slot may be reused, but the native run
        // cannot observe the aliasing defect anyway.
        std::hint::black_box(value)
    }

    /// These tests are the regression guard for a use-after-move in the writer's self-referential
    /// arena. The top-level encoding buffer is a `BumpVec` living inside the arena that holds a
    /// `&Bump` back to the writer's `allocator`. With the allocator stored inline (or in a `Box`),
    /// moving the writer invalidated that `&Bump` -- inline relocated it to freed memory, and
    /// `Box`'s uniqueness assertion disabled it under Stacked/Tree Borrows -- so the next growing
    /// write was UB. Holding it via `AliasableBump` (a non-uniqueness-asserting handle) keeps the
    /// reference valid across moves.
    ///
    /// The defect is only observable under Miri, so the guarantee is verified by running these
    /// tests under `cargo +nightly miri test` with both Stacked Borrows and `-Zmiri-tree-borrows`
    /// (they pass on this fix and fail for the inline/`Box` variants). Under plain `cargo test`
    /// they still exercise the code paths and assert output correctness, but cannot fail on the
    /// aliasing violation. `payload_len` is parameterized so at least one case (`SMALL`) stays cheap
    /// under Miri while another (`LARGE`) forces a fresh-chunk allocation.
    const SMALL: usize = 64;
    const LARGE: usize = 64 * 1024;

    /// Encode a value, move the writer, then encode a value that grows the top-level buffer; the
    /// moved writer must produce the same bytes as one that was never moved.
    #[rstest]
    #[case(SMALL)]
    #[case(LARGE)]
    fn move_between_growing_writes_is_consistent(#[case] payload_len: usize) -> IonResult<()> {
        let payload = "a".repeat(payload_len);

        // Writer that is moved mid-stream.
        let mut moved = LazyRawBinaryWriter_1_0::new(Vec::new())?;
        moved.write(1_i64)?; // allocates the top-level encoding buffer
        let mut moved = relocate(moved); // relocate the writer (and, pre-fix, its inline allocator)
        moved.write(payload.as_str())?; // growing write reaches the buffer's internal `&Bump`
        moved.flush()?;

        // Reference writer that stays put and encodes the same sequence.
        let mut stationary = LazyRawBinaryWriter_1_0::new(Vec::new())?;
        stationary.write(1_i64)?;
        stationary.write(payload.as_str())?;
        stationary.flush()?;

        assert_eq!(
            moved.output(),
            stationary.output(),
            "moved writer produced different bytes than the stationary writer (payload_len={payload_len})"
        );
        Ok(())
    }

    /// Same, but the writer is flushed (which resets the arena) *before* the move. Exercises
    /// `AliasableBump::reset` followed by a move and a growing write on the reset arena.
    #[rstest]
    #[case(SMALL)]
    #[case(LARGE)]
    fn move_after_flush_is_consistent(#[case] payload_len: usize) -> IonResult<()> {
        let payload = "a".repeat(payload_len);

        let mut moved = LazyRawBinaryWriter_1_0::new(Vec::new())?;
        moved.write(1_i64)?;
        moved.flush()?; // resets the arena and clears the encoding buffer pointer
        let mut moved = relocate(moved);
        moved.write(payload.as_str())?; // re-allocates the buffer in the (moved) reset arena
        moved.flush()?;

        let mut stationary = LazyRawBinaryWriter_1_0::new(Vec::new())?;
        stationary.write(1_i64)?;
        stationary.flush()?;
        stationary.write(payload.as_str())?;
        stationary.flush()?;

        assert_eq!(
            moved.output(),
            stationary.output(),
            "moved-after-flush writer produced different bytes (payload_len={payload_len})"
        );
        Ok(())
    }
}
