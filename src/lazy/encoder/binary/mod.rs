pub mod v1_0;
// TODO(pt004): this now holds only shared encoding primitives; relocate them and delete the module.
pub mod v1_1;

use bumpalo::Bump as BumpAllocator;
use std::ops::Deref;
use std::rc::Rc;

/// An owning handle to a heap-allocated [`BumpAllocator`] whose address is stable across moves and
/// which -- unlike `Box` -- does not assert unique access to its contents when dereferenced.
///
/// The raw binary Ion 1.0 writer hands out `&Bump` references that are captured (as `&'bump Bump`)
/// inside the `BumpVec` that holds its top-level encoding buffer, which itself lives *inside* the
/// arena. That captured reference must stay valid even when the writer -- and therefore this handle
/// -- is moved. `Box<Bump>` cannot provide that: it asserts unique access to its pointee, so
/// moving/reborrowing it retags the `Bump` as `Unique` and invalidates the captured `&Bump` under
/// Stacked/Tree Borrows (a subsequent growing write is then UB -- confirmed with Miri). `Rc`'s
/// shared `deref` performs no such assertion, so the captured reference survives.
///
/// Only shared access (`&Bump`, via [`Deref`]) is exposed generally; the one operation needing
/// `&mut Bump` -- resetting the arena -- is a dedicated method rather than `DerefMut`, so a
/// uniqueness-asserting reborrow of the `Bump` cannot happen implicitly and invalidate an
/// outstanding `&Bump` alias.
///
/// Implementation note: wrapping `Rc` is deliberately simpler than defining a bespoke
/// non-uniqueness-asserting pointer type -- `Rc`'s shared `deref` already provides exactly the
/// aliasing semantics we need. The inner `Rc` is never cloned (`AliasableBump` is not `Clone`), so
/// this handle always holds the sole strong reference and acts as a unique owner of the arena.
struct AliasableBump(Rc<BumpAllocator>);

impl AliasableBump {
    #[inline]
    pub(crate) fn new(bump: BumpAllocator) -> Self {
        Self(Rc::new(bump))
    }

    /// Resets the arena, freeing all allocations while retaining the current backing chunk (all
    /// other chunks are returned to the global allocator). See [`bumpalo::Bump::reset`].
    ///
    /// # Safety
    ///
    /// This takes `&mut Bump` (a `Unique` reborrow), which invalidates any `&Bump` previously
    /// handed out via [`Deref`] and reclaims the arena those references point into. The caller must
    /// ensure no such alias -- in particular the top-level encoding buffer referenced by the
    /// writer's `encoding_buffer_ptr` -- will be used after this call (e.g. clear that pointer
    /// first). Using a stale alias afterward is undefined behavior (aliasing violation and
    /// use-after-free).
    pub(crate) unsafe fn reset(&mut self) {
        match Rc::get_mut(&mut self.0) {
            Some(bump) => bump.reset(),
            None => unreachable!("get_mut never fails; the Rc is private and never cloned"),
        }
    }
}

impl Deref for AliasableBump {
    type Target = BumpAllocator;

    // A shared reborrow: does NOT assert uniqueness, so `&Bump`s previously handed out remain
    // valid alongside this one.
    #[inline]
    fn deref(&self) -> &BumpAllocator {
        &self.0
    }
}

#[cfg(test)]
mod tests {
    use super::AliasableBump;
    use bumpalo::Bump as BumpAllocator;

    /// The chunk size these tests start their arenas with; small enough that a handful of
    /// allocations forces the arena to add chunks.
    const TEST_CHUNK_SIZE: usize = 1024;

    // Not covered here: the `Rc`-shared fallback arm in `reset`. It is unreachable in practice --
    // `AliasableBump` is not `Clone`, never clones its `Rc`, and does not expose it -- so there is no
    // way for a test to observe a shared arena.

    /// `reset` must reclaim what the arena handed out, not merely rewind bookkeeping.
    #[test]
    fn reset_reclaims_allocated_chunks() {
        let mut allocator = AliasableBump::new(BumpAllocator::with_capacity(TEST_CHUNK_SIZE));
        let initial_bytes = allocator.allocated_bytes();
        // Allocate well past the initial chunk so the arena has to acquire additional ones.
        for _ in 0..64 {
            allocator.alloc([0u8; 256]);
        }
        let grown_bytes = allocator.allocated_bytes();
        assert!(
            grown_bytes > initial_bytes,
            "the arena did not grow: {grown_bytes} bytes vs. an initial {initial_bytes}"
        );

        // SAFETY: no `&Bump` handed out above is still in use; the allocations made from them are
        // dropped and none is referenced after this call.
        unsafe { allocator.reset() };

        let reset_bytes = allocator.allocated_bytes();
        assert!(
            reset_bytes < grown_bytes,
            "reset retained all {grown_bytes} allocated bytes"
        );
        // The arena stays usable (and warm) afterward: `reset` keeps a chunk to allocate from.
        let value = allocator.alloc(42u32);
        assert_eq!(*value, 42);
    }

    /// `Deref` yields a usable `&Bump`, and two such references may be live at once -- the aliasing
    /// property the raw binary writer depends on.
    #[test]
    fn deref_yields_aliasable_bump() {
        let allocator = AliasableBump::new(BumpAllocator::with_capacity(TEST_CHUNK_SIZE));
        let first: &BumpAllocator = &allocator;
        let second: &BumpAllocator = &allocator;
        let from_first = first.alloc_str("first");
        let from_second = second.alloc_str("second");
        // Both references remain valid, as do the allocations made through them.
        assert_eq!(from_first, "first");
        assert_eq!(from_second, "second");
    }
}
