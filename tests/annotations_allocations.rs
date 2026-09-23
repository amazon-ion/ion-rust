//! Allocation-counting integration test for `Annotations`.
//!
//! This is a **standalone integration test** (its own binary) on purpose: it installs a counting
//! `#[global_allocator]` to assert the property the tagged-pointer representation must guarantee by
//! construction — the consuming iterator allocates on **no** arm. It measures allocation *counts*,
//! not latency.
//!
//! It deliberately contains a **single** `#[test]`. The allocation counter is process-global mutable
//! state; a second test in this binary would run on another thread by default and its allocations
//! would race into the measurement window. Keeping one test keeps the window quiet.

use ion_rs::{Annotations, Symbol};
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Counts every allocation and reallocation. Deallocations are not counted — the claim here is about
/// how many times a path reaches the allocator, not about net live bytes.
struct CountingAllocator;

static ALLOCATIONS: AtomicUsize = AtomicUsize::new(0);

// SAFETY: `GlobalAlloc` requires that the allocator behave correctly and hand back blocks fitting
// the requested `Layout`. Every method forwards verbatim to `System`, the standard allocator, which
// upholds that contract; each caller-supplied pointer/layout is passed through unchanged, so the
// same layout invariants that made the call sound for `System` still hold. The only added work is an
// atomic counter increment, which allocates nothing and touches no memory the allocator manages, so
// it cannot violate any of the trait's requirements.
unsafe impl GlobalAlloc for CountingAllocator {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        // SAFETY: `layout` is forwarded unchanged to the system allocator.
        unsafe { System.alloc(layout) }
    }

    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        // SAFETY: `ptr`/`layout` came from this same allocator (a prior `alloc`/`realloc` that
        // forwarded to `System`), so they satisfy `System::dealloc`'s preconditions.
        unsafe { System.dealloc(ptr, layout) }
    }

    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        ALLOCATIONS.fetch_add(1, Ordering::Relaxed);
        // SAFETY: `ptr`/`layout`/`new_size` are forwarded unchanged; `ptr` and `layout` describe a
        // live block from this allocator, meeting `System::realloc`'s preconditions.
        unsafe { System.realloc(ptr, layout, new_size) }
    }
}

#[global_allocator]
static ALLOCATOR: CountingAllocator = CountingAllocator;

/// Runs `f` and returns how many allocations it made.
fn allocations_during<R>(f: impl FnOnce() -> R) -> (usize, R) {
    let before = ALLOCATIONS.load(Ordering::Relaxed);
    let result = f();
    let after = ALLOCATIONS.load(Ordering::Relaxed);
    (after - before, result)
}

/// Builds `n` owned symbols. Done outside every measurement window so the symbols' own allocations
/// never enter a count.
fn symbols(n: usize) -> Vec<Symbol> {
    (0..n)
        .map(|i| Symbol::owned(format!("annotation{i}")))
        .collect()
}

/// The consuming iterator must allocate on no arm; that is why `into_boxed_slice` reuses each arm's
/// existing allocation rather than rebuilding a `Vec`. Build the value outside the window, then count
/// only the `into_iter` + full drain. Covers every tag arm: 0 (empty), 1, 2, and 3+ (boxed slice).
#[test]
fn into_iter_does_not_allocate_on_any_arm() {
    for n in [0usize, 1, 2, 3] {
        let annotations = Annotations::from(symbols(n));
        let (allocs, drained) = allocations_during(|| {
            let count = black_box(annotations).into_iter().map(black_box).count();
            black_box(count)
        });
        assert_eq!(
            allocs, 0,
            "into_iter must not allocate on the {n}-annotation arm"
        );
        assert_eq!(drained, n, "into_iter must yield every annotation");
    }
}
