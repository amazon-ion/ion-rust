//! Allocation-counting harness for `Annotations`.
//!
//! This is a **bench target separate from any timing target** on purpose: it installs a counting
//! `#[global_allocator]`, and an atomic increment per allocation would skew any timings it shared a
//! binary with. It measures allocation *counts*, not latency, and asserts the property the
//! tagged-pointer representation must guarantee by construction: the consuming iterator allocates
//! on **no** arm.
//!
//! Run with `cargo bench --bench annotations_allocations`.

use ion_rs::{Annotations, Symbol};
use std::alloc::{GlobalAlloc, Layout, System};
use std::hint::black_box;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Counts every allocation and reallocation. Deallocations are not counted — the claims here are
/// about how many times a path reaches the allocator, not about net live bytes.
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

/// Builds `n` owned symbols. Done outside every measurement window so the symbols' own
/// allocations never enter a count.
fn symbols(n: usize) -> Vec<Symbol> {
    (0..n)
        .map(|i| Symbol::owned(format!("annotation{i}")))
        .collect()
}

fn main() {
    // The consuming iterator must allocate on no arm; that is why `into_boxed_slice` reuses each
    // arm's existing allocation rather than rebuilding a `Vec`. Build the value outside the window,
    // then count only the `into_iter` + full drain.
    for n in [0usize, 1, 2, 3] {
        let annotations = Annotations::from(symbols(n));
        let (allocs, drained) = allocations_during(|| {
            let count = black_box(annotations).into_iter().map(black_box).count();
            black_box(count)
        });
        println!("into_iter drain, {n} annotation(s): {allocs} allocation(s)");
        assert_eq!(
            allocs, 0,
            "into_iter must not allocate on the {n}-annotation arm"
        );
        assert_eq!(drained, n, "into_iter must yield every annotation");
    }

    // Allocations for the storage `Element` embeds. This is the heap work `Annotations`
    // construction performs for its field, measured over an already-built `Vec` so only the
    // representation's own allocations enter the count. The 0 case is not an allocation win (an
    // empty `Vec` did not allocate either); it is a footprint win — 24 bytes down to 8 in every
    // `Element`. Because construction routes an exact-sized `Vec`'s buffer through
    // `into_boxed_slice`, the 1- and 2-annotation arms reuse that buffer as their compact box and
    // allocate nothing; only the 3+ arm allocates, for its outer thinning cell. Reported, not
    // asserted, so a future arm change is visible here.
    for n in [0usize, 1, 2, 3] {
        let prebuilt = symbols(n);
        let (allocs, annotations) = allocations_during(|| Annotations::from(black_box(prebuilt)));
        println!("Annotations construction, {n} annotation(s): {allocs} allocation(s)");
        black_box(annotations);
    }
}
