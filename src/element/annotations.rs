use crate::element::iterators::{AnnotationsIntoIter, SymbolsIterator};
use crate::ion_data::{IonDataHash, IonDataOrd};
use crate::Symbol;
use repr::AnnotationsRepr;
use std::cmp::Ordering;
use std::hash::Hasher;

/// An ordered sequence of symbols that convey additional, application-specific information about
/// their associated Ion value.
///
/// The [`IntoAnnotations`] trait is a convenient way to convert collections of symbol convertible
/// things (including [`&str`] and [`String`]) into this sequence.
///
/// ```
/// use ion_rs::{Annotations, IntoAnnotations};
/// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
/// for annotation in &annotations {
///     assert_eq!(annotation.text().map(|s| s.len()), Some(3));
/// }
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotations {
    symbols: AnnotationsRepr,
}

impl Annotations {
    /// Constructs an Annotations object representing an empty symbol sequence
    pub fn empty() -> Self {
        Annotations {
            symbols: AnnotationsRepr::empty(),
        }
    }

    /// Returns an [`Iterator`] that yields each of the [`Symbol`]s in this annotations
    /// sequence in order.
    pub fn iter(&self) -> SymbolsIterator<'_> {
        SymbolsIterator::new(self.symbols.as_slice())
    }

    /// Returns the number of annotations in this sequence.
    /// ```
    /// use ion_rs::{Annotations, IntoAnnotations};
    /// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
    /// assert_eq!(annotations.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.symbols.len()
    }

    /// Returns `true` if this sequence contains zero annotations. Otherwise, returns `false`.
    /// ```
    /// use ion_rs::{Annotations, IntoAnnotations};
    /// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
    /// assert!(!annotations.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.symbols.is_empty()
    }

    /// Returns `true` if any symbol in this annotations sequence is equal to the provided text.
    /// Otherwise, returns `false`.
    /// ```
    /// use ion_rs::{Annotations, IntoAnnotations};
    /// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
    /// assert!(annotations.contains("foo"));
    /// assert!(annotations.contains("bar"));
    /// assert!(annotations.contains("baz"));
    ///
    /// assert!(!annotations.contains("quux"));
    /// assert!(!annotations.contains("quuz"));
    /// ```
    pub fn contains<S: AsRef<str>>(&self, query: S) -> bool {
        let query: &str = query.as_ref();
        self.iter().any(|symbol| symbol.text() == Some(query))
    }

    /// Returns the text of the first annotation in this sequence.
    ///
    /// If the sequence is empty, returns `None`.
    /// If the first annotation in the sequence is `$0` (symbol ID 0), returns `None`.
    /// Otherwise, returns a `Some(&str)` containing the text.
    ///
    /// To view the first annotation as a [Symbol] rather than a `&str`, use
    /// `annotations.iter().next()`.
    /// ```
    /// use ion_rs::{Annotations, IntoAnnotations};
    /// use ion_rs::Symbol;
    /// let annotations: Annotations = ["foo", "bar", "baz"].into_annotations();
    /// assert_eq!(annotations.first(), Some("foo"));
    ///
    /// let empty_sequence: Vec<&str> = vec![];
    /// let annotations: Annotations = empty_sequence.into_annotations();
    /// assert_eq!(annotations.first(), None);
    ///
    /// let annotations: Annotations = [Symbol::unknown_text()].into_annotations();
    /// assert_eq!(annotations.first(), None)
    /// ```
    pub fn first(&self) -> Option<&str> {
        self.symbols.as_slice().first().and_then(|a| a.text())
    }
}

impl AsRef<[Symbol]> for Annotations {
    fn as_ref(&self) -> &[Symbol] {
        self.symbols.as_slice()
    }
}

impl From<Vec<Symbol>> for Annotations {
    fn from(value: Vec<Symbol>) -> Self {
        Self {
            symbols: AnnotationsRepr::from_boxed_slice(value.into_boxed_slice()),
        }
    }
}

impl<S: Into<Symbol>> FromIterator<S> for Annotations {
    fn from_iter<T: IntoIterator<Item = S>>(iter: T) -> Self {
        iter.into_annotations()
    }
}

impl<'a> IntoIterator for &'a Annotations {
    type Item = &'a Symbol;
    type IntoIter = SymbolsIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        SymbolsIterator::new(self.symbols.as_slice())
    }
}

impl IntoIterator for Annotations {
    type Item = Symbol;
    type IntoIter = AnnotationsIntoIter;

    fn into_iter(self) -> Self::IntoIter {
        // `into_boxed_slice` collapses every arm to one `Box<[Symbol]>` without allocating, and
        // `into_vec` then reuses that buffer, so the whole owned path stays allocation-free. The
        // `into_vec` is load-bearing under edition 2021: a bare `Box<[T]>::into_iter()` resolves to
        // the borrowing `slice::Iter` shim, not the by-value `vec::IntoIter` this needs.
        AnnotationsIntoIter::new(self.symbols.into_boxed_slice().into_vec().into_iter())
    }
}

impl IonDataOrd for Annotations {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.symbols.ion_cmp(&other.symbols)
    }
}

impl IonDataHash for Annotations {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.symbols.as_slice().ion_data_hash(state)
    }
}

/// Defines conversion into [`Annotations`].
///
/// This trait allows us to have a blanket implementations that can cover many type combinations
/// without conflicting in ways that blanket [`From`] implementations can.
///
/// With this we can convert for some `T` that is string-like (`&str`, `String`, `Symbol`, etc...)
/// we can convert from collections of that type like `[T]`, `[T; n]`, `Vec<T>`, and
/// iterators of `T` generically.
pub trait IntoAnnotations {
    fn into_annotations(self) -> Annotations;
}

impl<S, I> IntoAnnotations for I
where
    S: Into<Symbol>,
    I: IntoIterator<Item = S>,
{
    fn into_annotations(self) -> Annotations {
        let symbols: Box<[Symbol]> = self.into_iter().map(|a| a.into()).collect();
        Annotations {
            symbols: AnnotationsRepr::from_boxed_slice(symbols),
        }
    }
}

/// Houses [`AnnotationsRepr`] so its `ptr`/`_owns` fields are private to this module. The type's
/// `unsafe` soundness rests on the tagged pointer only ever being built by `from_tag_and_ptr`; this
/// boundary makes that unforgeable from the parent module, which can reach the storage only through
/// the `pub` methods below (whose reach is capped at the crate by this module being private).
mod repr {
    use crate::ion_data::IonDataOrd;
    use crate::Symbol;
    use ice_code::ice as cold_path;
    use std::cmp::Ordering;
    use std::fmt::{Debug, Formatter};
    use std::marker::PhantomData;

    /// An annotations representation that is only one word wide.
    ///
    /// A `Box<[Symbol]>` must carry the length of the slice, making it two words wide, so we use a
    /// tagged pointer to encode small lengths. The overwhelmingly common empty case is a
    /// null pointer that touches no heap, and the one- and two-annotation cases carry a single
    /// indirection. The tag in the low bits distinguishes the four storage shapes; see the `TAG_*`
    /// constants. The type is immutable once constructed, which is what confines every `unsafe`
    /// invariant to construction.
    ///
    /// SAFETY BOUNDARY: `ptr` is a plain private field, so any code in this module can build an
    /// `AnnotationsRepr` by struct literal — but a non-empty value MUST come from `from_tag_and_ptr`,
    /// whose `# Safety` contract every read/drop path relies on. Constructing a non-empty repr any other
    /// way (a bogus tagged `ptr`) makes the otherwise-safe `as_slice`/`into_boxed_slice`/`Drop` unsound.
    /// The only in-module exception is a value carrying `TAG_EMPTY` with a non-null `ptr`, which the
    /// empty-tag arms handle without dereferencing; a test relies on that.
    pub struct AnnotationsRepr {
        /// Tagged pointer to the annotation storage, or null when empty. A pointer, not an integer, so
        /// that the representation is sound under strict provenance.
        ptr: *mut (),
        /// Makes Unpin/UnwindSafe/RefUnwindSafe for Annotations conditional on Symbol having those traits.
        _owns: PhantomData<Symbol>,
    }

    impl AnnotationsRepr {
        /// Mask selecting the tag bits.
        const TAG_MASK: usize = 0b11;
        /// No annotations. The pointer is null.
        const TAG_EMPTY: usize = 0b00;
        /// One annotation, stored in a `Box<Symbol>`.
        const TAG_ONE: usize = 0b01;
        /// Two annotations, stored in a `Box<[Symbol; 2]>`.
        const TAG_TWO: usize = 0b10;
        /// Three or more annotations, stored in a `Box<Box<[Symbol]>>`. The outer box thins the fat
        /// slice pointer so it fits in a tagged word; the inner boxed slice owns the symbols.
        const TAG_MANY: usize = 0b11;

        /// The empty representation: a null tagged pointer that owns no allocation.
        pub fn empty() -> Self {
            Self {
                ptr: std::ptr::null_mut(),
                _owns: PhantomData,
            }
        }

        /// Packs a raw pointer to owned storage into the tagged pointer under `tag`. The tag is applied
        /// by byte offset rather than by masking an integer address, so the stored pointer keeps the
        /// provenance of the allocation and never originates from an integer.
        ///
        /// # Safety
        ///
        /// The caller must guarantee that:
        ///
        /// * `ptr` is non-null, aligned to at least `align_of::<T>()`, and points to a live allocation
        ///   whose ownership is transferred here; the tag-dispatch sites (`as_slice`,
        ///   `into_boxed_slice`) later reconstruct and eventually free exactly this allocation. An
        ///   under-aligned `ptr` would carry set low bits that `as_tag_and_ptr` would misread as the
        ///   tag and subtract from the base.
        /// * `tag <= Self::TAG_MASK`, so it fits in the two low bits without disturbing the base
        ///   address.
        /// * `tag` is the tag whose documented pointee type is exactly `T`, so that those sites
        ///   reconstruct the allocation as the type it actually holds.
        /// * `tag != Self::TAG_EMPTY`, because the empty tag promises a null pointer and the value
        ///   built here is non-null.
        ///
        /// The `const` assert in the body constrains the *type* `T` — it guarantees `T` is aligned
        /// enough to leave the tag bits free — but it cannot check the pointer *value*, which is why
        /// `ptr`'s own alignment remains a caller obligation.
        unsafe fn from_tag_and_ptr<T>(tag: usize, ptr: *mut T) -> Self {
            // A future arm whose pointee is not at least 4-aligned would leave no room for the two tag
            // bits; fail to compile rather than store a pointer the tag corrupts.
            const { assert!(align_of::<T>() > Self::TAG_MASK) };
            debug_assert!(tag != Self::TAG_EMPTY && tag <= Self::TAG_MASK);
            debug_assert_eq!(
                ptr as usize & Self::TAG_MASK,
                0,
                "ptr must be aligned so the tag bits are free"
            );
            let base = ptr as *mut ();
            Self {
                ptr: base.wrapping_byte_add(tag),
                _owns: PhantomData,
            }
        }

        /// Decodes `(tag, untagged base pointer)` from the tagged pointer. The offset arithmetic that
        /// clears the tag lives here so the two tag-dispatch sites (`as_slice` for borrows,
        /// `into_boxed_slice` for ownership) share one definition; `Drop` and owned `IntoIterator` reach
        /// the tag only by delegating to `into_boxed_slice`, and `Clone` reaches it through `as_slice`.
        /// The returned base keeps the allocation's provenance: it is `self.ptr` moved by
        /// `wrapping_byte_sub`, not a pointer rebuilt from an integer. The `as usize` reads only the low
        /// bits for the tag — the strict-provenance `<*mut _>::addr` would say this directly, but it is
        /// not stable under the crate's 1.82 MSRV (stabilized in 1.84). The empty-tag/null agreement is
        /// debug-asserted by `as_slice` — the shared read path — rather than here, so a destructor never
        /// asserts.
        fn as_tag_and_ptr(&self) -> (usize, *mut ()) {
            let tag = (self.ptr as usize) & Self::TAG_MASK;
            (tag, self.ptr.wrapping_byte_sub(tag))
        }

        /// The shared-borrow slice view: every borrowing accessor reads the symbols through here, so a
        /// change to how a borrowed value is read lives in one place and each arm names the pointee type
        /// its tag promises. (`is_empty` deliberately does not — it answers from `self.ptr.is_null()`
        /// alone.)
        pub fn as_slice(&self) -> &[Symbol] {
            let (tag, base) = self.as_tag_and_ptr();
            debug_assert_eq!(
                tag == Self::TAG_EMPTY,
                self.ptr.is_null(),
                "the empty tag and a null pointer must agree"
            );
            // SAFETY: the representation is immutable, so a non-empty `ptr` was produced by
            // `from_tag_and_ptr` from a live allocation of the type this tag names and stays valid for `&self`.
            // `base` restores the original allocation pointer, so each cast reads the pointee that was
            // boxed.
            unsafe {
                match tag {
                    Self::TAG_EMPTY => &[],
                    Self::TAG_ONE => std::slice::from_ref(&*base.cast::<Symbol>()),
                    Self::TAG_TWO => &*base.cast::<[Symbol; 2]>(),
                    // Borrow through the real `Box<[Symbol]>` pointee — the same type `Drop` and owned
                    // `IntoIterator` reconstruct — so no arm depends on an unsized-`Box` layout the
                    // language does not promise.
                    Self::TAG_MANY => {
                        let boxed = &*base.cast::<Box<[Symbol]>>();
                        let slice: &[Symbol] = boxed;
                        slice
                    }
                    // Spelling every tag out means renumbering the constants can never make one arm
                    // silently absorb another tag's pointee type.
                    _ => unreachable!("tag is masked to two bits"),
                }
            }
        }

        /// The owned counterpart to [`as_slice`](Self::as_slice): consumes `self` and moves the symbols
        /// into a single `Box<[Symbol]>`, reusing the existing allocation on every non-empty arm rather
        /// than allocating a fresh buffer (the empty arm owns nothing and yields an empty boxed slice).
        /// Collapsing all four arms to one slice type here is what lets the
        /// consuming iterator funnel through a single `vec::IntoIter` without the extra allocation a
        /// `Vec` rebuild would cost on the one- and two-annotation arms.
        pub fn into_boxed_slice(self) -> Box<[Symbol]> {
            let (tag, base) = self.as_tag_and_ptr();
            // Suppress `Drop` — it would free the allocation the arms below move out. `base` was already
            // read above, so forgetting `self` here loses nothing.
            std::mem::forget(self);
            // SAFETY: `base` reconstructs the box each tag named at construction (the representation is
            // immutable, so a non-empty `ptr` still names a live box of that type). Each arm rebuilds
            // that exact box and transfers ownership into the returned `Box<[Symbol]>`, so every
            // allocation is freed exactly once, by the returned box's drop glue.
            unsafe {
                match tag {
                    Self::TAG_EMPTY => Box::default(),
                    // `[Symbol; 1]` has the same layout as `Symbol`, so the `Box<Symbol>` allocation is
                    // a valid `Box<[Symbol; 1]>`; the array box unsizes to a boxed slice for free. This
                    // keeps the one-annotation arm allocation-free where a `vec![*only]` rebuild would
                    // not.
                    Self::TAG_ONE => {
                        let boxed: Box<[Symbol]> = Box::from_raw(base.cast::<[Symbol; 1]>());
                        boxed
                    }
                    Self::TAG_TWO => {
                        let boxed: Box<[Symbol]> = Box::from_raw(base.cast::<[Symbol; 2]>());
                        boxed
                    }
                    // Free the outer thinning cell; its `Box<[Symbol]>` pointee is already the slice.
                    Self::TAG_MANY => *Box::from_raw(base.cast::<Box<[Symbol]>>()),
                    // Spelling every tag out means renumbering the constants can never make one arm
                    // free another tag's pointee under the wrong layout.
                    _ => unreachable!("tag is masked to two bits"),
                }
            }
        }

        /// The inverse of [`into_boxed_slice`](Self::into_boxed_slice), and the single owning
        /// constructor the `From`/[`IntoAnnotations`](super::IntoAnnotations) conversions and `Clone`
        /// all route through.
        /// Dispatches on length and reuses the incoming allocation for the compact one- and
        /// two-annotation shapes, so only the 3+ arm allocates (its outer thinning cell). Keeping the
        /// tag-shape choice here means `Clone` need not re-derive it.
        pub fn from_boxed_slice(boxed: Box<[Symbol]>) -> Self {
            match boxed.len() {
                0 => Self::empty(),
                // SAFETY: a length-`N` boxed slice's allocation has the exact layout of `[Symbol; N]`,
                // so casting its data pointer to the compact pointee type addresses that same
                // allocation; the types the tag-dispatch sites later name (`Symbol`/`[Symbol; 1]` for
                // one, `[Symbol; 2]` for two) share that layout, so it is freed once under the layout it
                // was allocated with. `Box::into_raw` transfers ownership, so nothing double-frees. Each
                // `from_tag_and_ptr` receives the tag whose documented pointee is exactly that type, and
                // neither tag is `TAG_EMPTY`.
                1 => unsafe {
                    Self::from_tag_and_ptr(Self::TAG_ONE, Box::into_raw(boxed).cast::<Symbol>())
                },
                2 => unsafe {
                    Self::from_tag_and_ptr(
                        Self::TAG_TWO,
                        Box::into_raw(boxed).cast::<[Symbol; 2]>(),
                    )
                },
                // Marked cold: this is the only arm that reaches the allocator, for the outer thinning
                // cell, and the compact arms are the common shapes.
                3.. => cold_path! {{
                    // SAFETY: `TAG_MANY`'s documented pointee is `Box<[Symbol]>`, exactly what is boxed
                    // here, and it is not `TAG_EMPTY`.
                    unsafe { Self::from_tag_and_ptr(Self::TAG_MANY, Box::into_raw(Box::new(boxed))) }
                }},
            }
        }

        /// Returns `true` if this sequence contains zero annotations. Otherwise, returns `false`.
        pub fn is_empty(&self) -> bool {
            // The representation's invariant: a null pointer is the empty sequence and every non-empty
            // arm is non-null. Reading the pointer answers this without the tag decode and dependent
            // load that going through `as_slice` would cost.
            debug_assert_eq!(self.ptr.is_null(), self.as_slice().is_empty());
            self.ptr.is_null()
        }

        /// Returns the number of annotations in this annotation sequence.
        pub fn len(&self) -> usize {
            let (tag, _) = self.as_tag_and_ptr();
            if tag < Self::TAG_MANY {
                tag
            } else {
                self.as_slice().len()
            }
        }
    }

    impl Clone for AnnotationsRepr {
        fn clone(&self) -> Self {
            // The empty case owns no allocation; reproduce the null word directly rather than paying a
            // tag decode, slice clone, and length dispatch to rebuild it. `Drop` and `is_empty` take the
            // same null short-circuit.
            if self.ptr.is_null() {
                return Self::empty();
            }
            // Clone the symbols into a fresh boxed slice, then let the owning constructor pick the
            // compact arm — reusing that slice's allocation for the 1- and 2-annotation shapes. This
            // matches a hand-dispatched clone's per-arm allocation counts with no tag match or `unsafe`
            // in this impl.
            Self::from_boxed_slice(self.as_slice().into())
        }
    }

    impl Drop for AnnotationsRepr {
        fn drop(&mut self) {
            // The empty case is the hot one and owns no allocation, so short-circuit before any of the
            // owning machinery. This mirrors the null/empty-tag agreement `as_slice` asserts.
            if self.ptr.is_null() {
                return;
            }
            // Delegate the owning tag dispatch to `into_boxed_slice`, the single owning primitive, so
            // freeing lives in one place rather than duplicating the per-arm match here.

            // SAFETY: `self` is not observed again after this read. `into_boxed_slice` takes
            // ownership of the bitwise-copied tagged pointer and suppresses that copy's own `Drop`
            // via `mem::forget`, so the allocation is reconstructed and freed exactly once by the
            // returned box's drop glue — no double free and no recursion back into this `drop`.
            let owned = unsafe { std::ptr::read(self) };
            drop(owned.into_boxed_slice());
        }
    }

    // SAFETY: the pointee is owned `Symbol` storage, so `Annotations` is `Send`/`Sync` exactly when
    // `Symbol` is. The bound on the concrete `Symbol` type keeps this honest: were `Symbol` to gain a
    // non-thread-safe field, the bound would fail to hold and this would stop compiling, rather than
    // silently asserting a property the data no longer has. A raw pointer carries neither auto trait,
    // and `PhantomData` cannot restore one, so these manual impls are what a public type in every
    // `Element` needs to keep the traits it had as a `Vec`.
    //
    // `UnwindSafe`/`RefUnwindSafe` are deliberately left to inference. The raw pointer is
    // unconditionally both, and the `PhantomData<Symbol>` field carries `Symbol`'s own unwind safety, so
    // the inferred impls already track the owned data without a manual assertion here.
    unsafe impl Send for AnnotationsRepr where Symbol: Send {}
    unsafe impl Sync for AnnotationsRepr where Symbol: Sync {}

    impl Debug for AnnotationsRepr {
        fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
            self.as_slice().fmt(f)
        }
    }

    impl PartialEq for AnnotationsRepr {
        fn eq(&self, other: &Self) -> bool {
            // Identical tagged pointers are equal without decoding either. Two owned reprs never share a
            // non-null `ptr` (each owns its allocation), so this fires exactly for the empty case
            // (`null == null`) and for a value compared with itself; an equal `ptr` also carries an
            // equal tag, so it can never be a false positive.
            self.ptr == other.ptr || self.as_slice() == other.as_slice()
        }
    }

    impl Eq for AnnotationsRepr {}

    impl IonDataOrd for AnnotationsRepr {
        fn ion_cmp(&self, other: &Self) -> Ordering {
            // Identical tagged pointers are equal without decoding, as in `PartialEq`: empty vs empty,
            // or a value against itself.
            if self.ptr == other.ptr {
                return Ordering::Equal;
            }
            self.as_slice().ion_cmp(other.as_slice())
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use std::marker::PhantomData;

        #[test]
        #[cfg(debug_assertions)]
        fn non_null_empty_tag_is_rejected() {
            use std::panic::{catch_unwind, AssertUnwindSafe};
            // A non-null pointer carrying the empty tag disagrees with the allocation it describes.
            // `NonNull::dangling()` is aligned (low bits zero → empty tag) and non-null, built without
            // reconstructing a pointer from an integer, so it stays strict-provenance clean. `as_slice`
            // returns an empty slice for the empty tag without dereferencing, and dropping this value
            // reaches `into_boxed_slice`'s `TAG_EMPTY` arm (its non-null pointer does not take `Drop`'s
            // null short-circuit), which allocates a fresh empty box instead of freeing anything. So the
            // bogus value is safe to build, observe panicking, and drop.
            let bogus = AnnotationsRepr {
                ptr: std::ptr::NonNull::<u64>::dangling().as_ptr() as *mut (),
                _owns: PhantomData,
            };
            let result = catch_unwind(AssertUnwindSafe(|| bogus.as_slice().len()));
            assert!(result.is_err(), "as_slice must reject a non-null empty tag");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Element;
    use rstest::rstest;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::Hasher;
    use std::sync::Arc;

    /// Builds an `Annotations` from owned text, exercising the tag arm implied by the count.
    fn anns(texts: &[&str]) -> Annotations {
        texts.iter().map(|t| Symbol::owned(*t)).collect()
    }

    /// Builds an `Annotations` whose `n` symbols all hold a handle to `text`, so
    /// `Arc::strong_count(&text)` counts exactly the symbols that are still alive: `n + 1` while
    /// this value lives (the caller keeps one handle), back to `1` once it has been freed. This
    /// makes freeing observable to plain `cargo test` — a missed drop leaves the count high and a
    /// double drop panics on the underlying count — without depending on a leak checker.
    fn shared_anns(text: &Arc<str>, n: usize) -> Annotations {
        (0..n).map(|_| Symbol::shared(Arc::clone(text))).collect()
    }

    fn ion_hash(annotations: &Annotations) -> u64 {
        let mut hasher = DefaultHasher::new();
        annotations.ion_data_hash(&mut hasher);
        hasher.finish()
    }

    #[test]
    fn test_into_iter() {
        let expected = vec!["a", "b", "c"].into_annotations();
        let collect: Annotations = expected.clone().into_iter().collect();
        assert_eq!(expected, collect);
    }

    #[test]
    fn test_from_vec() {
        let expected = vec!["d", "e", "f"].into_annotations();
        let symbols: Vec<_> = expected.clone().into_iter().collect();
        let from: Annotations = symbols.into();
        assert_eq!(expected, from);
    }

    #[test]
    fn size_and_alignment() {
        // `Annotations` must occupy exactly one word in every `Element`, which is the point of the
        // tagged-pointer representation. Stated relative to `usize` so the claim holds on 32-bit
        // targets too, where an unconditional `== 8` would not compile.
        assert_eq!(size_of::<Annotations>(), size_of::<usize>());
        assert_eq!(align_of::<Annotations>(), align_of::<usize>());
    }

    #[test]
    fn send_sync() {
        // Confirms the conditional `unsafe impl`s apply — the raw-pointer field does not silently
        // strip the auto traits from a public type or from the `Element` that embeds it.
        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Annotations>();
        assert_send_sync::<Element>();
    }

    /// Full behaviour across every tag arm: 0 (empty), 1, 2 (the distinct two-element allocation),
    /// 3 (where the boxed slice begins), and 4.
    #[rstest]
    #[case(&[])]
    #[case(&["a"])]
    #[case(&["a", "b"])]
    #[case(&["a", "b", "c"])]
    #[case(&["a", "b", "c", "d"])]
    fn behaviour_per_arm(#[case] texts: &[&str]) {
        let annotations = anns(texts);

        assert_eq!(annotations.len(), texts.len());
        assert_eq!(annotations.is_empty(), texts.is_empty());

        let collected: Vec<&str> = annotations.iter().filter_map(|s| s.text()).collect();
        assert_eq!(collected, texts);

        assert_eq!(annotations.as_ref().len(), texts.len());

        for t in texts {
            assert!(annotations.contains(t), "should contain {t}");
        }
        assert!(!annotations.contains("absent"));

        assert_eq!(annotations.first(), texts.first().copied());

        // Clone is equal. (Independence — that dropping one does not disturb the other — is
        // checked by `drop_frees_once_for_clone_and_container`.)
        let cloned = annotations.clone();
        assert_eq!(cloned, annotations);

        // Consuming round-trip recollects an equal value. That the consuming iterator reaches the
        // allocator on no arm is asserted by the `tests/annotations_allocations.rs` integration test.
        let recollected: Annotations = annotations.clone().into_iter().collect();
        assert_eq!(recollected, annotations);
    }

    #[test]
    fn unknown_text_first_and_len() {
        // `first()` maps the leading symbol through `text()`, so a leading `$0` (unknown text) reads
        // as `None` even though the sequence is non-empty — it reports the text, not the symbol's
        // presence.
        let one = Annotations::from(vec![Symbol::unknown_text()]);
        assert_eq!(one.first(), None);
        assert_eq!(one.len(), 1);
        assert!(!one.is_empty());

        let two = Annotations::from(vec![Symbol::unknown_text(), Symbol::owned("b")]);
        assert_eq!(two.first(), None);
        assert_eq!(two.len(), 2);
    }

    #[rstest]
    #[case(0)]
    #[case(1)]
    #[case(2)]
    #[case(3)]
    fn construction_from_oversized_vec_frees_once(#[case] n: usize) {
        // Construction routes the `Vec`'s buffer through `into_boxed_slice`. When the `Vec` has
        // spare capacity, `into_boxed_slice` shrinks to fit, so `from_boxed_slice` still receives an
        // exactly-sized allocation and the compact-arm reinterpret frees it under the matching
        // layout. The shared-handle count returning to 1 shows the symbols were freed exactly once
        // on each arm; when Miri runs this test it additionally reports a leaked buffer or a
        // layout-mismatched free, which counting alone cannot see.
        let text: Arc<str> = Arc::from("shared");
        let mut symbols = Vec::with_capacity(n + 8);
        symbols.extend((0..n).map(|_| Symbol::shared(Arc::clone(&text))));
        assert!(symbols.capacity() > symbols.len());

        let annotations = Annotations::from(symbols);
        assert_eq!(annotations.len(), n);
        assert_eq!(Arc::strong_count(&text), n + 1);
        drop(annotations);
        assert_eq!(
            Arc::strong_count(&text),
            1,
            "the {n}-annotation arm must free its symbols exactly once"
        );
    }

    /// Equality and ordering together, within an arm and across arm boundaries. A shorter prefix
    /// orders before its extension, so crossing into a higher arm is `Less`; `PartialEq` agrees
    /// exactly when the order is `Equal`.
    #[rstest]
    #[case(&[], &[], Ordering::Equal)] // empty vs empty
    #[case(&[], &["a"], Ordering::Less)] // empty vs 1
    #[case(&["a", "b"], &["a", "b"], Ordering::Equal)] // within-arm equal
    #[case(&["a"], &["a", "b"], Ordering::Less)] // 1 vs 2
    #[case(&["a", "b"], &["a", "b", "c"], Ordering::Less)] // 2 vs 3 (direct pointee vs boxed)
    #[case(&["a", "b", "c"], &["a", "b", "c", "d"], Ordering::Less)] // 3 vs 4
    #[case(&["a"], &["b"], Ordering::Less)] // same arm, different content
    #[case(&["b"], &["a"], Ordering::Greater)]
    fn compares_within_and_across_arms(
        #[case] lhs: &[&str],
        #[case] rhs: &[&str],
        #[case] expected: Ordering,
    ) {
        let (lhs, rhs) = (anns(lhs), anns(rhs));
        assert_eq!(lhs.ion_cmp(&rhs), expected);
        assert_eq!(lhs == rhs, expected == Ordering::Equal);
    }

    #[test]
    fn hashing_matches_within_arm_and_clone() {
        // Equal values hash equal, within an arm and through a clone. Delegating to the slice view
        // means the hash is exactly the slice's, as it was over the old `Vec`.
        assert_eq!(ion_hash(&anns(&["a", "b"])), ion_hash(&anns(&["a", "b"])));
        let three = anns(&["a", "b", "c"]);
        assert_eq!(ion_hash(&three), ion_hash(&three.clone()));
    }

    #[test]
    fn drop_frees_once_through_reassignment_and_replace() {
        // Reassignment drops the previous value; `mem::replace`/`swap` move ownership around. Every
        // symbol here holds a handle to one `Arc<str>`, so plain `cargo test` sees the count return
        // to the caller's single handle after each arm is dropped: a value whose destructor never
        // ran would leave it high. When Miri runs this test it additionally reports the undefined
        // behavior a double free or use-after-free would cause.
        let text: Arc<str> = Arc::from("shared");

        let mut a = shared_anns(&text, 3);
        assert_eq!(a.len(), 3);
        a = shared_anns(&text, 1); // drops the 3-arm value
        assert_eq!(a.len(), 1);
        drop(a);
        assert_eq!(Arc::strong_count(&text), 1, "reassignment must free both");

        let mut two = shared_anns(&text, 2);
        let old = std::mem::replace(&mut two, shared_anns(&text, 4));
        assert_eq!(old, shared_anns(&text, 2));
        assert_eq!(two.len(), 4);
        drop((old, two));
        assert_eq!(Arc::strong_count(&text), 1, "replace must free both");

        let mut lhs = shared_anns(&text, 1);
        let mut rhs = shared_anns(&text, 3);
        std::mem::swap(&mut lhs, &mut rhs);
        assert_eq!(lhs.len(), 3);
        assert_eq!(rhs.len(), 1);
        drop((lhs, rhs));
        assert_eq!(Arc::strong_count(&text), 1, "swap must free both");
    }

    #[test]
    fn drop_frees_once_for_clone_and_container() {
        // Clone then drop both — each owns its own allocation, so both must free without touching
        // the other's. A `Vec` of every arm exercises container drop and the 3+ arm's two nested
        // allocations. Sharing one `Arc<str>` across all the symbols makes both properties visible
        // to plain `cargo test`: the count drops by exactly the dropped value's length and returns
        // to the caller's single handle. Miri, when run, additionally catches the nested 3+ arm
        // leaking its outer cell, which no count can observe.
        let text: Arc<str> = Arc::from("shared");

        let original = shared_anns(&text, 4);
        let clone = original.clone();
        assert_eq!(Arc::strong_count(&text), 9, "1 held + 4 + 4 cloned");
        drop(original);
        // The clone is untouched by the original's drop: still four live symbols of its own.
        assert_eq!(clone.len(), 4);
        assert_eq!(Arc::strong_count(&text), 5);
        drop(clone);
        assert_eq!(Arc::strong_count(&text), 1);

        let container = vec![
            shared_anns(&text, 0),
            shared_anns(&text, 1),
            shared_anns(&text, 2),
            shared_anns(&text, 3),
        ];
        assert_eq!(Arc::strong_count(&text), 7, "1 held + 0 + 1 + 2 + 3");
        drop(container);
        assert_eq!(
            Arc::strong_count(&text),
            1,
            "container drop must free every arm"
        );
    }

    #[test]
    fn drop_during_unwind() {
        use std::panic::catch_unwind;
        // A panic while an `Annotations` (and its clone) are live must run their destructors as the
        // stack unwinds, freeing each exactly once. The shared handle count returning to 1 after the
        // unwind is caught shows both destructors ran under plain `cargo test`; Miri, when run, adds
        // the double-free and use-after-free checks on top.
        let text: Arc<str> = Arc::from("shared");
        let result = catch_unwind(|| {
            let held = shared_anns(&text, 3);
            let _also = held.clone();
            panic!("unwind with live annotations");
        });
        assert!(result.is_err());
        assert_eq!(
            Arc::strong_count(&text),
            1,
            "unwinding must run every destructor"
        );
    }
}
