//! Methods for working with raw pointers.
//!
//! The lazy reader and writer APIs use a bump allocator to cheaply create and discard buffers
//! and collections in the process of encoding and decoding. The bump allocator's contents remain
//! valid as long as necessary; the owning reader or writer calling `reset()` when
//! they are no longer required. This allows state to be preserved across top-level method
//! calls, but the lifetime of that state is not something that can be statically verified
//! by the current version of the borrow checker. (Polonius may address this to some extent.)
//!
//! The methods in this module are used to manually define the lifetime of values that reside
//! in the bump allocator and which must also be available across top-level method calls.

/// Helper function that turns a raw pointer into a mutable reference of the specified type.
///
/// The caller is responsible for confirming that `ptr` is a valid reference to some value
/// of type `T`.
pub(crate) unsafe fn ptr_to_mut_ref<'a, T>(ptr: *mut ()) -> &'a mut T {
    let typed_ptr: *mut T = ptr.cast();
    &mut *typed_ptr
}

/// Helper function that turns a mutable reference into a raw pointer.
///
/// Because this method does not read the data to which the reference points,
/// it is not considered `unsafe`.
pub(crate) fn mut_ref_to_ptr<T>(reference: &mut T) -> *mut () {
    let ptr: *mut T = reference;
    let untyped_ptr: *mut () = ptr.cast();
    untyped_ptr
}
