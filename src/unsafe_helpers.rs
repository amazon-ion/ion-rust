/// Helper function that turns a raw pointer into a mutable reference of the specified type.
pub(crate) unsafe fn ptr_to_mut_ref<'a, T>(ptr: *mut ()) -> &'a mut T {
    let typed_ptr: *mut T = ptr.cast();
    &mut *typed_ptr
}

/// Helper function that turns a mutable reference into a raw pointer.
pub(crate) fn mut_ref_to_ptr<T>(reference: &mut T) -> *mut () {
    let ptr: *mut T = reference;
    let untyped_ptr: *mut () = ptr.cast();
    untyped_ptr
}
