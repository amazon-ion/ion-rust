// Copyright Amazon.com, Inc. or its affiliates.

//! Provides higher-level APIs for `ION_INT`

use crate::result::*;
use crate::*;

use std::ops::{Deref, DerefMut};
use std::ptr;

/// Smart Pointer over `ION_INT` to ensure that `ion_int_free` is invoked on the instance.
#[derive(Debug)]
pub struct IonIntPtr {
    value: *mut ION_INT,
}

impl IonIntPtr {
    /// Allocates a new `ION_INT` to zero.
    pub fn try_new() -> IonCResult<Self> {
        let mut value = ptr::null_mut();
        ionc!(ion_int_alloc(ptr::null_mut(), &mut value))?;
        ionc!(ion_int_init(
            value,
            ptr::null_mut(), // no owner - defers to normal Ion C xalloc/xfree
        ))?;

        Ok(Self { value })
    }

    /// Allocates a new `ION_INT` from a `BigInt`.
    pub fn try_from_bigint(value: &BigInt) -> IonCResult<Self> {
        let mut ion_int = IonIntPtr::try_new()?;
        ion_int.assign_from_bigint(&value)?;

        Ok(ion_int)
    }

    /// Returns the underlying `ION_INT` as a mutable pointer.
    pub fn as_mut_ptr(&mut self) -> *mut ION_INT {
        self.value
    }
}

impl Deref for IonIntPtr {
    type Target = ION_INT;

    fn deref(&self) -> &Self::Target {
        unsafe { &*(self.value) }
    }
}

impl DerefMut for IonIntPtr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *(self.value) }
    }
}

impl Drop for IonIntPtr {
    fn drop(&mut self) {
        unsafe {
            ion_int_free(self.value);
        }
    }
}
