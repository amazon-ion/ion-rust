// Copyright Amazon.com, Inc. or its affiliates.

use std::marker::PhantomData;
use std::ops::{Deref, DerefMut};

use crate::*;

/// Represents a borrowed reference `ION_STRING`.
///
/// Ion C's `ION_STRING` type is essentially a `str` slice.  This struct provides
/// the mutable borrowing context for a given `ION_STRING`.
pub struct IonCStringRef<'a> {
    string: ION_STRING,
    /// Placeholder to tie our lifecycle back to the source of the data.
    referent: PhantomData<&'a mut u8>,
}

impl<'a> IonCStringRef<'a> {
    /// Creates a new reference to an `ION_STRING` mutably borrowed from `src`.
    #[inline]
    pub fn new<T>(_src: &'a mut T, value: ION_STRING) -> Self {
        IonCStringRef {
            string: value,
            referent: PhantomData::default(),
        }
    }
}

impl Deref for IonCStringRef<'_> {
    type Target = ION_STRING;

    fn deref(&self) -> &Self::Target {
        &self.string
    }
}

impl DerefMut for IonCStringRef<'_> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.string
    }
}
