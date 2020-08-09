// Copyright Amazon.com, Inc. or its affiliates.

//! Provides higher-level APIs for borrowing `str` slices safely from Ion C.

use std::marker::PhantomData;
use std::ops::Deref;

use crate::*;

/// Represents a `str` slice that is borrowed from some source.
///
/// This struct provides the mutable borrowing context for the given slice to avoid
/// destructive APIs from being called from the referent.
#[derive(Debug, Copy, Clone)]
pub struct StrSliceRef<'a> {
    string: &'a str,
    /// Placeholder to tie our lifetime back to the source of the data as a mutable borrow.
    referent: PhantomData<&'a mut u8>,
}

impl<'a> StrSliceRef<'a> {
    /// Creates a new reference to an `ION_STRING` mutably borrowed from `src`.
    #[inline]
    pub fn new<T>(_src: &'a mut T, string: &'a str) -> Self {
        StrSliceRef {
            string,
            referent: PhantomData::default(),
        }
    }

    /// Convenience method to get the underlying `&str`.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.string
    }
}

impl Deref for StrSliceRef<'_> {
    type Target = str;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.string
    }
}

/// Represents a slice of `str` slices that are borrowed from some source.
///
/// This struct provides the mutable borrowing context for the given slice to avoid
/// destructive APIs from being called from the referent.
#[derive(Debug, Clone)]
pub struct StrSlicesRef<'a> {
    /// holder for the slices--we don't currently have built in storage for the array itself
    /// from Ion C, so we hold it here in a `Vec`.
    strs: Vec<&'a str>,

    /// Placeholder to tie our lifetime back to the source of the data.
    referent: PhantomData<&'a mut u8>,
}

impl<'a> StrSlicesRef<'a> {
    #[inline]
    pub fn new<T>(_src: &'a mut T, strs: Vec<&'a str>) -> Self {
        Self {
            strs,
            referent: Default::default(),
        }
    }

    /// Convenience method to get the underlying slice of `&str`.
    #[inline]
    pub fn as_slice(&self) -> &[&str] {
        self.strs.as_slice()
    }
}

impl<'a> Deref for StrSlicesRef<'a> {
    type Target = [&'a str];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.strs.as_slice()
    }
}
