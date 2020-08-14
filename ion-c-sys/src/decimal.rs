// Copyright Amazon.com, Inc. or its affiliates.

//! Provides higher-level APIs for `ION_DECIMAL`

use crate::result::*;
use crate::*;

use std::ops::{Deref, DerefMut};

/// Smart Pointer over `ION_DECIMAL` to ensure that `ion_decimal_free` is invoked on the instance.
pub struct IonDecimalPtr {
    /// Unlike `ION_INT`, we can own the memory of the `ION_DECIMAL` structure itself, but its
    /// underlying components are managed by `ion_decimal_free`.
    value: ION_DECIMAL,
}

impl IonDecimalPtr {
    /// Creates an `ION_DECIMAL` from an `i32`.
    pub fn try_from_i32(value: i32) -> IonCResult<Self> {
        let mut decimal = Self::try_from_existing(ION_DECIMAL::default())?;
        ionc!(ion_decimal_from_int32(decimal.as_mut_ptr(), value))?;
        Ok(decimal)
    }

    /// Creates an `ION_DECIMAL` from a `BigDecimal`.
    pub fn try_from_bigdecimal(value: &BigDecimal) -> IonCResult<Self> {
        let mut decimal = Self::try_from_existing(ION_DECIMAL::default())?;
        decimal.try_assign_bigdecimal(value)?;
        Ok(decimal)
    }

    /// Binds an existing `ION_DECIMAL` to a pointer.
    pub fn try_from_existing(value: ION_DECIMAL) -> IonCResult<Self> {
        Ok(Self { value })
    }

    /// Returns the underlying `ION_DECIMAL` as a mutable pointer.
    pub fn as_mut_ptr(&mut self) -> *mut ION_DECIMAL {
        &mut self.value
    }
}

impl Deref for IonDecimalPtr {
    type Target = ION_DECIMAL;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl DerefMut for IonDecimalPtr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl Drop for IonDecimalPtr {
    fn drop(&mut self) {
        unsafe {
            ion_decimal_free(&mut self.value);
        }
    }
}
