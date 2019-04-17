//! This module provides the necessary structures and logic to read values from a binary Ion
//! data stream.
mod header;
mod nibbles;
mod type_code;

pub(crate) use type_code::IonTypeCode;
