use crate::types::UInt;
use num_bigint::{BigInt, BigUint};

/// A simple wrapper type around a [`UInt`]. Users are not expected to construct
/// instances of `Magnitude` directly; it is provided for conversion ergonomics.
///
/// Signed integer types cannot implement `Into<UInt>`. Instead, they implement
/// `TryInto<UInt>` and report an error if the input integer is negative.
///
/// Signed integers can infallibly implement `Into<Magnitude>` by using their
/// absolute value.
pub struct Magnitude(UInt);

impl Magnitude {
    fn new<I: Into<UInt>>(value: I) -> Self {
        Magnitude(value.into())
    }
}

impl From<UInt> for Magnitude {
    fn from(value: UInt) -> Self {
        Magnitude(value)
    }
}

impl From<Magnitude> for UInt {
    fn from(value: Magnitude) -> Self {
        value.0
    }
}

impl From<BigUint> for Magnitude {
    fn from(value: BigUint) -> Self {
        let uint: UInt = value.into();
        Magnitude(uint)
    }
}

impl From<BigInt> for Magnitude {
    fn from(value: BigInt) -> Self {
        let uint: UInt = value.into_parts().1.into();
        Magnitude(uint)
    }
}

macro_rules! impl_magnitude_from_small_unsigned_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Magnitude {
            fn from(value: $t) -> Magnitude {
                let uint: UInt = value.into();
                Magnitude(uint)
            }
        }
    )*)
}

impl_magnitude_from_small_unsigned_int_types!(u8, u16, u32, u64, u128, usize);

macro_rules! impl_magnitude_from_small_signed_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Magnitude {
            fn from(value: $t) -> Magnitude {
                let uint: UInt = (value.unsigned_abs() as u64).into();
                Magnitude(uint)
            }
        }
    )*)
}

impl_magnitude_from_small_signed_int_types!(i8, i16, i32, i64, isize);
