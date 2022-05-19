use std::cmp::Ordering;

use crate::Integer;
use bigdecimal::ToPrimitive;
use num_bigint::{BigUint, ToBigUint};
use num_integer::Integer as _;
use num_traits::Zero;

/// An unsigned integer that can be combined with a [Sign](crate::types::coefficient::Sign)
/// to act as the coefficient of a [Decimal](crate::types::decimal::Decimal).
///
/// When possible, users should prefer to represent the integer as a [u64] for efficiency. If the
/// integer is too large to fit in a u64, users may instead opt to represent it as a [BigUint] at
/// the cost of allocations and runtime complexity.
#[derive(Clone, Debug)]
pub enum Magnitude {
    U64(u64),
    BigUInt(BigUint),
}

impl PartialEq for Magnitude {
    fn eq(&self, other: &Self) -> bool {
        use Magnitude::*;
        match (self, other) {
            (U64(m1), U64(m2)) => m1 == m2,
            (BigUInt(m1), BigUInt(m2)) => m1 == m2,
            (U64(m1), BigUInt(m2)) => Magnitude::cross_representation_eq(*m1, m2),
            (BigUInt(m1), U64(m2)) => Magnitude::cross_representation_eq(*m2, m1),
        }
    }
}

impl Eq for Magnitude {}

impl PartialOrd for Magnitude {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Magnitude {
    fn cmp(&self, other: &Self) -> Ordering {
        use Magnitude::*;
        match (self, other) {
            (U64(m1), U64(m2)) => m1.cmp(m2),
            (BigUInt(m1), BigUInt(m2)) => m1.cmp(m2),
            (U64(m1), BigUInt(m2)) => Magnitude::cross_representation_cmp(*m1, m2),
            (BigUInt(m1), U64(m2)) => Magnitude::cross_representation_cmp(*m2, m1).reverse(),
        }
    }
}

impl Magnitude {
    /// Compares a [u64] integer with a [BigUint] to see if they are equal. This method never
    /// allocates. It will always prefer to downgrade a BigUint and compare the two integers as
    /// u64 values. If this is not possible, then the two numbers cannot be equal anyway.
    fn cross_representation_eq(m1: u64, m2: &BigUint) -> bool {
        Magnitude::cross_representation_cmp(m1, m2) == Ordering::Equal
    }

    /// Compares a [u64] integer with a [BigUint]. This method never allocates. It will always
    /// prefer to downgrade a BigUint and compare the two integers as u64 values. If this is
    /// not possible, then the BigUint is larger than the u64.
    fn cross_representation_cmp(m1: u64, m2: &BigUint) -> Ordering {
        // Try to downgrade the BigUint first since that's cheaper than upgrading the u64.
        if let Some(downgraded_m2) = m2.to_u64() {
            // If the conversion succeeds, compare the resulting values.
            return m1.cmp(&downgraded_m2);
        }
        // Otherwise, the BigUint must be larger than the u64.
        Ordering::Less
    }

    /// Returns the number of digits in the non-scaled integer representation of the magnitude.
    pub(crate) fn number_of_decimal_digits(&self) -> u64 {
        match self {
            Magnitude::U64(u64_value) => super::num_decimal_digits_in_u64(*u64_value),
            Magnitude::BigUInt(big_uint_value) => {
                Magnitude::calculate_big_uint_digits(big_uint_value)
            }
        }
    }

    fn calculate_big_uint_digits(int: &BigUint) -> u64 {
        if int.is_zero() {
            return 1;
        }
        let mut digits = 0;
        let mut int_value = int.to_owned();
        let ten: BigUint = BigUint::from(10u64);
        while int_value > BigUint::zero() {
            let (quotient, _) = int_value.div_rem(&ten);
            int_value = quotient;
            digits += 1;
        }
        digits
    }
}

impl From<BigUint> for Magnitude {
    fn from(value: BigUint) -> Self {
        // prefer a compact representation for the magnitude
        match value.to_u64() {
            Some(unsigned) => Magnitude::U64(unsigned),
            None => Magnitude::BigUInt(value),
        }
    }
}

impl From<Magnitude> for BigUint {
    fn from(value: Magnitude) -> Self {
        use Magnitude::*;
        match value {
            U64(m) => BigUint::from(m),
            BigUInt(m) => m,
        }
    }
}

impl ToBigUint for Magnitude {
    fn to_biguint(&self) -> Option<BigUint> {
        // This implementation never fails, but the trait requires an `Option` return type.
        Some(self.clone().into())
    }
}

// This macro makes it possible to turn unsigned int primitives into a Coefficient using `.into()`.
// Note that it works for both signed and unsigned ints. The resulting Magnitude will be the
// absolute value of the integer being converted.
macro_rules! impl_magnitude_from_small_unsigned_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Magnitude {
            fn from(value: $t) -> Magnitude {
                Magnitude::U64(value as u64)
            }
        }
    )*)
}

impl_magnitude_from_small_unsigned_int_types!(u8, u16, u32, u64, usize);

macro_rules! impl_magnitude_from_small_signed_int_types {
    ($($t:ty),*) => ($(
        impl From<$t> for Magnitude {
            fn from(value: $t) -> Magnitude {
                // Discard the sign and convert the value to a u64.
                let magnitude: u64 = value.checked_abs()
                        .and_then(|v| Some(v.abs() as u64))
                        // If .abs() fails, it's because <$t>::MIN.abs() cannot be represented
                        // as a $t. We can handle this case by simply using <$>::MAX + 1
                        .unwrap_or_else(|| (<$t>::MAX as u64) + 1);
                Magnitude::U64(magnitude)
            }
        }
    )*)
}

impl_magnitude_from_small_signed_int_types!(i8, i16, i32, i64, isize);

impl From<u128> for Magnitude {
    fn from(value: u128) -> Magnitude {
        Magnitude::BigUInt(BigUint::from(value))
    }
}

impl From<i128> for Magnitude {
    fn from(value: i128) -> Magnitude {
        Magnitude::BigUInt(value.abs().to_biguint().unwrap())
    }
}

impl From<Integer> for Magnitude {
    fn from(value: Integer) -> Self {
        match value {
            Integer::I64(i) => i.into(),
            // num_bigint::BigInt's `into_parts` consumes the BigInt and returns a
            // (sign: Sign, magnitude: BigUint) tuple. We only care about the magnitude, so we
            // extract it here with `.1` ---------------v and then convert the BigUint to a Magnitude
            Integer::BigInt(i) => i.into_parts().1.into(), // <-- using `.into()`
        }
    }
}
#[cfg(test)]
mod magnitude_tests {
    use num_bigint::BigUint;

    use crate::types::magnitude::Magnitude;
    use num_traits::Zero;
    use std::cmp::Ordering;

    fn eq_test<I1, I2>(m1: I1, m2: I2)
    where
        I1: Into<Magnitude>,
        I2: Into<Magnitude>,
    {
        let m1 = m1.into();
        let m2 = m2.into();
        assert_eq!(m1, m2);
    }

    fn ne_test<I1, I2>(m1: I1, m2: I2)
    where
        I1: Into<Magnitude>,
        I2: Into<Magnitude>,
    {
        let m1 = m1.into();
        let m2 = m2.into();
        assert_ne!(m1, m2);
    }

    fn cmp_test<I1, I2>(m1: I1, ordering: Ordering, m2: I2)
    where
        I1: Into<Magnitude>,
        I2: Into<Magnitude>,
    {
        let m1 = m1.into();
        let m2 = m2.into();
        assert!(m1.cmp(&m2) == ordering);
    }

    fn count_decimal_digits_test<M>(m: M, expected_count: u64)
    where
        M: Into<Magnitude>,
    {
        let magnitude = m.into();
        let actual_count = magnitude.number_of_decimal_digits();
        assert_eq!(
            actual_count, expected_count,
            "expected {} decimal digits for {:?}, actual: {}",
            expected_count, magnitude, actual_count
        );
    }

    #[test]
    fn test_magnitude_equals() {
        eq_test(0, 0);
        eq_test(-10, 10);
        eq_test(-7921i16, 7921u128);
        eq_test(BigUint::zero(), 0i64);
    }

    #[test]
    fn test_magnitude_not_equals() {
        ne_test(0, 1);
        ne_test(-9, 10);
        ne_test(-7922i16, 7921u128);
        ne_test(BigUint::zero(), 1i64);
    }

    #[test]
    fn test_magnitude_compare() {
        use Ordering::*;
        cmp_test(0, Equal, 0);
        cmp_test(0, Less, 1);
        cmp_test(1, Greater, 0);
        cmp_test(9, Less, 10);
        cmp_test(10, Equal, 10);
        cmp_test(11, Greater, 10);
        cmp_test(-9, Less, 10);
        cmp_test(-10, Equal, 10);
        cmp_test(-11, Greater, 10);
        cmp_test(-7920i16, Less, 7921u128);
        cmp_test(-7921i16, Equal, 7921u128);
        cmp_test(-7922i16, Greater, 7921u128);
    }

    #[test]
    fn count_decimal_digits() {
        count_decimal_digits_test(0, 1);
        count_decimal_digits_test(1, 1);
        count_decimal_digits_test(2, 1);
        count_decimal_digits_test(10, 2);
        count_decimal_digits_test(11, 2);
        count_decimal_digits_test(12, 2);
        count_decimal_digits_test(100, 3);
        count_decimal_digits_test(101, 3);
        count_decimal_digits_test(102, 3);

        count_decimal_digits_test(BigUint::from(0u64), 1);
        count_decimal_digits_test(BigUint::from(2u64), 1);
        count_decimal_digits_test(BigUint::from(1u64), 1);
        count_decimal_digits_test(BigUint::from(10u64), 2);
        count_decimal_digits_test(BigUint::from(11u64), 2);
        count_decimal_digits_test(BigUint::from(12u64), 2);
        count_decimal_digits_test(BigUint::from(100u64), 3);
        count_decimal_digits_test(BigUint::from(101u64), 3);
        count_decimal_digits_test(BigUint::from(102u64), 3);
    }
}
