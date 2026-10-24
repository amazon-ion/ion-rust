use crate::decimal::{Coefficient, Sign};
use crate::result::IonFailure;
use crate::serde::{TunnelBytes, DECIMAL_KIND};
use crate::{Decimal, IonError, IonResult, UInt};
use serde::de::Visitor;
use serde::{self, de, Deserialize, Deserializer, Serialize};
use std::fmt;
use std::mem::size_of;

pub(crate) const TUNNELED_DECIMAL_TYPE_NAME: &str = "$__ion_rs_decimal__";

/// Length of the kind, exponent, and sign bytes that precede the magnitude.
const DECIMAL_PREFIX_LEN: usize = 1 + size_of::<i64>() + 1;

// Layout: [kind][exponent: i64 LE][sign: u8 0|1][magnitude: LE bytes]
impl From<&Decimal> for TunnelBytes {
    fn from(decimal: &Decimal) -> Self {
        let coefficient = decimal.coefficient();
        let magnitude = coefficient.magnitude().to_le_bytes();
        let mut bytes = Vec::with_capacity(DECIMAL_PREFIX_LEN + magnitude.len());
        bytes.push(DECIMAL_KIND);
        bytes.extend_from_slice(&decimal.exponent().to_le_bytes());
        bytes.push((coefficient.sign() == Sign::Negative) as u8);
        bytes.extend_from_slice(&magnitude);
        TunnelBytes(bytes)
    }
}

impl TryFrom<TunnelBytes> for Decimal {
    type Error = IonError;

    fn try_from(payload: TunnelBytes) -> Result<Self, Self::Error> {
        let TunnelBytes(bytes) = payload;
        let Some((&DECIMAL_KIND, rest)) = bytes.split_first() else {
            return IonResult::encoding_error(
                "invalid Decimal serde payload: missing or wrong kind",
            );
        };
        let Some((exponent, rest)) = rest.split_first_chunk() else {
            return IonResult::encoding_error("invalid Decimal serde payload: truncated exponent");
        };
        let (sign, magnitude) = match rest.split_first() {
            Some((&0, magnitude)) => (Sign::Positive, magnitude),
            Some((&1, magnitude)) => (Sign::Negative, magnitude),
            Some(_) => {
                return IonResult::encoding_error(
                    "invalid Decimal serde payload: sign byte must be 0 or 1",
                )
            }
            None => {
                return IonResult::encoding_error("invalid Decimal serde payload: missing sign")
            }
        };
        let coefficient = Coefficient::from_sign_and_value(sign, UInt::from_le_bytes(magnitude));
        Ok(Decimal::new(coefficient, i64::from_le_bytes(*exponent)))
    }
}

/// Serialization for Ion `Decimal`
/// This serialization internally uses `serialize_newtype_struct` to trick serde to serialize a number value into decimal.
/// This `newtype_struct` is named with `$__ion_rs_decimal__` to distinguish it from an actual `newtype_struct`.
/// More information on `newtype_struct` can be found in the serde data model: `<https://serde.rs/data-model.html#types>`
impl Serialize for Decimal {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        serializer.serialize_newtype_struct(TUNNELED_DECIMAL_TYPE_NAME, &TunnelBytes::from(self))
    }
}

/// Deserialization for Ion `Decimal`
/// This deserialization internally uses `deserialize_newtype_struct` to trick serde to deserialize a number value into decimal.
/// This `newtype_struct` is named with `$__ion_rs_decimal__` to distinguish it from an actual `newtype_struct`.
/// More information on `newtype_struct` can be found in the serde data model: `<https://serde.rs/data-model.html#types>`
impl<'de> Deserialize<'de> for Decimal {
    fn deserialize<D>(deserializer: D) -> Result<Decimal, D::Error>
    where
        D: Deserializer<'de>,
    {
        struct DecimalVisitor;

        impl<'de> Visitor<'de> for DecimalVisitor {
            type Value = Decimal;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("an Ion Decimal")
            }

            fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: Deserializer<'de>,
            {
                let payload = TunnelBytes::deserialize(deserializer)?;
                Decimal::try_from(payload).map_err(|e| de::Error::custom(e.to_string()))
            }
        }

        deserializer.deserialize_newtype_struct(TUNNELED_DECIMAL_TYPE_NAME, DecimalVisitor)
    }
}
