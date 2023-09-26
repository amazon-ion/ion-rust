use crate::Decimal;
use serde::de::Visitor;
use serde::{self, Deserialize, Deserializer, Serialize};
use std::fmt;

pub(crate) const TUNNELED_DECIMAL_TYPE_NAME: &str = "$__ion_rs_decimal__";

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
        serializer.serialize_newtype_struct(TUNNELED_DECIMAL_TYPE_NAME, self)
    }
}

/// Deserialization for Ion `Decimal`
/// This deserialization internally uses `serialize_newtype_struct` to trick serde to deserialize a number value into decimal.
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
        }

        deserializer.deserialize_newtype_struct(TUNNELED_DECIMAL_TYPE_NAME, DecimalVisitor)
    }
}
