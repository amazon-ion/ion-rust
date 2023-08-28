use crate::serde::timestamp::ION_BINARY;
use crate::{Decimal, Element};
use serde::de::Error;
use serde::{self, de, Deserialize, Serialize};
use std::fmt;

/// Serialization for Ion `Decimal`
/// This serialization internally uses `serialize_newtype_struct` to trick serde to serialize a number value into decimal.
/// This `newtype_struct` is named with `$__ion_rs_decimal__` to distinguish it from an actual `newtype_struct`.
/// More information on `newtype_struct` can be found in the serde data model: https://serde.rs/data-model.html#types
impl Serialize for Decimal {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        ION_BINARY.with(move |cell| {
            let decimal: Decimal = self.clone();
            if cell.get() {
                serializer
                    .serialize_newtype_struct("$__ion_rs_decimal__", decimal.to_string().as_str())
            } else {
                serializer.serialize_str(decimal.to_string().as_str())
            }
        })
    }
}

/// Deserialization for Ion `Decimal`
/// This deserialization internally uses `serialize_newtype_struct` to trick serde to deserialize a number value into decimal.
/// This `newtype_struct` is named with `$__ion_rs_decimal__` to distinguish it from an actual `newtype_struct`.
/// More information on `newtype_struct` can be found in the serde data model: https://serde.rs/data-model.html#types
impl<'de> Deserialize<'de> for Decimal {
    fn deserialize<D>(deserializer: D) -> Result<Decimal, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        ION_BINARY.with(move |cell| {
            if cell.get() {
                struct DecimalVisitor;

                impl<'de> de::Visitor<'de> for DecimalVisitor {
                    type Value = Decimal;

                    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                        formatter.write_str("an Ion Decimal")
                    }

                    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
                    where
                        E: Error,
                    {
                        let decimal = Element::read_one(s)
                            .ok()
                            .and_then(|e| e.as_decimal().map(|d| d.to_owned()))
                            .ok_or(E::custom(format!(
                                "Decimal deserialization failed for: {}",
                                s
                            )))?;
                        Ok(decimal)
                    }
                }

                deserializer.deserialize_newtype_struct("$__ion_rs_decimal__", DecimalVisitor)
            } else {
                let string_rep = String::deserialize(deserializer)?;
                let decimal = Element::read_one(&string_rep)
                    .ok()
                    .and_then(|e| e.as_decimal().map(|d| d.to_owned()))
                    .ok_or(Error::custom(format!(
                        "Decimal deserialization failed for: {}",
                        string_rep
                    )))?;
                Ok(decimal)
            }
        })
    }
}
