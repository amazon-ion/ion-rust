use crate::serde::SERDE_AS_ION;
use crate::{IonError, Timestamp};
use chrono::{DateTime, FixedOffset, Utc};
use serde::de::Error;
use serde::{self, de, ser, Deserialize, Serialize};
use serde_with::{DeserializeAs, SerializeAs};
use std::fmt;

pub(crate) const ION_TIMESTAMP: &str = "$__ion_rs_timestamp__";

/// Serialization for Ion `Timestamp`
/// This serialization internally uses `serialize_newtype_struct` to trick serde to serialize a datetime value into timestamp.
/// This `newtype_struct` is named with `$__ion_rs_timestamp__` to distinguish it from an actual `newtype_struct`.
/// More information on `newtype_struct` can be found in the serde data model: `<https://serde.rs/data-model.html#types>`
impl Serialize for Timestamp {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        SERDE_AS_ION.with(move |cell| {
            let datetime: DateTime<FixedOffset> = self
                .clone()
                .try_into()
                .map_err(|e: IonError| ser::Error::custom(e.to_string()))?;
            if cell.get() {
                serializer.serialize_newtype_struct(
                    "$__ion_rs_timestamp__",
                    datetime.to_rfc3339().as_str(),
                )
            } else {
                serializer.serialize_str(datetime.to_rfc3339().as_str())
            }
        })
    }
}

/// Deserialization for Ion `Timestamp`
/// This deserialization internally uses `serialize_newtype_struct` to trick serde to deserialize a datetime value into timestamp.
/// This `newtype_struct` is named with `$__ion_rs_timestamp__` to distinguish it from an actual `newtype_struct`.
/// More information on `newtype_struct` can be found in the serde data model: `<https://serde.rs/data-model.html#types>`
impl<'de> Deserialize<'de> for Timestamp {
    fn deserialize<D>(deserializer: D) -> Result<Timestamp, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        SERDE_AS_ION.with(move |cell| {
            if cell.get() {
                struct TimestampVisitor;

                impl<'de> de::Visitor<'de> for TimestampVisitor {
                    type Value = Timestamp;

                    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                        formatter.write_str("an Ion Timestamp")
                    }

                    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
                    where
                        E: Error,
                    {
                        let naive: DateTime<FixedOffset> = match DateTime::parse_from_rfc3339(s) {
                            Ok(data) => Ok(data),
                            Err(e) => Err(de::Error::custom(e.to_string())),
                        }?;
                        Ok(Timestamp::from(naive))
                    }
                }

                deserializer.deserialize_newtype_struct("$__ion_rs_timestamp__", TimestampVisitor)
            } else {
                let string_rep = String::deserialize(deserializer)?;
                let fixed_date: DateTime<FixedOffset> =
                    match DateTime::parse_from_rfc3339(string_rep.as_str()) {
                        Ok(data) => Ok(data),
                        Err(e) => Err(de::Error::custom(e.to_string())),
                    }?;
                Ok(Timestamp::from(fixed_date))
            }
        })
    }
}

impl SerializeAs<DateTime<Utc>> for Timestamp {
    fn serialize_as<S>(source: &chrono::DateTime<Utc>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        let dt0: DateTime<FixedOffset> = (*source).into();
        let dt1 = Timestamp::from(dt0);
        dt1.serialize(serializer)
    }
}

impl SerializeAs<DateTime<FixedOffset>> for Timestamp {
    fn serialize_as<S>(
        source: &chrono::DateTime<FixedOffset>,
        serializer: S,
    ) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        let dt = Timestamp::from(*source);
        dt.serialize(serializer)
    }
}

impl<'de> DeserializeAs<'de, DateTime<Utc>> for Timestamp {
    fn deserialize_as<D>(deserializer: D) -> Result<DateTime<Utc>, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        let d0 = Timestamp::deserialize(deserializer)?;
        let d1: DateTime<FixedOffset> = d0
            .try_into()
            .map_err(|e: IonError| de::Error::custom(e.to_string()))?;
        Ok(d1.into())
    }
}

impl<'de> DeserializeAs<'de, DateTime<FixedOffset>> for Timestamp {
    fn deserialize_as<D>(deserializer: D) -> Result<DateTime<FixedOffset>, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        let d0 = Timestamp::deserialize(deserializer)?;
        d0.try_into()
            .map_err(|e: IonError| de::Error::custom(e.to_string()))
    }
}
