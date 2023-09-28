use crate::{IonError, Timestamp};
use chrono::{DateTime, FixedOffset, Utc};
use serde::{self, de, ser, Deserialize, Serialize, Serializer};
use serde_with::{DeserializeAs, SerializeAs};
use std::fmt;

pub(crate) const TUNNELED_TIMESTAMP_TYPE_NAME: &str = "$__ion_rs_timestamp__";

/// Serialization for Ion `Timestamp`
/// This serialization internally uses `serialize_newtype_struct` to trick serde to serialize a datetime value into timestamp.
/// This `newtype_struct` is named with `$__ion_rs_timestamp__` to distinguish it from an actual `newtype_struct`.
/// More information on `newtype_struct` can be found in the serde data model: `<https://serde.rs/data-model.html#types>`
impl Serialize for Timestamp {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_newtype_struct(TUNNELED_TIMESTAMP_TYPE_NAME, self)
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
        struct TimestampVisitor;

        impl<'de> de::Visitor<'de> for TimestampVisitor {
            type Value = Timestamp;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("an Ion Timestamp")
            }
        }

        deserializer.deserialize_newtype_struct(TUNNELED_TIMESTAMP_TYPE_NAME, TimestampVisitor)
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
