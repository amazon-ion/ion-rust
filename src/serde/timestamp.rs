use crate::result::IonFailure;
use crate::serde::{TunnelBytes, TIMESTAMP_KIND};
use crate::{IonError, IonResult, Timestamp};
use chrono::{DateTime, FixedOffset, Utc};
use serde::{self, de, ser, Deserialize, Serialize, Serializer};
use serde_with::{DeserializeAs, SerializeAs};
use std::fmt;
use std::mem::size_of;

pub(crate) const TUNNELED_TIMESTAMP_TYPE_NAME: &str = "$__ion_rs_timestamp__";

const TIMESTAMP_PAYLOAD_LEN: usize = 1 + 2 * size_of::<u64>();

// Layout: [kind][packed_fields: u64 LE][attoseconds: u64 LE]
impl From<&Timestamp> for TunnelBytes {
    fn from(timestamp: &Timestamp) -> Self {
        let (packed_fields, attoseconds) = timestamp.to_bits();
        let mut bytes = Vec::with_capacity(TIMESTAMP_PAYLOAD_LEN);
        bytes.push(TIMESTAMP_KIND);
        bytes.extend_from_slice(&packed_fields.to_le_bytes());
        bytes.extend_from_slice(&attoseconds.to_le_bytes());
        TunnelBytes(bytes)
    }
}

impl TryFrom<TunnelBytes> for Timestamp {
    type Error = IonError;

    fn try_from(payload: TunnelBytes) -> Result<Self, Self::Error> {
        let TunnelBytes(bytes) = payload;
        let Some((&TIMESTAMP_KIND, rest)) = bytes.split_first() else {
            return IonResult::encoding_error(
                "invalid Timestamp serde payload: missing or wrong kind",
            );
        };
        let Some((packed_fields, attoseconds)) = rest.split_first_chunk() else {
            return IonResult::encoding_error("invalid Timestamp serde payload: wrong length");
        };
        let Ok(attoseconds) = <[u8; 8]>::try_from(attoseconds) else {
            return IonResult::encoding_error("invalid Timestamp serde payload: wrong length");
        };
        Timestamp::try_from_bits(
            u64::from_le_bytes(*packed_fields),
            u64::from_le_bytes(attoseconds),
        )
    }
}

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
        serializer.serialize_newtype_struct(TUNNELED_TIMESTAMP_TYPE_NAME, &TunnelBytes::from(self))
    }
}

/// Deserialization for Ion `Timestamp`
/// This deserialization internally uses `deserialize_newtype_struct` to trick serde to deserialize a datetime value into timestamp.
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

            fn visit_newtype_struct<D>(self, deserializer: D) -> Result<Self::Value, D::Error>
            where
                D: de::Deserializer<'de>,
            {
                let payload = TunnelBytes::deserialize(deserializer)?;
                Timestamp::try_from(payload).map_err(|e| de::Error::custom(e.to_string()))
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
