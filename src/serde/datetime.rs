use crate::Timestamp;
use chrono::{DateTime, FixedOffset, Utc};
use serde::{self, de, ser, ser::SerializeStruct, Deserialize, Serialize};
use serde_with::{DeserializeAs, SerializeAs};
use std::fmt;
use std::fmt::Write;

impl Serialize for Timestamp {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        let datetime: DateTime<FixedOffset> = self.clone().try_into().unwrap();
        let mut state = serializer.serialize_struct("$datetime", 1)?;
        state.serialize_field("$datetime", datetime.to_rfc3339().as_str())?;
        state.end()
    }
}

impl<'de> Deserialize<'de> for Timestamp {
    fn deserialize<D>(deserializer: D) -> Result<Timestamp, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct TimestampVisitor;

        impl<'de> de::Visitor<'de> for TimestampVisitor {
            type Value = Timestamp;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a ION Timestamp")
            }

            fn visit_map<V>(self, mut visitor: V) -> Result<Timestamp, V::Error>
            where
                V: de::MapAccess<'de>,
            {
                let value = visitor.next_key::<TimestampKey>()?;
                if value.is_none() {
                    return Err(de::Error::custom("timestamp key not found"));
                }
                let v: TimestampFromString = visitor.next_value()?;
                Ok(v.value)
            }
        }

        static FIELDS: [&str; 1] = ["$datetime"];
        deserializer.deserialize_struct("$datetime", &FIELDS, TimestampVisitor)
    }
}

struct TimestampKey;

impl<'de> de::Deserialize<'de> for TimestampKey {
    fn deserialize<D>(deserializer: D) -> Result<TimestampKey, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct FieldVisitor;

        impl<'de> de::Visitor<'de> for FieldVisitor {
            type Value = ();

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("a valid datetime field")
            }

            fn visit_str<E>(self, s: &str) -> Result<(), E>
            where
                E: de::Error,
            {
                if s == "$datetime" {
                    Ok(())
                } else {
                    Err(de::Error::custom("expected field with custom name"))
                }
            }
        }

        deserializer.deserialize_identifier(FieldVisitor)?;
        Ok(TimestampKey)
    }
}

pub struct TimestampFromString {
    pub value: Timestamp,
}

impl<'de> de::Deserialize<'de> for TimestampFromString {
    fn deserialize<D>(deserializer: D) -> Result<TimestampFromString, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        struct Visitor;

        impl<'de> de::Visitor<'de> for Visitor {
            type Value = TimestampFromString;

            fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
                formatter.write_str("string containing a datetime")
            }

            fn visit_str<E>(self, s: &str) -> Result<TimestampFromString, E>
            where
                E: de::Error,
            {
                let naive: DateTime<FixedOffset> = DateTime::parse_from_rfc3339(s).unwrap();
                Ok(TimestampFromString {
                    value: Timestamp::from(naive),
                })
            }
        }

        deserializer.deserialize_str(Visitor)
    }
}

impl SerializeAs<DateTime<Utc>> for Timestamp {
    fn serialize_as<S>(source: &chrono::DateTime<Utc>, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: ser::Serializer,
    {
        let dt0: DateTime<FixedOffset> = source.clone().into();
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
        let dt = Timestamp::from(source.clone());
        dt.serialize(serializer)
    }
}

impl<'de> DeserializeAs<'de, DateTime<Utc>> for Timestamp {
    fn deserialize_as<D>(deserializer: D) -> Result<DateTime<Utc>, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        let d0 = Timestamp::deserialize(deserializer)?;
        let d1: DateTime<FixedOffset> = d0.try_into().unwrap();
        Ok(d1.into())
    }
}

impl<'de> DeserializeAs<'de, DateTime<FixedOffset>> for Timestamp {
    fn deserialize_as<D>(deserializer: D) -> Result<DateTime<FixedOffset>, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        let d0 = Timestamp::deserialize(deserializer)?;
        Ok(d0.try_into().unwrap())
    }
}
