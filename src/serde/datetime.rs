use crate::{IonError, Timestamp};
use chrono::{DateTime, FixedOffset, Utc};
use serde::{self, de, ser, ser::SerializeStruct, Deserialize, Serialize};
use serde_with::{DeserializeAs, SerializeAs};
use std::cell::Cell;
use std::fmt;

thread_local! {
    /// Cell that contains a flag to determine when serialization and deserialization
    /// is occurring with an ION serializer. This allows us to know when to encode
    /// Timestamps as ion timestamps
    pub(crate) static ION_BINARY_TIMESTAMP: Cell<bool> = Cell::new(false);
}

/// Serialization for ION's `Timestamp` object. This is dependent on `ION_BINARY_TIMESTAMP`.
/// when the serializer has switched this thread local flag on, we know we are serializing inside
/// an Ion compatible serializer. As such we actually use a trick to get to the write_timestamp method.
/// This trick is by creating a custom structure that we then catch in the serializer/deserializer
impl Serialize for Timestamp {
    #[inline]
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::ser::Serializer,
    {
        ION_BINARY_TIMESTAMP.with(move |cell| {
            let datetime: DateTime<FixedOffset> = self
                .clone()
                .try_into()
                .map_err(|e: IonError| ser::Error::custom(e.to_string()))?;
            if cell.get() {
                let mut state = serializer.serialize_struct("$datetime", 1)?;
                state.serialize_field("$datetime", datetime.to_rfc3339().as_str())?;
                state.end()
            } else {
                if self.offset.is_some() {
                    serializer.serialize_str(datetime.to_rfc3339().as_str())
                } else {
                    self.date_time.serialize(serializer)
                }
            }
        })
    }
}

/// Deserialization support for `Timestamp` once again we utilize `ION_BINARY_TIMESTAMP` to
/// determine if we are deserializing the timestamp from ION
impl<'de> Deserialize<'de> for Timestamp {
    fn deserialize<D>(deserializer: D) -> Result<Timestamp, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        ION_BINARY_TIMESTAMP.with(move |cell| {
            if cell.get() {
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

/// `TimestampKey` is used to detect and extract a custom ion datetime in its
/// intermediary structure format. It is primarily used inside of a Visitor inside
/// the deserialization for `Timestamp`
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

/// `TimestampFromString` is responsible for extracting the actual timestamp value
/// out of the custom intermediary structure used for handling ION `Timestamp` values
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
                let naive: DateTime<FixedOffset> = match DateTime::parse_from_rfc3339(s) {
                    Ok(data) => Ok(data),
                    Err(e) => Err(de::Error::custom(e.to_string())),
                }?;
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
