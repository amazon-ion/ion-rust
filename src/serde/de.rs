use crate::data_source::ToIonDataSource;
use crate::{IonError, IonResult, IonType, ReaderBuilder, StreamItem, StreamReader, Symbol};
use chrono::{DateTime, FixedOffset};
use serde::de;
use serde::de::{DeserializeSeed, EnumAccess, MapAccess, SeqAccess, Visitor};
use serde::Deserialize;
use std::borrow::Cow;
use std::iter::FusedIterator;
use std::marker::PhantomData;

pub fn from_ion_datasource<'a, T, S>(s: S) -> IonResult<T>
where
    T: Deserialize<'a>,
    S: ToIonDataSource,
{
    let mut deserializer = Deserializer {
        reader: ReaderBuilder::new().build(s)?,
    };

    // If we are hovering over nothing call next till we have an object
    while StreamItem::Nothing == deserializer.reader.current() {
        deserializer.reader.next()?;
    }

    T::deserialize(&mut deserializer)
}

#[inline]
pub fn from_slice<'a, T>(s: &'a [u8]) -> IonResult<T>
where
    T: Deserialize<'a>,
{
    from_ion_datasource(s)
}

#[inline]
pub fn from_str<'a, T>(s: &'a str) -> IonResult<T>
where
    T: Deserialize<'a>,
{
    from_ion_datasource(s)
}

pub struct Deserializer<R> {
    pub(crate) reader: R,
}

impl<'de, 'a, R> serde::de::Deserializer<'de> for &'a mut Deserializer<R>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if let Some(ion_type) = self.reader.ion_type() {
            match ion_type {
                IonType::Null => self.deserialize_unit(visitor),
                IonType::Blob | IonType::Clob => self.deserialize_bytes(visitor),
                IonType::String | IonType::Symbol => self.deserialize_string(visitor),
                IonType::Float => self.deserialize_f64(visitor),
                IonType::Integer | IonType::Decimal => self.deserialize_i64(visitor),
                IonType::Boolean => self.deserialize_bool(visitor),
                IonType::List => self.deserialize_seq(visitor),
                IonType::Struct => self.deserialize_struct("", &[], visitor),
                IonType::Timestamp => visitor.visit_map(TimestampDeserializer::<'a> {
                    visited: false,
                    deserializer: self,
                }),
                _ => Err(IonError::DecodingError {
                    description: "unexpected ion type".to_string(),
                }),
            }
        } else {
            Err(IonError::DecodingError {
                description: "unexpected end of file".to_string(),
            })
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_bool(self.reader.read_bool()?);
        self.reader.next()?;
        result
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_i8(self.reader.read_i64().map(|x| x as i8)?);
        self.reader.next()?;
        result
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_i16(self.reader.read_i64().map(|x| x as i16)?);
        self.reader.next()?;
        result
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_i32(self.reader.read_i64().map(|x| x as i32)?);
        self.reader.next()?;
        result
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_i64(self.reader.read_i64().map(|x| x as i64)?);
        self.reader.next()?;
        result
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_u8(self.reader.read_i64().map(|x| x as u8)?);
        self.reader.next()?;
        result
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_u16(self.reader.read_i64().map(|x| x as u16)?);
        self.reader.next()?;
        result
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_u32(self.reader.read_i64().map(|x| x as u32)?);
        self.reader.next()?;
        result
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_u64(self.reader.read_i64().map(|x| x as u64)?);
        self.reader.next()?;
        result
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_f32(self.reader.read_f32()?);
        self.reader.next()?;
        result
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_f64(self.reader.read_f64()?);
        self.reader.next()?;
        result
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_char(
            self.reader
                .read_string()
                .map(|x| x.chars().collect::<Vec<char>>()[0])?,
        );
        self.reader.next()?;
        result
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_string(self.reader.read_string()?);
        self.reader.next()?;
        result
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_string(self.reader.read_string()?);
        self.reader.next()?;
        result
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_bytes(self.reader.read_blob()?.as_slice());
        self.reader.next()?;
        result
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_byte_buf(self.reader.read_blob()?);
        self.reader.next()?;
        result
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if self.reader.is_null() {
            self.reader.next()?;
            visitor.visit_none()
        } else {
            visitor.visit_some(self)
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if self.reader.is_null() {
            self.reader.next()?;
            visitor.visit_unit()
        } else {
            Err(IonError::DecodingError {
                description: "expected a null value".to_string(),
            })
        }
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_unit(visitor)
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.reader.step_in()?;
        self.reader.next()?;
        let result = visitor.visit_newtype_struct(&mut *self)?;
        self.reader.next()?;
        Ok(result)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.reader.step_in()?;
        self.reader.next()?;
        let result = visitor.visit_seq(&mut *self);
        self.reader.next()?;
        result
    }

    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.reader.step_in()?;
        self.reader.next()?;
        let result = visitor.visit_seq(&mut *self);
        self.reader.next()?;
        result
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.reader.step_in()?;
        self.reader.next()?;
        let result = visitor.visit_seq(&mut *self);
        self.reader.next()?;
        result
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.reader.step_in()?;
        self.reader.next()?;
        let result = visitor.visit_map(&mut *self);
        self.reader.next()?;
        result
    }

    fn deserialize_struct<V>(
        self,
        name: &'static str,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if name == "$datetime" && fields == ["$datetime"] {
            let result = visitor.visit_map(TimestampDeserializer {
                visited: false,
                deserializer: self,
            });
            self.reader.next()?;
            return result;
        }

        self.reader.step_in()?;
        self.reader.next()?;
        let result = visitor.visit_map(&mut *self)?;
        self.reader.next()?;
        Ok(result)
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if let Some(ion_type) = self.reader.ion_type() {
            match ion_type {
                IonType::String => visitor.visit_enum(UnitVariantAccess::new(self)),
                IonType::Struct => {
                    self.reader.step_in()?;
                    self.reader.next()?;
                    let value = visitor.visit_enum(VariantAccess::new(self))?;
                    self.reader.step_out()?;
                    self.reader.next()?;
                    Ok(value)
                }
                _ => Err(IonError::DecodingError {
                    description: "expeted an enumeration".to_string(),
                }),
            }
        } else {
            Err(IonError::DecodingError {
                description: "unexpected end of file".to_string(),
            })
        }
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_string(self.reader.read_string()?);
        self.reader.next()?;
        result
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_any(visitor)
    }
}

impl<'de, 'a, R> SeqAccess<'de> for &'a mut Deserializer<R>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        if self.reader.ion_type().is_none() {
            if self.reader.depth() > 0 {
                self.reader.step_out()?;
            }
            Ok(None)
        } else {
            seed.deserialize(&mut **self).map(Some)
        }
    }
}

impl<'de, 'a, R> MapAccess<'de> for &'a mut Deserializer<R>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: DeserializeSeed<'de>,
    {
        if self.reader.ion_type().is_none() {
            self.reader.step_out()?;
            Ok(None)
        } else {
            let key = self.reader.field_name().map(|x| x.to_string())?;
            let deserializer = MapKeyDeserializer { key };
            Ok(Some(seed.deserialize(deserializer)?))
        }
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: DeserializeSeed<'de>,
    {
        seed.deserialize(&mut **self)
    }
}

struct VariantAccess<'a, R: 'a> {
    de: &'a mut Deserializer<R>,
}

impl<'a, R: 'a> VariantAccess<'a, R> {
    fn new(de: &'a mut Deserializer<R>) -> Self {
        VariantAccess { de }
    }
}

impl<'de, 'a, R: 'a> EnumAccess<'de> for VariantAccess<'a, R>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: DeserializeSeed<'de>,
    {
        Ok((seed.deserialize(&mut *self.de)?, self))
    }
}

impl<'de, 'a, R: 'a> de::VariantAccess<'de> for VariantAccess<'a, R>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        de::Deserialize::deserialize(self.de)
    }

    fn newtype_variant_seed<T>(self, seed: T) -> Result<T::Value, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        seed.deserialize(self.de)
    }

    fn tuple_variant<V>(self, _len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        de::Deserializer::deserialize_seq(self.de, visitor)
    }

    fn struct_variant<V>(
        self,
        fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        de::Deserializer::deserialize_struct(self.de, "", fields, visitor)
    }
}

struct UnitVariantAccess<'a, R: 'a> {
    de: &'a mut Deserializer<R>,
}

impl<'a, R: 'a> UnitVariantAccess<'a, R> {
    fn new(de: &'a mut Deserializer<R>) -> Self {
        UnitVariantAccess { de }
    }
}

impl<'de, 'a, R: 'a> EnumAccess<'de> for UnitVariantAccess<'a, R>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: DeserializeSeed<'de>,
    {
        let variant = seed.deserialize(&mut *self.de)?;
        Ok((variant, self))
    }
}

impl<'de, 'a, R: 'a> de::VariantAccess<'de> for UnitVariantAccess<'a, R>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, _seed: T) -> Result<T::Value, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        Err(IonError::DecodingError {
            description: "Unexpected newtype variant".to_string(),
        })
    }

    fn tuple_variant<V>(self, _len: usize, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "Unexpected tuple variant".to_string(),
        })
    }

    fn struct_variant<V>(
        self,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "Unexpected struct variant".to_string(),
        })
    }
}

struct MapKeyDeserializer {
    key: String,
}

impl<'de> de::Deserializer<'de> for MapKeyDeserializer {
    type Error = IonError;

    fn deserialize_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_bool<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_i8<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_i16<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_i32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_i64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_u8<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_u16<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_u32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_u64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_f32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_f64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_char<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_str(self.key.as_str())
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_string(self.key)
    }

    fn deserialize_bytes<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_option<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_unit<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_seq<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_tuple<V>(self, _len: usize, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_tuple_struct<V>(
        self,
        _name: &'static str,
        _len: usize,
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_map<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_struct<V>(
        self,
        _name: &'static str,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_enum<V>(
        self,
        _name: &'static str,
        _variants: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_string(self.key)
    }

    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        Err(IonError::DecodingError {
            description: "expected a string value".to_string(),
        })
    }
}

struct TimestampDeserializer<'a, R> {
    visited: bool,
    deserializer: &'a mut Deserializer<R>,
}

impl<'a, 'de, R> de::MapAccess<'de> for TimestampDeserializer<'a, R>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, IonError>
    where
        K: de::DeserializeSeed<'de>,
    {
        if self.visited {
            return Ok(None);
        }
        self.visited = true;
        seed.deserialize(DatetimeFieldDeserializer).map(Some)
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, IonError>
    where
        V: de::DeserializeSeed<'de>,
    {
        let timestamp = self.deserializer.reader.read_timestamp()?;
        let datetime: DateTime<FixedOffset> = timestamp.try_into().unwrap();
        let datetime_str = datetime.to_rfc3339();

        seed.deserialize(StrDeserializer::new(Cow::from(datetime_str)))
    }
}

struct DatetimeFieldDeserializer;

impl<'de> de::Deserializer<'de> for DatetimeFieldDeserializer {
    type Error = IonError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, IonError>
    where
        V: de::Visitor<'de>,
    {
        visitor.visit_borrowed_str("$datetime")
    }

    serde::forward_to_deserialize_any! {
        bool u8 u16 u32 u64 i8 i16 i32 i64 f32 f64 char str string seq
        bytes byte_buf map struct option unit newtype_struct
        ignored_any unit_struct tuple_struct tuple enum identifier
    }
}

struct StrDeserializer<'a> {
    key: Cow<'a, str>,
}

impl<'a> StrDeserializer<'a> {
    fn new(key: Cow<'a, str>) -> StrDeserializer<'a> {
        StrDeserializer { key }
    }
}

impl<'de> de::Deserializer<'de> for StrDeserializer<'de> {
    type Error = IonError;

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, IonError>
    where
        V: de::Visitor<'de>,
    {
        match self.key {
            Cow::Borrowed(s) => visitor.visit_borrowed_str(s),
            Cow::Owned(s) => visitor.visit_string(s),
        }
    }

    serde::forward_to_deserialize_any! {
        bool u8 u16 u32 u64 i8 i16 i32 i64 f32 f64 char str string seq
        bytes byte_buf map struct option unit newtype_struct
        ignored_any unit_struct tuple_struct tuple enum identifier
    }
}

pub struct StreamDeserializer<'de, R, T> {
    de: Deserializer<R>,
    failed: bool,
    output: PhantomData<T>,
    lifetime: PhantomData<&'de ()>,
}

impl<'de, R, T> StreamDeserializer<'de, R, T>
where
    T: de::Deserialize<'de>,
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
{
    pub fn new(read: R) -> Self {
        Self {
            de: Deserializer { reader: read },
            failed: false,
            output: PhantomData,
            lifetime: PhantomData,
        }
    }
}

impl<'de, R, T> Iterator for StreamDeserializer<'de, R, T>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
    T: de::Deserialize<'de>,
{
    type Item = IonResult<T>;

    fn next(&mut self) -> Option<IonResult<T>> {
        // Skip any nothing
        while let StreamItem::Nothing = self.de.reader.current() {
            match self.de.reader.next() {
                Ok(_) => (),
                Err(_) => return None,
            };
        }

        Some(T::deserialize(&mut self.de))
    }
}

impl<'de, R, T> FusedIterator for StreamDeserializer<'de, R, T>
where
    R: StreamReader<Symbol = Symbol, Item = StreamItem>,
    T: de::Deserialize<'de>,
{
}
