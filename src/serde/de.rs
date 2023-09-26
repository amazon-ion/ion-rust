use crate::data_source::IonDataSource;
use crate::result::IonFailure;
use crate::serde::decimal::TUNNELED_DECIMAL_TYPE_NAME;
use crate::serde::timestamp::TUNNELED_TIMESTAMP_TYPE_NAME;
use crate::{
    Decimal, IonError, IonReader, IonResult, IonType, ReaderBuilder, StreamItem, Symbol, Timestamp,
};
use serde::de;
use serde::de::{DeserializeSeed, EnumAccess, MapAccess, SeqAccess, Visitor};
use serde::Deserialize;
use std::borrow::Cow;
use std::iter::FusedIterator;
use std::marker::PhantomData;

/// Generic method that can deserialize an object from any given type
/// that implements `ToIonDataSource`.
pub fn from_ion<'a, T, S>(s: S) -> IonResult<T>
where
    T: Deserialize<'a>,
    S: IonDataSource,
{
    let mut deserializer = Deserializer {
        reader: ReaderBuilder::new().build(s)?,
    };

    if StreamItem::Nothing == deserializer.reader.current() {
        // We're not on a value. Advance the reader.
        deserializer.reader.next()?;
    }

    if StreamItem::Nothing == deserializer.reader.current() {
        // Advancing the reader did nothing; this input contains no values.
        return IonResult::decoding_error(
            "The input for deserialization doesn't contain any values",
        );
    }

    let result = T::deserialize(&mut deserializer)?;
    Ok(result)
}

/// The deserializer for Ion, it doesn't care about
/// whether the reader is reading binary or text representation.
#[derive(Debug)]
pub struct Deserializer<R> {
    pub(crate) reader: R,
}

impl<'de, 'a, R> de::Deserializer<'de> for &'a mut Deserializer<R>
where
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
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
                IonType::Int => self.deserialize_i64(visitor),
                IonType::Decimal => {
                    self.deserialize_newtype_struct(TUNNELED_DECIMAL_TYPE_NAME, visitor)
                }
                IonType::Bool => self.deserialize_bool(visitor),
                IonType::List => self.deserialize_seq(visitor),
                IonType::Struct => self.deserialize_struct("", &[], visitor),
                IonType::Timestamp => {
                    self.deserialize_newtype_struct(TUNNELED_TIMESTAMP_TYPE_NAME, visitor)
                }
                _ => IonResult::decoding_error("unexpected ion type"),
            }
        } else {
            IonResult::decoding_error("unexpected end of file")
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
        let result = visitor.visit_i8(self.reader.read_i64().map(i8::try_from)?.map_err(|_| {
            IonError::decoding_error("found an integer was out of bounds for an `i8`")
        })?);
        self.reader.next()?;
        result
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result =
            visitor.visit_i16(self.reader.read_i64().map(i16::try_from)?.map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `i16`")
            })?);
        self.reader.next()?;
        result
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result =
            visitor.visit_i32(self.reader.read_i64().map(i32::try_from)?.map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `i32`")
            })?);
        self.reader.next()?;
        result
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_i64(self.reader.read_i64()?);
        self.reader.next()?;
        result
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_u8(self.reader.read_i64().map(u8::try_from)?.map_err(|_| {
            IonError::decoding_error("found an integer was out of bounds for an `u8`")
        })?);
        self.reader.next()?;
        result
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result =
            visitor.visit_u16(self.reader.read_i64().map(u16::try_from)?.map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `u16`")
            })?);
        self.reader.next()?;
        result
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result =
            visitor.visit_u32(self.reader.read_i64().map(u32::try_from)?.map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `u32`")
            })?);
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
        let result = visitor.visit_char(self.reader.read_str().and_then(|s| {
            s.chars()
                .next()
                .ok_or_else(|| IonError::decoding_error("expected a char, found an empty string"))
        })?);
        self.reader.next()?;
        result
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_str(self.reader.read_str()?);
        self.reader.next()?;
        result
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_str(self.reader.read_str()?);
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
        let result = visitor.visit_byte_buf(self.reader.read_blob()?.as_slice().to_vec());
        self.reader.next()?;
        result
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if self.reader.is_null() {
            // since this is is a null value which is equivalent to `None` in Rust data type,
            // we can skip reading the next value and call visit_none
            self.reader.next()?;
            visitor.visit_none()
        } else {
            // For non null value we transfer the call to visit_some to perform the deserialization
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
            IonResult::decoding_error("expected a null value")
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
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if name == TUNNELED_TIMESTAMP_TYPE_NAME {
            let timestamp = self.reader.read_timestamp()?;
            assert_eq!(
                std::mem::size_of::<V::Value>(),
                std::mem::size_of::<Timestamp>()
            );
            // # Safety
            // compiler doesn't understand that the generic Timestamp here is actually V::Value here
            // The assert statement above that compares the sizes of the Timestamp and V::Value types
            let visitor_value =
                unsafe { std::mem::transmute_copy::<Timestamp, V::Value>(&timestamp) };
            self.reader.next()?;
            return Ok(visitor_value);
        } else if name == TUNNELED_DECIMAL_TYPE_NAME {
            let decimal = self.reader.read_decimal()?;
            assert_eq!(
                std::mem::size_of::<V::Value>(),
                std::mem::size_of::<Decimal>()
            );
            // # Safety
            // compiler doesn't understand that the generic Decimal here is actually V::Value here
            // The assert statement above that compares the sizes of the Decimal and V::Value types
            let visitor_value = unsafe { std::mem::transmute_copy::<Decimal, V::Value>(&decimal) };
            self.reader.next()?;
            return Ok(visitor_value);
        }
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
        _name: &'static str,
        _fields: &'static [&'static str],
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
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
                _ => IonResult::decoding_error("expected an enumeration"),
            }
        } else {
            IonResult::decoding_error("unexpected end of file")
        }
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_str(self.reader.read_str()?);
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
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
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
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
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
            let key = self
                .reader
                .field_name()
                .map(|x| x.text().unwrap().to_string())?;
            let deserializer = MapKeyDeserializer { key };
            let result = seed.deserialize(deserializer).map(Some)?;
            Ok(result)
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
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
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
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
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
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
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
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
{
    type Error = IonError;

    fn unit_variant(self) -> Result<(), Self::Error> {
        Ok(())
    }

    fn newtype_variant_seed<T>(self, _seed: T) -> Result<T::Value, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        IonResult::decoding_error("Unexpected newtype variant")
    }

    fn tuple_variant<V>(self, _len: usize, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("Unexpected tuple variant")
    }

    fn struct_variant<V>(
        self,
        _fields: &'static [&'static str],
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("Unexpected struct variant")
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
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_bool<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_i8<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_i16<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_i32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_i64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_u8<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_u16<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_u32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_u64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_f32<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_f64<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_char<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
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
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_byte_buf<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_option<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_unit<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_newtype_struct<V>(
        self,
        _name: &'static str,
        _visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_seq<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_tuple<V>(self, _len: usize, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
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
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_map<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
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
        IonResult::decoding_error("expected a string value")
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
        IonResult::decoding_error("expected a string value")
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let result = visitor.visit_string(self.key);
        result
    }

    fn deserialize_ignored_any<V>(self, _visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        IonResult::decoding_error("expected a string value")
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
    output: PhantomData<T>,
    lifetime: PhantomData<&'de ()>,
}

impl<'de, R, T> StreamDeserializer<'de, R, T>
where
    T: de::Deserialize<'de>,
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
{
    pub fn new(read: R) -> Self {
        Self {
            de: Deserializer { reader: read },
            output: PhantomData,
            lifetime: PhantomData,
        }
    }
}

impl<'de, R, T> Iterator for StreamDeserializer<'de, R, T>
where
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
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
    R: IonReader<Symbol = Symbol, Item = StreamItem>,
    T: de::Deserialize<'de>,
{
}
