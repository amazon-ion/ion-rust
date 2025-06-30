use serde::de;
use serde::de::{DeserializeOwned, DeserializeSeed, EnumAccess, MapAccess, SeqAccess, Visitor};

use crate::lazy::any_encoding::AnyEncoding;
use crate::lazy::r#struct::{LazyField, StructIterator};
use crate::lazy::streaming_raw_reader::IonInput;
use crate::lazy::value::LazyValue;
use crate::lazy::value_ref::ValueRef;
use crate::result::IonFailure;
use crate::serde::decimal::TUNNELED_DECIMAL_TYPE_NAME;
use crate::serde::timestamp::TUNNELED_TIMESTAMP_TYPE_NAME;
use crate::{
    Decimal, IonEncoding, IonError, IonResult, IonType, RawVersionMarker, SystemReader,
    SystemStreamItem, Timestamp,
};

/// Generic method that can deserialize an object from any given type
/// that implements `IonInput`.
pub fn from_ion<T, I>(input: I) -> IonResult<T>
where
    T: DeserializeOwned,
    I: IonInput,
{
    let mut ion_encoding = IonEncoding::default();
    let mut reader = SystemReader::new(AnyEncoding, input);
    loop {
        match reader.next_item()? {
            SystemStreamItem::VersionMarker(marker) => {
                // It's a version marker; update the detected Ion encoding
                ion_encoding = marker.stream_encoding_after_marker()?;
            }
            SystemStreamItem::Value(value) => {
                let value_deserializer = ValueDeserializer::new(
                    &value,
                    /*is_human_readable=*/ ion_encoding.is_text(),
                );
                return T::deserialize(value_deserializer);
            }
            SystemStreamItem::EndOfStream(_end) => {
                return IonResult::decoding_error("stream did not contain any values")
            }
            _system_value => {
                // Ignore system values
            }
        }
    }
}

#[derive(Clone, Copy)]
pub struct ValueDeserializer<'a, 'de> {
    pub(crate) value: &'a LazyValue<'de, AnyEncoding>,
    is_human_readable: bool,
    variant_nesting_depth: usize,  // Holds the number of nested variants we are for tracking
                                   // variant names in annotations. 0 indicates we're not in a
                                   // variant.
}

impl<'a, 'de> ValueDeserializer<'a, 'de> {
    pub(crate) fn new(value: &'a LazyValue<'de, AnyEncoding>, is_human_readable: bool) -> Self {
        Self {
            value,
            is_human_readable,
            variant_nesting_depth: 0,
        }
    }

    fn deserialize_as_sequence<V: Visitor<'de>>(
        self,
        visitor: V,
    ) -> Result<V::Value, <Self as de::Deserializer<'de>>::Error> {
        use ValueRef::*;
        match self.value.read()? {
            List(l) => visitor.visit_seq(SequenceIterator(l.iter(), self.is_human_readable)),
            SExp(l) => visitor.visit_seq(SequenceIterator(l.iter(), self.is_human_readable)),
            _ => IonResult::decoding_error("expected a list or sexp"),
        }
    }
    fn deserialize_as_map<V: Visitor<'de>>(
        self,
        visitor: V,
    ) -> Result<V::Value, <Self as de::Deserializer<'de>>::Error> {
        let strukt = self.value.read()?.expect_struct()?;
        let struct_as_map = StructAsMap::new(strukt.iter(), self.is_human_readable);

        visitor.visit_map(struct_as_map)
    }
}

impl<'de> de::Deserializer<'de> for ValueDeserializer<'_, 'de> {
    type Error = IonError;

    /// Determine whether Deserialize implementations should expect to deserialize their human-readable form.
    /// For binary Ion this will return `false` and for text Ion this will return `true`.
    fn is_human_readable(&self) -> bool {
        self.is_human_readable
    }

    fn deserialize_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        use IonType::*;
        // We look at the IonType because it doesn't require performing a `read()` operation.
        // The appropriate delegate can perform the `read()`.
        match self.value.ion_type() {
            Null => self.deserialize_unit(visitor),
            Bool => self.deserialize_bool(visitor),
            Int => self.deserialize_i64(visitor),
            Float => self.deserialize_f64(visitor),
            Decimal => self.deserialize_newtype_struct(TUNNELED_DECIMAL_TYPE_NAME, visitor),
            Timestamp => self.deserialize_newtype_struct(TUNNELED_TIMESTAMP_TYPE_NAME, visitor),
            String | Symbol => self.deserialize_str(visitor),
            Blob | Clob => self.deserialize_bytes(visitor),
            List | SExp => self.deserialize_seq(visitor),
            Struct => self.deserialize_struct("", &[], visitor),
        }
    }

    fn deserialize_bool<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_bool(self.value.read()?.expect_bool()?)
    }

    fn deserialize_i8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self
            .value
            .read()?
            .expect_i64()
            .map(i8::try_from)?
            .map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `i8`")
            })?;
        visitor.visit_i8(value)
    }

    fn deserialize_i16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self
            .value
            .read()?
            .expect_i64()
            .map(i16::try_from)?
            .map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `i16`")
            })?;
        visitor.visit_i16(value)
    }

    fn deserialize_i32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self
            .value
            .read()?
            .expect_i64()
            .map(i32::try_from)?
            .map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `i32`")
            })?;
        visitor.visit_i32(value)
    }

    fn deserialize_i64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_i64(self.value.read()?.expect_i64()?)
    }

    fn deserialize_u8<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self
            .value
            .read()?
            .expect_i64()
            .map(u8::try_from)?
            .map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for a `u8`")
            })?;
        visitor.visit_u8(value)
    }

    fn deserialize_u16<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self
            .value
            .read()?
            .expect_i64()
            .map(u16::try_from)?
            .map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `u16`")
            })?;
        visitor.visit_u16(value)
    }

    fn deserialize_u32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self
            .value
            .read()?
            .expect_i64()
            .map(u32::try_from)?
            .map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `u32`")
            })?;
        visitor.visit_u32(value)
    }

    fn deserialize_u64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self
            .value
            .read()?
            // There are integer values that fit in a u64 but not an i64, so we use
            // `expect_int` instead of `expect_i64` to accommodate that case.
            .expect_int()
            .map(u64::try_from)?
            .map_err(|_| {
                IonError::decoding_error("found an integer was out of bounds for an `u64`")
            })?;
        visitor.visit_u64(value)
    }

    fn deserialize_f32<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        // XXX: This risks loss of fidelity. If the input stream has an f64 and serde asks for an
        //      f32, this will lose precision.
        visitor.visit_f32(self.value.read()?.expect_float()? as f32)
    }

    fn deserialize_f64<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_f64(self.value.read()?.expect_float()?)
    }

    fn deserialize_char<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self.value.read()?.expect_string().and_then(|s| {
            let mut chars = s.chars();
            let Some(first_char) = chars.next() else {
                return IonResult::decoding_error("expected a char, found an empty string");
            };
            if let Some(_second_char) = chars.next() {
                return IonResult::decoding_error(
                    "expected a char, found a string with two or more characters",
                );
            }
            Ok(first_char)
        })?;
        visitor.visit_char(value)
    }

    fn deserialize_str<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_str(self.value.read()?.expect_text()?)
    }

    fn deserialize_string<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_string(self.value.read()?.expect_text()?.to_owned())
    }

    fn deserialize_bytes<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self.value.read()?.expect_lob()?;
        visitor.visit_bytes(value.as_ref())
    }

    fn deserialize_byte_buf<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self.value.read()?.expect_lob()?;
        // If the BytesRef is already backed by a Vec<u8>, this will use the Vec<u8>
        // instead of creating a clone.
        visitor.visit_bytes(value.as_ref())
    }

    fn deserialize_option<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        if self.value.is_null() {
            visitor.visit_none()
        } else {
            visitor.visit_some(self)
        }
    }

    fn deserialize_unit<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_unit_struct<V>(
        self,
        _name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        visitor.visit_unit()
    }

    fn deserialize_newtype_struct<V>(
        self,
        name: &'static str,
        visitor: V,
    ) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        let value = self.value.read()?;
        if name == TUNNELED_TIMESTAMP_TYPE_NAME {
            let timestamp = value.expect_timestamp()?;
            assert_eq!(
                std::mem::size_of::<V::Value>(),
                std::mem::size_of::<Timestamp>()
            );
            // # Safety
            // compiler doesn't understand that the generic Timestamp here is actually V::Value here
            // The assert statement above that compares the sizes of the Timestamp and V::Value types
            let visitor_value =
                unsafe { std::mem::transmute_copy::<Timestamp, V::Value>(&timestamp) };
            return Ok(visitor_value);
        } else if name == TUNNELED_DECIMAL_TYPE_NAME {
            let decimal = value.expect_decimal()?;
            assert_eq!(
                std::mem::size_of::<V::Value>(),
                std::mem::size_of::<Decimal>()
            );
            // # Safety
            // compiler doesn't understand that the generic Decimal here is actually V::Value here
            // The assert statement above that compares the sizes of the Decimal and V::Value types
            let visitor_value = unsafe { std::mem::transmute_copy::<Decimal, V::Value>(&decimal) };
            return Ok(visitor_value);
        }

        visitor.visit_newtype_struct(self)
    }

    fn deserialize_seq<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_as_sequence(visitor)
    }

    fn deserialize_tuple<V>(self, _len: usize, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_as_sequence(visitor)
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
        self.deserialize_as_sequence(visitor)
    }

    fn deserialize_map<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        self.deserialize_as_map(visitor)
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
        self.deserialize_as_map(visitor)
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
        visitor.visit_enum(VariantAccess::new(self))
    }

    fn deserialize_identifier<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        // Make sure we've started reading an enum.
        if self.variant_nesting_depth == 0 {
            return IonResult::decoding_error("unexpected serde state; was not expecting to read an identifier");
        }

        let mut annotations = self.value.annotations();
        let our_annotation = annotations.nth(self.variant_nesting_depth - 1).transpose()?;
        match our_annotation {
            None => {
                let symbol = self.value.read()?.expect_symbol()?;
                let symbol_text = symbol.text().ok_or_else(|| {
                    IonError::decoding_error(
                        "expected a symbol representing an enum's unit struct variant",
                    )
                })?;
                visitor.visit_str(symbol_text)
            }
            Some(variant_name) => {
                let variant_id = variant_name.text().ok_or_else(|| {
                    IonError::decoding_error("expected an enum variant identifier annotation")
                })?;
                visitor.visit_str(variant_id)
            }
        }
    }

    fn deserialize_ignored_any<V>(self, visitor: V) -> Result<V::Value, Self::Error>
    where
        V: Visitor<'de>,
    {
        // Ignore the value itself, return a `null` that will be also ignored
        visitor.visit_unit()
    }
}

pub(crate) struct SequenceIterator<S>(pub(crate) S, bool);

impl<'de, S> SeqAccess<'de> for SequenceIterator<S>
where
    S: Iterator<Item = IonResult<LazyValue<'de, AnyEncoding>>>,
{
    type Error = IonError;

    fn next_element_seed<T>(&mut self, seed: T) -> Result<Option<T::Value>, Self::Error>
    where
        T: DeserializeSeed<'de>,
    {
        let Some(lazy_value) = self.0.next().transpose()? else {
            return Ok(None);
        };
        let deserializer = ValueDeserializer::new(&lazy_value, self.1);
        seed.deserialize(deserializer).map(Some)
    }
}

struct StructAsMap<'de> {
    iter: StructIterator<'de, AnyEncoding>,
    current_field: Option<LazyField<'de, AnyEncoding>>,
    is_human_readable: bool,
}

impl<'de> StructAsMap<'de> {
    pub fn new(iter: StructIterator<'de, AnyEncoding>, is_human_readable: bool) -> Self {
        Self {
            iter,
            current_field: None,
            is_human_readable,
        }
    }
}

impl<'de> MapAccess<'de> for StructAsMap<'de> {
    type Error = IonError;

    fn next_key_seed<K>(&mut self, seed: K) -> Result<Option<K::Value>, Self::Error>
    where
        K: DeserializeSeed<'de>,
    {
        let Some(field) = self.iter.next_field()? else {
            return Ok(None);
        };

        let name = field
            .name()?
            .text()
            .ok_or_else(|| IonError::decoding_error("found a symbol with unknown text"))?
            .to_owned();
        self.current_field = Some(field);

        let deserializer = MapKeyDeserializer { key: name };
        seed.deserialize(deserializer).map(Some)
    }

    fn next_value_seed<V>(&mut self, seed: V) -> Result<V::Value, Self::Error>
    where
        V: DeserializeSeed<'de>,
    {
        seed.deserialize(ValueDeserializer::new(
            // This method will only be called when `next_key_seed` reported another field,
            // so we can unwrap this safely.
            &self.current_field.as_ref().unwrap().value(),
            self.is_human_readable,
        ))
    }
}

#[derive(Clone, Copy)]
struct VariantAccess<'a, 'de> {
    de: ValueDeserializer<'a, 'de>,
}

impl<'a, 'de> VariantAccess<'a, 'de> {
    fn new(de: ValueDeserializer<'a, 'de>) -> Self {
        let de = ValueDeserializer { variant_nesting_depth: de.variant_nesting_depth + 1, ..de };

        VariantAccess { de }
    }
}

impl<'de> EnumAccess<'de> for VariantAccess<'_, 'de> {
    type Error = IonError;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: DeserializeSeed<'de>,
    {
        Ok((seed.deserialize(self.de)?, self))
    }
}

impl<'de> de::VariantAccess<'de> for VariantAccess<'_, 'de> {
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

#[derive(Clone, Copy)]
struct UnitVariantAccess<'a, 'de> {
    de: ValueDeserializer<'a, 'de>,
}

impl<'de> EnumAccess<'de> for UnitVariantAccess<'_, 'de> {
    type Error = IonError;
    type Variant = Self;

    fn variant_seed<V>(self, seed: V) -> Result<(V::Value, Self::Variant), Self::Error>
    where
        V: DeserializeSeed<'de>,
    {
        let variant = seed.deserialize(self.de)?;
        Ok((variant, self))
    }
}

impl<'de> de::VariantAccess<'de> for UnitVariantAccess<'_, 'de> {
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
        visitor.visit_str(&self.key)
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
