// Copyright Amazon.com, Inc. or its affiliates.

//! Provides owned implementations of [`SymbolToken`], [`Element`] and its dependents.
//!
//! This API is simpler to manage with respect to borrowing lifetimes, but requires full
//! ownership of data to do so.

use super::{AnyInt, Element, ImportSource, Sequence, Struct, SymbolToken};
use crate::types::decimal::Decimal;
use crate::types::timestamp::Timestamp;
use crate::types::SymbolId;
use crate::IonType;
use std::collections::HashMap;
use std::iter::FromIterator;
use std::rc::Rc;

/// An owned implementation of  [`ImportSource`].
#[derive(Debug, Clone)]
pub struct OwnedImportSource {
    table: Rc<str>,
    sid: SymbolId,
}

impl OwnedImportSource {
    pub fn new<T: Into<Rc<str>>>(table: T, sid: SymbolId) -> Self {
        Self {
            table: table.into(),
            sid,
        }
    }
}

impl ImportSource for OwnedImportSource {
    fn table(&self) -> &str {
        &self.table
    }

    fn sid(&self) -> usize {
        self.sid
    }
}

/// An owned implementation of [`SymbolToken`].
#[derive(Debug, Clone)]
pub struct OwnedSymbolToken {
    text: Option<Rc<str>>,
    local_sid: Option<SymbolId>,
    source: Option<OwnedImportSource>,
}

impl OwnedSymbolToken {
    pub fn new(
        text: Option<Rc<str>>,
        local_sid: Option<SymbolId>,
        source: Option<OwnedImportSource>,
    ) -> Self {
        Self {
            text,
            local_sid,
            source,
        }
    }
}

impl<T: Into<Rc<str>>> From<T> for OwnedSymbolToken {
    /// Constructs an owned token that has only text.
    fn from(text: T) -> Self {
        Self::new(Some(text.into()), None, None)
    }
}

impl SymbolToken for OwnedSymbolToken {
    type ImportSource = OwnedImportSource;

    fn text(&self) -> Option<&str> {
        self.text.as_ref().map(|s| s.as_ref())
    }

    fn local_sid(&self) -> Option<usize> {
        self.local_sid
    }

    fn source(&self) -> Option<&Self::ImportSource> {
        self.source.as_ref()
    }
}

/// An owned implementation of [`Sequence`]
#[derive(Debug, Clone)]
pub struct OwnedSequence {
    children: Vec<OwnedElement>,
}

impl OwnedSequence {
    pub fn new(children: Vec<OwnedElement>) -> Self {
        Self { children }
    }
}

impl Sequence for OwnedSequence {
    type Element = OwnedElement;

    fn iter<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a> {
        Box::new(self.children.iter())
    }

    fn get(&self, index: usize) -> Option<&Self::Element> {
        if index > self.children.len() {
            None
        } else {
            Some(&self.children[index])
        }
    }

    fn len(&self) -> usize {
        self.children.len()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

/// An owned implementation of [`Struct`]
#[derive(Debug, Clone)]
pub struct OwnedStruct {
    text_fields: HashMap<Rc<str>, Vec<(OwnedSymbolToken, OwnedElement)>>,
    no_text_fields: Vec<(OwnedSymbolToken, OwnedElement)>,
}

impl<K, V> FromIterator<(K, V)> for OwnedStruct
where
    K: Into<OwnedSymbolToken>,
    V: Into<OwnedElement>,
{
    /// Returns an owned struct from the given iterator of field names/values.
    fn from_iter<I: IntoIterator<Item = (K, V)>>(iter: I) -> Self {
        let mut text_fields: HashMap<Rc<str>, Vec<(OwnedSymbolToken, OwnedElement)>> =
            HashMap::new();
        let mut no_text_fields: Vec<(OwnedSymbolToken, OwnedElement)> = Vec::new();

        for (k, v) in iter {
            let key = k.into();
            let val = v.into();

            match key.text() {
                Some(text) => {
                    let vals = text_fields.entry(text.into()).or_insert(Vec::new());
                    vals.push((key, val));
                }
                None => {
                    no_text_fields.push((key, val));
                }
            }
        }

        Self {
            text_fields,
            no_text_fields,
        }
    }
}

impl Struct for OwnedStruct {
    type FieldName = OwnedSymbolToken;
    type Element = OwnedElement;

    fn iter<'a>(
        &'a self,
    ) -> Box<dyn Iterator<Item = (&'a Self::FieldName, &'a Self::Element)> + 'a> {
        // convert &(k, v) -> (&k, &v)
        // flattens the fields_with_text_key HashMap and chains with fields_with_no_text_key
        // to return all fields with iterator
        Box::new(
            self.text_fields
                .values()
                .flat_map(|v| v)
                .into_iter()
                .chain(self.no_text_fields.iter())
                .map(|(k, v)| (k, v)),
        )
    }

    fn get<T: AsRef<str>>(&self, field_name: T) -> Option<&Self::Element> {
        self.text_fields
            .get(field_name.as_ref())?
            .last()
            .map(|(_s, v)| v)
    }

    fn get_all<'a, T: AsRef<str>>(
        &'a self,
        field_name: T,
    ) -> Box<dyn Iterator<Item = &'a Self::Element> + 'a> {
        Box::new(
            self.text_fields
                .get(field_name.as_ref())
                .into_iter()
                .flat_map(|v| v.iter())
                .map(|(_s, v)| v),
        )
    }
}

/// Variants for all owned version _values_ within an [`Element`].
#[derive(Debug, Clone)]
pub enum OwnedValue {
    Null(IonType),
    Integer(AnyInt),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(String),
    Symbol(OwnedSymbolToken),
    Boolean(bool),
    Blob(Vec<u8>),
    Clob(Vec<u8>),
    SExpression(OwnedSequence),
    List(OwnedSequence),
    Struct(OwnedStruct),
    // TODO fill this in with the rest of the value types...
}

/// An owned implementation of [`Element`]
#[derive(Debug, Clone)]
pub struct OwnedElement {
    annotations: Vec<OwnedSymbolToken>,
    value: OwnedValue,
}

impl OwnedElement {
    pub fn new(annotations: Vec<OwnedSymbolToken>, value: OwnedValue) -> Self {
        Self { annotations, value }
    }
}

impl From<OwnedValue> for OwnedElement {
    fn from(val: OwnedValue) -> Self {
        Self::new(vec![], val)
    }
}

impl Element for OwnedElement {
    type SymbolToken = OwnedSymbolToken;
    type Sequence = OwnedSequence;
    type Struct = OwnedStruct;

    fn ion_type(&self) -> IonType {
        use OwnedValue::*;

        match &self.value {
            Null(t) => *t,
            Integer(_) => IonType::Integer,
            Float(_) => IonType::Float,
            Decimal(_) => IonType::Decimal,
            Timestamp(_) => IonType::Timestamp,
            String(_) => IonType::String,
            Symbol(_) => IonType::Symbol,
            Boolean(_) => IonType::Boolean,
            Blob(_) => IonType::Blob,
            Clob(_) => IonType::Clob,
            SExpression(_) => IonType::SExpression,
            List(_) => IonType::List,
            Struct(_) => IonType::Struct,
        }
    }

    fn annotations<'a>(&'a self) -> Box<dyn Iterator<Item = &'a Self::SymbolToken> + 'a> {
        Box::new(self.annotations.iter())
    }

    fn is_null(&self) -> bool {
        match &self.value {
            OwnedValue::Null(_) => true,
            _ => false,
        }
    }

    fn as_any_int(&self) -> Option<&AnyInt> {
        match &self.value {
            OwnedValue::Integer(i) => Some(i),
            _ => None,
        }
    }

    fn as_float(&self) -> Option<f64> {
        match &self.value {
            OwnedValue::Float(f) => Some(*f),
            _ => None,
        }
    }

    fn as_decimal(&self) -> Option<&Decimal> {
        match &self.value {
            OwnedValue::Decimal(d) => Some(d),
            _ => None,
        }
    }

    fn as_timestamp(&self) -> Option<&Timestamp> {
        match &self.value {
            OwnedValue::Timestamp(t) => Some(t),
            _ => None,
        }
    }

    fn as_str(&self) -> Option<&str> {
        match &self.value {
            OwnedValue::String(text) => Some(text),
            OwnedValue::Symbol(sym) => sym.text(),
            _ => None,
        }
    }

    fn as_sym(&self) -> Option<&Self::SymbolToken> {
        match &self.value {
            OwnedValue::Symbol(sym) => Some(sym),
            _ => None,
        }
    }

    fn as_bool(&self) -> Option<bool> {
        match &self.value {
            OwnedValue::Boolean(b) => Some(*b),
            _ => None,
        }
    }

    fn as_blob(&self) -> Option<&[u8]> {
        match &self.value {
            OwnedValue::Blob(bytes) => Some(bytes),
            _ => None,
        }
    }

    fn as_clob(&self) -> Option<&[u8]> {
        match &self.value {
            OwnedValue::Clob(bytes) => Some(bytes),
            _ => None,
        }
    }

    fn as_sequence(&self) -> Option<&Self::Sequence> {
        match &self.value {
            OwnedValue::SExpression(seq) | OwnedValue::List(seq) => Some(seq),
            _ => None,
        }
    }

    fn as_struct(&self) -> Option<&Self::Struct> {
        match &self.value {
            OwnedValue::Struct(structure) => Some(structure),
            _ => None,
        }
    }
}

#[cfg(test)]
mod value_tests {
    use crate::result::IonResult;
    use crate::types::decimal::Decimal;
    use crate::types::timestamp::Timestamp;
    use crate::value::owned::{OwnedElement, OwnedSymbolToken, OwnedValue};
    use crate::value::{AnyInt, Element, IntAccess, SymbolToken};

    fn extract_text<T: SymbolToken>(tok: &T) -> &str {
        tok.text().unwrap().into()
    }

    fn create_element_from_value(value: OwnedValue) -> OwnedElement {
        let annotations = vec!["foo", "bar", "baz"];
        let owned_elem =
            OwnedElement::new(annotations.iter().map(|s| (*s).into()).collect(), value);
        owned_elem
    }

    #[test]
    fn test_as_any_int() -> IonResult<()> {
        let owned_elem = create_element_from_value(OwnedValue::Integer(AnyInt::I64(100)));
        let expected_elem = AnyInt::I64(100);

        assert_eq!(&expected_elem.as_i64(), &owned_elem.as_i64());
        assert_eq!(&expected_elem.as_big_int(), &owned_elem.as_big_int());
        Ok(())
    }

    #[test]
    fn test_as_float() -> IonResult<()> {
        let owned_elem = create_element_from_value(OwnedValue::Float(305e1));
        let expected_elem = Some(305e1);

        assert_eq!(&expected_elem, &owned_elem.as_float());
        Ok(())
    }

    #[test]
    fn test_as_decimal() -> IonResult<()> {
        let decimal_value1 = Decimal::new(8, 3);
        let decimal_value2 = Decimal::new(80, 2);

        let owned_elem = create_element_from_value(OwnedValue::Decimal(decimal_value1));
        let expected_elem = Some(&decimal_value2);

        assert_eq!(&expected_elem, &owned_elem.as_decimal());
        Ok(())
    }

    #[test]
    fn test_as_timestamp() -> IonResult<()> {
        let builder = Timestamp::with_ymd_hms_millis(2021, 2, 5, 16, 43, 51, 192);
        let timestamp_value1 = builder.clone().build_at_offset(5 * 60 * 60)?;
        let timestamp_value2 = builder.clone().build_at_offset(5 * 60 * 60)?;

        let owned_elem = create_element_from_value(OwnedValue::Timestamp(timestamp_value1));
        let expected_elem = Some(&timestamp_value2);

        assert_eq!(&expected_elem, &owned_elem.as_timestamp());
        Ok(())
    }

    #[test]
    fn test_as_str() -> IonResult<()> {
        let owned_elem = create_element_from_value(OwnedValue::String("hello".into()));
        let expected_elem = Some("hello");

        assert_eq!(&expected_elem, &owned_elem.as_str());
        Ok(())
    }

    #[test]
    fn test_as_sym() -> IonResult<()> {
        let owned_token: OwnedSymbolToken = "hello".into();
        let owned_elem = create_element_from_value(OwnedValue::Symbol(owned_token));
        let expected_elem: &OwnedSymbolToken = &("hello".into());

        assert_eq!(
            extract_text(expected_elem),
            extract_text(owned_elem.as_sym().unwrap().into())
        );
        Ok(())
    }

    #[test]
    fn test_as_bool() -> IonResult<()> {
        let owned_elem = create_element_from_value(OwnedValue::Boolean(false));
        let expected_elem = Some(false);

        assert_eq!(&expected_elem, &owned_elem.as_bool());
        Ok(())
    }

    #[test]
    fn test_as_blob() -> IonResult<()> {
        let owned_elem =
            create_element_from_value(OwnedValue::Blob(String::from("{{aGVsbG8h}}").into_bytes()));
        let expected_elem = Some("{{aGVsbG8h}}".as_bytes());

        assert_eq!(&expected_elem, &owned_elem.as_blob());
        Ok(())
    }

    #[test]
    fn test_as_clob() -> IonResult<()> {
        let owned_elem =
            create_element_from_value(OwnedValue::Clob(String::from("{{\"hello\"}}").into_bytes()));
        let expected_elem = Some("{{\"hello\"}}".as_bytes());

        assert_eq!(&expected_elem, &owned_elem.as_clob());
        Ok(())
    }
}
