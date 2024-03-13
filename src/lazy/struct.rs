use std::fmt;
use std::fmt::{Debug, Formatter};

use crate::element::builders::StructBuilder;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::encoding::BinaryEncoding_1_0;
use crate::lazy::expanded::r#struct::{
    ExpandedStructIterator, LazyExpandedField, LazyExpandedStruct,
};
use crate::lazy::value::{AnnotationsIterator, LazyValue};
use crate::lazy::value_ref::ValueRef;
use crate::result::IonFailure;
use crate::{
    Annotations, Element, IntoAnnotatedElement, IonError, IonResult, RawSymbolTokenRef, Struct,
    SymbolRef,
};

/// An as-of-yet unread binary Ion struct. `LazyStruct` is immutable; its fields and annotations
/// can be read any number of times.
///
/// ```
///# use ion_rs::IonResult;
///# fn main() -> IonResult<()> {
/// use ion_rs::Element;
/// use ion_rs::lazy::reader::LazyBinaryReader;;
///
/// let ion_data = r#"{foo: 1, bar: 2, foo: 3, bar: 4}"#;
/// let ion_bytes: Vec<u8> = Element::read_one(ion_data)?.to_binary()?;
/// let mut reader = LazyBinaryReader::new(ion_bytes)?;
///
/// // Advance the reader to the first value and confirm it's a struct
/// let lazy_struct = reader.expect_next()?.read()?.expect_struct()?;
///
/// // Add up the integer values of all the fields named 'foo'
/// let mut foo_sum = 0i64;
/// for field in &lazy_struct {
///     let field = field?;
///     if field.name()? == "foo" {
///         foo_sum += field.value().read()?.expect_i64()?;
///     }
/// }
///
/// assert_eq!(foo_sum, 4);
///# Ok(())
///# }
/// ```
#[derive(Clone)]
pub struct LazyStruct<'top, D: LazyDecoder> {
    pub(crate) expanded_struct: LazyExpandedStruct<'top, D>,
}

pub type LazyBinaryStruct<'top> = LazyStruct<'top, BinaryEncoding_1_0>;

// Best-effort debug formatting for LazyStruct. Any failures that occur during reading will result
// in the output being silently truncated.
impl<'top, D: LazyDecoder> Debug for LazyStruct<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for field in self {
            let field = field?;
            let name = field.name()?;
            let lazy_value = field.value();
            let value = lazy_value.read()?;
            write!(f, "{}:{:?},", name.text().unwrap_or("$0"), value)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<'top, D: LazyDecoder> LazyStruct<'top, D> {
    /// Returns an iterator over this struct's fields. See [`LazyField`].
    pub fn iter(&self) -> StructIterator<'top, D> {
        StructIterator {
            expanded_struct_iter: self.expanded_struct.iter(),
        }
    }

    /// Returns the value of the first field with the specified name, if any. The returned value is
    /// a [`LazyValue`]. Its type and annotations can be inspected without calling [LazyValue::read].
    ///
    /// Because the `LazyStruct` does not store materialized values or index field names, it must
    /// seek over its fields to find one with the requested name, giving this method linear time
    /// complexity.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::Element;
    /// use ion_rs::lazy::reader::LazyBinaryReader;;
    /// use ion_rs::lazy::value_ref::ValueRef;
    ///
    /// let ion_data = r#"{foo: "hello", bar: quux::5, baz: null, bar: false}"#;
    /// let ion_bytes: Vec<u8> = Element::read_one(ion_data)?.to_binary()?;
    /// let mut reader = LazyBinaryReader::new(ion_bytes)?;
    ///
    /// let lazy_struct = reader.expect_next()?.read()?.expect_struct()?;
    ///
    /// assert!(lazy_struct.find("foo")?.is_some());
    /// assert!(lazy_struct.find("Ontario")?.is_none());
    ///
    /// // There are two 'bar' fields; `find` will return the value of the first.
    /// let value = lazy_struct.find("bar")?.unwrap();
    ///
    /// assert!(value.annotations().next().unwrap()? == "quux");
    /// assert_eq!(value.read()?, ValueRef::Int(5.into()));
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn find(&self, name: &str) -> IonResult<Option<LazyValue<'top, D>>> {
        let Some(expanded_value) = self.expanded_struct.find(name)? else {
            return Ok(None);
        };
        let value = LazyValue::new(expanded_value);
        Ok(Some(value))
    }

    /// Like [`LazyStruct::find`], but returns an [`IonError::Decoding`] if no field with the
    /// specified name is found.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::Element;
    /// use ion_rs::lazy::reader::LazyBinaryReader;;
    ///
    /// let ion_data = r#"{foo: "hello", bar: quux::5, baz: null, bar: false}"#;
    /// let ion_bytes: Vec<u8> = Element::read_one(ion_data)?.to_binary()?;
    /// let mut reader = LazyBinaryReader::new(ion_bytes)?;
    ///
    /// let lazy_struct = reader.expect_next()?.read()?.expect_struct()?;
    ///
    /// assert!(lazy_struct.find_expected("foo").is_ok());
    /// assert!(lazy_struct.find_expected("Ontario").is_err());
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn find_expected(&self, name: &str) -> IonResult<LazyValue<'top, D>> {
        self.find(name)?
            .ok_or_else(|| IonError::decoding_error(format!("missing required field {}", name)))
    }

    /// Like [`LazyStruct::find`], but eagerly calls [`LazyValue::read`] on the first field with a
    /// matching name.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::{Element, IonType};
    /// use ion_rs::lazy::reader::LazyBinaryReader;
    /// use ion_rs::lazy::value_ref::ValueRef;
    ///
    /// let ion_data = r#"{foo: "hello", bar: null.list, baz: 3, bar: 4}"#;
    /// let ion_bytes = Element::read_one(ion_data)?.to_binary()?;
    /// let mut reader = LazyBinaryReader::new(ion_bytes)?;
    ///
    /// let lazy_struct = reader.expect_next()?.read()?.expect_struct()?;
    ///
    /// assert_eq!(lazy_struct.get("foo")?, Some(ValueRef::String("hello".into())));
    /// assert_eq!(lazy_struct.get("baz")?, Some(ValueRef::Int(3.into())));
    /// assert_eq!(lazy_struct.get("bar")?, Some(ValueRef::Null(IonType::List)));
    ///# Ok(())
    ///# }
    /// ```
    pub fn get(&self, name: &str) -> IonResult<Option<ValueRef<'top, D>>> {
        self.find(name)?.map(|f| f.read()).transpose()
    }

    /// Like [`LazyStruct::get`], but returns an [`IonError::Decoding`] if no field with the
    /// specified name is found.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::Element;
    /// use ion_rs::lazy::reader::LazyBinaryReader;
    /// use ion_rs::lazy::value_ref::ValueRef;
    ///
    /// let ion_data = r#"{foo: "hello", bar: null.list, baz: 3, bar: 4}"#;
    /// let ion_bytes = Element::read_one(ion_data)?.to_binary()?;
    /// let mut reader = LazyBinaryReader::new(ion_bytes)?;
    ///
    /// let lazy_struct = reader.expect_next()?.read()?.expect_struct()?;
    ///
    /// assert_eq!(lazy_struct.get_expected("foo")?, ValueRef::String("hello".into()));
    /// assert!(lazy_struct.get_expected("Ontario").is_err());
    ///# Ok(())
    ///# }
    /// ```
    pub fn get_expected(&self, name: &str) -> IonResult<ValueRef<'top, D>> {
        self.get(name)?.ok_or_else(move || {
            IonError::decoding_error(format!("missing required field {}", name))
        })
    }

    /// Returns an iterator over the annotations on this value. If this value has no annotations,
    /// the resulting iterator will be empty.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::{Element, IntoAnnotatedElement};
    /// use ion_rs::ion_struct;
    /// use ion_rs::lazy::reader::LazyBinaryReader;;
    ///
    /// let element: Element = ion_struct! {"foo": 1, "bar": 2}.with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.to_binary()?;
    ///
    /// let mut lazy_reader = LazyBinaryReader::new(binary_ion)?;
    ///
    /// // Get the first lazy value from the stream.
    /// let lazy_struct = lazy_reader.expect_next()?.read()?.expect_struct()?;
    ///
    /// // Inspect its annotations.
    /// let mut annotations = lazy_struct.annotations();
    /// assert_eq!(annotations.next().unwrap()?, "foo");
    /// assert_eq!(annotations.next().unwrap()?, "bar");
    /// assert_eq!(annotations.next().unwrap()?, "baz");
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn annotations(&self) -> AnnotationsIterator<'top, D> {
        AnnotationsIterator {
            expanded_annotations: self.expanded_struct.annotations(),
            symbol_table: self.expanded_struct.context.symbol_table,
        }
    }
}

/// A single field within a [`LazyStruct`].
pub struct LazyField<'top, D: LazyDecoder> {
    pub(crate) expanded_field: LazyExpandedField<'top, D>,
}

impl<'top, D: LazyDecoder> Debug for LazyField<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {:?}",
            self.name()?.text().unwrap_or("$0"),
            self.value().read()?,
        )
    }
}

impl<'top, D: LazyDecoder> LazyField<'top, D> {
    /// Returns a symbol representing the name of this field.
    pub fn name(&self) -> IonResult<SymbolRef<'top>> {
        let field_name = self.expanded_field.raw_name();
        let field_id = match field_name {
            RawSymbolTokenRef::SymbolId(sid) => sid,
            RawSymbolTokenRef::Text(text) => return Ok(SymbolRef::with_text(text)),
        };
        self.expanded_field
            .value
            .context
            .symbol_table
            .symbol_for(field_id)
            .map(|symbol| symbol.into())
            .ok_or_else(|| {
                IonError::decoding_error("found a symbol ID that was not in the symbol table")
            })
    }

    /// Returns a lazy value representing the value of this field. To access the value's data,
    /// see [`LazyValue::read`].
    pub fn value(&self) -> LazyValue<'top, D> {
        LazyValue {
            expanded_value: *self.expanded_field.value(),
        }
    }
}

pub struct StructIterator<'top, D: LazyDecoder> {
    pub(crate) expanded_struct_iter: ExpandedStructIterator<'top, D>,
}

impl<'top, D: LazyDecoder> Iterator for StructIterator<'top, D> {
    type Item = IonResult<LazyField<'top, D>>;

    fn next(&mut self) -> Option<Self::Item> {
        StructIterator::next_field(self).transpose()
    }
}

impl<'top, D: LazyDecoder> StructIterator<'top, D> {
    pub fn next_field(&mut self) -> IonResult<Option<LazyField<'top, D>>> {
        let expanded_field = match self.expanded_struct_iter.next() {
            Some(expanded_field) => expanded_field?,
            None => return Ok(None),
        };

        let lazy_field = LazyField { expanded_field };
        Ok(Some(lazy_field))
    }
}

impl<'top, D: LazyDecoder> TryFrom<LazyStruct<'top, D>> for Struct {
    type Error = IonError;

    fn try_from(lazy_struct: LazyStruct<'top, D>) -> Result<Self, Self::Error> {
        let mut builder = StructBuilder::new();
        for field in &lazy_struct {
            let field = field?;
            builder = builder.with_field(field.name()?, Element::try_from(field.value())?);
        }
        Ok(builder.build())
    }
}

impl<'top, D: LazyDecoder> TryFrom<LazyStruct<'top, D>> for Element {
    type Error = IonError;

    fn try_from(lazy_struct: LazyStruct<'top, D>) -> Result<Self, Self::Error> {
        let annotations: Annotations = lazy_struct.annotations().try_into()?;
        let struct_: Struct = lazy_struct.try_into()?;
        Ok(struct_.with_annotations(annotations))
    }
}

impl<'a, 'top, 'data: 'top, D: LazyDecoder> IntoIterator for &'a LazyStruct<'top, D> {
    type Item = IonResult<LazyField<'top, D>>;
    type IntoIter = StructIterator<'top, D>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::reader::LazyBinaryReader;

    use super::*;

    #[test]
    fn find() -> IonResult<()> {
        let ion_data = to_binary_ion("{foo: 1, bar: 2, baz: 3}")?;
        let mut reader = LazyBinaryReader::new(ion_data)?;
        let struct_ = reader.expect_next()?.read()?.expect_struct()?;
        let baz = struct_.find("baz")?;
        assert!(baz.is_some());
        assert_eq!(baz.unwrap().read()?, ValueRef::Int(3.into()));
        let quux = struct_.get("quux")?;
        assert_eq!(quux, None);
        Ok(())
    }

    #[test]
    fn find_expected() -> IonResult<()> {
        let ion_data = to_binary_ion("{foo: 1, bar: 2, baz: 3}")?;
        let mut reader = LazyBinaryReader::new(ion_data)?;
        let struct_ = reader.expect_next()?.read()?.expect_struct()?;
        let baz = struct_.find_expected("baz");
        assert!(baz.is_ok());
        assert_eq!(baz.unwrap().read()?, ValueRef::Int(3.into()));
        let quux = struct_.find_expected("quux");
        assert!(quux.is_err());
        Ok(())
    }

    #[test]
    fn get() -> IonResult<()> {
        let ion_data = to_binary_ion("{foo: 1, bar: 2, baz: 3}")?;
        let mut reader = LazyBinaryReader::new(ion_data)?;
        let struct_ = reader.expect_next()?.read()?.expect_struct()?;
        let baz = struct_.get("baz")?;
        assert_eq!(baz, Some(ValueRef::Int(3.into())));
        let quux = struct_.get("quux")?;
        assert_eq!(quux, None);
        Ok(())
    }

    #[test]
    fn get_expected() -> IonResult<()> {
        let ion_data = to_binary_ion("{foo: 1, bar: 2, baz: 3}")?;
        let mut reader = LazyBinaryReader::new(ion_data)?;
        let struct_ = reader.expect_next()?.read()?.expect_struct()?;
        let baz = struct_.get_expected("baz");
        assert_eq!(baz, Ok(ValueRef::Int(3.into())));
        let quux = struct_.get_expected("quux");
        assert!(quux.is_err());
        Ok(())
    }

    #[test]
    fn annotations() -> IonResult<()> {
        let ion_data = to_binary_ion("a::b::c::{foo: 1, bar: 2, baz: quux::quuz::3}")?;
        let mut reader = LazyBinaryReader::new(ion_data)?;
        let struct_ = reader.expect_next()?.read()?.expect_struct()?;
        assert!(struct_.annotations().are(["a", "b", "c"])?);
        let baz = struct_.find_expected("baz")?;
        assert!(baz.annotations().are(["quux", "quuz"])?);
        Ok(())
    }

    #[test]
    fn try_into_element() -> IonResult<()> {
        let ion_text = "foo::baz::baz::{a: 1, b: 2, c: 3}";
        let binary_ion = to_binary_ion(ion_text)?;
        let mut reader = LazyBinaryReader::new(binary_ion)?;
        let struct_ = reader.expect_next()?.read()?.expect_struct()?;
        let result: IonResult<Element> = struct_.try_into();
        assert!(result.is_ok());
        assert_eq!(result?, Element::read_one(ion_text)?);
        Ok(())
    }
}
