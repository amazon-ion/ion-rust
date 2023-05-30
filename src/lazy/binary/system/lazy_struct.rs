use crate::element::builders::StructBuilder;
use crate::element::{Annotations, Element, IntoAnnotatedElement, Struct};
use crate::lazy::binary::raw::lazy_raw_struct::{LazyRawStruct, RawStructIterator};
use crate::lazy::binary::system::lazy_value::AnnotationsIterator;
use crate::lazy::binary::system::lazy_value::LazyValue;
use crate::lazy::value_ref::ValueRef;
use crate::result::decoding_error_raw;
use crate::{IonError, IonResult, SymbolRef, SymbolTable};
use std::fmt;
use std::fmt::{Debug, Formatter};

/// An as-of-yet unread binary Ion struct. `LazyStruct` is immutable; its fields and annotations
/// can be read any number of times.
///
/// ```
///# use ion_rs::IonResult;
///# fn main() -> IonResult<()> {
/// use nom::AsBytes;
/// use ion_rs::{BinaryWriterBuilder, ion_struct, IonType};
/// use ion_rs::element::Element;
/// use ion_rs::lazy::binary::lazy_reader::LazyReader;
/// use ion_rs::lazy::value_ref::ValueRef;
///
/// let ion_data = r#"{foo: 1, bar: 2, foo: 3, bar: 4}"#;
/// let ion_bytes: Vec<u8> = Element::read_one(ion_data)?.to_binary()?;
/// let mut reader = LazyReader::new(&ion_bytes)?;
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
pub struct LazyStruct<'top, 'data> {
    pub(crate) raw_struct: LazyRawStruct<'data>,
    pub(crate) symbol_table: &'top SymbolTable,
}

// Best-effort debug formatting for LazyStruct. Any failures that occur during reading will result
// in the output being silently truncated.
impl<'top, 'data> Debug for LazyStruct<'top, 'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(f, "{{")?;
        for field in self {
            let field = field.map_err(|_| fmt::Error)?;
            let name = field.name().map_err(|_| fmt::Error)?;
            let lazy_value = field.value();
            let value = lazy_value.read().map_err(|_| fmt::Error)?;
            write!(f, "{}:{:?},", name.text().unwrap_or("$0"), value)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

impl<'top, 'data> LazyStruct<'top, 'data> {
    /// Returns an iterator over this struct's fields. See [`LazyField`].
    pub fn iter(&self) -> StructIterator<'top, 'data> {
        StructIterator {
            raw_struct_iter: self.raw_struct.iter(),
            symbol_table: self.symbol_table,
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
    /// use ion_rs::element::Element;
    /// use ion_rs::IonType;
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    /// use ion_rs::lazy::value_ref::ValueRef;
    ///
    /// let ion_data = r#"{foo: "hello", bar: quux::5, baz: null, bar: false}"#;
    /// let ion_bytes: Vec<u8> = Element::read_one(ion_data)?.to_binary()?;
    /// let mut reader = LazyReader::new(&ion_bytes)?;
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
    pub fn find(&self, name: &str) -> IonResult<Option<LazyValue<'top, 'data>>> {
        for field in self {
            let field = field?;
            if field.name()? == name {
                let value = field.value;
                return Ok(Some(value));
            }
        }
        Ok(None)
    }

    /// Like [`LazyStruct::find`], but returns an [`IonError::DecodingError`] if no field with the
    /// specified name is found.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::element::Element;
    /// use ion_rs::IonType;
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    /// use ion_rs::lazy::value_ref::ValueRef;
    ///
    /// let ion_data = r#"{foo: "hello", bar: quux::5, baz: null, bar: false}"#;
    /// let ion_bytes: Vec<u8> = Element::read_one(ion_data)?.to_binary()?;
    /// let mut reader = LazyReader::new(&ion_bytes)?;
    ///
    /// let lazy_struct = reader.expect_next()?.read()?.expect_struct()?;
    ///
    /// assert!(lazy_struct.find_expected("foo").is_ok());
    /// assert!(lazy_struct.find_expected("Ontario").is_err());
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn find_expected(&self, name: &str) -> IonResult<LazyValue<'top, 'data>> {
        self.find(name)?
            .ok_or_else(|| decoding_error_raw(format!("missing required field {}", name)))
    }

    /// Like [`LazyStruct::find`], but eagerly calls [`LazyValue::read`] on the first field with a
    /// matching name.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::element::Element;
    /// use ion_rs::IonType;
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    /// use ion_rs::lazy::value_ref::ValueRef;
    ///
    /// let ion_data = r#"{foo: "hello", bar: null.list, baz: 3, bar: 4}"#;
    /// let ion_bytes = Element::read_one(ion_data)?.to_binary()?;
    /// let mut reader = LazyReader::new(&ion_bytes)?;
    ///
    /// let lazy_struct = reader.expect_next()?.read()?.expect_struct()?;
    ///
    /// assert_eq!(lazy_struct.get("foo")?, Some(ValueRef::String("hello")));
    /// assert_eq!(lazy_struct.get("baz")?, Some(ValueRef::Int(3.into())));
    /// assert_eq!(lazy_struct.get("bar")?, Some(ValueRef::Null(IonType::List)));
    ///# Ok(())
    ///# }
    /// ```
    pub fn get(&self, name: &str) -> IonResult<Option<ValueRef<'top, 'data>>>
    where
        'data: 'top,
    {
        self.find(name)?.map(|f| f.read()).transpose()
    }

    /// Like [`LazyStruct::get`], but returns an [`IonError::DecodingError`] if no field with the
    /// specified name is found.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    /// use ion_rs::element::Element;
    /// use ion_rs::IonType;
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    /// use ion_rs::lazy::value_ref::ValueRef;
    ///
    /// let ion_data = r#"{foo: "hello", bar: null.list, baz: 3, bar: 4}"#;
    /// let ion_bytes = Element::read_one(ion_data)?.to_binary()?;
    /// let mut reader = LazyReader::new(&ion_bytes)?;
    ///
    /// let lazy_struct = reader.expect_next()?.read()?.expect_struct()?;
    ///
    /// assert_eq!(lazy_struct.get_expected("foo")?, ValueRef::String("hello"));
    /// assert!(dbg!(lazy_struct.get_expected("Ontario")).is_err());
    ///# Ok(())
    ///# }
    /// ```
    pub fn get_expected(&self, name: &str) -> IonResult<ValueRef<'top, 'data>>
    where
        'data: 'top,
    {
        self.get(name)?
            .ok_or_else(move || decoding_error_raw(format!("missing required field {}", name)))
    }

    /// Returns an iterator over the annotations on this value. If this value has no annotations,
    /// the resulting iterator will be empty.
    ///
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::element::{Element, IntoAnnotatedElement};
    /// use ion_rs::{ion_struct, IonType};
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    ///
    /// let element: Element = ion_struct! {"foo": 1, "bar": 2}.with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.to_binary()?;
    ///
    /// let mut lazy_reader = LazyReader::new(&binary_ion)?;
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
    pub fn annotations(&self) -> AnnotationsIterator<'top, 'data> {
        AnnotationsIterator {
            raw_annotations: self.raw_struct.value.annotations(),
            symbol_table: self.symbol_table,
            initial_offset: self
                .raw_struct
                .value
                .encoded_value
                .annotations_offset()
                .unwrap_or(self.raw_struct.value.encoded_value.header_offset),
        }
    }
}

/// A single field within a [`LazyStruct`].
pub struct LazyField<'top, 'data> {
    pub(crate) value: LazyValue<'top, 'data>,
}

impl<'top, 'data> Debug for LazyField<'top, 'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {:?}",
            self.name().map_err(|_| fmt::Error)?.text().unwrap_or("$0"),
            self.value().read().map_err(|_| fmt::Error)?,
        )
    }
}

impl<'top, 'data> LazyField<'top, 'data> {
    /// Returns a symbol representing the name of this field.
    pub fn name(&self) -> IonResult<SymbolRef<'top>> {
        // This is a LazyField (not a LazyValue), so the field name is defined.
        debug_assert!(self.value.raw_value.field_name().is_some());
        let field_sid = self.value.raw_value.field_name().unwrap();
        self.value
            .symbol_table
            .symbol_for(field_sid)
            .map(|symbol| symbol.into())
            .ok_or_else(|| decoding_error_raw("found a symbol ID that was not in the symbol table"))
    }

    /// Returns a lazy value representing the value of this field. To access the value's data,
    /// see [`LazyValue::read`].
    pub fn value(&self) -> &LazyValue<'top, 'data> {
        &self.value
    }
}

pub struct StructIterator<'top, 'data> {
    pub(crate) raw_struct_iter: RawStructIterator<'data>,
    pub(crate) symbol_table: &'top SymbolTable,
}

impl<'top, 'data> Iterator for StructIterator<'top, 'data> {
    type Item = IonResult<LazyField<'top, 'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        StructIterator::next_field(self).transpose()
    }
}

impl<'top, 'data> StructIterator<'top, 'data> {
    pub fn next_field(&mut self) -> IonResult<Option<LazyField<'top, 'data>>> {
        let raw_field = match self.raw_struct_iter.next() {
            Some(raw_field) => raw_field?,
            None => return Ok(None),
        };

        let lazy_value = LazyValue {
            raw_value: raw_field.into_value(),
            symbol_table: self.symbol_table,
        };
        let lazy_field = LazyField { value: lazy_value };
        Ok(Some(lazy_field))
    }
}

impl<'top, 'data> TryFrom<LazyStruct<'top, 'data>> for Struct {
    type Error = IonError;

    fn try_from(lazy_struct: LazyStruct<'top, 'data>) -> Result<Self, Self::Error> {
        let mut builder = StructBuilder::new();
        for field in &lazy_struct {
            let field = field?;
            builder = builder.with_field(field.name()?, Element::try_from(field.value().clone())?);
        }
        Ok(builder.build())
    }
}

impl<'top, 'data> TryFrom<LazyStruct<'top, 'data>> for Element {
    type Error = IonError;

    fn try_from(lazy_struct: LazyStruct<'top, 'data>) -> Result<Self, Self::Error> {
        let annotations: Annotations = lazy_struct.annotations().try_into()?;
        let struct_: Struct = lazy_struct.try_into()?;
        Ok(struct_.with_annotations(annotations))
    }
}

impl<'a, 'top, 'data> IntoIterator for &'a LazyStruct<'top, 'data> {
    type Item = IonResult<LazyField<'top, 'data>>;
    type IntoIter = StructIterator<'top, 'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lazy::binary::lazy_reader::LazyReader;
    use crate::lazy::binary::test_utilities::to_binary_ion;

    #[test]
    fn find() -> IonResult<()> {
        let ion_data = to_binary_ion("{foo: 1, bar: 2, baz: 3}")?;
        let mut reader = LazyReader::new(&ion_data)?;
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
        let mut reader = LazyReader::new(&ion_data)?;
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
        let mut reader = LazyReader::new(&ion_data)?;
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
        let mut reader = LazyReader::new(&ion_data)?;
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
        let mut reader = LazyReader::new(&ion_data)?;
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
        let mut reader = LazyReader::new(&binary_ion)?;
        let struct_ = reader.expect_next()?.read()?.expect_struct()?;
        let result: IonResult<Element> = struct_.try_into();
        assert!(result.is_ok());
        assert_eq!(result?, Element::read_one(ion_text)?);
        Ok(())
    }

    #[test]
    fn try_into_element_error() -> IonResult<()> {
        let mut binary_ion = to_binary_ion("foo::baz::baz::{a: 1, b: 2, c: 3}")?;
        let _oops_i_lost_a_byte = binary_ion.pop().unwrap();
        let mut reader = LazyReader::new(&binary_ion)?;
        let struct_ = reader.expect_next()?.read()?.expect_struct()?;
        // Conversion will fail because the reader will encounter an unexpected end of input
        let result: IonResult<Element> = struct_.try_into();
        assert!(result.is_err());
        Ok(())
    }
}
