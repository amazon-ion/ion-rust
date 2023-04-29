use crate::element::{Annotations, Element, IntoAnnotatedElement, Value};
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::lazy::binary::raw::raw_annotations_iterator::RawAnnotationsIterator;
use crate::lazy::value_ref::ValueRef;
use crate::result::decoding_error;
use crate::symbol_ref::AsSymbolRef;
use crate::{IonError, IonResult, IonType, RawSymbolTokenRef, SymbolRef, SymbolTable};

/// A value in a binary Ion stream whose header has been parsed but whose body (i.e. its data) has
/// not. A `LazyValue` is immutable; its data can be read any number of times.
///
/// ```
///# use ion_rs::IonResult;
///# fn main() -> IonResult<()> {
///
/// // Construct an Element and serialize it as binary Ion.
/// use ion_rs::element::Element;
/// use ion_rs::ion_list;
/// use ion_rs::lazy::binary::lazy_reader::LazyReader;
///
/// let element: Element = ion_list! [10, 20, 30].into();
/// let binary_ion = element.to_binary()?;
///
/// let mut lazy_reader = LazyReader::new(&binary_ion)?;
///
/// // Get the first value from the stream and confirm that it's a list.
/// let lazy_list = lazy_reader.next()?.expect("first value").read()?.expect_list()?;
///
/// // Visit the values in the list
/// let mut sum = 0;
/// for lazy_value in &lazy_list {
///     // Read each lazy value in the lazy list as an int (i64) and
///     // add it to the running total
///     sum += lazy_value?.read()?.expect_i64()?;
/// }
///
/// assert_eq!(sum, 60);
///
/// // Note that we can re-read any of the lazy values. Here we'll step into the list again and
/// // read the first child value.
/// let first_int = lazy_list.iter().next().unwrap()?.read()?.expect_i64()?;
/// assert_eq!(first_int, 10);
///
///# Ok(())
///# }
/// ```
#[derive(Clone)]
pub struct LazyValue<'top, 'data> {
    pub(crate) raw_value: LazyRawValue<'data>,
    pub(crate) symbol_table: &'top SymbolTable,
}

impl<'top, 'data> LazyValue<'top, 'data> {
    pub(crate) fn new(
        symbol_table: &'top SymbolTable,
        raw_value: LazyRawValue<'data>,
    ) -> LazyValue<'top, 'data> {
        LazyValue {
            raw_value,
            symbol_table,
        }
    }

    /// Returns the [`IonType`] of this value.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::element::Element;
    /// use ion_rs::IonType;
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    ///
    /// let element: Element = "hello".into();
    /// let binary_ion = element.to_binary()?;
    ///
    /// let mut lazy_reader = LazyReader::new(&binary_ion)?;
    ///
    /// // Get the first lazy value from the stream.
    /// let lazy_value = lazy_reader.next()?.expect("first value");
    ///
    /// // Check its type
    /// assert_eq!(lazy_value.ion_type(), IonType::String);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn ion_type(&self) -> IonType {
        self.raw_value.ion_type()
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
    /// use ion_rs::IonType;
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    ///
    /// let element: Element = "hello".with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.to_binary()?;
    ///
    /// let mut lazy_reader = LazyReader::new(&binary_ion)?;
    ///
    /// // Get the first lazy value from the stream.
    /// let lazy_value = lazy_reader.next()?.expect("first value");
    ///
    /// // Inspect its annotations.
    /// let mut annotations = lazy_value.annotations();
    /// assert_eq!(annotations.next().unwrap()?, "foo");
    /// assert_eq!(annotations.next().unwrap()?, "bar");
    /// assert_eq!(annotations.next().unwrap()?, "baz");
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn annotations(&self) -> AnnotationsIterator<'top, 'data> {
        AnnotationsIterator {
            raw_annotations: self.raw_value.annotations(),
            symbol_table: self.symbol_table,
            initial_offset: self
                .raw_value
                .encoded_value
                .annotations_offset()
                .unwrap_or(self.raw_value.encoded_value.header_offset),
        }
    }

    /// Reads the body of this value (that is: its data) and returns it as a [`ValueRef`].
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::element::{Element, IntoAnnotatedElement};
    /// use ion_rs::IonType;
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    /// use ion_rs::lazy::value_ref::ValueRef;
    ///
    /// let element: Element = "hello".with_annotations(["foo", "bar", "baz"]);
    /// let binary_ion = element.to_binary()?;
    ///
    /// let mut lazy_reader = LazyReader::new(&binary_ion)?;
    ///
    /// // Get the first lazy value from the stream.
    /// let lazy_value = lazy_reader.next()?.expect("first value");
    ///
    /// if let ValueRef::String(text) = lazy_value.read()? {
    ///     assert_eq!(text, "hello");
    /// } else {
    ///     panic!("Expected a string.");
    /// }
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn read(&self) -> IonResult<ValueRef<'top, 'data>>
    where
        'data: 'top,
    {
        use crate::lazy::binary::system::lazy_sequence::LazySequence;
        use crate::lazy::binary::system::lazy_struct::LazyStruct;
        use crate::lazy::raw_value_ref::RawValueRef::*;
        use crate::result::decoding_error_raw;

        let value_ref = match self.raw_value.read()? {
            Null(ion_type) => ValueRef::Null(ion_type),
            Bool(b) => ValueRef::Bool(b),
            Int(i) => ValueRef::Int(i),
            Float(f) => ValueRef::Float(f),
            Decimal(d) => ValueRef::Decimal(d),
            Timestamp(t) => ValueRef::Timestamp(t),
            String(s) => ValueRef::String(s),
            Symbol(s) => {
                let symbol = match s {
                    RawSymbolTokenRef::SymbolId(sid) => self
                        .symbol_table
                        .symbol_for(sid)
                        .ok_or_else(|| {
                            decoding_error_raw("found a symbol ID that was not in the symbol table")
                        })?
                        .into(),
                    RawSymbolTokenRef::Text(text) => text.into(),
                };
                ValueRef::Symbol(symbol)
            }
            Blob(b) => ValueRef::Blob(b),
            Clob(c) => ValueRef::Clob(c),
            SExp(s) => {
                let lazy_sequence = LazySequence {
                    raw_sequence: s,
                    symbol_table: self.symbol_table,
                };
                ValueRef::SExp(lazy_sequence)
            }
            List(l) => {
                let lazy_sequence = LazySequence {
                    raw_sequence: l,
                    symbol_table: self.symbol_table,
                };
                ValueRef::List(lazy_sequence)
            }
            Struct(s) => {
                let lazy_struct = LazyStruct {
                    raw_struct: s,
                    symbol_table: self.symbol_table,
                };
                ValueRef::Struct(lazy_struct)
            }
        };
        Ok(value_ref)
    }
}

impl<'top, 'data> TryFrom<LazyValue<'top, 'data>> for Element {
    type Error = IonError;

    fn try_from(value: LazyValue<'top, 'data>) -> Result<Self, Self::Error> {
        let annotations: Annotations = value.annotations().try_into()?;
        let value = Value::try_from(value.read()?)?;
        Ok(value.with_annotations(annotations))
    }
}

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
pub struct AnnotationsIterator<'top, 'data> {
    pub(crate) symbol_table: &'top SymbolTable,
    pub(crate) raw_annotations: RawAnnotationsIterator<'data>,
    pub(crate) initial_offset: usize,
}

impl<'top, 'data> AnnotationsIterator<'top, 'data>
where
    'data: 'top,
{
    /// Returns `Ok(true)` if this annotations iterator matches the provided sequence exactly, or
    /// `Ok(false)` if not. If a decoding error occurs while visiting and resolving each annotation,
    /// returns an `Err(IonError)`.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::element::{Element, IntoAnnotatedElement};
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    ///
    /// let element = Element::read_one("foo::bar::baz::99")?;
    /// let binary_ion = element.to_binary()?;
    /// let mut lazy_reader = LazyReader::new(&binary_ion)?;
    ///
    /// // Get the first value from the stream
    /// let lazy_value = lazy_reader.next()?.expect("first value");
    ///
    /// assert!(lazy_value.annotations().are(["foo", "bar", "baz"])?);
    ///
    /// assert!(!lazy_value.annotations().are(["foo", "bar", "baz", "quux"])?);
    /// assert!(!lazy_value.annotations().are(["baz", "bar", "foo"])?);
    /// assert!(!lazy_value.annotations().are(["foo", "bar"])?);
    /// assert!(!lazy_value.annotations().are(["foo"])?);
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn are<A: AsSymbolRef, I: IntoIterator<Item = A>>(
        mut self,
        annotations_to_match: I,
    ) -> IonResult<bool> {
        for to_match in annotations_to_match {
            match self.next() {
                Some(Ok(actual)) if actual == to_match => {}
                Some(Err(e)) => return Err(e),
                Some(_) | None => return Ok(false),
            }
        }
        // We've exhausted `annotations_to_match`, now make sure `self` is empty
        Ok(self.next().is_none())
    }

    /// Like [`Self::are`], but returns an [`IonError::DecodingError`] if the iterator's annotations
    /// don't match the provided sequence exactly.
    /// ```
    ///# use ion_rs::IonResult;
    ///# fn main() -> IonResult<()> {
    ///
    /// // Construct an Element and serialize it as binary Ion.
    /// use ion_rs::element::{Element, IntoAnnotatedElement};
    /// use ion_rs::lazy::binary::lazy_reader::LazyReader;
    ///
    /// let element = Element::read_one("foo::bar::baz::99")?;
    /// let binary_ion = element.to_binary()?;
    /// let mut lazy_reader = LazyReader::new(&binary_ion)?;
    ///
    /// // Get the first value from the stream
    /// let lazy_value = lazy_reader.next()?.expect("first value");
    ///
    /// assert!(lazy_value.annotations().expect(["foo", "bar", "baz"]).is_ok());
    ///
    /// assert!(lazy_value.annotations().expect(["foo", "bar", "baz", "quux"]).is_err());
    /// assert!(lazy_value.annotations().expect(["baz", "bar", "foo"]).is_err());
    /// assert!(lazy_value.annotations().expect(["foo", "bar"]).is_err());
    /// assert!(lazy_value.annotations().expect(["foo"]).is_err());
    ///
    ///# Ok(())
    ///# }
    /// ```
    pub fn expect<A: AsSymbolRef, I: IntoIterator<Item = A>>(
        self,
        annotations_to_match: I,
    ) -> IonResult<()> {
        if self.are(annotations_to_match)? {
            Ok(())
        } else {
            decoding_error("value annotations did not match expected sequence")
        }
    }
}

impl<'top, 'data> Iterator for AnnotationsIterator<'top, 'data>
where
    'data: 'top,
{
    type Item = IonResult<SymbolRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_annotation = self.raw_annotations.next()?;
        match raw_annotation {
            Ok(RawSymbolTokenRef::SymbolId(sid)) => match self.symbol_table.symbol_for(sid) {
                None => Some(decoding_error(
                    "found a symbol ID that was not in the symbol table",
                )),
                Some(symbol) => Some(Ok(symbol.into())),
            },
            Ok(RawSymbolTokenRef::Text(text)) => Some(Ok(SymbolRef::with_text(text))),
            Err(e) => Some(Err(e)),
        }
    }
}

impl<'top, 'data> TryFrom<AnnotationsIterator<'top, 'data>> for Annotations {
    type Error = IonError;

    fn try_from(iter: AnnotationsIterator<'top, 'data>) -> Result<Self, Self::Error> {
        let annotations = iter
            .map(|symbol_ref| match symbol_ref {
                Ok(symbol_ref) => Ok(symbol_ref.to_owned()),
                Err(e) => Err(e),
            })
            .collect::<IonResult<Vec<_>>>()?;
        Ok(Annotations::from(annotations))
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::lazy_reader::LazyReader;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::IonResult;

    #[test]
    fn annotations_are() -> IonResult<()> {
        let ion_data = to_binary_ion("foo::bar::baz::5")?;
        let mut reader = LazyReader::new(&ion_data)?;
        let first = reader.next()?.expect("first value");
        assert!(first.annotations().are(["foo", "bar", "baz"])?);

        // No similarity
        assert!(!first.annotations().are(["quux", "quuz"])?);

        // Prefix subset
        assert!(!first.annotations().are(["foo", "bar"])?);
        assert!(!first.annotations().are(["foo"])?);

        // Superset
        assert!(!first.annotations().are(["foo", "bar", "baz", "quux"])?);

        Ok(())
    }
}
