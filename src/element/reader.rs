// Copyright Amazon.com, Inc. or its affiliates.

//! Provides APIs to read Ion data into [Element] from different sources such
//! as slices or files.

use crate::element::{Annotations, Element, Sequence, Struct, Value};
use crate::ion_reader::IonReader;
use crate::reader::StreamItem;
use crate::result::{IonFailure, IonResult};
use crate::Symbol;

/// Reads Ion data into [`Element`] instances.
///
/// This trait is automatically implemented by all Ion reader implementations that operate
/// at the highest layer of abstraction, sometimes called the 'user' layer.
pub trait ElementReader {
    type ElementIterator<'a>: Iterator<Item = IonResult<Element>>
    where
        Self: 'a;

    /// Recursively materializes the next Ion value, returning it as an `Ok(Element)`.
    /// If there is no more data left to be read, returns `Ok(None)`.
    /// If an error occurs while the data is being read, returns `Err(IonError)`.
    fn read_next_element(&mut self) -> IonResult<Option<Element>>;

    /// Returns an iterator over the [Element]s in the data stream.
    fn elements(&mut self) -> Self::ElementIterator<'_>;

    fn into_elements(self) -> OwnedElementIterator<Self>
    where
        Self: Sized,
    {
        OwnedElementIterator { reader: self }
    }

    /// Like [Self::read_next_element], this method reads the next Ion value in the input stream,
    /// returning it as an `Ok(Element)`. However, it also requires that the stream contain exactly
    /// one value.
    ///
    /// If the stream's data is valid and it contains one value, returns `Ok(Element)`.
    /// If the stream's data is invalid or the stream does not contain exactly one value,
    /// returns `Err(IonError)`.
    fn read_one_element(&mut self) -> IonResult<Element> {
        let mut iter = self.elements();
        let only_element = match iter.next() {
            Some(Ok(element)) => element,
            Some(Err(e)) => return Err(e),
            None => return IonResult::decoding_error("expected 1 value, found 0"),
        };
        // See if there is a second, unexpected value.
        match iter.next() {
            Some(Ok(element)) => {
                return IonResult::decoding_error(format!(
                    "found more than one value; second value: {}",
                    element
                ))
            }
            Some(Err(e)) => {
                return IonResult::decoding_error(format!("error after expected value: {}", e))
            }
            None => {}
        };
        Ok(only_element)
    }

    /// Reads all of the values in the input stream, materializing each into an [Element] and
    /// returning the complete sequence as a `Vec<Element>`.
    ///
    /// If an error occurs while reading, returns `Err(IonError)`.
    fn read_all_elements(&mut self) -> IonResult<Vec<Element>> {
        self.elements().collect()
    }
}

impl<R> ElementReader for R
where
    R: IonReader<Item = StreamItem, Symbol = Symbol> + ?Sized,
{
    type ElementIterator<'a> = ElementIterator<'a, R> where R: 'a;

    fn read_next_element(&mut self) -> IonResult<Option<Element>> {
        ElementLoader::for_reader(self).materialize_next()
    }

    fn elements(&mut self) -> ElementIterator<R> {
        ElementIterator { reader: self }
    }
}

/// Holds a reference to a given [ElementReader] implementation and yields one [Element] at a time
/// until the stream is exhausted or invalid data is encountered.
pub struct ElementIterator<'a, R: ElementReader + ?Sized> {
    reader: &'a mut R,
}

impl<'a, R: ElementReader + ?Sized> Iterator for ElementIterator<'a, R> {
    type Item = IonResult<Element>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.reader.read_next_element() {
            Ok(Some(element)) => Some(Ok(element)),
            Ok(None) => None,
            Err(error) => Some(Err(error)),
        }
    }
}

pub struct OwnedElementIterator<R: ElementReader> {
    reader: R,
}

impl<R: ElementReader> Iterator for OwnedElementIterator<R> {
    type Item = IonResult<Element>;

    fn next(&mut self) -> Option<Self::Item> {
        self.reader.read_next_element().transpose()
    }
}

/// Helper type; wraps an [ElementReader] and recursively materializes the next value in the
/// reader's input, reporting any errors that might occur along the way.
struct ElementLoader<'a, R: ?Sized> {
    reader: &'a mut R,
}

impl<'a, R: IonReader<Item = StreamItem, Symbol = Symbol> + ?Sized> ElementLoader<'a, R> {
    pub(crate) fn for_reader(reader: &mut R) -> ElementLoader<R> {
        ElementLoader { reader }
    }

    /// Advances the reader to the next value in the stream and uses [Self::materialize_current]
    /// to materialize it.
    pub(crate) fn materialize_next(&mut self) -> IonResult<Option<Element>> {
        // Advance the reader to the next value
        let _ = self.reader.next()?;
        self.materialize_current()
    }

    /// Recursively materialize the reader's current Ion value and returns it as `Ok(Some(value))`.
    /// If there are no more values at this level, returns `Ok(None)`.
    /// If an error occurs while materializing the value, returns an `Err`.
    /// Calling this method advances the reader and consumes the current value.
    fn materialize_current(&mut self) -> IonResult<Option<Element>> {
        // Collect this item's annotations into a Vec. We have to do this before materializing the
        // value itself because materializing a collection requires advancing the reader further.
        let mut annotations = Vec::new();
        // Current API limitations require `self.reader.annotations()` to heap allocate its
        // iterator even if there aren't annotations. `self.reader.has_annotations()` is trivial
        // and allows us to skip the heap allocation in the common case.
        if self.reader.has_annotations() {
            for annotation in self.reader.annotations() {
                annotations.push(annotation?);
            }
        }

        let value = match self.reader.current() {
            // No more values at this level of the stream
            StreamItem::Nothing => return Ok(None),
            // This is a typed null
            StreamItem::Null(ion_type) => Value::Null(ion_type),
            // This is a non-null value
            StreamItem::Value(ion_type) => {
                use crate::IonType::*;
                match ion_type {
                    Null => unreachable!("non-null value had IonType::Null"),
                    Bool => Value::Bool(self.reader.read_bool()?),
                    Int => Value::Int(self.reader.read_int()?),
                    Float => Value::Float(self.reader.read_f64()?),
                    Decimal => Value::Decimal(self.reader.read_decimal()?),
                    Timestamp => Value::Timestamp(self.reader.read_timestamp()?),
                    Symbol => Value::Symbol(self.reader.read_symbol()?),
                    String => Value::String(self.reader.read_string()?),
                    Clob => Value::Clob(self.reader.read_clob()?.into()),
                    Blob => Value::Blob(self.reader.read_blob()?.into()),
                    // It's a collection; recursively materialize all of this value's children
                    List => Value::List(self.materialize_sequence()?),
                    SExp => Value::SExp(self.materialize_sequence()?),
                    Struct => Value::Struct(self.materialize_struct()?),
                }
            }
        };
        Ok(Some(Element::new(Annotations::new(annotations), value)))
    }

    /// Steps into the current sequence and materializes each of its children to construct
    /// an [`Vec<Element>`]. When all of the the children have been materialized, steps out.
    /// The reader MUST be positioned over a list or s-expression when this is called.
    fn materialize_sequence(&mut self) -> IonResult<Sequence> {
        let mut child_elements = Vec::new();
        self.reader.step_in()?;
        while let Some(element) = self.materialize_next()? {
            child_elements.push(element);
        }
        self.reader.step_out()?;
        Ok(child_elements.into())
    }

    /// Steps into the current struct and materializes each of its fields to construct
    /// an [`Struct`]. When all of the the fields have been materialized, steps out.
    /// The reader MUST be positioned over a struct when this is called.
    fn materialize_struct(&mut self) -> IonResult<Struct> {
        let mut child_elements = Vec::new();
        self.reader.step_in()?;
        while let StreamItem::Value(_) | StreamItem::Null(_) = self.reader.next()? {
            let field_name = self.reader.field_name()?;
            let value = self
                .materialize_current()?
                .expect("materialize_current() returned None for user data");
            child_elements.push((field_name, value));
        }
        self.reader.step_out()?;
        Ok(Struct::from_iter(child_elements.into_iter()))
    }
}

#[cfg(test)]
mod reader_tests {
    use super::*;
    use crate::element::Value::*;
    use crate::element::{Element, IntoAnnotatedElement};
    use crate::ion_data::IonEq;
    use crate::types::{Int, Timestamp as TS};
    use crate::{ion_list, ion_seq, ion_sexp, ion_struct};
    use crate::{IonType, Symbol};
    use bigdecimal::BigDecimal;
    use num_bigint::BigInt;
    use rstest::*;
    use std::str::FromStr;

    #[rstest]
    #[case::nulls(
        br#"
           null
           null.bool
           null.int
           null.float
           null.decimal
           null.timestamp
           null.symbol
           null.string
           null.clob
           null.blob
           null.list
           null.sexp
           null.struct
        "#,
        vec![
            Null(IonType::Null),
            Null(IonType::Bool),
            Null(IonType::Int),
            Null(IonType::Float),
            Null(IonType::Decimal),
            Null(IonType::Timestamp),
            Null(IonType::Symbol),
            Null(IonType::String),
            Null(IonType::Clob),
            Null(IonType::Blob),
            Null(IonType::List),
            Null(IonType::SExp),
            Null(IonType::Struct),
        ].into_iter().map(|v| v.into()).collect(),
    )]
    #[case::ints(
        br#"
            0
            -65536 65535
            -4294967296 4294967295
            -9007199254740992 9007199254740991
            -18446744073709551616 18446744073709551615
            -79228162514264337593543950336 79228162514264337593543950335
        "#,
        vec![
            0i64,
            -65536, 65535,
            -4294967296, 4294967295,
            -9007199254740992, 9007199254740991,
        ].into_iter().map(Int::from).chain(
        vec![
                "-18446744073709551616", "18446744073709551615",
                "-79228162514264337593543950336", "79228162514264337593543950335",
            ].into_iter()
            .map(|v| Int::from(BigInt::parse_bytes(v.as_bytes(), 10).unwrap()))
        ).map(|ai| Int(ai).into()).collect(),
    )]
    #[case::int64_threshold_as_big_int(
        &[0xE0, 0x01, 0x00, 0xEA, 0x28, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        vec![
            "18446744073709551615",
        ].into_iter()
        .map(|v| Int::from(BigInt::parse_bytes(v.as_bytes(), 10).unwrap())).map(|ai| Int(ai).into()).collect(),
    )]
    #[case::int64_threshold_as_int64(
        &[0xE0, 0x01, 0x00, 0xEA, 0x38, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        vec![
            "-9223372036854775808",
        ].into_iter()
        .map(|v| Int::from(BigInt::parse_bytes(v.as_bytes(), 10).unwrap())).map(|ai| Int(ai).into()).collect(),
    )]
    #[case::floats(
        br#"
           1e0 +inf -inf nan
        "#,
        vec![
            1f64, f64::INFINITY, f64::NEG_INFINITY, f64::NAN
        ].into_iter().map(|v| Float(v).into()).collect(),
    )]
    #[case::decimals(
        br#"
            1d0 100d10 -2.1234567d-100
        "#,
        vec![
            "1e0", "100e10", "-2.1234567e-100",
        ].into_iter().map(|s| Decimal(BigDecimal::from_str(s).unwrap().into()).into()).collect(),
    )]
    #[case::timestamps(
        br#"
            2020T
            2020-02-27T
            2020-02-27T14:16:33-00:00
            2020-02-27T14:16:33.123Z
        "#,
        vec![
            TS::with_year(2020).build(),
            TS::with_ymd(2020, 2, 27).build(),
            TS::with_ymd(2020, 2, 27)
                .with_hms(14, 16, 33)
                .build_at_unknown_offset(),
            TS::with_ymd(2020, 2, 27)
                .with_hms(14, 16, 33)
                .with_milliseconds(123)
                .build_at_offset(0),
        ].into_iter().map(|ts_res| Timestamp(ts_res.unwrap()).into()).collect(),
    )]
    #[case::text_symbols(
        br#"
            foo
            'bar'
        "#,
        vec![
            "foo", "bar",
        ].into_iter().map(|s| Symbol(s.into()).into()).collect(),
    )]
    #[case::strings(
        br#"
            '''hello'''
            "world"
        "#,
        vec![
            "hello", "world",
        ].into_iter().map(|s| String(s.into()).into()).collect(),
    )]
    #[case::clobs(
        br#"
            {{'''goodbye'''}}
            {{"moon"}}
        "#,
        {
            // XXX annotate a vector otherwise inference gets a bit confused
            let lobs: Vec<&[u8]> = vec![
                b"goodbye", b"moon",
            ];
            lobs
        }.into_iter().map(|b| Clob(b.into()).into()).collect(),
    )]
    #[case::blobs(
        br#"
           {{bW9v}}
        "#,
        {
            // XXX annotate a vector otherwise inference gets a bit confused
            let lobs: Vec<&[u8]> = vec![
                b"moo",
            ];
            lobs
        }.into_iter().map(|b| Blob(b.into()).into()).collect(),
    )]
    #[case::lists(
        br#"
            ["a", "b"]
        "#,
        ion_seq![
            ion_list!["a", "b"]
        ]
    )]
    #[case::sexps(
        br#"
            (e f g)
        "#,
        ion_seq![
            ion_sexp!(Symbol::owned("e") Symbol::owned("f") Symbol::owned("g"))
        ]
    )]
    #[case::structs(
        br#"
            {
                bool_field: a::true,
                string_field: a::"moo!",
                string_field: a::"oink!",
            }
        "#,
        ion_seq![
            ion_struct! {
                "string_field": "oink!".with_annotations(["a"]),
                "string_field": "moo!".with_annotations(["a"]),
                "bool_field": true.with_annotations(["a"])
            }
        ]
    )]
    fn read_and_compare(#[case] input: &[u8], #[case] expected: Sequence) -> IonResult<()> {
        let actual = Element::read_all(input)?;
        assert!(expected.ion_eq(&actual));
        Ok(())
    }
}
