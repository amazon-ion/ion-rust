// Copyright Amazon.com, Inc. or its affiliates.

//! Provides APIs to read Ion data into [Element] from different sources such
//! as slices or files.

use crate::result::{IonFailure, IonResult};
use crate::{Element, Sequence};

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
                    "found more than one value; second value: {element}",
                ))
            }
            Some(Err(e)) => {
                return IonResult::decoding_error(format!("error after expected value: {e}"))
            }
            None => {}
        };
        Ok(only_element)
    }

    /// Reads all of the values in the input stream, materializing each into an [Element] and
    /// returning the complete sequence as a `Vec<Element>`.
    ///
    /// If an error occurs while reading, returns `Err(IonError)`.
    fn read_all_elements(&mut self) -> IonResult<Sequence> {
        self.elements().collect()
    }
}

/// Holds a reference to a given [ElementReader] implementation and yields one [Element] at a time
/// until the stream is exhausted or invalid data is encountered.
pub struct ElementIterator<'a, R: ElementReader + ?Sized> {
    reader: &'a mut R,
}

impl<R: ElementReader + ?Sized> Iterator for ElementIterator<'_, R> {
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

#[cfg(test)]
mod reader_tests {
    use rstest::*;

    use crate::ion_data::IonEq;
    use crate::{ion_list, ion_seq, ion_sexp, ion_struct};
    use crate::{Decimal, Timestamp};
    use crate::{Element, IntoAnnotatedElement};
    use crate::{IonType, Symbol};

    use super::*;

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
            IonType::Null,
            IonType::Bool,
            IonType::Int,
            IonType::Float,
            IonType::Decimal,
            IonType::Timestamp,
            IonType::Symbol,
            IonType::String,
            IonType::Clob,
            IonType::Blob,
            IonType::List,
            IonType::SExp,
            IonType::Struct,
        ].into_iter()
        .map(Element::from)
        .collect(),
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
        ].into_iter()
        .map(Element::from)
        .chain(
            vec![
                "-18446744073709551616", "18446744073709551615",
                "-79228162514264337593543950336", "79228162514264337593543950335",
            ].into_iter()
            .map(|v| v.parse::<i128>().unwrap())
            .map(Element::from)
        )
        .collect(),
    )]
    #[case::int64_threshold_as_big_int(
        &[0xE0, 0x01, 0x00, 0xEA, 0x28, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        vec![
            "18446744073709551615",
        ].into_iter()
        .map(|v| v.parse::<i128>().unwrap())
        .map(Element::from)
        .collect(),
    )]
    #[case::int64_threshold_as_int64(
        &[0xE0, 0x01, 0x00, 0xEA, 0x38, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        vec![
            "-9223372036854775808",
        ].into_iter()
        .map(|v| v.parse::<i128>().unwrap())
        .map(Element::from)
        .collect(),
    )]
    #[case::floats(
        br#"
           1e0 +inf -inf nan
        "#,
        vec![
            1f64, f64::INFINITY, f64::NEG_INFINITY, f64::NAN
        ].into_iter()
        .map(Element::from)
        .collect(),
    )]
    #[case::decimals(
        br#"
            1d0 100d10 -2.1234567d-100
        "#,
        vec![
            Decimal::new(1, 0),
            Decimal::new(100, 10),
            Decimal::new(-21234567, -107),
        ].into_iter()
        .map(Element::from)
        .collect(),
    )]
    #[case::timestamps(
        br#"
            2020T
            2020-02-27T
            2020-02-27T14:16:33-00:00
            2020-02-27T14:16:33.123Z
        "#,
        vec![
            Timestamp::with_year(2020).build(),
            Timestamp::with_ymd(2020, 2, 27).build(),
            Timestamp::with_ymd(2020, 2, 27)
                .with_hms(14, 16, 33)
                .build(),
            Timestamp::with_ymd(2020, 2, 27)
                .with_hms(14, 16, 33)
                .with_milliseconds(123)
                .with_offset(0).build(),
        ].into_iter()
        .map(Result::unwrap)
        .map(Element::from)
        .collect(),
    )]
    #[case::text_symbols(
        br#"
            foo
            'bar'
        "#,
        vec![
            "foo", "bar",
        ].into_iter()
        .map(Element::symbol)
        .collect(),
    )]
    #[case::strings(
        br#"
            '''hello'''
            "world"
        "#,
        vec![
            "hello", "world",
        ].into_iter()
        .map(Element::from)
        .collect(),
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
        }.into_iter()
        .map(Element::clob)
        .collect(),
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
        }.into_iter()
        .map(Element::blob)
        .collect(),
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
