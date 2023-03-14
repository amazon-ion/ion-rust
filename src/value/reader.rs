// Copyright Amazon.com, Inc. or its affiliates.

//! Provides APIs to read Ion data into [Element] from different sources such
//! as slices or files.

use crate::result::{decoding_error, IonResult};
use crate::value::native_reader::NativeElementReader;
use crate::value::owned::Element;

// TODO add/refactor trait/implementation for borrowing over some context
//      we could make it generic with generic associated types or just have a lifetime
//      scoped implementation

/// Reads Ion data into [`Element`] instances.
pub trait ElementReader {
    /// Parses Ion over a given slice of data and yields each top-level value as
    /// an [`Element`] instance.
    ///
    /// The [`Iterator`] will generally return `Some(Ok([`Element`]))` but on a failure of
    /// parsing it will return a `Some(Err([IonError]))` and then a `None` to signal no more
    /// elements.
    ///
    /// This will return an [`IonError`](crate::result::IonError) if the parser could not
    /// be initialized over the given slice.
    fn iterate_over<'a, 'b>(
        &'a self,
        data: &'b [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<Element>> + 'b>>;

    /// Parses given Ion over a given slice into an [`Vec`] returning an
    /// [`IonError`](crate::result::IonError) if any error occurs during the parse.
    #[inline]
    fn read_all(&self, data: &[u8]) -> IonResult<Vec<Element>> {
        self.iterate_over(data)?.collect()
    }

    /// Parses Ion over a given slice into a single [`Element`] instance.
    /// Returns [`IonError`](crate::result::IonError) if any error occurs during the parse
    /// or there is more than one top-level [`Element`] in the data.
    #[inline]
    fn read_one(&self, data: &[u8]) -> IonResult<Element> {
        let mut iter = self.iterate_over(data)?;
        match iter.next() {
            Some(Ok(elem)) => {
                // make sure there is nothing else
                match iter.next() {
                    None => Ok(elem),
                    Some(Ok(_)) => {
                        decoding_error("Expected a single element, but there was more than one")
                    }
                    Some(other) => other,
                }
            }
            Some(other) => other,
            None => decoding_error("Expected a single element, data was empty"),
        }
    }
}

/// Returns an implementation defined [`ElementReader`] instance.
pub fn element_reader() -> impl ElementReader {
    native_element_reader()
}

pub fn native_element_reader() -> NativeElementReader {
    NativeElementReader {}
}

#[cfg(test)]
mod reader_tests {
    use super::*;
    use crate::ion_eq::IonEq;
    use crate::types::integer::Integer;
    use crate::types::timestamp::Timestamp as TS;
    use crate::value::builders::{ion_list, ion_sexp, ion_struct};
    use crate::value::owned::Value::*;
    use crate::value::owned::{Element, IntoAnnotatedElement};
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
            Null(IonType::Boolean),
            Null(IonType::Integer),
            Null(IonType::Float),
            Null(IonType::Decimal),
            Null(IonType::Timestamp),
            Null(IonType::Symbol),
            Null(IonType::String),
            Null(IonType::Clob),
            Null(IonType::Blob),
            Null(IonType::List),
            Null(IonType::SExpression),
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
            0,
            -65536, 65535,
            -4294967296, 4294967295,
            -9007199254740992, 9007199254740991,
        ].into_iter().map(Integer::I64).chain(
            vec![
                "-18446744073709551616", "18446744073709551615",
                "-79228162514264337593543950336", "79228162514264337593543950335",
            ].into_iter()
            .map(|v| Integer::BigInt(BigInt::parse_bytes(v.as_bytes(), 10).unwrap()))
        ).map(|ai| Integer(ai).into()).collect(),
    )]
    #[case::int64_threshold_as_big_int(
        &[0xE0, 0x01, 0x00, 0xEA, 0x28, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        vec![
            "18446744073709551615",
        ].into_iter()
        .map(|v| Integer::BigInt(BigInt::parse_bytes(v.as_bytes(), 10).unwrap())).map(|ai| Integer(ai).into()).collect(),
    )]
    #[case::int64_threshold_as_int64(
        &[0xE0, 0x01, 0x00, 0xEA, 0x38, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        vec![
            "-9223372036854775808",
        ].into_iter()
        .map(|v| Integer::BigInt(BigInt::parse_bytes(v.as_bytes(), 10).unwrap())).map(|ai| Integer(ai).into()).collect(),
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
        vec![
            ion_list!["a", "b"]
        ]
    )]
    #[case::sexps(
        br#"
            (e f g)
        "#,
        vec![
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
        vec![
            ion_struct! {
                "string_field": "oink!".with_annotations(["a"]),
                "string_field": "moo!".with_annotations(["a"]),
                "bool_field": true.with_annotations(["a"])
            }.into()
        ]
    )]
    fn read_and_compare(#[case] input: &[u8], #[case] expected: Vec<Element>) -> IonResult<()> {
        let actual = element_reader().read_all(input)?;
        assert!(expected.ion_eq(&actual));
        Ok(())
    }
}
