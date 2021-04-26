// Copyright Amazon.com, Inc. or its affiliates.

//! Provides utility to load Ion data into [`Element`](super::Element) from different sources such
//! as slices or files.

use crate::result::{decoding_error, IonResult};
use crate::value::owned::{OwnedElement, OwnedSequence, OwnedStruct, OwnedSymbolToken, OwnedValue};
use crate::value::AnyInt;
use crate::IonType;
use ion_c_sys::reader::{IonCReader, IonCReaderHandle};
use ion_c_sys::ION_TYPE;
use std::convert::{TryFrom, TryInto};

use super::owned::text_token;

// TODO add/refactor trait/implementation for borrowing over some context
//      we could make it generic with generic associated types or just have a lifetime
//      scoped implementation

/// Loads Ion data into [`Element`](super::Element) instances.
///
/// ## Notes
/// Users of this trait should not assume any particular implementation of [`Element`](super::Element).
/// In the future, [generic associated types (GAT)][gat] and [existential types in traits][et]
/// should make it easier to model this more abstractly.
///
/// [gat]: https://rust-lang.github.io/rfcs/1598-generic_associated_types.html
/// [et]:https://rust-lang.github.io/rfcs/2071-impl-trait-existential-types.html
pub trait Loader {
    /// Parses Ion over a given slice of data and yields each top-level value as
    /// an [`Element`](super::Element) instance.
    ///
    /// The [`Iterator`] will generally return `Some(Ok([Element]))` but on a failure of
    /// parsing it will return a `Some(Err([IonError]))` and then a `None` to signal no more
    /// elements.
    ///
    /// This will return an [`IonError`](crate::result::IonError) if the parser could not
    /// be initialized over the given slice.
    fn iterate_over<'a, 'b>(
        &'a self,
        data: &'b [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<OwnedElement>> + 'b>>;

    /// Parses given Ion over a given slice into an [`Vec`] returning an
    /// [`IonError`](crate::result::IonError) if any error occurs during the parse.
    #[inline]
    fn load_all(&self, data: &[u8]) -> IonResult<Vec<OwnedElement>> {
        self.iterate_over(data)?.collect()
    }

    /// Parses Ion over a given slice into a single [`Element`](super::Element) instance.
    /// Returning [`IonError`](crate::result::IonError) if any error occurs during the parse
    /// or there is more than one top-level [`Element`](super::Element) in the data.
    #[inline]
    fn load_one(&self, data: &[u8]) -> IonResult<OwnedElement> {
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

struct IonCReaderIterator<'a> {
    reader: IonCReaderHandle<'a>,
    done: bool,
}

impl<'a> IonCReaderIterator<'a> {
    /// Moves the reader forward converting to `IonResult`.
    #[inline]
    fn read_next(&mut self) -> IonResult<ION_TYPE> {
        Ok(self.reader.next()?)
    }

    /// Materializes a value with an [`IonType`]
    fn materialize(&mut self, ion_type: IonType) -> IonResult<OwnedElement> {
        use OwnedValue::*;
        // TODO when doing BorrowedElement, we can compare against the input buffer if
        //      there is one and be smart about when to materialize strings...

        // TODO deal with local SIDs/sources, this requires deeper integration with Ion C
        //      than we're willing to do right now...

        let annotations: Vec<OwnedSymbolToken> = self
            .reader
            .get_annotations()?
            .into_iter()
            .map(|s| (*s).into())
            .collect();

        let value: OwnedValue = if self.reader.is_null()? {
            Null(ion_type)
        } else {
            match ion_type {
                // technically unreachable...
                IonType::Null => Null(ion_type),
                IonType::Boolean => Boolean(self.reader.read_bool()?),
                // TODO deal with the big integer case
                IonType::Integer => Integer(if let Ok(ival) = self.reader.read_i64() {
                    AnyInt::I64(ival)
                } else {
                    AnyInt::BigInt(self.reader.read_bigint()?)
                }),
                IonType::Float => Float(self.reader.read_f64()?),
                IonType::Decimal => Decimal(self.reader.read_bigdecimal()?.into()),
                IonType::Timestamp => Timestamp(self.reader.read_datetime()?.into()),
                // TODO get the `ION_SYMBOL` value and extract the complete symbolic information.
                IonType::Symbol => Symbol(self.reader.read_string()?.as_str().into()),
                IonType::String => String(self.reader.read_string()?.as_str().into()),
                IonType::Clob => Clob(self.reader.read_bytes()?),
                IonType::Blob => Blob(self.reader.read_bytes()?),
                IonType::List => List(self.materialize_sequence()?),
                IonType::SExpression => SExpression(self.materialize_sequence()?),
                IonType::Struct => Struct(self.materialize_struct()?),
            }
        };

        Ok(OwnedElement::new(annotations, value))
    }

    /// Materializes a top-level value with a known Ion C type.
    #[inline]
    fn materialize_top_level(&mut self, ionc_type: ION_TYPE) -> IonResult<OwnedElement> {
        self.materialize(ionc_type.try_into()?)
    }

    fn materialize_sequence(&mut self) -> IonResult<OwnedSequence> {
        let mut children = Vec::new();
        self.reader.step_in()?;
        loop {
            let ionc_type = self.read_next()?;
            if let ion_c_sys::ION_TYPE_EOF = ionc_type {
                break;
            }

            children.push(self.materialize_top_level(ionc_type)?);
        }
        self.reader.step_out()?;
        Ok(children.into_iter().collect())
    }

    fn materialize_struct(&mut self) -> IonResult<OwnedStruct> {
        let mut fields = vec![];
        self.reader.step_in()?;
        loop {
            let ionc_type = self.read_next()?;
            if let ion_c_sys::ION_TYPE_EOF = ionc_type {
                break;
            }

            // TODO get the `ION_SYMBOL` value and extract the complete symbolic information.
            let token = text_token(self.reader.get_field_name()?.as_str());
            let elem = self.materialize_top_level(ionc_type)?;
            fields.push((token, elem));
        }
        self.reader.step_out()?;
        Ok(fields.into_iter().collect())
    }
}

impl<'a> Iterator for IonCReaderIterator<'a> {
    type Item = IonResult<OwnedElement>;

    fn next(&mut self) -> Option<Self::Item> {
        // if we previously returned an error, we're done
        if self.done {
            return None;
        }
        // perform scaffolding over the Some/None part of the API
        match self.read_next() {
            Ok(ionc_type) => {
                if let ion_c_sys::ION_TYPE_EOF = ionc_type {
                    // reader says nothing, we're done!
                    self.done = true;
                    None
                } else {
                    // we've got something
                    let result = self.materialize_top_level(ionc_type);
                    if let Err(_) = &result {
                        // a failure means the iterator is done
                        self.done = true;
                    }
                    Some(result)
                }
            }
            // next failed...
            Err(e) => Some(Err(e)),
        }
    }
}

struct IonCLoader {}

impl Loader for IonCLoader {
    fn iterate_over<'a, 'b>(
        &'a self,
        data: &'b [u8],
    ) -> IonResult<Box<dyn Iterator<Item = IonResult<OwnedElement>> + 'b>> {
        let reader = IonCReaderHandle::try_from(data)?;

        Ok(Box::new(IonCReaderIterator {
            reader,
            done: false,
        }))
    }
}

/// Returns an implementation defined [`Loader`] instance.
pub fn loader() -> impl Loader {
    IonCLoader {}
}

#[cfg(test)]
mod loader_tests {
    use super::*;
    use crate::types::timestamp::Timestamp as TS;
    use crate::value::owned::OwnedValue::*;
    use crate::value::owned::*;
    use crate::value::{AnyInt, Element};
    use crate::IonType;
    use bigdecimal::BigDecimal;
    use ion_c_sys::result::IonCError;
    use ion_c_sys::{
        ion_error_code_IERR_INVALID_BINARY, ion_error_code_IERR_INVALID_STATE,
        ion_error_code_IERR_NULL_VALUE,
    };
    use num_bigint::BigInt;
    use rstest::*;
    use std::str::FromStr;

    #[inline]
    fn load_all(input: &[u8]) -> IonResult<Vec<OwnedElement>> {
        loader().iterate_over(input)?.collect()
    }

    #[inline]
    fn single(input: &[u8]) -> IonResult<OwnedElement> {
        let loader = loader();
        let mut iter = loader.iterate_over(input)?;
        let first = iter.next().unwrap();
        assert_eq!(None, iter.next());
        first
    }

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
        ].into_iter().map(|v| AnyInt::I64(v)).chain(
            vec![
                "-18446744073709551616", "18446744073709551615",
                "-79228162514264337593543950336", "79228162514264337593543950335",
            ].into_iter()
            .map(|v| AnyInt::BigInt(BigInt::parse_bytes(v.as_bytes(), 10).unwrap()))
        ).map(|ai| Integer(ai).into()).collect(),
    )]
    #[case::floats(
        // TODO NaN is Ion Data Model equivalent to itself but not PartialEq
        br#"
           1e0 +inf -inf
        "#,
        vec![
            1f64, f64::INFINITY, f64::NEG_INFINITY,
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
            vec!["a", "b"].into_iter().map(|s| String(s.into()).into()).collect(),
        ].into_iter()
            .map(|elems: Vec<OwnedElement>| List(elems.into_iter().collect()).into())
            .collect(),
    )]
    #[case::sexps(
        br#"
            (e f g)
        "#,
        vec![
            vec!["e", "f", "g"].into_iter().map(|s| Symbol(s.into()).into()).collect(),
        ].into_iter()
            .map(|elems: Vec<OwnedElement>| SExpression(elems.into_iter().collect()).into())
            .collect(),
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
            vec![
                (text_token("string_field"), String("oink!".into())),
                (text_token("string_field"), String("moo!".into())),
                (text_token("bool_field"), Boolean(true)),
            ]
        ].into_iter()
            .map(|fields: Vec<(OwnedSymbolToken, OwnedValue)>| {
                Struct(
                    fields.into_iter().map(|(tok, val)| {
                        (tok, OwnedElement::new(vec![text_token("a")], val))
                    }).collect()).into()
            })
            .collect(),
    )]
    fn load_and_compare(
        #[case] input: &[u8],
        #[case] expected: Vec<OwnedElement>,
    ) -> IonResult<()> {
        let actual = load_all(input)?;
        assert_eq!(expected, actual);
        Ok(())
    }

    #[test]
    fn load_nan() -> IonResult<()> {
        let actual = single(b"nan")?;
        assert!(actual.as_f64().unwrap().is_nan());
        Ok(())
    }

    #[rstest]
    #[case::unknown_local_symbol(
        br#"
            $ion_1_0
            $ion_symbol_table::{
                symbols:[null]
            }
            $10
        "#,
        vec![
            Err(IonCError::from(ion_error_code_IERR_NULL_VALUE).into())
        ]
    )]
    #[case::unknown_shared_symbol_field_name(
        br#"
            $ion_1_0
            $ion_symbol_table::{
                imports:[{name: "my_table", version: 1, max_id: 100}]
            }
            {$10:5}
        "#,
        vec![
            Err(IonCError::from(ion_error_code_IERR_NULL_VALUE).into())
        ]
    )]
    #[case::illegal_negative_zero_int(
        &[0xE0, 0x01, 0x00, 0xEA, 0x30],
        vec![
            Err(IonCError::from(ion_error_code_IERR_INVALID_BINARY).into())
        ]
    )]
    #[case::illegal_fcode(
        &[0xE0, 0x01, 0x00, 0xEA, 0xF0],
        vec![
            Err(IonCError::from(ion_error_code_IERR_INVALID_STATE).into())
        ]
    )]
    /// Like load_and_compare, but against results (which makes it easier to test for errors).
    fn load_expect(
        #[case] input: &[u8],
        #[case] expected: Vec<IonResult<OwnedElement>>,
    ) -> IonResult<()> {
        let actual: Vec<_> = loader().iterate_over(input)?.collect();
        assert_eq!(expected, actual);
        Ok(())
    }
}
