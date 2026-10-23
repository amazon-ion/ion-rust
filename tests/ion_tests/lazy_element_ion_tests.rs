#![cfg(feature = "experimental-reader-writer")]

use super::Format;
use crate::good_round_trip;
use crate::ion_tests::{
    bad, equivs, non_equivs, DataStraw, ElementApi, SkipList, ELEMENT_EQUIVS_SKIP_LIST,
    ELEMENT_GLOBAL_SKIP_LIST, ELEMENT_ROUND_TRIP_SKIP_LIST,
};
use ion_rs::Reader;
use ion_rs::TextFormat;
use ion_rs::{
    AnyEncoding, Element, IonData, IonInput, IonResult, IonStream, LazyValue, Sequence, Value,
    ValueRef,
};
use std::fs::read;
use test_generator::test_resources;

struct LazyReaderElementApi;

impl ElementApi for LazyReaderElementApi {
    type ElementReader<'a> = Reader<AnyEncoding, &'a [u8]>;

    fn global_skip_list() -> SkipList {
        ELEMENT_GLOBAL_SKIP_LIST
    }

    fn read_one_equivs_skip_list() -> SkipList {
        &[]
    }

    fn round_trip_skip_list() -> SkipList {
        ELEMENT_ROUND_TRIP_SKIP_LIST
    }

    fn equivs_skip_list() -> SkipList {
        ELEMENT_EQUIVS_SKIP_LIST
    }

    fn non_equivs_skip_list() -> SkipList {
        &[]
    }

    fn make_reader(data: &[u8]) -> IonResult<Self::ElementReader<'_>> {
        Reader::new(AnyEncoding, data)
    }
}

good_round_trip! {
    use LazyReaderElementApi;
    fn binary_compact(Format::Binary, Format::Text(TextFormat::Compact));
    fn binary_lines(Format::Binary, Format::Text(TextFormat::Lines));
    fn binary_pretty(Format::Binary, Format::Text(TextFormat::Pretty));
    fn compact_binary(Format::Text(TextFormat::Compact), Format::Binary);
    fn compact_lines(Format::Text(TextFormat::Compact), Format::Text(TextFormat::Lines));
    fn compact_pretty(Format::Text(TextFormat::Compact), Format::Text(TextFormat::Pretty));
    fn lines_binary(Format::Text(TextFormat::Lines), Format::Binary);
    fn lines_compact(Format::Text(TextFormat::Lines), Format::Text(TextFormat::Compact));
    fn lines_pretty(Format::Text(TextFormat::Lines), Format::Text(TextFormat::Pretty));
    fn pretty_binary(Format::Text(TextFormat::Pretty), Format::Binary);
    fn pretty_compact(Format::Text(TextFormat::Pretty), Format::Text(TextFormat::Compact));
    fn pretty_lines(Format::Text(TextFormat::Pretty), Format::Text(TextFormat::Lines));
}

#[test_resources("ion-tests/iontestdata/bad/**/*.ion")]
#[test_resources("ion-tests/iontestdata/bad/**/*.10n")]
fn lazy_bad(file_name: &str) {
    bad(LazyReaderElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata/good/equivs/**/*.ion")]
#[test_resources("ion-tests/iontestdata/good/equivs/**/*.10n")]
fn lazy_equivs(file_name: &str) {
    equivs(LazyReaderElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.ion")]
// no binary files exist and the macro doesn't like empty globs...
// see frehberg/test-generator#12
//#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.10n")]
fn lazy_non_equivs(file_name: &str) {
    non_equivs(LazyReaderElementApi, file_name)
}

/// Stores each top-level value, and each first-level child of a container, as a `LazyElement`
/// and checks that it reads back as the `Element` read directly from the same bytes. A stored text
/// container is re-parsed from its own bytes on first read, so this compares that re-parse with
/// the original parse across the corpus. The second pass streams the input one byte per read, so
/// later values are stored from a buffer window at a nonzero stream offset, which the reader
/// copies rather than overwrites when it shifts the window.
#[test_resources("ion-tests/iontestdata/good/**/*.ion")]
#[test_resources("ion-tests/iontestdata/good/**/*.10n")]
fn lazy_stored_elements(file_name: &str) {
    LazyReaderElementApi::assert_file(LazyReaderElementApi::global_skip_list(), file_name, || {
        let data = read(file_name)?;
        let expected = Element::read_all(&data)?;
        assert_stored_elements_eq(&expected, Reader::new(AnyEncoding, data.as_slice())?)?;
        let stream = IonStream::new(DataStraw::new(data.as_slice()));
        assert_stored_elements_eq(&expected, Reader::new(AnyEncoding, stream)?)
    });
}

fn assert_stored_elements_eq<Input: IonInput>(
    expected: &Sequence,
    reader: Reader<AnyEncoding, Input>,
) -> IonResult<()> {
    let stored = reader.collect::<IonResult<Vec<_>>>()?;
    let actual = stored
        .iter()
        .map(Element::try_from)
        .collect::<IonResult<Vec<_>>>()?;
    assert_sequences_eq(expected, actual.into());

    for (expected, stored) in expected.iter().zip(&stored) {
        let expected_children: Sequence = match expected.value() {
            Value::List(seq) | Value::SExp(seq) => seq.clone(),
            Value::Struct(fields) => fields.fields().map(|(_, value)| value.clone()).collect(),
            _ => continue,
        };
        let children: IonResult<Vec<_>> = match &*stored.read()? {
            ValueRef::List(list) => list.iter().map(|v| v.map(LazyValue::to_owned)).collect(),
            ValueRef::SExp(sexp) => sexp.iter().map(|v| v.map(LazyValue::to_owned)).collect(),
            ValueRef::Struct(fields) => fields
                .iter()
                .map(|f| f.map(|f| f.value().to_owned()))
                .collect(),
            other => panic!("{expected} was read back as {other:?}"),
        };
        let actual_children = children?
            .iter()
            .map(Element::try_from)
            .collect::<IonResult<Vec<_>>>()?;
        assert_sequences_eq(&expected_children, actual_children.into());
    }
    Ok(())
}

fn assert_sequences_eq(expected: &Sequence, actual: Sequence) {
    assert!(
        IonData::eq(expected, &actual),
        "{}",
        LazyReaderElementApi::not_eq_error_message(expected, &actual)
    );
}
