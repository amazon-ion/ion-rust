#![cfg(all(test, feature = "experimental-streaming"))]

mod ion_tests;

use crate::ion_tests::{
    bad, equivs, non_equivs, ElementApi, SkipList, ELEMENT_EQUIVS_SKIP_LIST,
    ELEMENT_GLOBAL_SKIP_LIST, ELEMENT_ROUND_TRIP_SKIP_LIST,
};
use ion_rs::tokens::{ReaderTokenStream, TokenStreamReader};
use ion_rs::{Format, TextKind};
use ion_rs::{IonResult, Reader, ReaderBuilder};
use test_generator::test_resources;

struct TokenNativeElementApi;

impl ElementApi for TokenNativeElementApi {
    type ElementReader<'a> = TokenStreamReader<'a, ReaderTokenStream<'a, Reader<'a>>>;

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

    fn make_reader<'a>(data: &'a [u8]) -> IonResult<Self::ElementReader<'a>> {
        let reader = ReaderBuilder::default().build(data)?;
        let tokens: ReaderTokenStream<'a, _> = reader.into();
        let token_reader: TokenStreamReader<'a, _> = tokens.into();
        Ok(token_reader)
    }
}

good_round_trip! {
    use TokenNativeElementApi;
    fn binary_compact(Format::Binary, Format::Text(TextKind::Compact));
    fn binary_lines(Format::Binary, Format::Text(TextKind::Lines));
    fn binary_pretty(Format::Binary, Format::Text(TextKind::Pretty));
    fn compact_binary(Format::Text(TextKind::Compact), Format::Binary);
    fn compact_lines(Format::Text(TextKind::Compact), Format::Text(TextKind::Lines));
    fn compact_pretty(Format::Text(TextKind::Compact), Format::Text(TextKind::Pretty));
    fn lines_binary(Format::Text(TextKind::Lines), Format::Binary);
    fn lines_compact(Format::Text(TextKind::Lines), Format::Text(TextKind::Compact));
    fn lines_pretty(Format::Text(TextKind::Lines), Format::Text(TextKind::Pretty));
    fn pretty_binary(Format::Text(TextKind::Pretty), Format::Binary);
    fn pretty_compact(Format::Text(TextKind::Pretty), Format::Text(TextKind::Compact));
    fn pretty_lines(Format::Text(TextKind::Pretty), Format::Text(TextKind::Lines));
}

#[test_resources("ion-tests/iontestdata_1_0/bad/**/*.ion")]
#[test_resources("ion-tests/iontestdata_1_0/bad/**/*.10n")]
fn native_bad(file_name: &str) {
    bad(TokenNativeElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata_1_0/good/equivs/**/*.ion")]
#[test_resources("ion-tests/iontestdata_1_0/good/equivs/**/*.10n")]
fn native_equivs(file_name: &str) {
    equivs(TokenNativeElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata_1_0/good/non-equivs/**/*.ion")]
// no binary files exist and the macro doesn't like empty globs...
// see frehberg/test-generator#12
//#[test_resources("ion-tests/iontestdata_1_0/good/non-equivs/**/*.10n")]
fn native_non_equivs(file_name: &str) {
    non_equivs(TokenNativeElementApi, file_name)
}
