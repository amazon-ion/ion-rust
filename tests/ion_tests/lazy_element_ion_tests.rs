#![cfg(feature = "experimental-reader-writer")]

use crate::good_round_trip;
use crate::ion_tests::{
    bad, equivs, non_equivs, ElementApi, SkipList, ELEMENT_EQUIVS_SKIP_LIST,
    ELEMENT_GLOBAL_SKIP_LIST, ELEMENT_ROUND_TRIP_SKIP_LIST,
};
use ion_rs::Reader;
use ion_rs::{AnyEncoding, IonResult};
use ion_rs::{Format, TextFormat};
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

#[test_resources("ion-tests/iontestdata_1_0/bad/**/*.ion")]
#[test_resources("ion-tests/iontestdata_1_0/bad/**/*.10n")]
fn lazy_bad(file_name: &str) {
    bad(LazyReaderElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata_1_0/good/equivs/**/*.ion")]
#[test_resources("ion-tests/iontestdata_1_0/good/equivs/**/*.10n")]
fn lazy_equivs(file_name: &str) {
    equivs(LazyReaderElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata_1_0/good/non-equivs/**/*.ion")]
// no binary files exist and the macro doesn't like empty globs...
// see frehberg/test-generator#12
//#[test_resources("ion-tests/iontestdata_1_0/good/non-equivs/**/*.10n")]
fn lazy_non_equivs(file_name: &str) {
    non_equivs(LazyReaderElementApi, file_name)
}
