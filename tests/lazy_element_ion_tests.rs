#![cfg(feature = "experimental-lazy-reader")]
#![cfg(feature = "experimental-writer")]
mod ion_tests;

use crate::ion_tests::{
    bad, equivs, non_equivs, ElementApi, SkipList, ELEMENT_EQUIVS_SKIP_LIST,
    ELEMENT_GLOBAL_SKIP_LIST, ELEMENT_ROUND_TRIP_SKIP_LIST,
};
use ion_rs::lazy::reader::LazyReader;
use ion_rs::IonResult;
use ion_rs::{Format, TextKind};
use test_generator::test_resources;

struct LazyReaderElementApi;

impl ElementApi for LazyReaderElementApi {
    type ElementReader<'a> = LazyReader<&'a [u8]>;

    fn make_reader(data: &[u8]) -> IonResult<Self::ElementReader<'_>> {
        Ok(LazyReader::new(data))
    }

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
}

good_round_trip! {
    use LazyReaderElementApi;
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
