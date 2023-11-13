#![cfg(feature = "experimental-reader")]
#![cfg(feature = "experimental-writer")]
mod ion_tests;

use crate::ion_tests::{
    bad, equivs, non_equivs, ElementApi, SkipList, ELEMENT_EQUIVS_SKIP_LIST,
    ELEMENT_GLOBAL_SKIP_LIST, ELEMENT_ROUND_TRIP_SKIP_LIST,
};
use ion_rs::{Format, TextKind};
use ion_rs::{IonResult, RawBinaryReader, RawTextReader, Reader};
use test_generator::test_resources;

struct NonBlockingNativeElementApi;

impl ElementApi for NonBlockingNativeElementApi {
    type ElementReader<'a> = Reader<'a>;

    fn make_reader(data: &[u8]) -> IonResult<Self::ElementReader<'_>> {
        // These imports are visible as a temporary workaround.
        // See: https://github.com/amazon-ion/ion-rust/issues/484
        use ion_rs::integration_testing::{new_reader, IVM};
        // If the data is binary, create a non-blocking binary reader.
        if data.starts_with(&IVM) {
            let raw_reader = RawBinaryReader::new(data);
            Ok(new_reader(raw_reader))
        } else {
            // Otherwise, create a non-blocking text reader
            let raw_reader = RawTextReader::new(data);
            Ok(new_reader(raw_reader))
        }
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
    use NonBlockingNativeElementApi;
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
    bad(NonBlockingNativeElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata_1_0/good/equivs/**/*.ion")]
#[test_resources("ion-tests/iontestdata_1_0/good/equivs/**/*.10n")]
fn native_equivs(file_name: &str) {
    equivs(NonBlockingNativeElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata_1_0/good/non-equivs/**/*.ion")]
// no binary files exist and the macro doesn't like empty globs...
// see frehberg/test-generator#12
//#[test_resources("ion-tests/iontestdata_1_0/good/non-equivs/**/*.10n")]
fn native_non_equivs(file_name: &str) {
    non_equivs(NonBlockingNativeElementApi, file_name)
}
