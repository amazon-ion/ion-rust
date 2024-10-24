#![cfg(feature = "experimental-ion-1-1")]
#![cfg(feature = "experimental-reader-writer")]
/// TODO: When the Ion 1.1 binary reader is complete, update this module to include binary tests
mod ion_tests;

use crate::ion_tests::{bad, equivs, non_equivs, ElementApi, SkipList};
use ion_rs::IonResult;
use ion_rs::{v1_1, Reader};
use test_generator::test_resources;

struct LazyReaderElementApi;

impl ElementApi for LazyReaderElementApi {
    type ElementReader<'a> = Reader<v1_1::Text, &'a [u8]>;

    fn make_reader(data: &[u8]) -> IonResult<Self::ElementReader<'_>> {
        Ok(Reader::new(v1_1::Text, data).unwrap())
    }

    fn global_skip_list() -> SkipList {
        &[
            // TODO: Revisit these once the Ion 1.1 System Symbol Table is defined
            "ion-tests/iontestdata_1_1/good/equivs/localSymbolTableAppend.ion",
            "ion-tests/iontestdata_1_1/good/equivs/localSymbolTableNullSlots.ion",
            "ion-tests/iontestdata_1_1/good/equivs/localSymbolTableWithAnnotations.ion",
            "ion-tests/iontestdata_1_1/good/equivs/localSymbolTables.ion",
            "ion-tests/iontestdata_1_1/good/equivs/nonIVMNoOps.ion",
            "ion-tests/iontestdata_1_1/good/non-equivs/annotatedIvms.ion",
            "ion-tests/iontestdata_1_1/good/non-equivs/localSymbolTableWithAnnotations.ion",
            "ion-tests/iontestdata_1_1/good/non-equivs/symbolTables.ion",
            "ion-tests/iontestdata_1_1/good/non-equivs/symbolTablesUnknownText.ion",
            // TODO: Remove from skiplist when shared symbol tables are supported
            "ion-tests/iontestdata_1_1/good/localSymbolTableImportZeroMaxId.ion",
            "ion-tests/iontestdata_1_1/good/testfile35.ion",
            // TODO: https://github.com/amazon-ion/ion-rust/issues/653
            "ion-tests/iontestdata_1_1/good/equivs/macros/make_string.ion",
            "ion-tests/iontestdata_1_1/good/equivs/macros/values.ion",
            "ion-tests/iontestdata_1_1/good/equivs/macros/none.ion",
            "ion-tests/iontestdata_1_1/good/macros/none_invoked_deeply_nested.ion",
            "ion-tests/iontestdata_1_1/good/macros/none_invoked_in_struct.ion",
            "ion-tests/iontestdata_1_1/good/macros/none_invoked_in_struct_field.ion",
            // Ints outside the i128 range
            "ion-tests/iontestdata_1_1/good/intBigSize16.10n",
            "ion-tests/iontestdata_1_1/good/intBigSize256.ion",
            "ion-tests/iontestdata_1_1/good/intBigSize256.10n",
            "ion-tests/iontestdata_1_1/good/intBigSize512.ion",
            "ion-tests/iontestdata_1_1/good/intBigSize1201.10n",
            "ion-tests/iontestdata_1_1/good/equivs/bigInts.ion",
        ]
    }

    fn read_one_equivs_skip_list() -> SkipList {
        &[]
    }

    fn round_trip_skip_list() -> SkipList {
        &[]
    }

    fn equivs_skip_list() -> SkipList {
        &[]
    }

    fn non_equivs_skip_list() -> SkipList {
        &[]
    }
}

// TODO: Update to write as Ion 1.1
mod good_round_trip {
    use super::*;
    use ion_rs::Format::Text;
    use ion_rs::TextFormat;
    use test_generator::test_resources;

    #[test_resources("ion-tests/iontestdata_1_1/good/**/*.ion")]
    fn round_trip(file_name: &str) {
        LazyReaderElementApi::assert_file(
            LazyReaderElementApi::global_skip_list(),
            file_name,
            || {
                LazyReaderElementApi::assert_three_way_round_trip(
                    file_name,
                    Text(TextFormat::Lines),
                    Text(TextFormat::Lines),
                )
            },
        );
    }
}

#[test_resources("ion-tests/iontestdata_1_1/bad/**/*.ion")]
fn lazy_bad(file_name: &str) {
    bad(LazyReaderElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata_1_1/good/equivs/**/*.ion")]
fn lazy_equivs(file_name: &str) {
    equivs(LazyReaderElementApi, file_name)
}

#[test_resources("ion-tests/iontestdata_1_1/good/non-equivs/**/*.ion")]
fn lazy_non_equivs(file_name: &str) {
    non_equivs(LazyReaderElementApi, file_name)
}
