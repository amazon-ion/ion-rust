#![cfg(feature = "experimental-reader")]
#![cfg(feature = "experimental-writer")]
use crate::ion_tests::contains_path;
use ion_rs::IonData;
use ion_rs::{Element, IonResult, Sequence};
use std::fs::read;
use test_generator::test_resources;

mod ion_tests;

const TO_STRING_SKIP_LIST: &[&str] = &[
    // These tests have shared symbol table imports in them, which the Reader does not
    // yet support.
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt15bit.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt16bit.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt32bit.ion",
    // This test requires the reader to be able to read symbols whose ID is encoded
    // with more than 8 bytes. Having a symbol table with more than 18 quintillion
    // symbols is not very practical.
    "ion-tests/iontestdata_1_0/good/typecodes/T7-large.10n",
    "ion-tests/iontestdata_1_0/good/item1.10n",
    "ion-tests/iontestdata_1_0/good/localSymbolTableImportZeroMaxId.ion",
    "ion-tests/iontestdata_1_0/good/testfile35.ion",
    // These files are encoded in utf16 and utf32; the reader currently assumes utf8.
    "ion-tests/iontestdata_1_0/good/utf16.ion",
    "ion-tests/iontestdata_1_0/good/utf32.ion",
];

#[test_resources("ion-tests/iontestdata_1_0/good/**/*.ion")]
#[test_resources("ion-tests/iontestdata_1_0/good/**/*.10n")]
fn test_to_string(file_name: &str) {
    if contains_path(TO_STRING_SKIP_LIST, file_name) {
        println!("IGNORING: {file_name}");
        return;
    }

    let data = read(file_name).unwrap();
    let result: IonResult<Sequence> = Element::read_all(data.as_slice());
    let elements = result.unwrap_or_else(|e| {
        panic!("Expected to be able to read Ion values for contents of file {file_name}: {e:?}")
    });

    for element in elements {
        let roundtripped = Element::read_one(element.to_string()).unwrap();
        assert!(IonData::eq(&element, &roundtripped))
    }
}
