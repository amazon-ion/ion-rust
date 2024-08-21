#![cfg(feature = "experimental-reader-writer")]

use crate::ion_tests::{DataStraw, ELEMENT_GLOBAL_SKIP_LIST};
use ion_rs::{AnyEncoding, ElementReader, IonError, IonStream, Reader};
use std::fs;
use std::io::BufReader;
use test_generator::test_resources;

#[test_resources("ion-tests/iontestdata_1_1/good/**/*.ion")]
fn detect_incomplete_input(file_name: &str) {
    let skip_list_1_1: Vec<String> = ELEMENT_GLOBAL_SKIP_LIST
        .iter()
        .map(|file_1_0| file_1_0.replace("_1_0", "_1_1"))
        .collect();
    if skip_list_1_1.contains(&file_name.to_owned()) {
        return;
    }
    println!("testing {file_name}");
    let file = fs::File::open(file_name).unwrap();
    let buf_reader = BufReader::new(file);
    let input = DataStraw::new(buf_reader);
    let ion_stream = IonStream::new(input);
    let mut reader = Reader::new(AnyEncoding, ion_stream).unwrap();
    // Manually unwrap to allow for pretty-printing of errors
    match reader.read_all_elements() {
        Ok(_) => {}
        Err(IonError::Decoding(e)) => {
            panic!("{:?}: {}", e.position(), e);
        }
        Err(other) => {
            panic!("{other:#?}");
        }
    }
}
