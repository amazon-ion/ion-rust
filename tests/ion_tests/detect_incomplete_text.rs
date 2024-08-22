#![cfg(feature = "experimental-reader-writer")]

use crate::ion_tests::{DataStraw, ELEMENT_GLOBAL_SKIP_LIST};
use ion_rs::{AnyEncoding, ElementReader, IonError, IonStream, Reader};
use std::fs;
use std::io::BufReader;
use test_generator::test_resources;

#[test_resources("ion-tests/iontestdata_1_1/good/**/*.ion")]
fn detect_incomplete_input(file_name: &str) {
    // Canonicalize the file name so it can be compared to skip list file names without worrying
    // about path separators.
    let file_name: String = fs::canonicalize(file_name)
        .unwrap()
        .to_string_lossy()
        .into();
    // Map each 1.0 skip list file name to the 1.1 equivalent
    let skip_list_1_1: Vec<String> = ELEMENT_GLOBAL_SKIP_LIST
        .iter()
        .map(|file_1_0| file_1_0.replace("_1_0", "_1_1"))
        .filter_map(|filename| {
            // Canonicalize the skip list file names so they're in the host OS' preferred format.
            // This involves looking up the actual file; if canonicalization fails, the file could
            // not be found/read which could mean the skip list is outdated.
            fs::canonicalize(filename).ok()
        })
        .map(|filename| filename.to_string_lossy().into())
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
