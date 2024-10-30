#![cfg(feature = "experimental-reader-writer")]

use crate::ion_tests::{DataStraw, ELEMENT_GLOBAL_SKIP_LIST, SkipList};
use ion_rs::{AnyEncoding, Element, ElementReader, IonData, IonError, IonResult, IonStream, Reader};
use std::collections::HashSet;
use std::fs;
use std::io::BufReader;
use std::iter::Iterator;
use std::sync::LazyLock;
use test_generator::test_resources;

mod ion_tests;

// These tests are all failing because multipart long strings are not handled correctly when the
// "part" boundary happens to also fall on a point where the reader needs to refill the input buffer.
const INCOMPLETE_LONG_STRING_SKIP_LIST: SkipList = &[
    "ion-tests/iontestdata/good/equivs/localSymbolTableAppend.ion",
    "ion-tests/iontestdata/good/equivs/localSymbolTableNullSlots.ion",
    "ion-tests/iontestdata/good/equivs/longStringsWithComments.ion",
    "ion-tests/iontestdata/good/equivs/strings.ion",
    "ion-tests/iontestdata/good/lists.ion",
    "ion-tests/iontestdata/good/strings.ion",
    "ion-tests/iontestdata/good/stringsWithWhitespace.ion",
    "ion-tests/iontestdata/good/strings_cr_nl.ion",
    "ion-tests/iontestdata/good/strings2.ion",
    "ion-tests/iontestdata/good/structs.ion",
    "ion-tests/iontestdata/good/strings_nl.ion",
];

// A copy of the `ELEMENT_GLOBAL_SKIP_LIST` in which each file name has been canonicalized for the
// current host machine. This makes it possible to compare names in the list with names of files
// on the host without worrying about differences in (for example) path separators.
static CANONICAL_FILE_NAMES: LazyLock<Vec<String>> = LazyLock::new(|| {
    ELEMENT_GLOBAL_SKIP_LIST
        .iter()
        .chain(INCOMPLETE_LONG_STRING_SKIP_LIST.iter())
        .filter_map(|filename| {
            // Canonicalize the skip list file names so they're in the host OS' preferred format.
            // This involves looking up the actual file; if canonicalization fails, the file could
            // not be found/read which could mean the skip list is outdated.
            fs::canonicalize(filename).ok()
        })
        .map(|filename| filename.to_string_lossy().into())
        .collect()
});

static SKIP_LIST_1_0: LazyLock<HashSet<String>> =
    LazyLock::new(|| CANONICAL_FILE_NAMES.iter().cloned().collect());

static SKIP_LIST_1_1: LazyLock<HashSet<String>> = LazyLock::new(|| {
    CANONICAL_FILE_NAMES
        .iter()
        .map(|file_1_0| file_1_0.replace("iontestdata", "iontestdata_1_1"))
        .collect()
});

#[test_resources("ion-tests/iontestdata/good/**/*.ion")]
fn detect_incomplete_input_1_0(file_name: &str) {
    incomplete_text_detection_test(&SKIP_LIST_1_0, file_name).unwrap()
}

#[cfg(feature = "experimental-ion-1-1")]
#[test_resources("ion-tests/iontestdata_1_1/good/**/*.ion")]
fn detect_incomplete_input_1_1(file_name: &str) {
    incomplete_text_detection_test(&SKIP_LIST_1_1, file_name).unwrap()
}

fn incomplete_text_detection_test(skip_list: &HashSet<String>, file_name: &str) -> IonResult<()> {
    // Canonicalize the file name so it can be compared to skip list file names without worrying
    // about path separators.
    let file_name: String = fs::canonicalize(file_name)?.to_string_lossy().into();
    if skip_list.contains(&file_name) {
        return Ok(());
    }
    println!("testing {file_name}");
    let file = fs::File::open(&file_name)?;
    let buf_reader = BufReader::new(file);
    let input = DataStraw::new(buf_reader);
    let ion_stream = IonStream::new(input);
    let mut reader = Reader::new(AnyEncoding, ion_stream)?;
    // Manually destructure to allow for pretty-printing of errors
    match reader.read_all_elements() {
        Ok(elements) => {
            assert_eq!(IonData::from(elements), IonData::from(Element::read_all(fs::read(&file_name)?)?))
        }
        Err(IonError::Decoding(e)) => {
            panic!("{:?}: {}", e.position(), e);
        }
        Err(other) => {
            panic!("{other:#?}");
        }
    }
    Ok(())
}
