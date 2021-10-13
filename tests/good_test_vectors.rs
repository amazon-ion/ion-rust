use std::collections::BTreeSet;
use std::ffi::OsStr;
use std::fs::File;
use std::io::BufReader;
use std::iter::FromIterator;
use std::path::{Path, PathBuf};
use std::str::FromStr;

use walkdir::WalkDir;

use ion_rs::result::{decoding_error, IonResult};
use ion_rs::{IonType, RawBinaryReader, Reader};

const GOOD_TEST_FILES_PATH: &str = "ion-tests/iontestdata/good/";

// TODO: Populate skip list
const GOOD_TEST_FILES_SKIP_LIST: &[&str] = &[
    // NOP pad support
    "ion-tests/iontestdata/good/emptyThreeByteNopPad.10n",
    "ion-tests/iontestdata/good/equivs/nopPadEmptyStruct.10n",
    "ion-tests/iontestdata/good/equivs/nopPadNonEmptyStruct.10n",
    "ion-tests/iontestdata/good/nopPad16Bytes.10n",
    "ion-tests/iontestdata/good/nopPadInsideEmptyStructNonZeroSymbolId.10n",
    "ion-tests/iontestdata/good/nopPadInsideEmptyStructZeroSymbolId.10n",
    "ion-tests/iontestdata/good/nopPadInsideStructWithNopPadThenValueNonZeroSymbolId.10n",
    "ion-tests/iontestdata/good/nopPadInsideStructWithNopPadThenValueZeroSymbolId.10n",
    "ion-tests/iontestdata/good/nopPadInsideStructWithValueThenNopPad.10n",
    "ion-tests/iontestdata/good/nopPadOneByte.10n",
    "ion-tests/iontestdata/good/valueFollowedByNopPad.10n",
    "ion-tests/iontestdata/good/valuePrecededByNopPad.10n",
    "ion-tests/iontestdata/good/valueBetweenNopPads.10n",
    // Timestamp support
    "ion-tests/iontestdata/good/equivs/timestampSuperfluousOffset.10n",
    "ion-tests/iontestdata/good/timestamp/timestamp2011-02.10n",
    "ion-tests/iontestdata/good/timestamp/timestamp2011.10n",
    // Integer representation limits
    "ion-tests/iontestdata/good/equivs/intsLargeNegative1.10n",
    "ion-tests/iontestdata/good/equivs/intsLargeNegative2.10n",
    "ion-tests/iontestdata/good/equivs/intsLargeNegative3.10n",
    "ion-tests/iontestdata/good/equivs/intsLargePositive1.10n",
    "ion-tests/iontestdata/good/equivs/intsLargePositive2.10n",
    "ion-tests/iontestdata/good/equivs/intsLargePositive3.10n",
    "ion-tests/iontestdata/good/intBigSize1201.10n",
    "ion-tests/iontestdata/good/intBigSize13.10n",
    "ion-tests/iontestdata/good/intBigSize14.10n",
    "ion-tests/iontestdata/good/intBigSize16.10n",
    "ion-tests/iontestdata/good/intBigSize256.10n",
    "ion-tests/iontestdata/good/intLongMaxValuePlusOne.10n",
    "ion-tests/iontestdata/good/intLongMinValue.10n",
    "ion-tests/iontestdata/good/equivs/paddedInts.10n",
    "ion-tests/iontestdata/good/item1.10n",
    // Typecode validation
    "ion-tests/iontestdata/good/typecodes/T0.10n",
    "ion-tests/iontestdata/good/typecodes/T11.10n",
    "ion-tests/iontestdata/good/typecodes/T12.10n",
    "ion-tests/iontestdata/good/typecodes/T2.10n",
    "ion-tests/iontestdata/good/typecodes/T3.10n",
    "ion-tests/iontestdata/good/typecodes/T5.10n",
    "ion-tests/iontestdata/good/typecodes/T6-small.10n",
    "ion-tests/iontestdata/good/typecodes/T7-large.10n",
];

// Iterates over all of the Ion files in GOOD_TEST_FILES_PATH and tries reading each in full.
// If reading completes without an error, the test succeeds.
#[test]
fn read_good_files() -> IonResult<()> {
    // TODO: This is binary-specific because don't have a text reader yet.
    let binary_file_extension: &OsStr = OsStr::new("10n");
    let good_files = all_files_in(GOOD_TEST_FILES_PATH);
    let paths_to_skip = skip_list_as_set(GOOD_TEST_FILES_SKIP_LIST);
    let binary_good_files: Vec<_> = good_files
        .iter()
        .filter(|f| f.extension() == Some(binary_file_extension))
        .filter(|f| !paths_to_skip.contains(<&&PathBuf as AsRef<Path>>::as_ref(&f)))
        .collect();
    let mut failure_count: usize = 0;
    println!();
    for entry in &binary_good_files {
        print!("Reading {}... ", entry.display());
        if let Err(error) = read_file(entry.as_ref()) {
            print!("ERROR: {:?}", error);
            failure_count += 1;
        } else {
            print!("OK");
        }
        println!();
    }
    if failure_count > 0 {
        return decoding_error(&format!(
            "{} good test files could not be read successfully.",
            failure_count
        ));
    }
    Ok(())
}

// Converts the provided slice of strings to a HashSet of paths
fn skip_list_as_set(files_to_skip: &[&str]) -> BTreeSet<PathBuf> {
    let mut skip_set = BTreeSet::new();
    for file in files_to_skip {
        skip_set.insert(PathBuf::from_str(file).unwrap());
    }
    skip_set
}

// Collects all of the files in the provided path into a BTreeSet for easy iteration/filtering.
fn all_files_in(path: &str) -> BTreeSet<PathBuf> {
    let binary_file_iterator = WalkDir::new(path)
        .into_iter()
        .map(|entry| {
            entry.unwrap_or_else(|error| panic!("Failure during dir traversal: {:?}", error))
        })
        .filter(|entry| entry.path().is_file())
        .map(|entry| entry.path().to_owned());
    BTreeSet::from_iter(binary_file_iterator)
}

// Reads all of the Ion values found in the provided file, reporting any errors.
fn read_file(path: &Path) -> IonResult<()> {
    let file = File::open(path).unwrap_or_else(|error| panic!("Failed to open file: {:?}", error));
    let file_reader = BufReader::new(file);
    let mut reader = Reader::new(RawBinaryReader::new(file_reader));
    read_all_values(&mut reader)?;
    Ok(())
}

// Recursively reads all of the values in the provided Reader, surfacing any errors.
fn read_all_values(reader: &mut Reader<RawBinaryReader<BufReader<File>>>) -> IonResult<()> {
    use IonType::*;
    while let Some((ion_type, is_null)) = reader.next()? {
        if is_null {
            continue;
        }
        match ion_type {
            Struct | List | SExpression => {
                reader.step_in()?;
                read_all_values(reader)?;
                reader.step_out()?;
            }
            String => {
                let _text = reader.string_ref_map(|_s| ())?.unwrap();
            }
            Symbol => {
                // The binary reader's tokens are always SIDs
                let _symbol_id = reader.read_raw_symbol()?.unwrap().local_sid().unwrap();
            }
            Integer => {
                let _int = reader.read_i64()?.unwrap();
            }
            Float => {
                let _float = reader.read_f64()?.unwrap();
            }
            Decimal => {
                let _decimal = reader.read_big_decimal()?.unwrap();
            }
            Timestamp => {
                let _timestamp = reader.read_datetime()?.unwrap();
            }
            Boolean => {
                let _boolean = reader.read_bool()?.unwrap();
            }
            Blob => {
                let _blob = reader.read_blob_bytes()?.unwrap();
            }
            Clob => {
                let _clob = reader.read_clob_bytes()?.unwrap();
            }
            Null => {
                unreachable!("Value with IonType::Null returned is_null=false.");
            }
        }
    }
    Ok(())
}
