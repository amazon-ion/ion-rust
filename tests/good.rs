use std::collections::BTreeSet;
use std::fs::File;
use std::io::BufReader;
use std::iter::FromIterator;
use std::path::{Path, PathBuf};

use walkdir::WalkDir;

use ion_rust::result::IonResult;

const GOOD_TEST_FILES_PATH: &str = "ion-tests/iontestdata/good/";

// TODO: Populate skip list
const _SKIP_LIST: Vec<PathBuf> = Vec::new();

// Iterates over all of the Ion files in GOOD_TEST_FILES_PATH and tries reading each in full.
// If reading completes without an error, the test succeeds.
#[test]
fn read_good_files() -> IonResult<()> {
    let binary_files = all_files_in(GOOD_TEST_FILES_PATH);
    for entry in &binary_files {
        // TODO: Skip list check
        read_file(entry.as_ref())?;
    }
    Ok(())
}

// Reads all of the Ion values found in the provided file, reporting any errors.
fn read_file(path: &Path) -> IonResult<()> {
    let file = File::open(path).unwrap_or_else(|error| panic!("Failed to open file: {:?}", error));
    let _file_reader = BufReader::new(file);
    // TODO: Read this file
    Ok(())
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
