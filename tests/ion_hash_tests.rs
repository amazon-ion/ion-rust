// Copyright Amazon.com, Inc. or its affiliates.
#![cfg(feature = "ion-hash")]

use digest::consts::U4096;
use digest::{FixedOutput, Reset, Update};
use ion_rs::element::writer::ElementWriter;
use ion_rs::element::{Element, Struct};
use ion_rs::ion_hash::IonHasher;
use ion_rs::result::{illegal_operation, IonResult};
use ion_rs::types::IntAccess;

use ion_rs::IonWriter;
use std::convert::From;
use std::fmt::Debug;
use std::fs::read;
use std::iter::FromIterator;
use thiserror::Error;

#[derive(Default, Clone)]
struct IdentityDigest(Vec<u8>);

impl IdentityDigest {
    fn output_size() -> usize {
        4096usize
    }
}

impl Update for IdentityDigest {
    fn update(&mut self, data: impl AsRef<[u8]>) {
        // When we we get the finalized output of another `IdentityDigest`, it's
        // going to have a ton of trailing zeros. Sometimes Ion Hash actually
        // does call update with trailing zeros (e.g. float negative zero). So
        // we have a problem: when should we use the data verbatim and when
        // should we strip the trailing zeros that are *only there because of
        // the fixed output trait*? The hack is to strip trailing zeroes if we
        // get called with something that looks like it came from the result of
        // another IdentityDigest. Note that `>=` is used here due to escaping
        // (which ironically, means the output isn't fixed size).
        let data = data.as_ref();
        let actual_update = if data.len() >= IdentityDigest::output_size() {
            without_trailing_zeros(data)
        } else {
            data
        };
        self.0.extend(actual_update);
    }
}

impl FixedOutput for IdentityDigest {
    type OutputSize = U4096;

    fn finalize_into(self, out: &mut digest::generic_array::GenericArray<u8, Self::OutputSize>) {
        for (i, byte) in self.0.iter().enumerate() {
            out[i] = *byte;
        }
    }

    fn finalize_into_reset(
        &mut self,
        out: &mut digest::generic_array::GenericArray<u8, Self::OutputSize>,
    ) {
        for (i, byte) in self.0.iter().enumerate() {
            out[i] = *byte;
        }
        self.reset();
    }
}

impl Reset for IdentityDigest {
    fn reset(&mut self) {
        self.0.clear();
    }
}

fn without_trailing_zeros(data: &[u8]) -> &[u8] {
    if data.is_empty() {
        return data;
    }

    let index = data
        .as_ref()
        .iter()
        .rposition(|byte| *byte != 0x00)
        .unwrap();

    &data[0..=index]
}

const IGNORE_LIST: &[&str] = &[
    // Uses md5 (not identity)
    r#"{Metrics:{'Event.Catchup':[{Value:0,Unit:ms}],'FanoutCache.Time':[{Value:1,Unit:ms}]}}"#,
    // ion-rust doesn't have full support for unknown symbols yet, so we can't properly read these test cases.
    // The ion-hash crate, however, does have full support for symbols with unknown text.
    // See `mod unknown_symbol_text_tests` at the end of this file for equivalent tests.
    "'$0'",
    "{'$0':1}",
    "'$0'::{}",
];

fn should_ignore(test_name: &str) -> bool {
    /// Some tests don't have names (in Ion annotations) and are named after the
    /// Ion text representation of the case itself. We turn that (name) into a
    /// String (see `test_case_name`) in a non-deterministic way (e.g. struct
    /// field ordering is random). This method does some normalization for the
    /// sake of comparing two test names!
    fn normalize(name: &str) -> String {
        let mut chars: Vec<_> = name.chars().filter(|ch| !ch.is_whitespace()).collect();
        chars.sort();
        String::from_iter(chars.iter())
    }

    let normalized_test_name = normalize(test_name);
    IGNORE_LIST
        .iter()
        .any(|ignore| normalize(ignore) == normalized_test_name)
}

#[test]
fn ion_hash_tests() -> IonHashTestResult<()> {
    test_file("ion-hash-test/ion_hash_tests.ion")
}

fn test_file(file_name: &str) -> IonHashTestResult<()> {
    let data = read(file_name).map_err(|source| ion_rs::IonError::IoError { source })?;
    let elems = Element::read_all(data)?;
    test_all(elems)
}

fn test_all(elems: Vec<Element>) -> IonHashTestResult<()> {
    let mut failures: Vec<IonHashTestError> = vec![];
    for case in &elems {
        let annotated_test_name = test_case_name_from_annotation(case);

        let case = case.as_struct().expect("test cases are structs");
        let expect = case
            .get("expect")
            .expect("test cases have an `expect` value");

        // The case example can be text or binary but not both. Text is already
        // decoded at this point.
        //
        // Implementation note: the arms call into `test_case` directly (vs.
        // returning an `Element`) because of ownership. In the text case, we
        // already have a decoded, borrowed Element. In the binary case, we
        // first need to decode one and thus need to store the decoded Element
        // somewhere. Thus, the two cases have different types: `&E` vs `E`.
        // While we could clone the text case, it's just as simple to just
        // inline the call to `test_case` and avoid the clone.
        match (case.get("ion"), case.get("10n")) {
            (Some(text), None) => test_case(annotated_test_name, text, expect),
            (None, Some(binary)) => {
                // The sexp contains a binary value without the BVM.
                let value = seq_to_bytes(binary);
                // TODO: the binary IVM is pub(crate) in ion-rust
                let mut bytes = vec![0xE0, 0x01, 0x00, 0xEA];
                bytes.extend(value);

                let loaded = Element::read_all(&bytes)?;
                let elem = loaded
                    .into_iter()
                    .next()
                    .expect("10n test case should have a single element (there were none)");
                test_case(annotated_test_name, &elem, expect)
            }
            _ => {
                unreachable!("test case structs must have either an `ion` field or  an `10n` field")
            }
        }
        .unwrap_or_else(|e| failures.push(e));
    }
    match failures.len() {
        0 => Ok(()),
        1 => Err(failures.pop().unwrap()),
        _ => Err(IonHashTestError::MultipleTestsFailed { causes: failures }),
    }
}

/// A single test case. `input` is the input to ion-hash, while `expect` is a
/// "program" that we use to validate ion-hash computed the right result.
// There are two generics here due to the difference between text and binary
// cases. Binary cases need another call to `element_reader` and the calling
// function might be generic over `IonElement`.
fn test_case(
    test_case_name: Option<String>,
    input: &Element,
    expect: &Element,
) -> IonHashTestResult<()> {
    let test_case_name = match test_case_name {
        Some(name) => name,
        None => test_case_name_from_value(input).map_err(|e| IonHashTestError::TestError {
            test_case_name: None,
            message: Some(format!(
                "Unable to determine test case name for {:?}",
                input
            )),
            cause: Some(Box::new(e)),
        })?,
    };

    if should_ignore(&test_case_name) {
        println!("skipping: {}", test_case_name);
        return Ok(());
    }

    // Uncomment me if you're trying to debug a panic!
    // eprintln!("running: {}", test_case_name);

    let struct_ = expect.as_struct().expect("`expect` should be a struct");
    let expected = expected_hash(struct_)?;

    let result = IdentityDigest::hash_element(input)?;

    // Ignore trailing empty bytes caused by the identity digest producing a
    // variable sized result. Without this, any test failure will write lots of
    // stuff to your console which can be annoying since it takes forever.
    let expected_string = format!("{:02x?}", without_trailing_zeros(&expected[..]));
    let actual_string = format!("{:02x?}", without_trailing_zeros(&result[..]));

    if expected_string != actual_string {
        Err(IonHashTestError::TestFailed {
            test_case_name,
            message: Some(format!(
                "expected: {}\nwas: {}",
                expected_string, actual_string
            )),
        })
    } else {
        Ok(())
    }
}

fn expected_hash(struct_: &Struct) -> IonResult<Vec<u8>> {
    let identity = if let Some(identity) = struct_.get("identity") {
        identity.as_sequence().expect("`identity` should be a sexp")
    } else {
        illegal_operation("only identity tests are implemented")?
    };

    if let Some(expectation) = identity.elements().last() {
        let method = expectation
            .annotations()
            .iter()
            .next()
            .expect("identity sexps have one annotation")
            .text()
            .expect("identity sexps contain elements with text annotations");

        let bytes = seq_to_bytes(expectation);

        match method {
            "digest" | "final_digest" => Ok(bytes),
            _ => illegal_operation(format!("unknown expectation `{}`", method))?,
        }
    } else {
        illegal_operation("expected at least expectation!")?
    }
}

/// Test cases may be annotated with a test name. Or, not! If they aren't, the
/// name of the test is the Ion text representation of the input value.
fn test_case_name_from_value(test_input_ion: &Element) -> IonResult<String> {
    let mut buf = Vec::new();
    let mut text_writer = ion_rs::TextWriterBuilder::new().build(&mut buf)?;
    text_writer.write_element(test_input_ion)?;
    text_writer.flush()?;
    drop(text_writer);

    Ok(String::from_utf8_lossy(&buf).to_string())
}

fn test_case_name_from_annotation(test_case_ion: &Element) -> Option<String> {
    test_case_ion
        .annotations()
        .iter()
        .next()
        .map(|tok| tok.text().unwrap().into())
}

/// The test file is full of byte arrays represented as SExps of hex-formatted
/// bytes. This method extracts the bytes into a Vec.
fn seq_to_bytes(elem: &Element) -> Vec<u8> {
    elem.as_sequence()
        .expect("expected a sequence")
        .elements()
        .map(|it| {
            it.as_int()
                .and_then(|i| i.as_i64())
                .expect("expected a sequence of bytes") as u8
        })
        .collect()
}

type IonHashTestResult<T> = Result<T, IonHashTestError>;

#[derive(Debug, Error)]
pub enum IonHashTestError {
    /// Indicates that an IO error was encountered while reading or writing.
    #[error("{source:?}")]
    IonRsError {
        #[from]
        source: ion_rs::IonError,
    },

    #[error("FAIL: {test_case_name}: {message:?}")]
    TestFailed {
        test_case_name: String,
        message: Option<String>,
    },

    #[error("ERROR: {test_case_name:?}: {message:?} {cause:?}")]
    TestError {
        test_case_name: Option<String>,
        message: Option<String>,
        cause: Option<Box<dyn Debug>>,
    },

    #[error("FAIL: {causes:?}")]
    MultipleTestsFailed { causes: Vec<IonHashTestError> },
}

mod unknown_symbol_text_tests {
    use super::*;
    use ion_rs::Symbol;

    #[test]
    fn test_unknown_symbol_text() {
        let unknown_symbol = Element::from(Symbol::unknown_text());
        let digest = IdentityDigest::hash_element(&unknown_symbol).unwrap();

        let expected_string = format!("{:02x?}", &[0x0b, 0x71, 0x0e]);
        let actual_string = format!("{:02x?}", without_trailing_zeros(&digest[..]));
        assert_eq!(expected_string, actual_string)
    }

    #[test]
    fn test_unknown_field_name_text() {
        let fields_itr = vec![(Symbol::unknown_text(), Element::from(1))];
        let struct_ = Struct::from_iter(fields_itr);
        let element = Element::from(struct_);

        let digest = IdentityDigest::hash_element(&element).unwrap();

        let expected_string = format!(
            "{:02x?}",
            &[0x0b, 0xd0, 0x0c, 0x0b, 0x71, 0x0c, 0x0e, 0x0c, 0x0b, 0x20, 0x01, 0x0c, 0x0e, 0x0e]
        );
        let actual_string = format!("{:02x?}", without_trailing_zeros(&digest[..]));
        assert_eq!(expected_string, actual_string)
    }

    #[test]
    fn test_unknown_annotation_text() {
        let mut element = Element::read_one("{}".as_bytes()).unwrap();
        element = element.with_annotations(vec![Symbol::unknown_text()]);
        let digest = IdentityDigest::hash_element(&element).unwrap();

        let expected_string = format!(
            "{:02x?}",
            &[0x0b, 0xe0, 0x0b, 0x71, 0x0e, 0x0b, 0xd0, 0x0e, 0x0e]
        );
        let actual_string = format!("{:02x?}", without_trailing_zeros(&digest[..]));
        assert_eq!(expected_string, actual_string)
    }
}
