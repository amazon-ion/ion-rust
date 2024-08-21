// Copyright Amazon.com, Inc. or its affiliates.
#![cfg(feature = "experimental-reader-writer")]
#![allow(dead_code)]

use std::fs::read;
use std::io;
use std::io::Read;
use std::path::MAIN_SEPARATOR_STR as PATH_SEPARATOR;

use ion_rs::v1_0;
use ion_rs::Writer;
use ion_rs::{
    Element, ElementReader, ElementWriter, Format, IonData, IonError, IonResult, SExp, Sequence,
    Symbol, Value,
};

mod detect_incomplete_text;
pub mod lazy_element_ion_tests;

/// Concatenates two slices of string slices together.
#[inline]
pub fn concat<'a>(left: &[&'a str], right: &[&'a str]) -> Vec<&'a str> {
    left.iter().chain(right.iter()).copied().collect()
}

/// Determines if the given file name is in the paths list.  This deals with platform
/// path separator differences from '/' separators in the path list.
#[inline]
pub fn contains_path(paths: &[&str], file_name: &str) -> bool {
    paths
        .iter()
        // TODO construct the paths in a not so hacky way
        .map(|p| p.replace('/', PATH_SEPARATOR))
        .any(|p| p == file_name)
}

// Statically defined arrays containing test file paths to skip in various contexts.
pub type SkipList = &'static [&'static str];

trait RoundTrip {
    /// Encodes `elements` to a buffer in the specified Ion `format` and then reads them back into
    /// a `Vec<Element>` using the provided reader.
    fn roundtrip<R: ElementReader>(
        elements: &[Element],
        format: Format,
        reader: R,
    ) -> IonResult<Vec<Element>>;
}

/// Serializes all of the given [Element]s to a `Vec<u8>` according to the
/// specified [Format].
pub fn serialize(format: Format, elements: &Sequence) -> IonResult<Vec<u8>> {
    let mut buffer = Vec::with_capacity(2048);
    match format {
        Format::Text(kind) => {
            let mut writer = Writer::new(v1_0::Text, buffer)?;
            writer.write_elements(elements)?;
            buffer = writer.close()?;
            println!(
                "Serialized as {kind:?}:\n{}",
                std::str::from_utf8(buffer.as_slice()).unwrap()
            );
        }
        Format::Binary => {
            let mut binary_writer = Writer::new(v1_0::Binary, buffer)?;
            binary_writer.write_elements(elements)?;
            buffer = binary_writer.close()?;
        }
        _ => unimplemented!("requested format '{:?}' is not supported", format),
    };
    Ok(buffer)
}

pub trait ElementApi {
    type ElementReader<'a>: ElementReader;

    fn global_skip_list() -> SkipList;
    fn read_one_equivs_skip_list() -> SkipList;
    fn round_trip_skip_list() -> SkipList;
    fn equivs_skip_list() -> SkipList;
    fn non_equivs_skip_list() -> SkipList;

    fn make_reader(data: &[u8]) -> IonResult<Self::ElementReader<'_>>;

    /// Asserts the given elements can be round-tripped and equivalent, then returns the new elements.
    fn assert_round_trip(source_elements: &Sequence, format: Format) -> IonResult<Sequence> {
        let bytes = serialize(format, source_elements)?;
        let mut reader = Self::make_reader(&bytes)?;
        let new_elements = reader.read_all_elements()?;
        assert!(
            IonData::eq(source_elements, &new_elements),
            "Roundtrip via {:?} failed: {}",
            format,
            Self::not_eq_error_message(source_elements, &new_elements)
        );
        Ok(new_elements)
    }

    fn not_eq_error_message(e1: &Sequence, e2: &Sequence) -> String {
        if e1.len() != e2.len() {
            return format!(
                "e1 has {} elements, e2 has {} elements\n{e1:?} != {e2:?}",
                e1.len(),
                e2.len()
            );
        }

        for (index, (element1, element2)) in e1.iter().zip(e2.iter()).enumerate() {
            if !IonData::eq(element1, element2) {
                return format!(
                    "The values at position #{index} were not IonEq.\ne1: {element1}\ne2: {element2}"
                );
            }
        }
        unreachable!("not_eq_error_message called, but all elements were ion_eq");
    }

    fn assert_three_way_round_trip(
        file_name: &str,
        format1: Format,
        format2: Format,
    ) -> IonResult<()> {
        let source_elements = Self::read_file(file_name)?;
        if contains_path(Self::round_trip_skip_list(), file_name) {
            return Ok(());
        }
        let first_write_elements = Self::assert_round_trip(&source_elements, format1)?;
        let second_write_elements = Self::assert_round_trip(&first_write_elements, format2)?;
        assert!(IonData::eq(&source_elements, &second_write_elements));
        Ok(())
    }

    fn assert_file<T, F: FnOnce() -> IonResult<T>>(
        skip_list: &[&str],
        file_name: &str,
        asserter: F,
    ) {
        // TODO if frehberg/test-generator#7 gets implemented we could do a proper ignore

        // print the paths here either way so it is easy to copy/paste to investigate failures
        // use the --show-output argument to see it
        if contains_path(skip_list, file_name) {
            println!("IGNORING: {file_name}");
        } else {
            println!("TESTING: {file_name}");
            asserter().unwrap();
        }
    }

    /// Parses an element as text or binary Ion data and returns a Sequence containing all elements.
    ///
    /// For example, for the given group:
    ///
    /// ```plain
    /// embedded_documents::(
    ///   "a b c"
    ///   "'a' 'b' 'c'"
    ///   {{ 4AEA6u6OgYPbhnEDh7aBYYFigWNxCnELcQw= }}
    /// )
    /// ```
    fn read_embedded_doc_as_sequence(elem: &Element) -> IonResult<Sequence> {
        match elem.value() {
            Value::String(text) => Element::read_all(text.text().as_bytes()),
            Value::Blob(bytes) => Element::read_all(bytes.as_ref()),
            _ => panic!("Expected embedded document to be an Ion String or Ion Blob"),
        }
    }

    /// Parses a document that has top-level `list`/`sexp` values that represent a *group*.
    /// If this top-level value is annotated with `embedded_documents`, then all values in the group
    /// are interpreted as an embedded document, and read using [`read_embedded_doc_as_sequence`].
    /// (The returned Sequence is then wrapped in a SExp so they can be compared as Elements).
    /// After possibly handling an embedded document, `value_assert` function is invoked for
    /// every pair of values in a group including the identity case (a value in a group is compared
    /// against itself).
    ///
    /// Here is an example with two groups that might be used for equivalence testing:
    ///
    /// ```plain
    /// (name $2 'name')
    /// embedded_documents::(
    ///   "a name"
    ///   "a $2"
    ///   "'a' 'name'"
    /// )
    /// ```
    ///
    /// This would have two groups, one with direct values that will be compared and another
    /// with embedded Ion text that will be parsed and compared.
    fn read_group<F>(file_name: &str, value_assert: F) -> IonResult<()>
    where
        // group index, value 1 name/index, value 1, value 2 name/index, value 2
        F: Fn(usize, String, &Element, String, &Element),
    {
        let group_lists = Self::read_file(file_name)?;
        for (group_index, group_container) in group_lists.iter().enumerate() {
            // every grouping set is a list/sexp/struct
            // look for the embedded annotation to parse/test as the underlying value
            let is_embedded = group_container.annotations().contains("embedded_documents");
            match group_container.value() {
                Value::List(group) | Value::SExp(group) => {
                    let group = if is_embedded {
                        group
                            .iter()
                            .map(|it| Self::read_embedded_doc_as_sequence(it).unwrap())
                            .map(|it| Element::from(SExp::from(it)))
                            .collect::<Vec<_>>()
                            .into()
                    } else {
                        group.to_owned()
                    };

                    for (this_index, this) in group.elements().enumerate() {
                        for (that_index, that) in group.elements().enumerate() {
                            value_assert(
                                group_index,
                                format!("{this_index}"),
                                this,
                                format!("{that_index}"),
                                that,
                            );
                        }
                    }
                }
                Value::Struct(group) => {
                    let fields: Vec<(Symbol, Element)> = group
                        .fields()
                        .map(|(fname, value)| {
                            let value = if is_embedded {
                                let seq = Self::read_embedded_doc_as_sequence(value).unwrap();
                                Element::from(SExp::from(seq))
                            } else {
                                value.to_owned()
                            };
                            (fname.to_owned(), value)
                        })
                        .collect();

                    for (this_name, this) in &fields {
                        for (that_name, that) in &fields {
                            value_assert(
                                group_index,
                                format!("{this_name}"),
                                this,
                                format!("{that_name}"),
                                that,
                            );
                        }
                    }
                }

                _ => panic!("Expected a sequence or struct for group: {group_container:?}"),
            };
        }
        Ok(())
    }

    fn read_file(file_name: &str) -> IonResult<Sequence> {
        let data = read(file_name)?;
        let mut reader = Self::make_reader(&data)?;
        let result: IonResult<Sequence> = reader.read_all_elements();

        // do some simple single value reading tests
        let mut reader = Self::make_reader(&data)?;
        let single_result: IonResult<Element> = reader.read_one_element();

        match &result {
            Ok(elems) => {
                if elems.len() == 1 {
                    match single_result {
                        Ok(elem) => {
                            // only compare if we know equality to work
                            if !contains_path(Self::read_one_equivs_skip_list(), file_name) {
                                assert!(IonData::eq(elems.iter().next().unwrap(), &elem))
                            }
                        }
                        Err(e) => panic!("Expected element {elems:?}, got {e:?}"),
                    }
                } else {
                    match single_result {
                        Ok(elem) => {
                            panic!("Did not expect element for duplicates: {elems:?}, {elem:?}")
                        }
                        Err(IonError::Decoding(_)) => (),
                        Err(other) => {
                            panic!("Got an error we did not expect for duplicates: {other:?}")
                        }
                    }
                }
            }
            Err(_) => assert!(
                single_result.is_err(),
                "Expected error from read_one: {single_result:?}"
            ),
        };

        result
    }
}

/// Generates test cases for round-tripping Ion data between different formats.
/// The arguments to the macro are a DSL that looks somewhat like Rust code. Usage:
/// ```
/// good_round_trip! {
///     // Start by defining the implementation that is being tested.
///     use NativeElementImpl;
///     // Define some test functions—but use the actual formats rather than defining function parameters.
///     fn my_test_1(Format::Binary, Format::Text(TextKind::Compact));
///     fn my_test_2(Format::Binary, Format::Text(TextKind::Lines));
/// }
/// ```
///
/// ## The Generated Test Cases
/// Reads the data in `file_name` and writes it to an in-memory buffer (`b1`) using the writer provided
/// by `first_writer_provider`. Then reads the data from the `b1` and writes it to another buffer (`b2`)
/// using the writer provided by `second_writer_provider`. Finally, compares the data read from `b2`
/// to the data in `file_name` and asserts that they are equivalent, demonstrating that no data has
/// been lost.
#[macro_export]
macro_rules! good_round_trip {
    (use $ElementApiImpl:ident; $(fn $test_name:ident($format1:expr, $format2:expr);)+) => {
        mod good_round_trip_tests {
            use super::*; $(
            #[test_resources("ion-tests/iontestdata_1_0/good/**/*.ion")]
            //#[test_resources("ion-tests/iontestdata_1_1/good/**/*.ion")]
            #[test_resources("ion-tests/iontestdata_1_0/good/**/*.10n")]
            fn $test_name(file_name: &str) {
                $ElementApiImpl::assert_file($ElementApiImpl::global_skip_list(), file_name, || {
                    $ElementApiImpl::assert_three_way_round_trip(file_name, $format1, $format2)
                });
            })+
        }
    };
}

pub fn bad<E: ElementApi>(_element_api: E, file_name: &str) {
    E::assert_file(E::global_skip_list(), file_name, || {
        match E::read_file(file_name) {
            Ok(items) => panic!("Expected error, got: {items:?}"),
            Err(_) => Ok(()),
        }
    });
}

pub fn equivs<E: ElementApi>(_element_api: E, file_name: &str) {
    let skip_list = concat(E::global_skip_list(), E::equivs_skip_list());
    E::assert_file(&skip_list[..], file_name, || {
        E::read_group(
            file_name,
            |group_index, this_index, this, that_index, that| {
                assert!(
                    IonData::eq(this,that),
                    "in group {group_index}, index {this_index} ({this}) was not ion_eq to index {that_index} ({that})"
                )
            },
        )
    });
}

pub fn non_equivs<E: ElementApi>(_element_api: E, file_name: &str) {
    let skip_list = concat(E::global_skip_list(), E::non_equivs_skip_list());
    E::assert_file(&skip_list[..], file_name, || {
        E::read_group(
            file_name,
            |group_index, this_index, this, that_index, that| {
                if this_index == that_index {
                    assert!(
                        IonData::eq(this,that),
                        "in group {group_index}, index {this_index} ({this}) was not ion_eq to index {that_index} ({that})"
                    )
                } else {
                    assert!(
                        !IonData::eq(this,that),
                        "in group {group_index}, index {this_index} ({this}) was unexpectedly ion_eq to index {that_index} ({that})"
                    )
                }
            },
        )
    });
}

pub const ELEMENT_GLOBAL_SKIP_LIST: SkipList = &[
    // The binary reader does not check whether nested values are longer than their
    // parent container.
    "ion-tests/iontestdata_1_0/bad/listWithValueLargerThanSize.10n",
    // ROUND TRIP
    // These tests have shared symbol table imports in them, which the Reader does not
    // yet support.
    "ion-tests/iontestdata_1_0/good/subfieldVarInt.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt15bit.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt16bit.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt32bit.ion",
    // This test requires the reader to be able to read symbols whose ID is encoded
    // with more than 8 bytes. Having a symbol table with more than 18 quintillion
    // symbols is not very practical.
    "ion-tests/iontestdata_1_0/good/typecodes/T7-large.10n",
    // ---
    // Requires importing shared symbol tables
    "ion-tests/iontestdata_1_0/good/item1.10n",
    "ion-tests/iontestdata_1_0/good/localSymbolTableImportZeroMaxId.ion",
    // Requires importing shared symbol tables
    "ion-tests/iontestdata_1_0/good/testfile35.ion",
    // These files are encoded in utf16 and utf32; the reader currently assumes utf8.
    "ion-tests/iontestdata_1_0/good/utf16.ion",
    "ion-tests/iontestdata_1_0/good/utf32.ion",
    // NON-EQUIVS
    "ion-tests/iontestdata_1_0/good/non-equivs/localSymbolTableWithAnnotations.ion",
    "ion-tests/iontestdata_1_0/good/non-equivs/symbolTablesUnknownText.ion",
    // Integers outside the i128 range
    "ion-tests/iontestdata_1_0/good/intBigSize16.10n",
    "ion-tests/iontestdata_1_0/good/intBigSize256.ion",
    "ion-tests/iontestdata_1_0/good/intBigSize256.10n",
    "ion-tests/iontestdata_1_0/good/intBigSize512.ion",
    "ion-tests/iontestdata_1_0/good/intBigSize1201.10n",
    "ion-tests/iontestdata_1_0/good/equivs/bigInts.ion",
    "ion-tests/iontestdata_1_0/good/equivs/intsLargePositive3.10n",
    "ion-tests/iontestdata_1_0/good/equivs/intsLargeNegative3.10n",
];

pub const ELEMENT_ROUND_TRIP_SKIP_LIST: SkipList = &[
    "ion-tests/iontestdata_1_0/good/item1.10n",
    "ion-tests/iontestdata_1_0/good/localSymbolTableImportZeroMaxId.ion",
    "ion-tests/iontestdata_1_0/good/notVersionMarkers.ion",
    "ion-tests/iontestdata_1_0/good/subfieldInt.ion",
    "ion-tests/iontestdata_1_0/good/subfieldUInt.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarInt.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt15bit.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt16bit.ion",
    "ion-tests/iontestdata_1_0/good/subfieldVarUInt32bit.ion",
    "ion-tests/iontestdata_1_0/good/utf16.ion",
    "ion-tests/iontestdata_1_0/good/utf32.ion",
];

pub const ELEMENT_EQUIVS_SKIP_LIST: SkipList = &[
    "ion-tests/iontestdata_1_0/good/equivs/localSymbolTableAppend.ion",
    "ion-tests/iontestdata_1_0/good/equivs/localSymbolTableNullSlots.ion",
    "ion-tests/iontestdata_1_0/good/equivs/nonIVMNoOps.ion",
];

/// An implementation of `io::Read` that only yields a single byte on each
/// call to `read()`. This is used in tests to confirm that the reader's
/// data-incompleteness and retry logic will properly handle all corner
/// cases.
pub(crate) struct DataStraw<R> {
    input: R,
}

impl<R> DataStraw<R> {
    pub fn new(input: R) -> Self {
        Self { input }
    }
}

impl<R: Read> Read for DataStraw<R> {
    fn read(&mut self, buf: &mut [u8]) -> io::Result<usize> {
        let single_byte_buffer = &mut [0u8; 1];
        let bytes_read = self.input.read(single_byte_buffer)?;
        if bytes_read == 0 {
            return Ok(0);
        }
        buf[0] = single_byte_buffer[0];
        Ok(1)
    }
}
