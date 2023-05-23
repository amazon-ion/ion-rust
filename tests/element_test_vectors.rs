// Copyright Amazon.com, Inc. or its affiliates.

use ion_rs::element::reader::ElementReader;
use ion_rs::element::writer::{ElementWriter, Format, TextKind};
use ion_rs::element::{Element, Sequence};
use ion_rs::result::{decoding_error, IonError, IonResult};
use ion_rs::{BinaryWriterBuilder, IonData, IonWriter, TextWriterBuilder};

use std::fs::read;
use std::path::MAIN_SEPARATOR as PATH_SEPARATOR;
use test_generator::test_resources;

/// Concatenates two slices of string slices together.
#[inline]
fn concat<'a>(left: &[&'a str], right: &[&'a str]) -> Vec<&'a str> {
    left.iter().chain(right.iter()).copied().collect()
}

/// Determines if the given file name is in the paths list.  This deals with platform
/// path separator differences from '/' separators in the path list.
#[inline]
fn contains_path(paths: &[&str], file_name: &str) -> bool {
    paths
        .iter()
        // TODO construct the paths in a not so hacky way
        .map(|p| p.replace('/', &PATH_SEPARATOR.to_string()))
        .any(|p| p == file_name)
}

// Statically defined arrays containing test file paths to skip in various contexts.
type SkipList = &'static [&'static str];

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
fn serialize(format: Format, elements: &[Element]) -> IonResult<Vec<u8>> {
    let mut buffer = Vec::with_capacity(2048);
    match format {
        Format::Text(kind) => {
            let mut writer = match kind {
                TextKind::Compact => TextWriterBuilder::default().build(&mut buffer),
                TextKind::Lines => TextWriterBuilder::lines().build(&mut buffer),
                TextKind::Pretty => TextWriterBuilder::pretty().build(&mut buffer),
            }?;
            writer.write_elements(elements)?;
            writer.flush()?;
        }
        Format::Binary => {
            let mut binary_writer = BinaryWriterBuilder::new().build(&mut buffer)?;
            binary_writer.write_elements(elements)?;
            binary_writer.flush()?;
        }
    };
    Ok(buffer)
}

trait ElementApi {
    type ElementReader<'a>: ElementReader;

    fn global_skip_list() -> SkipList;
    fn read_one_equivs_skip_list() -> SkipList;
    fn round_trip_skip_list() -> SkipList;
    fn equivs_skip_list() -> SkipList;
    fn non_equivs_skip_list() -> SkipList;

    fn make_reader(data: &[u8]) -> IonResult<Self::ElementReader<'_>>;

    /// Asserts the given elements can be round-tripped and equivalent, then returns the new elements.
    fn assert_round_trip(
        source_elements: &Vec<Element>,
        format: Format,
    ) -> IonResult<Vec<Element>> {
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

    fn not_eq_error_message(e1: &Vec<Element>, e2: &Vec<Element>) -> String {
        if e1.len() != e2.len() {
            return format!("e1 has {} elements, e2 has {} elements", e1.len(), e2.len());
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

    /// Parses the elements of a given sequence as text Ion data and tests a grouping on the read
    /// documents.
    ///
    /// For example, for the given group:
    ///
    /// ```plain
    /// embedded_documents::(
    ///   "a b c"
    ///   "'a' 'b' 'c'"
    /// )
    /// ```
    ///
    /// This will parse each string as a [`Vec`] of [`Element`] and apply the `group_assert` function
    /// for every pair of the parsed data including the identity case (a parsed document is
    /// compared against itself).
    fn read_group_embedded<F>(raw_group: &Sequence, group_assert: &F) -> IonResult<()>
    where
        F: Fn(&Vec<Element>, &Vec<Element>),
    {
        let group_res: IonResult<Vec<_>> = raw_group
            .elements()
            .map(|elem| {
                Self::make_reader(elem.as_text().unwrap().as_bytes())?
                    .elements()
                    .collect()
            })
            .collect();
        let group = group_res?;
        for this in group.iter() {
            for that in group.iter() {
                group_assert(this, that);
            }
        }
        Ok(())
    }

    /// Parses a document that has top-level `list`/`sexp` values that represent a *group*.
    /// If this top-level value is annotated with `embedded_documents`, then [`read_group_embedded`]
    /// is executed for that grouping.  Otherwise, the `value_assert` function is invoked for
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
    fn read_group<F1, F2>(file_name: &str, value_assert: F1, group_assert: F2) -> IonResult<()>
    where
        // group index, value 1 index, value 1, value 2 index, value 2
        F1: Fn(usize, usize, &Element, usize, &Element),
        F2: Fn(&Vec<Element>, &Vec<Element>),
    {
        let group_lists = Self::read_file(file_name)?;
        for (group_index, group_list) in group_lists.iter().enumerate() {
            // every grouping set is a list/sexp
            // look for the embedded annotation to parse/test as the underlying value
            let is_embedded = group_list.annotations().contains("embedded_documents");
            match (group_list.as_sequence(), is_embedded) {
                (Some(group), true) => {
                    Self::read_group_embedded(group, &group_assert)?;
                }
                (Some(group), false) => {
                    for (this_index, this) in group.elements().enumerate() {
                        for (that_index, that) in group.elements().enumerate() {
                            value_assert(group_index, this_index, this, that_index, that);
                        }
                    }
                }
                _ => {
                    return decoding_error(format!("Expected a sequence for group: {group_list:?}"))
                }
            };
        }
        Ok(())
    }

    fn read_file(file_name: &str) -> IonResult<Vec<Element>> {
        let data = read(file_name)?;
        let mut reader = Self::make_reader(&data)?;
        let result: IonResult<Vec<Element>> = reader.read_all_elements();

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
                                assert!(IonData::eq(&elems[0], &elem))
                            }
                        }
                        Err(e) => panic!("Expected element {elems:?}, got {e:?}"),
                    }
                } else {
                    match single_result {
                        Ok(elem) => {
                            panic!("Did not expect element for duplicates: {elems:?}, {elem:?}")
                        }
                        Err(e) => match e {
                            IonError::DecodingError { description: _ } => (),
                            other => {
                                panic!("Got an error we did not expect for duplicates: {other:?}")
                            }
                        },
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
macro_rules! good_round_trip {
    (use $ElementApiImpl:ident; $(fn $test_name:ident($format1:expr, $format2:expr);)+) => {
        mod good_round_trip {
            use super::*; $(
            #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
            #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
            fn $test_name(file_name: &str) {
                $ElementApiImpl::assert_file($ElementApiImpl::global_skip_list(), file_name, || {
                    $ElementApiImpl::assert_three_way_round_trip(file_name, $format1, $format2)
                });
            })+
        }
    };
}

fn bad<E: ElementApi>(_element_api: E, file_name: &str) {
    E::assert_file(E::global_skip_list(), file_name, || {
        match E::read_file(file_name) {
            Ok(items) => panic!("Expected error, got: {items:?}"),
            Err(_) => Ok(()),
        }
    });
}

fn equivs<E: ElementApi>(_element_api: E, file_name: &str) {
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
            |this_group, that_group| assert!(IonData::eq(this_group, that_group)),
        )
    });
}

fn non_equivs<E: ElementApi>(_element_api: E, file_name: &str) {
    let skip_list = concat(E::global_skip_list(), E::non_equivs_skip_list());
    E::assert_file(&skip_list[..], file_name, || {
        E::read_group(
            file_name,
            |group_index, this_index, this, that_index, that| {
                if std::ptr::eq(this, that) {
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
            |this_group, that_group| {
                if std::ptr::eq(this_group, that_group) {
                    assert!(
                        IonData::eq(this_group,that_group),
                        "unexpected these to be equal but they were unequal: {this_group:?} != {that_group:?}"
                    );
                } else {
                    assert!(
                        !IonData::eq(this_group,that_group),
                        "unexpected these to be unequal but they were equal: {this_group:?} == {that_group:?}"
                    );
                }
            },
        )
    });
}

#[cfg(test)]
mod impl_display_for_element_tests {
    use super::*;
    use ion_rs::TextWriterBuilder;
    use std::fs::read;

    const TO_STRING_SKIP_LIST: &[&str] = &[
        // These tests have shared symbol table imports in them, which the Reader does not
        // yet support.
        "ion-tests/iontestdata/good/subfieldInt.ion",
        "ion-tests/iontestdata/good/subfieldUInt.ion",
        "ion-tests/iontestdata/good/subfieldVarInt.ion",
        "ion-tests/iontestdata/good/subfieldVarUInt.ion",
        "ion-tests/iontestdata/good/subfieldVarUInt15bit.ion",
        "ion-tests/iontestdata/good/subfieldVarUInt16bit.ion",
        "ion-tests/iontestdata/good/subfieldVarUInt32bit.ion",
        // This test requires the reader to be able to read symbols whose ID is encoded
        // with more than 8 bytes. Having a symbol table with more than 18 quintillion
        // symbols is not very practical.
        "ion-tests/iontestdata/good/typecodes/T7-large.10n",
        "ion-tests/iontestdata/good/item1.10n",
        "ion-tests/iontestdata/good/localSymbolTableImportZeroMaxId.ion",
        "ion-tests/iontestdata/good/testfile35.ion",
        // These files are encoded in utf16 and utf32; the reader currently assumes utf8.
        "ion-tests/iontestdata/good/utf16.ion",
        "ion-tests/iontestdata/good/utf32.ion",
    ];

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn test_to_string(file_name: &str) {
        if contains_path(TO_STRING_SKIP_LIST, file_name) {
            println!("IGNORING: {file_name}");
            return;
        }

        let data = read(file_name).unwrap();
        let result: IonResult<Vec<Element>> = Element::read_all(data.as_slice());
        let elements = result.unwrap_or_else(|e| {
            panic!("Expected to be able to read Ion values for contents of file {file_name}: {e:?}")
        });

        for element in elements {
            let mut buffer = Vec::with_capacity(2048);
            let mut writer = TextWriterBuilder::default().build(&mut buffer).unwrap();
            writer.write_element(&element).unwrap();
            writer.flush().unwrap();
            drop(writer);

            let expected_string = std::str::from_utf8(buffer.as_slice()).unwrap().to_string();

            assert_eq!(element.to_string(), expected_string);
        }
    }
}

const ELEMENT_GLOBAL_SKIP_LIST: SkipList = &[
    // The binary reader does not check whether nested values are longer than their
    // parent container.
    "ion-tests/iontestdata/bad/listWithValueLargerThanSize.10n",
    // ROUND TRIP
    // These tests have shared symbol table imports in them, which the Reader does not
    // yet support.
    "ion-tests/iontestdata/good/subfieldInt.ion",
    "ion-tests/iontestdata/good/subfieldUInt.ion",
    "ion-tests/iontestdata/good/subfieldVarInt.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt15bit.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt16bit.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt32bit.ion",
    // This test requires the reader to be able to read symbols whose ID is encoded
    // with more than 8 bytes. Having a symbol table with more than 18 quintillion
    // symbols is not very practical.
    "ion-tests/iontestdata/good/typecodes/T7-large.10n",
    // ---
    // Requires importing shared symbol tables
    "ion-tests/iontestdata/good/item1.10n",
    "ion-tests/iontestdata/good/localSymbolTableImportZeroMaxId.ion",
    // Requires importing shared symbol tables
    "ion-tests/iontestdata/good/testfile35.ion",
    // These files are encoded in utf16 and utf32; the reader currently assumes utf8.
    "ion-tests/iontestdata/good/utf16.ion",
    "ion-tests/iontestdata/good/utf32.ion",
    // NON-EQUIVS
    "ion-tests/iontestdata/good/non-equivs/localSymbolTableWithAnnotations.ion",
    "ion-tests/iontestdata/good/non-equivs/symbolTablesUnknownText.ion",
];

const ELEMENT_ROUND_TRIP_SKIP_LIST: SkipList = &[
    "ion-tests/iontestdata/good/item1.10n",
    "ion-tests/iontestdata/good/localSymbolTableImportZeroMaxId.ion",
    "ion-tests/iontestdata/good/notVersionMarkers.ion",
    "ion-tests/iontestdata/good/subfieldInt.ion",
    "ion-tests/iontestdata/good/subfieldUInt.ion",
    "ion-tests/iontestdata/good/subfieldVarInt.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt15bit.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt16bit.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt32bit.ion",
    "ion-tests/iontestdata/good/utf16.ion",
    "ion-tests/iontestdata/good/utf32.ion",
];

const ELEMENT_EQUIVS_SKIP_LIST: SkipList = &[
    "ion-tests/iontestdata/good/equivs/localSymbolTableAppend.ion",
    "ion-tests/iontestdata/good/equivs/localSymbolTableNullSlots.ion",
    "ion-tests/iontestdata/good/equivs/nonIVMNoOps.ion",
];

#[cfg(test)]
mod native_element_tests {
    use super::*;
    use ion_rs::{Reader, ReaderBuilder};

    struct NativeElementApi;

    impl ElementApi for NativeElementApi {
        type ElementReader<'a> = Reader<'a>;

        fn make_reader(data: &[u8]) -> IonResult<Reader<'_>> {
            ReaderBuilder::default().build(data)
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
        use NativeElementApi;
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

    #[test_resources("ion-tests/iontestdata/bad/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/bad/**/*.10n")]
    fn native_bad(file_name: &str) {
        bad(NativeElementApi, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.10n")]
    fn native_equivs(file_name: &str) {
        equivs(NativeElementApi, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.ion")]
    // no binary files exist and the macro doesn't like empty globs...
    // see frehberg/test-generator#12
    //#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.10n")]
    fn native_non_equivs(file_name: &str) {
        non_equivs(NativeElementApi, file_name)
    }
}

#[cfg(test)]
mod non_blocking_native_element_tests {
    use super::*;
    use ion_rs::binary::non_blocking::raw_binary_reader::RawBinaryReader;
    use ion_rs::text::non_blocking::raw_text_reader::RawTextReader;
    use ion_rs::Reader;

    struct NonBlockingNativeElementApi;

    impl ElementApi for NonBlockingNativeElementApi {
        type ElementReader<'a> = Reader<'a>;

        fn make_reader(data: &[u8]) -> IonResult<Self::ElementReader<'_>> {
            // These imports are visible as a temporary workaround.
            // See: https://github.com/amazon-ion/ion-rust/issues/484
            use ion_rs::binary::constants::v1_0::IVM;
            use ion_rs::reader::integration_testing::new_reader;
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

    #[test_resources("ion-tests/iontestdata/bad/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/bad/**/*.10n")]
    fn native_bad(file_name: &str) {
        bad(NonBlockingNativeElementApi, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.10n")]
    fn native_equivs(file_name: &str) {
        equivs(NonBlockingNativeElementApi, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.ion")]
    // no binary files exist and the macro doesn't like empty globs...
    // see frehberg/test-generator#12
    //#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.10n")]
    fn native_non_equivs(file_name: &str) {
        non_equivs(NonBlockingNativeElementApi, file_name)
    }
}

#[cfg(all(test, feature = "experimental-streaming"))]
mod token_native_element_tests {
    use super::*;
    use ion_rs::tokens::{ReaderTokenStream, TokenStreamReader};
    use ion_rs::{Reader, ReaderBuilder};

    struct TokenNativeElementApi;

    impl ElementApi for TokenNativeElementApi {
        type ElementReader<'a> = TokenStreamReader<'a, ReaderTokenStream<'a, Reader<'a>>>;

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

        fn make_reader<'a>(data: &'a [u8]) -> IonResult<Self::ElementReader<'a>> {
            let reader = ReaderBuilder::default().build(data)?;
            let tokens: ReaderTokenStream<'a, _> = reader.into();
            let token_reader: TokenStreamReader<'a, _> = tokens.into();
            Ok(token_reader)
        }
    }

    good_round_trip! {
        use TokenNativeElementApi;
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

    #[test_resources("ion-tests/iontestdata/bad/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/bad/**/*.10n")]
    fn native_bad(file_name: &str) {
        bad(TokenNativeElementApi, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.10n")]
    fn native_equivs(file_name: &str) {
        equivs(TokenNativeElementApi, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.ion")]
    // no binary files exist and the macro doesn't like empty globs...
    // see frehberg/test-generator#12
    //#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.10n")]
    fn native_non_equivs(file_name: &str) {
        non_equivs(TokenNativeElementApi, file_name)
    }
}
