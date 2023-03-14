// Copyright Amazon.com, Inc. or its affiliates.

use ion_rs::ion_eq::IonEq;
use ion_rs::result::{decoding_error, IonError, IonResult};
use ion_rs::value::native_writer::NativeElementWriter;
use ion_rs::value::owned::{Element, IonSequence};
use ion_rs::value::reader::ElementReader;
use ion_rs::value::writer::{ElementWriter, Format, TextKind};
use ion_rs::{BinaryWriterBuilder, TextWriterBuilder};

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

// TODO: This trait exists solely for the purposes of this integration test. It allows us to paper
// over the differences in the ion-c and native Rust ElementWriter implementations.
// Once all of the tests are passing, we should work to unify their APIs.
trait RoundTrip {
    /// Encodes `elements` to a buffer in the specified Ion `format` and then reads them back into
    /// a `Vec<OwnedElement>` using the provided reader.
    fn roundtrip<R: ElementReader>(
        elements: &[Element],
        format: Format,
        reader: R,
    ) -> IonResult<Vec<Element>>;
}

/// These unit structs implement the [RoundTrip] trait and can be passed throughout the
/// integration tests to dictate which readers/writers should be used in each test.
struct NativeElementWriterApi;

impl RoundTrip for NativeElementWriterApi {
    fn roundtrip<R: ElementReader>(
        elements: &[Element],
        format: Format,
        reader: R,
    ) -> IonResult<Vec<Element>> {
        // Unlike the C writer, the Rust writer can write into a growing Vec.
        // No need for an aggressive preallocation.
        let mut buffer = Vec::with_capacity(2048);
        match format {
            Format::Text(kind) => {
                let writer = match kind {
                    TextKind::Compact => TextWriterBuilder::new().build(&mut buffer),
                    TextKind::Lines => TextWriterBuilder::lines().build(&mut buffer),
                    TextKind::Pretty => TextWriterBuilder::pretty().build(&mut buffer),
                }?;
                let mut writer = NativeElementWriter::new(writer);
                writer.write_all(elements)?;
                let _ = writer.finish()?;
            }
            Format::Binary => {
                let binary_writer = BinaryWriterBuilder::new().build(&mut buffer)?;
                let mut writer = NativeElementWriter::new(binary_writer);
                writer.write_all(elements)?;
                let _ = writer.finish()?;
            }
        };

        reader.read_all(buffer.as_slice())
    }
}

trait ElementApi {
    type ReaderApi: ElementReader;
    type RoundTripper: RoundTrip;

    fn global_skip_list() -> SkipList;
    fn read_one_equivs_skip_list() -> SkipList;
    fn round_trip_skip_list() -> SkipList;
    fn equivs_skip_list() -> SkipList;
    fn non_equivs_skip_list() -> SkipList;

    fn make_reader() -> Self::ReaderApi;

    /// Asserts the given elements can be round-tripped and equivalent, then returns the new elements.
    fn assert_round_trip(
        source_elements: &Vec<Element>,
        format: Format,
    ) -> IonResult<Vec<Element>> {
        let new_elements =
            Self::RoundTripper::roundtrip(source_elements, format, Self::make_reader())?;
        assert!(
            source_elements.ion_eq(&new_elements),
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
            if !element1.ion_eq(element2) {
                return format!(
                    "The values at position #{index} were not IonEq.\ne1: {element1:?}\ne2: {element2:?}"
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
        let source_elements = Self::read_file(&Self::make_reader(), file_name)?;
        if contains_path(Self::round_trip_skip_list(), file_name) {
            return Ok(());
        }
        let first_write_elements = Self::assert_round_trip(&source_elements, format1)?;
        let second_write_elements = Self::assert_round_trip(&first_write_elements, format2)?;
        assert!(source_elements.ion_eq(&second_write_elements));
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
    fn read_group_embedded<R, F>(
        reader: &R,
        raw_group: &dyn IonSequence,
        group_assert: &F,
    ) -> IonResult<()>
    where
        R: ElementReader,
        F: Fn(&Vec<Element>, &Vec<Element>),
    {
        let group_res: IonResult<Vec<_>> = raw_group
            .iter()
            .map(|elem| reader.read_all(elem.as_text().unwrap().as_bytes()))
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
    fn read_group<F1, F2>(
        reader: Self::ReaderApi,
        file_name: &str,
        value_assert: F1,
        group_assert: F2,
    ) -> IonResult<()>
    where
        // group index, value 1 index, value 1, value 2 index, value 2
        F1: Fn(usize, usize, &Element, usize, &Element),
        F2: Fn(&Vec<Element>, &Vec<Element>),
    {
        let group_lists = Self::read_file(&reader, file_name)?;
        for (group_index, group_list) in group_lists.iter().enumerate() {
            // every grouping set is a list/sexp
            // look for the embedded annotation to parse/test as the underlying value
            let is_embedded = group_list
                .annotations()
                .any(|annotation| annotation.text() == Some("embedded_documents"));
            match (group_list.as_sequence(), is_embedded) {
                (Some(group), true) => {
                    Self::read_group_embedded(&reader, group, &group_assert)?;
                }
                (Some(group), false) => {
                    for (this_index, this) in group.iter().enumerate() {
                        for (that_index, that) in group.iter().enumerate() {
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

    fn read_file(reader: &Self::ReaderApi, file_name: &str) -> IonResult<Vec<Element>> {
        // TODO have a better API that doesn't require buffering into memory everything...
        let data = read(file_name)?;
        let result = reader.read_all(&data);

        // do some simple single value reading tests
        let single_result = reader.read_one(&data);
        match &result {
            Ok(elems) => {
                if elems.len() == 1 {
                    match single_result {
                        Ok(elem) => {
                            // only compare if we know equality to work
                            if !contains_path(Self::read_one_equivs_skip_list(), file_name) {
                                assert!(elems[0].ion_eq(&elem))
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
        match E::read_file(&E::make_reader(), file_name) {
            Ok(items) => panic!("Expected error, got: {items:?}"),
            Err(_) => Ok(()),
        }
    });
}

fn equivs<E: ElementApi>(_element_api: E, file_name: &str) {
    let skip_list = concat(E::global_skip_list(), E::equivs_skip_list());
    E::assert_file(&skip_list[..], file_name, || {
        E::read_group(
            E::make_reader(),
            file_name,
            |group_index, this_index, this, that_index, that| {
                assert!(
                    this.ion_eq(that),
                    "in group {group_index}, index {this_index} ({this}) was not ion_eq to index {that_index} ({that})"
                )
            },
            |this_group, that_group| assert!(this_group.ion_eq(that_group)),
        )
    });
}

fn non_equivs<E: ElementApi>(_element_api: E, file_name: &str) {
    let skip_list = concat(E::global_skip_list(), E::non_equivs_skip_list());
    E::assert_file(&skip_list[..], file_name, || {
        E::read_group(
            E::make_reader(),
            file_name,
            |group_index, this_index, this, that_index, that| {
                if std::ptr::eq(this, that) {
                    assert!(
                        this.ion_eq(that),
                        "in group {group_index}, index {this_index} ({this}) was not ion_eq to index {that_index} ({that})"
                    )
                } else {
                    assert!(
                        !this.ion_eq(that),
                        "in group {group_index}, index {this_index} ({this}) was unexpectedly ion_eq to index {that_index} ({that})"
                    )
                }
            },
            |this_group, that_group| {
                if std::ptr::eq(this_group, that_group) {
                    assert!(
                        this_group.ion_eq(that_group),
                        "unexpected these to be equal but they were unequal: {this_group:?} != {that_group:?}"
                    );
                } else {
                    assert!(
                        !this_group.ion_eq(that_group),
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
    use ion_rs::value::native_writer::NativeElementWriter;
    use ion_rs::value::reader::element_reader;
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
        let result = element_reader().read_all(&data).unwrap_or_else(|_| {
            panic!("Expected to be able to read Ion values for contents of file {file_name}")
        });

        for element in result {
            let mut buffer = Vec::with_capacity(2048);
            let mut writer =
                NativeElementWriter::new(TextWriterBuilder::new().build(&mut buffer).unwrap());
            writer.write(&element).unwrap();
            writer.finish().unwrap();

            let expected_string = std::str::from_utf8(buffer.as_slice()).unwrap().to_string();

            assert_eq!(element.to_string(), expected_string);
        }
    }
}

#[cfg(test)]
mod native_element_tests {
    use super::*;
    use ion_rs::value::native_reader::NativeElementReader;

    struct NativeElementApi;

    impl ElementApi for NativeElementApi {
        type ReaderApi = NativeElementReader;
        type RoundTripper = NativeElementWriterApi;

        fn global_skip_list() -> SkipList {
            &[
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
            ]
        }

        fn read_one_equivs_skip_list() -> SkipList {
            &[]
        }

        fn round_trip_skip_list() -> SkipList {
            &[
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
                // These tests have symbols with unknown text. While the raw and system readers
                // could process these, the user-level `Reader` simply raises an `IonError`.
                // This is in keeping with the Ion spec, but causes these tests to fail.
                "ion-tests/iontestdata/good/symbolExplicitZero.10n",
                "ion-tests/iontestdata/good/symbolImplicitZero.10n",
                "ion-tests/iontestdata/good/symbolZero.ion",
            ]
        }

        fn equivs_skip_list() -> SkipList {
            &[
                "ion-tests/iontestdata/good/equivs/localSymbolTableAppend.ion",
                "ion-tests/iontestdata/good/equivs/localSymbolTableNullSlots.ion",
                "ion-tests/iontestdata/good/equivs/nonIVMNoOps.ion",
            ]
        }

        fn non_equivs_skip_list() -> SkipList {
            &[]
        }

        fn make_reader() -> Self::ReaderApi {
            NativeElementReader
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

mod non_blocking_native_element_tests {
    use super::*;
    use ion_rs::value::native_reader::NonBlockingNativeElementReader;

    struct NonBlockingNativeElementApi;

    impl ElementApi for NonBlockingNativeElementApi {
        type ReaderApi = NonBlockingNativeElementReader;
        type RoundTripper = NativeElementWriterApi;

        fn global_skip_list() -> SkipList {
            &[
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
            ]
        }

        fn read_one_equivs_skip_list() -> SkipList {
            &[]
        }

        fn round_trip_skip_list() -> SkipList {
            &[
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
                // These tests have symbols with unknown text. While the raw and system readers
                // could process these, the user-level `Reader` simply raises an `IonError`.
                // This is in keeping with the Ion spec, but causes these tests to fail.
                "ion-tests/iontestdata/good/symbolExplicitZero.10n",
                "ion-tests/iontestdata/good/symbolImplicitZero.10n",
                "ion-tests/iontestdata/good/symbolZero.ion",
            ]
        }

        fn equivs_skip_list() -> SkipList {
            &[
                "ion-tests/iontestdata/good/equivs/localSymbolTableAppend.ion",
                "ion-tests/iontestdata/good/equivs/localSymbolTableNullSlots.ion",
                "ion-tests/iontestdata/good/equivs/nonIVMNoOps.ion",
            ]
        }

        fn non_equivs_skip_list() -> SkipList {
            &[]
        }

        fn make_reader() -> Self::ReaderApi {
            NonBlockingNativeElementReader
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
