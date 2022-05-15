// Copyright Amazon.com, Inc. or its affiliates.

use ion_rs::result::{decoding_error, IonError, IonResult};
use ion_rs::value::owned::OwnedElement;
use ion_rs::value::reader::{element_reader, ElementReader};
use ion_rs::value::writer::{ElementWriter, Format, SliceElementWriter, TextKind};
use ion_rs::value::{Element, Sequence, SymbolToken};
use pretty_hex::*;
use std::fs::read;
use std::path::MAIN_SEPARATOR as PATH_SEPARATOR;
use test_generator::test_resources;

/// Buffer size for our writing tests around round-tripping
const WRITE_BUF_LENGTH: usize = 16 * 1024 * 1024;

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
        .map(|p| p.replace("/", &PATH_SEPARATOR.to_string()))
        .any(|p| p == file_name)
}

// Statically defined arrays containing test file paths to skip in various contexts.
type SkipList = &'static [&'static str];

trait ElementApi {
    type ElementReader: ElementReader;

    fn global_skip_list() -> SkipList;
    fn read_one_equivs_skip_list() -> SkipList;
    fn round_trip_skip_list() -> SkipList;
    fn equivs_skip_list() -> SkipList;
    fn non_equivs_skip_list() -> SkipList;

    fn make_reader() -> Self::ElementReader;

    // TODO: These are currently all ion-c specific method signatures. SliceElementWriter takes a
    //       lifetime, so we can't specify it as an associated type until GATs is stable. That's
    //       ok for the moment because we don't have a native ElementWriter to test yet.
    fn make_text_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter>;
    fn make_pretty_text_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter>;
    fn make_binary_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter>;

    /// Asserts the given elements can be round-tripped and equivalent, then returns the new elements.
    fn assert_round_trip<F>(
        source_elements: &Vec<OwnedElement>,
        make_writer: F,
    ) -> IonResult<Vec<OwnedElement>>
    where
        F: FnOnce(&mut [u8]) -> IonResult<SliceElementWriter>,
    {
        let mut buf = vec![0u8; WRITE_BUF_LENGTH];
        let mut writer = make_writer(&mut buf)?;
        writer.write_all(source_elements)?;
        let output = writer.finish()?;
        let new_elements = element_reader().read_all(output)?;
        assert_eq!(*source_elements, new_elements, "{:?}", output.hex_dump());
        Ok(new_elements)
    }

    fn assert_three_way_round_trip<F1, F2>(
        file_name: &str,
        first_writer: F1,
        second_writer: F2,
    ) -> IonResult<()>
    where
        F1: FnOnce(&mut [u8]) -> IonResult<SliceElementWriter>,
        F2: FnOnce(&mut [u8]) -> IonResult<SliceElementWriter>,
    {
        let source_elements = Self::read_file(&Self::make_reader(), file_name)?;
        if contains_path(Self::round_trip_skip_list(), file_name) {
            return Ok(());
        }
        let first_write_elements = Self::assert_round_trip(&source_elements, first_writer)?;
        let second_write_elements = Self::assert_round_trip(&first_write_elements, second_writer)?;
        assert_eq!(source_elements, second_write_elements);
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
            println!("IGNORING: {}", file_name);
        } else {
            println!("TESTING: {}", file_name);
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
    fn read_group_embedded<R, S, F>(reader: &R, raw_group: &S, group_assert: &F) -> IonResult<()>
    where
        R: ElementReader,
        S: Sequence,
        F: Fn(&Vec<OwnedElement>, &Vec<OwnedElement>),
    {
        let group_res: IonResult<Vec<_>> = raw_group
            .iter()
            .map(|elem| reader.read_all(elem.as_str().unwrap().as_bytes()))
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
        reader: Self::ElementReader,
        file_name: &str,
        value_assert: F1,
        group_assert: F2,
    ) -> IonResult<()>
    where
        F1: Fn(&OwnedElement, &OwnedElement),
        F2: Fn(&Vec<OwnedElement>, &Vec<OwnedElement>),
    {
        let group_lists = Self::read_file(&reader, file_name)?;
        for group_list in group_lists.iter() {
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
                    for this in group.iter() {
                        for that in group.iter() {
                            value_assert(this, that);
                        }
                    }
                }
                _ => {
                    return decoding_error(format!(
                        "Expected a sequence for group: {:?}",
                        group_list
                    ))
                }
            };
        }
        Ok(())
    }

    fn read_file(reader: &Self::ElementReader, file_name: &str) -> IonResult<Vec<OwnedElement>> {
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
                                assert_eq!(elems[0], elem)
                            }
                        }
                        Err(e) => panic!("Expected element {:?}, got {:?}", elems, e),
                    }
                } else {
                    match single_result {
                        Ok(elem) => panic!(
                            "Did not expect element for duplicates: {:?}, {:?}",
                            elems, elem
                        ),
                        Err(e) => match e {
                            IonError::DecodingError { description: _ } => (),
                            other => {
                                panic!("Got an error we did not expect for duplicates: {:?}", other)
                            }
                        },
                    }
                }
            }
            Err(_) => assert!(
                single_result.is_err(),
                "Expected error from read_one: {:?}",
                single_result
            ),
        };

        result
    }
}

/// Reads the data in `file_name` and writes it to an in-memory buffer (`b1`) using the writer provided
/// by `first_writer_provider`. Then reads the data from the `b1` and writes it to another buffer (`b2`)
/// using the writer provided by `second_writer_provider`. Finally, compares the data read from `b2`
/// to the data in `file_name` and asserts that they are equivalent, demonstrating that no data has
/// been lost.
fn good_roundtrip<E: ElementApi, F1, F2>(
    _element_api: E,
    skip_list: &[&str],
    file_name: &str,
    first_writer_provider: F1,
    second_writer_provider: F2,
) where
    F1: FnOnce(&mut [u8]) -> IonResult<SliceElementWriter>,
    F2: FnOnce(&mut [u8]) -> IonResult<SliceElementWriter>,
{
    E::assert_file(skip_list, file_name, || {
        E::assert_three_way_round_trip(file_name, first_writer_provider, second_writer_provider)
    });
}

fn good_roundtrip_text_binary<E: ElementApi>(element_api: E, file_name: &str) {
    good_roundtrip(
        element_api,
        E::global_skip_list(),
        file_name,
        |slice| E::make_text_writer(slice),
        |slice| E::make_binary_writer(slice),
    )
}

fn good_roundtrip_binary_text<E: ElementApi>(element_api: E, file_name: &str) {
    good_roundtrip(
        element_api,
        E::global_skip_list(),
        file_name,
        |slice| E::make_binary_writer(slice),
        |slice| E::make_text_writer(slice),
    )
}

fn good_roundtrip_text_pretty<E: ElementApi>(element_api: E, file_name: &str) {
    good_roundtrip(
        element_api,
        E::global_skip_list(),
        file_name,
        |slice| E::make_text_writer(slice),
        |slice| E::make_pretty_text_writer(slice),
    )
}

fn good_roundtrip_pretty_text<E: ElementApi>(element_api: E, file_name: &str) {
    good_roundtrip(
        element_api,
        E::global_skip_list(),
        file_name,
        |slice| E::make_pretty_text_writer(slice),
        |slice| E::make_text_writer(slice),
    )
}

fn good_roundtrip_pretty_binary<E: ElementApi>(element_api: E, file_name: &str) {
    good_roundtrip(
        element_api,
        E::global_skip_list(),
        file_name,
        |slice| E::make_pretty_text_writer(slice),
        |slice| E::make_binary_writer(slice),
    )
}

fn good_roundtrip_binary_pretty<E: ElementApi>(element_api: E, file_name: &str) {
    good_roundtrip(
        element_api,
        E::global_skip_list(),
        file_name,
        |slice| E::make_binary_writer(slice),
        |slice| E::make_pretty_text_writer(slice),
    )
}

fn bad<E: ElementApi>(_element_api: E, file_name: &str) {
    E::assert_file(E::global_skip_list(), file_name, || {
        match E::read_file(&E::make_reader(), file_name) {
            Ok(items) => panic!("Expected error, got: {:?}", items),
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
            |this, that| assert_eq!(this, that),
            |this_group, that_group| assert_eq!(this_group, that_group),
        )
    });
}

fn non_equivs<E: ElementApi>(_element_api: E, file_name: &str) {
    let skip_list = concat(E::global_skip_list(), E::non_equivs_skip_list());
    E::assert_file(&skip_list[..], file_name, || {
        E::read_group(
            E::make_reader(),
            file_name,
            |this, that| {
                if std::ptr::eq(this, that) {
                    assert_eq!(this, that);
                } else {
                    assert_ne!(this, that);
                }
            },
            |this_group, that_group| {
                if std::ptr::eq(this_group, that_group) {
                    assert_eq!(this_group, that_group);
                } else {
                    assert_ne!(this_group, that_group);
                }
            },
        )
    });
}

#[cfg(test)]
mod ion_c_element_api_tests {
    use super::*;
    use ion_rs::value::ion_c_reader::IonCElementReader;
    use ion_rs::value::reader::ion_c_element_reader;

    struct IonCElementApi {}

    /// Files that should always be skipped for some reason.
    const GLOBAL_SKIP_LIST: SkipList = &[
        // ion-c does not currently support these
        // see: https://github.com/amzn/ion-c/blob/master/test/gather_vectors.cpp
        "ion-tests/iontestdata/good/utf16.ion",
        "ion-tests/iontestdata/good/utf32.ion",
        "ion-tests/iontestdata/good/subfieldVarUInt32bit.ion",
        "ion-tests/iontestdata/good/typecodes/T6-large.10n",
        "ion-tests/iontestdata/good/typecodes/T7-large.10n",
        "ion-tests/iontestdata/good/typecodes/type_6_length_0.10n",
        // these appear to have a problem specific to how we're calling ion-c (amzn/ion-rust#218)
        "ion-tests/iontestdata/good/item1.10n",
        "ion-tests/iontestdata/good/subfieldVarInt.ion",
        // these are symbols with unknown text (amzn/ion-rust#219)
        "ion-tests/iontestdata/good/symbolExplicitZero.10n",
        "ion-tests/iontestdata/good/symbolImplicitZero.10n",
        "ion-tests/iontestdata/good/symbolZero.ion",
        "ion-tests/iontestdata/good/typecodes/T7-small.10n",
    ];

    /// Files that should not be tested for equivalence with read_one against read_all
    const READ_ONE_EQUIVS_SKIP_LIST: SkipList = &[
        // we need a structural equality (IonEq) for these (amzn/ion-rust#220)
        "ion-tests/iontestdata/good/floatSpecials.ion",
    ];

    /// Files that should not be tested for equivalence in round-trip testing
    const ROUND_TRIP_SKIP_LIST: SkipList = &[
        // we need a structural equality (IonEq) for these (amzn/ion-rust#220)
        "ion-tests/iontestdata/good/float32.10n",
        "ion-tests/iontestdata/good/floatSpecials.ion",
        "ion-tests/iontestdata/good/non-equivs/floats.ion",
        // appears to be a bug with Ion C or ion-c-sys (specifically binary) (amzn/ion-rust#235)
        "ion-tests/iontestdata/good/equivs/bigInts.ion",
        "ion-tests/iontestdata/good/subfieldUInt.ion",
    ];

    /// Files that should only be skipped in equivalence file testing
    const EQUIVS_SKIP_LIST: SkipList = &[];

    /// Files that should only be skipped in non-equivalence file testing
    const NON_EQUIVS_SKIP_LIST: SkipList = &[
        // we need a structural equality (IonEq) for these (amzn/ion-rust#220)
        "ion-tests/iontestdata/good/non-equivs/decimals.ion",
        "ion-tests/iontestdata/good/non-equivs/floatsVsDecimals.ion",
        "ion-tests/iontestdata/good/non-equivs/floats.ion",
        // these have symbols with unknown text (amzn/ion-rust#219)
        "ion-tests/iontestdata/good/non-equivs/symbolTablesUnknownText.ion",
    ];

    impl ElementApi for IonCElementApi {
        type ElementReader = IonCElementReader;

        fn global_skip_list() -> SkipList {
            GLOBAL_SKIP_LIST
        }

        fn read_one_equivs_skip_list() -> SkipList {
            READ_ONE_EQUIVS_SKIP_LIST
        }

        fn round_trip_skip_list() -> SkipList {
            ROUND_TRIP_SKIP_LIST
        }

        fn equivs_skip_list() -> SkipList {
            EQUIVS_SKIP_LIST
        }

        fn non_equivs_skip_list() -> SkipList {
            NON_EQUIVS_SKIP_LIST
        }

        fn make_reader() -> Self::ElementReader {
            ion_c_element_reader()
        }

        fn make_text_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter> {
            Format::Text(TextKind::Compact).element_writer_for_slice(buffer)
        }

        fn make_pretty_text_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter> {
            Format::Text(TextKind::Pretty).element_writer_for_slice(buffer)
        }

        fn make_binary_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter> {
            Format::Binary.element_writer_for_slice(buffer)
        }
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn ion_c_good_roundtrip_text_binary(file_name: &str) {
        good_roundtrip_text_binary(IonCElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn ion_c_good_roundtrip_binary_text(file_name: &str) {
        good_roundtrip_binary_text(IonCElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn ion_c_good_roundtrip_text_pretty(file_name: &str) {
        good_roundtrip_text_pretty(IonCElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn ion_c_good_roundtrip_pretty_text(file_name: &str) {
        good_roundtrip_pretty_text(IonCElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn ion_c_good_roundtrip_pretty_binary(file_name: &str) {
        good_roundtrip_pretty_binary(IonCElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn ion_c_good_roundtrip_binary_pretty(file_name: &str) {
        good_roundtrip_binary_pretty(IonCElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/bad/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/bad/**/*.10n")]
    fn ion_c_bad(file_name: &str) {
        bad(IonCElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.10n")]
    fn ion_c_equivs(file_name: &str) {
        equivs(IonCElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.ion")]
    // no binary files exist and the macro doesn't like empty globs...
    // see frehberg/test-generator#12
    //#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.10n")]
    fn ion_c_non_equivs(file_name: &str) {
        non_equivs(IonCElementApi {}, file_name)
    }
}

#[cfg(test)]
mod native_element_tests {
    use super::*;
    use ion_rs::value::native_reader::NativeElementReader;
    use ion_rs::value::reader::native_element_reader;

    struct NativeElementApi {}

    impl ElementApi for NativeElementApi {
        type ElementReader = NativeElementReader;

        fn global_skip_list() -> SkipList {
            &[
                // The text reader does not validate whether a clob's text contains unescaped
                // characters outside of the displayable ASCII range.
                "ion-tests/iontestdata/bad/clobWithNonAsciiCharacter.ion",
                "ion-tests/iontestdata/bad/clobWithNonAsciiCharacterMultiline.ion",
                "ion-tests/iontestdata/bad/clobWithNullCharacter.ion",
                "ion-tests/iontestdata/bad/clobWithValidUtf8ButNonAsciiCharacter.ion",
                // The binary reader does not check whether nested values are longer than their
                // parent container.
                "ion-tests/iontestdata/bad/listWithValueLargerThanSize.10n",
                // These fail because non-displayable ASCII control characters are valid utf-8. A
                // separate check is needed to confirm that raw control characters only show up
                // as escape sequences.
                "ion-tests/iontestdata/bad/longStringRawControlCharacter.ion",
                "ion-tests/iontestdata/bad/stringRawControlCharacter.ion",
                "ion-tests/iontestdata/bad/stringWithEol.ion",
                // ROUND TRIP
                // These two tests fail because in most contexts, `NaN != NaN`, so Float(nan) != Float(nan).
                // We need a structural equality (IonEq) for this (amzn/ion-rust#220)
                "ion-tests/iontestdata/good/equivs/floats.ion",
                "ion-tests/iontestdata/good/floatSpecials.ion",
                // ---
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
                "ion-tests/iontestdata/good/innerVersionIdentifiers.ion",
                // Requires importing shared symbol tables
                "ion-tests/iontestdata/good/item1.10n",
                "ion-tests/iontestdata/good/localSymbolTableImportZeroMaxId.ion",
                "ion-tests/iontestdata/good/notVersionMarkers.ion",
                // Requires importing shared symbol tables
                "ion-tests/iontestdata/good/testfile35.ion",
                // This test has a Decimal with an enormous exponent. We'd need to change
                // DecodedInt to store an Integer instead of an i64.
                "ion-tests/iontestdata/good/typecodes/T5.10n",
                // These files are encoded in utf16 and utf32; the reader currently assumes utf8.
                "ion-tests/iontestdata/good/utf16.ion",
                "ion-tests/iontestdata/good/utf32.ion",
                // EQUIVS
                "ion-tests/iontestdata/good/equivs/utf8/stringUtf8.ion",
                // NON-EQUIVS
                "ion-tests/iontestdata/good/non-equivs/decimals.ion",
                "ion-tests/iontestdata/good/non-equivs/floats.ion",
                "ion-tests/iontestdata/good/non-equivs/floatsVsDecimals.ion",
                "ion-tests/iontestdata/good/non-equivs/localSymbolTableWithAnnotations.ion",
                "ion-tests/iontestdata/good/non-equivs/symbolTablesUnknownText.ion",
            ]
        }

        fn read_one_equivs_skip_list() -> SkipList {
            &[]
        }

        fn round_trip_skip_list() -> SkipList {
            &[
                "ion-tests/iontestdata/good/decimal_zeros.ion",
                "ion-tests/iontestdata/good/decimalNegativeZeroDot.10n",
                "ion-tests/iontestdata/good/decimalNegativeZeroDotZero.10n",
                "ion-tests/iontestdata/good/equivs/textNewlines.ion",
                "ion-tests/iontestdata/good/equivs/timestampFractions.10n",
                "ion-tests/iontestdata/good/equivs/timestampsLargeFractionalPrecision.ion",
                "ion-tests/iontestdata/good/equivs/utf8/stringUtf8.ion",
                "ion-tests/iontestdata/good/equivs/zeroDecimals.ion",
                "ion-tests/iontestdata/good/float_values.ion",
                "ion-tests/iontestdata/good/float_zeros.ion",
                "ion-tests/iontestdata/good/float32.10n",
                "ion-tests/iontestdata/good/floatDblMin.ion",
                "ion-tests/iontestdata/good/floatSpecials.ion",
                "ion-tests/iontestdata/good/innerVersionIdentifiers.ion",
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
                "ion-tests/iontestdata/good/testfile23.ion",
                "ion-tests/iontestdata/good/testfile31.ion",
                "ion-tests/iontestdata/good/testfile35.ion",
                "ion-tests/iontestdata/good/timestamp/equivTimeline/timestamps.ion",
                "ion-tests/iontestdata/good/timestamp/timestamp2011-02-20T19_30_59_100-08_00.10n",
                "ion-tests/iontestdata/good/typecodes/T5.10n",
                "ion-tests/iontestdata/good/typecodes/T6-large.10n",
                "ion-tests/iontestdata/good/utf16.ion",
                "ion-tests/iontestdata/good/utf32.ion",
            ]
        }

        fn equivs_skip_list() -> SkipList {
            &[
                "ion-tests/iontestdata/good/equivs/clobNewlines.ion",
                "ion-tests/iontestdata/good/equivs/localSymbolTableAppend.ion",
                "ion-tests/iontestdata/good/equivs/localSymbolTableNullSlots.ion",
                "ion-tests/iontestdata/good/equivs/nonIVMNoOps.ion",
                "ion-tests/iontestdata/good/equivs/textNewlines.ion",
                "ion-tests/iontestdata/good/equivs/timestampFractions.10n",
                "ion-tests/iontestdata/good/equivs/utf8/stringUtf8.ion",
            ]
        }

        fn non_equivs_skip_list() -> SkipList {
            &[]
        }

        fn make_reader() -> Self::ElementReader {
            native_element_reader()
        }

        // TODO: These methods return an ion-c writer for the time being.
        //       Once we have a native ElementWriter impl and the reader is passing (most of) its
        //       ion-tests, we can modify this.
        fn make_text_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter> {
            Format::Text(TextKind::Compact).element_writer_for_slice(buffer)
        }

        fn make_pretty_text_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter> {
            Format::Text(TextKind::Pretty).element_writer_for_slice(buffer)
        }

        fn make_binary_writer(buffer: &mut [u8]) -> IonResult<SliceElementWriter> {
            Format::Binary.element_writer_for_slice(buffer)
        }
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn native_good_roundtrip_text_binary(file_name: &str) {
        good_roundtrip_text_binary(NativeElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn native_good_roundtrip_binary_text(file_name: &str) {
        good_roundtrip_binary_text(NativeElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn native_good_roundtrip_text_pretty(file_name: &str) {
        good_roundtrip_text_pretty(NativeElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn native_good_roundtrip_pretty_text(file_name: &str) {
        good_roundtrip_pretty_text(NativeElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn native_good_roundtrip_pretty_binary(file_name: &str) {
        good_roundtrip_pretty_binary(NativeElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/**/*.10n")]
    fn native_good_roundtrip_binary_pretty(file_name: &str) {
        good_roundtrip_binary_pretty(NativeElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/bad/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/bad/**/*.10n")]
    fn native_bad(file_name: &str) {
        bad(NativeElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.ion")]
    #[test_resources("ion-tests/iontestdata/good/equivs/**/*.10n")]
    fn native_equivs(file_name: &str) {
        equivs(NativeElementApi {}, file_name)
    }

    #[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.ion")]
    // no binary files exist and the macro doesn't like empty globs...
    // see frehberg/test-generator#12
    //#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.10n")]
    fn native_non_equivs(file_name: &str) {
        non_equivs(NativeElementApi {}, file_name)
    }
}
