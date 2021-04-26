// Copyright Amazon.com, Inc. or its affiliates.

use ion_rs::result::{decoding_error, IonResult};
use ion_rs::value::loader::{loader, Loader};
use ion_rs::value::owned::OwnedElement;
use ion_rs::value::{Element, Sequence, SymbolToken};
use std::fs::read;
use std::path::MAIN_SEPARATOR as PATH_SEPARATOR;
use test_generator::test_resources;

/// Files that should always be skipped for some reason.
const ALL_SKIP_LIST: &[&str] = &[
    // ion-c does not currently support these
    // see: https://github.com/amzn/ion-c/blob/master/test/gather_vectors.cpp
    "ion-tests/iontestdata/good/utf16.ion",
    "ion-tests/iontestdata/good/utf32.ion",
    "ion-tests/iontestdata/good/subfieldVarUInt32bit.ion",
    "ion-tests/iontestdata/good/typecodes/T6-large.10n",
    "ion-tests/iontestdata/good/typecodes/T7-large.10n",
    "ion-tests/iontestdata/good/typecodes/type_6_length_0.10n",
    // these appear to have a problem specific to how we're calling ion-c (amzn/ion-rust#218)
    "ion-tests/iontestdata/good/equivs/intsLargeNegative1.10n",
    "ion-tests/iontestdata/good/equivs/intsLargePositive1.10n",
    "ion-tests/iontestdata/good/intLongMaxValuePlusOne.10n",
    "ion-tests/iontestdata/good/item1.10n",
    "ion-tests/iontestdata/good/subfieldVarInt.ion",
    "ion-tests/iontestdata/good/typecodes/T2.10n",
    "ion-tests/iontestdata/good/typecodes/T3.10n",
    // these are symbols with unknown text (amzn/ion-rust#219)
    "ion-tests/iontestdata/good/symbolExplicitZero.10n",
    "ion-tests/iontestdata/good/symbolImplicitZero.10n",
    "ion-tests/iontestdata/good/symbolZero.ion",
    "ion-tests/iontestdata/good/typecodes/T7-small.10n",
];

/// Files that should only be skipped in equivalence file testing
const EQUIVS_SKIP_LIST: &[&str] = &[
    // ion-c seems to have a problem with negative binary literals (amzn/ion-c#235)
    "ion-tests/iontestdata/good/equivs/binaryInts.ion",
    "ion-tests/iontestdata/good/equivs/intsWithUnderscores.ion",
];

/// Files that should only be skipped in non-equivalence file testing
const NON_EQUIVS_SKIP_LIST: &[&str] = &[
    // we need a structural equality (IonEq) for these (amzn/ion-rust#220)
    "ion-tests/iontestdata/good/non-equivs/decimals.ion",
    "ion-tests/iontestdata/good/non-equivs/floatsVsDecimals.ion",
    "ion-tests/iontestdata/good/non-equivs/floats.ion",
    // these have symbols with unknown text (amzn/ion-rust#219)
    "ion-tests/iontestdata/good/non-equivs/symbolTablesUnknownText.ion",
    // this is a bug in our PartialEq (amzn/ion-rust#216)
    "ion-tests/iontestdata/good/non-equivs/structs.ion",
];

/// Concatenates two slices of string slices together.
#[inline]
fn concat<'a>(left: &[&'a str], right: &[&'a str]) -> Vec<&'a str> {
    left.into_iter()
        .chain(right.into_iter())
        .map(|p| *p)
        .collect()
}

fn load_file<L: Loader>(loader: &L, file_name: &str) -> IonResult<Vec<OwnedElement>> {
    // TODO have a better API that doesn't require buffering into memory everything...
    let data = read(file_name)?;
    loader.load_all(&data)
}

fn assert_file<T, F: FnOnce() -> IonResult<T>>(skip_list: &[&str], file_name: &str, asserter: F) {
    // TODO if frehberg/test-generator#7 gets implemented we could do a proper ignore

    // print the paths here either way so it is easy to copy/paste to investigate failures
    // use the --show-output argument to see it
    if skip_list
        .into_iter()
        // TODO construct the paths in a not so hacky way
        .map(|p| p.replace("/", &PATH_SEPARATOR.to_string()))
        .find(|p| p == file_name)
        .is_some()
    {
        println!("IGNORING: {}", file_name);
    } else {
        println!("TESTING: {}", file_name);
        asserter().unwrap();
    }
}

#[test_resources("ion-tests/iontestdata/good/**/*.ion")]
#[test_resources("ion-tests/iontestdata/good/**/*.10n")]
fn good(file_name: &str) {
    assert_file(ALL_SKIP_LIST, file_name, || load_file(&loader(), file_name));
}

#[test_resources("ion-tests/iontestdata/bad/**/*.ion")]
#[test_resources("ion-tests/iontestdata/bad/**/*.10n")]
fn bad(file_name: &str) {
    assert_file(ALL_SKIP_LIST, file_name, || {
        match load_file(&loader(), file_name) {
            Ok(items) => panic!("Expected error, got: {:?}", items),
            Err(_) => Ok(()),
        }
    });
}

/// Parses the elements of a given sequence as text Ion data and tests a grouping on the loaded
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
fn load_group_embedded<L, S, F>(loader: &L, raw_group: &S, group_assert: &F) -> IonResult<()>
where
    L: Loader,
    S: Sequence,
    F: Fn(&Vec<OwnedElement>, &Vec<OwnedElement>) -> (),
{
    let group_res: IonResult<Vec<_>> = raw_group
        .iter()
        .map(|elem| loader.load_all(elem.as_str().unwrap().as_bytes()))
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
/// If this top-level value is annotated with `embedded_documents`, then [`load_group_embedded`]
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
fn load_group<L, F1, F2>(
    loader: L,
    file_name: &str,
    value_assert: F1,
    group_assert: F2,
) -> IonResult<()>
where
    L: Loader,
    F1: Fn(&OwnedElement, &OwnedElement) -> (),
    F2: Fn(&Vec<OwnedElement>, &Vec<OwnedElement>) -> (),
{
    let group_lists = load_file(&loader, file_name)?;
    for group_list in group_lists.iter() {
        // every grouping set is a list/sexp
        // look for the embedded annotation to parse/test as the underlying value
        let is_embedded = group_list
            .annotations()
            .find(|annotation| annotation.text() == Some("embedded_documents"))
            .is_some();
        match (group_list.as_sequence(), is_embedded) {
            (Some(group), true) => {
                load_group_embedded(&loader, group, &group_assert)?;
            }
            (Some(group), false) => {
                for this in group.iter() {
                    for that in group.iter() {
                        value_assert(this, that);
                    }
                }
            }
            _ => return decoding_error(format!("Expected a sequence for group: {:?}", group_list)),
        };
    }
    Ok(())
}

#[test_resources("ion-tests/iontestdata/good/equivs/**/*.ion")]
#[test_resources("ion-tests/iontestdata/good/equivs/**/*.10n")]
fn equivs(file_name: &str) {
    let skip_list = concat(ALL_SKIP_LIST, EQUIVS_SKIP_LIST);
    assert_file(&skip_list[..], file_name, || {
        load_group(
            loader(),
            file_name,
            |this, that| assert_eq!(this, that),
            |this_group, that_group| assert_eq!(this_group, that_group),
        )
    });
}

#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.ion")]
// no binary files exist and the macro doesn't like empty globs...
// see frehberg/test-generator#12
//#[test_resources("ion-tests/iontestdata/good/non-equivs/**/*.10n")]
fn non_equivs(file_name: &str) {
    let skip_list = concat(ALL_SKIP_LIST, NON_EQUIVS_SKIP_LIST);
    assert_file(&skip_list[..], file_name, || {
        load_group(
            loader(),
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
