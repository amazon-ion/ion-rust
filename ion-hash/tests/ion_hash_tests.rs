// Copyright Amazon.com, Inc. or its affiliates.

use digest::Digest;
use ion_hash;
use ion_rs::result::{illegal_operation, IonResult};
use ion_rs::value::reader::{element_reader, ElementReader};
use ion_rs::value::*;
use sha2::Sha256;
use std::fs::read;

#[test]
fn ion_hash_tests() -> IonResult<()> {
    test_file("tests/ion_hash_tests.ion")
}

fn test_file(file_name: &str) -> IonResult<()> {
    let data = read(file_name)?;
    let elems = element_reader().read_all(&data)?;
    test_all(elems)
}

fn test_all<E: Element>(elems: Vec<E>) -> IonResult<()> {
    for case in &elems {
        let case = case.as_struct().expect("test cases are structs");
        // TODO: support binary ion
        let ion = case.get("ion").expect("test cases have an `ion` value");
        let expect = case
            .get("expect")
            .expect("test cases have an `expect` value");
        test_case(ion, expect)?;
    }

    Ok(())
}

fn test_case<E: Element>(ion: &E, strukt: &E) -> IonResult<()> {
    let test_case_name = test_case_name(ion)?;
    let strukt = strukt.as_struct().expect("`expect` should be a struct");
    let expected = compute_expected_hash(strukt)?;
    let result = ion_hash::sha256(ion)?;
    assert_eq!(
        &expected[..],
        &result[..],
        "test case {} failed",
        test_case_name
    );

    Ok(())
}

fn compute_expected_hash<S: Struct + ?Sized>(strukt: &S) -> IonResult<Vec<u8>> {
    let identity = strukt
        .get("identity")
        .expect("`expect` should have a field called `identity`")
        .as_sequence()
        .expect("`identity` should be a sexp");

    // The Ion hash tests are written as a series of mock style expectations.
    // Consider the first test:
    //
    //     { ion:null, expect:{
    //        identity:(update::(0x0b) update::(0x0f) update::(0x0e) digest::(0x0b 0x0f 0x0e)),
    //
    // The 'identity' case says that the underlying hasher should receive 3x
    // calls to the `update` method (with the specified bytes) and then 1x call
    // to the `digest` method.
    //
    // The nice thing about these tests is they help with debugging. If an
    // implementation got the wrong answer, you can dig through how it got there
    // and see which steps were wrong.
    //
    // The Rust `digest` trait is organized around fixed size hashers. This
    // makes implementing an identity hasher tricky (since the result is
    // variable sized).
    //
    // So, instead of doing mock-style assertions, we instead use a real hasher.
    // We use the expectations to drive that hasher to produce a result, and
    // remember it. Then we take the Ion hash (using the same algorithm) and it
    // should have that same result!
    let mut preflight = Sha256::new();
    if let Some(ref expectation) = identity.iter().last() {
        let method = expectation
            .annotations()
            .next()
            .expect("identity sexps have one annotation")
            .text()
            .expect("identity sexps contain elements with text annotations");

        let bytes: Vec<_> = expectation
            .as_sequence()
            .expect("identity sexps have sub-sexps")
            .iter()
            .map(|it| it.as_i64().expect("sub-exps have bytes") as u8)
            .collect();

        match method {
            "digest" | "final_digest" => preflight.update(bytes),
            _ => illegal_operation(format!(
                "the last expectation should be a `digest` or `final_digest`, but as {}",
                method,
            ))?,
        }
    } else {
        illegal_operation("there were no expectations in this test case")?;
    }

    Ok(preflight.finalize().to_vec())
}

/// Test cases may be annotated with a test name. Or, not! If they aren't, the
/// name of the test is the Ion text representation of the input value.
// TODO: Once `dumper` lands, use it to generate test names for un-annotated
// test cases. For now, they're simply numbered.
fn test_case_name<E: Element>(ion: &E) -> IonResult<String> {
    let annotations: Vec<_> = ion
        .annotations()
        .map(|it| it.text().unwrap().to_string())
        .collect();
    match &annotations[..] {
        [] => {
            use ion_rs::value::writer::{ElementWriter, Format, TextKind};

            let mut buf = vec![0u8; 4096];
            let mut writer = Format::Text(TextKind::Compact).element_writer_for_slice(&mut buf)?;
            writer.write(ion)?;
            let result = writer.finish()?;

            Ok(String::from_utf8_lossy(result).to_string())
        }
        [single] => Ok(single.clone()),
        _ => unimplemented!(),
    }
}
