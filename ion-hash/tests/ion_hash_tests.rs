// Copyright Amazon.com, Inc. or its affiliates.

use digest::consts::U4096;
use digest::{FixedOutput, Reset, Update};
use ion_hash;
use ion_rs::result::{illegal_operation, IonResult};
use ion_rs::value::reader::{element_reader, ElementReader};
use ion_rs::value::*;
use std::fs::read;
use std::iter::FromIterator;

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
    if data.len() == 0 {
        return data;
    }

    let index = data
        .as_ref()
        .iter()
        .rposition(|byte| *byte != 0x00)
        .unwrap();

    &data[0..=index]
}

const IGNORE_LIST: &[&'static str] = &[
    // These struct tests contain types that aren't yet supported
    r#"{annotated_value:hello::{},clob:{{"hello"}},bool:false,struct:{},int:5,symbol:hello,timestamp:2017-01-01T00:00:00-00:00,list:[1,2,3],sexp:(1 2 3),float:4.9406564584124654418e-324,'null':null,string:"hello",blob:{{aGVsbG8=}},neg_int:-6,decimal:123.45}"#,
    r#"{a:{d:[1,2,3],b:{c:5}},e:6}"#,
    // Uses md5 (not identity)
    r#"{Metrics:{'Event.Catchup':[{Value:0,Unit:ms}],'FanoutCache.Time':[{Value:1,Unit:ms}]}}"#,
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

    if should_ignore(&test_case_name) {
        println!("skipping: {}", test_case_name);
        return Ok(());
    }

    // Uncomment me if you're trying to debug a panic!
    // eprintln!("running: {}", test_case_name);

    let strukt = strukt.as_struct().expect("`expect` should be a struct");
    let expected = expected_hash(strukt)?;

    let result = ion_hash::hash_element::<E, IdentityDigest>(ion)?;

    // Ignore trailing empty bytes caused by the identity digest producing a
    // variable sized result. Without this, any test failure will write lots of
    // stuff to your console which can be annoying since it takes forever.
    assert_eq!(
        format!("{:02x?}", without_trailing_zeros(&expected[..])),
        format!("{:02x?}", without_trailing_zeros(&result[..])),
        "test case {} failed",
        test_case_name
    );

    Ok(())
}

fn expected_hash<S: Struct + ?Sized>(strukt: &S) -> IonResult<Vec<u8>> {
    let identity = if let Some(identity) = strukt.get("identity") {
        identity.as_sequence().expect("`identity` should be a sexp")
    } else {
        illegal_operation("only identity tests are implemented")?
    };

    if let Some(expectation) = identity.iter().last() {
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
            "digest" | "final_digest" => return Ok(bytes),
            _ => illegal_operation(format!("unknown expectation `{}`", method))?,
        }
    } else {
        illegal_operation(format!("expected at least expectation!"))?
    }
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
