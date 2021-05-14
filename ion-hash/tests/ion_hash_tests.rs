// Copyright Amazon.com, Inc. or its affiliates.

use digest::{consts::U8, generic_array::GenericArray, Digest, Output};
use ion_hash::{self, IonHasher};
use ion_rs::result::IonResult;
use ion_rs::value::reader::{element_reader, ElementReader};
use ion_rs::value::*;
use std::{cell::RefCell, fs::read, rc::Rc};

// This type exists purely to facilitate testing with ion-hash-test. See that
// package for details on how the tests are structured.
//
// In a nutshell, the purpose of the tests are to ensure that the Ion Hash
// implementation correctly normalizes and represents the Ion values. The
// purpose is _not_ to test the hashing function! So.. `updates` track the byte
// representations of values we incorporate into the hash.
//
// The `Digest` trait specifies a fixed length output. Because our tests aren't
// really doing any hashing (they're just tracking the bytes sent to `update`),
// we don't have a fixed length output! Instead, we have the tests look at a Vec
// that tracks what was fed into `update`. This means that the result of calling
// `finalize` is garbage.
//
// Because [`IonHasher`] wants to own the `Digest`, we use `Rc<RefCell<T>>` to
// allow for cloning. This, in turn, allows our tests to retain access to the
// mock. Why is this important? Because concrete access to the mock allows
// access to the variable size update vec!
#[derive(Default, Clone)]
struct TestDigest {
    inner: Rc<RefCell<TestDigestInner>>,
}

#[derive(Default)]
struct TestDigestInner {
    updates: Vec<u8>,
}

impl Digest for TestDigest {
    // This is not really used other than to satisfy the trait. See the comments
    // on [`TestDigest`].
    type OutputSize = U8;

    fn new() -> Self {
        Self {
            inner: Rc::new(RefCell::new(TestDigestInner {
                updates: Vec::new(),
            })),
        }
    }

    fn update(&mut self, bytes: impl AsRef<[u8]>) {
        let mut inner = self.inner.borrow_mut();
        inner.updates.extend(bytes.as_ref());
    }

    fn chain(self, _data: impl AsRef<[u8]>) -> Self
    where
        Self: Sized,
    {
        todo!()
    }

    /// The output of this method should be ignored. This implementation **does
    /// not support fixed size results**.
    fn finalize(self) -> Output<Self> {
        GenericArray::default()
    }

    /// While this method does correctly reset the internal state, the result of
    /// this method should be ignored for the same reason as noted in
    /// [`finalize`].
    fn finalize_reset(&mut self) -> Output<Self> {
        let mut inner = self.inner.borrow_mut();
        inner.updates.clear();
        GenericArray::default()
    }

    fn reset(&mut self) {
        self.finalize_reset();
    }

    fn output_size() -> usize {
        8
    }

    /// The output of this method should be ignored (see `[finalize]`).
    fn digest(data: &[u8]) -> Output<Self> {
        let mut myself = Self::new();
        myself.update(data);
        myself.finalize()
    }
}

impl TestDigest {
    fn inspect_updates(&self) -> Vec<u8> {
        let inner = self.inner.borrow();
        inner.updates.clone()
    }
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
    let strukt = strukt.as_struct().expect("`expect` should be a struct");
    let identity = strukt
        .get("identity")
        .expect("`expect` should have a field called `identity`")
        .as_sequence()
        .expect("`identity` should be a sexp");

    let digest = TestDigest::default();
    let hasher = IonHasher::new(digest.clone());
    let test_case_name = test_case_name(ion)?;

    // We completely ignore the result here! See [`TestDigest`] for why!
    let _ = hasher.hash_element(ion)?;
    // .. instead, we use the result that's waiting in our mock digest
    // implementation.
    let result = digest.inspect_updates();

    for it in identity.iter() {
        let method = it
            .annotations()
            .next()
            .expect("identity sexps have one annotation")
            .text()
            .expect("identity sexps contain elements with text annotations");

        let bytes: Vec<_> = it
            .as_sequence()
            .expect("identity sexps have sub-sexps")
            .iter()
            .map(|it| it.as_i64().expect("sub-exps have bytes") as u8)
            .collect();

        match method {
            "update" => {
                // TODO: We currently don't assert on intermediate updates. It's
                // not clear if this is actually valuable, other than helping
                // diagnose bugs.
            }
            "digest" => {
                let result_slice = &result[..];

                // Convert into hex repr to make assertion failures look like
                // the test case definitions.
                let expected = format!("{:02X?}", bytes);
                let actual = format!("{:02X?}", result_slice);

                assert_eq!(
                    expected, actual,
                    "case: {}; bytes failed to match",
                    test_case_name
                );
            }
            other => unimplemented!("{} is not yet implemented", other),
        }
    }

    Ok(())
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
