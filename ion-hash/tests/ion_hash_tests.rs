// Copyright Amazon.com, Inc. or its affiliates.

use ion_hash::{self, IonHashDigest, IonHasher};
use ion_rs::result::IonResult;
use ion_rs::value::loader::{loader, Loader};
use ion_rs::value::*;
use std::{
    fs::read,
    sync::{Arc, Mutex},
};

#[derive(Default, Clone)]
struct TestDigest {
    inner: Arc<Mutex<TestDigestInner>>,
}

#[derive(Default)]
struct TestDigestInner {
    updates: Vec<u8>,
    digest: Vec<u8>,
}

impl TestDigest {
    fn inspect(&self) -> (Vec<u8>, Vec<u8>) {
        let inner = self.inner.lock().unwrap();
        (inner.updates.clone(), inner.digest.clone())
    }
}

impl IonHashDigest for TestDigest {
    fn update(&mut self, bytes: impl AsRef<[u8]>) {
        let mut inner = self.inner.lock().unwrap();
        for b in bytes.as_ref() {
            inner.updates.push(*b);
            inner.digest.push(*b);
        }
    }

    fn finalize(self) -> Vec<u8> {
        let inner = self.inner.lock().unwrap();
        inner.digest.clone()
    }
}

#[test]
fn the_first_test() -> IonResult<()> {
    let example = br#"
{ ion:null,           expect:{ identity:(update::(0x0b) update::(0x0f) update::(0x0e) digest::(0x0b 0x0f 0x0e)),
                                    md5:(digest::(0x0f 0x50 0xc5 0xe5 0xe8 0x77 0xb4 0x45 0x1a 0xa9 0xfe 0x77 0xc3 0x76 0xcd 0xe4)) } }"#;
    let elems = loader().load_all(example)?;
    test_all(elems)
}

fn test_all<E: Element>(elems: Vec<E>) -> IonResult<()> {
    for case in elems {
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
    let _result = hasher.hash_element(ion)?;

    let (recorded_updates, recorded_digest) = digest.inspect();
    let mut recorded_updates = recorded_updates.into_iter();

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
                let first = recorded_updates
                    .nth(0)
                    .expect("no more calls to `update` were made");

                assert_eq!(&bytes[..], &[first]);
            }
            "digest" => {
                assert_eq!(bytes, recorded_digest);
            }
            other => unimplemented!("{} is not yet implemented", other),
        }
    }

    Ok(())
}

// FIXME: This file doesn't load.
//#[test]
fn _ion_hash_tests() -> IonResult<()> {
    _test_file("ion-hash-test/ion_hash_tests.ion")
}

fn _test_file(file_name: &str) -> IonResult<()> {
    let data = read(file_name)?;
    let elems = loader().load_all(&data)?;
    test_all(elems)
}
