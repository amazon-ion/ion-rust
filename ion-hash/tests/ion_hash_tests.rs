// Copyright Amazon.com, Inc. or its affiliates.

use digest::{consts::U64, generic_array::GenericArray, Digest, Output};
use ion_hash::{self, IonHasher};
use ion_rs::result::IonResult;
use ion_rs::value::loader::{loader, Loader};
use ion_rs::value::*;
use std::fs::read;

#[derive(Default, Clone)]
struct TestDigest {
    updates: GenericArray<u8, U64>,
    position: usize,
}

impl Digest for TestDigest {
    type OutputSize = U64;

    fn new() -> Self {
        Self {
            updates: GenericArray::default(),
            position: 0,
        }
    }

    fn update(&mut self, bytes: impl AsRef<[u8]>) {
        for b in bytes.as_ref() {
            self.updates[self.position] = *b;
            self.position += 1;
        }
    }

    fn chain(self, _data: impl AsRef<[u8]>) -> Self
    where
        Self: Sized,
    {
        todo!()
    }

    fn finalize(self) -> Output<Self> {
        self.updates
    }

    fn finalize_reset(&mut self) -> Output<Self> {
        let output = self.updates;
        self.updates = GenericArray::default();
        self.position = 0;
        output
    }

    fn reset(&mut self) {
        self.updates = GenericArray::default();
        self.position = 0;
    }

    fn output_size() -> usize {
        64
    }

    fn digest(data: &[u8]) -> Output<Self> {
        let mut myself = Self::new();
        myself.update(data);
        myself.finalize()
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
    let result = hasher.hash_element(ion)?;

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
                for (i, byte) in bytes.iter().enumerate() {
                    assert_eq!(*byte, result[i]);
                }
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
