#![cfg(feature = "experimental-reader-writer")]
mod conformance_dsl;
use conformance_dsl::prelude::*;

use test_generator::test_resources;

use std::str::FromStr;



mod implementation {
    use super::*;

    #[test]
    fn test_encoding() {
        let test: &str = r#"
             (ion_1_1
                 (encoding (macro_table (macro m () 1)))
                 (text "(:m)")
                 (produces 1)
             )"#;
        Document::from_str(test)
            .unwrap_or_else(|e| panic!("Failed to load document:\n{:?}", e))
            .run()
            .unwrap_or_else(|e| panic!("Test failed: {:?}", e));
    }

    #[test]
    fn test_simple_docs() {
        let tests: &[&str] = &[
            "(document (produces ))",
            "(document (toplevel a) (produces a))",
            "(document (text \"a\") (produces a))",
            "(ion_1_0 (produces ))",
            "(ion_1_1 (produces ))",
            "(document (and (produces ) (produces )))",
            "(document (text \"a\") (not (and (produces b) (produces c))))",
            "(ion_1_1 (binary 0x60 0x61 0x01 0xEB 0x01) (produces 0 1 null.int))",
            r#"(ion_1_0 (then (text "a") (produces a)))"#,
            r#"(ion_1_1 (text "a") (text "b") (text "c") (produces a b c))"#,
            r#"(ion_1_1 (text "\"Hello\" null.int false") (denotes (String "Hello") (Null int) (Bool false)))"#,
            r#"(ion_1_1 (each 
                             (text "0")
                             (binary 0x60)
                             (denotes (Int 0)))
                        )"#,
            r#"(document (ivm 1 2) (signals "Invalid Version"))"#,
        ];
        for test in tests {
            println!("Testing: {}", test);
            Document::from_str(test)
                .unwrap_or_else(|e| panic!("Failed to load document: <<{}>>\n{:?}", test, e))
                .run()
                .unwrap_or_else(|e| panic!("Test failed for simple doc: <<{}>>\n{:?}", test, e)); 
            }
    }
}

mod ion_tests {
    use super::*;

    #[test_resources("ion-tests/conformance/null.ion")]
    #[test_resources("ion-tests/conformance/core/typed_null.ion")]
    #[test_resources("ion-tests/conformance/core/string_symbol.ion")]
    #[test_resources("ion-tests/conformance/core/empty_document.ion")]
    #[test_resources("ion-tests/conformance/core/toplevel_produces.ion")]
    // #[test_resources("ion-tests/conformance/ivm.ion")]
    fn conformance(file_name: &str) {
        println!("Testing: {}", file_name);
        let collection = TestCollection::load(file_name).expect("unable to load test file");

        println!("Collection: {:?}", collection);
        collection.run().expect("failed to run collection");
    }
}
