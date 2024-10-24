#![cfg(feature = "experimental-ion-1-1")]
#![cfg(feature = "experimental-reader-writer")]
#![cfg(feature = "experimental-tooling-apis")]
mod conformance_dsl;
use conformance_dsl::prelude::*;

use test_generator::test_resources;

use std::str::FromStr;

mod implementation {
    use super::*;

    #[test]
    fn test_absent_symbol() {
        let tests: &[&str] = &[
            r#"(ion_1_1
              (toplevel '#$2' {'#$9': '#$8'})
              (text "")
              (denotes (Symbol 2) (Struct (9 (Symbol 8))))
           )"#,
            r#"(ion_1_0
              (text '''$ion_symbol_table::{imports:[{name:"abcs", version: 2}]}''')
              (text "$10 $11")
              (produces '#$abcs#1' '#$abcs#2')
           )"#,
            r#"(ion_1_0
              (text '''$ion_symbol_table::{imports:[{name:"abcs", version: 2}]}''')
              (text "$10 $11")
              (denotes (Symbol (absent "abcs" 1)) (Symbol (absent "abcs" 2)))
           )"#,
        ];

        for test in tests {
            Document::from_str(test)
                .unwrap_or_else(|e| panic!("Failed to load document:\n{:?}", e))
                .run()
                .unwrap_or_else(|e| panic!("Test failed: {:?}", e));
        }
    }

    #[test]
    fn test_timestamps() {
        let tests: &[&str] = &[
            r#"(ion_1_1 "Timestamp Year" (text "2023T") (denotes (Timestamp year 2023)))"#,
            r#"(ion_1_1 "Timestamp Month" (text "2023-03T") (denotes (Timestamp month 2023 3)))"#,
            r#"(ion_1_1 "Timestamp Day" (text "2023-03-23T") (denotes (Timestamp day 2023 3 23)))"#,
            r#"(ion_1_1 "Timestamp Minute" (text "2023-03-23T10:12Z") (denotes (Timestamp minute 2023 3 23 (offset 0) 10 12)))"#,
            r#"(ion_1_1 "Timestamp Second" (text "2023-03-23T10:12:21Z") (denotes (Timestamp second 2023 3 23 (offset 0) 10 12 21))) "#,
            r#"(ion_1_1 "Timestamp Fractional" (text "2023-03-23T10:12:21.23Z") (denotes (Timestamp fraction 2023 3 23 (offset 0) 10 12 21 23 -2))) "#,
        ];

        for test in tests {
            Document::from_str(test)
                .unwrap_or_else(|e| panic!("Failed to load document: <<{}>>\n{:?}", test, e))
                .run()
                .unwrap_or_else(|e| panic!("Test failed for simple doc: <<{}>>\n{:?}", test, e));
        }
    }

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
            "(ion_1_1 (bytes 0x60 0x61 0x01 0xEB 0x01) (produces 0 1 null.int))",
            r#"(ion_1_0 (then (text "a") (produces a)))"#,
            r#"(ion_1_1 (text "a") (text "b") (text "c") (produces a b c))"#,
            r#"(ion_1_1 (text "\"Hello\" null.int false") (denotes (String "Hello") (Null int) (Bool false)))"#,
            r#"(ion_1_1 (each 
                             (text "0")
                             (bytes 0x60)
                             (denotes (Int 0)))
                        )"#,
            r#"(document (ivm 1 2) (signals "Invalid Version"))"#,
            r#"(ion_1_1 (text "2.3") (denotes (Decimal 23 -1)))"#,
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
    fn conformance(file_name: &str) {
        println!("Testing: {}", file_name);
        let collection = TestCollection::load(file_name).expect("unable to load test file");

        collection.run().expect("failed to run collection");
    }
}
