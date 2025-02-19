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
                 (encoding module _ (macro_table (macro m () 1)))
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

    type SkipList = &'static [&'static str];
    static GLOBAL_CONFORMANCE_SKIPLIST: SkipList = &[
        // half-float not implemented
        "ion-tests/conformance/data_model/float.ion",
        // e-expression transcription
        "ion-tests/conformance/eexp/arg_inlining.ion",
        "ion-tests/conformance/eexp/element_inlining.ion",
        "ion-tests/conformance/eexp/basic_system_macros.ion",
        "ion-tests/conformance/ion_encoding/mactab.ion",
        "ion-tests/conformance/ion_encoding/module/macro/cardinality/invoke_cardinality_ee.ion",
        "ion-tests/conformance/ion_encoding/module/macro/template/literal_form.ion",
        "ion-tests/conformance/ion_encoding/module/macro/template/quasiliteral.ion",
        "ion-tests/conformance/ion_encoding/module/macro/template/variable_reference.ion",
        "ion-tests/conformance/ion_encoding/module/macro/template/if.ion",
        "ion-tests/conformance/ion_encoding/module/macro/trivial/literal_value.ion",
        "ion-tests/conformance/ion_encoding/module/macro/trivial/invoke_ee.ion",
        // Error: Mismatched denotes
        "ion-tests/conformance/eexp/binary/tagless_types.ion",
        // Error: Unexpected EOF
        "ion-tests/conformance/eexp/binary/argument_encoding.ion",
        // Error: Mismatched Produce
        "ion-tests/conformance/ion_encoding/symtab.ion",
        "ion-tests/conformance/ion_encoding/load_symtab.ion",
        "ion-tests/conformance/ion_encoding/trivial_forms.ion",
        "ion-tests/conformance/ion_encoding/module/trivial.ion",
        "ion-tests/conformance/ion_encoding/module/macro_table.ion",
        "ion-tests/conformance/system_macros/add_macros.ion",
        // Error: found operation name with non-symbol type: sexp
        "ion-tests/conformance/ion_encoding/module/load_symtab.ion",
        "ion-tests/conformance/ion_encoding/module/symtab.ion",
        // Error: Too few arguments.
        "ion-tests/conformance/ion_encoding/module/macro/cardinality/invoke_cardinality_tl.ion",
        // Error: "Invalid macro name:"
        "ion-tests/conformance/ion_encoding/module/macro/trivial/signature.ion",
        // Error: ExpectedSignal: No such macro: NoSuchMacro
        "ion-tests/conformance/ion_encoding/module/macro/trivial/invoke_tl.ion",
        // Error: ExpectedSIgnal: invalid argument
        "ion-tests/conformance/system_macros/add_symbols.ion",
        "ion-tests/conformance/system_macros/set_macros.ion",
        "ion-tests/conformance/system_macros/set_symbols.ion",
        // Error: Decoding Error: macro none signature has 0 parameters(s), e-expression had an
        // extra argument.
        "ion-tests/conformance/system_macros/default.ion",
        // System macro delta not yet implemented
        "ion-tests/conformance/system_macros/delta.ion",
        // System macro make_decimal not yet implemented
        "ion-tests/conformance/system_macros/make_decimal.ion",
        // System macro repeat not yet implemented
        "ion-tests/conformance/system_macros/repeat.ion",
        // System macro parse_ion not yet implemented
        "ion-tests/conformance/system_macros/parse_ion.ion",
        // System macro sum not yet implemented
        "ion-tests/conformance/system_macros/sum.ion",
        // System macro make_timestamp not yet implemented
        "ion-tests/conformance/system_macros/make_timestamp.ion",
        // Expected Signal: invalid macro definition
        "ion-tests/conformance/tdl/expression_groups.ion",
        // Expected Signal Errors and e-expression transcription
        "ion-tests/conformance/tdl/if_none.ion",
        "ion-tests/conformance/tdl/if_some.ion",
        "ion-tests/conformance/tdl/if_multi.ion",
        "ion-tests/conformance/tdl/if_single.ion",
    ];

    #[test_resources("ion-tests/conformance/core/*.ion")]
    #[test_resources("ion-tests/conformance/data_model/*.ion")]
    #[test_resources("ion-tests/conformance/eexp/*.ion")]
    #[test_resources("ion-tests/conformance/eexp/binary/*.ion")]
    #[test_resources("ion-tests/conformance/ion_encoding/*.ion")]
    #[test_resources("ion-tests/conformance/ion_encoding/module/*.ion")]
    #[test_resources("ion-tests/conformance/ion_encoding/module/macro/cardinality/*.ion")]
    #[test_resources("ion-tests/conformance/ion_encoding/module/macro/template/*.ion")]
    #[test_resources("ion-tests/conformance/ion_encoding/module/macro/trivial/*.ion")]
    #[test_resources("ion-tests/conformance/system_macros/*.ion")]
    #[test_resources("ion-tests/conformance/tdl/*")]
    fn conformance(file_name: &str) {
        if !GLOBAL_CONFORMANCE_SKIPLIST.iter().any(|f| *f == file_name) {
            println!("TESTING: {}", file_name);
            let collection = TestCollection::load(file_name).expect("unable to load test file");

            collection.run().expect("failed to run collection");
        } else {
            println!("SKIPPING: {}", file_name);
        }
    }
}
