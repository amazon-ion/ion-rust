#![cfg(feature = "experimental-ion-1-1")]
#![cfg(feature = "experimental-reader-writer")]
#![cfg(feature = "experimental-tooling-apis")]
mod conformance_dsl;
use conformance_dsl::prelude::*;

use test_generator::test_resources;

use std::sync::LazyLock;

mod ion_tests {
    use super::*;

    #[derive(Default)]
    struct SkipItem {
        /// The source file containing one or more conformance tests.
        source: &'static str,
        /// The canonicalized path to the source, resolved at runtime.
        canonicalized_source: Option<String>,
        /// A list of tests found within the source to skip; if empty, all tests are skipped.
        tests: &'static [&'static str],
    }

    impl SkipItem {
        fn canonicalize(&self) -> Option<Self> {
            match std::fs::canonicalize(self.source) {
                Ok(path_buf) => Some(Self {
                    canonicalized_source: Some(path_buf.to_string_lossy().to_string()),
                    ..*self
                }),
                Err(_) => None,
            }
        }
    }

    // TODO: Turn this into a macro that doesn't have to be re-stated for every skip.
    macro_rules! skip {
        ( $l:literal ) => {
            SkipItem { source: $l, canonicalized_source: None, tests: &[] }
        };
        ( $l:literal, $($t:literal),+
        ) => {
            SkipItem {source: $l, canonicalized_source: None, tests: &[ $($t),+ ] }
        }
    }

    type SkipList = &'static [SkipItem];
    static GLOBAL_CONFORMANCE_SKIPLIST: SkipList = &[
        skip!(
            "ion-tests/conformance/data_model/float.ion",
            "Ion 1.1 binary" // PANIC: not yet implemented: implement half-precision floats
        ),
        // Issue parsing the comments left in decimal.ion, see ion-rust#972
        skip!("ion-tests/conformance/data_model/decimal.ion"),
        // Mismatched produces due to symbol id transcription.
        skip!("ion-tests/conformance/core/toplevel_produces.ion"),
        // Unrecognized encoding 'int8' (only flex_uint appears to be supported)
        skip!("ion-tests/conformance/demos/metaprogramming.ion"),
        // Context tracking in Conformance DSL cannot register macros added via set_macros
        // invocation.
        skip!("ion-tests/conformance/demos/telemetry_log.ion"),
        // error: flatten only accepts sequences
        skip!("ion-tests/conformance/eexp/arg_inlining.ion"),
        // Error: Unrecognized encoding (of various forms: flex_sym, uint8, uint16, uint32, etc)
        skip!("ion-tests/conformance/eexp/binary/tagless_types.ion"),
        // Error: Unexpected EOF and unrecognized encodings.
        skip!("ion-tests/conformance/eexp/binary/argument_encoding.ion"),
        // Error: Mismatched Produces; incorrect symbol table creation.
        skip!("ion-tests/conformance/system_macros/add_macros.ion"),
        skip!("ion-tests/conformance/system_symbols.ion"),
        // Error: ExpectedSignal: invalid argument
        skip!("ion-tests/conformance/system_macros/add_symbols.ion"),
        skip!("ion-tests/conformance/system_macros/set_macros.ion"),
        skip!("ion-tests/conformance/system_macros/set_symbols.ion"),
        skip!(
            "ion-tests/conformance/system_macros/default.ion",
            // Error: Decoding Error: macro none signature has 0 parameters(s)
            "when the first argument is non-empty, the second argument is not expanded"
        ),
        // System macro delta not yet implemented
        skip!("ion-tests/conformance/system_macros/delta.ion"),
        // System macro make_decimal not yet implemented
        skip!("ion-tests/conformance/system_macros/make_decimal.ion"),
        // System macro parse_ion not yet implemented
        skip!("ion-tests/conformance/system_macros/parse_ion.ion"),
        // System macro make_timestamp not yet implemented
        skip!("ion-tests/conformance/system_macros/make_timestamp.ion"),
        // $0 is not resolving: "expected text but found a symbol with undefined text"
        skip!("ion-tests/conformance/system_macros/annotate.ion"),
        // error reading struct: `make_field`'s first argument must be a text value
        skip!("ion-tests/conformance/system_macros/make_field.ion"),
        // system macro `use` not yet implemented.
        skip!("ion-tests/conformance/system_macros/use.ion"),
        // Expected Signal: invalid macro definition
        skip!("ion-tests/conformance/tdl/expression_groups.ion"),
        // "could not resolve macro ID \"for\""
        skip!("ion-tests/conformance/tdl/for.ion"),
        // Mismatched encodings for nested contexts.
        skip!("ion-tests/conformance/ivm.ion"),
        // Decoding error "expected struct but found a null.struct"
        skip!("ion-tests/conformance/local_symtab.ion"),
        // Encoding error: "symbol value ID $10 is not in the symbol table"
        skip!("ion-tests/conformance/local_symtab_imports.ion"),
        // Expected signal "invalid macro definition".
        skip!("ion-tests/conformance/tdl/variable_expansion.ion"),
    ];

    static CANONICAL_SKIP_LIST: LazyLock<Vec<SkipItem>> = LazyLock::new(|| {
        GLOBAL_CONFORMANCE_SKIPLIST
            .iter()
            .filter_map(|skip| skip.canonicalize())
            .collect()
    });

    #[test]
    #[ignore = "Only used to maintain skiplist, no need to break builds because of it. (use --include-ignored to run)"]
    fn check_skiplist() {
        let mut skip_file_removed = true;
        for skip_item in GLOBAL_CONFORMANCE_SKIPLIST.iter() {
            if skip_item.canonicalize().is_none() {
                skip_file_removed = false;
                println!("MISSING: {}", skip_item.source);
            }
        }
        assert!(skip_file_removed);
    }

    #[test_resources("ion-tests/conformance/**/*.ion")]
    fn conformance(file_name: &str) {
        let file_name: String = std::fs::canonicalize(file_name)
            .unwrap()
            .to_string_lossy()
            .into();
        let mut total_tests: usize = 0;
        let mut total_skipped: usize = 0;

        // Having a file_name in the skip list just means we ignore some part of it.. not
        // necessarily the whole file. If we don't specify a list of test names, then we ignore the
        // whole thing.
        let skip_item = CANONICAL_SKIP_LIST.iter().find(|item| {
            item.canonicalized_source
                .as_ref()
                .is_some_and(|source| *source == file_name)
        });
        if skip_item.is_some_and(|item| item.tests.is_empty()) {
            println!("SKIPPING: {file_name}");
            return;
        }

        let skip_tests: &[&'static str] = skip_item.map(|item| item.tests).unwrap_or(&[]);

        let collection = TestCollection::load(&file_name).expect("unable to load test file");

        for test in collection.iter() {
            total_tests += 1;
            let name = if let Some(name) = &test.name {
                if skip_tests.contains(&name.as_str()) {
                    println!("Skipping: {file_name} => \"{name}\"");
                    total_skipped += 1;
                    continue;
                }
                name
            } else {
                ""
            };

            println!("TESTING: {file_name} => {name}");
            test.run().expect("test failed");
        }

        println!(
            "SUMMARY: {file_name} : Total Tests {total_tests} :  Skipped {total_skipped}",
        );
    }
}
