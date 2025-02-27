#![cfg(feature = "experimental-ion-1-1")]
#![cfg(feature = "experimental-reader-writer")]
#![cfg(feature = "experimental-tooling-apis")]
mod conformance_dsl;
use conformance_dsl::prelude::*;

use test_generator::test_resources;


mod ion_tests {
    use super::*;

    type SkipList = &'static [&'static str];
    static GLOBAL_CONFORMANCE_SKIPLIST: SkipList = &[
        // half-float not implemented
        "ion-tests/conformance/data_model/float.ion",
        // e-expression transcription
        "ion-tests/conformance/demos/metaprogramming.ion",
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
        "ion-tests/conformance/ion_literal.ion",
        "ion-tests/conformance/system_symbols.ion",
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
        // Mismatched encodings for nested contexts.
        "ion-tests/conformance/ivm.ion",
        // Decoding error "expected struct but found a null.struct"
        "ion-tests/conformance/local_symtab.ion",
        // Encoding error: "symbol value ID $10 is not in the symbol table"
        "ion-tests/conformance/local_symtab_imports.ion",
    ];

    #[test_resources("ion-tests/conformance/**/*.ion")]
    fn conformance(file_name: &str) {
        // Test for skip list. Convert windows '\\' separators into '/' to match skiplist.
        if !GLOBAL_CONFORMANCE_SKIPLIST.iter().any(|f| *f == file_name.replace("\\", "/")) {
            println!("TESTING: {}", file_name);
            let collection = TestCollection::load(file_name).expect("unable to load test file");

            collection.run().expect("failed to run collection");
        } else {
            println!("SKIPPING: {}", file_name);
        }
    }
}
