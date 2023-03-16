// Copyright Amazon.com, Inc. or its affiliates.

//! Provides a dynamically typed, materialized representation of an Ion value.
//!
//! An [Element](owned::Element) represents an `(annotations, value)` pair, where a `value` is
//! an Ion `integer`, `float`, `list`, `struct`, etc.
//!
//! For reference here are a couple other _value_ style APIs for JSON:
//! * [`simd_json`'s `Value` API][simd-json-value]
//! * [`serde_json`'s `Value` API][serde-json-value]
//!
//! [simd-json-value]: https://docs.rs/simd-json/latest/simd_json/value/index.html
//! [serde-json-value]: https://docs.serde.rs/serde_json/value/enum.Value.html

pub mod builders;
mod element_stream_reader;
mod iterators;
pub mod native_writer;
pub mod owned;
pub mod reader;
pub mod writer;

#[cfg(test)]
mod tests {
    use crate::element::owned::*;
    use crate::types::timestamp::Timestamp;
    use crate::{ion_list, ion_sexp, ion_struct, Decimal, Integer, IonType, Symbol};
    use chrono::*;
    use rstest::*;
    use std::iter::{once, Once};
    use IntoAnnotatedElement;

    /// Makes a timestamp from an RFC-3339 string and panics if it can't
    fn make_timestamp<T: AsRef<str>>(text: T) -> Timestamp {
        DateTime::parse_from_rfc3339(text.as_ref()).unwrap().into()
    }

    struct CaseAnnotations {
        elem: Element,
        annotations: Vec<Symbol>,
    }

    fn annotations_text_case() -> CaseAnnotations {
        CaseAnnotations {
            elem: 10i64.with_annotations(["foo", "bar", "baz"]),
            annotations: ["foo", "bar", "baz"]
                .into_iter()
                .map(|i| i.into())
                .collect(),
        }
    }

    fn no_annotations_case() -> CaseAnnotations {
        CaseAnnotations {
            elem: 10i64.into(),
            annotations: vec![],
        }
    }

    #[rstest]
    #[case::annotations_text(annotations_text_case())]
    #[case::no_annotations(no_annotations_case())]
    fn annotations_with_element(#[case] input: CaseAnnotations) {
        let actual: Vec<&Symbol> = input.elem.annotations().collect();
        let expected: Vec<&Symbol> = input.annotations.iter().collect();
        assert_eq!(actual, expected);
    }

    struct CaseSym {
        eq_annotations: Vec<Symbol>,
        ne_annotations: Vec<Symbol>,
    }

    fn sym_text_case() -> CaseSym {
        // SymbolTokens with same text are equivalent
        CaseSym {
            eq_annotations: vec![Symbol::owned("foo"), Symbol::owned("foo")],
            // These are not equal to any of the ones in `eq_annotations` above
            ne_annotations: vec![Symbol::owned("bar"), Symbol::owned("baz")],
        }
    }

    /// Each case is a set of tokens that are the same, and a set of tokens that are not ever equal to the first.
    /// This should test symmetry/transitivity/commutativity
    #[rstest]
    #[case::owned_sym_text(sym_text_case())]
    fn symbol_token_eq(#[case] input: CaseSym) {
        // check if equivalent vector contains set of tokens that are all equal
        for eq_this_token in &input.eq_annotations {
            for eq_other_token in &input.eq_annotations {
                assert_eq!(eq_this_token, eq_other_token);
            }
        }

        // check if non_equivalent vector contains a set of tokens that are not ever equal
        // to the equivalent set tokens.
        for eq_token in &input.eq_annotations {
            for non_eq_token in &input.ne_annotations {
                assert_ne!(eq_token, non_eq_token);
            }
        }
    }

    /// A struct that defines input case for `struct_accessors` method
    struct CaseStruct {
        /// set of struct elements that are the same
        eq_elements: Vec<Element>,
        /// set of struct elements that are never equal to `eq_annotations`
        ne_elements: Vec<Element>,
    }

    /// A convenience method for constructing a Vec<Element> from a collection of
    /// homogeneously typed values that implement Into<Element>.
    fn ion_vec<E: Into<Element>, I: IntoIterator<Item = E>>(values: I) -> Vec<Element> {
        values.into_iter().map(|v| v.into()).collect()
    }

    fn struct_with_multiple_fields_case() -> CaseStruct {
        CaseStruct {
            eq_elements: ion_vec([
                // structs with different order of fields
                ion_struct! {
                    "greetings": "hello",
                    "name": "Ion"
                },
                ion_struct! {
                    "name": "Ion",
                    "greetings": "hello"
                },
            ]),
            ne_elements: ion_vec([
                // structs with different length and duplicates
                ion_struct! {
                    "greetings": "hello",
                    "name": "Ion",
                    "greetings": "hello"
                },
                // structs with different fields length and duplicates
                ion_struct! {
                    "greetings": "hello",
                    "name": "Ion",
                    "greetings": "bye"
                },
                // structs with different fields length
                ion_struct! {
                    "greetings": "hello",
                    "name": "Ion",
                    "message": "bye"
                },
            ]),
        }
    }

    fn struct_with_duplicates_in_multiple_fields_case() -> CaseStruct {
        CaseStruct {
            // Structs are bags of (field, value) pairs, order is irrelevant
            eq_elements: ion_vec([
                ion_struct! {
                    "a" : 2i64,
                    "a" : 2i64,
                    "a" : 1i64
                },
                ion_struct! {
                    "a" : 2i64,
                    "a" : 1i64,
                    "a" : 2i64
                },
                ion_struct! {
                    "a" : 1i64,
                    "a" : 2i64,
                    "a" : 2i64
                },
            ]),
            ne_elements: ion_vec([
                // structs with different length
                ion_struct! {
                    "a" : 1i64,
                    "a" : 2i64
                },
                // structs with annotated values
                ion_struct! {
                    "a" : 2i64,
                    "a" : 1i64.with_annotations(["a"]),
                    "a" : 2i64
                },
                // structs with different value for duplicates
                ion_struct! {
                    "a" : 2i64,
                    "a" : 3i64,
                    "a" : 2i64
                },
            ]),
        }
    }

    fn struct_with_duplicate_fieldnames_case() -> CaseStruct {
        CaseStruct {
            eq_elements: ion_vec([
                // structs with unordered fields
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello"
                },
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello"
                },
            ]),
            ne_elements: ion_vec([
                // structs with different length and duplicates
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello",
                    "greetings" : "hey"
                },
                // structs with annotated values
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello".with_annotations(["foo"])
                },
                // structs with different length
                ion_struct! {
                    "greetings" : "world",
                    "greetings" : "hello",
                    "name" : "hello"
                },
            ]),
        }
    }

    #[rstest]
    #[case::owned_struct_with_multiple_fields(struct_with_multiple_fields_case())]
    #[case::owned_struct_with_duplicates_in_multiple_fields(
        struct_with_duplicates_in_multiple_fields_case()
    )]
    #[case::owned_struct_with_duplicate_fieldnames(struct_with_duplicate_fieldnames_case())]
    fn struct_accessors(#[case] input: CaseStruct) {
        // check if equivalent vector contains set of structs that are all equal
        for eq_this_struct in &input.eq_elements {
            for eq_other_struct in &input.eq_elements {
                assert_eq!(eq_this_struct, eq_other_struct);
            }
        }

        // check if non_equivalent vector contains a set of structs that are not ever equal
        // to the equivalent set structs.
        for eq_struct in &input.eq_elements {
            for non_eq_struct in &input.ne_elements {
                assert_ne!(eq_struct, non_eq_struct);
            }
        }
    }

    /// Models the operations on `Element` that we want to test.
    #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash)]
    enum ElemOp {
        IsNull,
        AsBool,
        AsAnyInt,
        AsF64,
        AsDecimal,
        AsTimestamp,
        AsStr,
        AsSym,
        AsBytes,
        AsSequence,
        AsSExp,
        AsList,
        AsStruct,
    }

    impl IntoIterator for ElemOp {
        type Item = ElemOp;
        type IntoIter = <Once<ElemOp> as IntoIterator>::IntoIter;

        fn into_iter(self) -> Self::IntoIter {
            once(self)
        }
    }

    use crate::types::integer::IntAccess;
    use num_bigint::BigInt;
    use std::collections::HashSet;
    use std::str::FromStr;
    use ElemOp::*;

    type ElemAssertFn = Box<dyn FnOnce(&Element)>;

    struct Case {
        elem: Element,
        ion_type: IonType,
        ops: Vec<ElemOp>,
        op_assert: ElemAssertFn,
    }

    fn null_case() -> Case {
        Case {
            elem: Element::from(IonType::Null), // null.null
            ion_type: IonType::Null,
            ops: vec![IsNull],
            op_assert: Box::new(|e: &Element| assert!(e.is_null())),
        }
    }

    fn bool_case() -> Case {
        Case {
            elem: true.into(),
            ion_type: IonType::Boolean,
            ops: vec![AsBool],
            op_assert: Box::new(|e: &Element| {
                let expected = Element::from(true);
                assert_eq!(Some(true), e.as_boolean());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn i64_case() -> Case {
        Case {
            elem: 100.into(),
            ion_type: IonType::Integer,
            ops: vec![AsAnyInt],
            op_assert: Box::new(|e: &Element| {
                let expected: Element = 100i64.into();
                assert_eq!(Some(&Integer::I64(100)), e.as_integer());
                assert_eq!(Some(100), e.as_i64());
                assert_eq!(None, e.as_big_int());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn big_int_case() -> Case {
        Case {
            elem: BigInt::from(100).into(),
            ion_type: IonType::Integer,
            ops: vec![AsAnyInt],
            op_assert: Box::new(|e: &Element| {
                let expected: Element = BigInt::from(100).into();
                assert_eq!(Some(&Integer::BigInt(BigInt::from(100))), e.as_integer());
                assert_eq!(BigInt::from_str("100").unwrap(), *e.as_big_int().unwrap());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn f64_case() -> Case {
        Case {
            elem: 16.0.into(),
            ion_type: IonType::Float,
            ops: vec![AsF64],
            op_assert: Box::new(|e: &Element| {
                let expected = Element::from(16.0f64);
                assert_eq!(Some(16.0), e.as_float());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn timestamp_case() -> Case {
        Case {
            elem: make_timestamp("2014-10-16T12:01:00-00:00").into(),
            ion_type: IonType::Timestamp,
            ops: vec![AsTimestamp],
            op_assert: Box::new(|e: &Element| {
                let expected: Element = make_timestamp("2014-10-16T12:01:00+00:00").into();
                assert_eq!(
                    Some(&make_timestamp("2014-10-16T12:01:00+00:00")),
                    e.as_timestamp()
                );
                assert_eq!(&expected, e);
            }),
        }
    }

    fn decimal_case() -> Case {
        Case {
            elem: Decimal::new(8, 3).into(),
            ion_type: IonType::Decimal,
            ops: vec![AsDecimal],
            op_assert: Box::new(|e: &Element| {
                let expected: Element = Decimal::new(8, 3).into();
                assert_eq!(Some(&Decimal::new(80, 2)), e.as_decimal());
                assert_eq!(&expected, e);
            }),
        }
    }

    fn string_case() -> Case {
        Case {
            elem: "hello".into(),
            ion_type: IonType::String,
            ops: vec![AsStr],
            op_assert: Box::new(|e: &Element| assert_eq!(Some("hello"), e.as_text())),
        }
    }

    fn symbol_case() -> Case {
        Case {
            elem: Symbol::owned("foo").into(),
            ion_type: IonType::Symbol,
            ops: vec![AsSym, AsStr],
            op_assert: Box::new(|e: &Element| {
                assert_eq!(Some("foo"), e.as_symbol().unwrap().text());
                assert_eq!(Some("foo"), e.as_text());
            }),
        }
    }

    fn blob_case() -> Case {
        Case {
            elem: Element::blob(b"hello"),
            ion_type: IonType::Blob,
            ops: vec![AsBytes],
            op_assert: Box::new(|e: &Element| assert_eq!(Some("hello".as_bytes()), e.as_lob())),
        }
    }

    fn clob_case() -> Case {
        Case {
            elem: Element::clob(b"goodbye"),
            ion_type: IonType::Clob,
            ops: vec![AsBytes],
            op_assert: Box::new(|e: &Element| assert_eq!(Some("goodbye".as_bytes()), e.as_lob())),
        }
    }

    fn list_case() -> Case {
        Case {
            elem: ion_list![true, false].into(),
            ion_type: IonType::List,
            ops: vec![AsList, AsSequence],
            op_assert: Box::new(|e: &Element| {
                let actual = e.as_list().unwrap();
                let expected: Vec<Element> = ion_vec([true, false]);
                // assert the length of list
                assert_eq!(2, actual.len());
                for (i, actual_item) in actual.iter().enumerate() {
                    // assert the list elements one-by-one
                    assert_eq!(&expected[i], actual_item);
                }
                assert!(!actual.is_empty());
            }),
        }
    }

    fn sexp_case() -> Case {
        Case {
            elem: ion_sexp!(true false).into(),
            ion_type: IonType::SExp,
            ops: vec![AsSExp, AsSequence],
            op_assert: Box::new(|e: &Element| {
                let actual = e.as_sexp().unwrap();
                let expected: Vec<Element> = ion_vec([true, false]);
                // assert the length of s-expression
                assert_eq!(2, actual.len());
                for (i, actual_item) in actual.iter().enumerate() {
                    // assert the s-expression elements one-by-one
                    assert_eq!(&expected[i], actual_item);
                }
            }),
        }
    }

    fn struct_case() -> Case {
        Case {
            elem: ion_struct! {"greetings": "hello", "name": "ion"}.into(),
            ion_type: IonType::Struct,
            ops: vec![AsStruct],
            op_assert: Box::new(|e: &Element| {
                let actual: &Struct = e.as_struct().unwrap();

                // verify that the field order is maintained when creating Struct
                assert_eq!(
                    actual.iter().next(),
                    Some((&"greetings".into(), &"hello".into()))
                );

                assert_eq!(actual.get("greetings"), Some(&"hello".into()));
            }),
        }
    }
    // TODO add more tests to remove the separate Owned/Borrowed tests and only keep generic tests

    #[rstest]
    #[case::owned_null(null_case())]
    #[case::owned_bool(bool_case())]
    #[case::owned_i64(i64_case())]
    #[case::owned_big_int(big_int_case())]
    #[case::owned_f64(f64_case())]
    #[case::owned_decimal(decimal_case())]
    #[case::owned_timestamp(timestamp_case())]
    #[case::owned_string(string_case())]
    #[case::owned_blob(blob_case())]
    #[case::owned_clob(clob_case())]
    #[case::owned_list(list_case())]
    #[case::owned_sexp(sexp_case())]
    #[case::owned_struct(struct_case())]
    #[case::owned_symbol(symbol_case())]
    fn element_accessors(#[case] input_case: Case) {
        // table of negative assertions for each operation
        let neg_table: Vec<(ElemOp, ElemAssertFn)> = vec![
            (IsNull, Box::new(|e| assert!(!e.is_null()))),
            (AsBool, Box::new(|e| assert_eq!(None, e.as_boolean()))),
            (
                AsAnyInt,
                Box::new(|e| {
                    assert_eq!(None, e.as_integer());
                    assert_eq!(None, e.as_i64());
                    assert_eq!(None, e.as_big_int());
                }),
            ),
            (AsF64, Box::new(|e| assert_eq!(None, e.as_float()))),
            (AsDecimal, Box::new(|e| assert_eq!(None, e.as_decimal()))),
            (
                AsTimestamp,
                Box::new(|e| assert_eq!(None, e.as_timestamp())),
            ),
            (AsStr, Box::new(|e| assert_eq!(None, e.as_text()))),
            (AsSym, Box::new(|e| assert_eq!(None, e.as_symbol()))),
            (AsBytes, Box::new(|e| assert_eq!(None, e.as_lob()))),
            (AsSequence, Box::new(|e| assert!(e.as_sequence().is_none()))),
            (AsList, Box::new(|e| assert_eq!(None, e.as_list()))),
            (AsSExp, Box::new(|e| assert_eq!(None, e.as_sexp()))),
            (AsStruct, Box::new(|e| assert_eq!(None, e.as_struct()))),
        ];

        // produce the table of assertions to operate on, replacing the one specified by
        // the test case
        let valid_ops: HashSet<ElemOp> = input_case.ops.into_iter().collect();
        let op_assertions: Vec<ElemAssertFn> = neg_table
            .into_iter()
            .filter(|(op, _)| !valid_ops.contains(op))
            .map(|(_, neg_assert)| neg_assert)
            .chain(once(input_case.op_assert))
            .collect();

        // construct an element to test
        assert_eq!(input_case.ion_type, input_case.elem.ion_type());

        for assert in op_assertions {
            assert(&input_case.elem);
        }

        // assert that an element as-is is equal to itself
        // Creating an alias here bypasses clippy's objection to comparing any literal to itself.
        let itself = &input_case.elem;
        assert_eq!(&input_case.elem, itself);
    }
}
