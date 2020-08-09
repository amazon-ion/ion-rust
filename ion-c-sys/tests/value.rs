// Copyright Amazon.com, Inc. or its affiliates.

use ion_c_sys::reader::*;
use ion_c_sys::*;

use std::convert::TryFrom;
use std::error::Error;

use rstest::*;

type TestResult = Result<(), Box<dyn Error>>;

/// Simplified Ion element structure for our tests.
#[derive(Debug, Clone, PartialEq)]
struct Elem {
    pub annotations: Vec<&'static str>,
    pub val: Val,
}

impl Elem {
    /// Create an element without annotations.
    fn new(val: Val) -> Self {
        Self {
            annotations: vec![],
            val,
        }
    }

    /// Create an element with annotations.
    fn new_a(val: Val, annotations: Vec<&'static str>) -> Self {
        Self { annotations, val }
    }
}

/// Simplified value enum for our tests.
#[derive(Debug, Clone, PartialEq)]
enum Val {
    // scalars
    Null(ION_TYPE),
    Bool(bool),
    Int(i64),
    Float(f64),
    // TODO ion-rust/#42 - decimal support
    // TODO ion-rust/#43 - timestamp support
    Sym(&'static str),
    Str(&'static str),
    Clob(&'static [u8]),
    Blob(&'static [u8]),

    // aggregates
    List(Vec<Elem>),
    Sexp(Vec<Elem>),
    Struct(Vec<(&'static str, Elem)>),
}
use Val::*;

#[derive(Debug)]
struct TestCase {
    lit: &'static str,
    elem: Elem,
}

#[rstest(c,
    case::null(TestCase {
        lit: "null",
        elem: Elem::new(Null(ION_TYPE_NULL)),
    }),
    case::null_bool(TestCase {
        lit: "null.bool",
        elem: Elem::new(Null(ION_TYPE_BOOL)),
    }),
    case::null_int(TestCase {
        lit: "null.int",
        elem: Elem::new(Null(ION_TYPE_INT)),
    }),
    case::null_float(TestCase {
        lit: "null.float",
        elem: Elem::new(Null(ION_TYPE_FLOAT)),
    }),
    case::null_decimal(TestCase {
        lit: "null.decimal",
        elem: Elem::new(Null(ION_TYPE_DECIMAL)),
    }),
    case::null_timestamp(TestCase {
        lit: "null.timestamp",
        elem: Elem::new(Null(ION_TYPE_TIMESTAMP)),
    }),
    case::null_symbol(TestCase {
        lit: "null.symbol",
        elem: Elem::new(Null(ION_TYPE_SYMBOL)),
    }),
    case::null_string(TestCase {
        lit: "null.string",
        elem: Elem::new(Null(ION_TYPE_STRING)),
    }),
    case::null_clob(TestCase {
        lit: "null.clob",
        elem: Elem::new(Null(ION_TYPE_CLOB)),
    }),
    case::null_blob(TestCase {
        lit: "null.blob",
        elem: Elem::new(Null(ION_TYPE_BLOB)),
    }),
    case::null_list(TestCase {
        lit: "null.list",
        elem: Elem::new(Null(ION_TYPE_LIST)),
    }),
    case::null_sexp(TestCase {
        lit: "null.sexp",
        elem: Elem::new(Null(ION_TYPE_SEXP)),
    }),
    case::null_struct(TestCase {
        lit: "null.struct",
        elem: Elem::new(Null(ION_TYPE_STRUCT)),
    }),
    case::bool_true(TestCase {
        lit: "a::b::c::true",
        elem: Elem::new_a(Bool(true), vec!["a", "b", "c"]),
    }),
    case::bool_false(TestCase {
        lit: "abcdefghijklmnop::false",
        elem: Elem::new_a(Bool(false), vec!["abcdefghijklmnop"]),
    }),
    case::int_positive(TestCase {
        lit: "42",
        elem: Elem::new(Int(42)),
    }),
    case::int_negative(TestCase {
        lit: "-10",
        elem: Elem::new(Int(-10)),
    }),
    case::int_maxi64(TestCase {
        lit: "0x7fffffffffffffff",
        elem: Elem::new(Int(0x7fffffffffffffff)),
    }),
    case::float(TestCase {
        lit: "3e0",
        elem: Elem::new(Float(3.0)),
    }),
    case::float_nan(TestCase {
        lit: "nan",
        elem: Elem::new(Float(f64::NAN)),
    }),
    case::float_ninf(TestCase {
        lit: "-inf",
        elem: Elem::new(Float(f64::NEG_INFINITY)),
    }),
    case::float_pinf(TestCase {
        lit: "+inf",
        elem: Elem::new(Float(f64::INFINITY)),
    }),
    case::symbol(TestCase {
        lit: "\'hello 👾!\'",
        elem: Elem::new(Sym("hello 👾!")),
    }),
    case::string(TestCase {
        lit: "\"hello 💩!\"",
        elem: Elem::new(Str("hello 💩!")),
    }),
    case::clob(TestCase {
        lit: "{{\"hello\"}}",
        elem: Elem::new(Clob(b"hello")),
    }),
    case::blob(TestCase {
        lit: "{{d29ybGQ=}}",
        elem: Elem::new(Blob(b"world")),
    }),
    case::list(TestCase {
        lit: "[false, 0, 0e0]",
        elem: Elem::new(List(vec![
            Elem::new(Bool(false)),
            Elem::new(Int(0)),
            Elem::new(Float(0.0))
        ])),
    }),
    case::sexp(TestCase {
        lit: "(+ 1 2 3)",
        elem: Elem::new(Sexp(vec![
            Elem::new(Sym("+")),
            Elem::new(Int(1)),
            Elem::new(Int(2)),
            Elem::new(Int(3))])),
    }),
    case::structure(TestCase {
        lit: "{a:1, b:2, c:3}",
        elem: Elem::new(Struct(vec![
            ("a", Elem::new(Int(1))),
            ("b", Elem::new(Int(2))),
            ("c", Elem::new(Int(3))),
        ])),
    }),
)]
fn test_read_single(c: TestCase) -> TestResult {
    // copy into a mutable buffer as a defensive measure
    let mut reader = IonCReaderHandle::try_from(c.lit)?;

    assert_eq!(ION_TYPE_NONE, reader.get_type()?);
    // assert the that we read what was expected
    assert_single_value(&mut reader, &c.elem, 0)?;

    // we're at the end
    assert_eq!(ION_TYPE_EOF, reader.next()?);
    assert_eq!(0, reader.depth()?);

    Ok(())
}

fn assert_single_value(reader: &mut IonCReaderHandle, expected: &Elem, depth: i32) -> TestResult {
    assert_eq!(depth, reader.depth()?);
    let tid = reader.next()?;
    assert_eq!(depth, reader.depth()?);

    let annotations = expected.annotations.as_slice();
    let val = &expected.val;

    assert_eq!(annotations, reader.get_annotations()?.as_slice());

    // null check
    match val {
        Null(_) => {
            assert_eq!(true, reader.is_null()?);
        }
        _ => {
            assert_eq!(false, reader.is_null()?);
        }
    }

    // value/type check
    match val {
        Null(null_tid) => {
            assert_eq!(*null_tid, tid);
        }
        Bool(val) => {
            assert_eq!(ION_TYPE_BOOL, tid);
            assert_eq!(*val, reader.read_bool()?);
        }
        Int(val) => {
            assert_eq!(ION_TYPE_INT, tid);
            assert_eq!(*val, reader.read_i64()?);
        }
        Float(val) => {
            assert_eq!(ION_TYPE_FLOAT, tid);
            let actual = reader.read_f64()?;
            if val.is_finite() {
                assert_eq!(*val, actual);
            } else if val.is_infinite() {
                assert_eq!(true, actual.is_infinite());
                assert_eq!(val.signum(), actual.signum());
            } else {
                assert_eq!(true, val.is_nan());
                assert_eq!(true, actual.is_nan());
            }
        }
        Sym(val) => {
            assert_eq!(ION_TYPE_SYMBOL, tid);
            assert_eq!(*val, reader.read_string()?.as_str());
        }
        Str(val) => {
            assert_eq!(ION_TYPE_STRING, tid);
            assert_eq!(*val, reader.read_string()?.as_str());
        }
        Clob(val) => {
            assert_eq!(ION_TYPE_CLOB, tid);
            assert_eq!(*val, reader.read_bytes()?.as_slice());
        }
        Blob(val) => {
            assert_eq!(ION_TYPE_BLOB, tid);
            assert_eq!(*val, reader.read_bytes()?.as_slice());
        }
        List(vals) => {
            assert_eq!(ION_TYPE_LIST, tid);
            reader.step_in()?;
            for val in vals {
                assert_single_value(reader, val, depth + 1)?;
            }
            reader.step_out()?;
        }
        Sexp(vals) => {
            assert_eq!(ION_TYPE_SEXP, tid);
            reader.step_in()?;
            for val in vals {
                assert_single_value(reader, val, depth + 1)?;
            }
            reader.step_out()?;
        }
        Struct(fields) => {
            assert_eq!(ION_TYPE_STRUCT, tid);
            reader.step_in()?;
            for (name, val) in fields {
                assert_single_value(reader, val, depth + 1)?;
                assert_eq!(*name, reader.get_field_name()?.as_str());
            }
            reader.step_out()?;
        }
    }
    assert_eq!(depth, reader.depth()?);

    Ok(())
}
