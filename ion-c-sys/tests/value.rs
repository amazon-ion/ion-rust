// Copyright Amazon.com, Inc. or its affiliates.

use rstest::*;

use ion_c_sys::reader::*;
use ion_c_sys::timestamp::Mantissa::*;
use ion_c_sys::timestamp::TSOffsetKind::*;
use ion_c_sys::timestamp::TSPrecision::*;
use ion_c_sys::timestamp::*;
use ion_c_sys::*;

use Val::*;

use bigdecimal::BigDecimal;
use chrono::DateTime;
use std::convert::TryFrom;
use std::error::Error;

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

fn dec(lit: &str) -> Val {
    Decimal(BigDecimal::parse_bytes(lit.as_bytes(), 10).unwrap())
}

fn frac(lit: &str) -> Mantissa {
    Fraction(BigDecimal::parse_bytes(lit.as_bytes(), 10).unwrap())
}

fn ts(dt_lit: &str, precision: TSPrecision, offset_kind: TSOffsetKind) -> Val {
    let dt = DateTime::parse_from_rfc3339(dt_lit).unwrap();
    Timestamp(IonDateTime::try_new(dt, precision, offset_kind).unwrap())
}

/// Simplified value enum for our tests.
#[derive(Debug, Clone, PartialEq)]
enum Val {
    // scalars
    Null(ION_TYPE),
    Bool(bool),
    Int(i64),
    Float(f64),
    Decimal(BigDecimal),
    Timestamp(IonDateTime),
    Sym(&'static str),
    Str(&'static str),
    Clob(&'static [u8]),
    Blob(&'static [u8]),

    // aggregates
    List(Vec<Elem>),
    Sexp(Vec<Elem>),
    Struct(Vec<(&'static str, Elem)>),
}

#[derive(Debug)]
struct TestCase {
    lit: &'static str,
    bin: &'static [u8],
    elem: Elem,
}

enum TestMode {
    Text,
    Binary,
}

#[rstest(c,
    case::null(TestCase {
        lit: "null",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x0F],
        elem: Elem::new(Null(ION_TYPE_NULL)),
    }),
    case::null_bool(TestCase {
        lit: "null.bool",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x1F],
        elem: Elem::new(Null(ION_TYPE_BOOL)),
    }),
    case::null_int(TestCase {
        lit: "null.int",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x2F],
        elem: Elem::new(Null(ION_TYPE_INT)),
    }),
    case::null_float(TestCase {
        lit: "null.float",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x4F],
        elem: Elem::new(Null(ION_TYPE_FLOAT)),
    }),
    case::null_decimal(TestCase {
        lit: "null.decimal",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x5F],
        elem: Elem::new(Null(ION_TYPE_DECIMAL)),
    }),
    case::null_timestamp(TestCase {
        lit: "null.timestamp",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6F],
        elem: Elem::new(Null(ION_TYPE_TIMESTAMP)),
    }),
    case::null_symbol(TestCase {
        lit: "null.symbol",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x7F],
        elem: Elem::new(Null(ION_TYPE_SYMBOL)),
    }),
    case::null_string(TestCase {
        lit: "null.string",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x8F],
        elem: Elem::new(Null(ION_TYPE_STRING)),
    }),
    case::null_clob(TestCase {
        lit: "null.clob",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x9F],
        elem: Elem::new(Null(ION_TYPE_CLOB)),
    }),
    case::null_blob(TestCase {
        lit: "null.blob",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xAF],
        elem: Elem::new(Null(ION_TYPE_BLOB)),
    }),
    case::null_list(TestCase {
        lit: "null.list",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xBF],
        elem: Elem::new(Null(ION_TYPE_LIST)),
    }),
    case::null_sexp(TestCase {
        lit: "null.sexp",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xCF],
        elem: Elem::new(Null(ION_TYPE_SEXP)),
    }),
    case::null_struct(TestCase {
        lit: "null.struct",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xDF],
        elem: Elem::new(Null(ION_TYPE_STRUCT)),
    }),
    case::bool_true(TestCase {
        lit: "a::b::c::true",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xEC, 0x81, 0x83, 0xDE, 0x88, 0x87, 0xB6,
               0x81, 0x61, 0x81, 0x62, 0x81, 0x63, 0xE5, 0x83, 0x8A, 0x8B, 0x8C,
               0x11],
        elem: Elem::new_a(Bool(true), vec!["a", "b", "c"]),
    }),
    case::bool_false(TestCase {
        lit: "abcdefghijklmnop::false",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xEE, 0x99, 0x81, 0x83, 0xDE, 0x95, 0x87,
               0xBE, 0x92, 0x8E, 0x90, 0x61, 0x62, 0x63, 0x64, 0x65, 0x66, 0x67,
               0x68, 0x69, 0x6A, 0x6B, 0x6C, 0x6D, 0x6E, 0x6F, 0x70, 0xE3, 0x81,
               0x8A, 0x10],
        elem: Elem::new_a(Bool(false), vec!["abcdefghijklmnop"]),
    }),
    case::int_positive(TestCase {
        lit: "42",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x2A],
        elem: Elem::new(Int(42)),
    }),
    case::int_negative(TestCase {
        lit: "-10",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x0A],
        elem: Elem::new(Int(-10)),
    }),
    case::int_maxi64(TestCase {
        lit: "0x7fffffffffffffff",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x28, 0x7F, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF],
        elem: Elem::new(Int(0x7fffffffffffffff)),
    }),
    case::float(TestCase {
        lit: "3e0",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x48, 0x40, 0x08, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        elem: Elem::new(Float(3.0)),
    }),
    case::float_nan(TestCase {
        lit: "nan",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x48, 0x7F, 0xF8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        elem: Elem::new(Float(f64::NAN)),
    }),
    case::float_ninf(TestCase {
        lit: "-inf",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x48, 0xFF, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        elem: Elem::new(Float(f64::NEG_INFINITY)),
    }),
    case::float_pinf(TestCase {
        lit: "+inf",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x48, 0x7F, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
        elem: Elem::new(Float(f64::INFINITY)),
    }),
    case::decimal_p19_en13(TestCase {
        lit: "123123.7546745674467",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x59, 0xCD, 0x11, 0x16, 0x3C, 0x06, 0x7F, 0xE6, 0x3A, 0xE3],
        elem: Elem::new(dec("123123.7546745674467")),
    }),
    case::decimal_p28_en3000(TestCase {
        lit: "9174312341723649127364192734d-3000",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x5E, 0x8E, 0x57, 0xB8, 0x1D, 0xA4, 0xD0,
               0x34, 0x99, 0x0D, 0xDD, 0x28, 0xFB, 0xC4, 0x69, 0xDE],
        elem: Elem::new(dec("9174312341723649127364192734E-3000")),
    }),
    case::decimal_p34_e4000(TestCase {
        lit: "1743123417236491273641927340182374d4000",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x5E, 0x90, 0x1F, 0xA0, 0x55, 0xF1, 0x4F,
               0x88, 0x06, 0x74, 0x02, 0xE0, 0x13, 0x1D, 0xD4, 0x0F, 0xCB, 0x66],
        elem: Elem::new(dec("1743123417236491273641927340182374E4000")),
    }),
    case::timestamp_year(TestCase {
        lit: "2010T",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x63, 0xC0, 0x0F, 0xDA],
        elem: Elem::new(ts("2010-01-01T00:00:00Z", Year, UnknownOffset)),
    }),
    case::timestamp_month(TestCase {
        lit: "2010-10T",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x64, 0xC0, 0x0F, 0xDA, 0x8A],
        elem: Elem::new(ts("2010-10-01T00:00:00Z", Month, UnknownOffset)),
    }),
    case::timestamp_day(TestCase {
        lit: "2010-10-10T",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x65, 0xC0, 0x0F, 0xDA, 0x8A, 0x8A],
        elem: Elem::new(ts("2010-10-10T00:00:00Z", Day, UnknownOffset)),
    }),
    case::timestamp_minute_unknown(TestCase {
        lit: "2010-10-10T12:34-00:00",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x67, 0xC0, 0x0F, 0xDA, 0x8A, 0x8A, 0x8C, 0xA2],
        elem: Elem::new(ts("2010-10-10T12:34:00Z", Minute, UnknownOffset)),
    }),
    case::timestamp_minute_known(TestCase {
        lit: "2010-10-10T12:34+07:30",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x68, 0x03, 0xC2, 0x0F, 0xDA, 0x8A, 0x8A, 0x85, 0x84],
        elem: Elem::new(ts("2010-10-10T12:34:00+07:30", Minute, KnownOffset)),
    }),
    case::timestamp_second_unknown(TestCase {
        lit: "2010-10-10T12:34:56-00:00",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x68, 0xC0, 0x0F, 0xDA, 0x8A, 0x8A, 0x8C, 0xA2, 0xB8],
        elem: Elem::new(ts("2010-10-10T12:34:56.000000000-00:00", Second, UnknownOffset)),
    }),
    case::timestamp_second_known(TestCase {
        lit: "2010-10-10T12:34:56-08:15",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x69, 0x43, 0xEF, 0x0F, 0xDA, 0x8A, 0x8A, 0x94, 0xB1, 0xB8],
        elem: Elem::new(ts("2010-10-10T12:34:56.000000000-08:15", Second, KnownOffset)),
    }),
    case::timestamp_ms_unknown(TestCase {
        lit: "2010-10-10T12:34:56.123-00:00",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6A, 0xC0, 0x0F, 0xDA, 0x8A, 0x8A, 0x8C, 0xA2, 0xB8, 0xC3, 0x7B],
        elem: Elem::new(ts("2010-10-10T12:34:56.123000000-00:00", Fractional(Digits(3)), UnknownOffset)),
    }),
    case::timestamp_ms_known(TestCase {
        lit: "2010-10-10T12:34:56.001-08:15",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6B, 0x43, 0xEF, 0x0F, 0xDA, 0x8A, 0x8A, 0x94, 0xB1, 0xB8, 0xC3, 0x01],
        elem: Elem::new(ts("2010-10-10T12:34:56.001000000-08:15", Fractional(Digits(3)), KnownOffset)),
    }),
    case::timestamp_us_unknown(TestCase {
        lit: "2010-10-10T12:34:56.123456-00:00",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6C, 0xC0, 0x0F, 0xDA, 0x8A, 0x8A, 0x8C, 0xA2, 0xB8, 0xC6, 0x01, 0xE2, 0x40],
        elem: Elem::new(ts("2010-10-10T12:34:56.123456000-00:00", Fractional(Digits(6)), UnknownOffset)),
    }),
    case::timestamp_us_known(TestCase {
        lit: "2010-10-10T12:34:56.000001-08:15",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6B, 0x43, 0xEF, 0x0F, 0xDA, 0x8A, 0x8A, 0x94, 0xB1, 0xB8, 0xC6, 0x01],
        elem: Elem::new(ts("2010-10-10T12:34:56.000001000-08:15", Fractional(Digits(6)), KnownOffset)),
    }),
    case::timestamp_ns_unknown(TestCase {
        lit: "2010-10-10T12:34:56.123456789-00:00",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6D, 0xC0, 0x0F, 0xDA, 0x8A, 0x8A, 0x8C, 0xA2, 0xB8, 0xC9, 0x07, 0x5B, 0xCD, 0x15],
        elem: Elem::new(ts("2010-10-10T12:34:56.123456789-00:00", Fractional(Digits(9)), UnknownOffset)),
    }),
    case::timestamp_ns_known(TestCase {
        lit: "2010-10-10T12:34:56.000000001-08:15",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6B, 0x43, 0xEF, 0x0F, 0xDA, 0x8A, 0x8A, 0x94, 0xB1, 0xB8, 0xC9, 0x01],
        elem: Elem::new(ts("2010-10-10T12:34:56.000000001-08:15", Fractional(Digits(9)), KnownOffset)),
    }),
    case::timestamp_ps_unknown(TestCase {
        lit: "2010-10-10T12:34:56.123456789123-00:00",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6E, 0x8E, 0xC0, 0x0F, 0xDA, 0x8A, 0x8A, 0x8C, 0xA2, 0xB8, 0xCC, 0x1C, 0xBE, 0x99, 0x1A, 0x83],
        elem: Elem::new(ts("2010-10-10T12:34:56.123456789-00:00", Fractional(frac("0.123456789123")), UnknownOffset)),
    }),
    case::timestamp_ps_known(TestCase {
        lit: "2010-10-10T12:34:56.000000000001-08:15",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x6B, 0x43, 0xEF, 0x0F, 0xDA, 0x8A, 0x8A, 0x94, 0xB1, 0xB8, 0xCC, 0x01],
        elem: Elem::new(ts("2010-10-10T12:34:56.000000000-08:15", Fractional(frac("0.000000000001")), KnownOffset)),
    }),
    case::symbol(TestCase {
        lit: "'hello 👾!'",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xEE, 0x92, 0x81, 0x83, 0xDE, 0x8E, 0x87,
               0xBC, 0x8B, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0xF0, 0x9F, 0x91,
               0xBE, 0x21, 0x71, 0x0A],
        elem: Elem::new(Sym("hello 👾!")),
    }),
    case::string(TestCase {
        lit: "\"hello 💩!\"",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x8B, 0x68, 0x65, 0x6C, 0x6C, 0x6F, 0x20,
               0xF0, 0x9F, 0x92, 0xA9, 0x21],
        elem: Elem::new(Str("hello 💩!")),
    }),
    case::clob(TestCase {
        lit: "{{\"hello\"}}",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0x95, 0x68, 0x65, 0x6C, 0x6C, 0x6F],
        elem: Elem::new(Clob(b"hello")),
    }),
    case::blob(TestCase {
        lit: "{{d29ybGQ=}}",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xA5, 0x77, 0x6F, 0x72, 0x6C, 0x64],
        elem: Elem::new(Blob(b"world")),
    }),
    case::list(TestCase {
        lit: "[false, 0, 0e0]",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xB3, 0x10, 0x20, 0x40],
        elem: Elem::new(List(vec![
            Elem::new(Bool(false)),
            Elem::new(Int(0)),
            Elem::new(Float(0.0))
        ])),
    }),
    case::sexp(TestCase {
        lit: "(+ 1 2 3)",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xE8, 0x81, 0x83, 0xDE, 0x84, 0x87, 0xB2,
               0x81, 0x2B, 0xC8, 0x71, 0x0A, 0x21, 0x01, 0x21, 0x02, 0x21, 0x03],
        elem: Elem::new(Sexp(vec![
            Elem::new(Sym("+")),
            Elem::new(Int(1)),
            Elem::new(Int(2)),
            Elem::new(Int(3))])),
    }),
    case::structure(TestCase {
        lit: "{a:1, b:2, c:3}",
        bin: &[0xE0, 0x01, 0x00, 0xEA, 0xEC, 0x81, 0x83, 0xDE, 0x88, 0x87, 0xB6,
               0x81, 0x61, 0x81, 0x62, 0x81, 0x63, 0xDE, 0x89, 0x8A, 0x21, 0x01,
               0x8B, 0x21, 0x02, 0x8C, 0x21, 0x03],
        elem: Elem::new(Struct(vec![
            ("a", Elem::new(Int(1))),
            ("b", Elem::new(Int(2))),
            ("c", Elem::new(Int(3))),
        ])),
    }),
    mode => [TestMode::Text, TestMode::Binary],
)]
fn test_read_single(c: TestCase, mode: TestMode) -> TestResult {
    // copy into a mutable buffer as a defensive measure
    let mut reader = match mode {
        TestMode::Text => IonCReaderHandle::try_from(c.lit)?,
        TestMode::Binary => IonCReaderHandle::try_from(c.bin)?,
    };

    // TODO a bug in Ion C (amzn/ion-c#186) makes this fail on binary cases
    //assert_eq!(ION_TYPE_NONE, reader.get_type()?);

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
        Decimal(val) => {
            assert_eq!(ION_TYPE_DECIMAL, tid);
            let actual = reader.read_bigdecimal()?;
            assert_eq!(val, &actual);
        }
        Timestamp(val) => {
            assert_eq!(ION_TYPE_TIMESTAMP, tid);
            let actual = reader.read_datetime()?;
            assert_eq!(val, &actual);
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
