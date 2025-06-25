//! # Serialization and deserialization of Ion data
//!
//! This module offers APIs for serialization of Rust data structures into Ion data and deserialization
//! of Ion data into Rust data structures. The APIs use the `serde` framework for serialization and
//! deserialization. See [the Serde website](https://serde.rs/) for additional documentation and
//! usage examples. This feature doesn't yet support [Ion annotations] and [Ion SExpressions] for
//! serialization and deserialization.
//!
//! There are three different APIs for serializing Ion data:
//!
//! * `to_string`: Serialize an object into compact Ion text format.
//! * `to_pretty`: Serialize an object into pretty formatted Ion text.
//! * `to_binary`:  Serialize an object into Ion binary format.
//!
//! For deserialization `from_ion` API is provided through this module.
//!
//! ## Mapping of Ion data types to Rust and serde data types
//!
//!| Ion data type | Rust data structure                  | Serde data type                                       |
//!|---------------|--------------------------------------|-------------------------------------------------------|
//!| int           | u64, i64, u32, i32, u16, i16, u8, i8 | u64, i64, u32, i32, u16, i16, u8, i8                  |
//!| float         | f32, f64                             | f32, f64                                              |
//!| decimal       | Decimal(Ion Element API)             | newtype_struct (with name as `$__ion_rs_decimal__`)   |
//!| timestamp     | Timestamp(Ion Element API)           | newtype_struct (with name as `$__ion_rs_timestamp__`) |
//!| blob          | byte array                           | byte array                                            |
//!| clob          | byte array                           | byte array                                            |
//!| bool          | bool                                 | bool                                                  |
//!| symbol        | string                               | string                                                |
//!| string        | string                               | string                                                |
//!| struct        | struct                               | struct                                                |
//!| list          | vector                               | seq                                                   |
//!| null          | None                                 | unit                                                  |
//!
//! ## Mapping of serde data types to Ion representation
//!
//!| Serde data type                                              | Ion representation                          |
//!|--------------------------------------------------------------|---------------------------------------------|
//!| u64, i64, u32, i32, u16, i16, u8, i8                         | int                                         |
//!| char, string, unit_variant                                   | string                                      |
//!| byte-array                                                   | blob                                        |
//!| option                                                       | None - null, Some - based on other mappings |
//!| unit                                                         | null                                        |
//!| unit_struct                                                  | symbol                                      |
//!| seq, tuple, tuple_struct                                     | list                                        |
//!| newtype_struct, map, struct                                  | struct                                      |
//!| newtype_variant                                              | variant value with annotation               |
//!| struct_variant                                               | struct with annotation                      |
//!| tuple_variant                                                | list with annotation                        |
//!
//! _Note: Since the serde framework doesn't support [Ion decimal] and [Ion timestamp] types, distinct serialization
//! and deserialization of these types are defined in this module. It uses `newtype_struct` with `$__ion_rs_decimal__`
//! and `$__ion_rs_timestamp__` as struct names from [serde data model], to indicate serde framework to use Ion's
//! implementation of decimal and timestamp serialization and deserialization. If one wants to use [chrono::DateTime],
//! it needs to be tagged with `#[serde_as(as = crate::Timestamp)]`._
//!
//! ## Example of serialization of Rust struct into Ion data
//! ```
//! use ion_rs::IonResult;
//! use crate::ion_rs::serde::to_string;
//! use serde::{Deserialize, Serialize};
//!
//!#[derive(Serialize, Deserialize)]
//! struct Address {
//!     street: String,
//!     city: String,
//! }
//!
//! fn main() -> IonResult<()> {
//!     // data structure for representing address
//!     let address = Address {
//!         street: "10 Downing Street".to_owned(),
//!         city: "London".to_owned(),
//!     };
//!
//!     // serialize it to Ion text
//!     let ion = to_string(&address)?;
//!
//!     // assert that the serialized Ion data is as expected
//!     assert_eq!(r#"{street: "10 Downing Street", city: "London", } "#, ion);
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Example of deserialization of Ion data into Rust struct
//! ```
//! use ion_rs::IonResult;
//! use crate::ion_rs::serde::from_ion;
//! use serde::{Deserialize, Serialize};
//!
//!#[derive(Serialize, Deserialize)]
//! struct Address {
//!     street: String,
//!     city: String,
//! }
//!
//! fn main() -> IonResult<()> {
//!     // represents Ion data with address information
//!     let data = r#"
//!         {
//!             street: "10 Downing Street",
//!             city: "London"    
//!         }
//!     "#;
//!
//!     // deserialize Ion data into Rust struct for address
//!     let address: Address = from_ion(data)?;
//!
//!     // assert that the deserialized Rust struct has street and city field set correctly
//!     assert_eq!(address.street, "10 Downing Street");
//!     assert_eq!(address.city, "London");
//!
//!     Ok(())
//! }
//! ```
//!
//! ## Example of serialization and deserialization for Timestamp
//!```
//! use serde::{Deserialize, Serialize};
//! use ion_rs::Timestamp;
//! use ion_rs::IonResult;
//! use ion_rs::serde::from_ion;
//! use serde_with::serde_as;
//! use chrono::{Utc, TimeZone, FixedOffset, DateTime};
//!
//! #[serde_as]
//! #[derive(Serialize, Deserialize)]
//! struct Event {
//!     name: String,
//!     start_time: Timestamp,
//!     #[serde_as(as = "crate::Timestamp")]
//!     end_time: DateTime<FixedOffset>
//! }
//!
//! fn main() -> IonResult<()> {
//! // represents Ion data with event information
//! let data = r#"
//!         {
//!             name: "Annual Conference",
//!             start_time: 2023-01-01T16:30:00Z,
//!             end_time: 2023-01-01T18:00:00Z
//!         }
//!     "#;
//!
//!     // deserialize Ion data into Rust struct for event
//!     let event: Event = from_ion(data)?;
//!
//!     // assert that the deserialized Rust struct has name, start_time and end_time set correctly
//!     assert_eq!(event.name, "Annual Conference");
//!     assert_eq!(event.start_time, Timestamp::with_ymd(2023, 1, 1).with_hms(16, 30, 0).build()?);
//!     assert_eq!(event.end_time, Utc.with_ymd_and_hms(2023, 1, 1, 18, 0, 0).unwrap());
//!
//!    Ok(())
//! }
//! ```
//!
//! ## Example of serialization and deserialization for Decimal
//!```
//! use serde::{Deserialize, Serialize};
//! use ion_rs::Decimal;
//! use ion_rs::IonResult;
//! use ion_rs::serde::from_ion;
//!
//! #[derive(Serialize, Deserialize)]
//! struct Product {
//!     name: String,
//!     price: Decimal
//! }
//!
//! fn main() -> IonResult<()> {
//! // represents Ion data with product information
//! let data = r#"
//!         {
//!             name: "Chair",
//!             price: 35.5
//!         }
//!     "#;
//!
//!     // deserialize Ion data into Rust struct for product
//!     let product: Product = from_ion(data)?;
//!
//!     // assert that the deserialized Rust struct has name and price field set correctly
//!     assert_eq!(product.name, "Chair");
//!     assert_eq!(product.price, Decimal::new(355, -1));
//!
//!    Ok(())
//! }
//! ```
//!
//! [Ion annotations]: https://amazon-ion.github.io/ion-docs/docs/spec.html#annot
//! [Ion SExpressions]: https://amazon-ion.github.io/ion-docs/docs/spec.html#sexp
//! [Ion decimal]: https://amazon-ion.github.io/ion-docs/docs/spec.html#decimal
//! [Ion timestamp]: https://amazon-ion.github.io/ion-docs/docs/spec.html#timestamp
//! [serde data model]: https://serde.rs/data-model.html#types

pub mod de;
mod decimal;
pub mod ser;
mod timestamp;

pub use de::from_ion;
pub use ser::{to_binary, to_pretty, to_string};

#[cfg(test)]
#[cfg(feature = "experimental-serde")]
mod tests {
    use crate::serde::{from_ion, to_binary, to_pretty, to_string};
    use std::net::IpAddr;

    use crate::{Decimal, Element, Timestamp};
    use chrono::{DateTime, FixedOffset, Utc};
    use serde::{Deserialize, Serialize};
    use serde_with::serde_as;
    use rstest::*;

    #[rstest]
    #[case::i8(to_binary(&-1_i8).unwrap(),     &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x01])]
    #[case::i16(to_binary(&-1_i16).unwrap(),   &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x01])]
    #[case::i32(to_binary(&-1_i32).unwrap(),   &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x01])]
    #[case::i64(to_binary(&-1_i64).unwrap(),   &[0xE0, 0x01, 0x00, 0xEA, 0x31, 0x01])]
    #[case::u8(to_binary(&1_u8).unwrap(),      &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::u16(to_binary(&1_u16).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::u32(to_binary(&1_u32).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::u64(to_binary(&1_u64).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::f32(to_binary(&1_f32).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x44, 0x3f, 0x80, 0x00, 0x00])]
    #[case::f64(to_binary(&1_f64).unwrap(),    &[0xE0, 0x01, 0x00, 0xEA, 0x44, 0x3f, 0x80, 0x00, 0x00])]
    #[case::char(to_binary(&'a').unwrap(),     &[0xE0, 0x01, 0x00, 0xEA, 0x81, 0x61])]
    #[case::str(to_binary(&"a").unwrap(),      &[0xE0, 0x01, 0x00, 0xEA, 0x81, 0x61])]
    #[case::some(to_binary(&Some(1)).unwrap(), &[0xE0, 0x01, 0x00, 0xEA, 0x21, 0x01])]
    #[case::unit(to_binary(&()).unwrap(),      &[0xE0, 0x01, 0x00, 0xEA, 0x0F])]
    fn test_primitives_binary(#[case] ion_data: Vec<u8>, #[case] expected: &[u8]) {
        assert_eq!(&ion_data[..], expected);
    }

    #[rstest]
    #[case::i8(to_string(&-1_i8).unwrap(),     "-1")]
    #[case::i16(to_string(&-1_i16).unwrap(),   "-1")]
    #[case::i32(to_string(&-1_i32).unwrap(),   "-1")]
    #[case::i64(to_string(&-1_i64).unwrap(),   "-1")]
    #[case::u8(to_string(&1_u8).unwrap(),      "1")]
    #[case::u16(to_string(&1_u16).unwrap(),    "1")]
    #[case::u32(to_string(&1_u32).unwrap(),    "1")]
    #[case::u64(to_string(&1_u64).unwrap(),    "1")]
    #[case::char(to_string(&'a').unwrap(),     "\"a\"")]
    #[case::str(to_string(&"a").unwrap(),      "\"a\"")]
    #[case::some(to_string(&Some(1)).unwrap(), "1" )]
    #[case::unit(to_string(&()).unwrap(),      "null")]
    fn test_primitives_text(#[case] ion_data: String, #[case] expected: &str) {
        assert_eq!(ion_data.trim(), expected);
    }

    #[test]
    fn test_blob() {
        #[derive(Serialize, Deserialize)]
        struct Test {
            #[serde(with = "serde_bytes")]
            binary: Vec<u8>,
        }
        let expected = &[
            0xE0, 0x01, 0x00, 0xEA,                               // IVM
            0xEE, 0x8F, 0x81, 0x83, 0xDC,                         // $ion_symbol_table:: {
            0x86, 0x71, 0x03,                                     //   imports: $ion_symbol_table,
            0x87, 0xB7, 0x86, 0x62, 0x69, 0x6E, 0x61, 0x72, 0x79, // symbols: ["binary"] ]}
            0xD7, 0x8A, 0xA5, 0x68, 0x65, 0x6C, 0x6C, 0x6F,       // {binary: {{ aGVsbG8= }}
        ];

        let test = Test { binary: b"hello".to_vec() }; // aGVsbG8=
        let ion_data = to_binary(&test).unwrap();
        assert_eq!(&ion_data[..], expected);
        let de: Test = from_ion(ion_data).expect("unable to parse test");
        assert_eq!(de.binary, test.binary);

        let ion_data_str = to_string(&test).unwrap();
        assert_eq!(ion_data_str.trim(), "{binary: {{aGVsbG8=}}, }");
        let de: Test = from_ion(ion_data_str).expect("unable to parse test");
        assert_eq!(de.binary, test.binary);
    }

    #[test]
    fn test_struct() {
        #[serde_as]
        #[derive(Serialize, Deserialize)]
        struct Test {
            int: u32,
            float: f64,
            #[serde(with = "serde_bytes")]
            binary: Vec<u8>,
            seq: Vec<String>,
            decimal: Decimal,
            date: Timestamp,
            #[serde_as(as = "crate::Timestamp")]
            date0: DateTime<Utc>,
            #[serde_as(as = "crate::Timestamp")]
            date1: DateTime<FixedOffset>,
            nested_struct: NestedTest,
            unit_struct: UnitStruct,
            newtype_struct: NewTypeStruct,
            tuple_struct: TupleStruct,
            optional: Option<i64>,
        }

        #[serde_as]
        #[derive(Serialize, Deserialize)]
        struct NestedTest {
            boolean: bool,
            str: String,
        }

        #[serde_as]
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct UnitStruct;

        #[serde_as]
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct NewTypeStruct(i64);

        #[serde_as]
        #[derive(Debug, Serialize, Deserialize, PartialEq)]
        struct TupleStruct(i64, i64);

        let datetime: DateTime<FixedOffset> = Utc::now().into();
        let my_date0 = Utc::now();
        let my_date = Timestamp::from(datetime);
        let my_decimal = Decimal::new(1225, -2);
        let test = Test {
            int: 1,
            float: 3.46,
            binary: b"EDO".to_vec(),
            seq: vec!["a".to_string(), "b".to_string()],
            decimal: my_decimal,
            date: my_date,
            date0: my_date0,
            date1: datetime,
            nested_struct: NestedTest {
                boolean: true,
                str: "hello".to_string(),
            },

            unit_struct: UnitStruct,
            newtype_struct: NewTypeStruct(5),
            tuple_struct: TupleStruct(5, 10),
            optional: None,
        };

        let result = to_pretty(&test).expect("failed to serialize");
        println!("result: {}", result);
        let back_result: Test = from_ion(result.as_str()).expect("failed to deserialize");

        assert_eq!(back_result.int, 1);
        assert_eq!(back_result.float, 3.46);
        assert_eq!(back_result.binary, b"EDO");
        assert_eq!(back_result.seq.len(), 2);
        assert_eq!(back_result.seq[0], "a");
        assert_eq!(back_result.seq[1], "b");
        assert_eq!(back_result.decimal, my_decimal.clone());
        assert_eq!(back_result.date, my_date.clone());
        assert_eq!(back_result.date0, my_date0.clone());
        assert_eq!(back_result.date1, datetime.clone());
        assert!(back_result.nested_struct.boolean);
        assert_eq!(&back_result.nested_struct.str, "hello");
        assert_eq!(back_result.unit_struct, UnitStruct);
        assert_eq!(back_result.newtype_struct, NewTypeStruct(5));
        assert_eq!(back_result.tuple_struct, TupleStruct(5, 10));
        assert_eq!(back_result.optional, None);
    }

    #[test]
    fn test_enum() {
        #[serde_as]
        #[derive(Serialize, Deserialize, PartialEq, Debug)]
        enum E {
            Unit,
            Newtype(u32),
            Tuple(u32, u32),
            Struct { a: u32 },
        }

        let i = r#"Unit"#;
        let expected = E::Unit;
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"Newtype::1"#;
        let expected = E::Newtype(1);
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"Tuple::[1, 2]"#;
        let expected = E::Tuple(1, 2);
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"Struct::{a: 1}"#;
        let expected = E::Struct { a: 1 };
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );
    }

    #[test]
    fn test_nested_newtype_variant() {
        #[derive(Serialize, Deserialize, PartialEq, Debug)]
        enum Outter {
            First(Inner),
        }

        #[derive(Serialize, Deserialize, PartialEq, Debug)]
        enum Inner {
            Second(u32),
        }

        let expected_binary = [
            0xE0, 0x01, 0x00, 0xEA,                          // IVM
            0xEE, 0x96, 0x81, 0x83,                          // $ion_symbol_table::
            0xDE, 0x92, 0x86, 0x71, 0x03,                    // { imports: $ion_symbol_table,
            0x87, 0xBD, 0x85, 0x46, 0x69, 0x72, 0x73, 0x74,  //   symbols: ["First",
            0x86, 0x53, 0x65, 0x63, 0x6F, 0x6E, 0x64,        //             "Second"]}
            0xE5, 0x82, 0x8A, 0x8B, 0x21, 0x03,              // First::Second::3

        ];

        let i = r#"First::Second::3"#;
        let expected = Outter::First(Inner::Second(3));
        assert_eq!(expected, from_ion(i).unwrap());

        let b = to_binary(&expected).unwrap();
        assert_eq!(expected_binary, &b[..]);
    }

    #[test]
    fn test_symbol() {
        let i = r#"inches"#;
        let expected = String::from("inches");
        assert_eq!(expected, from_ion::<String, _>(i).unwrap());

        let i = r#"'with space'"#;
        let expected = String::from("with space");
        assert_eq!(expected, from_ion::<String, _>(i).unwrap());

        let i = r#"'\'embedded quotes\''"#;
        let expected = String::from("'embedded quotes'");
        assert_eq!(expected, from_ion::<String, _>(i).unwrap());
    }

    #[test]
    fn human_readable() {
        // IpAddr has different repr based on if codec is considered
        // human readable or not {true: string, false: byte array}
        let ip: IpAddr = "127.0.0.1".parse().unwrap();
        let expected_binary = [
            224, 1, 0, 234, 235, 129, 131, 216, 134, 113, 3, 135, 179, 130, 86, 52, 233, 129, 138,
            182, 33, 127, 32, 32, 33, 1,
        ];
        let expected_s = "\"127.0.0.1\" ";
        let binary = to_binary(&ip).unwrap();
        let s = to_string(&ip).unwrap();
        assert_eq!(&binary[..], &expected_binary[..]);
        assert_eq!(s, expected_s);
        assert_eq!(&from_ion::<IpAddr, _>(s).unwrap(), &ip);
        assert_eq!(&from_ion::<IpAddr, _>(binary).unwrap(), &ip);
    }
}
