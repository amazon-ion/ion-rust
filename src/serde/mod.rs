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
//!| unit, unit_struct                                            | null                                        |
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
//!     use ion_rs::{Element, ion_struct};
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
    use crate::serde::{from_ion, to_pretty, to_string};

    use crate::{Decimal, Element, Timestamp};
    use chrono::{DateTime, FixedOffset, Utc};
    use serde::{Deserialize, Serialize};
    use serde_with::serde_as;

    #[test]
    fn test_struct() {
        #[serde_as]
        #[derive(Serialize, Deserialize)]
        struct Test {
            int: u32,
            float: f64,
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
            decimal: my_decimal.clone(),
            date: my_date.clone(),
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

        let i = r#"E::Unit"#;
        let expected = E::Unit;
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"E::Newtype::1"#;
        let expected = E::Newtype(1);
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"E::Tuple::[1, 2]"#;
        let expected = E::Tuple(1, 2);
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );

        let i = r#"E::Struct::{a: 1}"#;
        let expected = E::Struct { a: 1 };
        assert_eq!(expected, from_ion(i).unwrap());
        assert_eq!(
            Element::read_first(i),
            Element::read_first(to_string(&expected).unwrap())
        );
    }
}
