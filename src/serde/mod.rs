pub mod de;
pub mod decimal;
pub mod ser;
pub mod timestamp;

pub use de::{from_ion, Deserializer};
pub use ser::{to_binary, to_pretty, to_string, Serializer};

#[cfg(test)]
#[cfg(feature = "experimental-serde")]
mod tests {
    use crate::serde::{from_ion, to_string};

    use crate::{Decimal, Timestamp};
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
        }

        #[serde_as]
        #[derive(Serialize, Deserialize)]
        struct NestedTest {
            boolean: bool,
            str: String,
        }

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
        };

        let result = to_string(&test).expect("failed to serialize");

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
    }
}
