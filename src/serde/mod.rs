pub mod datetime;
pub mod de;
pub mod ser;

pub use de::{from_slice, from_str, Deserializer};
pub use ser::{to_binary, to_pretty, to_string, Serializer};

#[cfg(test)]
mod tests {
    use crate::serde::{from_str, to_binary, to_pretty, to_string};
    
    use crate::Timestamp;
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
            date: Timestamp,
            #[serde_as(as = "crate::Timestamp")]
            date0: DateTime<Utc>,
            #[serde_as(as = "crate::Timestamp")]
            date1: DateTime<FixedOffset>,
        }
        let datetime: DateTime<FixedOffset> = Utc::now().into();
        let my_date0 = Utc::now();
        let my_date = Timestamp::from(datetime);
        let test = Test {
            int: 1,
            float: 3.14,
            binary: b"EDO".to_vec(),
            seq: vec!["a".to_string(), "b".to_string()],
            date: my_date.clone(),
            date0: my_date0.clone(),
            date1: datetime.clone(),
        };
        let result = to_string(&test).expect("failed to serialize");
        let presult = to_pretty(&test).expect("failed to serialize pretty style");
        let _bresult = to_binary(&test).expect("failed to serialize to binary");

        println!("Result: {}", presult);

        let back: Test = from_str(result.as_str()).expect("failed to deserialize");

        assert_eq!(back.int, 1);
        assert_eq!(back.float, 3.14);
        assert_eq!(back.binary, b"EDO");
        assert_eq!(back.seq.len(), 2);
        assert_eq!(back.date, my_date.clone());
        assert_eq!(back.date0, my_date0.clone());
        assert_eq!(back.date1, datetime.clone());
    }
}
