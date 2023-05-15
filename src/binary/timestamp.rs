// Copyright Amazon.com, Inc. or its affiliates.

use std::io::Write;
use std::ops::Neg;

use arrayvec::ArrayVec;
use chrono::{Datelike, Timelike};

use crate::binary::decimal::DecimalBinaryEncoder;
use crate::binary::raw_binary_writer::MAX_INLINE_LENGTH;
use crate::binary::var_int::VarInt;
use crate::binary::var_uint::VarUInt;
use crate::result::IonResult;
use crate::types::{Decimal, Mantissa, Precision, Timestamp};

const MAX_TIMESTAMP_LENGTH: usize = 32;

/// Provides support to write [`Timestamp`] into [Ion binary].
///
/// [Ion binary]: https://amazon-ion.github.io/ion-docs/docs/binary.html#6-timestamp
pub trait TimestampBinaryEncoder {
    /// Encodes the content of a [`Timestamp`] as per the Ion binary encoding.
    /// Returns the length of the encoded bytes.
    ///
    /// This does not encode the type descriptor nor the associated length.
    /// Prefer [`TimestampBinaryEncoder::encode_timestamp_value`] for that.
    fn encode_timestamp(&mut self, timestamp: &Timestamp) -> IonResult<usize>;

    /// Encodes a [`Timestamp`] as an Ion value with the type descriptor and length.
    /// Returns the length of the encoded bytes.
    fn encode_timestamp_value(&mut self, timestamp: &Timestamp) -> IonResult<usize>;
}

impl<W> TimestampBinaryEncoder for W
where
    W: Write,
{
    fn encode_timestamp(&mut self, timestamp: &Timestamp) -> IonResult<usize> {
        const SECONDS_PER_MINUTE: f32 = 60f32;
        let mut bytes_written: usize = 0;

        // Each unit of the binary-encoded timestamp (hour, minute, etc) is written in UTC.
        // The reader is expected to apply the encoded offset (in minutes) to derive the local time.

        // [Timestamp]s are modeled as a UTC NaiveDateTime and an optional FixedOffset.
        // We can use the UTC NaiveDateTime to query for the individual time fields (year, month,
        // etc) that we need to write out.
        let utc = timestamp.date_time;

        // Write out the offset (minutes difference from UTC). If the offset is
        // unknown, negative zero is used.
        if let Some(offset) = timestamp.offset {
            // Ion encodes offsets in minutes while chrono's DateTime stores it in seconds.
            let offset_seconds = offset.local_minus_utc();
            let offset_minutes = (offset_seconds as f32 / SECONDS_PER_MINUTE).round() as i64;
            bytes_written += VarInt::write_i64(self, offset_minutes)?;
        } else {
            // The offset is unknown. Write negative zero.
            bytes_written += VarInt::write_negative_zero(self)?;
        }

        bytes_written += VarUInt::write_u64(self, utc.year() as u64)?;

        // So far, we've written required fields. The rest are optional!
        if timestamp.precision > Precision::Year {
            bytes_written += VarUInt::write_u64(self, utc.month() as u64)?;
            if timestamp.precision > Precision::Month {
                bytes_written += VarUInt::write_u64(self, utc.day() as u64)?;
                if timestamp.precision > Precision::Day {
                    bytes_written += VarUInt::write_u64(self, utc.hour() as u64)?;
                    bytes_written += VarUInt::write_u64(self, utc.minute() as u64)?;
                    if timestamp.precision > Precision::HourAndMinute {
                        bytes_written += VarUInt::write_u64(self, utc.second() as u64)?;
                        if let Some(ref mantissa) = timestamp.fractional_seconds {
                            // TODO: Both branches encode directly due to one
                            // branch owning vs borrowing the decimal
                            // representation. #286 should provide a fix.
                            match mantissa {
                                Mantissa::Digits(precision) => {
                                    // Consider the following case: `2000-01-01T00:00:00.123Z`.
                                    // That's 123 millis, or 123,000,000 nanos.
                                    // Our mantissa is 0.123, or 123d-3.
                                    let scaled = utc.nanosecond() / 10u32.pow(9 - *precision); // 123,000,000 -> 123
                                    let exponent = (*precision as i64).neg(); // -3
                                    let fractional = Decimal::new(scaled, exponent); // 123d-3
                                    bytes_written += self.encode_decimal(&fractional)?;
                                }
                                Mantissa::Arbitrary(decimal) => {
                                    bytes_written += self.encode_decimal(decimal)?;
                                }
                            };
                        }
                    }
                }
            }
        }

        Ok(bytes_written)
    }

    fn encode_timestamp_value(&mut self, timestamp: &Timestamp) -> IonResult<usize> {
        let mut bytes_written: usize = 0;

        // First encode the timestamp. We need to know the encoded length before
        // we can compute and write out the type descriptor.
        let mut encoded: ArrayVec<u8, MAX_TIMESTAMP_LENGTH> = ArrayVec::new();
        encoded.encode_timestamp(timestamp)?;

        // Write the type descriptor and length.
        let type_descriptor: u8;
        if encoded.len() <= MAX_INLINE_LENGTH {
            type_descriptor = 0x60 | encoded.len() as u8;
            self.write_all(&[type_descriptor])?;
            bytes_written += 1;
        } else {
            type_descriptor = 0x6E;
            self.write_all(&[type_descriptor])?;
            bytes_written += 1;
            bytes_written += VarUInt::write_u64(self, encoded.len() as u64)?;
        }

        // Now we can write out the encoded timestamp!
        self.write_all(&encoded[..])?;
        bytes_written += &encoded[..].len();

        Ok(bytes_written)
    }
}

#[cfg(test)]
mod binary_timestamp_tests {
    use super::*;
    use crate::{reader, IonReader, IonType, ReaderBuilder};
    use rstest::*;

    // These tests show how varying levels of precision affects number of bytes
    // written (for binary encoding of timestamps).
    #[rstest]
    #[case::y2k_utc("2000-01-01T00:00:00+00:00", 9)]
    #[case::seconds_utc("2021-01-08T14:12:36+00:00", 9)]
    #[case::seconds_tz("2021-01-08T14:12:36-05:00", 10)]
    #[case::millis_tz("2021-01-08T14:12:36.888-05:00", 13)]
    #[case::micros_tz("2021-01-08T14:12:36.888888-05:00", 14)]
    #[case::nanos_tz("2021-01-08T14:12:36.888888888-05:00", 16)]
    fn timestamp_encoding_bytes_written(
        #[case] input: &str,
        #[case] expected: usize,
    ) -> IonResult<()> {
        let mut reader = ReaderBuilder::new().build(input).unwrap();
        match reader.next().unwrap() {
            reader::StreamItem::Value(IonType::Timestamp) => {
                let timestamp = reader.read_timestamp().unwrap();
                let mut buf = vec![];
                let written = buf.encode_timestamp_value(&timestamp)?;
                assert_eq!(buf.len(), expected);
                assert_eq!(written, expected);
            }
            _ => panic!(
                "reader.next() should only return reader::StreamItem::Value(IonType::Timestamp)"
            ),
        }
        Ok(())
    }
}
