// Copyright Amazon.com, Inc. or its affiliates.

use std::io::Write;

use arrayvec::ArrayVec;

use crate::binary::decimal::DecimalBinaryEncoder;
use crate::binary::var_int::VarInt;
use crate::binary::var_uint::VarUInt;
use crate::result::IonResult;
use crate::types::TimestampPrecision;
use crate::Timestamp;

const MAX_INLINE_LENGTH: usize = 13;
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
        let mut bytes_written: usize = 0;

        // Ion 1.0 binary encodes timestamp fields in UTC.
        // First, convert local fields to UTC by subtracting the offset.
        let utc = timestamp.to_utc();

        // Write offset (minutes from UTC). Unknown offset = negative zero.
        if let Some(offset_minutes) = timestamp.offset() {
            bytes_written += VarInt::write_i64(self, offset_minutes as i64)?;
        } else {
            bytes_written += VarInt::write_negative_zero(self)?;
        }

        bytes_written += VarUInt::write_u64(self, utc.year() as u64)?;

        let precision = timestamp.precision();
        if precision > TimestampPrecision::Year {
            bytes_written += VarUInt::write_u64(self, utc.month() as u64)?;
            if precision > TimestampPrecision::Month {
                bytes_written += VarUInt::write_u64(self, utc.day() as u64)?;
                if precision > TimestampPrecision::Day {
                    bytes_written += VarUInt::write_u64(self, utc.hour() as u64)?;
                    bytes_written += VarUInt::write_u64(self, utc.minute() as u64)?;
                    if precision > TimestampPrecision::HourAndMinute {
                        bytes_written += VarUInt::write_u64(self, utc.second() as u64)?;
                        if let Some(decimal) = timestamp.fractional_seconds_as_decimal() {
                            bytes_written += self.encode_decimal(&decimal)?;
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
    use crate::lazy::any_encoding::AnyEncoding;
    use crate::lazy::reader::Reader;
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
        let mut reader = Reader::new(AnyEncoding, input)?;
        let timestamp = reader.expect_next()?.read()?.expect_timestamp()?;
        let mut buf = vec![];
        let written = buf.encode_timestamp_value(&timestamp)?;
        assert_eq!(buf.len(), expected);
        assert_eq!(written, expected);
        Ok(())
    }
}
