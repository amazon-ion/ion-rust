// Copyright Amazon.com, Inc. or its affiliates.

use std::io::Write;

use arrayvec::ArrayVec;
use chrono::{Datelike, Timelike};

use crate::{
    binary::{uint::DecodedUInt, var_int::VarInt, var_uint::VarUInt, writer::MAX_INLINE_LENGTH},
    result::IonResult,
    types::timestamp::{Precision, Timestamp},
};

const MAX_TIMESTAMP_LENGTH: usize = 16;

/// Provides support to write [`Timestamp`] into [Ion binary].
///
/// [Ion binary]: https://amzn.github.io/ion-docs/docs/binary.html#6-timestamp
// TODO: Change these methods to return the number of bytes written. #283
pub trait TimestampBinaryEncoder {
    /// Encodes the content of a [`Timestamp`] as per the Ion binary encoding.
    /// Returns the length of the encoded bytes.
    ///
    /// This does not encode the type descriptor nor the associated length.
    /// Prefer [`TimestampBinaryEncoder::encode_timestamp_value`] for that.
    fn encode_timestamp(&mut self, timestamp: &Timestamp) -> IonResult<()>;

    /// Encodes a [`Timestamp`] as an Ion value with the type descriptor and length.
    /// Returns the length of the encoded bytes.
    fn encode_timestamp_value(&mut self, timestamp: &Timestamp) -> IonResult<()>;
}

impl<W> TimestampBinaryEncoder for W
where
    W: Write,
{
    /// NOTE: Currently, this function always encodes with nanosecond precision.
    fn encode_timestamp(&mut self, timestamp: &Timestamp) -> IonResult<()> {
        const SECONDS_PER_MINUTE: f32 = 60f32;

        // Each component of the timestamp is in UTC time. Readers then apply the offset minutes
        // to derive the localized time.
        let utc = timestamp.date_time;

        // Write out the offset (minutes difference from UTC). If the offset is
        // unknown, negative zero is used.
        if let Some(offset) = timestamp.offset {
            // Ion encodes offsets in minutes while DateTime stores it in seconds.
            let offset_seconds = offset.local_minus_utc();
            let offset_minutes = (offset_seconds as f32 / SECONDS_PER_MINUTE).round() as i64;
            VarInt::write_i64(self, offset_minutes)?;
        } else {
            VarInt::write_negative_zero(self)?;
        }

        VarUInt::write_u64(self, utc.year() as u64)?;

        // So far, we've written required fields. The rest are optional!
        if timestamp.precision > Precision::Year {
            VarUInt::write_u64(self, utc.month() as u64)?;
            if timestamp.precision > Precision::Month {
                VarUInt::write_u64(self, utc.day() as u64)?;
                if timestamp.precision > Precision::Day {
                    VarUInt::write_u64(self, utc.hour() as u64)?;
                    VarUInt::write_u64(self, utc.minute() as u64)?;
                    if timestamp.precision > Precision::HourAndMinute {
                        VarUInt::write_u64(self, utc.second() as u64)?;
                    }
                    if timestamp.precision > Precision::Second {
                        // This implementation always writes the datetime out with nanosecond precision.
                        // The nanoseconds are an integer, which means that our exponent is always 9
                        // and our coefficient is the number of nanoseconds.
                        let nanoseconds = utc.nanosecond();
                        const SCALE: i64 = -9; // "Scale" (used by BigDecimal) is -1 * exponent
                        VarInt::write_i64(self, SCALE)?;
                        DecodedUInt::write_u64(self, nanoseconds as u64)?;
                    }
                }
            }
        }

        Ok(())
    }

    fn encode_timestamp_value(&mut self, timestamp: &Timestamp) -> IonResult<()> {
        // First encode the timestamp. We need to know the encoded length before
        // we can compute and write out the type descriptor.
        let mut encoded: ArrayVec<u8, MAX_TIMESTAMP_LENGTH> = ArrayVec::new();
        encoded.encode_timestamp(timestamp)?;

        // Write the type descriptor and length.
        let type_descriptor: u8;
        if encoded.len() <= MAX_INLINE_LENGTH {
            type_descriptor = 0x60 | encoded.len() as u8;
            self.write(&[type_descriptor])?;
        } else {
            type_descriptor = 0x6E;
            self.write(&[type_descriptor])?;
            VarUInt::write_u64(self, encoded.len() as u64)?;
        }

        // Now we can write out the encoded timestamp!
        self.write(&encoded[..])?;

        Ok(())
    }
}

// Looking for the tests? See binary/writer.rs.
