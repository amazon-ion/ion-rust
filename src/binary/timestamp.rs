// Copyright Amazon.com, Inc. or its affiliates.

use std::io::Write;

use arrayvec::ArrayVec;
use chrono::{Datelike, Timelike};

use crate::{
    binary::{uint::DecodedUInt, var_int::VarInt, var_uint::VarUInt, writer::MAX_INLINE_LENGTH},
    result::IonResult,
    types::timestamp::{Precision, Timestamp},
};

const ENCODED_BUFFER_SIZE: usize = 16;

/// Extends [`Timestamp`] to support [Ion binary].
///
/// [Ion binary]: https://amzn.github.io/ion-docs/docs/binary.html#6-timestamp
pub trait TimestampBinaryExt {
    fn encode_binary(&self) -> IonResult<ArrayVec<u8, { ENCODED_BUFFER_SIZE }>>;
    fn write_binary<W: Write>(&self, sink: &mut W) -> IonResult<()>;
}

impl TimestampBinaryExt for Timestamp {
    /// NOTE: Currently, this function always encodes with nanosecond precision.
    fn encode_binary(&self) -> IonResult<ArrayVec<u8, { ENCODED_BUFFER_SIZE }>> {
        const SECONDS_PER_MINUTE: f32 = 60f32;
        let mut sink = ArrayVec::new_const();
        // Each component of the timestamp is in UTC time. Readers then apply the offset minutes
        // to derive the localized time.
        let utc = self.date_time;

        // Ion encodes offsets in minutes while DateTime stores it in seconds.
        let offset_seconds = self.offset.map(|o| o.utc_minus_local()).unwrap_or(0);
        let offset_minutes = (offset_seconds as f32 / SECONDS_PER_MINUTE).round() as i64;
        VarInt::write_i64(&mut sink, offset_minutes)?;
        VarUInt::write_u64(&mut sink, utc.year() as u64)?;

        // So far, we've written required fields. The rest are optional!
        if self.precision > Precision::Year {
            VarUInt::write_u64(&mut sink, utc.month() as u64)?;
            if self.precision > Precision::Month {
                VarUInt::write_u64(&mut sink, utc.day() as u64)?;
                if self.precision > Precision::Day {
                    VarUInt::write_u64(&mut sink, utc.hour() as u64)?;
                    VarUInt::write_u64(&mut sink, utc.minute() as u64)?;
                    if self.precision > Precision::HourAndMinute {
                        VarUInt::write_u64(&mut sink, utc.second() as u64)?;
                    }
                    if self.precision > Precision::Second {
                        // This implementation always writes the datetime out with nanosecond precision.
                        // The nanoseconds are an integer, which means that our exponent is always 9
                        // and our coefficient is the number of nanoseconds.
                        let nanoseconds = utc.nanosecond();
                        const SCALE: i64 = -9; // "Scale" (used by BigDecimal) is -1 * exponent
                        VarInt::write_i64(&mut sink, SCALE)?;
                        DecodedUInt::write_u64(&mut sink, nanoseconds as u64)?;
                    }
                }
            }
        }

        Ok(sink)
    }

    /// Write a timestamp. Encodes the timestamp and prepends an appropriate
    /// type decriptor.
    fn write_binary<W: Write>(&self, sink: &mut W) -> IonResult<()> {
        let encoded = self.encode_binary()?;

        // Write the type descriptor and length.
        let type_descriptor: u8;
        if encoded.len() <= MAX_INLINE_LENGTH {
            type_descriptor = 0x60 | encoded.len() as u8;
            sink.write(&[type_descriptor])?;
        } else {
            type_descriptor = 0x6E;
            sink.write(&[type_descriptor])?;
            VarUInt::write_u64(sink, encoded.len() as u64)?;
        }

        sink.write(&encoded[..])?;

        Ok(())
    }
}

// Looking for the tests? See binary/writer.rs.
