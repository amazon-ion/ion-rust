// Copyright Amazon.com, Inc. or its affiliates.

use std::io::{self, Write};

use arrayvec::ArrayVec;
use bytes::BufMut;
use chrono::{Datelike, Timelike};

use crate::{
    binary::{uint::DecodedUInt, var_int::VarInt, var_uint::VarUInt, writer::MAX_INLINE_LENGTH},
    result::IonResult,
    types::timestamp::{Precision, Timestamp},
};

/// Extends [`Timestamp`] to support [Ion binary].
///
/// [Ion binary]: https://amzn.github.io/ion-docs/docs/binary.html#6-timestamp
impl Timestamp {
    const BUFFER_SIZE: usize = 16;

    /// NOTE: Currently, this function always encodes with nanosecond precision.
    pub fn encode_binary(&self) -> IonResult<ArrayVec<u8, { Timestamp::BUFFER_SIZE }>> {
        const SECONDS_PER_MINUTE: f32 = 60f32;
        let mut buffer = ArrayVec::new_const();
        // When we pass our buffer into the cursor, it will use the buffer as a
        // slice and refuse to write past `len`. Our `len` is 0, so that's no
        // good. We set our len to capacity so that `std::io::Write::write_all`
        // will not think it's out of capacity. Later, we clamp the len back
        // down to the number of bytes written.
        //
        // Alternatively, we could use a second buffer here and then copy the
        // data back over. Or, we could fill the buffer with 0s (slowly
        // increasing len by 1 until capacity).
        unsafe {
            buffer.set_len(Timestamp::BUFFER_SIZE);
        }
        let mut writer = io::Cursor::new(&mut buffer).writer();

        // Each component of the timestamp is in UTC time. Readers then apply the offset minutes
        // to derive the localized time.
        let utc = self.date_time;

        // Ion encodes offsets in minutes while DateTime stores it in seconds.
        let offset_seconds = self.offset.map(|o| o.utc_minus_local()).unwrap_or(0);
        let offset_minutes = (offset_seconds as f32 / SECONDS_PER_MINUTE).round() as i64;
        VarInt::write_i64(&mut writer, offset_minutes)?;

        VarUInt::write_u64(&mut writer, utc.year() as u64)?;
        VarUInt::write_u64(&mut writer, utc.month() as u64)?;

        // So far, we've written required fields. The rest are optional!
        if self.precision > Precision::Month {
            VarUInt::write_u64(&mut writer, utc.day() as u64)?;
            if self.precision > Precision::Day {
                VarUInt::write_u64(&mut writer, utc.hour() as u64)?;
                VarUInt::write_u64(&mut writer, utc.minute() as u64)?;
                if self.precision > Precision::HourAndMinute {
                    VarUInt::write_u64(&mut writer, utc.second() as u64)?;
                }
                if self.precision > Precision::Second {
                    // This implementation always writes the datetime out with nanosecond precision.
                    // The nanoseconds are an integer, which means that our exponent is always 9
                    // and our coefficient is the number of nanoseconds.
                    let nanoseconds = utc.nanosecond();
                    const SCALE: i64 = -9; // "Scale" (used by BigDecimal) is -1 * exponent
                    VarInt::write_i64(&mut writer, SCALE)?;
                    DecodedUInt::write_u64(&mut writer, nanoseconds as u64)?;
                }
            }
        }

        let encoded_length = writer.get_ref().position() as usize;
        // See previous unsafe note.
        unsafe {
            buffer.set_len(encoded_length);
        }

        Ok(buffer)
    }
}

pub trait TimestampBinaryExt {
    fn write_timestamp(&mut self, value: &Timestamp) -> IonResult<()>;
}

impl<W> TimestampBinaryExt for W
where
    W: Write,
{
    /// Write a timestamp. Encodes the timestamp and prepends an appropriate
    /// type decriptor.
    fn write_timestamp(&mut self, value: &Timestamp) -> IonResult<()> {
        let encoded = value.encode_binary()?;

        // Write the type descriptor, length, and then flush our stack buffer.
        let type_descriptor: u8;
        if encoded.len() <= MAX_INLINE_LENGTH {
            type_descriptor = 0x60 | encoded.len() as u8;
            self.write(&[type_descriptor])?;
        } else {
            type_descriptor = 0x6E;
            self.write(&[type_descriptor])?;
            VarUInt::write_u64(self, encoded.len() as u64)?;
        }

        self.write(&encoded[..])?;

        Ok(())
    }
}

// Looking for the tests? See binary/writer.rs.
