// Copyright Amazon.com, Inc. or its affiliates.

use bytes::BufMut;
use chrono::{DateTime, Datelike, FixedOffset, Timelike};
use std::io::{self, Write};

use crate::{
    binary::{uint::DecodedUInt, var_int::VarInt, var_uint::VarUInt, writer::MAX_INLINE_LENGTH},
    result::IonResult,
};

/// NOTE: Currently, this function always writes a timestamp with nanosecond precision.
// TODO: Provide a `write_datetime_with_precision` method.
pub fn write_datetime<W: Write>(value: &DateTime<FixedOffset>, sink: &mut W) -> IonResult<()> {
    const TIMESTAMP_BUFFER_SIZE: usize = 16;
    const SECONDS_PER_MINUTE: f32 = 60f32;
    let mut buffer = [0u8; TIMESTAMP_BUFFER_SIZE];
    let mut writer = io::Cursor::new(&mut buffer).writer();

    // Each component of the timestamp is in UTC time. Readers then apply the offset minutes
    // to derive the localized time.
    let utc = value.naive_utc();

    // Ion encodes offsets in minutes while DateTime stores it in seconds.
    let offset_seconds = value.offset().utc_minus_local();
    let offset_minutes = (offset_seconds as f32 / SECONDS_PER_MINUTE).round() as i64;
    VarInt::write_i64(&mut writer, offset_minutes)?;

    VarUInt::write_u64(&mut writer, utc.year() as u64)?;
    VarUInt::write_u64(&mut writer, utc.month() as u64)?;
    VarUInt::write_u64(&mut writer, utc.day() as u64)?;
    VarUInt::write_u64(&mut writer, utc.hour() as u64)?;
    VarUInt::write_u64(&mut writer, utc.minute() as u64)?;
    VarUInt::write_u64(&mut writer, utc.second() as u64)?;

    // This implementation always writes the datetime out with nanosecond precision.
    // The nanoseconds are an integer, which means that our exponent is always 9
    // and our coefficient is the number of nanoseconds.
    let nanoseconds = utc.nanosecond();
    const SCALE: i64 = -9; // "Scale" (used by BigDecimal) is -1 * exponent
    VarInt::write_i64(&mut writer, SCALE)?;
    DecodedUInt::write_u64(&mut writer, nanoseconds as u64)?;

    let encoded_length = writer.get_ref().position() as usize;

    // Write the type descriptor, length, and then flush our stack buffer.
    let type_descriptor: u8;
    if encoded_length <= MAX_INLINE_LENGTH {
        type_descriptor = 0x60 | encoded_length as u8;
        sink.write(&[type_descriptor])?;
    } else {
        type_descriptor = 0x6E;
        sink.write(&[type_descriptor])?;
        VarUInt::write_u64(sink, encoded_length as u64)?;
    }
    let raw_buffer = writer.into_inner().into_inner();
    sink.write(&raw_buffer[..encoded_length])?;

    Ok(())
}
