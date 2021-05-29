// Copyright Amazon.com, Inc. or its affiliates.

use std::io::{self, Write};

use bytes::BufMut;
use chrono::{DateTime, Datelike, FixedOffset, Timelike};
use smallvec::SmallVec;

use crate::{
    binary::{uint::DecodedUInt, var_int::VarInt, var_uint::VarUInt, writer::MAX_INLINE_LENGTH},
    result::IonResult,
};

// TODO: Provide a `write_datetime_with_precision` method.
pub fn write_datetime<W: Write>(value: &DateTime<FixedOffset>, sink: &mut W) -> IonResult<()> {
    let encoded = encode_datetime(value)?;

    // Write the type descriptor, length, and then flush our stack buffer.
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

const TIMESTAMP_BUFFER_SIZE: usize = 16;

/// NOTE: Currently, this function always encodes with nanosecond precision.
pub fn encode_datetime(
    value: &DateTime<FixedOffset>,
) -> IonResult<SmallVec<[u8; TIMESTAMP_BUFFER_SIZE]>> {
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
    let slice = &writer.into_inner().into_inner()[..encoded_length];
    let encoded = SmallVec::from(slice);

    Ok(encoded)
}
