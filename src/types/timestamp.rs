use crate::ion_data::{IonDataHash, IonDataOrd, IonEq};
use crate::result::{IonFailure, IonResult};
use crate::types::Decimal;
use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::marker::PhantomData;

/// Indicates the most precise time unit that has been specified in the accompanying [Timestamp].
// IMPL NOTE: Discriminant values are cast to u64 and stored in the packed bit layout, so they must
// remain stable. The discriminants are left implicit (rather than written as `= 0`, `= 1`, ...) so
// they do not appear in the public API; the `const _` block below asserts the expected values, so
// reordering the variants fails the build instead of silently changing the packed encoding.
#[derive(Debug, Clone, Copy, Eq, PartialEq, PartialOrd, Ord, Default, Hash)]
pub enum TimestampPrecision {
    /// Year-level precision (e.g. `2020T`)
    #[default]
    Year,
    /// Month-level precision (e.g. `2020-08T`)
    Month,
    /// Day-level precision (e.g. `2020-08-01T`)
    Day,
    /// Minute-level precision (e.g. `2020-08-01T12:34Z`)
    HourAndMinute,
    /// Second-level precision or greater. (e.g. `2020-08-01T12:34:56Z` or `2020-08-01T12:34:56.123456789Z`)
    Second,
}

// The packed layout depends on these exact discriminant values; guard them at compile time.
const _: () = {
    assert!(TimestampPrecision::Year as u64 == 0);
    assert!(TimestampPrecision::Month as u64 == 1);
    assert!(TimestampPrecision::Day as u64 == 2);
    assert!(TimestampPrecision::HourAndMinute as u64 == 3);
    assert!(TimestampPrecision::Second as u64 == 4);
};

const YEAR_BITS: u64 = 14;
const MONTH_BITS: u64 = 4;
const DAY_BITS: u64 = 5;
const HOUR_BITS: u64 = 5;
const MINUTE_BITS: u64 = 6;
const SECOND_BITS: u64 = 6;
const OFFSET_BITS: u64 = 12;
const PRECISION_BITS: u64 = 3;
const SUBSECOND_PRECISION_BITS: u64 = 5;
const RESERVED_BITS: u64 = 4;

// Shifts: metadata at bottom, date-time at top.
// Within metadata: precision > subsecond_digits > offset (tiebreak order for IonDataOrd).
const RESERVED_SHIFT: u64 = 0;
const OFFSET_SHIFT: u64 = RESERVED_SHIFT + RESERVED_BITS; // 4
const SUBSECOND_PRECISION_SHIFT: u64 = OFFSET_SHIFT + OFFSET_BITS; // 16
const PRECISION_SHIFT: u64 = SUBSECOND_PRECISION_SHIFT + SUBSECOND_PRECISION_BITS; // 21
const SECOND_SHIFT: u64 = PRECISION_SHIFT + PRECISION_BITS; // 24
const MINUTE_SHIFT: u64 = SECOND_SHIFT + SECOND_BITS; // 30
const HOUR_SHIFT: u64 = MINUTE_SHIFT + MINUTE_BITS; // 36
const DAY_SHIFT: u64 = HOUR_SHIFT + HOUR_BITS; // 41
const MONTH_SHIFT: u64 = DAY_SHIFT + DAY_BITS; // 46
const YEAR_SHIFT: u64 = MONTH_SHIFT + MONTH_BITS; // 50

const YEAR_MASK: u64 = (1 << YEAR_BITS) - 1;
const MONTH_MASK: u64 = (1 << MONTH_BITS) - 1;
const DAY_MASK: u64 = (1 << DAY_BITS) - 1;
const HOUR_MASK: u64 = (1 << HOUR_BITS) - 1;
const MINUTE_MASK: u64 = (1 << MINUTE_BITS) - 1;
const SECOND_MASK: u64 = (1 << SECOND_BITS) - 1;
const OFFSET_MASK: u64 = (1 << OFFSET_BITS) - 1;
const PRECISION_MASK: u64 = (1 << PRECISION_BITS) - 1;
const SUBSECOND_PRECISION_MASK: u64 = (1 << SUBSECOND_PRECISION_BITS) - 1;

/// Mask covering only the date-time fields (year through second).
/// Comparing `packed & DATETIME_MASK` gives chronological order.
const DATETIME_MASK: u64 = (YEAR_MASK << YEAR_SHIFT)
    | (MONTH_MASK << MONTH_SHIFT)
    | (DAY_MASK << DAY_SHIFT)
    | (HOUR_MASK << HOUR_SHIFT)
    | (MINUTE_MASK << MINUTE_SHIFT)
    | (SECOND_MASK << SECOND_SHIFT);

// Compile-time guards on the bit layout. These enforce the invariants the
// packing (and the `Ord`/`PartialEq`/`ion_cmp` integer comparisons) rely on, so
// a future edit to the shifts, widths, or field order fails the build rather
// than silently corrupting comparisons.
const _: () = assert!(YEAR_SHIFT + YEAR_BITS == 64, "fields must fill the word");
// The date-time region must be contiguous and top-aligned; `Ord` compares it as an integer.
const _: () = assert!(DATETIME_MASK.leading_zeros() == 0);
const _: () = assert!(DATETIME_MASK.trailing_zeros() == SECOND_SHIFT as u32);
const _: () = assert!(DATETIME_MASK.count_ones() == 64 - SECOND_SHIFT as u32);

/// Offset-in-minutes is stored biased so the field's zero value can serve as the
/// "unknown offset" sentinel:
///
/// ```text
/// stored  = minutes + OFFSET_BIAS   // -1439..=1439  ->  1..=2879
/// minutes = stored  - OFFSET_BIAS
/// ```
///
/// Note that `+00:00` stores as 1440, distinct from _unknown_.
const OFFSET_BIAS: i16 = 1440;

/// Stored `offset` value meaning "no offset specified" (Ion's `-00:00`).
const OFFSET_UNKNOWN_SENTINEL: u16 = 0;

// 18 digits = attosecond precision. Exceeds any system clock or commercial
// atomic clock. Chosen over 19 to align with SI prefixes (multiples of 3)
// and to leave one bit free in the u64 coefficient for future niche use.
const MAX_FRAC_DIGITS: u8 = 18;
const _: () = assert!(
    10u128.pow(MAX_FRAC_DIGITS as u32) <= u64::MAX as u128,
    "attoseconds scale must fit in the u64 payload"
);

/// Powers of ten `10^0..=10^18`, indexed by exponent. Used to scale between a coefficient at a
/// declared number of fractional digits and the `attoseconds` (`10^-18`) payload. A lookup table
/// avoids the square-and-multiply loop (and its associated divide-by-zero panic edge) that
/// `u64::pow` with a runtime exponent compiles to on the timestamp read/write hot paths.
const POW10: [u64; MAX_FRAC_DIGITS as usize + 1] = {
    let mut table = [1u64; MAX_FRAC_DIGITS as usize + 1];
    let mut i = 1;
    while i < table.len() {
        table[i] = table[i - 1] * 10;
        i += 1;
    }
    table
};

/// One full second in attoseconds; `attoseconds` must always be strictly less than this.
const MAX_ATTOSECONDS: u64 = POW10[MAX_FRAC_DIGITS as usize];

/// The largest year the packed `year` field can represent.
const MAX_YEAR: u16 = 9999;

/// The smallest and largest offsets (in minutes) that Ion allows.
const MIN_OFFSET_MINUTES: i16 = -1439;
const MAX_OFFSET_MINUTES: i16 = 1439;

fn days_in_month(year: u16, month: u8) -> u8 {
    const DAYS_IN_MONTH: [u8; 12] = [31, 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
    let is_leap_year = |year| (year % 4 == 0 && year % 100 != 0) || (year % 400 == 0);

    if month == 2 && is_leap_year(year) {
        29
    } else {
        DAYS_IN_MONTH[(month - 1) as usize]
    }
}

fn validate_fields(y: u16, m: u8, d: u8, h: u8, min: u8, s: u8) -> bool {
    if y > MAX_YEAR {
        return false;
    }
    if !(1..=12).contains(&m) {
        return false;
    }
    let max_day = days_in_month(y, m);
    d >= 1 && d <= max_day && h <= 23 && min <= 59 && s <= 59
}

/// Returns an error if `offset_minutes` is outside Ion's valid UTC offset range. Takes an `i32`
/// so callers can validate before narrowing to the stored `i16`.
fn validate_offset_minutes(offset_minutes: i32) -> IonResult<()> {
    if !(MIN_OFFSET_MINUTES as i32..=MAX_OFFSET_MINUTES as i32).contains(&offset_minutes) {
        return IonResult::illegal_operation(format!(
            "offset ({} minutes) exceeds valid range ({}..={})",
            offset_minutes, MIN_OFFSET_MINUTES, MAX_OFFSET_MINUTES
        ));
    }
    Ok(())
}

/// Adds `offset_minutes` to a local time represented by the given fields,
/// returning the adjusted (year, month, day, hour, minute).
fn add_offset_to_utc(
    year: u16,
    month: u8,
    day: u8,
    hour: u8,
    minute: u8,
    offset_minutes: i16,
) -> (u16, u8, u8, u8, u8) {
    let total_minutes = hour as i32 * 60 + minute as i32 + offset_minutes as i32;
    let (mut d, h, m) = if (0..24 * 60).contains(&total_minutes) {
        // Common fast path: no day rollover
        (
            day as i32,
            (total_minutes / 60) as u8,
            (total_minutes % 60) as u8,
        )
    } else {
        let day_offset = total_minutes.div_euclid(24 * 60);
        let time_of_day = total_minutes.rem_euclid(24 * 60);
        (
            day as i32 + day_offset,
            (time_of_day / 60) as u8,
            (time_of_day % 60) as u8,
        )
    };

    let mut mo = month as i32;
    let mut y = year as i32;

    // Offset is at most ±1439 minutes (< 24h), so day shifts by at most ±1.
    if d > days_in_month(y as u16, mo as u8) as i32 {
        d -= days_in_month(y as u16, mo as u8) as i32;
        mo += 1;
        if mo > 12 {
            mo = 1;
            y += 1;
        }
    } else if d < 1 {
        mo -= 1;
        if mo < 1 {
            mo = 12;
            y -= 1;
        }
        d += days_in_month(y as u16, mo as u8) as i32;
    }

    (y as u16, mo as u8, d as u8, h, m)
}

/// Represents a point in time to a specified degree of precision. Unlike `chrono`'s `NaiveDateTime`
/// and `DateTime`, a `Timestamp` has variable precision ranging from a year to attoseconds.
///
/// NOTE: In an intentional divergence from the Ion Specification (which allows unlimited precision),
/// this implementation is limited to attoseconds precision and will produce an error when
/// attempting to read any value with more than attosecond precision.
//
// `Timestamp` is two 64-bit words. The time *value* needs 100 bits: 40 for the
// date-time fields (year..second) and 60 for the fraction (10^18 - 1 < 2^60),
// which is more than one word holds. It is intentional that the date-time
// component and the fraction each get their own word: the date-time occupies the
// top of `packed_fields`, and the fraction gets `attoseconds` to itself.
//
// The 24 bits left over in `packed_fields` hold the metadata, which is why
// precision, subsecond_precision, and offset sit *between* `second` and the
// fraction in significance order. Two consequences for future changes:
//
// - year..second must stay in the top bits, in descending significance, with no
//   metadata interleaved: `Ord` and `PartialEq` compare `packed & DATETIME_MASK`
//   as a single integer.
// - `ion_cmp` compares `packed_fields` and then `attoseconds` as raw integers, so
//   this layout *is* the `IonDataOrd` total order — date-time, precision,
//   subsecond_precision, offset, fraction. Permuting the metadata fields changes
//   how `IonData`-wrapped timestamps sort. (`IonDataOrd` makes no promise that
//   this ordering stays consistent between releases, so the layout is free to
//   change.)
//
// ─── Packed bit layout ────────────────────────────────────────────────
//
// All date-time fields are stored as LOCAL time in a single u64.
// A second u64 holds the attoseconds payload.
//
// Date-time fields are in the HIGH bits (most-significant first) so that
// a numeric comparison of the packed value yields chronological order.
// Metadata (offset, precision, subsecond_digits) is in the LOW bits.
//
// Bit layout of `packed` (MSB = bit 63):
//
//   [63:50] year                (14 bits, 0-9999)
//   [49:46] month               (4 bits, 1-12)
//   [45:41] day                 (5 bits, 1-31)
//   [40:36] hour                (5 bits, 0-23)
//   [35:30] minute              (6 bits, 0-59)
//   [29:24] second              (6 bits, 0-59)
//   [23:21] precision           (3 bits, 0-4 maps to TimestampPrecision)
//   [20:16] subsecond_precision (5 bits, 0 = none, 1-18 = digit count)
//   [15:4]  offset              (12 bits, biased unsigned: stored = minutes + 1440;
//                                valid range 1..=2879; 0 = unknown)
//   [3:0]   reserved            (4 bits)
//
// `attoseconds`: fractional seconds normalized to 10^-18 scale.
// `subsecond_precision` records display precision (how many digits to render).
//
// Invariants:
//
// 1. Fields below the declared precision hold their default values:
//    - Year:          month=1, day=1, hour=0, minute=0, second=0
//    - Month:         day=1, hour=0, minute=0, second=0
//    - Day:           hour=0, minute=0, second=0
//    - HourAndMinute: second=0
//    - Second:        (no fields required to be zero)
//
// 2. When precision < Second: attoseconds == 0 and subsecond_precision == 0.
//
// 3. When precision == Second and subsecond_precision == 0: attoseconds == 0.
//    (No fractional part means the attoseconds payload is unused.)
//
// 4. attoseconds < 10^18 (strictly less than one full second).
//
// 5. attoseconds is consistent with subsecond_precision: the value must be
//    representable in `subsecond_precision` decimal digits. Formally,
//    attoseconds % 10^(18 - subsecond_precision) == 0.
//    Example: subsecond_precision=3 (millis) → attoseconds is a multiple
//    of 10^15.
//
// 6. offset == 0 (unknown) is valid at any precision. When precision <
//    HourAndMinute, the offset field MUST be 0 (unknown) because sub-day
//    precision timestamps cannot meaningfully carry a UTC offset.
//
// 7. year is in 1..=9999 for user-constructed timestamps. Internally,
//    `to_utc` can produce year 0 (e.g., 0001-01-01T00:30+01:00 → year 0 UTC)
//    and `from_fixed_offset_datetime` can produce year 10000 (e.g., UTC
//    9999-12-31T23:30Z with offset -01:00 → local 10000-01-01). These values
//    fit in the 14-bit field but must not escape through public constructors.
//
// 8. reserved bits [3:0] are always 0.
#[derive(Clone)]
pub struct Timestamp {
    packed_fields: u64,
    attoseconds: u64,
}

impl Timestamp {
    /// Packs fields into the u64 bit-field.
    ///
    /// Callers typically validate their inputs before calling this helper. Each field is still
    /// masked to its bit width so exceptional paths that intentionally pack out-of-range values
    /// can only truncate within their own field rather than corrupt a neighboring one.
    #[allow(clippy::too_many_arguments)]
    fn pack_masked(
        precision: TimestampPrecision,
        year: u16,
        month: u8,
        day: u8,
        hour: u8,
        minute: u8,
        second: u8,
        offset_raw: u16,
        subsecond_digits: u8,
    ) -> u64 {
        (year as u64 & YEAR_MASK) << YEAR_SHIFT
            | (month as u64 & MONTH_MASK) << MONTH_SHIFT
            | (day as u64 & DAY_MASK) << DAY_SHIFT
            | (hour as u64 & HOUR_MASK) << HOUR_SHIFT
            | (minute as u64 & MINUTE_MASK) << MINUTE_SHIFT
            | (offset_raw as u64 & OFFSET_MASK) << OFFSET_SHIFT
            | (second as u64 & SECOND_MASK) << SECOND_SHIFT
            | (precision as u64 & PRECISION_MASK) << PRECISION_SHIFT
            | (subsecond_digits as u64 & SUBSECOND_PRECISION_MASK) << SUBSECOND_PRECISION_SHIFT
    }

    /// Direct construction from LOCAL time fields.
    /// `frac_digits`: number of fractional digits to display (0 = no fractional seconds).
    /// `attoseconds`: the fractional seconds value normalized to 10^-18 scale.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_fields(
        precision: TimestampPrecision,
        offset: Option<i16>,
        year: u16,
        month: u8,
        day: u8,
        hour: u8,
        minute: u8,
        second: u8,
        frac_digits: u8,
        attoseconds: u64,
    ) -> IonResult<Self> {
        if year == 0 || year > MAX_YEAR {
            return IonResult::illegal_operation(format!(
                "Timestamp year '{}' out of range (1-{})",
                year, MAX_YEAR
            ));
        }
        if precision >= TimestampPrecision::Month
            && !validate_fields(year, month, day, hour, minute, second)
        {
            return IonResult::illegal_operation("one or more timestamp fields are out of range");
        }
        if frac_digits > MAX_FRAC_DIGITS {
            return IonResult::illegal_operation(format!(
                "fractional seconds precision ({} digits) exceeds maximum ({})",
                frac_digits, MAX_FRAC_DIGITS
            ));
        }

        let offset_raw = match offset {
            None => OFFSET_UNKNOWN_SENTINEL,
            Some(m) => {
                validate_offset_minutes(m as i32)?;
                (m + OFFSET_BIAS) as u16
            }
        };

        let subsecond_digits = frac_digits;
        let packed = Self::pack_masked(
            precision,
            year,
            month,
            day,
            hour,
            minute,
            second,
            offset_raw,
            subsecond_digits,
        );

        Ok(Timestamp {
            packed_fields: packed,
            attoseconds,
        })
    }

    /// Construction from UTC fields + offset. Adds offset to convert to local time.
    /// `attoseconds`: fractional seconds normalized to 10^-18 scale.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn from_utc_fields(
        precision: TimestampPrecision,
        offset_minutes: i16,
        year: u16,
        month: u8,
        day: u8,
        hour: u8,
        minute: u8,
        second: u8,
        frac_digits: u8,
        attoseconds: u64,
    ) -> IonResult<Self> {
        // Validate the raw UTC fields before offset conversion
        if precision >= TimestampPrecision::Month
            && !validate_fields(year, month, day, hour, minute, second)
        {
            return IonResult::illegal_operation(
                "one or more timestamp UTC fields are out of range",
            );
        }
        let (ly, lmo, ld, lh, lmi) =
            add_offset_to_utc(year, month, day, hour, minute, offset_minutes);
        Self::from_fields(
            precision,
            Some(offset_minutes),
            ly,
            lmo,
            ld,
            lh,
            lmi,
            second,
            frac_digits,
            attoseconds,
        )
    }

    /// If the precision is [TimestampPrecision::Second], returns the Decimal scale of this Timestamp's
    /// fractional seconds; otherwise, returns None. If the Decimal scale is 0, it also returns None.
    ///
    /// For example, a Timestamp with 553 milliseconds would return a Decimal scale of 3.
    pub fn fractional_seconds_scale(&self) -> Option<i64> {
        let scale = self.subsecond_digit_count();
        if scale == 0 {
            None
        } else {
            Some(scale as i64)
        }
    }

    /// If the precision is [TimestampPrecision::Second], returns a Decimal representation of this Timestamp's
    /// fractional seconds; otherwise, returns None.
    ///
    /// For example, a Timestamp with 553 milliseconds would return a Decimal with
    /// coefficient 553, exponent -3.
    pub(crate) fn fractional_seconds_as_decimal(&self) -> Option<Decimal> {
        let digits = self.subsecond_digit_count() as u32;
        if digits == 0 {
            return None;
        }
        // Convert attoseconds to coefficient at the declared precision.
        let divisor = POW10[(MAX_FRAC_DIGITS as u32 - digits) as usize];
        let coefficient = self.attoseconds / divisor;
        Some(Decimal::new(coefficient, -(digits as i64)))
    }

    /// Number of subsecond digits of precision. Returns 0 when precision includes no subsecond
    /// digits, regardless of the reason.
    pub(crate) fn subsecond_digit_count(&self) -> u8 {
        ((self.packed_fields >> SUBSECOND_PRECISION_SHIFT) & SUBSECOND_PRECISION_MASK) as u8
    }

    /// Writes the fractional seconds portion of a text timestamp, including a leading `.`.
    fn format_fractional_seconds<W: std::fmt::Write>(&self, output: &mut W) -> IonResult<()> {
        let digits = self.subsecond_digit_count() as u32;
        if digits == 0 {
            return Ok(());
        }

        let divisor = POW10[(MAX_FRAC_DIGITS as u32 - digits) as usize];
        let coefficient = self.attoseconds / divisor;
        write!(output, ".{coefficient:0>width$}", width = digits as usize)?;
        Ok(())
    }

    pub(crate) fn format<W: std::fmt::Write>(&self, output: &mut W) -> IonResult<()> {
        match self.precision() {
            TimestampPrecision::Year => write!(output, "{:0>4}T", self.year())?,
            TimestampPrecision::Month => {
                write!(output, "{:0>4}-{:0>2}T", self.year(), self.month())?
            }
            TimestampPrecision::Day => write!(
                output,
                "{:0>4}-{:0>2}-{:0>2}T",
                self.year(),
                self.month(),
                self.day()
            )?,
            TimestampPrecision::HourAndMinute => {
                write!(
                    output,
                    "{:0>4}-{:0>2}-{:0>2}T{:0>2}:{:0>2}",
                    self.year(),
                    self.month(),
                    self.day(),
                    self.hour(),
                    self.minute()
                )?;
                self.format_offset(output)?;
            }
            TimestampPrecision::Second => {
                write!(
                    output,
                    "{:0>4}-{:0>2}-{:0>2}T{:0>2}:{:0>2}:{:0>2}",
                    self.year(),
                    self.month(),
                    self.day(),
                    self.hour(),
                    self.minute(),
                    self.second()
                )?;
                self.format_fractional_seconds(output)?;
                self.format_offset(output)?;
            }
        }
        Ok(())
    }

    fn format_offset<W: std::fmt::Write>(&self, output: &mut W) -> IonResult<()> {
        let offset_minutes = self.offset();
        let (sign, hours, minutes) = match offset_minutes {
            None => ("-", 0, 0),
            Some(offset_minutes) => {
                // Split the offset into a sign and magnitude for formatting
                const MINUTES_PER_HOUR: i32 = 60;
                let sign = if offset_minutes >= 0 { "+" } else { "-" };
                let offset_minutes = offset_minutes.abs();
                let hours = offset_minutes / MINUTES_PER_HOUR;
                let minutes = offset_minutes % MINUTES_PER_HOUR;

                (sign, hours, minutes)
            }
        };
        write!(output, "{sign}{hours:0>2}:{minutes:0>2}")?;
        Ok(())
    }

    /// Creates a TimestampBuilder with the specified year and [TimestampPrecision::Year].
    pub fn with_year(year: u32) -> TimestampBuilder<HasYear> {
        TimestampBuilder::with_year(year)
    }

    /// Creates a TimestampBuilder with the specified year, month, and day. Its precision is
    /// set to [TimestampPrecision::Day].
    pub fn with_ymd(year: u32, month: u32, day: u32) -> TimestampBuilder<HasDay> {
        TimestampBuilder::with_year(year)
            .with_month(month)
            .with_day(day)
    }

    /// Returns the offset in minutes that has been specified in the [Timestamp].
    /// A positive value indicates Eastern Hemisphere, while a negative value indicates Western Hemisphere.
    pub fn offset(&self) -> Option<i32> {
        let raw = ((self.packed_fields >> OFFSET_SHIFT) & OFFSET_MASK) as u16;
        if raw == OFFSET_UNKNOWN_SENTINEL {
            return None;
        }
        Some(raw as i32 - OFFSET_BIAS as i32)
    }

    /// Returns the precision that has been specified in the [Timestamp].
    pub fn precision(&self) -> TimestampPrecision {
        match (self.packed_fields >> PRECISION_SHIFT) & PRECISION_MASK {
            0 => TimestampPrecision::Year,
            1 => TimestampPrecision::Month,
            2 => TimestampPrecision::Day,
            3 => TimestampPrecision::HourAndMinute,
            _ => TimestampPrecision::Second,
        }
    }

    /// Returns the year that has been specified in the [Timestamp].
    pub fn year(&self) -> u32 {
        ((self.packed_fields >> YEAR_SHIFT) & YEAR_MASK) as u32
    }

    /// Returns the month that has been specified in the [Timestamp].
    /// Returns the month number starting from 1.
    /// The return value ranges from 1 to 12.
    pub fn month(&self) -> u32 {
        ((self.packed_fields >> MONTH_SHIFT) & MONTH_MASK) as u32
    }

    /// Returns the day that has been specified in the [Timestamp].
    /// Returns the day of month starting from 1.
    pub fn day(&self) -> u32 {
        ((self.packed_fields >> DAY_SHIFT) & DAY_MASK) as u32
    }

    /// Returns the hour(s) that has been specified in the [Timestamp].
    /// Returns the hour number from 0 to 23.
    pub fn hour(&self) -> u32 {
        ((self.packed_fields >> HOUR_SHIFT) & HOUR_MASK) as u32
    }

    /// Returns the minute(s) that has been specified in the [Timestamp].
    /// Returns the minute number from 0 to 59.
    pub fn minute(&self) -> u32 {
        ((self.packed_fields >> MINUTE_SHIFT) & MINUTE_MASK) as u32
    }

    /// Returns the second(s) that has been specified in the [Timestamp].
    /// Returns the second number from 0 to 59.
    pub fn second(&self) -> u32 {
        ((self.packed_fields >> SECOND_SHIFT) & SECOND_MASK) as u32
    }

    /// Return a UTC timestamp for this [Timestamp]
    pub fn to_utc(&self) -> Timestamp {
        let offset_minutes = match self.offset() {
            None => return self.clone(),
            Some(m) => m as i16,
        };
        let (uy, umo, ud, uh, umi) = add_offset_to_utc(
            self.year() as u16,
            self.month() as u8,
            self.day() as u8,
            self.hour() as u8,
            self.minute() as u8,
            -offset_minutes,
        );
        // Pack directly without validation — the source timestamp was already
        // valid, and UTC conversion can produce year 0 (e.g., 0001-01-01T00:30+01:00
        // → 0000-12-31T23:30 UTC). This is fine for comparison purposes.
        // TODO(#1033, #1034): to_utc should set offset to 0 (+00:00), not unknown.
        // Keeping unknown offset to match prior behavior for now.
        let packed = Self::pack_masked(
            self.precision(),
            uy,
            umo,
            ud,
            uh,
            umi,
            self.second() as u8,
            OFFSET_UNKNOWN_SENTINEL,
            self.subsecond_digit_count(),
        );
        Timestamp {
            packed_fields: packed,
            attoseconds: self.attoseconds,
        }
    }

    /// Returns this Timestamp's fractional seconds in nanoseconds
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would return a
    /// number of nanoseconds, losing precision. If it loses precision then truncation is performed.
    /// (e.g. a timestamp with fractional seconds of `0.000000000999` would return `0`)
    pub fn nanoseconds(&self) -> u32 {
        (self.attoseconds / 1_000_000_000) as u32
    }

    /// Returns this Timestamp's fractional seconds in microseconds
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would return a
    /// number of microseconds, losing precision. If it loses precision then truncation is performed.
    /// (e.g. a timestamp with fractional seconds of `0.000000999` would return `0`)
    pub fn microseconds(&self) -> u32 {
        (self.attoseconds / 1_000_000_000_000) as u32
    }

    /// Returns this Timestamp's fractional seconds in milliseconds
    ///
    /// NOTE: This is a potentially lossy operation. A Timestamp with picoseconds would return a
    /// number of milliseconds, losing precision. If it loses precision then truncation is performed.
    /// (e.g. a timestamp with fractional seconds of `0.000999` would return `0`)
    pub fn milliseconds(&self) -> u32 {
        (self.attoseconds / 1_000_000_000_000_000) as u32
    }
}

/// Formats an ISO-8601 timestamp of appropriate precision and offset.
impl Display for Timestamp {
    fn fmt(&self, output: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        self.format(output).map_err(|_| std::fmt::Error)?;
        Ok(())
    }
}

impl Debug for Timestamp {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "Timestamp({})", self)
    }
}

impl PartialOrd for Timestamp {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Timestamp {
    fn cmp(&self, other: &Self) -> Ordering {
        // Fast path: identical packed + attoseconds means same instant.
        if self.packed_fields == other.packed_fields && self.attoseconds == other.attoseconds {
            return Ordering::Equal;
        }

        let self_offset_raw = (self.packed_fields >> OFFSET_SHIFT) & OFFSET_MASK;
        let other_offset_raw = (other.packed_fields >> OFFSET_SHIFT) & OFFSET_MASK;

        if self_offset_raw == other_offset_raw {
            // Same offset (or both unknown) — compare date-time fields directly.
            return (self.packed_fields & DATETIME_MASK)
                .cmp(&(other.packed_fields & DATETIME_MASK))
                .then_with(|| self.attoseconds.cmp(&other.attoseconds));
        }

        // Different offsets: normalize other's local time to self's offset.
        let delta_minutes =
            offset_raw_to_minutes(self_offset_raw) - offset_raw_to_minutes(other_offset_raw);

        if delta_minutes == 0 {
            return (self.packed_fields & DATETIME_MASK)
                .cmp(&(other.packed_fields & DATETIME_MASK))
                .then_with(|| self.attoseconds.cmp(&other.attoseconds));
        }

        // Adjust other's time by delta and compare as linear minutes.
        // No division or repacking needed for the common no-rollover case.
        let other_hour = other.hour() as i32;
        let other_minute = other.minute() as i32;
        let other_total = other_hour * 60 + other_minute + delta_minutes as i32;

        if (0..24 * 60).contains(&other_total) {
            // No day rollover: date bits (year/month/day) unchanged.
            // Compare date portion first.
            const DATE_MASK: u64 =
                (YEAR_MASK << YEAR_SHIFT) | (MONTH_MASK << MONTH_SHIFT) | (DAY_MASK << DAY_SHIFT);
            let date_cmp = (self.packed_fields & DATE_MASK).cmp(&(other.packed_fields & DATE_MASK));
            if date_cmp != Ordering::Equal {
                return date_cmp;
            }
            // Compare time-of-day as linear minutes.
            let self_total = self.hour() as i32 * 60 + self.minute() as i32;
            let time_cmp = self_total.cmp(&other_total);
            if time_cmp != Ordering::Equal {
                return time_cmp;
            }
            return self
                .second()
                .cmp(&other.second())
                .then_with(|| self.attoseconds.cmp(&other.attoseconds));
        }

        // Day rollover: full conversion needed.
        let (ny, nmo, nd, nh, nmi) = add_offset_to_utc(
            other.year() as u16,
            other.month() as u8,
            other.day() as u8,
            other_hour as u8,
            other_minute as u8,
            delta_minutes,
        );
        let other_datetime = (ny as u64) << YEAR_SHIFT
            | (nmo as u64) << MONTH_SHIFT
            | (nd as u64) << DAY_SHIFT
            | (nh as u64) << HOUR_SHIFT
            | (nmi as u64) << MINUTE_SHIFT
            | (other.packed_fields & (SECOND_MASK << SECOND_SHIFT));

        (self.packed_fields & DATETIME_MASK)
            .cmp(&other_datetime)
            .then_with(|| self.attoseconds.cmp(&other.attoseconds))
    }
}

/// Convert biased raw offset to signed minutes.
/// Sentinel 0 (unknown) maps to 0 minutes — no branch needed since 0 - BIAS = -BIAS,
/// but we want unknown to be treated as +00:00 (= 0 minutes). Since sentinel is 0
/// and bias is 1440, we get -1440 if we just subtract. Instead: sentinel means the
/// offset field is 0, and we want the effective offset to be 0 (UTC). So we use
/// the fact that (raw == 0) means unknown and skip the subtraction via branchless mask.
#[inline(always)]
fn offset_raw_to_minutes(raw: u64) -> i16 {
    // When raw == 0 (unknown): result is 0.
    // When raw != 0 (known):   result is raw - BIAS.
    // Branchless: the mask is 0 when raw==0, all-ones otherwise.
    let mask = ((raw | raw.wrapping_neg()) >> 63) as u16; // 0 if raw==0, 1 otherwise
    let mask = mask.wrapping_neg(); // 0x0000 if raw==0, 0xFFFF otherwise
    (raw as i16).wrapping_sub(OFFSET_BIAS) & (mask as i16)
}

/// Two Timestamps are considered equal (though not necessarily IonEq) if they represent the same
/// instant in time. TimestampPrecision is ignored. Offsets do not have to match as long as the instants
/// being represented match. Examples:
/// * `2022T` == `2022T-01`
/// * `2022T` == `2022T-01-01T00:00:00.000+00:00`
/// * `2022T-05-11T12:00:00.000Z` == `2022T-05-11T07:00:00.000-05:00`
impl PartialEq for Timestamp {
    fn eq(&self, other: &Self) -> bool {
        // Offset normalization never changes seconds or attoseconds,
        // so if either differs the timestamps can't represent the same instant.
        if self.attoseconds != other.attoseconds {
            return false;
        }
        if self.second() != other.second() {
            return false;
        }
        // Mask out precision and subsecond_digits — they don't affect instant equality.
        const INSTANT_MASK: u64 = DATETIME_MASK | (OFFSET_MASK << OFFSET_SHIFT);
        if (self.packed_fields & INSTANT_MASK) == (other.packed_fields & INSTANT_MASK) {
            return true;
        }
        // Fallback to normalizing offsets.
        self.cmp(other) == Ordering::Equal
    }
}

impl Eq for Timestamp {}

impl IonEq for Timestamp {
    fn ion_eq(&self, other: &Self) -> bool {
        self.packed_fields.eq(&other.packed_fields) && self.attoseconds.eq(&other.attoseconds)
    }
}

impl IonDataOrd for Timestamp {
    fn ion_cmp(&self, other: &Self) -> Ordering {
        self.packed_fields
            .cmp(&other.packed_fields)
            .then(self.attoseconds.cmp(&other.attoseconds))
    }
}

impl IonDataHash for Timestamp {
    fn ion_data_hash<H: Hasher>(&self, state: &mut H) {
        self.packed_fields.hash(state);
        self.attoseconds.hash(state);
    }
}

/// A Builder object for incrementally configuring and finally instantiating a [Timestamp].
/// This builder uses the type-state pattern to expose only those methods which can result in a
/// valid Timestamp. For example, it is not possible to set the `day` field without first setting
/// the `year` and `month` fields.
// See the unit tests for usage examples.
#[derive(Debug, Clone)]
pub struct TimestampBuilder<T> {
    _state: PhantomData<T>,
    precision: TimestampPrecision,
    offset: Option<i32>,
    // year..second are always set. Default is the implied value for the field if precision is less than that field.
    year: u32,
    month: u32,
    day: u32,
    hour: u32,
    minute: u32,
    second: u32,
    attoseconds: u64,
    // Held as `u32` so a precision beyond `MAX_FRAC_DIGITS` is caught by `validate_field_ranges`
    // before it is narrowed to the `u8` that `Timestamp::from_fields` expects, rather than
    // silently wrapping into an in-range value. A setter whose input is wider than `u32` saturates
    // at `u32::MAX`, which validation still rejects.
    fractional_digits: u32,
}

impl<T> TimestampBuilder<T> {
    fn change_state<U>(self) -> TimestampBuilder<U> {
        // If we ever discover a performance difference, this entire function could be replaced with one line.
        // unsafe { std::mem::transmute(self) }
        TimestampBuilder {
            _state: PhantomData,
            precision: self.precision,
            offset: self.offset,
            year: self.year,
            month: self.month,
            day: self.day,
            hour: self.hour,
            minute: self.minute,
            second: self.second,
            attoseconds: self.attoseconds,
            fractional_digits: self.fractional_digits,
        }
    }

    /// Confirms that each configured field fits in the corresponding field of the packed
    /// [`Timestamp`] representation.
    ///
    /// [`Timestamp::from_fields`] performs the authoritative validation (including calendar
    /// rules like the number of days in the given month), but it receives fields that have
    /// already been narrowed from `u32`/`i32` to `u8`/`u16`/`i16`. This method runs first so
    /// that a value too large for the narrower type is reported as an error instead of
    /// silently wrapping into a different, possibly valid-looking value.
    fn validate_field_ranges(&self) -> IonResult<()> {
        if self.attoseconds >= MAX_ATTOSECONDS {
            // No value is reported: this also fires for the out-of-`[0, 1)` sentinel set by
            // `with_fractional_seconds`, where `attoseconds` is a placeholder rather than a value
            // the caller supplied.
            return IonResult::illegal_operation(
                "Timestamp fractional seconds are out of range (must be in [0, 1))",
            );
        }
        if self.year > MAX_YEAR as u32 {
            return IonResult::illegal_operation(format!(
                "Timestamp year '{}' out of range (1-{MAX_YEAR})",
                self.year,
            ));
        }
        if self.month > 12 {
            return IonResult::illegal_operation(format!(
                "Timestamp month '{}' out of range (1-12)",
                self.month
            ));
        }
        if self.day > 31 {
            return IonResult::illegal_operation(format!(
                "Timestamp day '{}' out of range (1-31)",
                self.day
            ));
        }
        if self.hour > 23 {
            return IonResult::illegal_operation(format!(
                "Timestamp hour '{}' out of range (0-23)",
                self.hour
            ));
        }
        if self.minute > 59 {
            return IonResult::illegal_operation(format!(
                "Timestamp minute '{}' out of range (0-59)",
                self.minute
            ));
        }
        if self.second > 59 {
            return IonResult::illegal_operation(format!(
                "Timestamp second '{}' out of range (0-59)",
                self.second
            ));
        }
        if self.fractional_digits > MAX_FRAC_DIGITS as u32 {
            return IonResult::illegal_operation(format!(
                "fractional seconds precision ({} digits) exceeds maximum ({})",
                self.fractional_digits, MAX_FRAC_DIGITS
            ));
        }
        if let Some(offset_minutes) = self.offset {
            validate_offset_minutes(offset_minutes)?;
        }
        Ok(())
    }

    /// Attempt to construct a [Timestamp] using the values configured on the [TimestampBuilder].
    pub fn build(self) -> IonResult<Timestamp> {
        // Each field is validated *before* it is narrowed; a `u32`-to-`u8`/`u16` cast of an
        // out-of-range value would silently wrap and could produce a field that
        // `Timestamp::from_fields` then accepts as valid (e.g. `month: 268` becomes `12`).
        self.validate_field_ranges()?;

        Timestamp::from_fields(
            self.precision,
            self.offset.map(|i| i as i16),
            self.year as u16,
            self.month as u8,
            self.day as u8,
            self.hour as u8,
            self.minute as u8,
            self.second as u8,
            self.fractional_digits as u8,
            self.attoseconds,
        )
    }

    /// Like [Self::build], but the fields provided for each time unit are understood
    /// to be in UTC rather than in the local time of the specified offset (if there is one).
    pub(crate) fn build_utc_fields_at_offset(self, offset_minutes: i32) -> IonResult<Timestamp> {
        // Validate the fields *before* they are narrowed, for the same reason `build` does: a
        // `u32`-to-`u8`/`u16` cast of an out-of-range value would silently wrap and could produce
        // a field that `Timestamp::from_utc_fields` then accepts as valid (e.g. `month: 268`
        // becomes `12`). `validate_field_ranges` covers the date-time fields and `self.offset`;
        // the UTC offset arrives as a parameter here, so validate it before its own narrowing to
        // `i16`.
        self.validate_field_ranges()?;
        validate_offset_minutes(offset_minutes)?;
        Timestamp::from_utc_fields(
            self.precision,
            offset_minutes as i16,
            self.year as u16,
            self.month as u8,
            self.day as u8,
            self.hour as u8,
            self.minute as u8,
            self.second as u8,
            self.fractional_digits as u8,
            self.attoseconds,
        )
    }
}

// The type states (HasYear, HasMonth, etc.) are pub in this module, but they do not appear as types
// in the documentation, they cannot be imported, and they are not nameable from outside this crate.
#[derive(Debug, Clone)]
pub struct HasYear;
impl TimestampBuilder<HasYear> {
    pub fn with_year(year: u32) -> Self {
        TimestampBuilder {
            _state: Default::default(),
            precision: TimestampPrecision::Year,
            offset: None,
            year,
            month: 1,
            day: 1,
            hour: 0,
            minute: 0,
            second: 0,
            attoseconds: 0,
            fractional_digits: 0,
        }
    }

    pub fn with_ymd(year: u32, month: u32, day: u32) -> TimestampBuilder<HasDay> {
        Self::with_year(year).with_month(month).with_day(day)
    }

    // Libraries have conflicting opinions about whether months should be
    // 0- or 1-indexed, so Timestamp follows chrono's lead and provides
    // convenient ways to do both. Internally, it uses a 1-based representation.

    // 0-indexed month
    pub fn with_month0(self, month: u32) -> TimestampBuilder<HasMonth> {
        self.with_month(month + 1)
    }

    // 1-indexed month
    pub fn with_month(mut self, month: u32) -> TimestampBuilder<HasMonth> {
        self.precision = TimestampPrecision::Month;
        self.month = month;
        self.change_state()
    }
}

#[derive(Debug, Clone)]
pub struct HasMonth;
impl TimestampBuilder<HasMonth> {
    // Libraries have conflicting opinions about whether days should be
    // 0- or 1-indexed, so Timestamp follows chrono's lead and provides
    // convenient ways to do both. Internally, it uses a 1-based representation.

    // 0-indexed day
    pub fn with_day0(self, day: u32) -> TimestampBuilder<HasDay> {
        self.with_day(day + 1)
    }

    // 1-indexed day
    pub fn with_day(mut self, day: u32) -> TimestampBuilder<HasDay> {
        self.precision = TimestampPrecision::Day;
        self.day = day;
        self.change_state()
    }
}

#[derive(Debug, Clone)]
pub struct HasDay;
impl TimestampBuilder<HasDay> {
    pub fn with_hms(self, hour: u32, minute: u32, second: u32) -> TimestampBuilder<HasSeconds> {
        self.with_hour(hour).with_minute(minute).with_second(second)
    }

    pub fn with_hour_and_minute(mut self, hour: u32, minute: u32) -> TimestampBuilder<HasMinute> {
        self.precision = TimestampPrecision::HourAndMinute;
        self.hour = hour;
        self.minute = minute;
        self.change_state()
    }

    pub fn with_hour(mut self, hour: u32) -> TimestampBuilder<HasHour> {
        self.precision = TimestampPrecision::HourAndMinute;
        self.hour = hour;
        self.change_state()
    }
}

macro_rules! with_offset {
    () => {
        /// Sets the difference, in minutes, from UTC. A positive value indicates
        /// Eastern Hemisphere, while a negative value indicates Western Hemisphere.
        // The unit (minutes) could be seconds (which is what the chrono crate uses
        // internally), but Ion uses minutes in its binary representation, so it
        // makes sense to be consistent.
        pub fn with_offset(mut self, offset_minutes: i32) -> TimestampBuilder<HasOffset> {
            self.offset = Some(offset_minutes);
            self.change_state()
        }
    };
}

#[derive(Debug, Clone)]
pub struct HasHour;
impl TimestampBuilder<HasHour> {
    pub fn with_minute(mut self, minute: u32) -> TimestampBuilder<HasMinute> {
        self.precision = TimestampPrecision::HourAndMinute;
        self.minute = minute;
        self.change_state()
    }

    with_offset!();
}

#[derive(Debug, Clone)]
pub struct HasMinute;
impl TimestampBuilder<HasMinute> {
    pub fn with_second(mut self, second: u32) -> TimestampBuilder<HasSeconds> {
        self.precision = TimestampPrecision::Second;
        self.second = second;
        self.change_state()
    }

    with_offset!();
}

#[derive(Debug, Clone)]
pub struct HasSeconds;
impl TimestampBuilder<HasSeconds> {
    // Note that in order to create a `FractionalSecondSetter`, the user will have had to first
    // create a `SecondSetter`. Because of this, the builder's precision is already set to
    // `TimestampPrecision::Second`.

    /// Sets the fractional seconds to `nanosecond`, which must be in the range `0..=999_999_999`.
    /// An out-of-range value causes [`Self::build`] to return an error.
    pub fn with_nanoseconds(mut self, nanosecond: u32) -> TimestampBuilder<HasFractionalSeconds> {
        self.attoseconds = (nanosecond as u64).saturating_mul(1_000_000_000);
        self.fractional_digits = 9;

        self.change_state()
    }

    /// Sets the fractional seconds to `microsecond`, which must be in the range `0..=999_999`.
    /// An out-of-range value causes [`Self::build`] to return an error.
    pub fn with_microseconds(mut self, microsecond: u32) -> TimestampBuilder<HasFractionalSeconds> {
        self.attoseconds = (microsecond as u64).saturating_mul(1_000_000_000_000);
        self.fractional_digits = 6;

        self.change_state()
    }

    /// Sets the fractional seconds to `millisecond`, which must be in the range `0..=999`.
    /// An out-of-range value causes [`Self::build`] to return an error.
    pub fn with_milliseconds(mut self, millisecond: u32) -> TimestampBuilder<HasFractionalSeconds> {
        self.attoseconds = (millisecond as u64).saturating_mul(1_000_000_000_000_000);
        self.fractional_digits = 3;

        self.change_state()
    }

    /// Sets the fractional seconds from a nanosecond-scale value with `precision_digits` of
    /// declared precision.
    ///
    /// `nanoseconds` is interpreted at `10^-9` scale (i.e. `0..=999_999_999`). When
    /// `precision_digits` is fewer than the digits present in `nanoseconds`, the extra
    /// (less-significant) digits are stripped so the stored value stays consistent with the
    /// declared precision. For example, `(123_456_789, 3)` stores `0.123`.
    ///
    /// A `precision_digits` greater than the supported maximum ([`MAX_FRAC_DIGITS`]) causes
    /// [`Self::build`] to return an error rather than wrapping.
    pub fn with_nanoseconds_and_precision(
        mut self,
        nanoseconds: u32,
        precision_digits: u32,
    ) -> TimestampBuilder<HasFractionalSeconds> {
        // Clamp only for the scale lookup; an out-of-range `precision_digits` is still surfaced as
        // an error below.
        let scale_digits = precision_digits.min(MAX_FRAC_DIGITS as u32);
        let attoseconds = (nanoseconds as u64).saturating_mul(1_000_000_000);
        let scale = POW10[(MAX_FRAC_DIGITS as u32 - scale_digits) as usize];
        // Drop any precision finer than `precision_digits` so `attoseconds` stays a multiple of
        // `10^(18 - precision)` (fractional-seconds invariant 5).
        self.attoseconds = attoseconds / scale * scale;
        // Stored verbatim; `build()` rejects a precision greater than the supported maximum.
        self.fractional_digits = precision_digits;

        self.change_state()
    }

    pub fn with_fractional_seconds(
        mut self,
        fractional_seconds: Decimal,
    ) -> TimestampBuilder<HasFractionalSeconds> {
        // The declared precision is the number of fractional digits, i.e. `-exponent` (0 when the
        // exponent is non-negative, e.g. a zero written as `0d2`). This also covers a zero value:
        // its coefficient is 0, so `attoseconds` works out to 0 below.
        //
        // `digits` is `u64` (`Decimal::exponent` is `i64`), so it saturates at `u32::MAX` when
        // narrowed to the field; an over-range precision is rejected by `build()` rather than
        // wrapping into a spuriously in-range value.
        let digits = fractional_seconds.exponent.min(0).unsigned_abs();
        self.fractional_digits = u32::try_from(digits).unwrap_or(u32::MAX);
        self.attoseconds = if digits > MAX_FRAC_DIGITS as u64 {
            // Precision exceeds the limit; `build()` rejects it via `fractional_digits`.
            0
        } else if fractional_seconds.is_less_than_zero() {
            // A negative fractional second cannot be represented in the unsigned `attoseconds`
            // field; saturate so the range check in `validate_field_ranges` rejects it.
            u64::MAX
        } else {
            // attoseconds = coefficient * 10^(18 - digits). A value `>= 1` produces `attoseconds
            // >= 10^18`, which `validate_field_ranges` rejects on its own; no separate check for
            // the upper bound is needed. Widen to `u128` first so the multiply cannot overflow,
            // then saturate any out-of-range result into the (rejected) range.
            let coefficient = fractional_seconds
                .coefficient()
                .magnitude()
                .as_u128()
                .unwrap_or(u128::MAX);
            let scale = POW10[MAX_FRAC_DIGITS as usize - digits as usize] as u128;
            u64::try_from(coefficient.saturating_mul(scale)).unwrap_or(u64::MAX)
        };
        self.change_state()
    }

    with_offset!();
}

#[derive(Debug, Clone)]
pub struct HasFractionalSeconds;
impl TimestampBuilder<HasFractionalSeconds> {
    with_offset!();
}

#[derive(Debug, Clone)]
pub struct HasOffset;
// No impl for TimestampBuilder<HasOffset> because `build()` is included in TimestampBuilder<T>

#[cfg(test)]
mod timestamp_tests {
    use super::*;
    use crate::ion_data::IonEq;
    use crate::result::IonResult;
    use crate::{Decimal, Element, Int, Timestamp, TimestampPrecision};
    use rstest::*;
    use std::cmp::Ordering;
    use std::io::Write;
    use std::ops::Mul;

    // `build` validates its `u32`/`i32` fields before narrowing them to `u8`/`u16`/`i16`.
    // `build_utc_fields_at_offset` must do the same: without pre-narrowing validation an
    // out-of-range field wraps into a plausible wrong value that `from_utc_fields` accepts. This
    // path is taken by binary 1.0 known-offset decoding and by binary 1.1 UTC-flag decoding (which
    // passes offset 0); binary 1.1 known-offset decoding uses `with_offset` + `build` instead.

    /// `build`'s own comment cites `month: 268` becoming `12` as the reason it validates before
    /// narrowing. Its sibling must not skip that guard. Each value wraps into an in-range value
    /// (e.g. `268 as u8 == 12`), so a rejection here can only come from pre-narrowing validation.
    #[rstest]
    #[case::year(67_557, 1, 1, 0, 0, 0)]
    #[case::month(2021, 268, 1, 0, 0, 0)]
    #[case::day(2021, 1, 261, 0, 0, 0)]
    #[case::hour(2021, 1, 1, 261, 0, 0)]
    #[case::minute(2021, 1, 1, 0, 286, 0)]
    #[case::second(2021, 1, 1, 0, 0, 315)]
    fn build_utc_fields_at_offset_rejects_out_of_range_fields(
        #[case] year: u32,
        #[case] month: u32,
        #[case] day: u32,
        #[case] hour: u32,
        #[case] minute: u32,
        #[case] second: u32,
    ) {
        let built = TimestampBuilder::with_ymd(year, month, day)
            .with_hms(hour, minute, second)
            .build_utc_fields_at_offset(0);
        assert!(
            built.is_err(),
            "expected {year}-{month}-{day}T{hour}:{minute}:{second} to be rejected, got `{}`",
            built.unwrap()
        );
    }

    /// The offset parameter is narrowed `i32 as i16`, so out-of-range values must be rejected
    /// before that cast. `MAX_OFFSET_MINUTES + 1` catches the ordinary out-of-range case; `65536`
    /// is the boundary that survives `as i16` (it wraps to `0`), the one value the downstream
    /// `from_fields` offset check cannot catch on its own.
    #[rstest]
    #[case(1440)]
    #[case(-1440)]
    #[case(65536)]
    fn build_utc_fields_at_offset_rejects_out_of_range_offset(#[case] offset_minutes: i32) {
        let built = TimestampBuilder::with_ymd(2021, 1, 1)
            .with_hour_and_minute(0, 0)
            .build_utc_fields_at_offset(offset_minutes);
        assert!(
            built.is_err(),
            "expected offset {offset_minutes} to be rejected, got `{}`",
            built.unwrap()
        );
    }

    /// `from_utc_fields`/`from_fields` never check `attoseconds`, so `validate_field_ranges` is the
    /// only guard against a subsecond value that outruns one full second (invariant 4). Reachable
    /// from binary 1.1 short-form subseconds (e.g. the 10-bit millisecond field admits 1000..=1023).
    #[test]
    fn build_utc_fields_at_offset_rejects_over_range_subseconds() {
        let built = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_milliseconds(1023)
            .build_utc_fields_at_offset(0);
        assert!(
            built.is_err(),
            "1023 milliseconds (>= 1 second) should be rejected, got `{}`",
            built.unwrap()
        );
    }

    /// Guards against over-rejection: in-range fields must still build. Includes the `..=` offset
    /// bounds (±1439) and the calendar extremes. The calendar max uses offset 0 because a positive
    /// offset would push local time into year 10000 (a legitimate rejection, not over-rejection).
    #[rstest]
    #[case(2021, 6, 15, 12, 30, 45, 1439)]
    #[case(2021, 6, 15, 12, 30, 45, -1439)]
    #[case(9999, 12, 31, 23, 59, 59, 0)]
    #[case(1, 1, 1, 0, 0, 0, 0)]
    fn build_utc_fields_at_offset_accepts_in_range_extremes(
        #[case] year: u32,
        #[case] month: u32,
        #[case] day: u32,
        #[case] hour: u32,
        #[case] minute: u32,
        #[case] second: u32,
        #[case] offset_minutes: i32,
    ) {
        let built = TimestampBuilder::with_ymd(year, month, day)
            .with_hms(hour, minute, second)
            .build_utc_fields_at_offset(offset_minutes);
        assert!(
            built.is_ok(),
            "expected {year}-{month}-{day}T{hour}:{minute}:{second} at offset {offset_minutes} \
             to build, got `{:?}`",
            built.unwrap_err()
        );
    }

    /// The same defect reached through the public API. A binary 1.0 timestamp with a known offset
    /// at HourAndMinute precision routes to `build_utc_fields_at_offset`, so an out-of-range
    /// VarUInt month must surface as an error rather than a plausible wrong month. The assertion
    /// checks the error names the offending field, so a structurally malformed buffer (which fails
    /// for an unrelated reason) can't pass this test by accident.
    #[test]
    fn binary_1_0_rejects_timestamp_with_out_of_range_month() {
        const IVM: [u8; 4] = [0xE0, 0x01, 0x00, 0xEA];

        // Control: month = 12 as a one-byte VarUInt reads as December.
        let mut control = IVM.to_vec();
        control.extend_from_slice(&[0x67, 0xBC, 0x0F, 0xE5, 0x8C, 0x81, 0x80, 0x80]);
        let control = Element::read_one(&control).expect("control timestamp must decode");
        assert_eq!(
            control
                .as_timestamp()
                .expect("control is a timestamp")
                .month(),
            12
        );

        // month = 268 as a two-byte VarUInt, and `268 as u8` is also 12. Only the month bytes
        // differ from the control (plus the length byte 0x67 -> 0x68 for the extra byte).
        let mut wrapped = IVM.to_vec();
        wrapped.extend_from_slice(&[0x68, 0xBC, 0x0F, 0xE5, 0x02, 0x8C, 0x81, 0x80, 0x80]);
        let error = Element::read_one(&wrapped)
            .expect_err("month 268 must not decode as a valid timestamp");
        let message = error.to_string();
        assert!(
            message.contains("month"),
            "expected an out-of-range month error, got: {message}"
        );
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_known_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(5 * 60).build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_known_offset_are_equal_ordering() -> IonResult<()>
    {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(5 * 60).build()?;
        assert_eq!(timestamp1, timestamp2);
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_millis_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_at_known_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(5 * 60).build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_from_utc_and_local_hm_fields_at_same_offset_are_equal() -> IonResult<()> {
        // Builder 1 specifies its time fields in the local time of the specified offset
        let builder1 = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(11, 43);
        let timestamp1 = builder1.with_offset(-5 * 60).build()?;
        // Builder 2 specifies its time fields in UTC and expects the offset to be applied afterwards
        let builder2 = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp2 = builder2.build_utc_fields_at_offset(-5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_from_utc_and_local_hms_fields_at_same_offset_are_equal() -> IonResult<()> {
        // Builder 1 specifies its time fields in the local time of the specified offset
        let builder1 = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(11, 43, 51);
        let timestamp1 = builder1.with_offset(-5 * 60).build()?;
        // Builder 2 specifies its time fields in UTC and expects the offset to be applied afterwards
        let builder2 = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp2 = builder2.build_utc_fields_at_offset(-5 * 60)?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hms_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hm_at_known_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(5 * 60).build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_hm_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ymd_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_ym_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_year(2021).with_month(2);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_same_year_at_unknown_offset_are_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_year(2021);
        let timestamp1 = builder.clone().build()?;
        let timestamp2 = builder.build()?;
        assert_eq!(timestamp1, timestamp2);
        assert!(timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_at_different_offsets_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_offset(4 * 60).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_known_and_unknown_offsets_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(16, 43, 51)
            .with_milliseconds(192);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_precisions_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder.clone().with_offset(5 * 60).build()?;
        let timestamp2 = builder.with_milliseconds(192).with_offset(5 * 60).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_second_precision_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder
            .clone()
            .with_milliseconds(192)
            .with_offset(5 * 60)
            .build()?;
        // The microseconds field has the same amount of time, but a different precision.
        let timestamp2 = builder
            .with_microseconds(193 * 1_000)
            .with_offset(5 * 60)
            .build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_fractional_seconds_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hms(16, 43, 51);
        let timestamp1 = builder
            .clone()
            .with_milliseconds(192)
            .with_offset(5 * 60)
            .build()?;
        let timestamp2 = builder.with_milliseconds(193).with_offset(5 * 60).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_seconds_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5).with_hour_and_minute(16, 43);
        let timestamp1 = builder
            .clone()
            .with_second(12)
            .with_offset(5 * 60)
            .build()?;
        let timestamp2 = builder.with_second(13).with_offset(5 * 60).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_minutes_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5);
        let timestamp1 = builder
            .clone()
            .with_hour_and_minute(16, 42)
            .with_offset(5 * 60)
            .build()?;
        let timestamp2 = builder
            .with_hour_and_minute(16, 43)
            .with_offset(5 * 60)
            .build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_hours_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_ymd(2021, 2, 5);
        let timestamp1 = builder
            .clone()
            .with_hour_and_minute(16, 42)
            .with_offset(5 * 60)
            .build()?;
        let timestamp2 = builder
            .with_hour_and_minute(17, 42)
            .with_offset(5 * 60)
            .build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_days_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_year(2021).with_month(2);
        let timestamp1 = builder.clone().with_day(5).build()?;
        let timestamp2 = builder.with_day(6).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_months_are_not_equal() -> IonResult<()> {
        let builder = TimestampBuilder::with_year(2021);
        let timestamp1 = builder.clone().with_month(2).build()?;
        let timestamp2 = builder.with_month(3).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamps_with_different_years_are_not_equal() -> IonResult<()> {
        let timestamp1 = TimestampBuilder::with_year(2021).build()?;
        let timestamp2 = TimestampBuilder::with_year(2022).build()?;
        assert_ne!(timestamp1, timestamp2);
        assert!(!timestamp1.ion_eq(&timestamp2));
        Ok(())
    }

    #[test]
    fn test_timestamp_builder() {
        // Using individual field setters produces the same Timestamp as using setters
        // for common combinations of fields (with_ymd, with_hms).
        let timestamp1 = TimestampBuilder::with_year(2021)
            .with_month(2)
            .with_day(5)
            .with_hour(17)
            .with_minute(39)
            .with_second(51)
            .with_milliseconds(194)
            .with_offset(-4 * 60)
            .build()
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        let timestamp2 = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hms(17, 39, 51)
            .with_milliseconds(194)
            .with_offset(-4 * 60)
            .build()
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        assert_eq!(timestamp1.precision(), TimestampPrecision::Second);
        assert_eq!(timestamp1.subsecond_digit_count(), 3);
        assert_eq!(timestamp1, timestamp2);

        assert!(timestamp1.ion_eq(&timestamp2));
    }

    #[test]
    fn test_timestamp_builder_without_minutes() {
        // Even though we set hour and not minute, this should still have a precision of HourAndMinute.
        let timestamp1 = TimestampBuilder::with_year(2021)
            .with_month(2)
            .with_day(5)
            .with_hour(17)
            .with_offset(60)
            .build()
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        let timestamp2 = TimestampBuilder::with_ymd(2021, 2, 5)
            .with_hour_and_minute(17, 0)
            .with_offset(60)
            .build()
            .unwrap_or_else(|e| panic!("Couldn't build timestamp: {e:?}"));

        assert_eq!(timestamp1.precision(), TimestampPrecision::HourAndMinute);
        assert_eq!(timestamp1, timestamp2)
    }

    #[test]
    fn test_timestamp_fixed_offset() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_milliseconds(449)
            .with_offset(-5 * 60)
            .build()?;
        //                    ^-- Timestamp's offset API takes minutes
        // expected offset in minutes
        let expected_offset = -5 * 60;

        assert_eq!(timestamp.offset().unwrap(), expected_offset);
        Ok(())
    }

    #[test]
    fn test_timestamp_precision() -> IonResult<()> {
        let timestamp = Timestamp::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp.precision(), TimestampPrecision::Month);
        Ok(())
    }

    #[test]
    fn test_timestamp_year() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.year(), 2021);

        let timestamp_2 = TimestampBuilder::with_ymd(2021, 12, 31)
            .with_hms(10, 15, 30)
            .with_offset(-11 * 60)
            .build()?;

        assert_eq!(timestamp_2.year(), 2021);

        let timestamp_3 = TimestampBuilder::with_ymd(2021, 12, 31)
            .with_hms(15, 15, 30)
            .with_offset(10 * 60)
            .build()?;

        assert_eq!(timestamp_3.year(), 2021);

        Ok(())
    }

    #[test]
    fn test_timestamp_month() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.month(), 2);

        let timestamp_2 = TimestampBuilder::with_ymd(2021, 1, 31)
            .with_hms(10, 15, 30)
            .with_offset(-11 * 60)
            .build()?;

        assert_eq!(timestamp_2.month(), 1);

        let timestamp_3 = TimestampBuilder::with_ymd(2021, 1, 31)
            .with_hms(15, 15, 30)
            .with_offset(10 * 60)
            .build()?;

        assert_eq!(timestamp_3.month(), 1);

        Ok(())
    }

    #[test]
    fn test_timestamp_day() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_year(2021).with_month(2).build()?;
        assert_eq!(timestamp_1.day(), 1);

        let timestamp_2 = TimestampBuilder::with_year(2021)
            .with_month(2)
            .with_day(4)
            .build()?;

        assert_eq!(timestamp_2.day(), 4);

        let timestamp_3 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_offset(-11 * 60)
            .build()?;

        assert_eq!(timestamp_3.day(), 6);

        let timestamp_4 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(15, 15, 30)
            .with_offset(10 * 60)
            .build()?;

        assert_eq!(timestamp_4.day(), 6);

        Ok(())
    }

    #[rstest]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-90).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-5 * 60).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(5 * 60).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(15).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(30).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(0).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(0, 15, 30).with_offset(5 * 60).build(), 0)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(23, 15, 30).with_offset(-5 * 60).build(), 23)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(0, 15, 30).with_offset(23 * 60).build(), 0)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-11 * 60).build(), 10)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(15, 15, 30).with_offset(10 * 60).build(), 15)]
    fn test_timestamp_hour(
        #[case] timestamp: IonResult<Timestamp>,
        #[case] expected_hours: u32,
    ) -> IonResult<()> {
        assert_eq!(timestamp?.hour(), expected_hours);
        Ok(())
    }

    #[rstest]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-90).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-5 * 60).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(5 * 60).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(0).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 0, 30).with_offset(5 * 60).build(), 0)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 59, 30).with_offset(5 * 60).build(), 59)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 30).with_offset(-11 * 60).build(), 15)]
    #[case(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(15, 15, 30).with_offset(10 * 60).build(), 15)]
    fn test_timestamp_minute(
        #[case] timestamp: IonResult<Timestamp>,
        #[case] expected_minutes: u32,
    ) -> IonResult<()> {
        assert_eq!(timestamp?.minute(), expected_minutes);
        Ok(())
    }

    #[test]
    fn test_timestamp_second() -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp.second(), 30);
        Ok(())
    }

    #[test]
    fn test_timestamp_nanoseconds() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_nanoseconds(192)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_1.nanoseconds(), 192);

        let timestamp_2 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_milliseconds(192)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_2.nanoseconds(), 192000000);

        let timestamp_3 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_3.nanoseconds(), 0);

        // Big fractional coefficient (>18 digits) is rejected
        let big_coefficient: Int = Int::from(i128::MAX).data.mul(4).into();
        let result = Timestamp::with_ymd(2023, 1, 1)
            .with_hour_and_minute(0, 0)
            .with_second(0)
            .with_fractional_seconds(Decimal::new(big_coefficient, -39))
            .build();
        assert!(result.is_err());

        // Exponent delta > 18 digits: also rejected
        let result = Timestamp::with_ymd(2023, 1, 1)
            .with_hour_and_minute(0, 0)
            .with_second(0)
            .with_fractional_seconds(Decimal::new(1i64, -50))
            .build();
        assert!(result.is_err());

        // 19 fractional digits: rejected (limit is 18)
        let result = Timestamp::with_ymd(2023, 1, 1)
            .with_hour_and_minute(0, 0)
            .with_second(0)
            .with_fractional_seconds(Decimal::new(1234567890123456789u64, -19))
            .build();
        assert!(result.is_err());

        // 18 fractional digits (max allowed) should work
        let timestamp_4 = Timestamp::with_ymd(2023, 1, 1)
            .with_hour_and_minute(0, 0)
            .with_second(0)
            .with_fractional_seconds(Decimal::new(123456789u64, -9))
            .build()?;
        assert_eq!(timestamp_4.nanoseconds(), 123456789);

        Ok(())
    }

    #[rstest]
    // `precision_digits` finer than or equal to the value keeps it intact...
    #[case(123_456_789, 9, 123_456_789, "2023-01-01T00:00:00.123456789+00:00")]
    // ...and a coarser precision strips the less-significant digits so the stored value stays
    // consistent with the declared precision (fractional-seconds invariant 5).
    #[case(123_456_789, 3, 123_000_000, "2023-01-01T00:00:00.123+00:00")]
    #[case(123_456_789, 6, 123_456_000, "2023-01-01T00:00:00.123456+00:00")]
    #[case(1, 3, 0, "2023-01-01T00:00:00.000+00:00")]
    fn with_nanoseconds_and_precision_strips_over_precision(
        #[case] nanoseconds: u32,
        #[case] precision_digits: u32,
        #[case] expected_nanoseconds: u32,
        #[case] expected_text: &str,
    ) -> IonResult<()> {
        let timestamp = TimestampBuilder::with_ymd(2023, 1, 1)
            .with_hms(0, 0, 0)
            .with_nanoseconds_and_precision(nanoseconds, precision_digits)
            .with_offset(0)
            .build()?;
        assert_eq!(timestamp.nanoseconds(), expected_nanoseconds);
        assert_eq!(timestamp.to_string(), expected_text);
        Ok(())
    }

    #[test]
    fn test_timestamp_milliseconds() -> IonResult<()> {
        let timestamp_1 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_milliseconds(192)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_1.milliseconds(), 192);

        let timestamp_2 = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 30)
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(timestamp_2.milliseconds(), 0);
        Ok(())
    }

    #[test]
    fn test_timestamp_to_utc() -> IonResult<()> {
        let new_years_eve_nyc = TimestampBuilder::with_ymd(2022, 12, 31)
            .with_hms(23, 59, 00)
            .with_offset(-5 * 60)
            .build()?;

        let london = new_years_eve_nyc.to_utc();
        assert_eq!(london.year(), 2023);
        assert_eq!(london.month(), 1);
        assert_eq!(london.day(), 1);
        assert_eq!(london.hour(), 4);
        assert_eq!(london.minute(), 59);
        assert_eq!(london.second(), 0);
        Ok(())
    }

    #[test]
    fn test_timestamp_to_utc_year_boundary() -> IonResult<()> {
        // UTC conversion that crosses year boundary to year 0 must not panic
        let ts = TimestampBuilder::with_ymd(1, 1, 1)
            .with_hour_and_minute(0, 30)
            .with_offset(60)
            .build()?;
        let utc = ts.to_utc();
        assert_eq!(utc.year(), 0);
        assert_eq!(utc.month(), 12);
        assert_eq!(utc.day(), 31);
        assert_eq!(utc.hour(), 23);
        assert_eq!(utc.minute(), 30);
        Ok(())
    }

    #[test]
    fn test_timestamp_comparison_year_boundary_no_panic() -> IonResult<()> {
        // Comparing timestamps where UTC conversion yields year 0 must not panic
        let ts1 = TimestampBuilder::with_ymd(1, 1, 1)
            .with_hour_and_minute(0, 30)
            .with_offset(60)
            .build()?;
        let ts2 = TimestampBuilder::with_ymd(1, 1, 1)
            .with_hour_and_minute(1, 30)
            .with_offset(60)
            .build()?;
        assert!(ts1 < ts2);
        Ok(())
    }

    #[test]
    fn test_timestamp_fractional_seconds_scale() -> IonResult<()> {
        // Set fractional seconds as Decimal
        let timestamp_with_micro_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_fractional_seconds(Decimal::new(553u64, -6))
            .with_offset(-5 * 60)
            .build()?;

        assert_eq!(
            timestamp_with_micro_seconds
                .fractional_seconds_scale()
                .unwrap(),
            6
        );

        // Set fractional seconds as Decimal with 0 coefficient and non-negative exponent
        // "Fractions whose coefficient is zero and exponent is greater than -1 are ignored."
        let timestamp_with_redundant_fractional_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_fractional_seconds(Decimal::new(0, 6))
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(
            timestamp_with_redundant_fractional_seconds.precision(),
            TimestampPrecision::Second
        );
        assert_eq!(
            timestamp_with_redundant_fractional_seconds.fractional_seconds_scale(),
            None
        );

        // Set fractional seconds with milliseconds
        let timestamp_with_milliseconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_milliseconds(449)
            .with_offset(-5 * 60)
            .build()?;

        assert_eq!(
            timestamp_with_milliseconds
                .fractional_seconds_scale()
                .unwrap(),
            3
        );

        // Set a fractional seconds as Decimal with low precision
        let timestamp_with_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_offset(-5 * 60)
            .build()?;

        // For low precision fractional_seconds_scale should return a None
        assert_eq!(timestamp_with_seconds.fractional_seconds_scale(), None);
        Ok(())
    }

    #[test]
    fn test_timestamp_subsecond_digit_count() -> IonResult<()> {
        // Set fractional seconds as Decimal
        let timestamp_with_micro_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_fractional_seconds(Decimal::new(553u64, -6))
            .with_offset(-5 * 60)
            .build()?;

        assert_eq!(timestamp_with_micro_seconds.subsecond_digit_count(), 6);

        // Set fractional seconds as Decimal with 0 coefficient and non-negative exponent
        // "Fractions whose coefficient is zero and exponent is greater than -1 are ignored."
        let timestamp_with_redundant_fractional_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_fractional_seconds(Decimal::new(0, 6))
            .with_offset(-5 * 60)
            .build()?;
        assert_eq!(
            timestamp_with_redundant_fractional_seconds.precision(),
            TimestampPrecision::Second
        );
        assert_eq!(
            timestamp_with_redundant_fractional_seconds.subsecond_digit_count(),
            0
        );

        // Set fractional seconds with milliseconds
        let timestamp_with_milliseconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_milliseconds(449)
            .with_offset(-5 * 60)
            .build()?;

        assert_eq!(timestamp_with_milliseconds.subsecond_digit_count(), 3);

        // Set a fractional seconds as Decimal with low precision
        let timestamp_with_seconds = TimestampBuilder::with_ymd(2021, 4, 6)
            .with_hms(10, 15, 0)
            .with_offset(-5 * 60)
            .build()?;

        // For low precision fractional_seconds_digits should return 0
        assert_eq!(timestamp_with_seconds.subsecond_digit_count(), 0);
        Ok(())
    }

    #[rstest]
    #[case::timestamp_with_same_year(TimestampBuilder::with_year(2020).build().unwrap(), TimestampBuilder::with_year(2020).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_year(TimestampBuilder::with_year(2020).build().unwrap(), TimestampBuilder::with_year(2021).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_milliseconds(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_milliseconds(449).with_offset(5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_milliseconds(449).with_offset(5 * 60).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_milliseconds_nanoseconds(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_milliseconds(449).with_offset(5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_nanoseconds(449000005).with_offset(5 * 60).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_fractional_seconds(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_fractional_seconds(Decimal::new(449u64, -3)).with_offset(5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_nanoseconds(449000000).with_offset(5 * 60).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_precision(TimestampBuilder::with_year(2020).with_month(3).build().unwrap(), TimestampBuilder::with_year(2020).build().unwrap(), Ordering::Greater)]
    #[case::timestamp_with_same_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(-5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(-5 * 60).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_different_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(5 * 60).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(-5 * 60).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_unknown_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_offset(-5 * 60).build().unwrap(), Ordering::Less)]
    #[case::timestamp_with_unknown_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_nanoseconds(0).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).build().unwrap(), Ordering::Equal)]
    #[case::timestamp_with_unknown_offset(TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).with_nanoseconds(449000005).build().unwrap(), TimestampBuilder::with_ymd(2021, 4, 6).with_hms(10, 15, 0).build().unwrap(), Ordering::Greater)]
    #[case::timestamp_with_second_precison_and_year_precision(TimestampBuilder::with_ymd(2001, 1, 1).build().unwrap(), TimestampBuilder::with_ymd(2001, 1, 1).with_hms(0, 0, 0).with_fractional_seconds(Decimal::new(0i128, -18)).build().unwrap(), Ordering::Equal)]
    fn timestamp_ordering_tests(
        #[case] this: Timestamp,
        #[case] other: Timestamp,
        #[case] expected: Ordering,
    ) {
        assert_eq!(this.cmp(&other), expected)
    }

    #[test]
    fn ion_eq_same_instant_different_offset_not_ion_eq() {
        // Same instant, different offsets → PartialEq but NOT ion_eq
        let t1 = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(12, 0, 0)
            .with_offset(0)
            .build()
            .unwrap();
        let t2 = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(13, 0, 0)
            .with_offset(60)
            .build()
            .unwrap();
        assert_eq!(t1, t2); // same instant
        assert!(!t1.ion_eq(&t2)); // different local representations
    }

    #[test]
    fn ion_eq_different_fractional_precision_not_ion_eq() {
        // Same value but different precision → NOT ion_eq
        // 2024-01-01T00:00:00.100+00:00 vs 2024-01-01T00:00:00.1+00:00
        let t1 = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_milliseconds(100)
            .with_offset(0)
            .build()
            .unwrap();
        let t2 = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_fractional_seconds(Decimal::new(1u64, -1))
            .with_offset(0)
            .build()
            .unwrap();
        assert_eq!(t1, t2); // same instant
        assert!(!t1.ion_eq(&t2)); // different precision (3 digits vs 1 digit)
    }

    #[rstest]
    #[case(TimestampBuilder::with_year(3030).build().unwrap(), "3030T")]
    #[case(TimestampBuilder::with_year(3030).with_month(11).build().unwrap(), "3030-11T")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).build().unwrap(), "3030-03-31T")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).build().unwrap(), "3030-03-31T17:31-00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).with_offset(-420).build().unwrap(), "3030-03-31T17:31-07:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hour_and_minute(17, 31).build_utc_fields_at_offset(-420).unwrap(), "3030-03-31T10:31-07:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_offset(0).build().unwrap(), "3030-03-31T17:31:57+00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_milliseconds(27).with_offset(0).build().unwrap(), "3030-03-31T17:31:57.027+00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_microseconds(27).with_offset(0).build().unwrap(), "3030-03-31T17:31:57.000027+00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_nanoseconds(27).with_offset(0).build().unwrap(), "3030-03-31T17:31:57.000000027+00:00")]
    #[case(TimestampBuilder::with_ymd(3030, 3, 31).with_hms(17, 31, 57).with_fractional_seconds(Decimal::new(27, -12)).with_offset(0).build().unwrap(), "3030-03-31T17:31:57.000000000027+00:00")]
    fn test_display(#[case] ts: Timestamp, #[case] expect: String) {
        let mut buf = Vec::new();
        write!(&mut buf, "{ts}").unwrap();
        assert_eq!(expect, String::from_utf8(buf).unwrap());
    }

    /// Fields that do not fit the packed representation must be reported as an error rather than
    /// being silently narrowed. Several of these values would wrap into an in-range value if
    /// cast without validation (e.g. month 268 truncates to 12, offset 65536 to 0), producing a
    /// `Timestamp` that differs from what the caller asked for.
    #[rstest]
    #[case::year_too_large(TimestampBuilder::with_year(10_000).build())]
    #[case::year_wraps_to_in_range(TimestampBuilder::with_year(65536 + 2021).build())]
    #[case::month_too_large(TimestampBuilder::with_year(2021).with_month(13).build())]
    #[case::month_wraps_to_in_range(TimestampBuilder::with_year(2021).with_month(268).build())]
    #[case::day_too_large(TimestampBuilder::with_ymd(2021, 1, 32).build())]
    #[case::day_wraps_to_in_range(TimestampBuilder::with_ymd(2021, 1, 256 + 5).build())]
    #[case::hour_too_large(TimestampBuilder::with_ymd(2021, 1, 1).with_hour_and_minute(24, 0).build())]
    #[case::hour_wraps_to_in_range(TimestampBuilder::with_ymd(2021, 1, 1).with_hour_and_minute(256 + 5, 0).build())]
    #[case::minute_too_large(TimestampBuilder::with_ymd(2021, 1, 1).with_hour_and_minute(0, 60).build())]
    #[case::minute_wraps_to_in_range(TimestampBuilder::with_ymd(2021, 1, 1).with_hour_and_minute(0, 256 + 5).build())]
    #[case::second_too_large(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 60).build())]
    #[case::second_wraps_to_in_range(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 256 + 5).build())]
    #[case::offset_too_large(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_offset(1440).build())]
    #[case::offset_too_small(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_offset(-1440).build())]
    #[case::offset_wraps_to_in_range(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_offset(65536).build())]
    #[case::millis_too_large(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_milliseconds(1000).build())]
    #[case::micros_too_large(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_microseconds(1_000_000).build())]
    #[case::nanos_too_large(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_nanoseconds(1_000_000_000).build())]
    #[case::frac_precision_too_large(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_nanoseconds_and_precision(1, 30).build())]
    // Precisions that narrow to an in-range `u8` (`256 as u8 == 0`, `274 as u8 == 18`) must still
    // be rejected, i.e. the wider `fractional_digits` field must not let them wrap.
    #[case::frac_precision_wraps_to_zero(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_nanoseconds_and_precision(1, 256).build())]
    #[case::frac_precision_wraps_to_in_range(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_nanoseconds_and_precision(1, 274).build())]
    // A `Decimal` exponent whose magnitude wraps to an in-range value when narrowed (`2^32 + 3`
    // narrows to `3`) must be rejected, for both a non-zero and a zero coefficient.
    #[case::frac_exponent_wraps_nonzero(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_fractional_seconds(Decimal::new(1i128, -4_294_967_299i64)).build())]
    #[case::frac_exponent_wraps_zero(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_fractional_seconds(Decimal::new(0i128, -4_294_967_299i64)).build())]
    // A zero value with >18 declared digits is rejected too, for consistency with the non-zero
    // path (rather than silently truncating its precision to 18).
    #[case::frac_zero_over_precision(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_fractional_seconds(Decimal::new(0i128, -19i64)).build())]
    // A fractional value outside `[0, 1)` must be rejected.
    #[case::frac_seconds_ge_one(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_fractional_seconds(Decimal::new(15i128, -1i64)).build())]
    #[case::frac_seconds_negative(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_fractional_seconds(Decimal::new(-5i128, -1i64)).build())]
    fn test_out_of_range_fields_are_rejected(#[case] result: IonResult<Timestamp>) {
        assert!(
            result.is_err(),
            "expected an out-of-range field to be rejected, but built {:?}",
            result.ok()
        );
    }

    /// The largest in-range value for each field must still build, confirming the range checks
    /// above are not off by one.
    #[rstest]
    #[case::max_year(TimestampBuilder::with_year(9999).build(), "9999T")]
    #[case::max_month(TimestampBuilder::with_year(2021).with_month(12).build(), "2021-12T")]
    #[case::max_day(TimestampBuilder::with_ymd(2021, 1, 31).build(), "2021-01-31T")]
    #[case::max_hour_and_minute(TimestampBuilder::with_ymd(2021, 1, 1).with_hour_and_minute(23, 59).build(), "2021-01-01T23:59-00:00")]
    #[case::max_second(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(23, 59, 59).build(), "2021-01-01T23:59:59-00:00")]
    #[case::max_offset(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_offset(1439).build(), "2021-01-01T00:00:00+23:59")]
    #[case::min_offset(TimestampBuilder::with_ymd(2021, 1, 2).with_hms(0, 0, 0).with_offset(-1439).build(), "2021-01-02T00:00:00-23:59")]
    #[case::max_millis(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_milliseconds(999).build(), "2021-01-01T00:00:00.999-00:00")]
    #[case::max_micros(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_microseconds(999_999).build(), "2021-01-01T00:00:00.999999-00:00")]
    #[case::max_nanos(TimestampBuilder::with_ymd(2021, 1, 1).with_hms(0, 0, 0).with_nanoseconds(999_999_999).build(), "2021-01-01T00:00:00.999999999-00:00")]
    fn test_max_in_range_fields_are_accepted(
        #[case] result: IonResult<Timestamp>,
        #[case] expected: &str,
    ) -> IonResult<()> {
        assert_eq!(expected, result?.to_string());
        Ok(())
    }

    // --- Day rollover in Ord ---

    #[test]
    fn cmp_day_rollover_forward() -> IonResult<()> {
        // 2024-01-01T23:00+00:00 vs 2024-01-01T01:00-23:00
        // Second timestamp's local time is 01:00, but offset is -23:00
        // so UTC = 01:00 + 23:00 = 2024-01-02T00:00 UTC
        // First is 2024-01-01T23:00 UTC
        // Second > First
        let t1 = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(23, 0, 0)
            .with_offset(0)
            .build()?;
        let t2 = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(1, 0, 0)
            .with_offset(-23 * 60)
            .build()?;
        assert_eq!(t1.cmp(&t2), Ordering::Less);
        Ok(())
    }

    #[test]
    fn cmp_day_rollover_backward() -> IonResult<()> {
        // 2024-01-02T01:00+00:00 vs 2024-01-02T23:00+23:00
        // Second: local 23:00, offset +23:00, UTC = 23:00 - 23:00 = 00:00 on same day
        // = 2024-01-02T00:00 UTC
        // First: 2024-01-02T01:00 UTC
        // First > Second
        let t1 = TimestampBuilder::with_ymd(2024, 1, 2)
            .with_hms(1, 0, 0)
            .with_offset(0)
            .build()?;
        let t2 = TimestampBuilder::with_ymd(2024, 1, 2)
            .with_hms(23, 0, 0)
            .with_offset(23 * 60)
            .build()?;
        assert_eq!(t1.cmp(&t2), Ordering::Greater);
        Ok(())
    }

    #[test]
    fn cmp_day_rollover_equal() -> IonResult<()> {
        // Same instant across a day boundary via offset
        let t1 = TimestampBuilder::with_ymd(2024, 3, 1)
            .with_hms(0, 30, 0)
            .with_offset(0)
            .build()?;
        let t2 = TimestampBuilder::with_ymd(2024, 2, 29)
            .with_hms(23, 30, 0)
            .with_offset(-60)
            .build()?;
        assert_eq!(t1.cmp(&t2), Ordering::Equal);
        assert_eq!(t1, t2);
        Ok(())
    }

    // --- Debug impl ---

    #[test]
    fn debug_impl() -> IonResult<()> {
        let ts = TimestampBuilder::with_ymd(2024, 8, 12)
            .with_hms(14, 30, 45)
            .with_offset(0)
            .build()?;
        let debug = format!("{:?}", ts);
        assert_eq!(debug, "Timestamp(2024-08-12T14:30:45+00:00)");
        Ok(())
    }

    // --- with_month0 and with_day0 ---

    #[test]
    fn with_month0_zero_indexed() -> IonResult<()> {
        // month0(0) = January, month0(11) = December
        let jan = TimestampBuilder::with_year(2024).with_month0(0).build()?;
        assert_eq!(jan.month(), 1);
        let dec = TimestampBuilder::with_year(2024).with_month0(11).build()?;
        assert_eq!(dec.month(), 12);
        Ok(())
    }

    #[test]
    fn with_day0_zero_indexed() -> IonResult<()> {
        // day0(0) = day 1, day0(30) = day 31
        let d1 = TimestampBuilder::with_year(2024)
            .with_month(1)
            .with_day0(0)
            .build()?;
        assert_eq!(d1.day(), 1);
        let d31 = TimestampBuilder::with_year(2024)
            .with_month(1)
            .with_day0(30)
            .build()?;
        assert_eq!(d31.day(), 31);
        Ok(())
    }

    // --- Boundary validation ---

    #[test]
    fn invalid_year_zero() {
        assert!(TimestampBuilder::with_year(0).build().is_err());
    }

    #[test]
    fn invalid_year_too_large() {
        assert!(TimestampBuilder::with_year(10000).build().is_err());
    }

    #[test]
    fn valid_year_boundaries() -> IonResult<()> {
        let y1 = TimestampBuilder::with_year(1).build()?;
        assert_eq!(y1.year(), 1);
        let y9999 = TimestampBuilder::with_year(9999).build()?;
        assert_eq!(y9999.year(), 9999);
        Ok(())
    }

    #[test]
    fn invalid_month_zero() {
        assert!(TimestampBuilder::with_year(2024)
            .with_month(0)
            .build()
            .is_err());
    }

    #[test]
    fn invalid_month_13() {
        assert!(TimestampBuilder::with_year(2024)
            .with_month(13)
            .build()
            .is_err());
    }

    #[test]
    fn valid_month_boundaries() -> IonResult<()> {
        let m1 = TimestampBuilder::with_year(2024).with_month(1).build()?;
        assert_eq!(m1.month(), 1);
        let m12 = TimestampBuilder::with_year(2024).with_month(12).build()?;
        assert_eq!(m12.month(), 12);
        Ok(())
    }

    #[test]
    fn invalid_day_zero() {
        assert!(TimestampBuilder::with_ymd(2024, 1, 0).build().is_err());
    }

    #[test]
    fn invalid_day_32() {
        assert!(TimestampBuilder::with_ymd(2024, 1, 32).build().is_err());
    }

    #[test]
    fn invalid_day_feb_29_non_leap() {
        assert!(TimestampBuilder::with_ymd(2023, 2, 29).build().is_err());
    }

    #[test]
    fn valid_day_feb_29_leap() -> IonResult<()> {
        let ts = TimestampBuilder::with_ymd(2024, 2, 29).build()?;
        assert_eq!(ts.day(), 29);
        Ok(())
    }

    #[test]
    fn invalid_offset_too_negative() {
        assert!(TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_offset(-1440)
            .build()
            .is_err());
    }

    #[test]
    fn invalid_offset_too_positive() {
        assert!(TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_offset(1440)
            .build()
            .is_err());
    }

    #[test]
    fn valid_offset_boundaries() -> IonResult<()> {
        let min = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_offset(-1439)
            .build()?;
        assert_eq!(min.offset(), Some(-1439));
        let max = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_offset(1439)
            .build()?;
        assert_eq!(max.offset(), Some(1439));
        Ok(())
    }

    #[test]
    fn invalid_nanoseconds_too_large() {
        assert!(TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_nanoseconds(1_000_000_000)
            .build()
            .is_err());
    }

    #[test]
    fn invalid_microseconds_too_large() {
        assert!(TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_microseconds(1_000_000)
            .build()
            .is_err());
    }

    #[test]
    fn invalid_milliseconds_too_large() {
        assert!(TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_milliseconds(1000)
            .build()
            .is_err());
    }

    #[test]
    fn valid_max_fractional_seconds() -> IonResult<()> {
        let ts = TimestampBuilder::with_ymd(2024, 1, 1)
            .with_hms(0, 0, 0)
            .with_nanoseconds(999_999_999)
            .build()?;
        assert_eq!(ts.nanoseconds(), 999_999_999);
        Ok(())
    }
}

/// `chrono` interop. All of `timestamp.rs`'s `experimental-chrono` code lives here so the
/// feature's footprint in this file is a single gated module rather than gates scattered
/// throughout. (`serde` support also compiles under this feature; see `src/serde/`.) As a
/// descendant module it retains access to `Timestamp`'s private fields and the packed-layout
/// constants.
///
/// Named `chrono_interop` rather than `chrono` so it does not shadow the extern crate for the
/// rest of `timestamp.rs`.
#[cfg(feature = "experimental-chrono")]
mod chrono_interop {
    use super::{
        Timestamp, TimestampPrecision, DAY_MASK, DAY_SHIFT, HOUR_MASK, HOUR_SHIFT, MINUTE_MASK,
        MINUTE_SHIFT, MONTH_MASK, MONTH_SHIFT, OFFSET_BIAS, OFFSET_MASK, OFFSET_SHIFT,
        OFFSET_UNKNOWN_SENTINEL, PRECISION_MASK, PRECISION_SHIFT, YEAR_MASK, YEAR_SHIFT,
    };
    use crate::result::{IonFailure, IonResult};
    use crate::IonError;
    use chrono::{DateTime, Datelike, FixedOffset, NaiveDate, NaiveDateTime, TimeZone, Timelike};

    /// Converts a chrono subsecond value (`Timelike::nanosecond`) into `attoseconds`.
    ///
    /// chrono encodes a leap second as `second() == 59` with `nanosecond()` in
    /// `1_000_000_000..2_000_000_000`. Ion `Timestamp` has no leap-second representation, so a
    /// leap-second value is folded into the final second: the extra second is dropped and the
    /// fractional part is kept (e.g. `23:59:60.5` becomes `23:59:59.5`).
    fn nanoseconds_to_attoseconds(nanosecond: u32) -> u64 {
        let folded = if nanosecond >= 1_000_000_000 {
            nanosecond - 1_000_000_000
        } else {
            nanosecond
        };
        folded as u64 * 1_000_000_000
    }

    impl Timestamp {
        /// Converts a [`NaiveDateTime`] or [`DateTime<FixedOffset>`] to a Timestamp with the specified
        /// precision. If the precision is [`TimestampPrecision::Second`], nanosecond precision (the maximum
        /// supported by a [`Timelike`]) is assumed.
        pub fn from_datetime<D>(datetime: D, precision: TimestampPrecision) -> Timestamp
        where
            D: Datelike + Timelike + Into<Timestamp>,
        {
            let mut timestamp: Timestamp = datetime.into();

            // Zero fields below the requested precision to uphold invariants 1, 2, and 6.
            match precision {
                TimestampPrecision::Year => {
                    timestamp.packed_fields &= YEAR_MASK << YEAR_SHIFT;
                    // Restore month=1, day=1 (the default "unset" values)
                    timestamp.packed_fields |= 1 << MONTH_SHIFT | 1 << DAY_SHIFT;
                    timestamp.attoseconds = 0;
                }
                TimestampPrecision::Month => {
                    timestamp.packed_fields &=
                        (YEAR_MASK << YEAR_SHIFT) | (MONTH_MASK << MONTH_SHIFT);
                    // Restore day=1
                    timestamp.packed_fields |= 1 << DAY_SHIFT;
                    timestamp.attoseconds = 0;
                }
                TimestampPrecision::Day => {
                    timestamp.packed_fields &= (YEAR_MASK << YEAR_SHIFT)
                        | (MONTH_MASK << MONTH_SHIFT)
                        | (DAY_MASK << DAY_SHIFT);
                    timestamp.attoseconds = 0;
                }
                TimestampPrecision::HourAndMinute => {
                    timestamp.packed_fields &= (YEAR_MASK << YEAR_SHIFT)
                        | (MONTH_MASK << MONTH_SHIFT)
                        | (DAY_MASK << DAY_SHIFT)
                        | (HOUR_MASK << HOUR_SHIFT)
                        | (MINUTE_MASK << MINUTE_SHIFT)
                        | (OFFSET_MASK << OFFSET_SHIFT);
                    timestamp.attoseconds = 0;
                }
                TimestampPrecision::Second => {
                    // Keep everything; just strip subsecond if not already at Second precision
                }
            }

            // Set the precision field
            timestamp.packed_fields &= !(PRECISION_MASK << PRECISION_SHIFT);
            timestamp.packed_fields |= (precision as u64 & PRECISION_MASK) << PRECISION_SHIFT;

            // Retain offset only at HourAndMinute or Second precision
            if precision < TimestampPrecision::HourAndMinute {
                timestamp.packed_fields &= !(OFFSET_MASK << OFFSET_SHIFT);
            }

            timestamp
        }

        fn from_naive_datetime(date_time: NaiveDateTime) -> Self {
            let attoseconds = nanoseconds_to_attoseconds(date_time.nanosecond());
            // Pack directly from the fields, bypassing `from_fields` validation. chrono permits
            // years outside Ion's 1..=9999 range (e.g. year 0), which `from_fields` would reject;
            // we accept them silently here so this conversion behaves consistently with
            // `from_fixed_offset_datetime`. Making both conversions fallible is tracked in #1035.
            // A `NaiveDateTime` has no offset, so the offset is stored as "unknown".
            let packed = Self::pack_masked(
                TimestampPrecision::Second,
                date_time.year() as u16,
                date_time.month() as u8,
                date_time.day() as u8,
                date_time.hour() as u8,
                date_time.minute() as u8,
                date_time.second() as u8,
                OFFSET_UNKNOWN_SENTINEL,
                9,
            );
            Timestamp {
                packed_fields: packed,
                attoseconds,
            }
        }

        fn from_fixed_offset_datetime(fixed_offset_date_time: DateTime<FixedOffset>) -> Self {
            let offset_seconds = fixed_offset_date_time.offset().local_minus_utc();
            let offset_minutes = (offset_seconds / 60) as i16;
            let local = fixed_offset_date_time.naive_local();
            let attoseconds = nanoseconds_to_attoseconds(local.nanosecond());
            // Pack directly from local fields — chrono guarantees validity of the
            // DateTime, and local year may exceed 9999 (e.g., UTC year 9999 Dec 31
            // with negative offset). We bypass from_fields validation to avoid panic.
            let packed = Self::pack_masked(
                TimestampPrecision::Second,
                local.year() as u16,
                local.month() as u8,
                local.day() as u8,
                local.hour() as u8,
                local.minute() as u8,
                local.second() as u8,
                (offset_minutes + OFFSET_BIAS) as u16,
                9,
            );
            Timestamp {
                packed_fields: packed,
                attoseconds,
            }
        }

        fn try_to_naive_datetime(&self) -> IonResult<NaiveDateTime> {
            if self.offset().is_some() {
                return IonResult::illegal_operation(
                    "cannot convert a Timestamp with a known offset into a NaiveDateTime",
                );
            }
            downconvert_to_naive_datetime_with_nanoseconds(self)
        }

        fn try_to_datetime_fixed_offset(&self) -> IonResult<DateTime<FixedOffset>> {
            if self.offset().is_none() {
                return IonResult::illegal_operation(
                    "cannot convert a Timestamp with an unknown offset into a DateTime<FixedOffset>",
                );
            }
            let utc = self.to_utc();
            let utc_naive = downconvert_to_naive_datetime_with_nanoseconds(&utc)?;
            let offset = FixedOffset::east_opt(self.offset().unwrap_or_default() * 60);
            Ok(offset.unwrap().from_utc_datetime(&utc_naive))
        }
    }

    fn downconvert_to_naive_datetime_with_nanoseconds(
        timestamp: &Timestamp,
    ) -> IonResult<NaiveDateTime> {
        let dt =
            NaiveDate::from_ymd_opt(timestamp.year() as i32, timestamp.month(), timestamp.day())
                .and_then(|d| {
                    d.and_hms_nano_opt(
                        timestamp.hour(),
                        timestamp.minute(),
                        timestamp.second(),
                        timestamp.nanoseconds(),
                    )
                })
                .ok_or_else(|| {
                    IonError::illegal_operation("timestamp fields produce invalid NaiveDateTime")
                })?;
        Ok(dt)
    }

    impl TryInto<NaiveDateTime> for Timestamp {
        type Error = IonError;

        fn try_into(self) -> Result<NaiveDateTime, Self::Error> {
            self.try_to_naive_datetime()
        }
    }

    impl TryInto<DateTime<FixedOffset>> for Timestamp {
        type Error = IonError;

        fn try_into(self) -> Result<DateTime<FixedOffset>, Self::Error> {
            self.try_to_datetime_fixed_offset()
        }
    }

    impl From<NaiveDateTime> for Timestamp {
        fn from(date_time: NaiveDateTime) -> Self {
            Self::from_naive_datetime(date_time)
        }
    }

    impl From<DateTime<FixedOffset>> for Timestamp {
        fn from(fixed_offset_date_time: DateTime<FixedOffset>) -> Self {
            Self::from_fixed_offset_datetime(fixed_offset_date_time)
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;
        use crate::types::TimestampBuilder;

        /// Constructs a [`FixedOffset`] at the specified offset seconds from UTC. If the specified
        /// offset is out of bounds, this method will panic.
        // Only these tests construct a `FixedOffset` this way; production conversions build the
        // offset from a `Timestamp` whose offset the builder has already bounded to ±1439 minutes.
        fn offset_east(seconds_east: i32) -> FixedOffset {
            FixedOffset::east_opt(seconds_east)
                .expect("seconds_east was outside the supported range")
        }

        /// chrono encodes a leap second as `23:59:60` (`second() == 59`, `nanosecond() >= 1e9`).
        /// Ion has no leap-second representation, so the conversion folds it into the final second.
        #[test]
        fn leap_second_is_folded_into_prior_second() {
            let leap = NaiveDate::from_ymd_opt(2016, 12, 31)
                .unwrap()
                .and_hms_nano_opt(23, 59, 59, 1_500_000_000)
                .unwrap();
            let timestamp = Timestamp::from(leap);
            assert_eq!(timestamp.second(), 59);
            // The `.5` of the leap second is retained, attributed to second 59.
            assert_eq!(timestamp.nanoseconds(), 500_000_000);

            // Same folding through the `DateTime<FixedOffset>` conversion.
            let leap_fixed = offset_east(0).from_utc_datetime(&leap);
            let from_fixed = Timestamp::from(leap_fixed);
            assert_eq!(from_fixed.second(), 59);
            assert_eq!(from_fixed.nanoseconds(), 500_000_000);
        }

        /// chrono permits years outside Ion's `1..=9999` range. Both `From` conversions accept
        /// such values silently (masking the year to the packed field) rather than one panicking
        /// and the other masking. This documents that agreed-upon behavior; making the conversions
        /// fallible is tracked in #1035.
        #[test]
        fn out_of_range_year_is_accepted_consistently_by_both_conversions() {
            // `From<NaiveDateTime>`: year 0 must not panic.
            let naive_year_zero = NaiveDate::from_ymd_opt(0, 1, 1)
                .unwrap()
                .and_hms_opt(0, 0, 0)
                .unwrap();
            let from_naive = Timestamp::from(naive_year_zero);

            // `From<DateTime<FixedOffset>>`: year 0 at UTC.
            let fixed_year_zero = offset_east(0)
                .from_local_datetime(&naive_year_zero)
                .unwrap();
            let from_fixed = Timestamp::from(fixed_year_zero);

            // Neither errored or panicked, and both masked year 0 into the 14-bit field the same
            // way, so the two conversions agree.
            assert_eq!(from_naive.year(), from_fixed.year());
        }

        #[test]
        fn test_timestamp_try_into_naive_datetime() -> IonResult<()> {
            let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
                .with_hms(10, 15, 0)
                .build()?;
            let naive_datetime: NaiveDateTime = timestamp.try_into()?;
            let expected = NaiveDate::from_ymd_opt(2021, 4, 6)
                .unwrap()
                .and_hms_opt(10, 15, 0)
                .unwrap();
            assert_eq!(expected, naive_datetime);
            Ok(())
        }

        #[test]
        fn test_timestamp_try_into_naive_datetime_fractional_seconds() -> IonResult<()> {
            let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
                .with_hms(10, 15, 0)
                .with_milliseconds(449)
                .build()?;
            let datetime: NaiveDateTime = timestamp.try_into()?;
            let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
                .unwrap()
                .and_hms_opt(10, 15, 0)
                .unwrap()
                .with_nanosecond(449000000)
                .unwrap();
            assert_eq!(datetime, naive_datetime);
            Ok(())
        }

        #[test]
        fn test_timestamp_try_into_naive_datetime_error() -> IonResult<()> {
            let timestamp = TimestampBuilder::with_ymd(2021, 1, 1)
                .with_hms(0, 0, 0)
                .with_offset(0)
                .build()?;
            //     ^---- This timestamp has a known offset, so we cannot convert it into a NaiveDateTime
            let result: IonResult<NaiveDateTime> = timestamp.try_into();
            assert!(result.is_err());
            Ok(())
        }

        #[test]
        fn test_timestamp_try_into_fixed_offset_datetime() -> IonResult<()> {
            let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
                .with_hms(10, 15, 0)
                .with_offset(-5 * 60)
                .build()?;
            //                    ^-- Timestamp's offset API takes minutes
            let datetime: DateTime<FixedOffset> = timestamp.try_into()?;
            // chrono's FixedOffset takes seconds ----------v
            let expected_offset = offset_east(-5 * 60 * 60);
            let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
                .unwrap()
                .and_hms_opt(10, 15, 0)
                .unwrap();
            let expected_datetime = expected_offset
                .from_local_datetime(&naive_datetime)
                .unwrap();
            assert_eq!(datetime, expected_datetime);
            Ok(())
        }

        #[test]
        fn test_timestamp_try_into_fixed_offset_datetime_fractional_seconds() -> IonResult<()> {
            let timestamp = TimestampBuilder::with_ymd(2021, 4, 6)
                .with_hms(10, 15, 0)
                .with_milliseconds(449)
                .with_offset(-5 * 60)
                .build()?;
            //                    ^-- Timestamp's offset API takes minutes
            let datetime: DateTime<FixedOffset> = timestamp.try_into()?;
            // chrono's FixedOffset takes seconds ----------v
            let expected_offset = offset_east(-5 * 60 * 60);
            let naive_datetime = NaiveDate::from_ymd_opt(2021, 4, 6)
                .unwrap()
                .and_hms_opt(10, 15, 0)
                .unwrap()
                .with_nanosecond(449000000)
                .unwrap();
            let expected_datetime = expected_offset
                .from_local_datetime(&naive_datetime)
                .unwrap();
            assert_eq!(datetime, expected_datetime);
            Ok(())
        }

        #[test]
        fn test_fixed_offset_datetime_to_timestamp_offset_roundtrip() {
            let offsets_minutes: &[i32] = &[0, 330, -330, 60, -60, 720, -720, 1, -1];
            for &offset_min in offsets_minutes {
                let offset = FixedOffset::east_opt(offset_min * 60).unwrap();
                let dt = NaiveDate::from_ymd_opt(2024, 6, 15)
                    .unwrap()
                    .and_hms_opt(12, 30, 45)
                    .unwrap();
                let fixed_dt = offset.from_local_datetime(&dt).unwrap();
                let timestamp: Timestamp = fixed_dt.into();
                assert_eq!(
                    timestamp.offset(),
                    Some(offset_min),
                    "offset roundtrip failed for {offset_min} minutes"
                );
            }
        }

        #[test]
        fn test_timestamp_try_into_datetime_fixedoffset_error() -> IonResult<()> {
            let timestamp = TimestampBuilder::with_ymd(2021, 1, 1)
                .with_hms(0, 0, 0)
                .build()?;
            //     ^---- This timestamp has an unknown offset, so we cannot convert it into a DateTime<FixedOffset>
            let result: IonResult<DateTime<FixedOffset>> = timestamp.try_into();
            assert!(result.is_err());
            Ok(())
        }
    }
}
