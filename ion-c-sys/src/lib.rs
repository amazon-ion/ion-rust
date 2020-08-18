// Copyright Amazon.com, Inc. or its affiliates.

//! Provides basic bindings for [Ion C](https://github.com/amzn/ion-c)
//!
//! These bindings are created with `bindgen` and are considerably low-level.
//!
//! ## Examples
//! Using `ion-c-sys` directly can be a pretty verbose affair, and requires checking the
//! error code for most calls.  This crate provides the [`result`](result/index.html)
//! module to make it easier to integrate with `std::result::Result` with respect
//! to the `iERR` that Ion C functions generally return.  Specifically, any low-level
//! IonC function that returns `iERR` should be called with the [`ionc!`][ionc-call] macro
//! to facilitate `Result<(), IonCError>` conversion.
//!
//! This library provides smart pointers over the low-level reader/writer pointers, and should
//! generally be used, especially with `Result` handling code.  These types provide some facade
//! over Ion C, but only for the most generally used APIs. See:
//!
//! * [IonCReaderHandle][reader-handle]
//! * [IonCWriterHandle][writer-handle]
//!
//! [ionc-call]: macro.ionc.html
//! [reader-handle]: reader/struct.IonCReaderHandle.html
//! [writer-handle]: writer/struct.IonCWriterHandle.html
//!
//! ### Ion Reader
//! Here is an end-to-end example of reading some Ion data.
//!
//! ```
//! # use std::ptr;
//! # use std::slice;
//! # use std::str;
//! # use std::convert::TryFrom;
//! # use ion_c_sys::*;
//! # use ion_c_sys::reader::*;
//! # use ion_c_sys::result::*;
//! # fn main() -> IonCResult<()> {
//! let mut reader = IonCReaderHandle::try_from("{a:2}")?;
//!
//! // step to the struct
//! assert_eq!(ION_TYPE_STRUCT, reader.next()?);
//! // step into the struct
//! reader.step_in()?;
//! // step to the field
//! assert_eq!(ION_TYPE_INT, reader.next()?);
//! // retrieve the field name
//! assert_eq!("a", reader.get_field_name()?.as_str());
//! // read the integer value
//! assert_eq!(2, reader.read_i64()?);
//! // step to the end of the struct
//! assert_eq!(ION_TYPE_EOF, reader.next()?);
//! // step out of the struct
//! reader.step_out()?;
//! // step to the end of the stream
//! assert_eq!(ION_TYPE_EOF, reader.next()?);
//!
//! # Ok(())
//! # }
//! ```
//!
//! ### Ion Writer
//! Here is an end-to-end example of writing some Ion data.
//!
//! ```
//! # use std::ptr;
//! # use std::convert::TryInto;
//! # use ion_c_sys::*;
//! # use ion_c_sys::result::*;
//! # use ion_c_sys::writer::*;
//! # fn main() -> IonCResult<()> {
//! // output buffer
//! let mut buf: Vec<u8> = vec![0; 128];
//! let len = {
//!     let mut writer = IonCWriterHandle::new_buf_mode(buf.as_mut(), WriterMode::Binary)?;
//!     // start a list
//!     writer.start_container(ION_TYPE_LIST)?;
//!     // write some integers
//!     for n in 0..4 {
//!         writer.write_i64(n * 2)?;
//!     }
//!     // end the list
//!     writer.finish_container()?;
//!     // start a struct
//!     writer.start_container(ION_TYPE_STRUCT)?;
//!     {
//!         // write a string
//!         writer.field("name").annotations(&["version"]).write_string("💩")?;
//!     }
//!     // end the struct
//!     writer.finish_container()?;
//!     // finish writing
//!     writer.finish()?
//! };
//!
//! // make sure the bytes match what we expect
//! let expected: &[u8] = &[
//!     0xE0, 0x01, 0x00, 0xEA,         // IVM
//!     0xB7,                           // LIST size 7
//!     0x20,                           // INT 0
//!     0x21, 0x02,                     // INT 2
//!     0x21, 0x04,                     // INT 4
//!     0x21, 0x06,                     // INT 6
//!     0xD9,                           // STRUCT size 8
//!     0x84,                           // field "name" (sid 4)
//!     0xE7, 0x81, 0x85,               // annotation "version" (sid 5)
//!     0x84, 0xF0, 0x9F, 0x92, 0xA9,   // STRING 💩
//! ];
//! assert_eq!(expected.len(), len);
//! assert_eq!(expected, &buf[0..len]);
//!
//! # Ok(())
//! # }
//! ```

#![allow(non_upper_case_globals)]
#![allow(non_camel_case_types)]
#![allow(non_snake_case)]

pub mod decimal;
pub mod int;
pub mod reader;
pub mod result;
pub mod string;
pub mod timestamp;
pub mod writer;

include!(concat!(env!("OUT_DIR"), "/ionc_bindings.rs"));

use crate::decimal::IonDecimalPtr;
use crate::int::IonIntPtr;
use crate::result::*;
use crate::timestamp::Mantissa::*;
use crate::timestamp::TSOffsetKind::*;
use crate::timestamp::TSPrecision::*;
use crate::timestamp::{IonDateTime, Mantissa, TSOffsetKind, TS_MAX_MANTISSA_DIGITS};

use std::cmp::min;
use std::convert::TryInto;
use std::marker::PhantomData;
use std::ptr;
use std::str::Utf8Error;
use std::{slice, str};

use bigdecimal::{BigDecimal, ToPrimitive, Zero};
use chrono::offset::FixedOffset;
use chrono::{Datelike, LocalResult, TimeZone, Timelike};
use num_bigint::{BigInt, Sign};
use paste::paste;

#[cfg(test)]
use rstest_reuse;

impl ION_INT {
    /// Constructs a `BigInt` from this `ION_INT`.
    ///
    /// Note that since `BigInt` does not have a ***view*** into its digits,
    /// this method will make an intermediate copy as the big-endian encoded
    /// byte vector that will then be stored into this `ION_INT`
    pub fn try_assign_bigint(&mut self, src: &BigInt) -> IonCResult<()> {
        let (sign, mut raw_mag) = src.to_bytes_be();
        let is_neg = match sign {
            Sign::Minus => 1,
            _ => 0,
        };

        ionc!(ion_int_from_abs_bytes(
            &mut *self,
            raw_mag.as_mut_ptr(),
            raw_mag.len().try_into()?,
            is_neg
        ))?;

        Ok(())
    }

    /// Constructs a `BigInt` from this `ION_INT`.
    pub fn try_to_bigint(&self) -> IonCResult<BigInt> {
        if self._digits.is_null() {
            return Err(IonCError::from(ion_error_code_IERR_NULL_VALUE));
        }
        if self._len < 0 {
            return Err(IonCError::from(ion_error_code_IERR_INVALID_ARG));
        }
        if self._signum < -1 || self._signum > 1 {
            return Err(IonCError::from(ion_error_code_IERR_INVALID_ARG));
        }
        let src_digits = unsafe { slice::from_raw_parts(self._digits, self._len.try_into()?) };

        // figure out how many BigInt digits we need keeping in mind that
        // ION_INT is base 2**31, and BigInt is base 2**32.
        const ION_INT_BITS: u64 = 31;
        const BIGINT_BITS: u64 = 32;
        const ION_INT_DIGIT_MASK: u64 = 0x7FFF_FFFF;
        let tgt_len = (((self._len as u64) * ION_INT_BITS) / BIGINT_BITS) + 1;
        let mut digits = vec![0u32; tgt_len.try_into()?];

        // total bits written
        let mut bits_written = 0u64;
        // note that we go from back to front for ION_INT as it is big-endian
        // but BigInt is little-endian
        for src_digit in src_digits.iter().rev() {
            // get the source digit to deposit into the target digit(s)
            let src_digit = (*src_digit as u64) & ION_INT_DIGIT_MASK;
            // which target digit are we working on
            let tgt_idx = (bits_written >> 5) as usize;
            // how many bits are used in the current target digit
            let filled_bits = bits_written & 0x1F;
            // how many bits we can fit in the current target digit
            let avail_bits = BIGINT_BITS - filled_bits;
            // how many source bits have to go into the next target digit
            let rem_bits = ION_INT_BITS - min(ION_INT_BITS, avail_bits);

            // push the low order bits of the source into the available high order bits of the target
            let old_tgt_digit = digits[tgt_idx];
            let high_bit_mask = (src_digit << filled_bits) as u32;
            let new_tgt_digit = old_tgt_digit | high_bit_mask;
            digits[tgt_idx] = new_tgt_digit;

            if tgt_idx + 1 < digits.len() && rem_bits > 0 {
                // push the remaining high order bits into the low order bits of the next target digit
                let next_idx = tgt_idx + 1;
                let shift_bits = ION_INT_BITS - rem_bits;
                let next_tgt_digit = (src_digit >> shift_bits) as u32;
                digits[next_idx] = next_tgt_digit;
            }

            bits_written += ION_INT_BITS as u64;
        }

        const SIGN_TABLE: &[Sign] = &[Sign::Minus, Sign::NoSign, Sign::Plus];
        Ok(BigInt::new(SIGN_TABLE[(self._signum + 1) as usize], digits))
    }
}

#[cfg(test)]
mod test_bigint {
    use crate::int::*;
    use crate::result::*;
    use crate::*;

    use rstest::rstest;
    use rstest_reuse::{self, *};

    use num_bigint::BigInt;
    use num_bigint::Sign::{self, *};

    // TODO consider some kind of fuzz/property testing for this

    #[template]
    #[rstest(
        lit,
        sign,
        case::zero("0", NoSign),
        case::pos_31_bit("1576217826", Plus),
        case::neg_31_bit("-1135682218", Minus),
        case::pos_62_bit("4044881356853627201", Plus),
        case::neg_62_bit("-3912230224800585615", Minus),
        case::pos_80_bit("739079489563988370954567", Plus),
        case::neg_80_bit("-1086195751445330490038795", Minus),
        case::pos_256_bit(
            "137867910096739512996847672171101012368076859213341045932878406344693462874820",
            Plus,
        ),
        case::neg_256_bit(
            "-172272298565065214306566076919200322665607032158922187439565911507697602517448",
            Minus,
        ),
        case::pos_280_bit(
            "1757357796823956205198798709416201514711937158830789249081025568737706527211427788829",
            Plus,
        ),
        case::neg_280_bit(
            "-1075268761612498909802747877455511969232059561308078408290306546278351574885791689247",
            Minus,
        )
    )]
    fn bigint(lit: &str, sign: Sign) {}

    #[apply(bigint)]
    fn try_assign_bigint(lit: &str, sign: Sign) -> IonCResult<()> {
        let big_val = BigInt::parse_bytes(lit.as_bytes(), 10).unwrap();
        let mut ion_val = IonIntPtr::try_from_bigint(&big_val)?;

        let mut buf = vec![0u8; 512];
        let mut len = 0;
        ionc!(ion_int_to_char(
            ion_val.as_mut_ptr(),
            buf.as_mut_ptr(),
            buf.len().try_into()?,
            &mut len
        ))?;

        let expected_signum = match sign {
            Minus => -1,
            NoSign => 0,
            Plus => 1,
        };
        let mut actual_signum = 0;
        ionc!(ion_int_signum(ion_val.as_mut_ptr(), &mut actual_signum))?;
        assert_eq!(expected_signum, actual_signum);
        assert_eq!(lit.as_bytes(), &buf[0..len.try_into()?]);

        Ok(())
    }

    #[apply(bigint)]
    fn try_to_bigint(lit: &str, sign: Sign) -> IonCResult<()> {
        let mut ion_val = IonIntPtr::try_new()?;

        let mut ion_str = ION_STRING::try_from_str(lit)?;
        ionc!(ion_int_from_string(ion_val.as_mut_ptr(), &mut ion_str))?;

        let big_val = ion_val.try_to_bigint()?;
        assert_eq!(sign, big_val.sign());
        assert_eq!(lit, big_val.to_string().as_str());

        Ok(())
    }
}

/// Creates an operating context for decNum with maximum ranges primarily for conversions
/// between `ION_DECIMAL` and `BigDecimal`.
///
/// This range is still below the capabilities of `BigDecimal`
#[inline]
fn make_context() -> decContext {
    let mut ctx = decContext::default();
    unsafe { decContextDefault(&mut ctx, DEC_INIT_DECQUAD as i32) };
    ctx.digits = DEC_MAX_DIGITS as i32;
    ctx.emax = DEC_MAX_EMAX as i32;
    ctx.emin = DEC_MIN_EMIN as i32;
    // make sure we don't pad decQuads
    ctx.clamp = 0;

    ctx
}

impl ION_DECIMAL {
    /// Assigns a `BigDecimal` into this `ION_DECIMAL`.
    pub fn try_assign_bigdecimal(&mut self, value: &BigDecimal) -> IonCResult<()> {
        let digits = value.digits();

        // FIXME amzn/ion-rust#80 - this breaks encapsulation
        ionc!(ion_decimal_free(self))?;
        if digits > (DECQUAD_Pmax as u64) {
            self.type_ = ION_DECIMAL_TYPE_ION_DECIMAL_TYPE_NUMBER;
            // need to allocate the number field
            ionc!(_ion_decimal_number_alloc(
                ptr::null_mut(),
                digits.try_into()?,
                &mut self.value.num_value,
            ))?;
        } else {
            self.type_ = ION_DECIMAL_TYPE_ION_DECIMAL_TYPE_QUAD;
        }
        ionc!(ion_decimal_zero(self))?;

        let mut ctx = make_context();
        let (coefficient, scale) = value.as_bigint_and_exponent();

        // set the coefficient
        let mut ion_coefficient = IonIntPtr::try_from_bigint(&coefficient)?;
        ionc!(ion_decimal_from_ion_int(
            self,
            &mut ctx,
            ion_coefficient.as_mut_ptr()
        ))?;

        // scale the value
        let mut dec_scale = IonDecimalPtr::try_from_i32((-scale).try_into()?)?;
        ionc!(ion_decimal_scaleb(
            self,
            self,
            dec_scale.as_mut_ptr(),
            &mut ctx
        ))?;

        match unsafe { decContextGetStatus(&mut ctx) } {
            0 => Ok(()),
            // FIXME amzn/ion-rust#79 - we need to fix decNumber support.
            DEC_Invalid_context => Err(IonCError::with_additional(
                ion_error_code_IERR_INVALID_STATE,
                "DecNumber Not Supported",
            )),
            _ => Err(IonCError::from(ion_error_code_IERR_INTERNAL_ERROR)),
        }
    }

    /// Converts this `ION_DECIMAL` to a `BigDecimal`.
    ///
    /// Special decimal values such as NaN and infinity are not supported for conversion.
    ///
    /// This implementation borrows mutably, to avoid a copy of the underlying
    /// decimal implementation, but does not change the value.
    ///
    /// Specifically, this code scales from/to the exponent the value to extract the coefficient.
    pub fn try_to_bigdecimal(&mut self) -> IonCResult<BigDecimal> {
        // special values are not supported
        let special =
            unsafe { ion_decimal_is_nan(self) } | unsafe { ion_decimal_is_infinite(self) };
        if special != 0 {
            return Err(IonCError::from(ion_error_code_IERR_INVALID_ARG));
        }

        // get some information about the decimal
        let negative = unsafe { ion_decimal_is_negative(self) } != 0;
        let exponent = unsafe { ion_decimal_get_exponent(self) };
        let mut ctx = make_context();

        // scale the value to an integer
        let mut scale_amount = IonDecimalPtr::try_from_i32(-exponent)?;
        ionc!(ion_decimal_scaleb(
            self,
            self,
            scale_amount.as_mut_ptr(),
            &mut ctx
        ))?;
        let mut ion_coefficient = IonIntPtr::try_new()?;
        ionc!(ion_decimal_to_ion_int(
            self,
            &mut ctx,
            ion_coefficient.as_mut_ptr()
        ))?;

        // scale back the value
        ionc!(ion_decimal_from_int32(scale_amount.as_mut_ptr(), exponent))?;
        ionc!(ion_decimal_scaleb(
            self,
            self,
            scale_amount.as_mut_ptr(),
            &mut ctx
        ))?;

        // make the decimal -- note scale is negative exponent
        let mut coefficient = ion_coefficient.try_to_bigint()?;
        if negative {
            coefficient *= -1;
        }
        Ok(BigDecimal::new(coefficient, -exponent as i64))
    }
}

#[cfg(test)]
mod test_bigdecimal {
    // because of test table re-use we sometimes end up with unused variables
    #![allow(unused_variables)]

    use crate::decimal::*;
    use crate::result::*;
    use crate::*;

    use rstest::rstest;
    use rstest_reuse::{self, *};

    use std::ffi::CString;

    use bigdecimal::BigDecimal;
    use num_bigint::BigInt;

    // TODO consider some kind of fuzz/property testing for this

    #[template]
    #[rstest(
        d_lit, c_lit, exponent,
        case::zero("0E0", "0", 0),
        case::zero_p1_en8("0E-8", "0", -8),
        case::p8_en9(
            "0.060231219",
            "60231219",
            -9
        ),
        case::p8_e7(
            "2.7851880E+14",
            "27851880",
            7
        ),
        case::p10_en32(
            "8.960115983E-23",
            "8960115983",
            -32
        ),
        case::p10_e33(
            "9.020634788E+42",
            "9020634788",
            33
        ),
        case::p28_en200(
            "6.262354479103128947759990609E-173",
            "6262354479103128947759990609",
            -200
        ),
        case::p28_e256(
            "9.486968202420944975464220485E+283",
            "9486968202420944975464220485",
            256
        ),
        case::p30_en80(
            "1.95671174876514167707949046494E-51",
            "195671174876514167707949046494",
            -80
        ),
        case::p30_e85(
            "6.50276908237082165030429776240E+114",
            "650276908237082165030429776240",
            85
        ),
        case::p32_en2500(
            "4.1111441587902074230255158471962E-2469",
            "41111441587902074230255158471962",
            -2500
        ),
        case::p32_e2000(
            "2.9557665423302931520009385209142E+2031",
            "29557665423302931520009385209142",
            2000
        ),
        case::p34_en6100(
            "7.550261799183309871071383313529625E-6067",
            "7550261799183309871071383313529625",
            -6100
        ),
        case::p34_e6110(
            "6.385180511995820599706505142429397E+6143",
            "6385180511995820599706505142429397",
            6110
        ),
        case::p35_en5500(
            "5.7516904150035820771702738217456585E-5466",
            "57516904150035820771702738217456585",
            -5500
        ),
        case::p35_e4500(
            "7.7008733801862767698341856677462573E+4534",
            "77008733801862767698341856677462573",
            4500
        ),
        case::p37_en5000(
            "4.623874712756984956766514373293465450E-4964",
            "4623874712756984956766514373293465450",
            -5000
        ),
        case::p37_e6000(
            "9.970304500552494301196940956407522192E+6036",
            "9970304500552494301196940956407522192",
            6000
        ),
        case::p38_en110(
            "5.9025723530133359201873978774331457987E-73",
            "59025723530133359201873978774331457987",
            -110
        ),
        case::p38_e120(
            "1.9141033431585215614236049655094977149E+157",
            "19141033431585215614236049655094977149",
            120
        ),
        case::p80_en100(
            "4.4818084368071883463971983799827359329516552715395136426901699171061657459862827E-21",
            "44818084368071883463971983799827359329516552715395136426901699171061657459862827",
            -100
        ),
        case::p80_e100(
            "1.1050923646496935500303958597719760541602476378798913802309108901778807590265278E+279",
            "11050923646496935500303958597719760541602476378798913802309108901778807590265278",
            200
        ),
        case::p90_en7500(
            "4.29926815238794553771012929776377470059985366468509955296419658127318674237363065734779169E-7411",
            "429926815238794553771012929776377470059985366468509955296419658127318674237363065734779169",
            -7500
        ),
        case::p95_e8900(
            "7.2528362571947544011741381371920928164665526193613163529470013995124245887784236337589645597617E+8994",
            "72528362571947544011741381371920928164665526193613163529470013995124245887784236337589645597617",
            8900
        ),
    )]
    fn bigdecimal(d_lit: &str, c_lit: &str, exponent: i32) {}

    #[apply(bigdecimal)]
    fn try_assign_bigdecimal(d_lit: &str, c_lit: &str, exponent: i32) -> IonCResult<()> {
        let big_val = BigDecimal::parse_bytes(d_lit.as_bytes(), 10).unwrap();
        match IonDecimalPtr::try_from_bigdecimal(&big_val) {
            Ok(mut ion_val) => {
                let actual_exponent = unsafe { ion_decimal_get_exponent(ion_val.as_mut_ptr()) };

                // test the string representations--not ideal, but easier than extracting coefficient
                let mut buf = vec![0u8; 128usize];
                ionc!(ion_decimal_to_string(
                    ion_val.as_mut_ptr(),
                    buf.as_mut_ptr() as *mut i8
                ))?;
                let len = unsafe { strlen(buf.as_ptr() as *const i8) };
                assert_eq!(
                    d_lit.replace("E", "d"),
                    str::from_utf8(&buf[0..len.try_into()?]).unwrap(),
                    "Testing string serialization from ION_DECIMAL"
                );
                assert_eq!(exponent, actual_exponent, "Testing exponents");
            }
            Err(e) => match e.code {
                ion_error_code_IERR_INVALID_STATE => match e.additional {
                    "DecNumber Not Supported" => {
                        println!("Ignoring amzn/ion-rust#79 for {}", d_lit)
                    }
                    _ => assert!(false, "Unexpected error {:?}", e),
                },
                _ => assert!(false, "Unexpected error: {:?}", e),
            },
        }

        Ok(())
    }

    #[apply(bigdecimal)]
    fn try_to_bigdecimal(d_lit: &str, c_lit: &str, exponent: i32) -> IonCResult<()> {
        let cstring = CString::new(d_lit).unwrap();
        let mut ctx = make_context();
        let mut ion_val = IonDecimalPtr::try_from_existing(ION_DECIMAL::default())?;
        ionc!(ion_decimal_from_string(
            ion_val.as_mut_ptr(),
            cstring.as_ptr(),
            &mut ctx
        ))?;

        let big_val = ion_val.try_to_bigdecimal()?;
        assert_eq!(
            big_val,
            ion_val.try_to_bigdecimal()?,
            "Make sure conversion is effectively immutable"
        );

        // we test against the coefficient and exponent because the string representation
        // is not stable between decNum and BigDecimal
        let expected_coefficient = BigInt::parse_bytes(c_lit.as_bytes(), 10).unwrap();
        let (actual_coefficient, scale) = big_val.as_bigint_and_exponent();
        assert_eq!(
            expected_coefficient, actual_coefficient,
            "Testing coefficents"
        );
        assert_eq!(exponent, (-scale).try_into()?, "Testing exponents");

        Ok(())
    }
}

const SEC_IN_MINS: i32 = 60;
const NS_IN_SEC: u32 = 1_000_000_000;

impl ION_TIMESTAMP {
    // Note that although we have `IonDateTime` as a wrapper--the logic to convert
    // to/from `ION_TIMESTAMP` is kept here to avoid the dependency on `ION_TIMESTAMP`
    // in `IonDateTime` and to keep it consistent to the bigint and decimal conversions.

    /// Converts the given `IonDateTime` into this `ION_TIMESTAMP`.
    pub fn try_assign_from_iondt(&mut self, ion_dt: &IonDateTime) -> IonCResult<()> {
        let dt = ion_dt.as_datetime();
        let prec = ion_dt.precision();
        let offset_kind = ion_dt.offset_kind();

        // clear everything out
        self.month = 1;
        self.day = 1;
        self.hours = 0;
        self.minutes = 0;
        self.seconds = 0;
        unsafe {
            decQuadZero(&mut self.fraction);
        }
        self.tz_offset = 0;
        self.precision = 0;

        // fill in the timestamp
        self.year = dt.year().try_into()?;
        if *prec >= Month {
            self.month = dt.month().try_into()?;
            if *prec >= Day {
                self.day = dt.day().try_into()?;
                if *prec >= Minute {
                    self.hours = dt.hour().try_into()?;
                    self.minutes = dt.minute().try_into()?;
                    if *prec >= Second {
                        self.seconds = dt.second().try_into()?;
                        if let Fractional(mantissa) = prec {
                            self.try_assign_mantissa(dt, mantissa)?;
                        }
                    }
                }
            }
        }

        // set the precision
        self.precision = match prec {
            Year => ION_TS_YEAR,
            Month => ION_TS_MONTH,
            Day => ION_TS_DAY,
            Minute => ION_TS_MIN,
            Second => ION_TS_SEC,
            Fractional(_) => ION_TS_FRAC,
        } as u8;

        // set the offset
        match offset_kind {
            KnownOffset => {
                let offset_minutes = dt.offset().local_minus_utc() / SEC_IN_MINS;
                ionc!(ion_timestamp_set_local_offset(self, offset_minutes))?;
            }
            UnknownOffset => {
                ionc!(ion_timestamp_unset_local_offset(self))?;
            }
        }

        Ok(())
    }

    /// Assigns the fractional component.
    fn try_assign_mantissa<T>(&mut self, dt: &T, mantissa: &Mantissa) -> IonCResult<()>
    where
        T: Timelike,
    {
        let mut ctx = make_context();
        match mantissa {
            Digits(digits) => {
                unsafe {
                    let nanos = dt.nanosecond();
                    decQuadFromUInt32(&mut self.fraction, nanos);

                    // shift over to set the precision to the number of digits
                    let mut shift = decQuad::default();
                    decQuadFromInt32(
                        &mut shift,
                        (*digits as i32) - (TS_MAX_MANTISSA_DIGITS as i32),
                    );
                    decQuadShift(&mut self.fraction, &self.fraction, &shift, &mut ctx);

                    // scale the value to be a fraction
                    let mut scale = decQuad::default();
                    decQuadFromInt32(&mut scale, -(*digits as i32));
                    decQuadScaleB(&mut self.fraction, &self.fraction, &scale, &mut ctx);
                }
            }
            Fraction(frac) => {
                let ion_frac = IonDecimalPtr::try_from_bigdecimal(frac)?;
                // we don't support converting from a decimal that cannot fit in a decQuad
                if ion_frac.type_ != ION_DECIMAL_TYPE_ION_DECIMAL_TYPE_QUAD {
                    return Err(IonCError::with_additional(
                        ion_error_code_IERR_INVALID_TIMESTAMP,
                        "Precision exceeds decQuad for Timestamp",
                    ));
                }
                unsafe {
                    self.fraction = (*ion_frac).value.quad_value;
                }
            }
        }

        Ok(())
    }

    /// Converts this `ION_TIMESTAMP` into a `IonDateTime`.
    ///
    /// Note that this borrows mutably, because all of the underlying
    /// `ion_timestamp_*` functions require a mutable pointer, but this operation
    /// does not actually change the value.
    pub fn try_to_iondt(&mut self) -> IonCResult<IonDateTime> {
        let mut prec = 0;
        ionc!(ion_timestamp_get_precision(self, &mut prec))?;
        // XXX all of our constants are small u32--so cast over to work with them
        let prec = prec as u32;

        // we need an offset to construct the date with chrono
        let mut offset_minutes = 0;
        let mut has_offset = 0;

        if prec >= ION_TS_MIN {
            ionc!(ion_timestamp_has_local_offset(self, &mut has_offset))?;
            if has_offset != 0 {
                ionc!(ion_timestamp_get_local_offset(self, &mut offset_minutes))?;
            }
        }
        let offset_seconds = (offset_minutes as i32) * SEC_IN_MINS;
        let tz = FixedOffset::east_opt(offset_seconds)
            .ok_or(IonCError::from(ion_error_code_IERR_INVALID_STATE))?;
        let ts_offset = if has_offset != 0 {
            TSOffsetKind::KnownOffset
        } else {
            TSOffsetKind::UnknownOffset
        };

        let day = if prec >= ION_TS_DAY { self.day } else { 1 };
        let month = if prec >= ION_TS_MONTH { self.month } else { 1 };
        match tz.ymd_opt(self.year as i32, month as u32, day as u32) {
            LocalResult::Single(date) => {
                let mut hours = 0;
                let mut minutes = 0;
                let mut seconds = 0;
                if prec >= ION_TS_MIN {
                    hours = self.hours;
                    minutes = self.minutes;
                    seconds = self.seconds;
                }

                // convert fractional seconds to nanoseconds
                let frac_seconds = if prec >= ION_TS_FRAC {
                    IonDecimalPtr::try_from_decquad(self.fraction)?.try_to_bigdecimal()?
                } else {
                    BigDecimal::zero()
                };
                if frac_seconds < BigDecimal::zero() || frac_seconds >= BigDecimal::from(1) {
                    return Err(IonCError::from(ion_error_code_IERR_INVALID_STATE));
                }
                let nanos = (&frac_seconds * BigDecimal::from(NS_IN_SEC))
                    .abs()
                    .to_u32()
                    .unwrap();

                let dt = date
                    .and_hms_nano_opt(hours as u32, minutes as u32, seconds as u32, nanos)
                    .ok_or(IonCError::with_additional(
                        ion_error_code_IERR_INVALID_TIMESTAMP,
                        "Could not create DateTime",
                    ))?;

                let ts_prec = match prec {
                    ION_TS_YEAR => Year,
                    ION_TS_MONTH => Month,
                    ION_TS_DAY => Day,
                    ION_TS_MIN => Minute,
                    ION_TS_SEC => Second,
                    ION_TS_FRAC => {
                        let (_, exponent) = frac_seconds.as_bigint_and_exponent();
                        let mantissa = if exponent <= TS_MAX_MANTISSA_DIGITS {
                            Digits(exponent as u32)
                        } else {
                            // preserve the fractional seconds in the precision.
                            Fraction(frac_seconds)
                        };
                        Fractional(mantissa)
                    }
                    _ => {
                        return Err(IonCError::with_additional(
                            ion_error_code_IERR_INVALID_TIMESTAMP,
                            "Invalid ION_TIMESTAMP precision",
                        ))
                    }
                };

                Ok(IonDateTime::new(dt, ts_prec, ts_offset))
            }
            _ => Err(IonCError::with_additional(
                ion_error_code_IERR_INVALID_TIMESTAMP,
                "Could not create Date",
            )),
        }
    }
}

#[cfg(test)]
mod test_timestamp {
    use crate::result::*;
    use crate::timestamp::*;
    use crate::*;

    use rstest::rstest;
    use rstest_reuse::{self, *};

    use std::ffi::CString;
    use std::str;

    use chrono::DateTime;

    fn frac(lit: &str) -> Mantissa {
        Fraction(BigDecimal::parse_bytes(lit.as_bytes(), 10).unwrap())
    }

    #[template]
    #[rstest(
        ion_lit,
        iso_lit,
        precision,
        offset_kind,
        case::ts_2020("2020T", "2020-01-01T00:00:00Z", Year, UnknownOffset),
        case::ts_1901_04("1901-04T", "1901-04-01T00:00:00Z", Month, UnknownOffset),
        case::ts_2014_10_10("2014-10-10", "2014-10-10T00:00:00Z", Day, UnknownOffset),
        case::ts_2017_07_07T01_20(
            "2017-07-07T01:20-00:00",
            "2017-07-07T01:20:00Z",
            Minute,
            UnknownOffset,
        ),
        case::ts_2018_06_30T03_25_p07_30(
            "2018-06-30T03:25+07:30",
            "2018-06-30T03:25:00+07:30",
            Minute,
            KnownOffset,
        ),
        case::ts_2019_04_30T03_25_32(
            "2019-04-30T03:25:32-00:00",
            "2019-04-30T03:25:32Z",
            Second,
            UnknownOffset,
        ),
        case::ts_2016_03_30T03_25_32_n00_00_same_as_zulu(
            "2016-03-30T03:25:32-00:00",
            "2016-03-30T03:25:32Z",
            Second,
            UnknownOffset,
        ),
        case::ts_2016_03_30T03_25_32_n08_00(
            "2016-03-30T03:25:32-08:00",
            "2016-03-30T03:25:32-08:00",
            Second,
            KnownOffset,
        ),
        case::ts_1975_02_19T12_43_55_123_n08_00(
            "1975-02-19T12:43:55.123-08:00",
            "1975-02-19T12:43:55.123-08:00",
            Fractional(Digits(3)),
            KnownOffset,
        ),
        case::ts_1975_02_19T12_43_55_001_n08_00(
            "1975-02-19T12:43:55.001-08:00",
            "1975-02-19T12:43:55.001-08:00",
            Fractional(Digits(3)),
            KnownOffset,
        ),
        case::ts_1975_02_19T12_43_55_12345_n08_00(
            "1975-02-19T12:43:55.12345-08:00",
            "1975-02-19T12:43:55.12345-08:00",
            Fractional(Digits(5)),
            KnownOffset,
        ),
        case::ts_1975_02_19T12_43_55_00005_n08_00(
            "1975-02-19T12:43:55.00005-08:00",
            "1975-02-19T12:43:55.00005-08:00",
            Fractional(Digits(5)),
            KnownOffset,
        ),
        case::ts_1975_02_19T12_43_55_012345_n08_00(
            "1975-02-19T12:43:55.012345-08:00",
            "1975-02-19T12:43:55.012345-08:00",
            Fractional(Digits(6)),
            KnownOffset,
        ),
        case::ts_1975_02_19T12_43_55_000056_n08_00(
            "1975-02-19T12:43:55.000056-08:00",
            "1975-02-19T12:43:55.000056-08:00",
            Fractional(Digits(6)),
            KnownOffset,
        ),
        case::ts_1974_01_20T12_43_55_123456789_n08_00(
            "1974-01-20T12:43:55.123456789-08:00",
            "1974-01-20T12:43:55.123456789-08:00",
            Fractional(Digits(9)),
            KnownOffset,
        ),
        case::ts_1974_01_20T12_43_55_000056789_n08_00(
            "1974-01-20T12:43:55.000056789-08:00",
            "1974-01-20T12:43:55.000056789-08:00",
            Fractional(Digits(9)),
            KnownOffset,
        ),
        case::ts_1973_12_25T12_43_55_123456789123456789_n08_00_truncation(
            "1973-12-25T12:43:55.123456789123456789-08:00",
            "1973-12-25T12:43:55.123456789-08:00",
            Fractional(frac("0.123456789123456789")),
            KnownOffset,
        )
    )]
    fn timestamp(ion_lit: &str, iso_lit: &str, precision: TSPrecision, offset_kind: TSOffsetKind) {}

    #[apply(timestamp)]
    fn assign_from_datetime(
        ion_lit: &str,
        iso_lit: &str,
        precision: TSPrecision,
        offset_kind: TSOffsetKind,
    ) -> IonCResult<()> {
        // assign into an ION_TIMESTAMP
        let dt = DateTime::parse_from_rfc3339(iso_lit).unwrap();
        let ion_dt = IonDateTime::try_new(dt, precision, offset_kind)?;
        let mut ion_timestamp = ION_TIMESTAMP::default();
        ion_timestamp.try_assign_from_iondt(&ion_dt)?;

        // serialize
        let mut ctx = make_context();
        let mut buf = vec![0u8; 128usize];
        let mut read = 0;
        ionc!(ion_timestamp_to_string(
            &mut ion_timestamp,
            buf.as_mut_ptr() as *mut i8,
            buf.len().try_into()?,
            &mut read,
            &mut ctx
        ))?;
        assert_eq!(
            ion_lit,
            str::from_utf8(&buf[0..read.try_into()?])?,
            "Compare timestamp text serialization"
        );

        Ok(())
    }

    #[apply(timestamp)]
    fn try_to_datetime(
        ion_lit: &str,
        iso_lit: &str,
        precision: TSPrecision,
        offset_kind: TSOffsetKind,
    ) -> IonCResult<()> {
        let c_ion_lit_owned = CString::new(ion_lit).unwrap();
        let c_ion_lit = c_ion_lit_owned.as_bytes_with_nul();
        // construct ION_TIMESTAMP from test vector
        let mut ion_timestamp = ION_TIMESTAMP::default();
        let mut read = 0;
        let mut ctx = make_context();
        ionc!(ion_timestamp_parse(
            &mut ion_timestamp,
            c_ion_lit.as_ptr() as *mut i8,
            c_ion_lit.len().try_into()?,
            &mut read,
            &mut ctx,
        ))?;
        assert_eq!(
            ion_lit.len(),
            read.try_into()?,
            "Test that we parsed the entire Ion timestamp literal"
        );

        let expected_dt = DateTime::parse_from_rfc3339(iso_lit).unwrap();
        let ion_dt = ion_timestamp.try_to_iondt()?;
        assert_eq!(
            &expected_dt,
            ion_dt.as_datetime(),
            "Test that our converted timestamp is equivalent"
        );
        assert_eq!(
            &precision,
            ion_dt.precision(),
            "Compare timestamp precision"
        );
        assert_eq!(offset_kind, ion_dt.offset_kind(), "Compare offset kind");

        Ok(())
    }
}

impl ION_STRING {
    /// Constructs an `ION_STRING` from a `&mut str`.
    ///
    /// Note that this is effectively Ion C's `&mut str` type so lifetime is managed
    /// manually by the caller.
    ///
    /// Also note, that it is possible to violate the UTF-8 invariant of the source
    /// data, so care should be taken when using this API.
    ///
    /// ## Usage
    /// Generally, using a mutable owned source will be the safest option.
    /// ```
    /// # use ion_c_sys::ION_STRING;
    /// # use ion_c_sys::result::IonCResult;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = "Some data".to_string();
    /// let mut ion_str = ION_STRING::try_from_mut_str(buf.as_mut_str())?;
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn try_from_mut_str(src: &mut str) -> IonCResult<Self> {
        unsafe { Self::try_from_mut_bytes(src.as_bytes_mut()) }
    }

    /// Internal function to coerce an immutable slice to an `ION_STRING`.
    ///
    /// Inherently unsafe and can only be used with APIs that guarantee immutability.
    #[inline]
    fn try_from_str(src: &str) -> IonCResult<Self> {
        Ok(Self {
            value: src.as_ptr() as *mut u8,
            length: src.len().try_into()?,
        })
    }

    /// Constructs an `ION_STRING` from a `&mut [u8]`.
    ///
    /// Note that this is effectively Ion C's `&mut [u8]` type so lifetime is managed
    /// manually by the caller.
    ///
    /// ## Usage
    /// Generally, using a mutable owned source will be the safest option.
    /// ```
    /// # use ion_c_sys::ION_STRING;
    /// # use ion_c_sys::result::IonCResult;
    /// # fn main() -> IonCResult<()> {
    /// let mut buf = b"Some data".to_vec();
    /// let mut ion_str = ION_STRING::try_from_mut_bytes(buf.as_mut_slice())?;
    /// # Ok(())
    /// # }
    /// ```
    #[inline]
    pub fn try_from_mut_bytes(src: &mut [u8]) -> IonCResult<Self> {
        Ok(ION_STRING {
            value: src.as_mut_ptr(),
            length: src.len().try_into()?,
        })
    }

    /// Retrieves a UTF-8 slice view from an `ION_STRING`.
    ///
    /// When the `value` pointer is `null`, the conversion will fail:
    /// ```
    /// # use ion_c_sys::*;
    /// let ion_str = ION_STRING::default();
    /// match ion_str.try_as_str() {
    ///     Ok(_) => panic!("Cannot happen!"),
    ///     Err(e) => assert_eq!(ion_error_code_IERR_NULL_VALUE, e.code),
    /// }
    /// ```
    ///
    /// When the string is not valid UTF-8, the conversion will fail:
    /// ```
    /// # use ion_c_sys::*;
    /// let mut buf = b"\xFF".to_vec();
    /// let ion_str = ION_STRING::try_from_mut_bytes(buf.as_mut_slice()).unwrap();
    /// match ion_str.try_as_str() {
    ///     Ok(_) => panic!("Cannot happen!"),
    ///     Err(e) => assert_eq!(ion_error_code_IERR_INVALID_UTF8, e.code),
    /// }
    /// ```
    #[inline]
    pub fn try_as_str(&self) -> IonCResult<&str> {
        Ok(str::from_utf8(self.try_as_bytes()?)?)
    }

    /// Retrieves a slice view from an `ION_STRING`
    ///
    /// When the `value` pointer is `null`, the conversion will return an `IonCError`:
    /// ```
    /// # use ion_c_sys::*;
    /// let ion_str = ION_STRING::default();
    /// match ion_str.try_as_bytes() {
    ///     Ok(_) => panic!("Cannot happen!"),
    ///     Err(e) => assert_eq!(ion_error_code_IERR_NULL_VALUE, e.code),
    /// }
    /// ```
    #[inline]
    pub fn try_as_bytes<'a>(&'a self) -> IonCResult<&'a [u8]> {
        self.as_bytes(PhantomData::<&'a u8>::default())
    }

    /// Low-level conversion into an str reference tied to the given owner without UTF-8 validation
    fn as_str<'a>(&self, life: PhantomData<&'a u8>) -> IonCResult<&'a str> {
        unsafe {
            let raw_slice: &'a [u8] = self.as_bytes(life)?;
            // Better make sure this came from an Ion C call that checks this
            let str_slice = str::from_utf8_unchecked(raw_slice);
            Ok(str_slice)
        }
    }

    /// Low-level conversion into a slice associated with a given owner
    fn as_bytes<'a>(&self, _life: PhantomData<&'a u8>) -> IonCResult<&'a [u8]> {
        // note that we need to build the str slice at a very low level
        // to tie the lifetime to the reader
        if self.value.is_null() {
            Err(IonCError::from(ion_error_code_IERR_NULL_VALUE))
        } else {
            unsafe {
                let u8_slice = slice::from_raw_parts(self.value, self.length.try_into()?);
                Ok(u8_slice)
            }
        }
    }
}

/// Generates easier to use constants for `ION_TYPE`
/// These exist as C macros in `ion_types.h` that don't get translated over from `bindgen`.
///
/// Using `ion_types!(NULL)` will generate a constant of the form:
/// ```
/// # use ion_c_sys::*;
/// pub const ION_TYPE_NULL: *mut ion_type = tid_NULL_INT as *mut ion_type;
/// ```
macro_rules! ion_types {
    ( $($name:ident),* ) => {
        $(
            paste! {
                pub const [<ION_TYPE_ $name:upper>]: *mut ion_type =
                    [<tid_ $name _INT>] as *mut ion_type;
            }
        )*
    };
}

ion_types!(
    none, EOF, NULL, BOOL, INT, FLOAT, DECIMAL, TIMESTAMP, SYMBOL, STRING, CLOB, BLOB, LIST, SEXP,
    STRUCT, DATAGRAM
);
