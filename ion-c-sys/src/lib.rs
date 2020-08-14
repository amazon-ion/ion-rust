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
pub mod writer;

include!(concat!(env!("OUT_DIR"), "/ionc_bindings.rs"));

use crate::decimal::IonDecimalPtr;
use crate::int::IonIntPtr;
use crate::result::*;

use std::cmp::min;
use std::convert::TryInto;
use std::marker::PhantomData;
use std::ptr;
use std::str::Utf8Error;
use std::{slice, str};

use bigdecimal::BigDecimal;
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
        let bval = BigInt::parse_bytes(lit.as_bytes(), 10).unwrap();
        let mut ival = IonIntPtr::try_from_bigint(&bval)?;

        let mut buf = vec![0u8; 512];
        let mut len = 0;
        ionc!(ion_int_to_char(
            ival.as_mut_ptr(),
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
        ionc!(ion_int_signum(ival.as_mut_ptr(), &mut actual_signum))?;
        assert_eq!(expected_signum, actual_signum);
        assert_eq!(lit.as_bytes(), &buf[0..len.try_into()?]);

        Ok(())
    }

    #[apply(bigint)]
    fn try_to_bigint(lit: &str, sign: Sign) -> IonCResult<()> {
        let mut ival = IonIntPtr::try_new()?;

        let mut istr = ION_STRING::try_from_str(lit)?;
        ionc!(ion_int_from_string(ival.as_mut_ptr(), &mut istr))?;

        let bval = ival.try_to_bigint()?;
        assert_eq!(sign, bval.sign());
        assert_eq!(lit, bval.to_string().as_str());

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

const DEC_QUAD_DIGITS: u64 = 37;

impl ION_DECIMAL {
    /// Assigns a `BigDecimal` into this `ION_DECIMAL`.
    pub fn try_assign_bigdecimal(&mut self, value: &BigDecimal) -> IonCResult<()> {
        let digits = value.digits();

        // FIXME amzn/ion-rust#80 - this breaks encapsulation
        ionc!(ion_decimal_free(self))?;
        if digits > DEC_QUAD_DIGITS {
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
            // FIXME amzn/ion-rust#78 - we need to be more careful around the limits of decQuad.
            DEC_Inexact => Err(IonCError::from(ion_error_code_IERR_NUMERIC_OVERFLOW)),
            // FIXME amzn/ion-rust#79 - we need to fix decNumber support.
            DEC_Invalid_context => Err(IonCError::from(ion_error_code_IERR_INVALID_STATE)),
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
        let bval = BigDecimal::parse_bytes(d_lit.as_bytes(), 10).unwrap();
        match IonDecimalPtr::try_from_bigdecimal(&bval) {
            Ok(mut ival) => {
                let actual_exponent = unsafe { ion_decimal_get_exponent(ival.as_mut_ptr()) };

                // test the string representations--not ideal, but easier than extracting coefficient
                let mut buf = vec![0u8; 128usize];
                ionc!(ion_decimal_to_string(
                    ival.as_mut_ptr(),
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
                ion_error_code_IERR_NUMERIC_OVERFLOW => {
                    println!("Ignoring amzn/ion-rust#78 for {}", d_lit)
                }
                ion_error_code_IERR_INVALID_STATE => {
                    println!("Ignoring amzn/ion-rust#79 for {}", d_lit)
                }
                _ => assert!(false, "Unexpected error: {:?}", e),
            },
        }

        Ok(())
    }

    #[apply(bigdecimal)]
    fn try_to_bigdecimal(d_lit: &str, c_lit: &str, exponent: i32) -> IonCResult<()> {
        let cstring = CString::new(d_lit).unwrap();
        let mut ctx = make_context();
        let mut ival = IonDecimalPtr::try_from_existing(ION_DECIMAL::default())?;
        ionc!(ion_decimal_from_string(
            ival.as_mut_ptr(),
            cstring.as_ptr(),
            &mut ctx
        ))?;

        let bval = ival.try_to_bigdecimal()?;
        assert_eq!(
            bval,
            ival.try_to_bigdecimal()?,
            "Make sure conversion is effectively immutable"
        );

        // we test against the coefficient and exponent because the string representation
        // is not stable between decNum and BigDecimal
        let expected_coefficient = BigInt::parse_bytes(c_lit.as_bytes(), 10).unwrap();
        let (actual_coefficient, scale) = bval.as_bigint_and_exponent();
        assert_eq!(
            expected_coefficient, actual_coefficient,
            "Testing coefficents"
        );
        assert_eq!(exponent, (-scale).try_into()?, "Testing exponents");

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
