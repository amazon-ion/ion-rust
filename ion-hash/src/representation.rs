// Copyright Amazon.com, Inc. or its affiliates.

//! This file provides an extension trait [`Representation`] that is implemented
//! for Ion types found in the [`Element`] API. In the fullness of time, this
//! file should not exist as we should be using the Ion "raw" binary writer
//! instead. This implementation fills in that gap, and is focused on coverage
//! and not speed.

use std::io;

use crate::ElementHasher;
use crate::{type_qualifier::type_qualifier_symbol, Markers};
use digest::{FixedOutput, Output, Reset, Update};
use ion_rs::binary::{self, decimal::DecimalBinaryEncoder, timestamp::TimestampBinaryEncoder};
use ion_rs::types::decimal::Decimal;
use ion_rs::{
    result::IonResult,
    types::timestamp::Timestamp,
    value::{AnyInt, Element, Sequence, Struct, SymbolToken},
    IonType,
};

pub(crate) trait RepresentationEncoder<E>
where
    E: Element + ?Sized,
{
    fn update_with_representation(&mut self, elem: &E) -> IonResult<()> {
        match elem.ion_type() {
            IonType::Null | IonType::Boolean => {} // these types have no representation
            IonType::Integer => self.write_repr_integer(elem.as_any_int())?,
            IonType::Float => self.write_repr_float(elem.as_f64())?,
            IonType::Decimal => self.write_repr_decimal(elem.as_decimal())?,
            IonType::Timestamp => self.write_repr_timestamp(elem.as_timestamp())?,
            IonType::Symbol => self.write_repr_symbol(elem.as_sym())?,
            IonType::String => self.write_repr_string(elem.as_str())?,
            IonType::Clob | IonType::Blob => self.write_repr_blob(elem.as_bytes())?,
            IonType::List | IonType::SExpression => self.write_repr_seq(elem.as_sequence())?,
            IonType::Struct => self.write_repr_struct(elem.as_struct())?,
        }

        Ok(())
    }

    fn write_repr_integer(&mut self, value: Option<&AnyInt>) -> IonResult<()>;
    fn write_repr_float(&mut self, value: Option<f64>) -> IonResult<()>;
    fn write_repr_decimal(&mut self, value: Option<&Decimal>) -> IonResult<()>;
    fn write_repr_timestamp(&mut self, value: Option<&Timestamp>) -> IonResult<()>;
    fn write_repr_symbol<S>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: SymbolToken + ?Sized;
    fn write_repr_string(&mut self, value: Option<&str>) -> IonResult<()>;
    fn write_repr_blob(&mut self, value: Option<&[u8]>) -> IonResult<()>;
    fn write_repr_seq<S>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: Sequence + ?Sized;
    fn write_repr_struct<S, F>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: Struct<FieldName = F, Element = E> + ?Sized,
        F: SymbolToken + ?Sized;
}

impl<E, D> RepresentationEncoder<E> for D
where
    E: Element + ?Sized,
    D: Update + FixedOutput + Reset + Clone + Default,
{
    fn write_repr_integer(&mut self, value: Option<&AnyInt>) -> IonResult<()> {
        match value {
            Some(AnyInt::I64(v)) => match v {
                0 => {}
                _ => {
                    let magnitude = v.abs() as u64;
                    let encoded = binary::uint::encode_uint(magnitude);
                    escaping(self).update_escaping(encoded.as_bytes());
                }
            },
            Some(AnyInt::BigInt(b)) => {
                escaping(self).update_escaping(&b.magnitude().to_bytes_be()[..])
            }
            None => {}
        }

        Ok(())
    }

    /// Floats are encoded as big-endian octets of their IEEE-754 bit patterns,
    /// except for special cases: +-zero, +-inf and nan.
    ///
    /// Ion hash defines representations for some special values.
    fn write_repr_float(&mut self, value: Option<f64>) -> IonResult<()> {
        match value {
            None => {}
            Some(v) => {
                // This matches positive and negative zero.
                if v == 0.0 {
                    if !v.is_sign_positive() {
                        escaping(self)
                            .update_escaping([0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                    };
                    return Ok(());
                }
                if v.is_infinite() {
                    return if v.is_sign_positive() {
                        escaping(self)
                            .update_escaping([0x7F, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                        Ok(())
                    } else {
                        escaping(self)
                            .update_escaping([0xFF, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                        Ok(())
                    };
                }

                if v.is_nan() {
                    escaping(self)
                        .update_escaping([0x7F, 0xF8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                    return Ok(());
                }

                escaping(self).update_escaping(&v.to_be_bytes());
            }
        }

        Ok(())
    }

    fn write_repr_decimal(&mut self, value: Option<&Decimal>) -> IonResult<()> {
        match value {
            None => {}
            Some(decimal) => escaping(self).encode_decimal(decimal)?,
        };

        Ok(())
    }

    fn write_repr_timestamp(&mut self, value: Option<&Timestamp>) -> IonResult<()> {
        match value {
            None => {}
            Some(timestamp) => escaping(self).encode_timestamp(timestamp)?,
        };

        Ok(())
    }

    fn write_repr_symbol<S>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: SymbolToken + ?Sized,
    {
        match value {
            Some(s) => match s.text() {
                Some(s) => RepresentationEncoder::<E>::write_repr_string(self, Some(s))?, // FIXME: Why must E be explicit here?
                None => {
                    todo!("hash SymbolToken without text")
                }
            },
            None => {}
        }

        Ok(())
    }

    fn write_repr_string(&mut self, value: Option<&str>) -> IonResult<()> {
        match value {
            Some(s) if s.len() > 0 => escaping(self).update_escaping(s.as_bytes()),
            _ => {}
        };

        Ok(())
    }

    fn write_repr_blob(&mut self, value: Option<&[u8]>) -> IonResult<()> {
        match value {
            Some(bytes) if bytes.len() > 0 => escaping(self).update_escaping(bytes),
            _ => {}
        }

        Ok(())
    }

    fn write_repr_seq<S>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: Sequence + ?Sized,
    {
        if let Some(seq) = value {
            for elem in seq.iter() {
                self.update_serialized_bytes(elem)?;
            }
        }

        Ok(())
    }

    /// Iterates over a `Struct`, computing the "field hash" of each field
    /// (key-value pair). The field hash is defined in the spec as:
    ///
    /// ```text
    /// H(field) -> h(s(fieldname) || s(fieldvalue))
    /// ```
    ///
    /// The resulting `Vec` is not sorted (i.e. is in the same order as the field
    /// iterator).
    fn write_repr_struct<S, F>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: Struct<FieldName = F, Element = E> + ?Sized,
        F: SymbolToken + ?Sized,
    {
        if let Some(strukt) = value {
            let mut hashes: Vec<_> = strukt
                .iter()
                .map(|(key, value)| struct_field_hash::<D, _, _>(key, value))
                .collect::<IonResult<_>>()?;

            hashes.sort();

            for hash in hashes {
                escaping(self).update_escaping(hash);
            }
        }

        Ok(())
    }
}

fn struct_field_hash<D, F, E>(key: &F, value: &E) -> IonResult<Output<D>>
where
    D: Update + FixedOutput + Reset + Clone + Default,
    F: SymbolToken + ?Sized,
    E: Element + ?Sized,
{
    let mut hasher = D::default();

    // TODO: How do I tell the compiler (using the normal sugar) that the `E` in
    // this signature (must) match the `E` of `ElementHasher<E>` for the built
    // digest?

    // key
    ElementHasher::<E>::mark_begin(&mut hasher);
    let tq = type_qualifier_symbol(Some(key));
    hasher.update(tq.as_bytes());
    RepresentationEncoder::<E>::write_repr_symbol(&mut hasher, Some(key))?;
    ElementHasher::<E>::mark_end(&mut hasher);

    // value
    ElementHasher::<E>::update_serialized_bytes(&mut hasher, value)?;

    Ok(hasher.finalize_fixed())
}

/// The ion-rust crate uses the `io::Write` trait as a sink for writing
/// representations. This implementation provides compatibility with the
/// `Digest` trait (represented as a set of "sub"-traits). We have no need of an
/// intermediate buffer!
impl<'a, D> io::Write for EscapingDigest<'a, D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.update_escaping(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

struct EscapingDigest<'a, D>(&'a mut D)
where
    D: Update + FixedOutput + Reset + Clone + Default;

impl<'a, D> EscapingDigest<'a, D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    /// Escapes various markers as per the spec. Allocates a temporary array to
    /// do so.
    fn update_escaping(&mut self, data: impl AsRef<[u8]>) {
        let mut escaped = vec![];

        for byte in data.as_ref() {
            if let Markers::B | Markers::E | Markers::ESC = *byte {
                escaped.extend(&[Markers::ESC, *byte]);
            } else {
                escaped.extend(&[*byte]);
            }
        }

        self.0.update(escaped);
    }
}

fn escaping<'a, D>(inner: &'a mut D) -> EscapingDigest<'a, D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    EscapingDigest(inner)
}
