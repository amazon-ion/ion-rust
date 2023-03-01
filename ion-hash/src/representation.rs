// Copyright Amazon.com, Inc. or its affiliates.

//! This file provides an extension trait [`Representation`] that is implemented
//! for Ion types found in the [`IonElement`] API. In the fullness of time, this
//! file should not exist as we should be using the Ion "raw" binary writer
//! instead. This implementation fills in that gap, and is focused on coverage
//! and not speed.

use crate::element_hasher::ElementHasher;
use crate::type_qualifier::type_qualifier_symbol;
use digest::{FixedOutput, Output, Reset, Update};
use ion_rs::binary::{self, decimal::DecimalBinaryEncoder, timestamp::TimestampBinaryEncoder};
use ion_rs::types::decimal::Decimal;
use ion_rs::types::integer::Integer;
use ion_rs::{
    result::IonResult,
    types::timestamp::Timestamp,
    value::{IonElement, IonSequence, IonStruct, IonSymbolToken},
    IonType,
};

pub(crate) trait RepresentationEncoder {
    fn update_with_representation<E>(&mut self, elem: &E) -> IonResult<()>
    where
        E: IonElement + ?Sized,
    {
        match elem.ion_type() {
            IonType::Null | IonType::Boolean => {} // these types have no representation
            IonType::Integer => self.write_repr_integer(elem.as_integer())?,
            IonType::Float => self.write_repr_float(elem.as_float())?,
            IonType::Decimal => self.write_repr_decimal(elem.as_decimal())?,
            IonType::Timestamp => self.write_repr_timestamp(elem.as_timestamp())?,
            IonType::Symbol => self.write_repr_symbol(elem.as_symbol())?,
            IonType::String => self.write_repr_string(elem.as_string())?,
            IonType::Clob | IonType::Blob => self.write_repr_blob(elem.as_bytes())?,
            IonType::List | IonType::SExpression => self.write_repr_seq(elem.as_sequence())?,
            IonType::Struct => self.write_repr_struct(elem.as_struct())?,
        }

        Ok(())
    }

    fn write_repr_integer(&mut self, value: Option<&Integer>) -> IonResult<()>;
    fn write_repr_float(&mut self, value: Option<f64>) -> IonResult<()>;
    fn write_repr_decimal(&mut self, value: Option<&Decimal>) -> IonResult<()>;
    fn write_repr_timestamp(&mut self, value: Option<&Timestamp>) -> IonResult<()>;
    fn write_repr_symbol<S>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: IonSymbolToken + ?Sized;
    fn write_repr_string(&mut self, value: Option<&str>) -> IonResult<()>;
    fn write_repr_blob(&mut self, value: Option<&[u8]>) -> IonResult<()>;
    fn write_repr_seq<S>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: IonSequence + ?Sized;
    fn write_repr_struct<E, S, F>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        E: IonElement + ?Sized,
        S: IonStruct<FieldName = F, Element = E> + ?Sized,
        F: IonSymbolToken + ?Sized;
}

impl<D> RepresentationEncoder for ElementHasher<D>
where
    D: Update + FixedOutput + Reset + Clone + Default,
{
    fn write_repr_integer(&mut self, value: Option<&Integer>) -> IonResult<()> {
        match value {
            Some(Integer::I64(v)) => match v {
                0 => {}
                _ => {
                    let magnitude = v.abs() as u64;
                    let encoded = binary::uint::encode_u64(magnitude);
                    self.update_escaping(encoded.as_bytes());
                }
            },
            Some(Integer::BigInt(b)) => self.update_escaping(&b.magnitude().to_bytes_be()[..]),
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
                        self.update_escaping([0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                    };
                    return Ok(());
                }
                if v.is_infinite() {
                    return if v.is_sign_positive() {
                        self.update_escaping([0x7F, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                        Ok(())
                    } else {
                        self.update_escaping([0xFF, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                        Ok(())
                    };
                }

                if v.is_nan() {
                    self.update_escaping([0x7F, 0xF8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]);
                    return Ok(());
                }

                self.update_escaping(&v.to_be_bytes());
            }
        }

        Ok(())
    }

    fn write_repr_decimal(&mut self, value: Option<&Decimal>) -> IonResult<()> {
        match value {
            None => {}
            Some(decimal) => {
                let _ = self.encode_decimal(decimal)?;
            }
        };

        Ok(())
    }

    fn write_repr_timestamp(&mut self, value: Option<&Timestamp>) -> IonResult<()> {
        match value {
            None => {}
            Some(timestamp) => {
                let _ = self.encode_timestamp(timestamp)?;
            }
        };

        Ok(())
    }

    fn write_repr_symbol<S>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: IonSymbolToken + ?Sized,
    {
        // There are no representation bytes for null symbols or unknown-text symbols.
        if let Some(symbol) = value {
            if let Some(text) = symbol.text() {
                self.write_repr_string(Some(text))?;
            }
        }
        Ok(())
    }

    fn write_repr_string(&mut self, value: Option<&str>) -> IonResult<()> {
        match value {
            Some(s) if s.len() > 0 => self.update_escaping(s.as_bytes()),
            _ => {}
        };

        Ok(())
    }

    fn write_repr_blob(&mut self, value: Option<&[u8]>) -> IonResult<()> {
        match value {
            Some(bytes) if bytes.len() > 0 => self.update_escaping(bytes),
            _ => {}
        }

        Ok(())
    }

    fn write_repr_seq<S>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        S: IonSequence + ?Sized,
    {
        if let Some(seq) = value {
            for elem in seq.iter() {
                self.update_serialized_bytes(elem)?;
            }
        }

        Ok(())
    }

    /// Iterates over an `IonStruct`, computing the "field hash" of each field
    /// (key-value pair). The field hash is defined in the spec as:
    ///
    /// ```text
    /// H(field) -> h(s(fieldname) || s(fieldvalue))
    /// ```
    ///
    /// The resulting `Vec` is not sorted (i.e. is in the same order as the field
    /// iterator).
    fn write_repr_struct<E, S, F>(&mut self, value: Option<&S>) -> IonResult<()>
    where
        E: IonElement + ?Sized,
        S: IonStruct<FieldName = F, Element = E> + ?Sized,
        F: IonSymbolToken + ?Sized,
    {
        if let Some(struct_) = value {
            let mut hashes: Vec<_> = struct_
                .iter()
                .map(|(key, value)| struct_field_hash::<D, _, _>(key, value))
                .collect::<IonResult<_>>()?;

            hashes.sort();

            for hash in hashes {
                self.update_escaping(hash);
            }
        }

        Ok(())
    }
}

fn struct_field_hash<D, F, E>(key: &F, value: &E) -> IonResult<Output<D>>
where
    D: Update + FixedOutput + Reset + Clone + Default,
    F: IonSymbolToken + ?Sized,
    E: IonElement + ?Sized,
{
    let mut hasher = ElementHasher::new(D::default());

    // key
    hasher.mark_begin();
    let tq = type_qualifier_symbol(Some(key));
    hasher.digest.update(tq.as_bytes());
    hasher.write_repr_symbol(Some(key))?; // Not sure why I need this syntax.
    hasher.mark_end();

    // value
    hasher.update_serialized_bytes(value)?;

    Ok(hasher.digest.finalize_fixed())
}
