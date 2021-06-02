// Copyright Amazon.com, Inc. or its affiliates.

//! This file provides an extension trait [`Representation`] that is implemented
//! for Ion types found in the [`Element`] API. In the fullness of time, this
//! file should not exist as we should be using the Ion "raw" binary writer
//! instead. This implementation fills in that gap, and is focused on coverage
//! and not speed.

use crate::{
    mark_begin, mark_end, type_qualifier::type_qualifier_symbol,
    update_type_qualifier_and_representation, Markers,
};
use digest::{FixedOutput, Output, Reset, Update};
use ion_rs::{
    binary,
    result::{illegal_operation, IonResult},
    value::{AnyInt, Element, Struct, SymbolToken},
    IonType,
};

// TODO: Finish ion-rust's binary writer and factor it such that the binary
// representations can be written by the "raw" writer (ref. the Java
// implementation).
pub(crate) fn update_with_representation<E, D>(elem: &E, hasher: &mut D) -> IonResult<()>
where
    E: Element + ?Sized,
    D: Update + FixedOutput + Reset + Clone + Default,
{
    let mut escaping = escaping(hasher);
    write_repr(elem, &mut escaping)
}

fn write_repr<E, D>(elem: &E, hasher: &mut EscapingDigest<'_, D>) -> IonResult<()>
where
    E: Element + ?Sized,
    D: Update + FixedOutput + Reset + Clone + Default,
{
    match elem.ion_type() {
        IonType::Null | IonType::Boolean => {} // these types have no representation
        IonType::Integer => write_repr_integer(elem.as_any_int(), hasher),
        IonType::Float => write_repr_float(elem.as_f64(), hasher),
        IonType::Decimal | IonType::Timestamp => todo!(),
        IonType::Symbol => write_repr_symbol(elem.as_sym(), hasher),
        IonType::String => write_repr_string(elem.as_str(), hasher),
        IonType::Clob | IonType::Blob => write_repr_blob(elem.as_bytes(), hasher),
        IonType::List | IonType::SExpression => {
            illegal_operation(format!("type {} is not yet supported", elem.ion_type()))?
        }
        IonType::Struct => write_repr_struct(elem.as_struct(), hasher)?,
    }

    Ok(())
}

/// Wraps an existing `Update` in an escaping one, which replaces each marker
/// byte M with ESC || M.
fn escaping<'a, D>(inner: &'a mut D) -> EscapingDigest<'a, D>
where
    D: Update,
{
    EscapingDigest(inner)
}

struct EscapingDigest<'a, D: Update>(&'a mut D);

impl<'a, D> Update for EscapingDigest<'a, D>
where
    D: Update,
{
    /// Escapes various markers as per the spec. Allocates a temporary array to
    /// do so.
    fn update(&mut self, data: impl AsRef<[u8]>) {
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

fn write_repr_integer<D: Update>(value: Option<&AnyInt>, hasher: &mut EscapingDigest<'_, D>) {
    match value {
        Some(AnyInt::I64(v)) => match v {
            0 => {}
            _ => {
                let magnitude = v.abs() as u64;
                let encoded = binary::uint::encode_uint(magnitude);
                hasher.update(encoded.as_bytes())
            }
        },
        Some(AnyInt::BigInt(b)) => hasher.update(&b.magnitude().to_bytes_be()[..]),
        None => {}
    }
}

/// Ion hash defines representations for some special values.
struct Floats;
impl Floats {
    const NEGATIVE_ZERO: [u8; 8] = [0x80, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    const POSITIVE_INFINITY: [u8; 8] = [0x7F, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    const NEGATIVE_INFINITY: [u8; 8] = [0xFF, 0xF0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
    const NAN: [u8; 8] = [0x7F, 0xF8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00];
}

/// Floats are encoded as big-endian octets of their IEEE-754 bit patterns,
/// except for special cases: +-zero, +-inf and nan.
fn write_repr_float<D: Update>(value: Option<f64>, hasher: &mut EscapingDigest<'_, D>) {
    match value {
        None => {}
        Some(v) => {
            // This matches positive and negative zero.
            if v == 0.0 {
                return if !v.is_sign_positive() {
                    hasher.update(Floats::NEGATIVE_ZERO);
                };
            }
            if v.is_infinite() {
                return if v.is_sign_positive() {
                    hasher.update(Floats::POSITIVE_INFINITY)
                } else {
                    hasher.update(Floats::NEGATIVE_INFINITY)
                };
            }

            if v.is_nan() {
                return hasher.update(Floats::NAN);
            }

            hasher.update(&v.to_be_bytes())
        }
    }
}

fn write_repr_symbol<D, S>(value: Option<&S>, hasher: &mut EscapingDigest<'_, D>)
where
    D: Update,
    S: SymbolToken + ?Sized,
{
    match value {
        Some(s) => {
            match s.text() {
                Some(s) => write_repr_string(Some(s), hasher),
                None => {
                    todo!("hash SymbolToken without text")
                }
            }
        }
        None => {}
    }
}

fn write_repr_string<D: Update>(value: Option<&str>, hasher: &mut EscapingDigest<'_, D>) {
    match value {
        Some(s) if s.len() > 0 => hasher.update(s.as_bytes()),
        _ => {}
    }
}

fn write_repr_blob<D: Update>(value: Option<&[u8]>, hasher: &mut EscapingDigest<'_, D>) {
    match value {
        Some(bytes) if bytes.len() > 0 => hasher.update(bytes),
        _ => {}
    }
}

fn write_repr_struct<D, S, F, E>(
    value: Option<&S>,
    hasher: &mut EscapingDigest<'_, D>,
) -> IonResult<()>
where
    D: Update + FixedOutput + Reset + Clone + Default,
    S: Struct<FieldName = F, Element = E> + ?Sized,
    F: SymbolToken + ?Sized,
    E: Element + ?Sized,
{
    if let Some(strukt) = value {
        let mut hashes: Vec<_> = strukt
            .iter()
            .map(|(key, value)| struct_field_hash::<D, _, _>(key, value))
            .collect::<IonResult<_>>()?;

        hashes.sort();

        for hash in hashes {
            hasher.update(hash);
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
fn struct_field_hash<D, F, E>(key: &F, value: &E) -> IonResult<Output<D>>
where
    D: Update + FixedOutput + Reset + Clone + Default,
    F: SymbolToken + ?Sized,
    E: Element + ?Sized,
{
    let mut hasher = D::default();

    // TODO: This is duplicated code, because a SymbolToken is not an
    // Element. Will dedup this in a future commit!

    // key
    mark_begin(&mut hasher);
    let tq = type_qualifier_symbol(Some(key));
    hasher.update(tq.as_bytes());
    {
        let mut inner_esc = escaping(&mut hasher);
        write_repr_symbol(Some(key), &mut inner_esc);
    }
    mark_end(&mut hasher);

    // value
    mark_begin(&mut hasher);
    update_type_qualifier_and_representation(value, &mut hasher)?;
    mark_end(&mut hasher);

    Ok(hasher.finalize_fixed())
}
