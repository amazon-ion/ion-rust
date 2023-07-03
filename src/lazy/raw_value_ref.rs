use crate::lazy::binary::raw::lazy_raw_sequence::LazyRawSequence;
use crate::lazy::binary::raw::lazy_raw_struct::LazyRawStruct;
use crate::result::IonFailure;
use crate::{Decimal, Int, IonResult, IonType, RawSymbolTokenRef, Timestamp};
use std::fmt::{Debug, Formatter};

/// As RawValueRef represents a reference to an unresolved value read from the data stream.
/// If the value is a symbol, it only contains the information found in the data stream (a symbol ID
/// or text literal). If it is a symbol ID, a symbol table will be needed to find its associated text.
///
/// For a resolved version of this type, see [crate::lazy::value_ref::ValueRef].
pub enum RawValueRef<'a> {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(&'a str),
    Symbol(RawSymbolTokenRef<'a>),
    Blob(&'a [u8]),
    Clob(&'a [u8]),
    SExp(LazyRawSequence<'a>),
    List(LazyRawSequence<'a>),
    Struct(LazyRawStruct<'a>),
}

impl<'a> Debug for RawValueRef<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            RawValueRef::Null(ion_type) => write!(f, "null.{}", ion_type),
            RawValueRef::Bool(b) => write!(f, "{}", b),
            RawValueRef::Int(i) => write!(f, "{}", i),
            RawValueRef::Float(float) => write!(f, "{}", float),
            RawValueRef::Decimal(d) => write!(f, "{}", d),
            RawValueRef::Timestamp(t) => write!(f, "{}", t),
            RawValueRef::String(s) => write!(f, "{}", s),
            RawValueRef::Symbol(s) => write!(f, "{:?}", s),
            RawValueRef::Blob(b) => write!(f, "blob ({} bytes)", b.len()),
            RawValueRef::Clob(c) => write!(f, "clob ({} bytes)", c.len()),
            RawValueRef::SExp(s) => write!(f, "sexp={:?}", s),
            RawValueRef::List(l) => write!(f, "{:?}", l),
            RawValueRef::Struct(s) => write!(f, "{:?}", s),
        }
    }
}

impl<'a> RawValueRef<'a> {
    pub fn expect_null(self) -> IonResult<IonType> {
        if let RawValueRef::Null(ion_type) = self {
            Ok(ion_type)
        } else {
            IonResult::decoding_error("expected a null")
        }
    }

    pub fn expect_bool(self) -> IonResult<bool> {
        if let RawValueRef::Bool(b) = self {
            Ok(b)
        } else {
            IonResult::decoding_error("expected a bool")
        }
    }

    pub fn expect_int(self) -> IonResult<Int> {
        if let RawValueRef::Int(i) = self {
            Ok(i)
        } else {
            IonResult::decoding_error("expected an int")
        }
    }

    pub fn expect_float(self) -> IonResult<f64> {
        if let RawValueRef::Float(f) = self {
            Ok(f)
        } else {
            IonResult::decoding_error("expected a float")
        }
    }

    pub fn expect_decimal(self) -> IonResult<Decimal> {
        if let RawValueRef::Decimal(d) = self {
            Ok(d)
        } else {
            IonResult::decoding_error("expected a decimal")
        }
    }

    pub fn expect_timestamp(self) -> IonResult<Timestamp> {
        if let RawValueRef::Timestamp(t) = self {
            Ok(t)
        } else {
            IonResult::decoding_error("expected a timestamp")
        }
    }

    pub fn expect_string(self) -> IonResult<&'a str> {
        if let RawValueRef::String(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error("expected a string")
        }
    }

    pub fn expect_symbol(self) -> IonResult<RawSymbolTokenRef<'a>> {
        if let RawValueRef::Symbol(s) = self {
            Ok(s.clone())
        } else {
            IonResult::decoding_error("expected a symbol")
        }
    }

    pub fn expect_blob(self) -> IonResult<&'a [u8]> {
        if let RawValueRef::Blob(b) = self {
            Ok(b)
        } else {
            IonResult::decoding_error("expected a blob")
        }
    }

    pub fn expect_clob(self) -> IonResult<&'a [u8]> {
        if let RawValueRef::Clob(c) = self {
            Ok(c)
        } else {
            IonResult::decoding_error("expected a clob")
        }
    }

    pub fn expect_list(self) -> IonResult<LazyRawSequence<'a>> {
        if let RawValueRef::List(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error("expected a list")
        }
    }

    pub fn expect_sexp(self) -> IonResult<LazyRawSequence<'a>> {
        if let RawValueRef::SExp(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error("expected a sexp")
        }
    }

    pub fn expect_struct(self) -> IonResult<LazyRawStruct<'a>> {
        if let RawValueRef::Struct(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error("expected a struct")
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::raw::lazy_raw_reader::LazyRawReader;
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::{Decimal, IonResult, IonType, RawSymbolTokenRef, Timestamp};

    #[test]
    fn expect_type() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
            null
            true
            1
            2.5e0
            2.5
            2023-04-29T13:45:38.281Z
            foo
            "hello"
            {{Blob}}
            {{"Clob"}}
            [this, is, a, list]
            (this is a sexp)
            {this: is, a: struct}
        "#,
        )?;
        let mut reader = LazyRawReader::new(&ion_data);
        // IVM
        reader.next()?.expect_ivm()?;
        // Symbol table
        reader.next()?.expect_value()?.read()?.expect_struct()?;
        // User data
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_null()?,
            IonType::Null
        );
        assert!(reader.next()?.expect_value()?.read()?.expect_bool()?);
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_int()?,
            1.into()
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_float()?,
            2.5f64
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_decimal()?,
            Decimal::new(25, -1)
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_timestamp()?,
            Timestamp::with_ymd_hms_millis(2023, 4, 29, 13, 45, 38, 281).build_at_offset(0)?
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_symbol()?,
            RawSymbolTokenRef::SymbolId(10) // foo
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_string()?,
            "hello"
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_blob()?,
            &[0x06, 0x5A, 0x1B] // Base64-decoded "Blob"
        );
        assert_eq!(
            reader.next()?.expect_value()?.read()?.expect_clob()?,
            "Clob".as_bytes()
        );
        assert!(reader.next()?.expect_value()?.read()?.expect_list().is_ok());
        assert!(reader.next()?.expect_value()?.read()?.expect_sexp().is_ok());
        assert!(reader
            .next()?
            .expect_value()?
            .read()?
            .expect_struct()
            .is_ok());

        Ok(())
    }

    #[test]
    fn expect_type_error() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
            true
            null.bool
        "#,
        )?;
        let mut reader = LazyRawReader::new(&ion_data);
        // IVM
        reader.next()?.expect_ivm()?;

        let bool_value = reader.next()?.expect_value()?;
        assert!(bool_value.read()?.expect_null().is_err());
        assert!(bool_value.read()?.expect_int().is_err());
        assert!(bool_value.read()?.expect_float().is_err());
        assert!(bool_value.read()?.expect_decimal().is_err());
        assert!(bool_value.read()?.expect_timestamp().is_err());
        assert!(bool_value.read()?.expect_symbol().is_err());
        assert!(bool_value.read()?.expect_string().is_err());
        assert!(bool_value.read()?.expect_blob().is_err());
        assert!(bool_value.read()?.expect_clob().is_err());
        assert!(bool_value.read()?.expect_list().is_err());
        assert!(bool_value.read()?.expect_sexp().is_err());
        assert!(bool_value.read()?.expect_struct().is_err());

        let null_value = reader.next()?.expect_value()?;
        assert!(null_value.read()?.expect_bool().is_err());
        Ok(())
    }
}
