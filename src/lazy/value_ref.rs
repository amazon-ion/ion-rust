use crate::element::Value;
use crate::lazy::bytes_ref::BytesRef;
use crate::lazy::decoder::LazyDecoder;
use crate::lazy::r#struct::LazyStruct;
use crate::lazy::sequence::{LazyList, LazySExp};
use crate::lazy::str_ref::StrRef;
use crate::result::IonFailure;
use crate::{Decimal, Element, Int, IonError, IonResult, IonType, SymbolRef, Timestamp};
use std::fmt::{Debug, Formatter};

/// A [ValueRef] represents a value that has been read from the input stream. Scalar variants contain
/// their associated data, while container variants contain a handle to traverse the container. (See
/// [LazyList] and [LazyStruct].)
///
/// Unlike a [Value], a `ValueRef` avoids heap allocation whenever possible, choosing to point instead
/// to existing resources. Numeric values and timestamps are stored within the `ValueRef` itself.
/// Text values and lobs hold references to either a slice of input data or text in the symbol table.
pub enum ValueRef<'top, D: LazyDecoder> {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(StrRef<'top>),
    Symbol(SymbolRef<'top>),
    Blob(BytesRef<'top>),
    Clob(BytesRef<'top>),
    SExp(LazySExp<'top, D>),
    List(LazyList<'top, D>),
    Struct(LazyStruct<'top, D>),
}

impl<'top, D: LazyDecoder> PartialEq for ValueRef<'top, D> {
    fn eq(&self, other: &Self) -> bool {
        use ValueRef::*;
        match (self, other) {
            (Null(i1), Null(i2)) => i1 == i2,
            (Bool(b1), Bool(b2)) => b1 == b2,
            (Int(i1), Int(i2)) => i1 == i2,
            (Float(f1), Float(f2)) => f1 == f2,
            (Decimal(d1), Decimal(d2)) => d1 == d2,
            (Timestamp(t1), Timestamp(t2)) => t1 == t2,
            (String(s1), String(s2)) => s1 == s2,
            (Symbol(s1), Symbol(s2)) => s1 == s2,
            (Blob(b1), Blob(b2)) => b1 == b2,
            (Clob(c1), Clob(c2)) => c1 == c2,
            // TODO: The following is no longer true; should we finish implementing PartialEq for
            //       container types?
            // We cannot compare lazy containers as we cannot guarantee that their complete contents
            // are available in the buffer. Is `{foo: bar}` equal to `{foo: b`?
            _ => false,
        }
    }
}

impl<'top, D: LazyDecoder> Debug for ValueRef<'top, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        use ValueRef::*;
        match self {
            Null(ion_type) => write!(f, "null.{}", ion_type),
            Bool(b) => write!(f, "{}", b),
            Int(i) => write!(f, "{}", i),
            Float(float) => write!(f, "{}", float),
            Decimal(d) => write!(f, "{}", d),
            Timestamp(t) => write!(f, "{}", t),
            String(s) => write!(f, "\"{}\"", s),
            Symbol(s) => write!(f, "{}", s.text().unwrap_or("$0")),
            Blob(b) => write!(f, "blob ({} bytes)", b.len()),
            Clob(c) => write!(f, "clob ({} bytes)", c.len()),
            SExp(s) => write!(f, "sexp={:?}", s),
            List(l) => write!(f, "{:?}", l),
            Struct(s) => write!(f, "{:?}", s),
        }
    }
}

impl<'top, D: LazyDecoder> TryFrom<ValueRef<'top, D>> for Value {
    type Error = IonError;

    fn try_from(value: ValueRef<'top, D>) -> Result<Self, Self::Error> {
        use ValueRef::*;
        let value = match value {
            Null(ion_type) => Value::Null(ion_type),
            Bool(b) => Value::Bool(b),
            Int(i) => Value::Int(i),
            Float(f) => Value::Float(f),
            Decimal(d) => Value::Decimal(d),
            Timestamp(t) => Value::Timestamp(t),
            String(s) => Value::String(s.into()),
            Symbol(s) => Value::Symbol(s.into()),
            Blob(b) => Value::Blob(b.into()),
            Clob(c) => Value::Clob(c.into()),
            SExp(s) => Value::SExp(s.try_into()?),
            List(l) => Value::List(l.try_into()?),
            Struct(s) => Value::Struct(s.try_into()?),
        };
        Ok(value)
    }
}

impl<'top, D: LazyDecoder> TryFrom<ValueRef<'top, D>> for Element {
    type Error = IonError;

    fn try_from(value_ref: ValueRef<'top, D>) -> Result<Self, Self::Error> {
        let value: Value = value_ref.try_into()?;
        Ok(value.into())
    }
}

impl<'top, D: LazyDecoder> ValueRef<'top, D> {
    pub fn expect_null(self) -> IonResult<IonType> {
        if let ValueRef::Null(ion_type) = self {
            Ok(ion_type)
        } else {
            IonResult::decoding_error("expected a null")
        }
    }

    pub fn expect_bool(self) -> IonResult<bool> {
        if let ValueRef::Bool(b) = self {
            Ok(b)
        } else {
            IonResult::decoding_error("expected a bool")
        }
    }

    pub fn expect_int(self) -> IonResult<Int> {
        if let ValueRef::Int(i) = self {
            Ok(i)
        } else {
            IonResult::decoding_error("expected an int")
        }
    }

    pub fn expect_i64(self) -> IonResult<i64> {
        if let ValueRef::Int(i) = self {
            i.expect_i64()
        } else {
            IonResult::decoding_error("expected an int (i64)")
        }
    }

    pub fn expect_float(self) -> IonResult<f64> {
        if let ValueRef::Float(f) = self {
            Ok(f)
        } else {
            IonResult::decoding_error("expected a float")
        }
    }

    pub fn expect_decimal(self) -> IonResult<Decimal> {
        if let ValueRef::Decimal(d) = self {
            Ok(d)
        } else {
            IonResult::decoding_error("expected a decimal")
        }
    }

    pub fn expect_timestamp(self) -> IonResult<Timestamp> {
        if let ValueRef::Timestamp(t) = self {
            Ok(t)
        } else {
            IonResult::decoding_error("expected a timestamp")
        }
    }

    pub fn expect_string(self) -> IonResult<StrRef<'top>> {
        if let ValueRef::String(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error("expected a string")
        }
    }

    pub fn expect_symbol(self) -> IonResult<SymbolRef<'top>> {
        if let ValueRef::Symbol(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error(format!("expected a symbol, found {:?}", self))
        }
    }

    pub fn expect_text(&self) -> IonResult<&'_ str> {
        use ValueRef::*;
        match self {
            String(string) => Ok(string.text()),
            Symbol(symbol) => symbol.text().ok_or_else(|| {
                IonError::decoding_error("expected text but found a symbol with undefined text")
            }),
            _ => IonResult::decoding_error("expected a string or symbol"),
        }
    }

    pub fn expect_blob(self) -> IonResult<BytesRef<'top>> {
        if let ValueRef::Blob(b) = self {
            Ok(b)
        } else {
            IonResult::decoding_error("expected a blob")
        }
    }

    pub fn expect_clob(self) -> IonResult<BytesRef<'top>> {
        if let ValueRef::Clob(c) = self {
            Ok(c)
        } else {
            IonResult::decoding_error("expected a clob")
        }
    }

    pub fn expect_lob(self) -> IonResult<BytesRef<'top>> {
        use ValueRef::*;
        match self {
            Blob(b) | Clob(b) => Ok(b),
            _ => IonResult::decoding_error("expected a blob or clob"),
        }
    }

    pub fn expect_list(self) -> IonResult<LazyList<'top, D>> {
        if let ValueRef::List(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error("expected a list")
        }
    }

    pub fn expect_sexp(self) -> IonResult<LazySExp<'top, D>> {
        if let ValueRef::SExp(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error("expected a sexp")
        }
    }

    pub fn expect_struct(self) -> IonResult<LazyStruct<'top, D>> {
        if let ValueRef::Struct(s) = self {
            Ok(s)
        } else {
            IonResult::decoding_error("expected a struct")
        }
    }

    pub fn ion_type(&self) -> IonType {
        match self {
            ValueRef::Null(ion_type) => *ion_type,
            ValueRef::Bool(_) => IonType::Bool,
            ValueRef::Int(_) => IonType::Int,
            ValueRef::Float(_) => IonType::Float,
            ValueRef::Decimal(_) => IonType::Decimal,
            ValueRef::Timestamp(_) => IonType::Timestamp,
            ValueRef::String(_) => IonType::String,
            ValueRef::Symbol(_) => IonType::Symbol,
            ValueRef::Blob(_) => IonType::Blob,
            ValueRef::Clob(_) => IonType::Clob,
            ValueRef::SExp(_) => IonType::SExp,
            ValueRef::List(_) => IonType::List,
            ValueRef::Struct(_) => IonType::Struct,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::lazy::binary::test_utilities::to_binary_ion;
    use crate::lazy::reader::LazyBinaryReader;
    use crate::lazy::value_ref::ValueRef;
    use crate::{Decimal, IonResult, IonType, SymbolRef, Timestamp};

    #[test]
    fn expect_type() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
            null
            true
            1
            2.5e0
            2.5
            2023-04-29T
            foo
            "hello"
            {{Blob}}
            {{"Clob"}}
            [this, is, a, list]
            (this is a sexp)
            {this: is, a: struct}
        "#,
        )?;
        let mut reader = LazyBinaryReader::new(ion_data)?;
        assert_eq!(reader.expect_next()?.read()?.expect_null()?, IonType::Null);
        assert!(reader.expect_next()?.read()?.expect_bool()?);
        assert_eq!(reader.expect_next()?.read()?.expect_i64()?, 1);
        assert_eq!(reader.expect_next()?.read()?.expect_float()?, 2.5f64);
        assert_eq!(
            reader.expect_next()?.read()?.expect_decimal()?,
            Decimal::new(25, -1)
        );
        assert_eq!(
            reader.expect_next()?.read()?.expect_timestamp()?,
            Timestamp::with_ymd(2023, 4, 29).build()?
        );
        assert_eq!(
            reader.expect_next()?.read()?.expect_symbol()?,
            SymbolRef::from("foo")
        );
        assert_eq!(reader.expect_next()?.read()?.expect_string()?, "hello");
        assert_eq!(
            reader.expect_next()?.read()?.expect_blob()?,
            [0x06u8, 0x5A, 0x1B].as_ref() // Base64-decoded "Blob"
        );
        assert_eq!(
            reader.expect_next()?.read()?.expect_clob()?,
            "Clob".as_bytes()
        );
        assert!(reader.expect_next()?.read()?.expect_list().is_ok());
        assert!(reader.expect_next()?.read()?.expect_sexp().is_ok());
        assert!(reader.expect_next()?.read()?.expect_struct().is_ok());

        Ok(())
    }

    #[test]
    fn partial_eq() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
            null
            true
            1
            2.5e0
            2.5
            2023-04-29T
            foo
            "hello"
            {{Blob}}
            {{"Clob"}}
        "#,
        )?;
        let mut reader = LazyBinaryReader::new(ion_data)?;
        let first_value = reader.expect_next()?.read()?;
        assert_ne!(first_value, ValueRef::String("it's not a string".into()));
        assert_eq!(first_value, ValueRef::Null(IonType::Null));
        assert_eq!(reader.expect_next()?.read()?, ValueRef::Bool(true));
        assert_eq!(reader.expect_next()?.read()?, ValueRef::Int(1.into()));
        assert_eq!(reader.expect_next()?.read()?, ValueRef::Float(2.5f64));
        assert_eq!(
            reader.expect_next()?.read()?,
            ValueRef::Decimal(Decimal::new(25, -1))
        );
        assert_eq!(
            reader.expect_next()?.read()?,
            ValueRef::Timestamp(Timestamp::with_ymd(2023, 4, 29).build()?)
        );
        assert_eq!(
            reader.expect_next()?.read()?,
            ValueRef::Symbol(SymbolRef::from("foo"))
        );
        assert_eq!(
            reader.expect_next()?.read()?,
            ValueRef::String("hello".into())
        );
        assert_eq!(
            reader.expect_next()?.read()?,
            ValueRef::Blob([0x06, 0x5A, 0x1B].as_ref().into()) // Base64-decoded "Blob"
        );
        assert_eq!(
            reader.expect_next()?.read()?,
            ValueRef::Clob("Clob".as_bytes().into())
        );

        // PartialEq doesn't cover lazy containers

        Ok(())
    }
}
