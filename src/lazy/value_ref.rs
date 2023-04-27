use crate::element::Value;
use crate::lazy::binary::lazy_system_reader::{LazySequence, LazyStruct};
use crate::result::decoding_error;
use crate::{Decimal, Int, IonError, IonResult, IonType, SymbolRef, Timestamp};
use std::fmt::{Debug, Formatter};

/// A [ValueRef] represents a value that has been read from the input stream. Scalar variants contain
/// their associated data, while container variants contain a handle to traverse the container. (See
/// [SequenceRef] and [StructRef].)
///
/// Unlike a [crate::element::Value], a `ValueRef` avoids heap allocation whenever possible.
/// Numeric values and timestamps are stored within the `ValueRef` itself. Text values and lobs hold
/// references to either a slice of input data or text in the symbol table.
pub enum ValueRef<'top, 'data> {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(&'data str),
    Symbol(SymbolRef<'top>),
    Blob(&'data [u8]),
    Clob(&'data [u8]),
    // As ValueRef represents a reference to a value in the streaming APIs, the container variants
    // simply indicate their Ion type. To access their nested data, the reader would need to step in.
    SExp(LazySequence<'top, 'data>),
    List(LazySequence<'top, 'data>),
    Struct(LazyStruct<'top, 'data>),
}

impl<'top, 'data> Debug for ValueRef<'top, 'data> {
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

impl<'top, 'data> TryFrom<ValueRef<'top, 'data>> for Value {
    type Error = IonError;

    fn try_from(value: ValueRef<'top, 'data>) -> Result<Self, Self::Error> {
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

impl<'top, 'data> ValueRef<'top, 'data> {
    pub fn expect_null(self) -> IonResult<IonType> {
        if let ValueRef::Null(ion_type) = self {
            Ok(ion_type)
        } else {
            decoding_error("expected a null")
        }
    }

    pub fn expect_bool(self) -> IonResult<bool> {
        if let ValueRef::Bool(b) = self {
            Ok(b)
        } else {
            decoding_error("expected a bool")
        }
    }

    pub fn expect_int(self) -> IonResult<Int> {
        if let ValueRef::Int(i) = self {
            Ok(i)
        } else {
            decoding_error("expected an int")
        }
    }

    pub fn expect_float(self) -> IonResult<f64> {
        if let ValueRef::Float(f) = self {
            Ok(f)
        } else {
            decoding_error("expected a float")
        }
    }

    pub fn expect_decimal(self) -> IonResult<Decimal> {
        if let ValueRef::Decimal(d) = self {
            Ok(d)
        } else {
            decoding_error("expected a decimal")
        }
    }

    pub fn expect_timestamp(self) -> IonResult<Timestamp> {
        if let ValueRef::Timestamp(t) = self {
            Ok(t)
        } else {
            decoding_error("expected a timestamp")
        }
    }

    pub fn expect_string(self) -> IonResult<&'data str> {
        if let ValueRef::String(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a string")
        }
    }

    pub fn expect_symbol(self) -> IonResult<SymbolRef<'top>> {
        if let ValueRef::Symbol(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a symbol")
        }
    }

    pub fn expect_blob(self) -> IonResult<&'data [u8]> {
        if let ValueRef::Blob(b) = self {
            Ok(b)
        } else {
            decoding_error("expected a blob")
        }
    }

    pub fn expect_clob(self) -> IonResult<&'data [u8]> {
        if let ValueRef::Clob(c) = self {
            Ok(c)
        } else {
            decoding_error("expected a clob")
        }
    }

    pub fn expect_list(self) -> IonResult<LazySequence<'top, 'data>> {
        if let ValueRef::List(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a list")
        }
    }

    pub fn expect_sexp(self) -> IonResult<LazySequence<'top, 'data>> {
        if let ValueRef::SExp(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a sexp")
        }
    }

    pub fn expect_struct(self) -> IonResult<LazyStruct<'top, 'data>> {
        if let ValueRef::Struct(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a struct")
        }
    }
}
