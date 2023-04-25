use crate::lazy::lazy_system_reader::{LazySequence, LazyStruct};
use crate::result::decoding_error;
use crate::{Decimal, Int, IonResult, IonType, Symbol, Timestamp};
use std::fmt::{Debug, Formatter};

/// A [ValueRef] represents a value that has been read from the input stream. Scalar variants contain
/// their associated data, while container variants contain a handle to traverse the container. (See
/// [SequenceRef] and [StructRef].)
///
/// Unlike a [crate::element::Value], a `ValueRef` avoids heap allocation whenever possible.
/// Numeric values and timestamps are stored within the `ValueRef` itself. Text values and lobs hold
/// references to either a slice of input data or text in the symbol table.
pub enum ValueRef<'a> {
    Null(IonType),
    Bool(bool),
    Int(Int),
    Float(f64),
    Decimal(Decimal),
    Timestamp(Timestamp),
    String(&'a str),
    Symbol(Symbol),
    Blob(&'a [u8]),
    Clob(&'a [u8]),
    // As ValueRef represents a reference to a value in the streaming APIs, the container variants
    // simply indicate their Ion type. To access their nested data, the reader would need to step in.
    SExp(LazySequence<'a>),
    List(LazySequence<'a>),
    Struct(LazyStruct<'a>),
}

impl<'a> Debug for ValueRef<'a> {
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

impl<'a> ValueRef<'a> {
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

    pub fn expect_string(self) -> IonResult<&'a str> {
        if let ValueRef::String(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a string")
        }
    }

    pub fn expect_symbol(self) -> IonResult<Symbol> {
        if let ValueRef::Symbol(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a symbol")
        }
    }

    pub fn expect_blob(self) -> IonResult<&'a [u8]> {
        if let ValueRef::Blob(b) = self {
            Ok(b)
        } else {
            decoding_error("expected a blob")
        }
    }

    pub fn expect_clob(self) -> IonResult<&'a [u8]> {
        if let ValueRef::Clob(c) = self {
            Ok(c)
        } else {
            decoding_error("expected a clob")
        }
    }

    pub fn expect_list(self) -> IonResult<LazySequence<'a>> {
        if let ValueRef::List(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a list")
        }
    }

    pub fn expect_sexp(self) -> IonResult<LazySequence<'a>> {
        if let ValueRef::SExp(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a sexp")
        }
    }

    pub fn expect_struct(self) -> IonResult<LazyStruct<'a>> {
        if let ValueRef::Struct(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a struct")
        }
    }
}
