use crate::lazy::binary::raw::lazy_raw_sequence::LazyRawSequence;
use crate::lazy::binary::raw::lazy_raw_struct::LazyRawStruct;
use crate::result::decoding_error;
use crate::{Decimal, Int, IonResult, IonType, RawSymbolTokenRef, Timestamp};
use std::fmt::{Debug, Formatter};

/// As RawValueRef represents a reference to an unresolved value read from the data stream.
/// If the value is a symbol, it only contains the information found in the data stream (a symbol ID
/// or text literal). If it is a symbol ID, a symbol table will be needed to find its associated text.
///
/// For a resolved version of this type, see [ValueRef].
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
            decoding_error("expected a null")
        }
    }

    pub fn expect_bool(self) -> IonResult<bool> {
        if let RawValueRef::Bool(b) = self {
            Ok(b)
        } else {
            decoding_error("expected a bool")
        }
    }

    pub fn expect_int(self) -> IonResult<Int> {
        if let RawValueRef::Int(i) = self {
            Ok(i)
        } else {
            decoding_error("expected an int")
        }
    }

    pub fn expect_float(self) -> IonResult<f64> {
        if let RawValueRef::Float(f) = self {
            Ok(f)
        } else {
            decoding_error("expected a float")
        }
    }

    pub fn expect_decimal(self) -> IonResult<Decimal> {
        if let RawValueRef::Decimal(d) = self {
            Ok(d)
        } else {
            decoding_error("expected a decimal")
        }
    }

    pub fn expect_timestamp(self) -> IonResult<Timestamp> {
        if let RawValueRef::Timestamp(t) = self {
            Ok(t)
        } else {
            decoding_error("expected a timestamp")
        }
    }

    pub fn expect_string(self) -> IonResult<&'a str> {
        if let RawValueRef::String(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a string")
        }
    }

    pub fn expect_symbol(self) -> IonResult<RawSymbolTokenRef<'a>> {
        if let RawValueRef::Symbol(s) = self {
            Ok(s.clone())
        } else {
            decoding_error("expected a symbol")
        }
    }

    pub fn expect_blob(self) -> IonResult<&'a [u8]> {
        if let RawValueRef::Blob(b) = self {
            Ok(b)
        } else {
            decoding_error("expected a blob")
        }
    }

    pub fn expect_clob(self) -> IonResult<&'a [u8]> {
        if let RawValueRef::Clob(c) = self {
            Ok(c)
        } else {
            decoding_error("expected a clob")
        }
    }

    pub fn expect_list(self) -> IonResult<LazyRawSequence<'a>> {
        if let RawValueRef::List(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a list")
        }
    }

    pub fn expect_sexp(self) -> IonResult<LazyRawSequence<'a>> {
        if let RawValueRef::SExp(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a sexp")
        }
    }

    pub fn expect_struct(self) -> IonResult<LazyRawStruct<'a>> {
        if let RawValueRef::Struct(s) = self {
            Ok(s)
        } else {
            decoding_error("expected a struct")
        }
    }
}

pub trait ReadRawValueRef {
    fn read_value(&self) -> IonResult<RawValueRef>;

    fn read_null(&self) -> IonResult<IonType> {
        self.read_value()?.expect_null()
    }

    fn read_bool(&self) -> IonResult<bool> {
        self.read_value()?.expect_bool()
    }

    fn read_int(&self) -> IonResult<Int> {
        self.read_value()?.expect_int()
    }

    fn read_float(&self) -> IonResult<f64> {
        self.read_value()?.expect_float()
    }

    fn read_decimal(&self) -> IonResult<Decimal> {
        self.read_value()?.expect_decimal()
    }

    fn read_timestamp(&self) -> IonResult<Timestamp> {
        self.read_value()?.expect_timestamp()
    }

    fn read_string(&self) -> IonResult<&str> {
        self.read_value()?.expect_string()
    }

    fn read_symbol(&self) -> IonResult<RawSymbolTokenRef> {
        self.read_value()?.expect_symbol()
    }

    fn read_clob(&self) -> IonResult<&[u8]> {
        self.read_value()?.expect_clob()
    }

    fn read_blob(&self) -> IonResult<&[u8]> {
        self.read_value()?.expect_blob()
    }

    fn as_list(&self) -> IonResult<LazyRawSequence> {
        self.read_value()?.expect_list()
    }

    fn as_sexp(&self) -> IonResult<LazyRawSequence> {
        self.read_value()?.expect_sexp()
    }

    fn as_struct(&self) -> IonResult<LazyRawStruct> {
        self.read_value()?.expect_struct()
    }
}
