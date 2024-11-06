#![allow(non_camel_case_types)]

use crate::lazy::expanded::EncodingContextRef;
use crate::result::IonFailure;
use crate::symbol_table::{SystemSymbolTable, SYSTEM_SYMBOLS_1_1};
use crate::types::SymbolAddress;
use crate::{IonError, IonResult, Symbol, SymbolId, SymbolRef};
use ice_code::ice;

/// A raw symbol token found in the input stream.
#[derive(Debug, Copy, Clone, Eq)]
pub enum RawSymbolRef<'a> {
    /// A symbol address in the active symbol table.
    SymbolId(SymbolId),
    /// An Ion 1.1 system symbol.
    ///
    /// In Ion 1.0, the system symbol table is a permanent prefix to the active symbol table.
    /// Ion 1.0 system symbols are encoded using an address in the active symbol table just like
    /// application symbols, they just have an address lower than `$10`.
    ///
    /// In Ion 1.1, system symbols have their own address space. This variant represents a symbol
    /// in that address space, indicating that its corresponding text should be resolved in the
    /// system symbol table rather than the active symbol table.
    SystemSymbol_1_1(SystemSymbol_1_1),
    /// A text literal. In Ion 1.1, this can also represent text from the system symbol table.
    Text(&'a str),
}

impl PartialEq for RawSymbolRef<'_> {
    fn eq(&self, other: &Self) -> bool {
        use RawSymbolRef::*;
        match (self, other) {
            (SymbolId(sid1), SymbolId(sid2)) => sid1 == sid2,
            (Text(text1), Text(text2)) => text1 == text2,
            (SystemSymbol_1_1(address1), SystemSymbol_1_1(address2)) => address1 == address2,
            // SystemSymbol_1_1 instances are guaranteed to have associated text, so we can compare them to
            // text literals for equality.
            (SystemSymbol_1_1(symbol), Text(text)) | (Text(text), SystemSymbol_1_1(symbol)) => {
                symbol.text() == *text
            }
            _ => false,
        }
    }
}

impl<'a> RawSymbolRef<'a> {
    /// Returns `true` if this token matches either the specified symbol ID or text value.
    /// This is useful for comparing tokens that represent system symbol values of an unknown
    /// encoding.
    pub fn matches_sid_or_text(&self, symbol_id: SymbolId, symbol_text: &str) -> bool {
        match self {
            RawSymbolRef::SymbolId(sid) => symbol_id == *sid,
            RawSymbolRef::Text(text) => symbol_text == *text,
            // XXX: This method doesn't make much sense now that Ion 1.1 system symbols have their
            //      own address space.
            RawSymbolRef::SystemSymbol_1_1(system_symbol) => symbol_text == system_symbol.text(),
        }
    }

    pub fn is_unknown_text(&self) -> bool {
        self.is_symbol_id(0)
    }

    pub fn is_symbol_id(&self, symbol_id: SymbolId) -> bool {
        matches!(self, RawSymbolRef::SymbolId(s) if *s == symbol_id)
    }

    pub fn resolve(
        self,
        label: &'static str,
        context: EncodingContextRef<'a>,
    ) -> IonResult<SymbolRef<'a>> {
        let symbol = match self {
            RawSymbolRef::SymbolId(sid) => context
                .symbol_table()
                .symbol_for(sid)
                .ok_or_else(
                    #[inline(never)]
                    || {
                        IonError::decoding_error(format!(
                            "found {label} symbol ID (${}) that was not in the symbol table\n{:?}",
                            sid,
                            context.symbol_table()
                        ))
                    },
                )?
                .into(),
            RawSymbolRef::SystemSymbol_1_1(symbol) => symbol.text().into(),
            RawSymbolRef::Text(text) => text.into(),
        };
        Ok(symbol)
    }
}

/// Implemented by types that can be viewed as a [RawSymbolRef] without allocations.
pub trait AsRawSymbolRef {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef;
}

impl<'a> AsRawSymbolRef for RawSymbolRef<'a> {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef {
        *self
    }
}

impl AsRawSymbolRef for SymbolId {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef {
        RawSymbolRef::SymbolId(*self)
    }
}

impl AsRawSymbolRef for &str {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef {
        RawSymbolRef::Text(self)
    }
}

impl AsRawSymbolRef for Symbol {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef {
        match self.text() {
            Some(text) => RawSymbolRef::Text(text),
            None => RawSymbolRef::SymbolId(0),
        }
    }
}

impl<T> AsRawSymbolRef for &T
where
    T: AsRawSymbolRef,
{
    fn as_raw_symbol_ref(&self) -> RawSymbolRef {
        (*self).as_raw_symbol_ref()
    }
}

impl<'a, 'b> From<&'a RawSymbolRef<'b>> for RawSymbolRef<'a> {
    fn from(value: &'a RawSymbolRef<'b>) -> Self {
        *value
    }
}

impl<'a> From<&'a str> for RawSymbolRef<'a> {
    fn from(value: &'a str) -> Self {
        RawSymbolRef::Text(value)
    }
}

impl<'a> From<&'a &str> for RawSymbolRef<'a> {
    fn from(value: &'a &str) -> Self {
        RawSymbolRef::Text(value)
    }
}

impl<'a> From<SymbolId> for RawSymbolRef<'a> {
    fn from(value: SymbolId) -> Self {
        RawSymbolRef::SymbolId(value)
    }
}

impl<'a> From<&'a SymbolId> for RawSymbolRef<'a> {
    fn from(value: &'a SymbolId) -> Self {
        RawSymbolRef::SymbolId(*value)
    }
}

impl<'a> From<SymbolRef<'a>> for RawSymbolRef<'a> {
    fn from(value: SymbolRef<'a>) -> Self {
        match value.text() {
            None => RawSymbolRef::SymbolId(0),
            Some(text) => RawSymbolRef::Text(text),
        }
    }
}

impl<'a> From<&'a Symbol> for RawSymbolRef<'a> {
    fn from(value: &'a Symbol) -> Self {
        value.as_raw_symbol_ref()
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct SystemSymbol_1_1(SymbolAddress);

impl SystemSymbol_1_1 {
    /// Creates a new instance of this type **without range checking the address.**
    /// It should only be used when the address passed in has already been confirmed to be in range.
    pub const fn new_unchecked(symbol_address: SymbolAddress) -> Self {
        Self(symbol_address)
    }

    /// Creates a new system symbol if the provided address is non-zero and in range for the
    /// corresponding system symbol table.
    fn new(symbol_address: SymbolAddress) -> Option<Self> {
        match symbol_address {
            0 => None,
            address if address >= Self::system_symbol_table().len() => None,
            address => Some(Self::new_unchecked(address)),
        }
    }

    /// Constructs a system symbol from the provided address, returning `Ok(symbol)`.
    /// If the provided address is zero or out of bounds, returns an `Err`.
    #[inline]
    fn try_new(symbol_address: SymbolAddress) -> IonResult<Self> {
        Self::new(symbol_address).ok_or_else(|| {
            ice!(IonError::decoding_error(format!(
                "system symbol address {symbol_address} is out of bounds"
            )))
        })
    }

    #[inline]
    pub fn system_symbol_table() -> &'static SystemSymbolTable {
        SYSTEM_SYMBOLS_1_1
    }

    pub const fn address(&self) -> SymbolAddress {
        self.0
    }

    pub fn text(&self) -> &'static str {
        // TODO: `NonZeroUsize` might offer minor optimization opportunities around system
        //       symbol representation/resolution.
        //
        // https://doc.rust-lang.org/std/num/type.NonZeroUsize.html

        // The address has been confirmed to be non-zero and in bounds
        Self::system_symbol_table().symbols_by_address()[self.address() - 1]
    }
}

impl AsRawSymbolRef for SystemSymbol_1_1 {
    fn as_raw_symbol_ref(&self) -> RawSymbolRef {
        // In Ion 1.1, system symbols have their own address space.
        RawSymbolRef::SystemSymbol_1_1(*self)
    }
}
