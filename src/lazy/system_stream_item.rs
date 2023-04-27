use crate::lazy::binary::lazy_system_reader::{LazyStruct, LazyValue};
use crate::result::{decoding_error, decoding_error_raw};
use crate::IonResult;
use std::fmt::{Debug, Formatter};

/// Raw stream elements that a SystemReader may encounter.
pub enum SystemStreamItem<'top, 'data> {
    VersionMarker(u8, u8),
    SymbolTable(LazyStruct<'top, 'data>),
    Value(LazyValue<'top, 'data>),
    Nothing,
}

impl<'top, 'data> Debug for SystemStreamItem<'top, 'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SystemStreamItem::VersionMarker(major, minor) => {
                write!(f, "version marker v{}.{}", major, minor)
            }
            SystemStreamItem::SymbolTable(_) => write!(f, "a symbol table"),
            SystemStreamItem::Value(value) => write!(f, "{}", value.ion_type()),
            SystemStreamItem::Nothing => write!(f, "<nothing>"),
        }
    }
}

impl<'top, 'data> SystemStreamItem<'top, 'data> {
    pub fn version_marker(&self) -> Option<(u8, u8)> {
        if let Self::VersionMarker(major, minor) = self {
            Some((*major, *minor))
        } else {
            None
        }
    }

    pub fn expect_ivm(self) -> IonResult<(u8, u8)> {
        self.version_marker()
            .ok_or_else(|| decoding_error_raw(format!("expected IVM, found {:?}", self)))
    }

    pub fn value(&self) -> Option<&LazyValue<'top, 'data>> {
        if let Self::Value(value) = self {
            Some(value)
        } else {
            None
        }
    }

    pub fn expect_value(self) -> IonResult<LazyValue<'top, 'data>> {
        if let Self::Value(value) = self {
            Ok(value)
        } else {
            decoding_error(format!("expected value, found {:?}", self))
        }
    }
}
