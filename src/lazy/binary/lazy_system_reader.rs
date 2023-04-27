use crate::element::builders::StructBuilder;
use crate::element::{Annotations, Element, IntoAnnotatedElement, Sequence, Struct, Value};
use crate::result::{decoding_error, decoding_error_raw};
use crate::{IonError, IonResult, IonType, RawSymbolTokenRef, SymbolRef, SymbolTable};
use std::fmt;
use std::fmt::{Debug, Formatter};

use crate::lazy::binary::raw::lazy_raw_reader::LazyRawBinaryReader;
use crate::lazy::binary::raw::lazy_raw_sequence::{LazyRawSequence, RawSequenceIterator};
use crate::lazy::binary::raw::lazy_raw_struct::{LazyRawStruct, RawStructIterator};
use crate::lazy::binary::raw::lazy_raw_value::LazyRawValue;
use crate::lazy::binary::raw::raw_annotations_iterator::RawAnnotationsIterator;
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::value_ref::ValueRef;

impl<'top, 'data> Debug for LazySequence<'top, 'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut reader = self.iter();
        match self.ion_type() {
            IonType::SExp => {
                write!(f, "(")?;
                while let Some(value) = reader.next().map_err(|_| fmt::Error)? {
                    write!(f, "{:?} ", value.read().map_err(|_| fmt::Error)?)?;
                }
                write!(f, ")")?;
            }
            IonType::List => {
                write!(f, "[")?;
                while let Some(value) = reader.next().map_err(|_| fmt::Error)? {
                    write!(f, "{:?},", value.read().map_err(|_| fmt::Error)?)?;
                }
                write!(f, "]")?;
            }
            _ => unreachable!("LazySequence is only created for list and sexp"),
        }

        Ok(())
    }
}

impl<'top, 'data> Debug for LazyField<'top, 'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{}: {:?}",
            self.name().map_err(|_| fmt::Error)?.text().unwrap_or("$0"),
            self.value().read().map_err(|_| fmt::Error)?,
        )
    }
}

impl<'top, 'data> Debug for LazyStruct<'top, 'data> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        let mut reader = self.iter();
        write!(f, "{{")?;
        while let Some(field) = reader.next_field().map_err(|_| fmt::Error)? {
            let name = field.name().map_err(|_| fmt::Error)?;
            let lazy_value = field.value();
            let value = lazy_value.read().map_err(|_| fmt::Error)?;
            write!(f, "{}:{:?},", name.text().unwrap_or("$0"), value)?;
        }
        write!(f, "}}")?;
        Ok(())
    }
}

pub struct SequenceIterator<'top, 'data> {
    raw_sequence_reader: RawSequenceIterator<'data>,
    symbol_table: &'top SymbolTable,
}

pub struct StructIterator<'top, 'data> {
    raw_struct_reader: RawStructIterator<'data>,
    symbol_table: &'top SymbolTable,
}

#[derive(Clone)]
pub struct LazyValue<'top, 'data> {
    raw_value: LazyRawValue<'data>,
    symbol_table: &'top SymbolTable,
}

pub struct LazySequence<'top, 'data> {
    raw_sequence: LazyRawSequence<'data>,
    symbol_table: &'top SymbolTable,
}

pub struct LazyStruct<'top, 'data> {
    raw_struct: LazyRawStruct<'data>,
    symbol_table: &'top SymbolTable,
}

pub struct LazyField<'top, 'data> {
    value: LazyValue<'top, 'data>,
}

impl<'top, 'data> TryFrom<LazyValue<'top, 'data>> for Element {
    type Error = IonError;

    fn try_from(value: LazyValue<'top, 'data>) -> Result<Self, Self::Error> {
        let annotations: Annotations = value.annotations().try_into()?;
        let value = Value::try_from(value.read()?)?;
        Ok(value.with_annotations(annotations))
    }
}

impl<'top, 'data> TryFrom<LazySequence<'top, 'data>> for Sequence {
    type Error = IonError;

    fn try_from(lazy_sequence: LazySequence<'top, 'data>) -> Result<Self, Self::Error> {
        let sequence: Sequence = lazy_sequence
            .iter()
            .map(|v| Element::try_from(v?))
            .collect::<IonResult<Vec<_>>>()?
            .into();
        Ok(sequence)
    }
}

impl<'top, 'data> TryFrom<LazySequence<'top, 'data>> for Element {
    type Error = IonError;

    fn try_from(lazy_sequence: LazySequence<'top, 'data>) -> Result<Self, Self::Error> {
        let ion_type = lazy_sequence.ion_type();
        let annotations: Annotations = lazy_sequence.annotations().try_into()?;
        let sequence: Sequence = lazy_sequence.try_into()?;
        let value = match ion_type {
            IonType::SExp => Value::SExp(sequence),
            IonType::List => Value::List(sequence),
            _ => unreachable!("no other IonTypes are sequences"),
        };
        Ok(value.with_annotations(annotations))
    }
}

impl<'top, 'data> TryFrom<LazyStruct<'top, 'data>> for Struct {
    type Error = IonError;

    fn try_from(lazy_struct: LazyStruct<'top, 'data>) -> Result<Self, Self::Error> {
        let mut builder = StructBuilder::new();
        for field in &lazy_struct {
            let field = field?;
            builder = builder.with_field(field.name()?, Element::try_from(field.value().clone())?);
        }
        Ok(builder.build())
    }
}

impl<'top, 'data> TryFrom<LazyStruct<'top, 'data>> for Element {
    type Error = IonError;

    fn try_from(lazy_struct: LazyStruct<'top, 'data>) -> Result<Self, Self::Error> {
        let annotations: Annotations = lazy_struct.annotations().try_into()?;
        let struct_: Struct = lazy_struct.try_into()?;
        Ok(struct_.with_annotations(annotations))
    }
}

impl<'top, 'data> Iterator for StructIterator<'top, 'data> {
    type Item = IonResult<LazyField<'top, 'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        StructIterator::next_field(self).transpose()
    }
}

impl<'a, 'top, 'data> IntoIterator for &'a LazyStruct<'top, 'data> {
    type Item = IonResult<LazyField<'top, 'data>>;
    type IntoIter = StructIterator<'top, 'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'top, 'data> LazySequence<'top, 'data> {
    pub fn ion_type(&self) -> IonType {
        self.raw_sequence.ion_type()
    }

    pub fn iter(&self) -> SequenceIterator<'top, 'data> {
        SequenceIterator {
            raw_sequence_reader: self.raw_sequence.iter(),
            symbol_table: &self.symbol_table,
        }
    }

    pub fn annotations(&self) -> AnnotationsIterator<'top, 'data> {
        AnnotationsIterator {
            raw_annotations: self.raw_sequence.value.annotations(),
            symbol_table: self.symbol_table,
            initial_offset: self
                .raw_sequence
                .value
                .encoded_value
                .annotations_offset()
                .unwrap_or_else(|| self.raw_sequence.value.encoded_value.header_offset),
        }
    }
}

impl<'a, 'top, 'data> IntoIterator for &'a LazySequence<'top, 'data> {
    type Item = IonResult<LazyValue<'top, 'data>>;
    type IntoIter = SequenceIterator<'top, 'data>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'top, 'data> LazyStruct<'top, 'data> {
    pub fn iter(&self) -> StructIterator<'top, 'data> {
        StructIterator {
            raw_struct_reader: self.raw_struct.iter(),
            symbol_table: &self.symbol_table,
        }
    }

    pub fn annotations(&self) -> AnnotationsIterator<'top, 'data> {
        AnnotationsIterator {
            raw_annotations: self.raw_struct.value.annotations(),
            symbol_table: &self.symbol_table,
            initial_offset: self
                .raw_struct
                .value
                .encoded_value
                .annotations_offset()
                .unwrap_or_else(|| self.raw_struct.value.encoded_value.header_offset),
        }
    }
}

impl<'top, 'data> LazyField<'top, 'data> {
    pub fn name(&self) -> IonResult<SymbolRef<'top>> {
        let field_sid = self.value.raw_value.field_name().unwrap();
        self.value
            .symbol_table
            .symbol_for(field_sid)
            .map(|symbol| symbol.into())
            .ok_or_else(|| decoding_error_raw("found a symbol ID that was not in the symbol table"))
    }

    pub fn value(&self) -> &LazyValue<'top, 'data> {
        &self.value
    }
}

impl<'top, 'data> StructIterator<'top, 'data> {
    pub fn next_field(&mut self) -> IonResult<Option<LazyField<'top, 'data>>> {
        let raw_field = self.raw_struct_reader.next()?;
        if let Some(raw_field) = raw_field {
            let lazy_value = LazyValue {
                raw_value: raw_field.into_value(),
                symbol_table: &self.symbol_table,
            };
            let lazy_field = LazyField { value: lazy_value };
            return Ok(Some(lazy_field));
        }
        Ok(None)
    }
}

impl<'top, 'data> SequenceIterator<'top, 'data> {
    pub fn next(&mut self) -> IonResult<Option<LazyValue<'top, 'data>>> {
        let raw_value = self.raw_sequence_reader.next()?;
        if let Some(raw_value) = raw_value {
            let lazy_value = LazyValue {
                raw_value,
                symbol_table: &self.symbol_table,
            };
            return Ok(Some(lazy_value));
        }
        Ok(None)
    }
}

impl<'top, 'data> Iterator for SequenceIterator<'top, 'data> {
    type Item = IonResult<LazyValue<'top, 'data>>;

    fn next(&mut self) -> Option<Self::Item> {
        SequenceIterator::next(self).transpose()
    }
}

impl<'top, 'data> LazyValue<'top, 'data> {
    pub(crate) fn new(
        symbol_table: &'top SymbolTable,
        raw_value: LazyRawValue<'data>,
    ) -> LazyValue<'top, 'data> {
        LazyValue {
            raw_value,
            symbol_table,
        }
    }

    pub fn ion_type(&self) -> IonType {
        self.raw_value.ion_type()
    }

    pub fn annotations(&self) -> AnnotationsIterator {
        AnnotationsIterator {
            raw_annotations: self.raw_value.annotations(),
            symbol_table: &self.symbol_table,
            initial_offset: self
                .raw_value
                .encoded_value
                .annotations_offset()
                .unwrap_or_else(|| self.raw_value.encoded_value.header_offset),
        }
    }

    pub fn read(&self) -> IonResult<ValueRef> {
        use RawValueRef::*;
        let value_ref = match self.raw_value.read()? {
            Null(ion_type) => ValueRef::Null(ion_type),
            Bool(b) => ValueRef::Bool(b),
            Int(i) => ValueRef::Int(i),
            Float(f) => ValueRef::Float(f),
            Decimal(d) => ValueRef::Decimal(d),
            Timestamp(t) => ValueRef::Timestamp(t),
            String(s) => ValueRef::String(s),
            Symbol(s) => {
                let symbol = match s {
                    RawSymbolTokenRef::SymbolId(sid) => self
                        .symbol_table
                        .symbol_for(sid)
                        .ok_or_else(|| {
                            decoding_error_raw("found a symbol ID that was not in the symbol table")
                        })?
                        .into(),
                    RawSymbolTokenRef::Text(text) => text.into(),
                };
                ValueRef::Symbol(symbol)
            }
            Blob(b) => ValueRef::Blob(b),
            Clob(c) => ValueRef::Clob(c),
            SExp(s) => {
                let lazy_sequence = LazySequence {
                    raw_sequence: s,
                    symbol_table: &self.symbol_table,
                };
                ValueRef::SExp(lazy_sequence)
            }
            List(l) => {
                let lazy_sequence = LazySequence {
                    raw_sequence: l,
                    symbol_table: &self.symbol_table,
                };
                ValueRef::List(lazy_sequence)
            }
            Struct(s) => {
                let lazy_struct = LazyStruct {
                    raw_struct: s,
                    symbol_table: &self.symbol_table,
                };
                ValueRef::Struct(lazy_struct)
            }
        };
        Ok(value_ref)
    }
}

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
pub struct AnnotationsIterator<'top, 'data> {
    symbol_table: &'top SymbolTable,
    raw_annotations: RawAnnotationsIterator<'data>,
    initial_offset: usize,
}

impl<'top, 'data> Iterator for AnnotationsIterator<'top, 'data>
where
    'data: 'top,
{
    type Item = IonResult<SymbolRef<'top>>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_annotation = self.raw_annotations.next()?;
        match raw_annotation {
            Ok(RawSymbolTokenRef::SymbolId(sid)) => match self.symbol_table.symbol_for(sid) {
                None => Some(decoding_error(
                    "found a symbol ID that was not in the symbol table",
                )),
                Some(symbol) => Some(Ok(symbol.into())),
            },
            Ok(RawSymbolTokenRef::Text(text)) => Some(Ok(SymbolRef::with_text(text))),
            Err(e) => Some(Err(e)),
        }
    }
}

impl<'top, 'data> TryFrom<AnnotationsIterator<'top, 'data>> for Annotations {
    type Error = IonError;

    fn try_from(iter: AnnotationsIterator<'top, 'data>) -> Result<Self, Self::Error> {
        let annotations = iter
            .map(|symbol_ref| match symbol_ref {
                Ok(symbol_ref) => Ok(symbol_ref.to_owned()),
                Err(e) => Err(e),
            })
            .collect::<IonResult<Vec<_>>>()?;
        Ok(Annotations::from(annotations))
    }
}

struct PendingLst {
    is_lst_append: bool,
    symbols: Vec<Option<String>>,
}

// TODO: Make generic over any impl of (not yet created) trait LazyRawReader
pub struct LazySystemReader<'data> {
    raw_reader: LazyRawBinaryReader<'data>,
    symbol_table: SymbolTable,
    pending_lst: PendingLst,
}

impl<'data> LazySystemReader<'data> {
    pub(crate) fn new(ion_data: &'data [u8]) -> LazySystemReader<'data> {
        let raw_reader = LazyRawBinaryReader::new(ion_data);
        LazySystemReader {
            raw_reader,
            symbol_table: SymbolTable::new(),
            pending_lst: PendingLst {
                is_lst_append: false,
                symbols: Vec::new(),
            },
        }
    }

    fn is_symbol_table_struct(lazy_value: &LazyRawValue) -> IonResult<bool> {
        let is_struct = lazy_value.ion_type() == IonType::Struct;
        if !is_struct {
            return Ok(false);
        }
        if let Some(symbol_ref) = lazy_value.annotations().next() {
            return Ok(symbol_ref? == RawSymbolTokenRef::SymbolId(3));
        };
        Ok(false)
    }

    pub fn next<'top>(&'top mut self) -> IonResult<SystemStreamItem<'top, 'data>> {
        let LazySystemReader {
            raw_reader,
            symbol_table,
            pending_lst,
        } = self;
        Self::apply_pending_lst(symbol_table, pending_lst);
        let lazy_raw_value = match raw_reader.next()? {
            RawStreamItem::VersionMarker(major, minor) => {
                return Ok(SystemStreamItem::VersionMarker(major, minor));
            }
            RawStreamItem::Value(lazy_raw_value) => lazy_raw_value,
            RawStreamItem::Nothing => return Ok(SystemStreamItem::Nothing),
        };
        if Self::is_symbol_table_struct(&lazy_raw_value)? {
            Self::process_symbol_table(pending_lst, &lazy_raw_value)?;
            let lazy_struct = LazyStruct {
                raw_struct: LazyRawStruct {
                    value: lazy_raw_value,
                },
                symbol_table: symbol_table,
            };
            return Ok(SystemStreamItem::SymbolTable(lazy_struct));
        }
        let lazy_value = LazyValue::new(symbol_table, lazy_raw_value);
        Ok(SystemStreamItem::Value(lazy_value))
    }

    // It would make more sense for this logic to live in the user-level `LazyReader` as a simple
    // loop over LazySystemReader::next. However, due to a limitation in the borrow checker[1], it's
    // not able to determine that calling next() multiple times is safe. Rust's experimental
    // borrow checker, Polonius, is able to understand it. In the meantime,
    // [1]: https://github.com/rust-lang/rust/issues/70255
    pub fn next_user_value<'top>(&'top mut self) -> IonResult<Option<LazyValue<'top, 'data>>> {
        let LazySystemReader {
            raw_reader,
            symbol_table,
            pending_lst,
        } = self;
        loop {
            Self::apply_pending_lst(symbol_table, pending_lst);
            let lazy_raw_value = match raw_reader.next()? {
                RawStreamItem::VersionMarker(_, _) => continue,
                RawStreamItem::Value(lazy_raw_value) => lazy_raw_value,
                RawStreamItem::Nothing => return Ok(None),
            };
            if Self::is_symbol_table_struct(&lazy_raw_value)? {
                // process the symbol table, but do not surface it
                Self::process_symbol_table(pending_lst, &lazy_raw_value)?;
            } else {
                return Ok(Some(LazyValue::new(symbol_table, lazy_raw_value)));
            }
        }
    }

    fn apply_pending_lst(symbol_table: &mut SymbolTable, pending_lst: &mut PendingLst) {
        if pending_lst.symbols.is_empty() {
            return;
        }
        if !pending_lst.is_lst_append {
            // We're setting the symbols list, not appending to it.
            symbol_table.reset();
        }
        for symbol in pending_lst.symbols.drain(..) {
            symbol_table.intern_or_add_placeholder(symbol);
        }
        pending_lst.is_lst_append = false;
    }

    fn process_symbol_table(
        pending_lst: &mut PendingLst,
        symbol_table: &LazyRawValue,
    ) -> IonResult<()> {
        // We've already confirmed this is an annotated struct
        let symbol_table = symbol_table.read()?.expect_struct()?;
        // Assume it's not an LST append unless we found `imports: $ion_symbol_table`
        pending_lst.is_lst_append = false;
        let mut fields = symbol_table.iter();
        let mut found_symbols_field = false;
        let mut found_imports_field = false;

        // TODO: Add a symbol_id() method to RawSymbolTokenRef

        while let Some(field) = fields.next()? {
            if field.name() == RawSymbolTokenRef::SymbolId(7) {
                if found_symbols_field {
                    return decoding_error("found symbol table with multiple 'symbols' fields");
                }
                found_symbols_field = true;
                Self::process_symbols(pending_lst, field.value())?;
            }
            if field.name() == RawSymbolTokenRef::SymbolId(6) {
                if found_imports_field {
                    return decoding_error("found symbol table with multiple 'imports' fields");
                }
                found_imports_field = true;
                Self::process_imports(pending_lst, field.value())?;
            }
            // Ignore other fields
        }
        Ok(())
    }

    fn process_symbols(pending_lst: &mut PendingLst, symbols: &LazyRawValue) -> IonResult<()> {
        if let RawValueRef::List(list) = symbols.read()? {
            let mut reader = list.iter();
            while let Some(value) = reader.next()? {
                if let RawValueRef::String(text) = value.read()? {
                    pending_lst.symbols.push(Some(text.to_owned()))
                } else {
                    pending_lst.symbols.push(None)
                }
            }
        }
        // Nulls and non-list values are ignored.
        Ok(())
    }

    fn process_imports(pending_lst: &mut PendingLst, imports: &LazyRawValue) -> IonResult<()> {
        match imports.read()? {
            RawValueRef::Symbol(symbol_ref) => {
                if symbol_ref == RawSymbolTokenRef::SymbolId(3) {
                    pending_lst.is_lst_append = true;
                }
                // Any other symbol is ignored
            }
            RawValueRef::List(_) => {
                return decoding_error(
                    "This implementation does not yet support shared symbol table imports",
                );
            }
            _ => {
                // Nulls and other types are ignored
            }
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::element::writer::ElementWriter;
    use crate::element::Element;
    use crate::lazy::binary::lazy_system_reader::LazySystemReader;
    use crate::lazy::system_stream_item::SystemStreamItem;
    use crate::{BinaryWriterBuilder, IonResult, IonWriter};

    fn to_binary_ion(text_ion: &str) -> IonResult<Vec<u8>> {
        let mut buffer = Vec::new();
        let mut writer = BinaryWriterBuilder::default().build(&mut buffer)?;
        let elements = Element::read_all(text_ion)?;
        writer.write_elements(&elements)?;
        writer.flush()?;
        drop(writer);
        Ok(buffer)
    }

    #[test]
    fn try_it() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        foo
        bar
        $ion_symbol_table
        baz
        name
        gary
        imports
        hello
        "#,
        )?;
        let mut system_reader = LazySystemReader::new(&ion_data);
        loop {
            match system_reader.next()? {
                SystemStreamItem::VersionMarker(major, minor) => {
                    println!("ivm => v{}.{}", major, minor)
                }
                SystemStreamItem::SymbolTable(ref s) => println!("symtab => {:?}", s),
                SystemStreamItem::Value(ref v) => println!("value => {:?}", v.read()?),
                SystemStreamItem::Nothing => break,
            }
        }
        Ok(())
    }

    #[test]
    fn sequence_iter() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        (
          (foo baz baz)
          (1 2 3)
          (a b c)
        )
        "#,
        )?;
        let mut system_reader = LazySystemReader::new(&ion_data);
        loop {
            match system_reader.next()? {
                SystemStreamItem::Value(value) => {
                    for value in &value.read()?.expect_sexp()? {
                        println!("{:?}", value?.read()?);
                    }
                }
                SystemStreamItem::Nothing => break,
                _ => {}
            }
        }
        Ok(())
    }

    #[test]
    fn struct_iter() -> IonResult<()> {
        let ion_data = to_binary_ion(
            r#"
        {
          foo: 1,
          bar: true,
          baz: null.symbol,
          quux: "hello"
        }
        "#,
        )?;
        let mut system_reader = LazySystemReader::new(&ion_data);
        loop {
            match system_reader.next()? {
                SystemStreamItem::Value(value) => {
                    for field in &value.read()?.expect_struct()? {
                        let field = field?;
                        println!("{:?}: {:?},", field.name()?, field.value().read()?);
                    }
                }
                SystemStreamItem::Nothing => break,
                _ => {}
            }
        }
        Ok(())
    }
}
