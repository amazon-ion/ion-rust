use crate::result::{decoding_error, decoding_error_raw};
use crate::{IonResult, IonType, RawSymbolTokenRef, Symbol, SymbolRef, SymbolTable};
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::rc::Rc;

use crate::lazy::binary::lazy_raw_reader::{
    LazyRawBinaryReader, LazyRawSequence, LazyRawStruct, LazyRawValue, RawAnnotationsIterator,
    RawSequenceIterator, RawStructIterator,
};
use crate::lazy::raw_stream_item::RawStreamItem;
use crate::lazy::raw_value_ref::RawValueRef;
use crate::lazy::system_stream_item::SystemStreamItem;
use crate::lazy::value_ref::ValueRef;

impl<'a> Debug for LazySequence<'a> {
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

impl<'a> Debug for LazyField<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}: {:?}",
            self.name().map_err(|_| fmt::Error)?.text().unwrap_or("$0"),
            self.value().read().map_err(|_| fmt::Error)?,
        )
    }
}

impl<'a> Debug for LazyStruct<'a> {
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

pub struct SequenceIterator<'a> {
    raw_sequence_reader: RawSequenceIterator<'a>,
    symbol_table: Rc<SymbolTable>,
}

pub struct StructIterator<'a> {
    raw_struct_reader: RawStructIterator<'a>,
    symbol_table: Rc<SymbolTable>,
}

pub struct LazyValue<'a> {
    raw_value: LazyRawValue<'a>,
    symbol_table: Rc<SymbolTable>,
}

pub struct LazySequence<'a> {
    raw_sequence: LazyRawSequence<'a>,
    symbol_table: Rc<SymbolTable>,
}

pub struct LazyStruct<'a> {
    raw_struct: LazyRawStruct<'a>,
    symbol_table: Rc<SymbolTable>,
}

pub struct LazyField<'a> {
    value: LazyValue<'a>,
}

impl<'a> Iterator for StructIterator<'a> {
    type Item = IonResult<LazyField<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        StructIterator::next_field(self).transpose()
    }
}

impl<'a, 'b> IntoIterator for &'b LazyStruct<'a>
where
    'a: 'b,
{
    type Item = IonResult<LazyField<'a>>;
    type IntoIter = StructIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> LazySequence<'a> {
    pub fn ion_type(&self) -> IonType {
        self.raw_sequence.ion_type()
    }

    pub fn iter(&self) -> SequenceIterator<'a> {
        SequenceIterator {
            raw_sequence_reader: self.raw_sequence.iter(),
            symbol_table: Rc::clone(&self.symbol_table),
        }
    }
}

impl<'a, 'b> IntoIterator for &'b LazySequence<'a>
where
    'a: 'b,
{
    type Item = IonResult<LazyValue<'a>>;
    type IntoIter = SequenceIterator<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> LazyStruct<'a> {
    pub fn iter(&self) -> StructIterator<'a> {
        StructIterator {
            raw_struct_reader: self.raw_struct.iter(),
            symbol_table: Rc::clone(&self.symbol_table),
        }
    }
}

impl<'a> LazyField<'a> {
    pub fn name(&self) -> IonResult<SymbolRef> {
        let field_sid = self.value.raw_value.field_name().unwrap();
        self.value
            .symbol_table
            .symbol_for(field_sid)
            .map(|symbol| symbol.into())
            .ok_or_else(|| decoding_error_raw("found a symbol ID that was not in the symbol table"))
    }

    pub fn value(&self) -> &LazyValue<'a> {
        &self.value
    }
}

impl<'a> StructIterator<'a> {
    pub fn next_field(&mut self) -> IonResult<Option<LazyField<'a>>> {
        let raw_field = self.raw_struct_reader.next_field()?;
        if let Some(raw_field) = raw_field {
            let lazy_value = LazyValue {
                raw_value: raw_field.into_value(),
                symbol_table: Rc::clone(&self.symbol_table),
            };
            let lazy_field = LazyField { value: lazy_value };
            return Ok(Some(lazy_field));
        }
        Ok(None)
    }
}

impl<'a> SequenceIterator<'a> {
    pub fn next(&mut self) -> IonResult<Option<LazyValue<'a>>> {
        let raw_value = self.raw_sequence_reader.next()?;
        if let Some(raw_value) = raw_value {
            let lazy_value = LazyValue {
                raw_value,
                symbol_table: Rc::clone(&self.symbol_table),
            };
            return Ok(Some(lazy_value));
        }
        Ok(None)
    }
}

impl<'a> Iterator for SequenceIterator<'a> {
    type Item = IonResult<LazyValue<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        SequenceIterator::next(self).transpose()
    }
}

impl<'a> LazyValue<'a> {
    pub fn ion_type(&self) -> IonType {
        self.raw_value.ion_type()
    }

    pub fn annotations(&self) -> AnnotationsIterator<'a> {
        AnnotationsIterator {
            raw_annotations: self.raw_value.annotations(),
            symbol_table: Rc::clone(&self.symbol_table),
            initial_offset: self
                .raw_value
                .encoded_value
                .annotations_offset()
                .unwrap_or_else(|| self.raw_value.encoded_value.header_offset),
        }
    }

    pub fn read(&self) -> IonResult<ValueRef<'a>> {
        use super::raw_value_ref::RawValueRef::*;
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
                        .to_owned(),
                    RawSymbolTokenRef::Text(text) => text.into(),
                };
                ValueRef::Symbol(symbol)
            }
            Blob(b) => ValueRef::Blob(b),
            Clob(c) => ValueRef::Clob(c),
            SExp(s) => {
                let lazy_sequence = LazySequence {
                    raw_sequence: s,
                    symbol_table: Rc::clone(&self.symbol_table),
                };
                ValueRef::SExp(lazy_sequence)
            }
            List(l) => {
                let lazy_sequence = LazySequence {
                    raw_sequence: l,
                    symbol_table: Rc::clone(&self.symbol_table),
                };
                ValueRef::List(lazy_sequence)
            }
            Struct(s) => {
                let lazy_struct = LazyStruct {
                    raw_struct: s,
                    symbol_table: Rc::clone(&self.symbol_table),
                };
                ValueRef::Struct(lazy_struct)
            }
        };
        Ok(value_ref)
    }
}

/// Iterates over a slice of bytes, lazily reading them as a sequence of VarUInt symbol IDs.
pub struct AnnotationsIterator<'a> {
    symbol_table: Rc<SymbolTable>,
    raw_annotations: RawAnnotationsIterator<'a>,
    initial_offset: usize,
}

impl<'a> Iterator for AnnotationsIterator<'a> {
    type Item = IonResult<Symbol>;

    fn next(&mut self) -> Option<Self::Item> {
        let raw_annotation = self.raw_annotations.next()?;
        match raw_annotation {
            Ok(RawSymbolTokenRef::SymbolId(sid)) => match self.symbol_table.symbol_for(sid) {
                None => Some(decoding_error(
                    "found a symbol ID that was not in the symbol table",
                )),
                Some(symbol) => Some(Ok(symbol.to_owned())),
            },
            Ok(RawSymbolTokenRef::Text(text)) => Some(Ok(text.into())),
            Err(e) => Some(Err(e)),
        }
    }
}

struct PendingLst<'a> {
    is_lst_append: bool,
    symbols: Vec<Option<&'a str>>,
}

// TODO: Make generic over any impl of (not yet created) trait LazyRawReader
pub struct LazySystemReader<'a> {
    raw_reader: LazyRawBinaryReader<'a>,
    symbol_table: Rc<SymbolTable>,
    pending_lst: PendingLst<'a>,
}

impl<'a> LazySystemReader<'a> {
    pub(crate) fn new(ion_data: &'a [u8]) -> Self {
        let raw_reader = LazyRawBinaryReader::new(ion_data);
        LazySystemReader {
            raw_reader,
            symbol_table: Rc::new(SymbolTable::new()),
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

    pub fn next(&mut self) -> IonResult<SystemStreamItem<'a>> {
        if !self.pending_lst.symbols.is_empty() {
            let symbol_table: &mut SymbolTable =
                Rc::get_mut(&mut self.symbol_table).expect("lifetimes prevent a strong count > 1");
            if !self.pending_lst.is_lst_append {
                // We're setting the symbols list, not appending to it.
                symbol_table.reset();
            }
            for symbol in self.pending_lst.symbols.drain(..) {
                symbol_table.intern_or_add_placeholder(symbol);
            }
            self.pending_lst.is_lst_append = false;
        }
        let stream_item = match self.raw_reader.next()? {
            RawStreamItem::VersionMarker(major, minor) => {
                SystemStreamItem::VersionMarker(major, minor)
            }
            RawStreamItem::Value(lazy_raw_value) => {
                // Temporarily break `self` apart into simultaneous mutable references to its
                // constituent fields.
                if Self::is_symbol_table_struct(&lazy_raw_value)? {
                    self.process_symbol_table(&lazy_raw_value)?;
                    let lazy_value = self.resolve_lazy_raw_value(lazy_raw_value);
                    SystemStreamItem::SymbolTable(lazy_value.read()?.expect_struct()?)
                } else {
                    let lazy_value = self.resolve_lazy_raw_value(lazy_raw_value);
                    SystemStreamItem::Value(lazy_value)
                }
            }
            RawStreamItem::Nothing => SystemStreamItem::Nothing,
        };
        Ok(stream_item)
    }

    fn resolve_lazy_raw_value(&mut self, raw_value: LazyRawValue<'a>) -> LazyValue<'a> {
        LazyValue {
            raw_value,
            symbol_table: Rc::clone(&self.symbol_table),
        }
    }

    fn process_symbol_table(&mut self, symbol_table: &LazyRawValue<'a>) -> IonResult<()> {
        // We've already confirmed this is an annotated struct
        let symbol_table = symbol_table.read()?.expect_struct()?;
        // Assume it's not an LST append unless we found `imports: $ion_symbol_table`
        self.pending_lst.is_lst_append = false;
        let mut fields = symbol_table.iter();
        let mut found_symbols_field = false;
        let mut found_imports_field = false;

        // TODO: Add a symbol_id() method to RawSymbolTokenRef

        while let Some(field) = fields.next_field()? {
            if field.name() == RawSymbolTokenRef::SymbolId(7) {
                if found_symbols_field {
                    return decoding_error("found symbol table with multiple 'symbols' fields");
                }
                found_symbols_field = true;
                self.process_symbols(field.value())?;
            }
            if field.name() == RawSymbolTokenRef::SymbolId(6) {
                if found_imports_field {
                    return decoding_error("found symbol table with multiple 'imports' fields");
                }
                found_imports_field = true;
                self.process_imports(field.value())?;
            }
            // Ignore other fields
        }
        Ok(())
    }

    fn process_symbols(&mut self, symbols: &LazyRawValue<'a>) -> IonResult<()> {
        if let RawValueRef::List(list) = symbols.read()? {
            let mut reader = list.iter();
            while let Some(value) = reader.next()? {
                if let RawValueRef::String(text) = value.read()? {
                    self.pending_lst.symbols.push(Some(text))
                } else {
                    self.pending_lst.symbols.push(None)
                }
            }
        }
        // Nulls and non-list values are ignored.
        Ok(())
    }

    fn process_imports(&mut self, imports: &LazyRawValue<'a>) -> IonResult<()> {
        match imports.read()? {
            RawValueRef::Symbol(symbol_ref) => {
                if symbol_ref == RawSymbolTokenRef::SymbolId(3) {
                    self.pending_lst.is_lst_append = true;
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
    use crate::lazy::lazy_system_reader::LazySystemReader;
    use crate::lazy::system_stream_item::SystemStreamItem;
    use crate::{BinaryWriterBuilder, IonResult, IonWriter};

    fn to_10n(text_ion: &str) -> IonResult<Vec<u8>> {
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
        let ion_data = to_10n(
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
        let ion_data = to_10n(
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
        let ion_data = to_10n(
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
