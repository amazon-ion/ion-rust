use crate::raw_symbol_token_ref::AsRawSymbolTokenRef;
use crate::result::{decoding_error, decoding_error_raw};
use crate::{IonResult, IonType, RawSymbolTokenRef, SymbolRef, SymbolTable};
use std::fmt;
use std::fmt::{Debug, Formatter};

use crate::constants::v1_0::system_symbol_ids;
use crate::lazy_reader::binary::lazy_raw_reader::{
    LazyRawBinaryReader, LazyRawSequence, LazyRawStruct, LazyRawValue, RawSequenceReader,
    RawStructReader,
};
use crate::lazy_reader::raw_stream_item::RawStreamItem;
use crate::lazy_reader::raw_value_ref::RawValueRef;
use crate::lazy_reader::system_stream_item::SystemStreamItem;
use crate::lazy_reader::value_ref::ValueRef;
use crate::symbol_ref::AsSymbolRef;

impl<'a> Debug for LazySequence<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut reader = self.reader();
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
        let mut reader = self.reader();
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

pub struct SequenceReader<'a> {
    raw_sequence_reader: RawSequenceReader<'a>,
    symbol_table: &'a SymbolTable,
}

pub struct StructReader<'a> {
    raw_struct_reader: RawStructReader<'a>,
    symbol_table: &'a SymbolTable,
}

pub struct LazyValue<'a> {
    raw_value: LazyRawValue<'a>,
    symbol_table: &'a SymbolTable,
}

pub struct LazySequence<'a> {
    raw_sequence: LazyRawSequence<'a>,
    symbol_table: &'a SymbolTable,
}

pub struct LazyStruct<'a> {
    raw_struct: LazyRawStruct<'a>,
    symbol_table: &'a SymbolTable,
}

pub struct LazyField<'a> {
    value: LazyValue<'a>,
}

impl<'a> Iterator for StructReader<'a> {
    type Item = IonResult<LazyField<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        StructReader::next_field(self).transpose()
    }
}

impl<'a, 'b> IntoIterator for &'b LazyStruct<'a>
where
    'a: 'b,
{
    type Item = IonResult<LazyField<'a>>;
    type IntoIter = StructReader<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.reader()
    }
}

impl<'a> LazySequence<'a> {
    pub fn ion_type(&self) -> IonType {
        self.raw_sequence.ion_type()
    }

    pub fn reader(&self) -> SequenceReader<'a> {
        SequenceReader {
            raw_sequence_reader: self.raw_sequence.reader(),
            symbol_table: self.symbol_table,
        }
    }
}

impl<'a, 'b> IntoIterator for &'b LazySequence<'a>
where
    'a: 'b,
{
    type Item = IonResult<LazyValue<'a>>;
    type IntoIter = SequenceReader<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.reader()
    }
}

impl<'a> LazyStruct<'a> {
    pub fn reader(&self) -> StructReader<'a> {
        StructReader {
            raw_struct_reader: self.raw_struct.reader(),
            symbol_table: self.symbol_table,
        }
    }
}

impl<'a> LazyField<'a> {
    pub fn name(&self) -> IonResult<SymbolRef<'a>> {
        let field_sid = self.value.raw_value.field_name().unwrap();
        self.value
            .symbol_table
            .symbol_for(field_sid)
            .map(|symbol| symbol.as_symbol_ref())
            .ok_or_else(|| decoding_error_raw("found a symbol ID that was not in the symbol table"))
    }

    pub fn value(&self) -> &LazyValue<'a> {
        &self.value
    }
}

impl<'a> StructReader<'a> {
    pub fn next_field(&mut self) -> IonResult<Option<LazyField<'a>>> {
        let raw_field = self.raw_struct_reader.next_field()?;
        if let Some(raw_field) = raw_field {
            let lazy_value = LazyValue {
                raw_value: raw_field.into_value(),
                symbol_table: self.symbol_table,
            };
            let lazy_field = LazyField { value: lazy_value };
            return Ok(Some(lazy_field));
        }
        Ok(None)
    }
}

impl<'a> SequenceReader<'a> {
    pub fn next(&mut self) -> IonResult<Option<LazyValue<'a>>> {
        let raw_value = self.raw_sequence_reader.next()?;
        if let Some(raw_value) = raw_value {
            let lazy_value = LazyValue {
                raw_value,
                symbol_table: self.symbol_table,
            };
            return Ok(Some(lazy_value));
        }
        Ok(None)
    }
}

impl<'a> Iterator for SequenceReader<'a> {
    type Item = IonResult<LazyValue<'a>>;

    fn next(&mut self) -> Option<Self::Item> {
        SequenceReader::next(self).transpose()
    }
}

impl<'a> LazyValue<'a> {
    pub fn ion_type(&self) -> IonType {
        self.raw_value.ion_type()
    }

    fn read(&self) -> IonResult<ValueRef<'a>> {
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
                let symbol_ref = match s {
                    RawSymbolTokenRef::SymbolId(sid) => self
                        .symbol_table
                        .symbol_for(sid)
                        .ok_or_else(|| {
                            decoding_error_raw("found a symbol ID that was not in the symbol table")
                        })?
                        .as_symbol_ref(),
                    RawSymbolTokenRef::Text(text) => SymbolRef::with_text(text),
                };
                ValueRef::Symbol(symbol_ref)
            }
            Blob(b) => ValueRef::Blob(b),
            Clob(c) => ValueRef::Clob(c),
            SExp(s) => {
                let lazy_sequence = LazySequence {
                    raw_sequence: s,
                    symbol_table: self.symbol_table,
                };
                ValueRef::SExp(lazy_sequence)
            }
            List(l) => {
                let lazy_sequence = LazySequence {
                    raw_sequence: l,
                    symbol_table: self.symbol_table,
                };
                ValueRef::List(lazy_sequence)
            }
            Struct(s) => {
                let lazy_struct = LazyStruct {
                    raw_struct: s,
                    symbol_table: self.symbol_table,
                };
                ValueRef::Struct(lazy_struct)
            }
        };
        Ok(value_ref)
    }
}

// TODO: Make generic over any impl of trait IceRawReader
struct LazySystemReader<'a> {
    raw_reader: LazyRawBinaryReader<'a>,
    symbol_table: SymbolTable,
    // LST processing
    is_lst_append: bool,
    pending_symbols: Vec<Option<&'a str>>,
}

impl<'a> LazySystemReader<'a> {
    fn new(ion_data: &'a [u8]) -> Self {
        let raw_reader = LazyRawBinaryReader::new(ion_data);
        LazySystemReader {
            raw_reader,
            symbol_table: SymbolTable::new(),
            is_lst_append: false,
            pending_symbols: Vec::new(),
        }
    }

    fn is_symbol_table(raw_value: &LazyRawValue) -> bool {
        raw_value.ion_type() == IonType::Struct
            && raw_value.annotations().next() == Some(Ok(RawSymbolTokenRef::SymbolId(3)))
    }

    // Note that &mut self and the SystemStreamItem have the same lifetime.
    // You cannot call `next()` again until the SystemStreamItem is no longer being used.
    pub fn next(&mut self) -> IonResult<SystemStreamItem> {
        if !self.pending_symbols.is_empty() {
            if !self.is_lst_append {
                // We're setting the symbols list, not appending to it.
                self.symbol_table.reset();
            }
            for symbol in self.pending_symbols.drain(..) {
                self.symbol_table.intern_or_add_placeholder(symbol);
            }
            self.is_lst_append = false;
        }
        let stream_item = match self.raw_reader.next()? {
            RawStreamItem::VersionMarker(major, minor) => {
                SystemStreamItem::VersionMarker(major, minor)
            }
            RawStreamItem::Value(lazy_raw_value) => {
                if Self::is_symbol_table(&lazy_raw_value) {
                    return self.process_symbol_table(lazy_raw_value);
                } else {
                    let lazy_value = LazyValue {
                        raw_value: lazy_raw_value,
                        symbol_table: &self.symbol_table,
                    };
                    SystemStreamItem::Value(lazy_value)
                }
            }
            RawStreamItem::Nothing => SystemStreamItem::Nothing,
        };
        Ok(stream_item)
    }

    fn process_symbol_table<'b>(
        &'b mut self,
        symbol_table: LazyRawValue<'a>,
    ) -> IonResult<SystemStreamItem<'b>>
    where
        'a: 'b,
    {
        // We've already confirmed this is an annotated struct
        let symbol_table = match symbol_table.read()? {
            RawValueRef::Struct(symbol_table) => symbol_table,
            _ => unreachable!("`symbol_table` is known to be a struct"),
        };
        // Assume it's not an LST append unless we found imports: $ion_symbol_table
        self.is_lst_append = false;
        let mut reader = symbol_table.reader();
        let mut found_symbols_field = false;
        let mut found_imports_field = false;

        // TODO: Add a symbol_id() method to RawSymbolTokenRef
        use system_symbol_ids::*;
        while let Some(field) = reader.next_field()? {
            if field.name() == SYMBOLS.as_raw_symbol_token_ref() {
                if found_symbols_field {
                    return decoding_error("found symbol table with multiple 'symbols' fields");
                }
                found_symbols_field = true;
                self.process_symbols(field.value())?;
            }
            if field.name() == IMPORTS.as_raw_symbol_token_ref() {
                if found_imports_field {
                    return decoding_error("found symbol table with multiple 'symbols' fields");
                }
                found_imports_field = true;
                self.process_imports(field.value())?;
            }
            // Ignore other fields
        }
        let lazy_struct = LazyStruct {
            raw_struct: symbol_table,
            symbol_table: &self.symbol_table,
        };
        Ok(SystemStreamItem::SymbolTable(lazy_struct))
    }

    fn process_symbols(&mut self, symbols: &LazyRawValue<'a>) -> IonResult<()> {
        if let RawValueRef::List(list) = symbols.read()? {
            let mut reader = list.reader();
            while let Some(value) = reader.next()? {
                if let RawValueRef::String(text) = value.read()? {
                    self.pending_symbols.push(Some(text))
                } else {
                    self.pending_symbols.push(None)
                }
            }
        }
        // Nulls and non-list values are ignored.
        Ok(())
    }

    fn process_imports(&mut self, imports: &LazyRawValue) -> IonResult<()> {
        match imports.read()? {
            RawValueRef::Symbol(symbol_token) => {
                if symbol_token == system_symbol_ids::ION_SYMBOL_TABLE.as_raw_symbol_token_ref() {
                    self.is_lst_append = true;
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
    use crate::lazy_reader::system_reader::LazySystemReader;
    use crate::lazy_reader::system_stream_item::SystemStreamItem;
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
