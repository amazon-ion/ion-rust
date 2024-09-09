use ion_rs::{Element, Sequence, SExp, Struct, Symbol};
use ion_rs::{v1_0, v1_1, WriteConfig, Encoding, ion_seq};
use ion_rs::{RawSymbolRef, StructWriter, SequenceWriter, Writer, WriteAsIon, ValueWriter};

use super::*;
use super::context::Context;

/// Shared functionality for Fragments.
trait FragmentImpl  {
    /// Encode the current fragment into ion given the provided `WriteConfig`
    fn encode<E: Encoding>(&self, config: impl Into<WriteConfig<E>>) -> InnerResult<Vec<u8>>;
}


/// Fragments represent parts of the ion document read for testing.
#[derive(Clone, Debug)]
pub(crate) enum Fragment {
    /// Provide ion data encoded as binary ion to be used as part of the test document.
    Binary(Vec<u8>),
    /// Provide a major and minor version that should be used to emit an IVM for the document.
    Ivm(i64, i64),
    /// Provide ion data encoded as text ion to be used as part of the test document.
    Text(String),
    /// Provide ion data using ion literals to be used as part of the test document.
    TopLevel(TopLevel),
}

static EMPTY_TOPLEVEL: Fragment = Fragment::TopLevel(TopLevel { elems: vec!() });

impl Fragment {
    /// Encode the fragment as binary ion.
    pub fn to_binary(&self, ctx: &Context) -> InnerResult<Vec<u8>> {
        match ctx.version() {
            IonVersion::V1_1 => self.write_as_binary(ctx, v1_1::Binary),
            _ => self.write_as_binary(ctx, v1_0::Binary),
        }
    }

    /// Encode the fragment as text ion.
    pub fn to_text(&self, ctx: &Context) -> InnerResult<Vec<u8>> {
        match ctx.version() {
            IonVersion::V1_1 => self.write_as_text(ctx, v1_1::Text),
            _ => self.write_as_text(ctx, v1_0::Text),
        }
    }

    /// Internal. Writes the fragment as binary ion using the provided WriteConfig.
    fn write_as_binary<E: Encoding>(&self, _ctx: &Context, config: impl Into<WriteConfig<E>>) -> InnerResult<Vec<u8>> {
        match self {
            Fragment::TopLevel(toplevel) => toplevel.encode(config),
            Fragment::Binary(bin) => Ok(bin.clone()),
            Fragment::Text(_) => unreachable!(),
            Fragment::Ivm(maj, min) => Ok([0xE0, *maj as u8, *min as u8, 0xEA].to_vec()),
        }
    }

    /// Internal. Writes the fragment as text ion using the provided WriteConfig.
    fn write_as_text<E: Encoding>(&self, _ctx: &Context, config: impl Into<WriteConfig<E>>) -> InnerResult<Vec<u8>> {
        match self {
            Fragment::TopLevel(toplevel) => toplevel.encode(config),
            Fragment::Text(txt) => {
                let bytes = txt.as_bytes();
                Ok(bytes.to_owned())
            }
            Fragment::Binary(_) => unreachable!(),
            Fragment::Ivm(maj, min) => return Ok(format!("$ion_{}_{}", maj, min).as_bytes().to_owned()),
        }
    }

    /// Returns the required encoding (binary/text) for the fragment if one is required, otherwise
    /// `IonEncoding::Unspecified` is returned.
    pub fn required_encoding(&self) -> IonEncoding {
        match self {
            Fragment::Text(_) => IonEncoding::Text,
            Fragment::Binary(_) => IonEncoding::Binary,
            _ => IonEncoding::Unspecified,
        }
    }
}

impl TryFrom<Clause> for Fragment {
    type Error = ConformanceErrorKind;

    fn try_from(other: Clause) -> InnerResult<Self> {
        let frag = match other.tpe {
            ClauseType::Text => {
                let mut text = String::from("");
                for elem in other.body.iter() {
                    let txt = match elem.ion_type() {
                        IonType::String => elem.as_string().unwrap().to_owned(),
                        _ => return Err(ConformanceErrorKind::UnexpectedValue),
                    };
                    text = text + " " + &txt;
                }
                Fragment::Text(text)
            }
            ClauseType::Binary => Fragment::Binary(parse_bytes_exp(other.body.iter())?),
            ClauseType::Ivm => {
                // IVM: (ivm <int> <int>)
                let maj = other.body.first().map(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?.unwrap();
                let min = other.body.get(1).map(|e| e.as_i64()).ok_or(ConformanceErrorKind::ExpectedInteger)?.unwrap();
                Fragment::Ivm(maj, min)
            }
            ClauseType::TopLevel => Fragment::TopLevel(TopLevel { elems: other.body }),
            ClauseType::Encoding => {
                // Rather than treat Encoding special, we expand it to a (toplevel ..) as described
                // in the spec.
                let inner: Element = SExp(Sequence::new(other.body)).into();
                let inner = inner.with_annotations(["$ion_encoding"]);
                Fragment::TopLevel(TopLevel { elems: vec!(inner) })
            }
            ClauseType::MacTab => {
                // Like encoding, MacTab is expanded into a TopLevel fragment.
                let mut mac_table_elems: Vec<Element> = vec!(Symbol::from("macro_table").into());
                for elem in other.body {
                    mac_table_elems.push(elem);
                }
                let mac_table: Element = SExp(Sequence::new(mac_table_elems)).into();
                let module: Element = SExp(ion_seq!(
                        Symbol::from("module"),
                        Symbol::from("M"),
                        mac_table,
                        SExp(ion_seq!(Symbol::from("macro_table"), Symbol::from("M"))),
                )).into();
                let encoding: Element = SExp(ion_seq!(module)).into();
                let encoding = encoding.with_annotations(["$ion_encoding"]);
                Fragment::TopLevel(TopLevel { elems: vec!(encoding) })
            }
            _ => return Err(ConformanceErrorKind::ExpectedFragment),
        };
        Ok(frag)
    }
}

impl TryFrom<Sequence> for Fragment {
    type Error = ConformanceErrorKind;

    fn try_from(other: Sequence) -> InnerResult<Self> {
        let clause = Clause::try_from(other)?;
        Fragment::try_from(clause)
    }
}

// newtype to handle writing an Element, after we check to make sure it's not a symbol that has our
// special absent symbol sauce.
#[derive(Debug)]
pub(crate) struct ProxyElement<'a>(pub &'a Element);

impl<'a> ProxyElement<'a> {

    fn write_struct<V: ValueWriter>(&self, val: &Struct, writer: V) -> ion_rs::IonResult<()> {
        let annotations: Vec<&Symbol> = self.0.annotations().iter().collect();
        let annot_writer = writer.with_annotations(annotations)?;
        let mut strukt = annot_writer.struct_writer()?;

        for (name, value) in val.fields() {
            match parse_absent_symbol(name.text().unwrap_or("")) {
                (None, None) => { strukt.write(name, ProxyElement(value))?; }
                (_, Some(id)) => { strukt.write(RawSymbolRef::from(id), ProxyElement(value))?; },
                _ => unreachable!(),
            }
        }
        strukt.close()
    }

    fn write_symbol<V: ValueWriter>(&self, writer: V) -> ion_rs::IonResult<()> {
        if !self.0.is_null() {
            let annotations: Vec<&Symbol> = self.0.annotations().iter().collect();
            let annot_writer = writer.with_annotations(annotations)?;
            let symbol = self.0.as_symbol().unwrap();
            match parse_absent_symbol(symbol.text().unwrap_or("")) {
                (None, None) => annot_writer.write(symbol),
                (_, Some(id)) => annot_writer.write(RawSymbolRef::from(id)),
                _ => unreachable!(),
            }
        } else {
            writer.write(self.0)
        }
    }

}

impl<T: ion_rs::Decoder> PartialEq<ion_rs::LazyValue<'_, T>> for ProxyElement<'_> {
    fn eq(&self, other: &ion_rs::LazyValue<'_, T>) -> bool {
        use ion_rs::{LazyRawFieldName, LazyRawValue, v1_0::RawValueRef, ValueRef};
        match self.0.ion_type() {
            IonType::Symbol => match parse_absent_symbol(self.0.as_symbol().unwrap().text().unwrap_or("")) {
                (None, None) => *self.0 == Element::try_from(*other).expect("unable to convert lazyvalue into element"),
                (_, Some(id)) => {
                    let Some(raw_symbol) = other.raw().map(|r| r.read()) else {
                        unreachable!()
                    };
                    let raw_symbol = raw_symbol.expect("error reading symbol");

                    let RawValueRef::Symbol(raw_symbol) = raw_symbol else {
                        return false;
                    };
                    raw_symbol.matches_sid_or_text(id, "")
                }
                _ => unreachable!(),
            }
            IonType::Struct => {
                let ValueRef::Struct(actual_struct) = other.read().expect("error reading input value") else {
                    return false;
                };

                let mut is_equal = true;
                let mut actual_iter = actual_struct.iter();
                let mut expected_field_iter = self.0.as_struct().expect("error reading struct").fields();

                while is_equal {
                    let actual = actual_iter.next();
                    let expected = expected_field_iter.next();

                    match (actual, expected) {
                        (Some(actual), Some((expected_field, expected_field_elem))) => {
                            let actual = actual.expect("unable to read struct field");
                            let actual_field = actual.raw_name().map(|n| n.read()).expect("unable to get SymbolRef for field name");
                            let actual_field = actual_field.expect("unable to read SymbolRef for field name");

                            is_equal &= match parse_absent_symbol(expected_field.text().unwrap_or("")) {
                                (None, None) => *self.0 == Element::try_from(*other).expect("unable to convert LazyValue into Element"),
                                (_, Some(id)) => actual_field.matches_sid_or_text(id, ""),
                                _ => unreachable!(),
                            };

                            let actual_value = actual.value();
                            is_equal &= ProxyElement(expected_field_elem) == actual_value;
                        }
                        (None, None) => break,
                        _ => is_equal = false,
                    }
                }
                is_equal
            }
            IonType::List | IonType::SExp => {
                let ValueRef::List(actual_list) = other.read().expect("error reading list") else {
                    return false;
                };

                let actual_list: ion_rs::IonResult<Vec<ion_rs::LazyValue<_>>> = actual_list.iter().collect();
                let actual_list = actual_list.expect("error parsing list");

                let expected_list = self.0.as_sequence().expect("unable to get sequence for list");
                let expected_list: Vec<&Element> = expected_list.iter().collect();

                if actual_list.len() != expected_list.len() {
                    false
                } else {
                    for (actual, expected) in actual_list.iter().zip(expected_list.iter()) {
                        if ProxyElement(expected) != *actual {
                            return false
                        }
                    }
                    true
                }
            }
            _ => *self.0 == Element::try_from(*other).expect("unable to convert lazyvalue into element"),
        }
    }
}

impl<'a> WriteAsIon for ProxyElement<'a> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> ion_rs::IonResult<()> {
        match self.0.ion_type() {
            IonType::Symbol => self.write_symbol(writer),
            IonType::Struct => {
                if !self.0.is_null() {
                    self.write_struct(self.0.as_struct().unwrap(), writer)
                } else {
                    writer.write(self.0)
                }
            }
            IonType::List => {
                let annotations: Vec<&Symbol> = self.0.annotations().iter().collect();
                let annot_writer = writer.with_annotations(annotations)?;
                let mut list_writer = annot_writer.list_writer()?;
                for elem in self.0.as_sequence().unwrap() {
                    list_writer.write(ProxyElement(elem))?;
                }
                list_writer.close()?;
                Ok(())
            }
            IonType::SExp => {
                let annotations: Vec<&Symbol> = self.0.annotations().iter().collect();
                let annot_writer = writer.with_annotations(annotations)?;
                let mut sexp_writer = annot_writer.sexp_writer()?;
                for elem in self.0.as_sequence().unwrap() {
                    sexp_writer.write(ProxyElement(elem))?;
                }
                sexp_writer.close()?;
                Ok(())
            }
            _ => writer.write(self.0),
        }
    }
}

/// Implments the TopLevel fragment.
#[derive(Clone, Debug, Default)]
pub(crate) struct TopLevel {
    elems: Vec<Element>,
}

impl FragmentImpl for TopLevel {
    /// Encodes the provided ion literals into an ion stream, using the provided WriteConfig.
    fn encode<E: Encoding>(&self, config: impl Into<WriteConfig<E>>) -> InnerResult<Vec<u8>> {
        let mut buffer = Vec::with_capacity(1024);
        let mut writer = Writer::new(config, buffer)?;

        for elem in self.elems.as_slice() {
            writer.write(ProxyElement(elem))?;
        }
        buffer = writer.close()?;
        Ok(buffer)
    }
}
