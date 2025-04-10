//! Fragments within the DSL are responsible for piecing together the ion document used during the
//! test. Each fragment contributes in some way to the full ion stream that is tested, usually
//! providing different mechanisms for representing ion data, but also by providing shortcuts to
//! adding common data to be tested such as encoding directives and macros.
//!
//! In order to produce the input document each fragment is encoded in the order that they appear
//! in the test document. In the case of `Text`, the data is concatenated to an ion text stream
//! verbatim. The `Toplevel` fragment requires a little more work in order to support the
//! missing/absent symbol notation. Since all of the Toplevel fragments are provided as ion
//! literals within the test document, any symbols that is unknown in the context of the test
//! document, or may otherwise differ in value, needs to be encoded using a notation that
//! communicates the Symbol ID and an optional Symbol Table, to the DSL parser. When the values are
//! read by the ion reader they're treated as normal quoted symbols. When the Toplevel fragment is
//! encoded however, each Element read from the Toplevel clause is wrapped within a `ProxyElement`,
//! which by implementing `WriteAsIon` is able to recursively look at all values being written to
//! the test's input and capture any symbols that match the unknown symbol notation.
//!
//! The `ProxyElement` type is also used for testing equality between LazyValues and Elements. The
//! type is used in order to hold onto a Context for accessing the input document's symbol tables,
//! so that symbols from the Produces continuation can be evaluated for unknown symbol notation as
//! well.

use super::context::Context;
use super::*;
use ion_rs::{ion_seq, Encoding, WriteConfig};
use ion_rs::{Element, SExp, Sequence, Struct, Symbol};
use ion_rs::{RawSymbolRef, SequenceWriter, StructWriter, ValueWriter, WriteAsIon, Writer};

/// Shared functionality for Fragments.
trait FragmentImpl {
    /// Encode the current fragment into ion given the provided `WriteConfig`
    fn encode<E: Encoding>(
        &self,
        ctx: &Context,
        config: impl Into<WriteConfig<E>>,
    ) -> InnerResult<Vec<u8>>;

    fn write<E: ion_rs::Encoding, O: std::io::Write>(
        &self,
        ctx: &Context,
        writer: &mut ion_rs::Writer<E, O>,
    ) -> InnerResult<()>;
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

static EMPTY_TOPLEVEL: Fragment = Fragment::TopLevel(TopLevel { elems: vec![] });

impl Fragment {
    /// Write the fragment to the test document using the provided writer
    pub(crate) fn write<E: ion_rs::Encoding, O: std::io::Write>(
        &self,
        ctx: &Context,
        writer: &mut ion_rs::Writer<E, O>,
    ) -> InnerResult<()> {
        match self {
            Fragment::TopLevel(toplevel) => toplevel.write(ctx, writer),
            Fragment::Text(txt) => {
                writer.flush()?;
                let _ = writer.output_mut().write(txt.as_bytes())?;
                Ok(())
            }
            Fragment::Binary(bytes) => {
                writer.flush()?;
                let _ = writer.output_mut().write(bytes)?;
                Ok(())
            }
            Fragment::Ivm(maj, min) => match ctx.encoding() {
                IonEncoding::Binary => {
                    writer.flush()?;
                    let _ = writer
                        .output_mut()
                        .write(&[0xE0, *maj as u8, *min as u8, 0xEA])?;
                    Ok(())
                }
                _ => {
                    writer.flush()?;
                    let _ = writer
                        .output_mut()
                        .write(format!("$ion_{}_{} ", maj, min).as_bytes())?;
                    Ok(())
                }
            },
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
                let maj = other
                    .body
                    .first()
                    .map(|e| e.as_i64())
                    .ok_or(ConformanceErrorKind::ExpectedInteger)?
                    .unwrap();
                let min = other
                    .body
                    .get(1)
                    .map(|e| e.as_i64())
                    .ok_or(ConformanceErrorKind::ExpectedInteger)?
                    .unwrap();
                Fragment::Ivm(maj, min)
            }
            ClauseType::TopLevel => Fragment::TopLevel(TopLevel { elems: other.body }),
            ClauseType::Encoding => {
                // Rather than treat Encoding special, we expand it to a (toplevel ..) as described
                // in the spec.
                let inner: Element = SExp(Sequence::new(other.body)).into();
                let inner = inner.with_annotations(["$ion"]);
                Fragment::TopLevel(TopLevel { elems: vec![inner] })
            }
            ClauseType::MacTab => {
                // Like encoding, MacTab is expanded into a TopLevel fragment.
                let mut mac_table_elems: Vec<Element> = vec![Symbol::from("macro_table").into()];
                mac_table_elems.push(Element::symbol("_"));
                for elem in other.body {
                    mac_table_elems.push(elem);
                }
                let mac_table: Element = SExp(Sequence::new(mac_table_elems)).into();

                // Construct our Module
                let module: Element = SExp(ion_seq!(
                    Symbol::from("module"),
                    Symbol::from("_"),
                    mac_table,
                ))
                .into();

                Fragment::TopLevel(TopLevel {
                    elems: vec![module.with_annotations(["$ion"])],
                })
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

pub trait FragmentWriter {
    fn write(&mut self, _frag: &Fragment) -> InnerResult<usize> {
        todo!()
    }
}

// newtype to handle writing an Element, after we check to make sure it's not a symbol that has our
// special absent symbol sauce.
pub(crate) struct ProxyElement<'a>(pub &'a Element, pub &'a Context<'a>);

impl ProxyElement<'_> {
    fn write_struct<V: ValueWriter>(&self, val: &Struct, writer: V) -> ion_rs::IonResult<()> {
        let annot_writer = writer.with_annotations(self.0.annotations())?;
        let mut strukt = annot_writer.struct_writer()?;

        for (name, value) in val.fields() {
            match parse_absent_symbol(name.text().unwrap_or("")) {
                (None, None) => {
                    strukt.write(name, ProxyElement(value, self.1))?;
                }
                (_, Some(id)) => {
                    strukt.write(RawSymbolRef::from(id), ProxyElement(value, self.1))?;
                }
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
                (None, Some(id)) => annot_writer.write(RawSymbolRef::from(id)),
                (Some(symtab), Some(id)) => {
                    match self.1.get_symbol_from_table(symtab, id) {
                        Some(symbol) => {
                            annot_writer.write(RawSymbolRef::from(symbol.text().unwrap_or("")))
                        }
                        None => annot_writer.write(RawSymbolRef::from(0)), // TODO: error.
                    }
                }
                _ => unreachable!(),
            }
        } else {
            writer.write(self.0)
        }
    }

    /// Test whether the ProxyElement represents an expression group, using the transcription
    /// syntax.
    fn is_expr_group(&self) -> bool {
        use ion_rs::Value;
        match self.0.value() {
            Value::SExp(seq) => seq.get(0).is_some_and(|x| Some("#$:") == x.as_symbol().and_then(|s| s.text())),
            _ => false,
        }
    }
}

impl<T: ion_rs::Decoder> PartialEq<ion_rs::LazyValue<'_, T>> for ProxyElement<'_> {
    // TODO: Move this out of PartialEq - there are a lot of potential errors comparing these two
    // types that might be better bubbling up.
    fn eq(&self, other: &ion_rs::LazyValue<'_, T>) -> bool {
        use super::compare_symbols_eq;
        use ion_rs::{LazyRawFieldName, ValueRef};
        match self.0.ion_type() {
            IonType::Symbol => compare_symbols_eq(self.1, other, self.0).unwrap_or(false),
            IonType::Struct => {
                let ValueRef::Struct(actual_struct) =
                    other.read().expect("error reading input value")
                else {
                    return false;
                };

                let mut is_equal = true;
                let mut actual_iter = actual_struct.iter();
                let mut expected_field_iter =
                    self.0.as_struct().expect("error reading struct").fields();

                while is_equal {
                    let actual = actual_iter.next();
                    let expected = expected_field_iter.next();

                    match (actual, expected) {
                        (Some(actual), Some((expected_field, expected_field_elem))) => {
                            let actual = actual.expect("unable to read struct field");
                            let actual_field = actual
                                .raw_name()
                                .map(|n| n.read())
                                .expect("unable to get SymbolRef for field name");
                            let actual_field =
                                actual_field.expect("unable to read SymbolRef for field name");

                            is_equal &=
                                match parse_absent_symbol(expected_field.text().unwrap_or("")) {
                                    (None, None) => {
                                        *self.0
                                            == Element::try_from(*other)
                                                .expect("unable to convert LazyValue into Element")
                                    }
                                    (None, Some(id)) => actual_field.is_symbol_id(id),
                                    (Some(symtab), Some(id)) => {
                                        let symbol_table = other.symbol_table();
                                        match self.1.get_symbol_from_table(symtab, id) {
                                            None => actual_field.is_unknown_text(),
                                            Some(shared_symbol) => {
                                                let shared_symbol_txt =
                                                    shared_symbol.text().unwrap_or("");
                                                let shared_id = symbol_table
                                                    .sid_for(shared_symbol_txt)
                                                    .unwrap_or(0);
                                                actual_field.matches_sid_or_text(
                                                    shared_id,
                                                    shared_symbol_txt,
                                                )
                                            }
                                        }
                                    }
                                    _ => unreachable!(), // Cannot have symtab without id.
                                };

                            let actual_value = actual.value();
                            is_equal &= ProxyElement(expected_field_elem, self.1) == actual_value;
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

                let actual_list: ion_rs::IonResult<Vec<ion_rs::LazyValue<_>>> =
                    actual_list.iter().collect();
                let actual_list = actual_list.expect("error parsing list");

                let expected_list = self
                    .0
                    .as_sequence()
                    .expect("unable to get sequence for list");
                let expected_list: Vec<&Element> = expected_list.iter().collect();

                if actual_list.len() != expected_list.len() {
                    false
                } else {
                    for (actual, expected) in actual_list.iter().zip(expected_list.iter()) {
                        if ProxyElement(expected, self.1) != *actual {
                            return false;
                        }
                    }
                    true
                }
            }
            _ => {
                *self.0
                    == Element::try_from(*other).expect("unable to convert lazyvalue into element")
            }
        }
    }
}

impl WriteAsIon for ProxyElement<'_> {
    fn write_as_ion<V: ValueWriter>(&self, writer: V) -> ion_rs::IonResult<()> {
        use ion_rs::Value::*;
        use ion_rs::EExpWriter;
        match self.0.value() {
            Symbol(_) => self.write_symbol(writer),
            Struct(strukt) => self.write_struct(strukt, writer),
            List(list) => {
                let annot_writer = writer.with_annotations(self.0.annotations())?;
                let mut list_writer = annot_writer.list_writer()?;
                for elem in list {
                    list_writer.write(ProxyElement(elem, self.1))?;
                }
                list_writer.close()?;
                Ok(())
            }
            SExp(sexp) => {
                match sexp.get(0).map(Element::value) {
                    Some(Symbol(symbol)) if symbol.text().is_some() => {
                        let text = symbol.text().unwrap();
                        if text.starts_with("#$:") {
                            let macro_id = text.strip_prefix("#$:").unwrap(); // SAFETY: Tested above.
                            let mut args: V::EExpWriter =
                                if let Ok(symbol_id) = macro_id.parse::<ion_rs::SymbolId>() {
                                    writer.eexp_writer(symbol_id)?
                                } else {
                                    // TODO: Need to handle text macro IDs when generating a binary
                                    // test document.
                                    writer.eexp_writer(macro_id)?
                                };
                            for arg in sexp.iter().skip(1) {
                                let proxy = ProxyElement(arg, self.1);
                                if proxy.is_expr_group() {
                                    let mut group = args.expr_group_writer()?;
                                    if let Some(seq) = arg.as_sequence() {
                                        for group_arg in seq.into_iter().skip(1) {
                                            group.write(ProxyElement(group_arg, self.1))?;
                                        }
                                        let _ = group.close()?;
                                    }
                                } else {
                                    args.write(ProxyElement(arg, self.1))?;
                                }
                            }
                            args.close()?;
                            return Ok(());
                        }
                    }
                    _ => {}
                }

                let annot_writer = writer.with_annotations(self.0.annotations())?;
                let mut sexp_writer = annot_writer.sexp_writer()?;
                for elem in sexp {
                    sexp_writer.write(ProxyElement(elem, self.1))?;
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
    fn encode<E: Encoding>(
        &self,
        ctx: &Context,
        config: impl Into<WriteConfig<E>>,
    ) -> InnerResult<Vec<u8>> {
        let mut buffer = Vec::with_capacity(1024);
        let mut writer = Writer::new(config, buffer)?;

        for elem in self.elems.as_slice() {
            writer.write(ProxyElement(elem, ctx))?;
        }
        buffer = writer.close()?;
        Ok(buffer)
    }

    fn write<E: ion_rs::Encoding, O: std::io::Write>(
        &self,
        ctx: &Context,
        writer: &mut ion_rs::Writer<E, O>,
    ) -> InnerResult<()> {
        for elem in self.elems.as_slice() {
            writer.write(ProxyElement(elem, ctx))?;
        }
        Ok(())
    }
}
