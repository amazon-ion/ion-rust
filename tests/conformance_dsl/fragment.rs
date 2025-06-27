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
use ion_rs::{ion_seq, v1_1, AnyEncoding, EExpWriter, Encoding, Reader, Value, WriteConfig};
use ion_rs::{Element, Sequence, Struct, Symbol};
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
                        .write(format!("$ion_{maj}_{min} ").as_bytes())?;
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
                let inner: Element = Value::SExp(Sequence::new(other.body)).into();
                let inner = inner.with_annotations(["$ion"]);
                Fragment::TopLevel(TopLevel { elems: vec![inner] })
            }
            ClauseType::MacTab => {
                // Like encoding, MacTab is expanded into a TopLevel fragment.
                let mut mac_table_elems: Vec<Element> = vec![Symbol::from("macro_table").into()];
                for elem in other.body {
                    mac_table_elems.push(elem);
                }
                let mac_table: Element = Value::SExp(Sequence::new(mac_table_elems)).into();

                // Construct our Module
                let module: Element = Value::SExp(ion_seq!(
                    Symbol::from("module"),
                    Symbol::from("_"),
                    mac_table,
                ))
                .into();

                Fragment::TopLevel(TopLevel {
                    elems: vec![module.with_annotations(["$ion"])],
                })
            }
            ClauseType::SymTab => {
                use ion_rs::{ion_struct, Sequence, SequenceBuilder};
                let symbols = other
                    .body
                    .iter()
                    .try_fold(Sequence::builder(), |seq: SequenceBuilder, elem| {
                        elem.as_string()
                            .ok_or(ConformanceErrorKind::ExpectedString)
                            .map(|s| seq.push(s))
                    })?
                    .build_list();

                let table: Element = ion_struct! {
                    "symbols": symbols,
                }
                .into();
                Fragment::TopLevel(TopLevel {
                    elems: vec![table.with_annotations(["$ion_symbol_table"])],
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
                        const EEXP_PREFIX: &str = "#$:";
                        const EXP_GROUP_PLACEHOLDER: &str = "#$::";
                        if text.starts_with(EEXP_PREFIX) {
                            // It's an e-expression. Start by isolating the macro ID.
                            let macro_id = text.strip_prefix(EEXP_PREFIX).unwrap(); // SAFETY: Tested above.
                            let mut eexp_writer =
                                // See if it's a numeric identifier
                                if let Ok(macro_address) = macro_id.parse::<usize>() {
                                    writer.eexp_writer(macro_address)?
                                } else {
                                    // TODO: Need to handle text macro IDs when generating a binary
                                    // test document.
                                    writer.eexp_writer(macro_id)?
                                };
                            // Get an iterator over the ProxyElement argument expressions by skipping
                            // over the first child value in the s-expression.
                            let arg_elements = &mut sexp.iter().skip(1);
                            while let Some(arg) = arg_elements.next() {
                                // Whether this argument represents an expression group.
                                let arg_is_expr_group = arg
                                    .as_sexp()
                                    .and_then(|sexp| sexp.get(0))
                                    .and_then(Element::as_symbol)
                                    .map(|sym| sym.text() == Some(EXP_GROUP_PLACEHOLDER))
                                    .unwrap_or(false);
                                // Whether this argument is being passed to a parameter that accepts
                                // 'rest' syntax. This is true for the last parameter when its
                                // cardinality is anything other than exactly-one.
                                let is_rest_parameter = eexp_writer
                                    .current_parameter()
                                    .map(|p| p.accepts_rest())
                                    .unwrap_or(false);

                                // If this argument isn't in 'rest' position and it's not an
                                // expression group...
                                if !is_rest_parameter && !arg_is_expr_group {
                                    // ...then wrap it in a `ProxyElement` and write it out.
                                    eexp_writer.write(ProxyElement(arg, self.1))?;
                                } else if arg_is_expr_group {
                                    // ...if it is an expression group, we need to encode it in an
                                    // expression group built via our expression writer
                                    // ProxyElement cannot do this alone.
                                    let mut group_writer = eexp_writer.expr_group_writer()?;
                                    let group_args = arg
                                        .as_sexp()
                                        .unwrap() // Verified above
                                        .iter()
                                        .skip(1); // Skip past expression group marker.
                                    group_writer
                                        .write_all(group_args.map(|e| ProxyElement(e, self.1)))?;
                                    let _ = group_writer.close();
                                } else {
                                    // However, if the argument is in rest position and it isn't an
                                    // expression group, we need to convert it to an expression group
                                    // to support binary Ion (which doesn't have rest syntax).
                                    let mut group_writer = eexp_writer.expr_group_writer()?;
                                    group_writer.write(ProxyElement(arg, self.1))?;
                                    group_writer
                                        .write_all(arg_elements.map(|e| ProxyElement(e, self.1)))?;
                                    let _ = group_writer.close()?;
                                }
                            }
                            eexp_writer.close()?;
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

/// Implements the TopLevel fragment.
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

        self.write(ctx, &mut writer)?;

        buffer = writer.close()?;
        Ok(buffer)
    }

    fn write<E: Encoding, O: std::io::Write>(
        &self,
        ctx: &Context,
        writer: &mut Writer<E, O>,
    ) -> InnerResult<()> {
        // The Writer is asked to serialize Elements that represent system values.
        // In many cases, it will emit a macro table containing macros that are not in its own
        // encoding context. For example, this snippet:
        //
        //     (mactab (macro m (v!) v))
        //
        // will emit a system value that the reader will understand defines macro `m`.
        // However, the writer emitting the system value does not have macro `m` in its own
        // encoding context. If the test later invokes `m` like this:
        //
        //     (toplevel ('#$:m' 5))
        //
        // the Writer will raise an error reporting that the test is trying to invoke a
        // non-existent macro.
        //
        // As a workaround, when serializing top-level Elements, the writer does an initial
        // serialization pass to load any necessary encoding context changes.
        //
        // Serialize the data once...
        let serialized = v1_1::Text::encode_all(self.elems.as_slice())?;
        // ...then read the data, constructing a macro table in the Reader...
        let mut reader = Reader::new(AnyEncoding, serialized)?;
        while reader.next()?.is_some() {}
        let macro_table = reader.macro_table();
        if ctx.version() == IonVersion::V1_1 {
            // For each macro in the Reader...
            for mac in macro_table.iter() {
                // ...try to register the macro in the Writer.
                let is_already_defined = writer
                    .get_macro(
                        mac.name()
                            // See: https://github.com/amazon-ion/ion-rust/issues/967
                            .expect("this hack will not work for anonymous macros"),
                    )
                    .is_ok();
                if is_already_defined {
                    // For simplicity, we skip over system macros that are already defined.
                } else {
                    // Otherwise, register the macro.
                    let _result = writer.register_macro(&mac);
                }
            }
        }

        // Now that the Writer has the necessary context, it can encode the ProxyElements.
        for elem in self.elems.as_slice() {
            writer.write(ProxyElement(elem, ctx))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_symtab_strings() {
        let source = r#"(symtab 1 2 3)"#;
        let clause_elem = Element::read_one(source).expect("unable to read source");
        let seq = clause_elem.as_sequence().expect("could not read sequence");
        let clause: Clause = seq
            .try_into()
            .expect("unable to convert elements into clause");

        assert_eq!(
            ConformanceErrorKind::ExpectedString,
            Fragment::try_from(clause).unwrap_err()
        );
    }

    #[test]
    fn parse_symtab() {
        struct TestCase {
            source: &'static str,
            symbols: &'static [&'static str],
        }

        let tests = &[
            TestCase {
                source: r#"(symtab "a")"#,
                symbols: &["a"],
            },
            TestCase {
                source: r#"(symtab "a" "b" "c")"#,
                symbols: &["a", "b", "c"],
            },
        ];

        for test in tests {
            println!("Testing: {:?}", test.source);
            let clause_elem = Element::read_one(test.source).expect("unable to read source");
            let seq = clause_elem.as_sequence().expect("could not read sequence");
            let clause: Clause = seq
                .try_into()
                .expect("unable to convert elements into clause");
            let frag: Fragment = clause
                .try_into()
                .expect("unable to convert clause into fragment");

            let Fragment::TopLevel(toplevel) = frag else {
                panic!("SymTab clause did not parse into a top-level fragment");
            };

            let element = toplevel
                .elems
                .first()
                .expect("No sub-elements of toplevel fragment");
            let annotations = element.annotations();

            assert_eq!(annotations.len(), 1);
            assert_eq!(annotations.first(), Some("$ion_symbol_table"));

            let strukt = element
                .as_struct()
                .expect("could not turn element into struct");
            let field = strukt.get("symbols").expect("unable to find symbol field");
            let symbols = field.as_list().expect("symbols field is not a list");

            assert_eq!(symbols.len(), test.symbols.len());
            let symbols_match = symbols
                .iter()
                .zip(test.symbols)
                .fold(true, |acc, (a, b)| acc && (a == &Element::string(*b)));
            assert!(symbols_match);
        }
    }
}
