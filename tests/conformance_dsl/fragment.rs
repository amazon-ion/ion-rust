use ion_rs::{Element, Sequence, SExp, Symbol};
use ion_rs::{v1_0, v1_1, WriteConfig, Encoding, ion_seq};

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

/// Implments the TopLevel fragment.
#[derive(Clone, Debug, Default)]
pub(crate) struct TopLevel {
    elems: Vec<Element>,
}

impl FragmentImpl for TopLevel {
    /// Encodes the provided ion literals into an ion stream, using the provided WriteConfig.
    fn encode<E: Encoding>(&self, config: impl Into<WriteConfig<E>>) -> InnerResult<Vec<u8>> {
        use ion_rs::Writer;
        let mut buffer = Vec::with_capacity(1024);
        let mut writer = Writer::new(config, buffer)?;
        for elem in self.elems.as_slice() {
            writer.write(elem)?;
        }
        buffer = writer.close()?;
        Ok(buffer)
    }
}
