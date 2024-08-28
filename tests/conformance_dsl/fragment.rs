use ion_rs::{Element, Sequence};
use ion_rs::{v1_0, v1_1, WriteConfig, Encoding};

use super::*;
use super::context::Context;

trait FragmentImpl  {
    fn encode<E: Encoding>(&self, config: impl Into<WriteConfig<E>>) -> InnerResult<Vec<u8>>;
}


#[derive(Clone, Debug)]
pub(crate) enum Fragment {
    Binary(Vec<u8>),
    Each(Vec<Fragment>),
    Ivm(i64, i64),
    Text(String),
    TopLevel(TopLevel),
    MacTab,                 // TODO: Implement.
    Encoding,               // TODO: Implement.
}

static EMPTY_TOPLEVEL: Fragment = Fragment::TopLevel(TopLevel { elems: vec!() });

impl Fragment {
    pub fn to_binary(&self, ctx: &Context) -> InnerResult<Vec<u8>> {
        match ctx.version() {
            IonVersion::V1_1 => self.write_as_binary(ctx, v1_1::Binary),
            _ => self.write_as_binary(ctx, v1_0::Binary),
        }
    }

    pub fn to_text(&self, ctx: &Context) -> InnerResult<Vec<u8>> {
        match ctx.version() {
            IonVersion::V1_1 => self.write_as_text(ctx, v1_1::Text),
            _ => self.write_as_text(ctx, v1_0::Text),
        }
    }

    fn write_as_binary<E: Encoding>(&self, _ctx: &Context, config: impl Into<WriteConfig<E>>) -> InnerResult<Vec<u8>> {
        match self {
            Fragment::TopLevel(toplevel) => toplevel.encode(config),
            Fragment::Binary(bin) => Ok(bin.clone()),
            Fragment::Text(_) => unreachable!(),
            Fragment::Ivm(maj, min) => Ok([0xE0, *maj as u8, *min as u8, 0xEA].to_vec()),
            _ => unimplemented!(),
        }
    }

    fn write_as_text<E: Encoding>(&self, _ctx: &Context, config: impl Into<WriteConfig<E>>) -> InnerResult<Vec<u8>> {
        match self {
            Fragment::TopLevel(toplevel) => toplevel.encode(config),
            Fragment::Text(txt) => {
                let bytes = txt.as_bytes();
                Ok(bytes.to_owned())
            }
            Fragment::Binary(_) => unreachable!(),
            Fragment::Ivm(maj, min) => return Ok(format!("$ion_{}_{}", maj, min).as_bytes().to_owned()),
            _ => unimplemented!(),
        }
    }


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
            ClauseType::Encoding => Fragment::Encoding,
            ClauseType::MacTab => Fragment::MacTab,
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

#[derive(Clone, Debug, Default)]
pub(crate) struct TopLevel {
    elems: Vec<Element>,
}

impl FragmentImpl for TopLevel {
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
