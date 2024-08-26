use crate::conformance_dsl::*;

use ion_rs::{Element, ElementReader, Sequence, Reader, IonSlice};
use ion_rs::{v1_0, v1_1};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Context<'a> {
    version: IonVersion,
    encoding: IonEncoding,
    fragments: &'a Vec<Fragment>,
    parent_ctx: Option<&'a Context<'a>>,
}

impl<'a> Context<'a> {
    pub fn new(version: IonVersion, encoding: IonEncoding, fragments: &'a Vec<Fragment>) -> Self {
        Self { version, encoding, fragments, parent_ctx: None}
    }

    pub fn extend(parent: &'a Context, fragments: &'a Vec<Fragment>) -> Self {
        Self {
            version: parent.version,
            encoding: parent.encoding,
            parent_ctx: Some(parent),
            fragments,
        }
    }

    pub fn version(&self) -> IonVersion {
        let parent_ver = self.parent_ctx.map(|c| c.version()).unwrap_or(IonVersion::Unspecified);
        let frag_ver = self.fragment_version();
        let my_ver = if frag_ver == IonVersion::Unspecified {
            self.version
        } else {
            frag_ver
        };

        match (parent_ver, my_ver) {
            (IonVersion::Unspecified, v) => v,
            (v, IonVersion::Unspecified) => v,
            (a, b) if a == b => a,
            _ => panic!("Mismatched versions"),
        }
    }

    pub fn set_version(&mut self, version: IonVersion) {
        self.version = version;
    }

    pub fn encoding(&self) -> IonEncoding {
        let parent_enc = self.parent_ctx.map(|c| c.encoding).unwrap_or(IonEncoding::Unspecified);
        Self::resolve_encoding(parent_enc, self.encoding)
    }

    pub fn fragment_version(&self) -> IonVersion {
        match self.fragments.first() {
            Some(Fragment::Ivm(1, 0)) => IonVersion::V1_0,
            Some(Fragment::Ivm(1, 1)) => IonVersion::V1_1,
            _ => IonVersion::Unspecified,
        }
    }

    pub fn fragment_encoding(&self) -> IonEncoding {
        let enc = self.fragments.iter().find(|f| matches!(f, Fragment::Text(_) | Fragment::Binary(_)));
        match enc {
            Some(Fragment::Text(_)) => IonEncoding::Text,
            Some(Fragment::Binary(_)) => IonEncoding::Binary,
            _ => IonEncoding::Unspecified,
        }
    }

    pub fn set_encoding(&mut self, enc: IonEncoding) {
        self.encoding  = enc;
    }

    fn resolve_encoding(parent: IonEncoding, child: IonEncoding) -> IonEncoding {
        match (parent, child) {
            (a, b) if a == b => a,
            (IonEncoding::Unspecified, n) => n,
            (n, IonEncoding::Unspecified) => n,
            _ => panic!("Mismatched encodings for nested contexts"), // TODO: Bubble error.
        }
    }

    pub fn input(&self, child_encoding: IonEncoding) -> InnerResult<(Vec<u8>, IonEncoding)> {
        let encoding = Self::resolve_encoding(self.encoding(), child_encoding);
        let (data, data_encoding) = match encoding {
            IonEncoding::Text => (to_text(self, self.fragments.iter())?, encoding),
            IonEncoding::Binary => (to_binary(self, self.fragments.iter())?, encoding),
            IonEncoding::Unspecified => (to_binary(self, self.fragments.iter())?, IonEncoding::Binary),
        };
        Ok((data, data_encoding))
    }

    pub fn read_all(&self, encoding: IonEncoding) -> InnerResult<Sequence> {
        let (data, data_encoding) = self.input(encoding)?;
        let data_slice = IonSlice::new(data);

        if self.fragments.is_empty() {
            let empty: Vec<Element> = vec!();
            return Ok(empty.into());
        }

        let version = match self.version() {
            IonVersion::Unspecified => IonVersion::V1_0,
            v => v,
        };

        // Ok(Reader::new(AnyEncoding, data_slice)?.read_all_elements()?)

        match (version, data_encoding) {
            (IonVersion::V1_0, IonEncoding::Binary) =>
                Ok(Reader::new(v1_0::Binary, data_slice)?.read_all_elements()?),
            (IonVersion::V1_0, IonEncoding::Text) =>
                Ok(Reader::new(v1_0::Text, data_slice)?.read_all_elements()?),
            (IonVersion::V1_0, IonEncoding::Unspecified) =>
                Ok(Reader::new(v1_0::Binary, data_slice)?.read_all_elements()?),
            (IonVersion::V1_1, IonEncoding::Binary) =>
                Ok(Reader::new(v1_1::Binary, data_slice)?.read_all_elements()?),
            (IonVersion::V1_1, IonEncoding::Text) =>
                Ok(Reader::new(v1_1::Text, data_slice)?.read_all_elements()?),
            (IonVersion::V1_1, IonEncoding::Unspecified) =>
                Ok(Reader::new(v1_1::Binary, data_slice)?.read_all_elements()?),
            _ => unreachable!(),
        }
    }

}
