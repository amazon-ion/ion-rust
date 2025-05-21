use crate::conformance_dsl::*;

use ion_rs::{v1_0, v1_1};
use ion_rs::{
    Catalog, Element, ElementReader, Reader, Sequence, SharedSymbolTable, Symbol, SymbolId,
};

/// A Context forms a scope for tracking all of the document fragments and any parent Contexts that
/// also need to be considered. Through this context the ability to generate the full test
/// document input, and evaluate any forced encodings or Ion versions, is provided.
#[derive(Clone)]
pub(crate) struct Context<'a> {
    version: IonVersion,
    encoding: IonEncoding,
    fragments: &'a Vec<Fragment>,
    parent_ctx: Option<&'a Context<'a>>,
    symbol_tables: Vec<SharedSymbolTable>, // To build Catalogs when needed, Catalog doesn't
                                           // require Clone.
}

impl<'a> Context<'a> {
    /// Creates a new Context with the provided version, encoding and fragments. A parent context
    /// is not set.
    pub fn new(
        version: IonVersion,
        encoding: IonEncoding,
        fragments: &'a Vec<Fragment>,
    ) -> Result<Self> {
        let symbol_tables = build_ion_tests_symtables()?;
        Ok(Self {
            version,
            encoding,
            fragments,
            parent_ctx: None,
            symbol_tables,
        })
    }

    /// Creates a new Context with the provided fragments, based on the supplied `parent`. The
    /// encoding and version for the new Context is inherited from `parent`.
    pub fn extend(parent: &'a Context, fragments: &'a Vec<Fragment>) -> Self {
        Self {
            version: parent.version,
            encoding: parent.encoding,
            parent_ctx: Some(parent),
            fragments,
            symbol_tables: parent.symbol_tables.clone(),
        }
    }

    /// Determine the ion version used for this context. In the case of multi-version testing
    /// (eg. through ion_1_x) multiple branches in the test are produced, one for each concrete
    /// version. `IonVersion::Unspecified` will be returned only when no IVM is emitted in the test
    /// document, and no version has been set for the context.
    pub fn version(&self) -> IonVersion {
        let parent_ver = self
            .parent_ctx
            .map(|c| c.version())
            .unwrap_or(IonVersion::Unspecified);
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

    /// Force an ion version to be used in this Context. Manually setting a version will be
    /// overridden if the fragments for this context emit an IVM.
    pub fn set_version(&mut self, version: IonVersion) {
        self.version = version;
    }

    /// Determine the encoding for all fragments in the path to this Context.
    pub fn encoding(&self) -> IonEncoding {
        let parent_enc = self
            .parent_ctx
            .map(|c| c.encoding)
            .unwrap_or(IonEncoding::Unspecified);
        Self::resolve_encoding(parent_enc, self.encoding)
    }

    /// Determine the version requirements for this Context's fragments.
    pub fn fragment_version(&self) -> IonVersion {
        match self.fragments.first() {
            Some(Fragment::Ivm(1, 0)) => IonVersion::V1_0,
            Some(Fragment::Ivm(1, 1)) => IonVersion::V1_1,
            _ => IonVersion::Unspecified,
        }
    }

    /// Determine the encoding requirements for this Context's fragments.
    pub fn fragment_encoding(&self) -> IonEncoding {
        let enc = self
            .fragments
            .iter()
            .find(|f| matches!(f, Fragment::Text(_) | Fragment::Binary(_)));
        match enc {
            Some(Fragment::Text(_)) => IonEncoding::Text,
            Some(Fragment::Binary(_)) => IonEncoding::Binary,
            _ => IonEncoding::Unspecified,
        }
    }

    /// Force an ion encoding (text or binary) for this Context. All encodings through the path of
    /// a test must match.
    pub fn set_encoding(&mut self, enc: IonEncoding) {
        self.encoding = enc;
    }

    /// Given 2 encodings, one for a parent context, and one for the child, validate and return the
    /// resulting encoding for the whole path.
    fn resolve_encoding(parent: IonEncoding, child: IonEncoding) -> IonEncoding {
        match (parent, child) {
            (a, b) if a == b => a,
            (IonEncoding::Unspecified, n) => n,
            (n, IonEncoding::Unspecified) => n,
            _ => panic!("Mismatched encodings for nested contexts"), // TODO: Bubble error.
        }
    }

    /// Build all of the symbol tables loaded from ion-tests/catalog into a usuable Catalog.
    pub fn build_catalog(&self) -> impl Catalog {
        let mut catalog = MapCatalog::new();

        for sym_table in self.symbol_tables.iter() {
            catalog.insert_table(sym_table.clone());
        }

        catalog
    }

    /// Returns the symbol at the provided offset `offset` within the symbol table named `symtab`,
    /// if either the symbol table, or the offset, is not valid then None is returned.
    pub fn get_symbol_from_table<S: AsRef<str>>(
        &self,
        symtab: S,
        offset: SymbolId,
    ) -> Option<Symbol> {
        self.symbol_tables
            .iter()
            .filter(|st| st.name() == symtab.as_ref())
            .max_by_key(|sst| sst.version())
            .and_then(|st| st.symbols().get(offset - 1).cloned())
    }

    pub fn write_input<E: ion_rs::Encoding, O: std::io::Write>(
        &self,
        writer: &mut ion_rs::Writer<E, O>,
    ) -> InnerResult<()> {
        self.parent_ctx
            .map(|ctx| {
                let mut new_ctx = ctx.clone();
                new_ctx.set_encoding(self.encoding());
                new_ctx.write_input(writer)
            })
            .unwrap_or(Ok(()))?;

        for frag in self.fragments.iter() {
            frag.write(self, writer)?;
        }
        writer.flush()?;
        Ok(())
    }

    /// Returns a Vec<u8> containing the serialized data consisting of all fragments in the path
    /// for this context.
    pub fn input(&self, child_encoding: IonEncoding) -> InnerResult<(Vec<u8>, IonEncoding)> {
        use ion_rs::Writer;
        let encoding = match Self::resolve_encoding(self.encoding(), child_encoding) {
            IonEncoding::Unspecified => IonEncoding::Text,
            x => x,
        };
        let version = match self.version() {
            IonVersion::Unspecified => IonVersion::V1_1,
            x => x,
        };

        let buffer = vec![];
        match (encoding, version) {
            (IonEncoding::Text, IonVersion::V1_0) => {
                let mut writer = Writer::new(v1_0::Text, buffer)?;
                self.write_input(&mut writer)?;
                let output = writer.close()?;
                Ok((output, encoding))
            }
            (IonEncoding::Text, IonVersion::V1_1) => {
                let mut writer = Writer::new(v1_1::Text, buffer)?;
                self.write_input(&mut writer)?;
                let output = writer.close()?;
                Ok((output, encoding))
            }
            (IonEncoding::Binary, IonVersion::V1_0) => {
                let mut writer = Writer::new(v1_0::Binary, buffer)?;
                self.write_input(&mut writer)?;
                let output = writer.close()?;
                Ok((output, encoding))
            }
            (IonEncoding::Binary, IonVersion::V1_1) => {
                let mut writer = Writer::new(v1_1::Binary, buffer)?;
                self.write_input(&mut writer)?;
                let output = writer.close()?;
                Ok((output, encoding))
            }
            _ => unreachable!(),
        }
    }

    /// Returns the Sequence of Elements representing the test document.
    pub fn read_all(&self, encoding: IonEncoding) -> InnerResult<Sequence> {
        let (data, data_encoding) = self.input(encoding)?;

        if self.fragments.is_empty() {
            let empty: Vec<Element> = vec![];
            return Ok(empty.into());
        }

        let version = match self.version() {
            IonVersion::Unspecified => IonVersion::V1_0,
            v => v,
        };

        match (version, data_encoding) {
            (IonVersion::V1_0, IonEncoding::Binary) => {
                Ok(Reader::new(v1_0::Binary, data)?.read_all_elements()?)
            }
            (IonVersion::V1_0, IonEncoding::Text) => {
                Ok(Reader::new(v1_0::Text, data)?.read_all_elements()?)
            }
            (IonVersion::V1_0, IonEncoding::Unspecified) => {
                Ok(Reader::new(v1_0::Binary, data)?.read_all_elements()?)
            }
            (IonVersion::V1_1, IonEncoding::Binary) => {
                Ok(Reader::new(v1_1::Binary, data)?.read_all_elements()?)
            }
            (IonVersion::V1_1, IonEncoding::Text) => {
                Ok(Reader::new(v1_1::Text, data)?.read_all_elements()?)
            }
            (IonVersion::V1_1, IonEncoding::Unspecified) => {
                Ok(Reader::new(v1_1::Binary, data)?.read_all_elements()?)
            }
            _ => unreachable!(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ion_rs::IonData;

    #[test]
    // Test to ensure that when we render fragments, we don't insert new IVMs breaking the context
    // established by previous fragments.
    fn unbroken_fragment_encoding_context() {
        let elems = Element::read_all("mactab (macro m (v!) (%v))")
            .expect("unable to parse mactab into elements");
        let frags: Vec<Fragment> = vec![
            Clause::try_from(elems)
                .expect("unable to convert elements to clause")
                .try_into()
                .expect("unable to convert clause to fragment"),
            Fragment::Text("(:m 1)".to_string()),
        ];
        let context = Context::new(IonVersion::V1_1, IonEncoding::Text, &frags)
            .expect("unable to create context");
        let (bytes, _) = context
            .input(IonEncoding::Text)
            .expect("failed to render fragments");

        let expected_sequence = Element::read_all(
            "$ion_1_1 $ion::(module _ (macro_table (macro m (v '!' ) ('%' v ) ) ) ) (:m 1)",
        )
        .expect("valid Ion");
        let actual_sequence = Element::read_all(bytes).expect("Writer must generate valid Ion.");
        assert!(IonData::from(expected_sequence).eq(&IonData::from(actual_sequence)))
    }
}
