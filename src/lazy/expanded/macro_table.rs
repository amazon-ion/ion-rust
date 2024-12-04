use crate::lazy::expanded::compiler::ExpansionAnalysis;
use crate::lazy::expanded::template::{
    ExprRange, MacroSignature, Parameter, ParameterCardinality, ParameterEncoding,
    RestSyntaxPolicy, TemplateBody, TemplateBodyElement, TemplateMacro, TemplateMacroRef,
    TemplateValue,
};
use crate::lazy::text::raw::v1_1::reader::{MacroAddress, MacroIdRef};
use crate::result::IonFailure;
use crate::{IonResult, IonType, Symbol, TemplateBodyExpr};
use compact_str::CompactString;
use delegate::delegate;
use rustc_hash::{FxBuildHasher, FxHashMap};
use std::borrow::Cow;
use std::sync::{Arc, LazyLock};

#[derive(Debug, Clone, PartialEq)]
pub struct Macro {
    name: Option<CompactString>,
    signature: MacroSignature,
    kind: MacroKind,
    // Compile-time heuristics that allow the reader to evaluate e-expressions lazily or using fewer
    // resources in many cases.
    //
    // For the time being, e-expressions that could produce multiple values cannot be lazily evaluated.
    // This is because the reader gives out lazy value handles for each value in the stream. If it knows
    // in advance that an expression will produce one value, it can give out a lazy value that is
    // backed by that e-expression.
    //
    // At the top level, e-expressions that both:
    // 1. Produce a single value
    //   and
    // 2. Will not produce a system value
    // can be lazily evaluated.
    //
    // At other levels of nesting, the single-value expansion is the only requirement for lazy
    // evaluation.
    expansion_analysis: ExpansionAnalysis,
}

impl Macro {
    pub fn named(
        name: impl Into<CompactString>,
        signature: MacroSignature,
        kind: MacroKind,
        expansion_analysis: ExpansionAnalysis,
    ) -> Self {
        Self::new(Some(name.into()), signature, kind, expansion_analysis)
    }

    pub fn anonymous(
        signature: MacroSignature,
        kind: MacroKind,
        expansion_analysis: ExpansionAnalysis,
    ) -> Self {
        Self::new(None, signature, kind, expansion_analysis)
    }

    pub fn from_template_macro(template_macro: TemplateMacro) -> Self {
        Macro::new(
            template_macro.name,
            template_macro.signature,
            MacroKind::Template(template_macro.body),
            template_macro.expansion_analysis,
        )
    }

    pub fn new(
        name: Option<CompactString>,
        signature: MacroSignature,
        kind: MacroKind,
        expansion_analysis: ExpansionAnalysis,
    ) -> Self {
        Self {
            name,
            signature,
            kind,
            expansion_analysis,
        }
    }

    pub fn name(&self) -> Option<&str> {
        self.name.as_deref()
    }
    pub(crate) fn clone_name(&self) -> Option<CompactString> {
        self.name.clone()
    }
    pub fn signature(&self) -> &MacroSignature {
        &self.signature
    }
    pub fn kind(&self) -> &MacroKind {
        &self.kind
    }

    pub fn expansion_analysis(&self) -> ExpansionAnalysis {
        self.expansion_analysis
    }

    pub fn can_be_lazily_evaluated_at_top_level(&self) -> bool {
        self.expansion_analysis()
            .can_be_lazily_evaluated_at_top_level()
    }

    pub fn must_produce_exactly_one_value(&self) -> bool {
        self.expansion_analysis().must_produce_exactly_one_value()
    }
}

/// The kinds of macros supported by
/// [`MacroEvaluator`](crate::MacroEvaluator)
/// This list parallels
/// [`MacroExpansionKind`](crate::MacroExpansionKind),
/// but its variants do not hold any associated state.
#[derive(Debug, Clone, PartialEq)]
pub enum MacroKind {
    None, // `(.none)` returns the empty stream
    ExprGroup,
    MakeString,
    MakeSymbol,
    MakeSExp,
    Annotate,
    Template(TemplateBody),
    // A placeholder for not-yet-implemented macros
    ToDo,
}

#[derive(Debug, Copy, Clone, PartialEq)]
pub struct MacroRef<'top> {
    address: MacroAddress,
    reference: &'top Macro,
}

impl<'top> MacroRef<'top> {
    pub fn new(address: MacroAddress, reference: &'top Macro) -> Self {
        Self { address, reference }
    }

    pub fn require_template(self) -> TemplateMacroRef<'top> {
        if let MacroKind::Template(body) = &self.kind() {
            return TemplateMacroRef::new(self.reference(), body);
        }
        unreachable!(
            "caller required a template macro but found {:?}",
            self.kind()
        )
    }

    pub fn id_text(&'top self) -> Cow<'top, str> {
        self.name()
            .map(Cow::from)
            .unwrap_or_else(move || Cow::from(format!("{}", self.address())))
    }

    pub fn address(&self) -> MacroAddress {
        self.address
    }

    pub fn reference(&self) -> &'top Macro {
        self.reference
    }

    delegate! {
        to self.reference {
            pub fn name(&'top self) -> Option<&'top str>;
            pub fn signature(self) -> &'top MacroSignature;
            pub fn kind(&self) -> &'top MacroKind;
            pub fn expansion_analysis(&self) -> ExpansionAnalysis;
            pub fn can_be_lazily_evaluated_at_top_level(&self) -> bool;
            pub fn must_produce_exactly_one_value(&self) -> bool;
        }
    }
}

/// Allows callers to resolve a macro ID (that is: name or address) to a [`MacroKind`], confirming
/// its validity and allowing evaluation to begin.
#[derive(Debug, Clone)]
pub struct MacroTable {
    // Stores `Rc` references to the macro definitions to make cloning the table's contents cheaper.
    macros_by_address: Vec<Arc<Macro>>,
    // Maps names to an address that can be used to query the Vec above.
    macros_by_name: FxHashMap<CompactString, usize>,
}

/// A lazily initialized singleton instance of the Ion 1.1 system macro table.
///
/// This instance is shared by all readers, minimizing the number of times that macro compilation
/// and heap allocation occurs.
pub static ION_1_1_SYSTEM_MACROS: LazyLock<MacroTable> =
    LazyLock::new(MacroTable::construct_system_macro_table);

impl Default for MacroTable {
    fn default() -> Self {
        Self::with_system_macros()
    }
}

impl MacroTable {
    pub const SYSTEM_MACRO_KINDS: &'static [MacroKind] = &[
        MacroKind::None,
        MacroKind::ExprGroup,
        MacroKind::MakeString,
        MacroKind::MakeSExp,
        MacroKind::Annotate,
    ];
    // The system macros range from address 0 to 23
    pub const NUM_SYSTEM_MACROS: usize = 24;
    // When a user defines new macros, this is the first ID that will be assigned. This value
    // is expected to change as development continues. It is currently used in several unit tests.
    pub const FIRST_USER_MACRO_ID: usize = Self::NUM_SYSTEM_MACROS;

    fn compile_system_macros() -> Vec<Arc<Macro>> {
        // We cannot compile template macros from source (text Ion) because that would require a Reader,
        // and a Reader would require system macros. To avoid this circular dependency, we manually
        // compile any TemplateMacros ourselves.
        vec![
            Arc::new(Macro::named(
                "none",
                MacroSignature::new(vec![]).unwrap(),
                MacroKind::None,
                ExpansionAnalysis {
                    could_produce_system_value: false,
                    must_produce_exactly_one_value: false,
                    // This is false because lazy evaluation requires giving out a LazyValue as a
                    // handle to eventually read the expression. We cannot give out a `LazyValue`
                    // for e-expressions that will produce 0 or 2+ values.
                    can_be_lazily_evaluated_at_top_level: false,
                    expansion_singleton: None,
                },
            )),
            //
            // This macro is equivalent to:
            //    (macro values (x*) x)
            //
            // It is effectively a user-addressable expression group.
            Arc::new(Macro::from_template_macro(TemplateMacro {
                name: Some("values".into()),
                signature: MacroSignature::new(vec![Parameter::rest("expr_group")]).unwrap(),
                body: TemplateBody {
                    expressions: vec![TemplateBodyExpr::variable(0, ExprRange::new(0..1))],
                    annotations_storage: vec![],
                },
                expansion_analysis: ExpansionAnalysis::no_assertions_made(),
            })),
            Arc::new(Macro::named(
                "annotate",
                MacroSignature::new(vec![
                    Parameter::zero_or_more("annotations"),
                    Parameter::required("value_to_annotate"),
                ])
                .unwrap(),
                MacroKind::Annotate,
                ExpansionAnalysis {
                    could_produce_system_value: true,
                    must_produce_exactly_one_value: true,
                    can_be_lazily_evaluated_at_top_level: false,
                    expansion_singleton: None,
                },
            )),
            Arc::new(Macro::named(
                "make_string",
                MacroSignature::new(vec![Parameter::rest("text_values")]).unwrap(),
                MacroKind::MakeString,
                ExpansionAnalysis::single_application_value(IonType::String),
            )),
            Arc::new(Macro::named(
                "make_symbol",
                MacroSignature::new(vec![Parameter::rest("text_values")]).unwrap(),
                MacroKind::MakeSymbol,
                ExpansionAnalysis::single_application_value(IonType::Symbol),
            )),
            Arc::new(Macro::named(
                "make_blob",
                MacroSignature::new(vec![Parameter::rest("lob_values")]).unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::single_application_value(IonType::Blob),
            )),
            Arc::new(Macro::named(
                "make_decimal",
                MacroSignature::new(vec![
                    Parameter::required("coefficient"),
                    Parameter::required("coefficient"),
                ])
                .unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::single_application_value(IonType::Decimal),
            )),
            Arc::new(Macro::named(
                "make_timestamp",
                MacroSignature::new(vec![
                    Parameter::required("year"),
                    Parameter::optional("month"),
                    Parameter::optional("day"),
                    Parameter::optional("hour"),
                    Parameter::optional("minute"),
                    Parameter::optional("second"),
                    Parameter::optional("offset_minutes"),
                ])
                .unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::single_application_value(IonType::Decimal),
            )),
            Arc::new(Macro::named(
                "make_list",
                MacroSignature::new(vec![Parameter::rest("sequences")]).unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::single_application_value(IonType::List),
            )),
            Arc::new(Macro::named(
                "make_sexp",
                MacroSignature::new(vec![Parameter::rest("sequences")]).unwrap(),
                MacroKind::MakeSExp,
                ExpansionAnalysis::single_application_value(IonType::SExp),
            )),
            Arc::new(Macro::named(
                "make_struct",
                MacroSignature::new(vec![Parameter::rest("sequences")]).unwrap(),
                MacroKind::MakeSExp,
                ExpansionAnalysis::single_application_value(IonType::Struct),
            )),
            // This macro is equivalent to:
            //    (macro set_symbols (symbols*)
            //      $ion_encoding::(
            //        // Set a new symbol table
            //        (symbol_table [(%symbols)])
            //        // Include the active encoding module macros
            //        (macro_table $ion_encoding)
            //      )
            //    )
            Arc::new(Macro::from_template_macro(TemplateMacro {
                name: Some("set_symbols".into()),
                signature: MacroSignature::new(vec![Parameter::rest("symbols")]).unwrap(),
                body: TemplateBody {
                    expressions: vec![
                        // The `$ion_encoding::(...)` s-expression
                        /* 0 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp)
                                // Has the first annotation in annotations storage below; `$ion_encoding`
                                .with_annotations(0..1),
                            // Contains expressions 0 (itself) through 7 (exclusive)
                            ExprRange::new(0..8),
                        ),
                        // The `(symbol_table ...)` s-expression.
                        /* 1 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp),
                            ExprRange::new(1..5),
                        ),
                        // The clause name `symbol_table`
                        /* 2 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "symbol_table",
                            ))),
                            ExprRange::new(2..3),
                        ),
                        // The list which will contain the expanded variable `symbols`
                        /* 3 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::List),
                            ExprRange::new(3..5),
                        ),
                        // We do not include the symbol literal `$ion_encoding`, indicating that
                        // we're replacing the existing symbol table.

                        // The variable at signature index 0 (`symbols`)
                        /* 4 */
                        TemplateBodyExpr::variable(0, ExprRange::new(4..5)),
                        // The `(macro_table ...)` s-expression.
                        /* 5 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp),
                            // Contains expression 4 (itself) through 8 (exclusive)
                            ExprRange::new(5..8),
                        ),
                        // The clause name `macro_table`
                        /* 6 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "macro_table",
                            ))),
                            ExprRange::new(6..7),
                        ),
                        // The module name $ion_encoding
                        /* 7 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "$ion_encoding",
                            ))),
                            ExprRange::new(7..8),
                        ),
                    ],
                    annotations_storage: vec![Symbol::owned("$ion_encoding")],
                },
                expansion_analysis: ExpansionAnalysis::directive(),
            })),
            // This macro is equivalent to:
            //    (macro add_symbols (symbols*)
            //      $ion_encoding::(
            //        // Include the active encoding module symbols, and add more
            //        (symbol_table $ion_encoding [(%symbols)])
            //        // Include the active encoding module macros
            //        (macro_table $ion_encoding)
            //      )
            //    )
            Arc::new(Macro::from_template_macro(TemplateMacro {
                name: Some("add_symbols".into()),
                signature: MacroSignature::new(vec![Parameter::rest("symbols")]).unwrap(),
                body: TemplateBody {
                    expressions: vec![
                        // The `$ion_encoding::(...)` s-expression
                        /* 0 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp)
                                // Has the first annotation in annotations storage below; `$ion_encoding`
                                .with_annotations(0..1),
                            // Contains expressions 0 (itself) through 8 (exclusive)
                            ExprRange::new(0..9),
                        ),
                        // The `(symbol_table ...)` s-expression.
                        /* 1 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp),
                            // Contains expression 1 (itself) through 5 (exclusive)
                            ExprRange::new(1..6),
                        ),
                        // The clause name `symbol_table`
                        /* 2 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "symbol_table",
                            ))),
                            ExprRange::new(2..3),
                        ),
                        // The module name $ion_encoding
                        /* 3 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "$ion_encoding",
                            ))),
                            ExprRange::new(3..4),
                        ),
                        // The list which will contain the expanded variable `symbols`
                        /* 4 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::List),
                            ExprRange::new(4..6),
                        ),
                        // The variable at signature index 0 (`symbols`)
                        /* 5 */
                        TemplateBodyExpr::variable(0, ExprRange::new(5..6)),
                        // The `(macro_table ...)` s-expression.
                        /* 6 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp),
                            // Contains expression 6 (itself) through 9 (exclusive)
                            ExprRange::new(6..9),
                        ),
                        // The clause name `macro_table`
                        /* 7 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "macro_table",
                            ))),
                            ExprRange::new(7..8),
                        ),
                        // The module name $ion_encoding
                        /* 8 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "$ion_encoding",
                            ))),
                            ExprRange::new(8..9),
                        ),
                    ],
                    annotations_storage: vec![Symbol::owned("$ion_encoding")],
                },
                expansion_analysis: ExpansionAnalysis::directive(),
            })),
            // This macro is equivalent to:
            //    (macro set_macros (macro_definitions*)
            //      $ion_encoding::(
            //        // Include the active encoding module symbols
            //        (symbol_table $ion_encoding)
            //        // Set a new macro table
            //        (macro_table (%macro_definitions))
            //      )
            //    )
            Arc::new(Macro::from_template_macro(TemplateMacro {
                name: Some("set_macros".into()),
                signature: MacroSignature::new(vec![Parameter::rest("macro_definitions")]).unwrap(),
                body: TemplateBody {
                    expressions: vec![
                        // The `$ion_encoding::(...)` s-expression
                        /* 0 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp)
                                // Has the first annotation in annotations storage below; `$ion_encoding`
                                .with_annotations(0..1),
                            // Contains expressions 0 (itself) through 7 (exclusive)
                            ExprRange::new(0..7),
                        ),
                        // The `(symbol_table ...)` s-expression.
                        /* 1 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp),
                            // Contains expression 1 (itself) through 4 (exclusive)
                            ExprRange::new(1..4),
                        ),
                        // The clause name `symbol_table`
                        /* 2 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "symbol_table",
                            ))),
                            ExprRange::new(2..3),
                        ),
                        // The module name $ion_encoding
                        /* 3 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "$ion_encoding",
                            ))),
                            ExprRange::new(3..4),
                        ),
                        // The `(macro_table ...)` s-expression.
                        /* 4 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp),
                            // Contains expression 4 (itself) through 7 (exclusive)
                            ExprRange::new(4..7),
                        ),
                        // The clause name `macro_table`
                        /* 5 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "macro_table",
                            ))),
                            ExprRange::new(5..6),
                        ),
                        // We do not include the symbol literal `$ion_encoding`, indicating that
                        // we're replacing the existing macro table.

                        // The variable at signature index 0 (`macro_definitions`)
                        /* 6 */
                        TemplateBodyExpr::variable(0, ExprRange::new(6..7)),
                    ],
                    annotations_storage: vec![Symbol::owned("$ion_encoding")],
                },
                expansion_analysis: ExpansionAnalysis::directive(),
            })),
            // This macro is equivalent to:
            //    (macro add_macros (macro_definitions*)
            //      $ion_encoding::(
            //        // Include the active encoding module symbols
            //        (symbol_table $ion_encoding)
            //        // Include the active encoding module macros and add more
            //        (macro_table $ion_encoding (%macro_definitions))
            //      )
            //    )
            Arc::new(Macro::from_template_macro(TemplateMacro {
                name: Some("add_macros".into()),
                signature: MacroSignature::new(vec![Parameter::rest("macro_definitions")]).unwrap(),
                body: TemplateBody {
                    expressions: vec![
                        // The `$ion_encoding::(...)` s-expression
                        /* 0 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp)
                                // Has the first annotation in annotations storage below; `$ion_encoding`
                                .with_annotations(0..1),
                            // Contains expressions 0 (itself) through 8 (exclusive)
                            ExprRange::new(0..8),
                        ),
                        // The `(symbol_table ...)` s-expression.
                        /* 1 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp),
                            // Contains expression 1 (itself) through 4 (exclusive)
                            ExprRange::new(1..4),
                        ),
                        // The clause name `symbol_table`
                        /* 2 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "symbol_table",
                            ))),
                            ExprRange::new(2..3),
                        ),
                        // The module name $ion_encoding
                        /* 3 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "$ion_encoding",
                            ))),
                            ExprRange::new(3..4),
                        ),
                        // The `(macro_table ...)` s-expression.
                        /* 4 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::SExp),
                            // Contains expression 4 (itself) through 8 (exclusive)
                            ExprRange::new(4..8),
                        ),
                        // The clause name `macro_table`
                        /* 5 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "macro_table",
                            ))),
                            ExprRange::new(5..6),
                        ),
                        // The symbol literal `$ion_encoding`, indicating that we're appending
                        // to the existing macro table.
                        /* 6 */
                        TemplateBodyExpr::element(
                            TemplateBodyElement::with_value(TemplateValue::Symbol(Symbol::owned(
                                "$ion_encoding",
                            ))),
                            ExprRange::new(6..7),
                        ),
                        // The variable at signature index 0 (`macro_definitions`)
                        /* 7 */
                        TemplateBodyExpr::variable(0, ExprRange::new(7..8)),
                    ],
                    annotations_storage: vec![Symbol::owned("$ion_encoding")],
                },
                expansion_analysis: ExpansionAnalysis::directive(),
            })),
            Arc::new(Macro::named(
                "use",
                MacroSignature::new(vec![
                    Parameter::required("catalog_key"),
                    Parameter::optional("version"),
                ])
                .unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::directive(),
            )),
            Arc::new(Macro::named(
                "parse_ion",
                MacroSignature::new(vec![Parameter::new(
                    "data",
                    ParameterEncoding::Tagged, // TODO: Support for other tagless types
                    ParameterCardinality::ZeroOrMore,
                    RestSyntaxPolicy::Allowed,
                )])
                .unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::no_assertions_made(),
            )),
            Arc::new(Macro::named(
                "repeat",
                MacroSignature::new(vec![Parameter::required("n"), Parameter::rest("expr")])
                    .unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::no_assertions_made(),
            )),
            Arc::new(Macro::named(
                "delta",
                MacroSignature::new(vec![Parameter::rest("deltas")]).unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis {
                    could_produce_system_value: false,
                    must_produce_exactly_one_value: false,
                    can_be_lazily_evaluated_at_top_level: true,
                    expansion_singleton: None,
                },
            )),
            Arc::new(Macro::named(
                "flatten",
                MacroSignature::new(vec![Parameter::rest("sequences")]).unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::no_assertions_made(),
            )),
            Arc::new(Macro::named(
                "sum",
                MacroSignature::new(vec![Parameter::required("a"), Parameter::required("b")])
                    .unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::single_application_value(IonType::Int),
            )),
            Arc::new(Macro::named(
                "meta",
                MacroSignature::new(vec![Parameter::rest("anything")]).unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::no_assertions_made(),
            )),
            Arc::new(Macro::named(
                "make_field",
                MacroSignature::new(vec![
                    Parameter::required("field_name"),
                    Parameter::required("field_value"),
                ])
                .unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::single_application_value(IonType::Struct),
            )),
            Arc::new(Macro::named(
                "default",
                MacroSignature::new(vec![
                    Parameter::zero_or_more("expr"),
                    Parameter::rest("default_expr"),
                ])
                .unwrap(),
                MacroKind::ToDo,
                ExpansionAnalysis::no_assertions_made(),
            )),
            // Adding a new system macro? Make sure you update FIRST_USER_MACRO_ID
        ]
    }

    pub(crate) fn construct_system_macro_table() -> Self {
        let macros_by_id = Self::compile_system_macros();
        let mut macros_by_name =
            FxHashMap::with_capacity_and_hasher(macros_by_id.len(), FxBuildHasher);
        for (id, mac) in macros_by_id.iter().enumerate() {
            if let Some(name) = mac.name() {
                macros_by_name.insert(name.into(), id);
            }
            // Anonymous macros are not entered into the macros_by_name lookup table
        }
        Self {
            macros_by_address: macros_by_id,
            macros_by_name,
        }
    }

    // TODO: Remove this
    pub fn with_system_macros() -> Self {
        ION_1_1_SYSTEM_MACROS.clone()
    }

    pub fn empty() -> Self {
        Self {
            macros_by_address: Vec::new(),
            macros_by_name: FxHashMap::default(),
        }
    }

    pub fn len(&self) -> usize {
        self.macros_by_address.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn macro_with_id<'a, 'b, I: Into<MacroIdRef<'b>>>(&'a self, id: I) -> Option<MacroRef<'a>> {
        let id = id.into();
        match id {
            MacroIdRef::LocalName(name) => self.macro_with_name(name),
            MacroIdRef::LocalAddress(address) => self.macro_at_address(address),
            MacroIdRef::SystemAddress(system_address) => {
                ION_1_1_SYSTEM_MACROS.macro_at_address(system_address.as_usize())
            }
        }
    }

    pub fn macro_at_address(&self, address: usize) -> Option<MacroRef<'_>> {
        let reference = self.macros_by_address.get(address)?;
        Some(MacroRef { address, reference })
    }

    pub fn address_for_name(&self, name: &str) -> Option<usize> {
        self.macros_by_name.get(name).copied()
    }

    pub fn macro_with_name(&self, name: &str) -> Option<MacroRef<'_>> {
        let address = *self.macros_by_name.get(name)?;
        let reference = self.macros_by_address.get(address)?;
        Some(MacroRef { address, reference })
    }

    pub(crate) fn clone_macro_with_name(&self, name: &str) -> Option<Arc<Macro>> {
        let address = *self.macros_by_name.get(name)?;
        let reference = self.macros_by_address.get(address)?;
        Some(Arc::clone(reference))
    }

    pub(crate) fn clone_macro_with_address(&self, address: usize) -> Option<Arc<Macro>> {
        let reference = self.macros_by_address.get(address)?;
        Some(Arc::clone(reference))
    }

    pub(crate) fn clone_macro_with_id(&self, macro_id: MacroIdRef<'_>) -> Option<Arc<Macro>> {
        use MacroIdRef::*;
        match macro_id {
            LocalName(name) => self.clone_macro_with_name(name),
            LocalAddress(address) => self.clone_macro_with_address(address),
            SystemAddress(system_address) => {
                ION_1_1_SYSTEM_MACROS.clone_macro_with_address(system_address.as_usize())
            }
        }
    }

    pub fn add_macro(&mut self, template: TemplateMacro) -> IonResult<usize> {
        let id = self.macros_by_address.len();
        // If the macro has a name, make sure that name is not already in use and then add it.
        if let Some(name) = &template.name {
            if self.macros_by_name.contains_key(name.as_str()) {
                return IonResult::decoding_error(format!("macro named '{name}' already exists"));
            }
            self.macros_by_name.insert(name.clone(), id);
        }

        let new_macro = Macro::new(
            template.name,
            template.signature,
            MacroKind::Template(template.body),
            template.expansion_analysis,
        );

        self.macros_by_address.push(Arc::new(new_macro));
        Ok(id)
    }

    pub(crate) fn append_all_macros_from(&mut self, other: &MacroTable) -> IonResult<()> {
        for macro_ref in &other.macros_by_address {
            let next_id = self.len();
            if let Some(name) = macro_ref.clone_name() {
                if self.macros_by_name.contains_key(name.as_str()) {
                    return IonResult::decoding_error(format!(
                        "macro named '{name}' already exists"
                    ));
                }
                self.macros_by_name.insert(name, next_id);
            }
            self.macros_by_address.push(Arc::clone(macro_ref))
        }
        Ok(())
    }
}
