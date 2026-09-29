use crate::lazy::decoder::private::RawStructFieldExprIterator;
use crate::lazy::decoder::{Decoder, HasRange, LazyRawFieldName, LazyRawStruct};
#[cfg(feature = "experimental-tooling-apis")]
use crate::lazy::expanded::r#struct::tooling::FieldExprIterator;
use crate::lazy::expanded::{
    EncodingContextRef, ExpandedAnnotationsIterator, ExpandedAnnotationsSource, ExpandedValueRef,
    LazyExpandedValue,
};
use crate::result::IonFailure;
use crate::{IonResult, SymbolRef};
use std::ops::Range;

/// A unified type embodying all possible field representations coming from input data
/// (i.e. raw structs of some encoding).
//
// LazyRawStruct implementations have a `unexpanded_fields` method that lifts its raw fields into
// `FieldExpr` instances. The `ExpandedStructIterator` unpacks the field as part of its iteration
// process.
//
// The `NameMacro` and `EExp` variants this enum used to have were only reachable from macro
// expansion, which Ion 1.0 does not have.
#[derive(Debug, Clone, Copy)]
pub enum FieldExpr<'top, D: Decoder> {
    NameValue(LazyExpandedFieldName<'top, D>, LazyExpandedValue<'top, D>),
}

impl<'top, D: Decoder> FieldExpr<'top, D> {
    pub fn name(&self) -> Option<&LazyExpandedFieldName<'top, D>> {
        let FieldExpr::NameValue(name, _) = self;
        Some(name)
    }

    pub fn name_is(&self, text: &str) -> IonResult<bool> {
        let Some(field_name) = self.name() else {
            return Ok(false);
        };
        Ok(field_name.read()?.text() == Some(text))
    }

    pub fn range(&self) -> Option<Range<usize>> {
        let FieldExpr::NameValue(name, value) = self;
        Some(name.range()?.start..value.range()?.end)
    }

    pub fn expect_expanded(self) -> IonResult<LazyExpandedField<'top, D>> {
        let FieldExpr::NameValue(name, value) = self;
        Ok(LazyExpandedField::new(name, value))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct LazyExpandedField<'top, D: Decoder> {
    name: LazyExpandedFieldName<'top, D>,
    value: LazyExpandedValue<'top, D>,
}

impl<'top, D: Decoder> LazyExpandedField<'top, D> {
    pub fn new(name: LazyExpandedFieldName<'top, D>, value: LazyExpandedValue<'top, D>) -> Self {
        Self { name, value }
    }

    pub fn value(&self) -> LazyExpandedValue<'top, D> {
        self.value
    }

    pub fn name(&self) -> LazyExpandedFieldName<'top, D> {
        self.name
    }

    pub fn to_field_expr(self) -> FieldExpr<'top, D> {
        FieldExpr::NameValue(self.name(), self.value())
    }
}

// The `TemplateName` and `MakeField` variants this enum used to have were only reachable from macro
// expansion, which Ion 1.0 does not have.
#[derive(Debug, Clone, Copy)]
pub enum LazyExpandedFieldName<'top, D: Decoder> {
    RawName(EncodingContextRef<'top>, D::FieldName<'top>),
}

impl<'top, D: Decoder> LazyExpandedFieldName<'top, D> {
    /// Returns `true` if this name was produced by evaluating a macro. Otherwise, returns `false`.
    ///
    /// Ion 1.0 has no macros, so every field name is a literal from the input stream and this
    /// always returns `false`.
    pub fn is_ephemeral(&self) -> bool {
        false
    }

    pub fn read(&self) -> IonResult<SymbolRef<'top>> {
        let LazyExpandedFieldName::RawName(context, name) = self;
        name.read()?.resolve("a field name", *context)
    }

    pub fn raw(&self) -> Option<&D::FieldName<'top>> {
        let LazyExpandedFieldName::RawName(_, raw_name) = self;
        Some(raw_name)
    }

    pub fn range(&self) -> Option<Range<usize>> {
        let LazyExpandedFieldName::RawName(_context, name) = self;
        Some(name.range())
    }
}

// The `Template`, `MakeStruct`, and `MakeField` variants this enum used to have were only reachable
// from macro expansion, which Ion 1.0 does not have.
#[derive(Copy, Clone)]
pub enum ExpandedStructSource<'top, D: Decoder> {
    ValueLiteral(D::Struct<'top>),
}

#[derive(Copy, Clone)]
pub struct LazyExpandedStruct<'top, D: Decoder> {
    pub(crate) context: EncodingContextRef<'top>,
    pub(crate) source: ExpandedStructSource<'top, D>,
}

#[cfg(feature = "experimental-tooling-apis")]
impl<'top, D: Decoder> LazyExpandedStruct<'top, D> {
    pub fn context(&self) -> EncodingContextRef<'top> {
        self.context
    }
    pub fn source(&self) -> ExpandedStructSource<'top, D> {
        self.source
    }
}

impl<'top, D: Decoder> LazyExpandedStruct<'top, D> {
    pub fn from_literal(
        context: EncodingContextRef<'top>,
        sexp: D::Struct<'top>,
    ) -> LazyExpandedStruct<'top, D> {
        let source = ExpandedStructSource::ValueLiteral(sexp);
        Self { source, context }
    }

    pub fn annotations(&self) -> ExpandedAnnotationsIterator<'top, D> {
        let ExpandedStructSource::ValueLiteral(value) = &self.source;
        ExpandedAnnotationsIterator::new(ExpandedAnnotationsSource::ValueLiteral(
            value.annotations(),
        ))
    }

    pub fn iter(&self) -> ExpandedStructIterator<'top, D> {
        let ExpandedStructSource::ValueLiteral(raw_struct) = &self.source;
        let field_exprs = RawStructFieldExprIterator::new(self.context, raw_struct.iter());
        ExpandedStructIterator {
            source: ExpandedStructIteratorSource::ValueLiteral(field_exprs),
        }
    }

    #[cfg(feature = "experimental-tooling-apis")]
    pub fn field_exprs(&self) -> FieldExprIterator<'top, D> {
        // The field source iterator has the same data as the regular iterator, it just uses it
        // differently. Since the regular iterator's initialization process is non-trivial, we'll
        // just make a regular iterator and use it for parts.
        let ExpandedStructIterator { source } = self.iter();
        FieldExprIterator::new(source)
    }

    pub fn bump_iter(&self) -> &'top mut ExpandedStructIterator<'top, D> {
        self.context.allocator().alloc_with(|| self.iter())
    }

    pub fn find(&self, name: &str) -> IonResult<Option<LazyExpandedValue<'top, D>>> {
        // Do a linear scan over the struct's fields until we encounter one with the requested name.
        for field_result in self.iter() {
            let field = field_result?;
            if field.name().read()?.text() == Some(name) {
                return Ok(Some(field.value));
            }
        }
        // If there is no such field, return None.
        Ok(None)
    }

    pub fn get(&self, name: &str) -> IonResult<Option<ExpandedValueRef<'top, D>>> {
        self.find(name)?.map(|f| f.read()).transpose()
    }

    pub fn get_expected(&self, name: &str) -> IonResult<ExpandedValueRef<'top, D>> {
        if let Some(value) = self.get(name)? {
            Ok(value)
        } else {
            IonResult::decoding_error(format!("did not find expected struct field '{name}'"))
        }
    }
}

// The `Template`, `MakeField`, and `MakeStruct` variants this enum used to have were only reachable
// from macro expansion, which Ion 1.0 does not have. The remaining variant no longer needs to carry
// a macro evaluator alongside its field source.
pub enum ExpandedStructIteratorSource<'top, D: Decoder> {
    // The struct we're iterating over is a literal in the data stream.
    ValueLiteral(RawStructFieldExprIterator<'top, D>),
}

impl<'top, D: Decoder> ExpandedStructIteratorSource<'top, D> {
    fn next_field(&mut self) -> Option<IonResult<FieldExpr<'top, D>>> {
        // Get the next unexpanded field from our source's iterator.
        let ExpandedStructIteratorSource::ValueLiteral(raw_struct_iter) = self;
        raw_struct_iter.next()
    }
}

pub struct ExpandedStructIterator<'top, D: Decoder> {
    // Each variant of 'source' below holds its own encoding context reference
    source: ExpandedStructIteratorSource<'top, D>,
}

impl<'top, D: Decoder> Iterator for ExpandedStructIterator<'top, D> {
    type Item = IonResult<LazyExpandedField<'top, D>>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        let field = match self.source.next_field()? {
            Ok(field) => field,
            Err(e) => return Some(Err(e)),
        };
        let FieldExpr::NameValue(name, value) = field;
        Some(Ok(LazyExpandedField::new(name, value)))
    }
}

#[cfg(feature = "experimental-tooling-apis")]
mod tooling {
    use super::*;

    /// Like the [`ExpandedStructIterator`], but yields the expressions that back the fields rather
    /// than the fields themselves.
    pub struct FieldExprIterator<'top, D: Decoder> {
        // Each variant of 'source' below holds its own encoding context reference
        source: ExpandedStructIteratorSource<'top, D>,
    }

    impl<'top, D: Decoder> FieldExprIterator<'top, D> {
        pub(crate) fn new(source: ExpandedStructIteratorSource<'top, D>) -> Self {
            Self { source }
        }
    }

    impl<'top, D: Decoder> Iterator for FieldExprIterator<'top, D> {
        type Item = IonResult<FieldExpr<'top, D>>;

        fn next(&mut self) -> Option<Self::Item> {
            self.source.next_field()
        }
    }
}
