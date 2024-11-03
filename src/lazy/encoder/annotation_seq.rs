use smallvec::SmallVec;

use crate::raw_symbol_ref::SystemSymbol_1_1;
use crate::{RawSymbolRef, SymbolId};

/// A sequence of annotations.
///
/// When the sequence is two or fewer annotations, it will not require a heap allocation.
pub type AnnotationsVec<'a> = SmallVec<[RawSymbolRef<'a>; 2]>;

/// Types that can be viewed as an annotations sequence.
///
/// Examples include `SymbolId`, `&str`, and iterables of those types.
pub trait AnnotationSeq<'a> {
    fn into_annotations_vec(self) -> AnnotationsVec<'a>;
}

impl<'a> AnnotationSeq<'a> for &'a str {
    /// Converts the value into an `AnnotationsVec`.
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolRef::Text(self));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for &'a &str {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolRef::Text(self));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for SymbolId {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolRef::SymbolId(self));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for &'a SymbolId {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolRef::SymbolId(*self));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for SystemSymbol_1_1 {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolRef::SystemSymbol_1_1(self));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for &'a SystemSymbol_1_1 {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolRef::SystemSymbol_1_1(*self));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for RawSymbolRef<'a> {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(self);
        vec
    }
}

impl<'a> AnnotationSeq<'a> for AnnotationsVec<'a> {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        self
    }
}

impl<'a, T> AnnotationSeq<'a> for Vec<T>
where
    T: Into<RawSymbolRef<'a>>,
{
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut annotations = AnnotationsVec::new();
        for token in self {
            annotations.push(token.into());
        }
        annotations
    }
}

impl<'a, T> AnnotationSeq<'a> for &'a [T]
where
    for<'b> &'b T: Into<RawSymbolRef<'b>>,
{
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut annotations = AnnotationsVec::new();
        for token in self {
            annotations.push(token.into());
        }
        annotations
    }
}

impl<'a, T, const N: usize> AnnotationSeq<'a> for [T; N]
where
    T: Into<RawSymbolRef<'a>>,
{
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut annotations = AnnotationsVec::new();
        for token in self {
            annotations.push(token.into());
        }
        annotations
    }
}

impl<'a, T, const N: usize> AnnotationSeq<'a> for &'a [T; N]
where
    for<'b> &'b T: Into<RawSymbolRef<'b>>,
{
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut annotations = AnnotationsVec::new();
        for token in self {
            annotations.push(token.into());
        }
        annotations
    }
}
