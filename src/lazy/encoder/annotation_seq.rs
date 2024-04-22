use crate::{RawSymbolTokenRef, SymbolId};
use smallvec::SmallVec;

/// A sequence of annotations.
///
/// When the sequence is two or fewer annotations, it will not require a heap allocation.
pub type AnnotationsVec<'a> = SmallVec<[RawSymbolTokenRef<'a>; 2]>;

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
        vec.push(RawSymbolTokenRef::Text(self.into()));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for &'a &str {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolTokenRef::Text((*self).into()));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for SymbolId {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolTokenRef::SymbolId(self));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for &'a SymbolId {
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut vec = AnnotationsVec::new();
        vec.push(RawSymbolTokenRef::SymbolId(*self));
        vec
    }
}

impl<'a> AnnotationSeq<'a> for RawSymbolTokenRef<'a> {
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
    T: Into<RawSymbolTokenRef<'a>>,
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
    for<'b> &'b T: Into<RawSymbolTokenRef<'b>>,
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
    T: Into<RawSymbolTokenRef<'a>>,
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
    for<'b> &'b T: Into<RawSymbolTokenRef<'b>>,
{
    fn into_annotations_vec(self) -> AnnotationsVec<'a> {
        let mut annotations = AnnotationsVec::new();
        for token in self {
            annotations.push(token.into());
        }
        annotations
    }
}
