use crate::lazy::decoder::{Decoder, LazyRawValueExpr};
use bumpalo::collections::Vec as BumpVec;

pub struct RawValueExprCache<'top, D: Decoder> {
    values: BumpVec<'top, LazyRawValueExpr<'top, D>>,
}
