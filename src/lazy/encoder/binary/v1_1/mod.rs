// TODO(pt004): relocate these modules out of `v1_1/`. The Ion 1.1 binary writer is gone, but these
//              encoding primitives are shared: the binary readers (and, for `FlexInt`/`FlexUInt`,
//              the shared `BinaryBuffer`) still decode with them.
pub mod fixed_int;
pub mod fixed_uint;
pub mod flex_int;
pub mod flex_sym;
pub mod flex_uint;
