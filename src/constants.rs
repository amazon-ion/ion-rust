/// The deepest level of container nesting that the text parser, lazy binary navigation, and
/// conversions from lazy values to `Element`, `Value`, `Sequence`, and `Struct` accept, and the
/// default and maximum depth of managed writers. Top-level values are at depth 0 and a container's
/// children are one level deeper than the container, so in `[[1]]` the inner list is at depth 1 and
/// `1` is at depth 2. Parsing, converting, or writing a container whose children would be deeper
/// than this limit returns an error, even if the container is empty. Lazy binary navigation returns
/// the error when the container is read, by `LazyValue::read` or a method that calls it such as
/// `LazyStruct::get`, not when the container is reached with `Reader::next` or a container's
/// iterator. Depth counts from the top-level value of the input, including when a nested value is
/// converted to an `Element` or written to a writer. Serde deserialization of binary input reads
/// lists, s-expressions, and structs with `LazyValue::read`, so it is limited too. With a limit
/// greater than 255, lazy binary navigation never returns the error, because binary values store
/// their depth in a `u8` that saturates at 255; conversions still check the limit. Raw writers and
/// `Display` do not check this limit.
///
/// Parsing text, converting values to `Element`s, and encoding values recurse at least once per
/// level of nesting. The default (64) leaves room in a 2 MiB thread stack (the default for threads
/// spawned by `std`) in both debug and release builds. Reading nested text structs uses the most
/// stack per level of the inputs measured; it exhausts that stack at roughly 100 levels in a debug
/// build.
///
/// The default can be overridden at build time by setting the `ION_RS_MAX_READ_WRITE_DEPTH`
/// environment variable to a base-10 integer no greater than 65535, e.g.
/// `ION_RS_MAX_READ_WRITE_DEPTH=512 cargo build`. An empty value is treated as unset, and any
/// other malformed or out-of-range value is a compile error. `rustc` records the read, so the
/// crate is rebuilt when the value changes. Nothing at runtime can raise the limit, so a library
/// that depends on `ion-rs` cannot raise it on behalf of the application that uses it.
pub(crate) const MAX_READ_WRITE_DEPTH: u16 =
    max_read_write_depth(option_env!("ION_RS_MAX_READ_WRITE_DEPTH"));

/// Returns the limit selected by `setting`, the value of `ION_RS_MAX_READ_WRITE_DEPTH` at build
/// time. `None` and an empty value select the default.
const fn max_read_write_depth(setting: Option<&str>) -> u16 {
    match setting {
        Some(text) if !text.is_empty() => parse_max_read_write_depth(text),
        _ => 64,
    }
}

/// Parses the `ION_RS_MAX_READ_WRITE_DEPTH` override in const context. Accepts a run of ASCII
/// digits whose value fits in a `u16`; anything else panics, which is a compile error when
/// evaluated for a `const`.
const fn parse_max_read_write_depth(text: &str) -> u16 {
    let bytes = text.as_bytes();
    let mut value: u16 = 0;
    let mut i = 0;
    while i < bytes.len() {
        let digit = bytes[i];
        assert!(
            digit.is_ascii_digit(),
            "ION_RS_MAX_READ_WRITE_DEPTH must be a base-10 integer"
        );
        let next = match value.checked_mul(10) {
            Some(tens) => tens.checked_add((digit - b'0') as u16),
            None => None,
        };
        value = match next {
            Some(next) => next,
            None => panic!("ION_RS_MAX_READ_WRITE_DEPTH must be no greater than 65535"),
        };
        i += 1;
    }
    value
}

pub(crate) mod v1_0 {
    use phf::phf_map;

    // The indexes in this slice are off by one relative to the corresponding Ion symbol ID.
    // This is because it does not contain symbol ID `0`-the symbol with unknown text.
    pub static SYSTEM_SYMBOLS: &[&str] = &[
        // <unknown text>              $0
        "$ion",                     // $1
        "$ion_1_0",                 // $2
        "$ion_symbol_table",        // $3
        "name",                     // $4
        "version",                  // $5
        "imports",                  // $6
        "symbols",                  // $7
        "max_id",                   // $8
        "$ion_shared_symbol_table", // $9
    ];

    #[allow(dead_code)]
    pub(crate) mod system_symbol_ids {
        pub const ION: usize = 1;
        pub const ION_1_0: usize = 2;
        pub const ION_SYMBOL_TABLE: usize = 3;
        pub const NAME: usize = 4;
        pub const VERSION: usize = 5;
        pub const IMPORTS: usize = 6;
        pub const SYMBOLS: usize = 7;
        pub const MAX_ID: usize = 8;
        pub const ION_SHARED_SYMBOL_TABLE: usize = 9;
    }

    /// A static, read-only map of text to Ion v1.0 system symbol addresses.
    /// Because the set of string keys is known at compile time, this map is able to use a
    /// perfect hashing function (PHF) to optimize lookup operations for those keys.
    pub(crate) static SYSTEM_SYMBOL_TEXT_TO_ID: phf::Map<&str, usize> = phf_map! {
        "$ion"                     => 1,
        "$ion_1_0"                 => 2,
        "$ion_symbol_table"        => 3,
        "name"                     => 4,
        "version"                  => 5,
        "imports"                  => 6,
        "symbols"                  => 7,
        "max_id"                   => 8,
        "$ion_shared_symbol_table" => 9,
    };
}

#[cfg(test)]
mod tests {
    use super::max_read_write_depth;
    use rstest::rstest;

    #[rstest]
    #[case::unset(None, 64)]
    #[case::empty(Some(""), 64)]
    #[case::zero(Some("0"), 0)]
    #[case::leading_zero(Some("064"), 64)]
    #[case::largest(Some("65535"), 65535)]
    fn accepts_depth_setting(#[case] setting: Option<&str>, #[case] expected: u16) {
        assert_eq!(max_read_write_depth(setting), expected);
    }

    #[rstest]
    #[case::just_too_large("65536")]
    #[case::too_large_after_multiplying("100000")]
    #[should_panic(expected = "no greater than 65535")]
    fn rejects_out_of_range_depth_setting(#[case] setting: &str) {
        max_read_write_depth(Some(setting));
    }

    #[rstest]
    #[case::letters("abc")]
    #[case::trailing_letter("6a")]
    #[case::negative("-1")]
    #[should_panic(expected = "base-10 integer")]
    fn rejects_non_digit_depth_setting(#[case] setting: &str) {
        max_read_write_depth(Some(setting));
    }
}
