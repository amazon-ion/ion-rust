#[derive(Debug, Clone, Copy)]
pub enum ValueTokenKind {
    // An ASCII decimal digit, 0-9 inclusive, as well as `-` and `+`
    // Could be the start of an int, float, decimal, or timestamp.
    NumberOrTimestamp,
    // An ASCII letter, [a-zA-Z] inclusive.
    // Could be the start of a null, bool, identifier, or float (`nan`).
    Letter,
    // A `$` or `_`, which could be either a symbol ID (`$10`)
    // or an identifier (`$foo`, `_`).
    Symbol,
    // A `"` or `'`, which could be either a string or symbol.
    QuotedText,
    // `[`
    List,
    // `(`
    SExp,
    // `{`
    LobOrStruct,
    // Any other byte
    Invalid(u8),
}

/// A table of `ValueTokenKind` instances that can be queried by using the
/// byte in question as an index.
pub(crate) static TEXT_ION_TOKEN_KINDS: &[ValueTokenKind] = &init_value_token_cache();

pub(crate) const fn init_value_token_cache() -> [ValueTokenKind; 256] {
    let mut jump_table = [ValueTokenKind::Invalid(0); 256];
    let mut index: usize = 0;
    while index < 256 {
        let byte = index as u8;
        jump_table[index] = match byte {
            b'0'..=b'9' | b'-' | b'+' => ValueTokenKind::NumberOrTimestamp,
            b'a'..=b'z' | b'A'..=b'Z' => ValueTokenKind::Letter,
            b'$' | b'_' => ValueTokenKind::Symbol,
            b'"' | b'\'' => ValueTokenKind::QuotedText,
            b'[' => ValueTokenKind::List,
            b'(' => ValueTokenKind::SExp,
            b'{' => ValueTokenKind::LobOrStruct,
            other_byte => ValueTokenKind::Invalid(other_byte),
        };
        index += 1;
    }
    jump_table
}
