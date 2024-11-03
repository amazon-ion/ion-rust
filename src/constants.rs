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

pub(crate) mod v1_1 {
    use crate::types::SymbolAddress;
    use phf::phf_map;

    pub static SYSTEM_SYMBOLS: &[&str] = &[
        // <unknown text>               $0
        "$ion",                     //  $1
        "$ion_1_0",                 //  $2
        "$ion_symbol_table",        //  $3
        "name",                     //  $4
        "version",                  //  $5
        "imports",                  //  $6
        "symbols",                  //  $7
        "max_id",                   //  $8
        "$ion_shared_symbol_table", //  $9
        "$ion_encoding",            // $10
        "$ion_literal",             // $11
        "$ion_shared_module",       // $12
        "macro",                    // $13
        "macro_table",              // $14
        "symbol_table",             // $15
        "module",                   // $16
        "<REMOVE>",                 // $17 (see: ion-docs#345)
        "export",                   // $18
        "<REMOVE>",                 // $19 (see: ion-docs#345)
        "import",                   // $20
        "",                         // $21 (empty text)
        "literal",                  // $22
        "if_none",                  // $23
        "if_some",                  // $24
        "if_single",                // $25
        "if_multi",                 // $26
        "for",                      // $27
        "default",                  // $28
        "values",                   // $29
        "annotate",                 // $30
        "make_string",              // $31
        "make_symbol",              // $32
        "make_blob",                // $33
        "make_decimal",             // $34
        "make_timestamp",           // $35
        "make_list",                // $36
        "make_sexp",                // $37
        "make_struct",              // $38
        "parse_ion",                // $39
        "repeat",                   // $40
        "delta",                    // $41
        "flatten",                  // $42
        "sum",                      // $43
        "set_symbols",              // $44
        "add_symbols",              // $45
        "set_macros",               // $46
        "add_macros",               // $47
        "use",                      // $48
        "meta",                     // $49
        "flex_symbol",              // $50
        "flex_int",                 // $51
        "flex_uint",                // $52
        "uint8",                    // $53
        "uint16",                   // $54
        "uint32",                   // $55
        "uint64",                   // $56
        "int8",                     // $57
        "int16",                    // $58
        "int32",                    // $59
        "int64",                    // $60
        "float16",                  // $61
        "float32",                  // $62
        "float64",                  // $63
        "none",                     // $64
        "make_field",               // $65
    ];

    pub mod system_symbol_ids {
        use crate::raw_symbol_ref::SystemSymbol_1_1;

        pub const ION_ENCODING: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(10);
        pub const SYMBOL_TABLE: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(15);
        pub const ADD_SYMBOLS: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(45);
        pub const ADD_MACROS: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(47);
    }

    /// A static, read-only map of text to Ion v1.1 system symbol addresses.
    /// Because the set of string keys is known at compile time, this map is able to use a
    /// perfect hashing function (PHF) to optimize lookup operations for those keys.
    pub(crate) static SYSTEM_SYMBOL_TEXT_TO_ID: phf::Map<&str, usize> = phf_map! {
        "$ion"                     =>  1,
        "$ion_1_0"                 =>  2,
        "$ion_symbol_table"        =>  3,
        "name"                     =>  4,
        "version"                  =>  5,
        "imports"                  =>  6,
        "symbols"                  =>  7,
        "max_id"                   =>  8,
        "$ion_shared_symbol_table" =>  9,
        "$ion_encoding"            => 10,
        "$ion_literal"             => 11,
        "$ion_shared_module"       => 12,
        "macro"                    => 13,
        "macro_table"              => 14,
        "symbol_table"             => 15,
        "module"                   => 16,
        // ion-docs#345            => 17,
        "export"                   => 18,
        // ion-docs#345            => 19,
        "import"                   => 20,
        ""                         => 21,
        "literal"                  => 22,
        "if_none"                  => 23,
        "if_some"                  => 24,
        "if_single"                => 25,
        "if_multi"                 => 26,
        "for"                      => 27,
        "default"                  => 28,
        "values"                   => 29,
        "annotate"                 => 30,
        "make_string"              => 31,
        "make_symbol"              => 32,
        "make_blob"                => 33,
        "make_decimal"             => 34,
        "make_timestamp"           => 35,
        "make_list"                => 36,
        "make_sexp"                => 37,
        "make_struct"              => 38,
        "parse_ion"                => 39,
        "repeat"                   => 40,
        "delta"                    => 41,
        "flatten"                  => 42,
        "sum"                      => 43,
        "set_symbols"              => 44,
        "add_symbols"              => 45,
        "set_macros"               => 46,
        "add_macros"               => 47,
        "use"                      => 48,
        "meta"                     => 49,
        "flex_symbol"              => 50,
        "flex_int"                 => 51,
        "flex_uint"                => 52,
        "uint8"                    => 53,
        "uint16"                   => 54,
        "uint32"                   => 55,
        "uint64"                   => 56,
        "int8"                     => 57,
        "int16"                    => 58,
        "int32"                    => 59,
        "int64"                    => 60,
        "float16"                  => 61,
        "float32"                  => 62,
        "float64"                  => 63,
        "none"                     => 64,
        "make_field"               => 65,
    };

    pub fn address_for_text(text: &str) -> Option<usize> {
        SYSTEM_SYMBOL_TEXT_TO_ID.get(text).copied()
    }

    pub fn symbol_text_for_address(address: SymbolAddress) -> Option<&'static str> {
        SYSTEM_SYMBOLS.get(address - 1).copied()
    }
}
