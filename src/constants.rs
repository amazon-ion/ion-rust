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

pub(crate) mod v1_1 {
    use phf::phf_map;

    pub mod constants {
        pub const DEFAULT_MODULE_NAME: &str = "_";
    }
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
        "encoding",                 // $10
        "$ion_literal",             // $11
        "$ion_shared_module",       // $12
        "macro",                    // $13
        "macro_table",              // $14
        "symbol_table",             // $15
        "module",                   // $16
        "export",                   // $17
        "import",                   // $18
        "flex_symbol",              // $19
        "flex_int",                 // $20
        "flex_uint",                // $21
        "uint8",                    // $22
        "uint16",                   // $23
        "uint32",                   // $24
        "uint64",                   // $25
        "int8",                     // $26
        "int16",                    // $27
        "int32",                    // $28
        "int64",                    // $29
        "float16",                  // $30
        "float32",                  // $31
        "float64",                  // $32
        "",                         // $33 (empty text)
        "for",                      // $34
        "literal",                  // $35
        "if_none",                  // $36
        "if_some",                  // $37
        "if_single",                // $38
        "if_multi",                 // $39
        "none",                     // $40
        "values",                   // $41
        "default",                  // $42
        "meta",                     // $43
        "repeat",                   // $44
        "flatten",                  // $45
        "delta",                    // $46
        "sum",                      // $47
        "annotate",                 // $48
        "make_string",              // $49
        "make_symbol",              // $50
        "make_decimal",             // $51
        "make_timestamp",           // $52
        "make_blob",                // $53
        "make_list",                // $54
        "make_sexp",                // $55
        "make_field",               // $56
        "make_struct",              // $57
        "parse_ion",                // $58
        "set_symbols",              // $59
        "add_symbols",              // $60
        "set_macros",               // $61
        "add_macros",               // $62
        "use",                      // $63
    ];

    pub mod system_symbols {
        use crate::raw_symbol_ref::SystemSymbol_1_1;

        pub const ION: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(1);
        pub const ENCODING: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(10);
        pub const SYMBOL_TABLE: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(15);
        pub const MODULE: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(16);
        pub const EMPTY_TEXT: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(33);
        pub const ADD_SYMBOLS: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(60);
        pub const ADD_MACROS: SystemSymbol_1_1 = SystemSymbol_1_1::new_unchecked(62);
    }

    /// A static, read-only map of text to Ion v1.1 system symbol addresses.
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
        "encoding"                 => 10,
        "$ion_literal"             => 11,
        "$ion_shared_module"       => 12,
        "macro"                    => 13,
        "macro_table"              => 14,
        "symbol_table"             => 15,
        "module"                   => 16,
        "export"                   => 17,
        "import"                   => 18,
        "flex_symbol"              => 19,
        "flex_int"                 => 20,
        "flex_uint"                => 21,
        "uint8"                    => 22,
        "uint16"                   => 23,
        "uint32"                   => 24,
        "uint64"                   => 25,
        "int8"                     => 26,
        "int16"                    => 27,
        "int32"                    => 28,
        "int64"                    => 29,
        "float16"                  => 30,
        "float32"                  => 31,
        "float64"                  => 32,
        ""                         => 33,
        "for"                      => 34,
        "literal"                  => 35,
        "if_none"                  => 36,
        "if_some"                  => 37,
        "if_single"                => 38,
        "if_multi"                 => 39,
        "none"                     => 40,
        "values"                   => 41,
        "default"                  => 42,
        "meta"                     => 43,
        "repeat"                   => 44,
        "flatten"                  => 45,
        "delta"                    => 46,
        "sum"                      => 47,
        "annotate"                 => 48,
        "make_string"              => 49,
        "make_symbol"              => 50,
        "make_decimal"             => 51,
        "make_timestamp"           => 52,
        "make_blob"                => 53,
        "make_list"                => 54,
        "make_sexp"                => 55,
        "make_field"               => 56,
        "make_struct"              => 57,
        "parse_ion"                => 58,
        "set_symbols"              => 59,
        "add_symbols"              => 60,
        "set_macros"               => 61,
        "add_macros"               => 62,
        "use"                      => 63,
    };
}
