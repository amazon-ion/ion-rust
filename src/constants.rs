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
