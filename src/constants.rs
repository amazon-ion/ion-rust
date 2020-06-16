pub(crate) mod v1_0 {
    pub const SYSTEM_SYMBOLS: &[&str] = &[
        "$0",                       // $0
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
}
