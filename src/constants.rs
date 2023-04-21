pub(crate) mod v1_0 {
    pub const SYSTEM_SYMBOLS: &[Option<&str>] = &[
        None,                             // $0
        Some("$ion"),                     // $1
        Some("$ion_1_0"),                 // $2
        Some("$ion_symbol_table"),        // $3
        Some("name"),                     // $4
        Some("version"),                  // $5
        Some("imports"),                  // $6
        Some("symbols"),                  // $7
        Some("max_id"),                   // $8
        Some("$ion_shared_symbol_table"), // $9
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
