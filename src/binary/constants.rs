/// Constants for Ion v1.0
pub(crate) mod v1_0 {
    /// Ion Version Marker byte sequence
    pub(crate) const IVM: [u8; 4] = [0xE0, 0x01, 0x00, 0xEA];

    /// Constants for interpreting the length (`L`) code of binary values
    pub(crate) mod length_codes {
        pub const NULL: u8 = 15;
        pub const VAR_UINT: u8 = 14;
    }

    pub(crate) mod system_symbol_ids {
        pub const ION_SYMBOL_TABLE: usize = 3;
    }
}
