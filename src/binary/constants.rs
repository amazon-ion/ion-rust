// This module and its contents are visible as a workaround for:
// https://github.com/amazon-ion/ion-rust/issues/484

/// Constants for Ion v1.0
pub mod v1_0 {
    /// Ion Version Marker byte sequence
    pub const IVM: [u8; 4] = [0xE0, 0x01, 0x00, 0xEA];

    /// Constants for interpreting the length (`L`) code of binary values
    pub mod length_codes {
        pub const NULL: u8 = 15;
        pub const VAR_UINT: u8 = 14;
    }
}
