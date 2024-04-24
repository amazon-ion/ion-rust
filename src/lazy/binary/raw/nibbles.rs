//! This module provides utility methods for splitting a byte into its component nibbles or joining
//! two nibbles to form a new byte value.

const MAX_NIBBLE_VALUE: u8 = 15;
const NIBBLE_SIZE_IN_BITS: u8 = 4;

/// Given a byte, will return a tuple containing the values of its left and right nibbles.
pub(crate) const fn nibbles_from_byte(byte: u8) -> (u8, u8) {
    let left = byte >> NIBBLE_SIZE_IN_BITS;
    let right = byte & 0b1111;
    (left, right)
}

/// Will join the given left and right nibbles into a new byte value.
pub(crate) fn byte_from_nibbles(left: u8, right: u8) -> u8 {
    assert!(left <= MAX_NIBBLE_VALUE);
    assert!(right <= MAX_NIBBLE_VALUE);
    (left << NIBBLE_SIZE_IN_BITS) | right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_byte_from_nibbles() {
        assert_eq!(byte_from_nibbles(0b1111, 0b1111), 0b1111_1111);
        assert_eq!(byte_from_nibbles(0b0000, 0b0000), 0b0000_0000);
        assert_eq!(byte_from_nibbles(0b1111, 0b0000), 0b1111_0000);
        assert_eq!(byte_from_nibbles(0b0000, 0b1111), 0b0000_1111);
        assert_eq!(byte_from_nibbles(0b0011, 0b1100), 0b0011_1100);
        assert_eq!(byte_from_nibbles(0b1010, 0b0101), 0b1010_0101);
    }

    #[test]
    fn test_nibbles_from_byte() {
        assert_eq!(nibbles_from_byte(0b1111_1111), (0b1111, 0b1111));
        assert_eq!(nibbles_from_byte(0b0000_0000), (0b0000, 0b0000));
        assert_eq!(nibbles_from_byte(0b0000_1111), (0b0000, 0b1111));
        assert_eq!(nibbles_from_byte(0b1111_0000), (0b1111, 0b0000));
        assert_eq!(nibbles_from_byte(0b1010_1010), (0b1010, 0b1010));
        assert_eq!(nibbles_from_byte(0b0101_0101), (0b0101, 0b0101));
        assert_eq!(nibbles_from_byte(0b1001_1001), (0b1001, 0b1001));
    }
}
