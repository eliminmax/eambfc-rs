// SPDX-FileCopyrightText: 2025 Eli Array Minkoff
//
// SPDX-License-Identifier: GPL-3.0-only

/// An extension trait that's used to provide a `fits_within_bits` method used within some backends
pub(super) trait MinimumBits {
    /// Returns `true` if the value of `self` can be stored within an integer of size `bits`
    ///
    /// For signed types, acts as though the hypothetical `i{bits}` type is a 2's complement signed
    /// type, and for unsigned types, acts as though the the hypothetical `u{bits}` type is also
    /// unsigned.
    fn fits_within_bits(self, bits: u32) -> bool;
}

/// Truncate `val` to `amnt` bits and sign extend the result
pub(super) const fn sign_extend(val: i64, amnt: u32) -> i64 {
    val << (i64::BITS - amnt) >> (i64::BITS - amnt)
}

macro_rules! impl_min_bits {
    ([unsigned] $t: ty) => {
        impl MinimumBits for $t {
            fn fits_within_bits(self, bits: u32) -> bool {
                self < <$t>::pow(2, bits)
            }
        }
    };
    ([signed] $t: ty) => {
        impl MinimumBits for $t {
            fn fits_within_bits(self, bits: u32) -> bool {
                self >= -<$t>::pow(2, bits - 1) && self < <$t>::pow(2, bits - 1)
            }
        }
    };
}

impl_min_bits!([signed] i8);
impl_min_bits!([signed] i16);
impl_min_bits!([signed] i32);
impl_min_bits!([signed] i64);
impl_min_bits!([unsigned] u8);
impl_min_bits!([unsigned] u16);
impl_min_bits!([unsigned] u32);
impl_min_bits!([unsigned] u64);

#[cfg(test)]
mod test_min_bits {
    use super::MinimumBits;

    #[test]
    fn test_unsigned() {
        macro_rules! test_for {
            ($t: ty) => {
                for i in 1..(<$t>::BITS - 1) {
                    let tst_val = <$t>::pow(2, i);
                    assert!(tst_val.fits_within_bits(i + 1));
                    assert!(!tst_val.fits_within_bits(i));
                    assert!((tst_val - 1).fits_within_bits(i));
                }
            };
        }
        test_for!(u8);
        test_for!(u16);
        test_for!(u32);
        test_for!(u64);
    }

    #[test]
    fn test_signed() {
        macro_rules! test_for {
            ($t: ty) => {
                for i in 1..(<$t>::BITS - 2) {
                    let tst_val = <$t>::pow(2, i);
                    assert!(tst_val.fits_within_bits(i + 2));
                    assert!(!tst_val.fits_within_bits(i + 1));
                    assert!((-tst_val).fits_within_bits(i + 1));
                    assert!(!(-tst_val).fits_within_bits(i));
                    assert!((tst_val - 1).fits_within_bits(i + 1));
                }
            };
        }
        test_for!(i8);
        test_for!(i16);
        test_for!(i32);
        test_for!(i64);
    }
}
