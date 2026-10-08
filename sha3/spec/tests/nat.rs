//! `nat::Nat` against the nonnegative integers it stands for.
//!
//! `Nat` is opaque to the extraction, so its Lean model in
//! `Assumptions/TypesExternal.lean` -- Lean's `Nat` -- is hand-written, and the
//! correspondence between that model and the `u128` below it is assumed rather
//! than proved. These tests are what stands in for the proof:
//!
//! * on operands small enough to read back through `to_usize`, every operation
//!   gives exactly what integer arithmetic gives;
//! * on full-width `u64` operands, whose sums and products leave `u64` (and
//!   `usize`), the laws of the nonnegative integers hold;
//! * what is partial in the model is partial here, and panics rather than
//!   wrapping: a difference below zero, division by zero, and handing back a
//!   value too large for a `usize`. So does the one place the `u128` stops
//!   where the model does not.

use pedantic_sha3::nat::Nat;
use proptest::prelude::*;

fn n(x: u64) -> Nat {
    Nat::new(x.into())
}

/// `2^64`, the first value no `u64` holds.
fn two_pow_64() -> Nat {
    n(u64::MAX) + n(1)
}

// ------------------------------------------------------------------
// Exact arithmetic, read back through `to_usize`.
// ------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    /// Operands below `2^16`, so that every result fits a `usize` on any target.
    #[test]
    fn small_operands_are_exact(a in 0u64..1 << 16, b in 0u64..1 << 16) {
        prop_assert_eq!((n(a) + n(b)).to_usize() as u64, a + b);
        prop_assert_eq!((n(a) * n(b)).to_usize() as u64, a * b);
        if a >= b {
            prop_assert_eq!((n(a) - n(b)).to_usize() as u64, a - b);
        }
        if b != 0 {
            prop_assert_eq!((n(a) / n(b)).to_usize() as u64, a / b);
            prop_assert_eq!((n(a) % n(b)).to_usize() as u64, a % b);
        }
    }

    #[test]
    fn conversions_agree(x in any::<usize>()) {
        prop_assert_eq!(Nat::from_usize(x), n(x as u64));
        prop_assert_eq!(Nat::from_usize(x).to_usize(), x);
    }

    /// Every comparison agrees with the integers', including at equality.
    #[test]
    fn comparisons_agree(a in any::<u64>(), b in any::<u64>(), same in any::<bool>()) {
        let b = if same { a } else { b };
        prop_assert_eq!(n(a) == n(b), a == b);
        prop_assert_eq!(n(a) != n(b), a != b);
        prop_assert_eq!(n(a) < n(b), a < b);
        prop_assert_eq!(n(a) <= n(b), a <= b);
        prop_assert_eq!(n(a) > n(b), a > b);
        prop_assert_eq!(n(a) >= n(b), a >= b);
        prop_assert_eq!(n(a).partial_cmp(&n(b)), a.partial_cmp(&b));
    }
}

// ------------------------------------------------------------------
// The laws of the nonnegative integers, past `u64`.
// ------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    #[test]
    fn addition_laws(a in any::<u64>(), b in any::<u64>(), c in any::<u64>()) {
        prop_assert_eq!(n(a) + n(b), n(b) + n(a));
        prop_assert_eq!((n(a) + n(b)) + n(c), n(a) + (n(b) + n(c)));
        prop_assert_eq!(n(a) + n(0), n(a));
        prop_assert_eq!((n(a) + n(b)) - n(b), n(a));
        prop_assert!(n(a) + n(b) >= n(a));
        prop_assert_eq!(n(a) + n(b) > n(a), b != 0);
    }

    #[test]
    fn multiplication_laws(a in any::<u64>(), b in any::<u64>(), c in 0u64..1 << 62) {
        prop_assert_eq!(n(a) * n(b), n(b) * n(a));
        prop_assert_eq!(n(a) * n(1), n(a));
        prop_assert_eq!(n(a) * n(0), n(0));
        // Distributivity, with every intermediate past `u64` and below the
        // `u128`'s end: `b + c < 2^63`, so `a · (b + c) < 2^127`.
        let b = b >> 2;
        prop_assert_eq!(n(a) * (n(b) + n(c)), n(a) * n(b) + n(a) * n(c));
        if b != 0 {
            prop_assert_eq!((n(a) * n(b)) / n(b), n(a));
            prop_assert_eq!((n(a) * n(b)) % n(b), n(0));
        }
    }

    /// Euclidean division, on dividends past `u64`.
    #[test]
    fn division_laws(hi in any::<u64>(), lo in any::<u64>(), b in 1u64..) {
        let a = n(hi) * two_pow_64() + n(lo);
        let (q, r) = (a / n(b), a % n(b));
        prop_assert_eq!(q * n(b) + r, a);
        prop_assert!(r < n(b));
    }

    /// `8 * len` for any length a `usize` can count, as `h2b` forms it.
    #[test]
    fn bit_counts_of_any_byte_length(len in any::<usize>()) {
        let bits = Nat::from_usize(len) * n(8);
        prop_assert_eq!(bits / n(8), Nat::from_usize(len));
        prop_assert_eq!(bits % n(8), n(0));
    }
}

// ------------------------------------------------------------------
// Partiality: where the model is partial, and where the `u128` stops.
// ------------------------------------------------------------------

#[test]
#[should_panic(expected = "difference below zero")]
fn difference_below_zero_panics() {
    let _ = n(1) - n(2);
}

#[test]
#[should_panic(expected = "division by zero")]
fn division_by_zero_panics() {
    let _ = n(1) / n(0);
}

#[test]
#[should_panic(expected = "division by zero")]
fn remainder_by_zero_panics() {
    let _ = n(1) % n(0);
}

#[test]
#[should_panic(expected = "too large to hand to the fixed-width layer")]
fn to_usize_past_usize_panics() {
    let _ = (Nat::from_usize(usize::MAX) + n(1)).to_usize();
}

/// `2^64 · 2^64 = 2^128` is where the `u128` ends. The model keeps counting;
/// the implementation stops rather than wrapping.
#[test]
#[should_panic(expected = "product too large")]
fn product_past_u128_panics() {
    let _ = two_pow_64() * two_pow_64();
}

#[test]
#[should_panic(expected = "sum too large")]
fn sum_past_u128_panics() {
    let near = two_pow_64() * n(u64::MAX) + n(u64::MAX); // 2^128 - 1
    let _ = near + n(1);
}
