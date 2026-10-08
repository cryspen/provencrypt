//! The sponge construction, multi-rate padding and `KECCAK[c]` —
//! FIPS 202, Sec. 4, 5.1 and 5.2.

use crate::bits::{concat, trunc, xor, zeros, Bit, BitStr, BitString};
use crate::keccak_p::keccak_p;
use crate::nat::Nat;

/// Algorithm 9: `pad10*1(x, m)`.
///
/// Returns `P = 1 || 0^j || 1` where `j = (-m - 2) mod x`, so that `m + len(P)`
/// is a positive multiple of `x`.
pub fn pad10_star_1(x: Nat, m: Nat) -> BitStr {
    assert!(x > Nat::new(0), "Algorithm 9 takes a positive x");
    // `j = (-m - 2) mod x`. Written so that it never leaves the nonnegative
    // integers: `-m - 2 ≡ x - ((m + 2) mod x) (mod x)`, and reducing `m` first
    // keeps the sum small. The Standard's form would need a signed type, which
    // a length here is not — the subtraction below is the one place this crate
    // relies on `Nat`'s subtraction, and `(m % x + 2) % x < x` is what makes it
    // total.
    let j = (x - ((m % x + Nat::new(2)) % x)) % x;
    let one = BitStr::from_bits(&[true]);
    one.concat(&BitStr::zeros(j)).concat(&one)
}

/// Algorithm 8: `SPONGE[f, pad, r](N, d)` — Sec. 4.
///
/// The construction's three components, "an underlying function on
/// fixed-length strings, denoted by `f`", "a padding rule, denoted by `pad`"
/// and the rate `r`, are its first arguments, as in the Standard's notation.
/// The width `b` "is determined by the choice of `f`"; a Rust function does not
/// carry the length of the strings it takes, so `b` is passed alongside `f`.
pub fn sponge(
    f: impl Fn(&[Bit]) -> BitString,
    b: usize,
    pad: impl Fn(Nat, Nat) -> BitStr,
    r: Nat,
    n: &BitStr,
    d: Nat,
) -> BitStr {
    // Sec. 4: "The rate r is a positive integer that is strictly less than
    // the width b."
    assert!(
        r > Nat::new(0) && r < Nat::from_usize(b),
        "Sec. 4 takes 0 < r < b"
    );
    // 1. Let P = N || pad(r, len(N)).
    let p = n.concat(&pad(r, n.len()));
    // 2. Let n = len(P)/r.
    //    Step 4 cuts P into n blocks of exactly r bits, which takes `pad` to
    //    have made len(P) a multiple of r; `pad10*1` always does.
    assert!(
        p.len() % r == Nat::new(0),
        "Algorithm 8 needs len(P) to be a multiple of r"
    );
    let blocks = p.len() / r;
    // 3. Let c = b - r.
    //    `r < b ≤ 1600`, so the rate goes back down to a `usize` here
    //    without question; it is a `Nat` on the bit-string side because
    //    the lengths it is compared against are.
    let c = b - r.to_usize();
    // 4. Let P_0, … , P_{n-1} be the r-bit blocks of P.
    // 5. Let S = 0^b.
    let mut s = zeros(b);
    // 6. For i from 0 to n-1, let S = f(S ⊕ (P_i || 0^c)).
    let mut i = Nat::new(0);
    while i < blocks {
        let block = concat(&p.slice(i * r, r).to_bits(), &zeros(c));
        s = f(&xor(&s, &block));
        i = i + Nat::new(1);
    }
    // 7. Let Z be the empty string.
    let mut z = BitStr::empty();
    loop {
        // 8. Let Z = Z || Trunc_r(S).
        let head = trunc(&s, r.to_usize());
        z = z.concat(&BitStr::from_bits(&head));
        // 9. If d ≤ |Z|, then return Trunc_d(Z); else continue.
        if d <= z.len() {
            return z.trunc(d);
        }
        // 10. Let S = f(S), and continue with Step 8.
        s = f(&s);
    }
}

/// `b = 1600`, the width that `KECCAK[c]` restricts the KECCAK family to —
/// Sec. 5.2.
///
/// The family itself is defined for every `r + c` in Table 1; `KECCAK[c]` is
/// the case `b = 1600`, in which `r` is determined by the choice of `c`.
pub const B: usize = 1600;

/// Sec. 5.2: `KECCAK[c](N, d) = SPONGE[KECCAK-p[1600, 24], pad10*1, 1600-c](N, d)`.
pub fn keccak_c(c: usize, n: &BitStr, d: Nat) -> BitStr {
    // Both are closures, `pad10_star_1` included: the extraction does not
    // support function types, which naming a function as an argument would be.
    sponge(
        |s: &[Bit]| keccak_p::<64>(s, 24),
        B,
        |x, m| pad10_star_1(x, m),
        Nat::from_usize(B - c),
        n,
        d,
    )
}
