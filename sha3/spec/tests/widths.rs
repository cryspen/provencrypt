//! `KECCAK-p[b, n_r]` at every width of Table 1, not only `b = 1600`.
//!
//! SHA-3 uses only `KECCAK-p[1600, 24]`, so every other test reaches the
//! permutation at that one width. This file checks the others: against the
//! Keccak team's known answers where they publish them, and against an
//! independent lane-oriented formulation at every width and round count.

// The lane formulation indexes lanes by `(x, y)` and round constants by `i_r`,
// as the Standard does; the indices are the point.
#![allow(clippy::needless_range_loop)]

use pedantic::bits::{h2b_full, Bit, BitString};
use pedantic::keccak_p::{keccak_f, keccak_p};
use pedantic_sha3 as pedantic;

// ---------------------------------------------------------------------------
// Known answers
// ---------------------------------------------------------------------------

/// `KECCAK-f[b]` applied once to the all-zero state, and once more to the
/// result, from `KeccakF-<b>-IntermediateValues.txt` in XKCP's
/// `tests/TestVectors` ("State after permutation"). The states are written as
/// bytes in the order of App. B.1, so `h2b` reads them as the Standard's
/// `b`-bit strings. XKCP publishes these for `b` of 200 and up only.
const XKCP: [(usize, &str, &str); 4] = [
    (
        200,
        "3C2826841CB35C171EAAE9B811134CEAA3852C69D2C5ABAFEA",
        "1BEF689492A8A543A5999FDB834E3166A14BE827D95040479E",
    ),
    (
        400,
        "F509AC40A90FF5149FE8A0ECD15B7078F0EF8FBF3703526075DCC90E76E74652A159815D956D146E3E63EE58FF714C718EB3",
        "37E5D6D5E7DBF3AAC79B7DCAB286ECFD2C695B4EB167AD15F7A76FA6FF678A3F992FC2E26B65315FA65B29CA24C25CB87C09",
    ),
    (
        800,
        "5DD431E5FBC604F499BFA0232F45F8F142D0FF5178F539E5A7800BF0643697AF4CF35ABF24247A22152717888458689F54D05CB10EFCF41B91FA66619A599E1A1F0A97A3879665AB688DABAF15104BE7981A0034F3EF1941760E0A937080B28796E9EF11",
        "0D2DBF75890E619B40AF26C8AB84CD64D6BD05F9352883BCB901805FCE2C66155EC9388E43E51F708043541BFFDEAC89DEB5ED51D902970E16AA196CEE3E91A29A4E75603C061998549270F484909FD059A22D77F75DB31D6201A65AD5258835AB3B78B3",
    ),
    (
        1600,
        "E7DDE140798F25F18A47C033F9CCD584EEA95AA61E2698D54D49806F304715BD57D05362054E288BD46F8E7F2DA497FFC44746A4A0E5FE90762E19D60CDA5B8C9C05191BF7A630AD64FC8FD0B75A933035D617233FA95AEB0321710D26E6A6A95F55CFDB167CA58126C84703CD31B8439F56A5111A2FF20161AED9215A63E505F270C98CF2FEBE641166C47B95703661CB0ED04F555A7CB8C832CF1C8AE83E8C14263AAE22790C94E409C5A224F94118C26504E72635F5163BA1307FE944F67549A2EC5C7BFFF1EA",
        "3CCB6EF94D955C2D6DB55770D02C336A6C6BD770128D3D0994D06955B2D9208A56F1E7E5994F9C4F38FB65DAA2B957F90DAF7512AE3D7785F710D8C347F2F4FA59879AF7E69E1B1F25B498EE0FCCFEE4A168CEB9B661CE684F978FBAC466EADEF5B1AF6E833DC433D9DB1927045406E065128309F0A9F87C434717BFA64954FD404B99D833ADDD9774E70B5DFCD5EA483CB0B755EEC8B8E3E9429E646E22A0917BDDBAE729310E90E8CCA3FAC59E2A20B63D1C4E4602345B59104CA4624E9F605CBF8F6AD26CD020",
    ),
];

fn state(hex: &str) -> BitString {
    h2b_full(&hex::decode(hex).unwrap()).to_bits()
}

#[test]
fn keccak_f_matches_xkcp() {
    for (b, once, twice) in XKCP {
        let f = |s: &[Bit]| match b {
            200 => keccak_f::<8>(s),
            400 => keccak_f::<16>(s),
            800 => keccak_f::<32>(s),
            1600 => keccak_f::<64>(s),
            _ => unreachable!(),
        };
        let first = f(&vec![false; b]);
        assert_eq!(first, state(once), "KECCAK-f[{b}](0^{b})");
        assert_eq!(
            f(&first),
            state(twice),
            "KECCAK-f[{b}] applied twice to 0^{b}"
        );
    }
}

// ---------------------------------------------------------------------------
// An independent formulation, at every width
// ---------------------------------------------------------------------------

/// The 24 round constants of `KECCAK-f[1600]`, as the Keccak reference
/// tabulates them. At lane size `w` the constant of round `i_r` is the low `w`
/// bits of entry `i_r`.
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808A,
    0x8000000080008000,
    0x000000000000808B,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008A,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000A,
    0x000000008000808B,
    0x800000000000008B,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800A,
    0x800000008000000A,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

/// The ρ offsets of Table 2 reduced mod 64, indexed `[x][y]`. At lane size
/// `w` they are reduced mod `w`.
const RHO: [[u32; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

/// `KECCAK-p[25w, n_r]` on lanes held in machine words: the step mappings as
/// the Keccak reference writes them, with tabulated constants in place of the
/// Standard's `(x, y)` walk and `rc` LFSR. Only round indices `0 ≤ i_r < 24`
/// have a tabulated constant, so `n_r` is at most `12 + 2l`.
fn lane_keccak_p(s: &[Bit], w: usize, n_r: usize) -> BitString {
    let l = w.trailing_zeros() as usize;
    let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
    let rot = |v: u64, n: u32| {
        let n = n % w as u32;
        if n == 0 {
            v
        } else {
            ((v << n) | (v >> (w as u32 - n))) & mask
        }
    };

    let mut a = [[0u64; 5]; 5];
    for x in 0..5 {
        for y in 0..5 {
            for z in 0..w {
                a[x][y] |= u64::from(s[w * (5 * y + x) + z]) << z;
            }
        }
    }
    for i_r in (12 + 2 * l - n_r)..(12 + 2 * l) {
        let c: Vec<u64> = (0..5)
            .map(|x| a[x].iter().fold(0, |acc, v| acc ^ v))
            .collect();
        for x in 0..5 {
            let d = c[(x + 4) % 5] ^ rot(c[(x + 1) % 5], 1);
            for y in 0..5 {
                a[x][y] ^= d;
            }
        }
        let mut b = [[0u64; 5]; 5];
        for x in 0..5 {
            for y in 0..5 {
                b[y][(2 * x + 3 * y) % 5] = rot(a[x][y], RHO[x][y]);
            }
        }
        for x in 0..5 {
            for y in 0..5 {
                a[x][y] = b[x][y] ^ (!b[(x + 1) % 5][y] & b[(x + 2) % 5][y] & mask);
            }
        }
        a[0][0] ^= RC[i_r] & mask;
    }

    let mut out = Vec::with_capacity(25 * w);
    for y in 0..5 {
        for x in 0..5 {
            for z in 0..w {
                out.push((a[x][y] >> z) & 1 == 1);
            }
        }
    }
    out
}

/// `n` pseudorandom bits, different for every `seed`.
fn bits(n: usize, seed: u64) -> BitString {
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x >> 63 == 1
        })
        .collect()
}

macro_rules! width_matches_lanes {
    ($name:ident, $w:literal) => {
        /// Every round count from 1 to `12 + 2l`, on a few random states.
        #[test]
        fn $name() {
            let rounds = 12 + 2 * ($w as usize).trailing_zeros() as usize;
            for n_r in 1..=rounds {
                for seed in 0..4 {
                    let s = bits(25 * $w, 1000 * n_r as u64 + seed);
                    assert_eq!(
                        keccak_p::<$w>(&s, n_r),
                        lane_keccak_p(&s, $w, n_r),
                        "KECCAK-p[{}, {n_r}], seed {seed}",
                        25 * $w
                    );
                }
            }
        }
    };
}

width_matches_lanes!(b25_matches_lanes, 1);
width_matches_lanes!(b50_matches_lanes, 2);
width_matches_lanes!(b100_matches_lanes, 4);
width_matches_lanes!(b200_matches_lanes, 8);
width_matches_lanes!(b400_matches_lanes, 16);
width_matches_lanes!(b800_matches_lanes, 32);
width_matches_lanes!(b1600_matches_lanes, 64);
