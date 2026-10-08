//! `pedantic-sha3` against the `libcrux-sha3` implementation.
//!
//! All six functions are compared one-shot at input lengths around every
//! multiple of the rate up to two blocks, and the XOFs also at output lengths
//! around the same boundaries: a sponge goes wrong at its block boundaries, if
//! anywhere. The incremental `Xof` API is compared by splitting the input at
//! every such boundary and the output after whole blocks, and the block API
//! ML-KEM uses by squeezing whole blocks after a single-block absorb. Last come
//! random contents at random lengths, and random splits of the incremental
//! input.

use libcrux_sha3::portable as reference;
use libcrux_sha3::portable::incremental::{Shake128Xof, Shake256Xof, Xof};
use pedantic_sha3::bytes as spec;
use proptest::prelude::*;

const SHA3_224_RATE: usize = 144;
const SHA3_256_RATE: usize = 136;
const SHA3_384_RATE: usize = 104;
const SHA3_512_RATE: usize = 72;
const SHAKE128_RATE: usize = 168;
const SHAKE256_RATE: usize = 136;

/// `n` bytes that differ from each other and from one call to the next `seed`,
/// so that a message is never all zeros or a shifted copy of another.
fn bytes(n: usize, seed: u64) -> Vec<u8> {
    let mut x = seed.wrapping_mul(0x9e37_79b9_7f4a_7c15) | 1;
    (0..n)
        .map(|_| {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            (x >> 32) as u8
        })
        .collect()
}

/// `0`, `1`, and `k·rate - 1`, `k·rate`, `k·rate + 1` for `k = 1, 2`.
fn around_blocks(rate: usize) -> Vec<usize> {
    let mut v = vec![0, 1];
    for k in 1..=2 {
        v.extend([k * rate - 1, k * rate, k * rate + 1]);
    }
    v
}

fn ref_sha3_224(m: &[u8]) -> [u8; 28] {
    let mut d = [0u8; 28];
    reference::sha224(&mut d, m);
    d
}

fn ref_sha3_256(m: &[u8]) -> [u8; 32] {
    let mut d = [0u8; 32];
    reference::sha256(&mut d, m);
    d
}

fn ref_sha3_384(m: &[u8]) -> [u8; 48] {
    let mut d = [0u8; 48];
    reference::sha384(&mut d, m);
    d
}

fn ref_sha3_512(m: &[u8]) -> [u8; 64] {
    let mut d = [0u8; 64];
    reference::sha512(&mut d, m);
    d
}

fn ref_shake128(m: &[u8], out: usize) -> Vec<u8> {
    let mut d = vec![0u8; out];
    reference::shake128(&mut d, m);
    d
}

fn ref_shake256(m: &[u8], out: usize) -> Vec<u8> {
    let mut d = vec![0u8; out];
    reference::shake256(&mut d, m);
    d
}

// ------------------------------------------------------------------
// One-shot functions, at the block boundaries.
// ------------------------------------------------------------------

macro_rules! digest_boundaries {
    ($name:ident, $rate:expr, $reference:ident, $spec:path) => {
        #[test]
        fn $name() {
            for len in around_blocks($rate) {
                let m = bytes(len, len as u64);
                assert_eq!($reference(&m), $spec(&m), "input length {len}");
            }
        }
    };
}

digest_boundaries!(
    sha3_224_input_boundaries,
    SHA3_224_RATE,
    ref_sha3_224,
    spec::sha3_224
);
digest_boundaries!(
    sha3_256_input_boundaries,
    SHA3_256_RATE,
    ref_sha3_256,
    spec::sha3_256
);
digest_boundaries!(
    sha3_384_input_boundaries,
    SHA3_384_RATE,
    ref_sha3_384,
    spec::sha3_384
);
digest_boundaries!(
    sha3_512_input_boundaries,
    SHA3_512_RATE,
    ref_sha3_512,
    spec::sha3_512
);

macro_rules! xof_boundaries {
    ($name:ident, $rate:expr, $reference:ident, $spec:path) => {
        #[test]
        fn $name() {
            for len in around_blocks($rate) {
                let m = bytes(len, len as u64);
                for out in around_blocks($rate) {
                    assert_eq!(
                        $reference(&m, out),
                        $spec(&m, out),
                        "input length {len}, output length {out}"
                    );
                }
            }
        }
    };
}

xof_boundaries!(
    shake128_input_output_boundaries,
    SHAKE128_RATE,
    ref_shake128,
    spec::shake128
);
xof_boundaries!(
    shake256_input_output_boundaries,
    SHAKE256_RATE,
    ref_shake256,
    spec::shake256
);

// ------------------------------------------------------------------
// The incremental `Xof` API.
// ------------------------------------------------------------------

/// Absorbs `m` split at `split_in`, then squeezes `first` bytes followed by
/// `second`. The `Xof`'s output is not buffered across calls: a squeeze that
/// is not a whole number of blocks makes the next one start at a fresh block.
/// So `first` is whole blocks here, and `second` is any length.
fn xof_split<X: Xof<R>, const R: usize>(
    m: &[u8],
    split_in: usize,
    first: usize,
    second: usize,
) -> Vec<u8> {
    let mut st = X::new();
    st.absorb(&m[..split_in]);
    st.absorb_final(&m[split_in..]);
    let mut out = vec![0u8; first + second];
    let (a, b) = out.split_at_mut(first);
    st.squeeze(a);
    st.squeeze(b);
    out
}

macro_rules! xof_incremental {
    ($name:ident, $xof:ty, $rate:expr, $spec:path) => {
        #[test]
        fn $name() {
            let m = bytes(2 * $rate + 1, 1);
            for split_in in around_blocks($rate) {
                for first in [$rate, 2 * $rate] {
                    for second in around_blocks($rate) {
                        assert_eq!(
                            xof_split::<$xof, $rate>(&m, split_in, first, second),
                            $spec(&m, first + second),
                            "input split {split_in}, output {first} + {second}"
                        );
                    }
                }
            }
        }
    };
}

xof_incremental!(
    shake128_xof_splits,
    Shake128Xof,
    SHAKE128_RATE,
    spec::shake128
);
xof_incremental!(
    shake256_xof_splits,
    Shake256Xof,
    SHAKE256_RATE,
    spec::shake256
);

// ------------------------------------------------------------------
// The block API ML-KEM samples with.
// ------------------------------------------------------------------

/// `shake128_absorb_final` on less than one block, then three blocks at once
/// and two more one at a time -- the way ML-KEM samples its matrix.
#[test]
fn shake128_blocks() {
    for len in [0, 1, 34, SHAKE128_RATE - 1] {
        let m = bytes(len, len as u64);
        let mut st = reference::incremental::shake128_init();
        reference::incremental::shake128_absorb_final(&mut st, &m);
        let mut out = vec![0u8; 5 * SHAKE128_RATE];
        reference::incremental::shake128_squeeze_first_three_blocks(
            &mut st,
            &mut out[..3 * SHAKE128_RATE],
        );
        reference::incremental::shake128_squeeze_next_block(
            &mut st,
            &mut out[3 * SHAKE128_RATE..4 * SHAKE128_RATE],
        );
        reference::incremental::shake128_squeeze_next_block(&mut st, &mut out[4 * SHAKE128_RATE..]);
        assert_eq!(out, spec::shake128(&m, out.len()), "input length {len}");

        let mut st = reference::incremental::shake128_init();
        reference::incremental::shake128_absorb_final(&mut st, &m);
        let mut out = vec![0u8; 5 * SHAKE128_RATE];
        reference::incremental::shake128_squeeze_first_five_blocks(&mut st, &mut out);
        assert_eq!(
            out,
            spec::shake128(&m, out.len()),
            "input length {len}, five blocks"
        );
    }
}

/// `shake256_absorb_final` on less than one block, then one block followed by
/// two more.
#[test]
fn shake256_blocks() {
    for len in [0, 1, 33, SHAKE256_RATE - 1] {
        let m = bytes(len, len as u64);
        let mut st = reference::incremental::shake256_init();
        reference::incremental::shake256_absorb_final(&mut st, &m);
        let mut out = vec![0u8; 3 * SHAKE256_RATE];
        reference::incremental::shake256_squeeze_first_block(&mut st, &mut out[..SHAKE256_RATE]);
        reference::incremental::shake256_squeeze_next_block(
            &mut st,
            &mut out[SHAKE256_RATE..2 * SHAKE256_RATE],
        );
        reference::incremental::shake256_squeeze_next_block(&mut st, &mut out[2 * SHAKE256_RATE..]);
        assert_eq!(out, spec::shake256(&m, out.len()), "input length {len}");
    }
}

// ------------------------------------------------------------------
// Random contents at random lengths.
// ------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn sha3_224_random(m in prop::collection::vec(any::<u8>(), 0..600)) {
        prop_assert_eq!(ref_sha3_224(&m), spec::sha3_224(&m));
    }

    #[test]
    fn sha3_256_random(m in prop::collection::vec(any::<u8>(), 0..600)) {
        prop_assert_eq!(ref_sha3_256(&m), spec::sha3_256(&m));
    }

    #[test]
    fn sha3_384_random(m in prop::collection::vec(any::<u8>(), 0..600)) {
        prop_assert_eq!(ref_sha3_384(&m), spec::sha3_384(&m));
    }

    #[test]
    fn sha3_512_random(m in prop::collection::vec(any::<u8>(), 0..600)) {
        prop_assert_eq!(ref_sha3_512(&m), spec::sha3_512(&m));
    }

    #[test]
    fn shake128_random(m in prop::collection::vec(any::<u8>(), 0..600), out in 0usize..700) {
        prop_assert_eq!(ref_shake128(&m, out), spec::shake128(&m, out));
    }

    #[test]
    fn shake256_random(m in prop::collection::vec(any::<u8>(), 0..600), out in 0usize..700) {
        prop_assert_eq!(ref_shake256(&m, out), spec::shake256(&m, out));
    }

    /// A random message absorbed in two pieces at a random point, squeezed as
    /// a random number of whole blocks followed by a random remainder.
    #[test]
    fn shake128_xof_random(
        m in prop::collection::vec(any::<u8>(), 0..600),
        split in any::<prop::sample::Index>(),
        blocks in 1usize..4,
        rest in 0usize..300,
    ) {
        let split = split.index(m.len() + 1);
        let first = blocks * SHAKE128_RATE;
        prop_assert_eq!(
            xof_split::<Shake128Xof, SHAKE128_RATE>(&m, split, first, rest),
            spec::shake128(&m, first + rest)
        );
    }

    #[test]
    fn shake256_xof_random(
        m in prop::collection::vec(any::<u8>(), 0..600),
        split in any::<prop::sample::Index>(),
        blocks in 1usize..4,
        rest in 0usize..300,
    ) {
        let split = split.index(m.len() + 1);
        let first = blocks * SHAKE256_RATE;
        prop_assert_eq!(
            xof_split::<Shake256Xof, SHAKE256_RATE>(&m, split, first, rest),
            spec::shake256(&m, first + rest)
        );
    }
}
