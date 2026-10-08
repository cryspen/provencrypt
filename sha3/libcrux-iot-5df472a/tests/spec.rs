//! `libcrux-iot-sha3` against `pedantic-sha3`, the FIPS 202 transcript
//! its contracts name.
//!
//! The Lean proof shows that the thirteen contracted functions agree with the
//! transcript; these tests check the same claim by running both. Each function
//! is compared at input lengths around every multiple of the rate up to two
//! blocks, and the XOFs also at output lengths around the same boundaries: a
//! sponge goes wrong at its block boundaries, if anywhere. The incremental
//! `Xof` API, which the proof does not cover, is compared by splitting the
//! input at every such boundary. Last come random contents at random lengths.

use libcrux_iot_sha3::incremental::{Shake128Xof, Shake256Xof, Xof};
use libcrux_iot_sha3::Algorithm;
use libcrux_secrets::{Classify as _, ClassifyRef as _, DeclassifyRef as _, U8};
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

fn zeros(n: usize) -> Vec<U8> {
    vec![0u8; n].into_iter().map(|b| b.classify()).collect()
}

// ------------------------------------------------------------------
// Each SHA-3 digest, in its three forms: allocating, into a caller's
// buffer, and through the `hash` dispatcher.
// ------------------------------------------------------------------

macro_rules! digest {
    ($mod:ident, $len:expr, $rate:expr, $alloc:path, $ema:path, $alg:expr, $spec:path) => {
        mod $mod {
            use super::*;

            fn check(m: &[u8]) {
                let expected = $spec(m);
                let alloc = $alloc(m.classify_ref());
                assert_eq!(alloc.declassify_ref(), &expected[..], "allocating");
                let mut ema = zeros($len);
                $ema(&mut ema, m.classify_ref());
                assert_eq!(ema.declassify_ref(), &expected[..], "into a buffer");
                let hash: [U8; $len] = libcrux_iot_sha3::hash($alg, m.classify_ref());
                assert_eq!(hash.declassify_ref(), &expected[..], "hash");
            }

            #[test]
            fn input_boundaries() {
                for len in around_blocks($rate) {
                    check(&bytes(len, len as u64));
                }
            }

            proptest! {
                #![proptest_config(ProptestConfig::with_cases(64))]

                #[test]
                fn random(m in prop::collection::vec(any::<u8>(), 0..600)) {
                    check(&m);
                }
            }
        }
    };
}

digest!(
    sha3_224,
    28,
    SHA3_224_RATE,
    libcrux_iot_sha3::sha224,
    libcrux_iot_sha3::sha224_ema,
    Algorithm::Sha224,
    spec::sha3_224
);
digest!(
    sha3_256,
    32,
    SHA3_256_RATE,
    libcrux_iot_sha3::sha256,
    libcrux_iot_sha3::sha256_ema,
    Algorithm::Sha256,
    spec::sha3_256
);
digest!(
    sha3_384,
    48,
    SHA3_384_RATE,
    libcrux_iot_sha3::sha384,
    libcrux_iot_sha3::sha384_ema,
    Algorithm::Sha384,
    spec::sha3_384
);
digest!(
    sha3_512,
    64,
    SHA3_512_RATE,
    libcrux_iot_sha3::sha512,
    libcrux_iot_sha3::sha512_ema,
    Algorithm::Sha512,
    spec::sha3_512
);

// ------------------------------------------------------------------
// The XOFs. The allocating form takes its output length as a const
// generic, so it is compared at the output lengths below; the form
// writing into a caller's buffer at every length.
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
    st.absorb(m[..split_in].classify_ref());
    st.absorb_final(m[split_in..].classify_ref());
    let mut out = zeros(first + second);
    let (a, b) = out.split_at_mut(first);
    st.squeeze(a);
    st.squeeze(b);
    out.declassify_ref().to_vec()
}

macro_rules! xof {
    ($mod:ident, $rate:expr, $alloc:path, $ema:path, $xof:ty, $spec:path) => {
        mod $mod {
            use super::*;

            fn ema(m: &[u8], out: usize) -> Vec<u8> {
                let mut d = zeros(out);
                $ema(&mut d, m.classify_ref());
                d.declassify_ref().to_vec()
            }

            fn alloc_at<const N: usize>(m: &[u8]) {
                let d: [U8; N] = $alloc(m.classify_ref());
                assert_eq!(d.declassify_ref(), &$spec(m, N)[..], "output length {N}");
            }

            /// The allocating form at output lengths around one and two blocks.
            fn alloc(m: &[u8]) {
                alloc_at::<0>(m);
                alloc_at::<1>(m);
                alloc_at::<{ $rate - 1 }>(m);
                alloc_at::<{ $rate }>(m);
                alloc_at::<{ $rate + 1 }>(m);
                alloc_at::<{ 2 * $rate - 1 }>(m);
                alloc_at::<{ 2 * $rate }>(m);
                alloc_at::<{ 2 * $rate + 1 }>(m);
            }

            #[test]
            fn input_output_boundaries() {
                for len in around_blocks($rate) {
                    let m = bytes(len, len as u64);
                    alloc(&m);
                    for out in around_blocks($rate) {
                        assert_eq!(
                            ema(&m, out),
                            $spec(&m, out),
                            "input length {len}, output length {out}"
                        );
                    }
                }
            }

            #[test]
            fn incremental_splits() {
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

            proptest! {
                #![proptest_config(ProptestConfig::with_cases(64))]

                #[test]
                fn random(m in prop::collection::vec(any::<u8>(), 0..600), out in 0usize..700) {
                    prop_assert_eq!(ema(&m, out), $spec(&m, out));
                }

                /// A random message absorbed in two pieces at a random point,
                /// squeezed as a random number of whole blocks followed by a
                /// random remainder.
                #[test]
                fn incremental_random(
                    m in prop::collection::vec(any::<u8>(), 0..600),
                    split in any::<prop::sample::Index>(),
                    blocks in 1usize..4,
                    rest in 0usize..300,
                ) {
                    let split = split.index(m.len() + 1);
                    let first = blocks * $rate;
                    prop_assert_eq!(
                        xof_split::<$xof, $rate>(&m, split, first, rest),
                        $spec(&m, first + rest)
                    );
                }
            }
        }
    };
}

xof!(
    shake128,
    SHAKE128_RATE,
    libcrux_iot_sha3::shake128,
    libcrux_iot_sha3::shake128_ema,
    Shake128Xof,
    spec::shake128
);
xof!(
    shake256,
    SHAKE256_RATE,
    libcrux_iot_sha3::shake256,
    libcrux_iot_sha3::shake256_ema,
    Shake256Xof,
    spec::shake256
);
