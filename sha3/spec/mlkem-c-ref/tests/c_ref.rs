//! `pedantic-sha3` against `fips202.c` of the ML-KEM C reference
//! implementation.
//!
//! The one-shot functions are compared at input lengths around every multiple
//! of the rate up to two blocks, and the XOFs also at output lengths around
//! the same boundaries: a sponge goes wrong at its block boundaries, if
//! anywhere. The incremental API is compared by splitting the input and the
//! output at every such boundary, and by squeezing whole blocks the way ML-KEM
//! samples its matrix. Last come the exact shapes ML-KEM feeds its `G`, `H`,
//! `J`, `PRF` and `XOF` (FIPS 203, Sec. 4.1) for all three parameter sets, and
//! random contents at random lengths.

use pedantic_sha3::bytes as spec;
use proptest::prelude::*;
use sha3_mlkem_c_ref_tests as c_ref;
use sha3_mlkem_c_ref_tests::{Shake128, Shake256};

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

// ------------------------------------------------------------------
// One-shot functions, at the block boundaries.
// ------------------------------------------------------------------

#[test]
fn sha3_256_input_boundaries() {
    for len in around_blocks(c_ref::SHA3_256_RATE) {
        let m = bytes(len, len as u64);
        assert_eq!(
            c_ref::sha3_256(&m),
            spec::sha3_256(&m),
            "input length {len}"
        );
    }
}

#[test]
fn sha3_512_input_boundaries() {
    for len in around_blocks(c_ref::SHA3_512_RATE) {
        let m = bytes(len, len as u64);
        assert_eq!(
            c_ref::sha3_512(&m),
            spec::sha3_512(&m),
            "input length {len}"
        );
    }
}

#[test]
fn shake128_input_output_boundaries() {
    for len in around_blocks(c_ref::SHAKE128_RATE) {
        let m = bytes(len, len as u64);
        for out in around_blocks(c_ref::SHAKE128_RATE) {
            assert_eq!(
                c_ref::shake128(&m, out),
                spec::shake128(&m, out),
                "input length {len}, output length {out}"
            );
        }
    }
}

#[test]
fn shake256_input_output_boundaries() {
    for len in around_blocks(c_ref::SHAKE256_RATE) {
        let m = bytes(len, len as u64);
        for out in around_blocks(c_ref::SHAKE256_RATE) {
            assert_eq!(
                c_ref::shake256(&m, out),
                spec::shake256(&m, out),
                "input length {len}, output length {out}"
            );
        }
    }
}

// ------------------------------------------------------------------
// The incremental API.
// ------------------------------------------------------------------

macro_rules! incremental_tests {
    ($absorb_squeeze:ident, $blocks:ident, $xof:ident, $spec:path) => {
        /// Absorbs the input in two calls and squeezes the output in two,
        /// splitting each at every length `around_blocks` gives.
        #[test]
        fn $absorb_squeeze() {
            let rate = $xof::RATE;
            let m = bytes(2 * rate + 1, 1);
            let out_len = 2 * rate + 1;
            let expected = $spec(&m, out_len);
            for split_in in around_blocks(rate) {
                for split_out in around_blocks(rate) {
                    let mut st = $xof::init();
                    st.absorb(&m[..split_in]);
                    st.absorb(&m[split_in..]);
                    st.finalize();
                    let mut out = vec![0u8; out_len];
                    let (a, b) = out.split_at_mut(split_out);
                    st.squeeze(a);
                    st.squeeze(b);
                    assert_eq!(
                        out, expected,
                        "input split {split_in}, output split {split_out}"
                    );
                }
            }
        }

        /// `absorb_once` followed by whole blocks, first one at a time and
        /// then all at once, followed by a `squeeze` that picks up after them.
        #[test]
        fn $blocks() {
            let rate = $xof::RATE;
            for len in around_blocks(rate) {
                let m = bytes(len, len as u64);
                let expected = $spec(&m, 3 * rate + 5);

                let mut st = $xof::absorb_once(&m);
                let mut out = vec![0u8; 3 * rate + 5];
                st.squeezeblocks(&mut out[..rate]);
                st.squeezeblocks(&mut out[rate..3 * rate]);
                st.squeeze(&mut out[3 * rate..]);
                assert_eq!(out, expected, "input length {len}");

                let mut st = $xof::absorb_once(&m);
                let mut out = vec![0u8; 3 * rate];
                st.squeezeblocks(&mut out);
                assert_eq!(out, expected[..3 * rate], "input length {len}");
            }
        }
    };
}

incremental_tests!(
    shake128_absorb_squeeze_splits,
    shake128_squeezeblocks,
    Shake128,
    spec::shake128
);
incremental_tests!(
    shake256_absorb_squeeze_splits,
    shake256_squeezeblocks,
    Shake256,
    spec::shake256
);

// ------------------------------------------------------------------
// The inputs ML-KEM gives its hash functions (FIPS 203, Sec. 4.1).
// ------------------------------------------------------------------

/// The three parameter sets: `k`, `η1`, `η2`, `d_u`, `d_v`.
const PARAMS: [(usize, usize, usize, usize, usize); 3] = [
    (2, 3, 2, 10, 4), // ML-KEM-512
    (3, 2, 2, 10, 4), // ML-KEM-768
    (4, 2, 2, 11, 5), // ML-KEM-1024
];

/// `G(c) = SHA3-512(c)`: on `d || k` (33 bytes) in `ML-KEM.KeyGen_internal`,
/// on `m || H(ek)` (64 bytes) in `Encaps_internal` and `m' || h` in
/// `Decaps_internal`.
#[test]
fn mlkem_g() {
    for (k, _, _, _, _) in PARAMS {
        let mut d_k = bytes(32, 1);
        d_k.push(k as u8);
        assert_eq!(c_ref::sha3_512(&d_k), spec::sha3_512(&d_k), "k = {k}");
    }
    let m_h = bytes(64, 2);
    assert_eq!(c_ref::sha3_512(&m_h), spec::sha3_512(&m_h));
}

/// `H(s) = SHA3-256(s)` on the encapsulation key, `384k + 32` bytes.
#[test]
fn mlkem_h() {
    for (k, _, _, _, _) in PARAMS {
        let ek = bytes(384 * k + 32, k as u64);
        assert_eq!(c_ref::sha3_256(&ek), spec::sha3_256(&ek), "k = {k}");
    }
}

/// `J(s) = SHAKE256(s, 8·32)` on `z || c`, with the ciphertext
/// `32(d_u·k + d_v)` bytes long.
#[test]
fn mlkem_j() {
    for (k, _, _, d_u, d_v) in PARAMS {
        let z_c = bytes(32 + 32 * (d_u * k + d_v), k as u64);
        assert_eq!(
            c_ref::shake256(&z_c, 32),
            spec::shake256(&z_c, 32),
            "k = {k}"
        );
        let mut st = Shake256::init();
        st.absorb(&z_c[..32]);
        st.absorb(&z_c[32..]);
        st.finalize();
        let mut out = [0u8; 32];
        st.squeeze(&mut out);
        assert_eq!(out[..], spec::shake256(&z_c, 32), "k = {k}, incremental");
    }
}

/// `PRF_η(s, b) = SHAKE256(s || b, 8·64η)`, for both `η` of every parameter
/// set, the way `ref/symmetric-shake.c` computes it.
#[test]
fn mlkem_prf() {
    for (k, eta1, eta2, _, _) in PARAMS {
        for eta in [eta1, eta2] {
            for b in 0..(2 * k) as u8 {
                let mut s_b = bytes(32, eta as u64);
                s_b.push(b);
                assert_eq!(
                    c_ref::shake256(&s_b, 64 * eta),
                    spec::shake256(&s_b, 64 * eta),
                    "k = {k}, eta = {eta}, b = {b}"
                );
            }
        }
    }
}

/// `XOF(ρ, i, j)` as `SampleNTT` reads it: `SHAKE128(ρ || j || i)`, squeezed
/// in 168-byte blocks. `ref/indcpa.c` squeezes `GEN_MATRIX_NBLOCKS = 3`
/// blocks up front and one block at a time after that; five blocks cover both.
#[test]
fn mlkem_xof() {
    let rho = bytes(32, 3);
    let k = 4;
    for i in 0..k as u8 {
        for j in 0..k as u8 {
            let mut seed = rho.clone();
            seed.extend([j, i]);
            let mut st = Shake128::absorb_once(&seed);
            let mut out = vec![0u8; 5 * Shake128::RATE];
            st.squeezeblocks(&mut out[..3 * Shake128::RATE]);
            st.squeezeblocks(&mut out[3 * Shake128::RATE..4 * Shake128::RATE]);
            st.squeezeblocks(&mut out[4 * Shake128::RATE..]);
            assert_eq!(out, spec::shake128(&seed, out.len()), "i = {i}, j = {j}");
        }
    }
}

// ------------------------------------------------------------------
// Random contents at random lengths.
// ------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    #[test]
    fn sha3_256_random(m in prop::collection::vec(any::<u8>(), 0..400)) {
        prop_assert_eq!(c_ref::sha3_256(&m), spec::sha3_256(&m));
    }

    #[test]
    fn sha3_512_random(m in prop::collection::vec(any::<u8>(), 0..400)) {
        prop_assert_eq!(c_ref::sha3_512(&m), spec::sha3_512(&m));
    }

    #[test]
    fn shake128_random(m in prop::collection::vec(any::<u8>(), 0..400), out in 0usize..600) {
        prop_assert_eq!(c_ref::shake128(&m, out), spec::shake128(&m, out));
    }

    #[test]
    fn shake256_random(m in prop::collection::vec(any::<u8>(), 0..400), out in 0usize..600) {
        prop_assert_eq!(c_ref::shake256(&m, out), spec::shake256(&m, out));
    }
}
