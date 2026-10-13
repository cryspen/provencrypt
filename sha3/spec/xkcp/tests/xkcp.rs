//! `pedantic-sha3` against the reference code of the eXtended Keccak Code
//! Package.
//!
//! XKCP reaches further below SHA-3 than the other implementations the
//! specification is tested against, so the comparison goes layer by layer:
//!
//! * `KECCAK-p[b, n_r]` at every width XKCP has, `b` = 200, 400, 800 and 1600,
//!   and every round count from 1 to `12 + 2l`;
//! * the sponge on `KECCAK-f[b]` at every one of those widths and every rate
//!   that is a whole number of bytes, and with every suffix of up to seven
//!   bits that XKCP can append to a message -- among them SHA-3's `01`,
//!   SHAKE's `1111`, RawSHAKE's `11` and Keccak's empty one;
//! * the incremental sponge, with its input and its output split at every
//!   block boundary;
//! * the six functions of FIPS 202, one-shot at the block boundaries, and on
//!   messages of every bit length near a block boundary through `KeccakHash`,
//!   which is the one XKCP interface that takes messages that are not a whole
//!   number of bytes. The XOFs are also compared at output lengths that are
//!   not, by truncating XKCP's output;
//! * random messages, rates, suffixes and splits, via `proptest`.

use pedantic::bits::{b2h, h2b, h2b_full, BitStr};
use pedantic::keccak_p::{keccak_f, keccak_p};
use pedantic::nat::Nat;
use pedantic::sponge::{keccak_c, pad10_star_1, sponge};
use pedantic::{bytes as spec, sha3};
use pedantic_sha3 as pedantic;
use proptest::prelude::*;
use sha3_xkcp_tests as xkcp;
use sha3_xkcp_tests::{Hash, Sponge1600, WIDTHS};

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

/// A message of `n` bits: the bytes XKCP is given, with the last of them
/// partial and its unused high bits set, and the bit string `h2b` makes of
/// them -- the Standard's message.
fn message(n: usize, seed: u64) -> (Vec<u8>, BitStr) {
    let m = bytes(n.div_ceil(8), seed);
    let bits = h2b(&m, Nat::from_usize(n));
    (m, bits)
}

/// `0`, `1`, and `k·rate - 1`, `k·rate`, `k·rate + 1` for `k = 1, 2`.
fn around_blocks(rate: usize) -> Vec<usize> {
    let mut v = vec![0, 1];
    for k in 1..=2 {
        v.extend([k * rate - 1, k * rate, k * rate + 1]);
    }
    v
}

/// Every length within 16 of `0`, `rate` and `2·rate`: every residue mod 8 on
/// either side of every boundary, and so every way a suffix of up to four bits
/// and the padding can fall across one.
fn near_blocks(rate: usize) -> Vec<usize> {
    let mut v = Vec::new();
    for k in 0..=2 {
        v.extend((k * rate).saturating_sub(16)..=k * rate + 16);
    }
    v
}

/// The suffix bits XKCP's delimited byte stands for: those below its highest
/// set bit, least significant first.
fn suffix_bits(delimited: u8) -> BitStr {
    assert!(
        delimited != 0,
        "a delimited suffix has its delimiter bit set"
    );
    h2b(
        &[delimited],
        Nat::new(7 - u128::from(delimited.leading_zeros())),
    )
}

/// `KECCAK-p[b, n_r]` of the specification, on a state given as `b / 8` bytes.
fn spec_keccak_p(b: usize, state: &[u8], n_r: usize) -> Vec<u8> {
    let s = h2b_full(state).to_bits();
    let out = match b {
        200 => keccak_p::<8>(&s, n_r),
        400 => keccak_p::<16>(&s, n_r),
        800 => keccak_p::<32>(&s, n_r),
        1600 => keccak_p::<64>(&s, n_r),
        _ => unreachable!(),
    };
    b2h(&BitStr::from_bits(&out))
}

/// `SPONGE[KECCAK-f[b], pad10*1, r](N, d)` of the specification. At
/// `b = 1600` that is `KECCAK[1600 - r]`, Sec. 5.2, and goes through it.
fn spec_sponge(b: usize, r: usize, n: &BitStr, d: Nat) -> BitStr {
    let r_nat = Nat::from_usize(r);
    match b {
        200 => sponge(keccak_f::<8>, b, pad10_star_1, r_nat, n, d),
        400 => sponge(keccak_f::<16>, b, pad10_star_1, r_nat, n, d),
        800 => sponge(keccak_f::<32>, b, pad10_star_1, r_nat, n, d),
        1600 => keccak_c(1600 - r, n, d),
        _ => unreachable!(),
    }
}

/// `KeccakWidth<b>_Sponge` against [`spec_sponge`] on `m || suffix`, for
/// `out_bytes` bytes of output.
fn check_sponge(b: usize, r: usize, m: &[u8], suffix: u8, out_bytes: usize) {
    let n = h2b_full(m).concat(&suffix_bits(suffix));
    assert_eq!(
        xkcp::sponge(b, r, m, suffix, out_bytes),
        b2h(&spec_sponge(b, r, &n, Nat::from_usize(8 * out_bytes))),
        "b = {b}, r = {r}, input length {}, suffix {suffix:#04x}",
        m.len()
    );
}

// ------------------------------------------------------------------
// KECCAK-p[b, n_r], at every width and round count.
// ------------------------------------------------------------------

#[test]
fn keccak_p_every_width_and_round_count() {
    for b in WIDTHS {
        for n_r in 1..=xkcp::max_rounds(b) {
            for seed in 0..4 {
                let state = if seed == 0 {
                    vec![0; b / 8]
                } else {
                    bytes(b / 8, seed)
                };
                assert_eq!(
                    xkcp::keccak_p(b, &state, n_r),
                    spec_keccak_p(b, &state, n_r),
                    "KECCAK-p[{b}, {n_r}], state {seed}"
                );
            }
        }
    }
}

// ------------------------------------------------------------------
// The sponge, at every width.
// ------------------------------------------------------------------

/// The suffixes FIPS 202 appends, as XKCP delimits them: none, as in Keccak
/// before standardisation; `01` for the hash functions; `11` for RawSHAKE;
/// `1111` for SHAKE.
const SUFFIXES: [u8; 4] = [0x01, 0x06, 0x07, 0x1F];

/// Every rate `r` that is a whole number of bytes and leaves a capacity, at
/// every width; input lengths on either side of the first block boundary, and
/// output lengths just past it.
#[test]
fn sponge_every_width_and_rate() {
    for b in WIDTHS {
        for r in (8..b).step_by(8) {
            let block = r / 8;
            let suffix = SUFFIXES[block % SUFFIXES.len()];
            for len in [0, block - 1, block, block + 1] {
                check_sponge(b, r, &bytes(len, len as u64), suffix, block + 1);
            }
        }
    }
}

/// A rate at each width, as the Keccak team's `ShortMsgKAT_Keccakr<r>c<c>`
/// files and FIPS 202 use them. The ones below `1600` are not multiples of
/// the lane size.
const RATES: [(usize, usize); 4] = [(200, 40), (400, 144), (800, 640), (1600, 1088)];

/// Every suffix of zero to seven bits, on an empty message and on one that
/// leaves a single byte of the block for it: when the suffix is seven bits
/// long, its delimiter is the last bit of the block, and the padding's final
/// `1` needs a block of its own.
#[test]
fn sponge_every_suffix() {
    for (b, r) in RATES {
        for suffix in 1..=u8::MAX {
            for len in [0, r / 8 - 1] {
                check_sponge(b, r, &bytes(len, suffix as u64), suffix, r / 8 + 1);
            }
        }
    }
}

/// Inputs and outputs of several blocks, at each width.
#[test]
fn sponge_several_blocks() {
    for (b, r) in RATES {
        let block = r / 8;
        for len in around_blocks(block) {
            for out in around_blocks(block) {
                check_sponge(b, r, &bytes(len, out as u64), 0x06, out);
            }
        }
    }
}

// ------------------------------------------------------------------
// The incremental sponge.
// ------------------------------------------------------------------

/// Absorbs the input in two calls and squeezes the output in two, splitting
/// each at every length `around_blocks` gives, at the rates of SHAKE128 and
/// SHA3-512 and at one that is not a whole number of lanes.
#[test]
fn sponge1600_absorb_squeeze_splits() {
    for r in [1344, 576, 1000] {
        let block = r / 8;
        let m = bytes(2 * block + 1, r as u64);
        let out_len = 2 * block + 1;
        let expected = b2h(&keccak_c(
            1600 - r,
            &h2b_full(&m).concat(&suffix_bits(0x1F)),
            Nat::from_usize(8 * out_len),
        ));
        for split_in in around_blocks(block) {
            for split_out in around_blocks(block) {
                let mut st = Sponge1600::new(r);
                st.absorb(&m[..split_in]);
                st.absorb(&m[split_in..]);
                st.absorb_last_few_bits(0x1F);
                let mut out = vec![0u8; out_len];
                let (a, b) = out.split_at_mut(split_out);
                st.squeeze(a);
                st.squeeze(b);
                assert_eq!(
                    out, expected,
                    "r = {r}, input split {split_in}, output split {split_out}"
                );
            }
        }
    }
}

/// `KeccakWidth1600_SpongeSqueeze` straight after absorbing pads with the
/// empty suffix: `KECCAK[c]` on the message itself.
#[test]
fn sponge1600_squeeze_without_suffix() {
    for len in around_blocks(136) {
        let m = bytes(len, len as u64);
        let mut st = Sponge1600::new(1088);
        st.absorb(&m);
        let mut out = [0u8; 32];
        st.squeeze(&mut out);
        assert_eq!(
            out[..],
            b2h(&keccak_c(512, &h2b_full(&m), Nat::new(256))),
            "input length {len}"
        );
    }
}

// ------------------------------------------------------------------
// The FIPS 202 functions.
// ------------------------------------------------------------------

#[test]
fn simple_fips202_hashes_input_boundaries() {
    for len in around_blocks(144) {
        let m = bytes(len, len as u64);
        assert_eq!(
            xkcp::sha3_224(&m),
            spec::sha3_224(&m),
            "SHA3-224, input length {len}"
        );
    }
    for len in around_blocks(136) {
        let m = bytes(len, len as u64);
        assert_eq!(
            xkcp::sha3_256(&m),
            spec::sha3_256(&m),
            "SHA3-256, input length {len}"
        );
    }
    for len in around_blocks(104) {
        let m = bytes(len, len as u64);
        assert_eq!(
            xkcp::sha3_384(&m),
            spec::sha3_384(&m),
            "SHA3-384, input length {len}"
        );
    }
    for len in around_blocks(72) {
        let m = bytes(len, len as u64);
        assert_eq!(
            xkcp::sha3_512(&m),
            spec::sha3_512(&m),
            "SHA3-512, input length {len}"
        );
    }
}

#[test]
fn simple_fips202_xofs_input_output_boundaries() {
    for len in around_blocks(168) {
        let m = bytes(len, len as u64);
        for out in around_blocks(168) {
            assert_eq!(
                xkcp::shake128(&m, out),
                spec::shake128(&m, out),
                "SHAKE128, input length {len}, output length {out}"
            );
        }
    }
    for len in around_blocks(136) {
        let m = bytes(len, len as u64);
        for out in around_blocks(136) {
            assert_eq!(
                xkcp::shake256(&m, out),
                spec::shake256(&m, out),
                "SHAKE256, input length {len}, output length {out}"
            );
        }
    }
}

/// One of the six functions of FIPS 202, on bit strings, next to the
/// `KeccakHash` instance that computes it.
struct Function {
    name: &'static str,
    /// The rate, in bits.
    rate: usize,
    xkcp: fn() -> Hash,
    /// The function, with the output length `d` that the XOFs take and the
    /// hash functions ignore.
    spec: fn(&BitStr, Nat) -> BitStr,
    /// The output length of a hash function, in bits; `None` for an XOF.
    digest: Option<usize>,
}

const FUNCTIONS: [Function; 6] = [
    Function {
        name: "SHA3-224",
        rate: 1152,
        xkcp: Hash::sha3_224,
        spec: |m, _| sha3::sha3_224(m),
        digest: Some(224),
    },
    Function {
        name: "SHA3-256",
        rate: 1088,
        xkcp: Hash::sha3_256,
        spec: |m, _| sha3::sha3_256(m),
        digest: Some(256),
    },
    Function {
        name: "SHA3-384",
        rate: 832,
        xkcp: Hash::sha3_384,
        spec: |m, _| sha3::sha3_384(m),
        digest: Some(384),
    },
    Function {
        name: "SHA3-512",
        rate: 576,
        xkcp: Hash::sha3_512,
        spec: |m, _| sha3::sha3_512(m),
        digest: Some(512),
    },
    Function {
        name: "SHAKE128",
        rate: 1344,
        xkcp: Hash::shake128,
        spec: sha3::shake128,
        digest: None,
    },
    Function {
        name: "SHAKE256",
        rate: 1088,
        xkcp: Hash::shake256,
        spec: sha3::shake256,
        digest: None,
    },
];

/// `f` on the first `bits` bits of `m` through `KeccakHash`, given as whole
/// bytes up to byte `split` and then the rest, for `out_bits` bits of output
/// (a multiple of 8).
fn keccak_hash(f: &Function, m: &[u8], bits: usize, split: usize, out_bits: usize) -> Vec<u8> {
    let split = split.min(bits / 8);
    let mut st = (f.xkcp)();
    st.update(&m[..split], 8 * split);
    st.update(&m[split..], bits - 8 * split);
    match f.digest {
        Some(digest) => {
            assert_eq!(out_bits, digest, "{} has a fixed output length", f.name);
            let mut out = vec![0u8; digest / 8];
            st.finalize(&mut out);
            out
        }
        None => {
            st.finalize(&mut []);
            let mut out = vec![0u8; out_bits / 8];
            st.squeeze(&mut out);
            out
        }
    }
}

/// Messages of every bit length within 16 of the empty message and of the
/// first two block boundaries, through `Keccak_HashUpdate`, which takes the
/// last few bits of a message in the low bits of its last byte. The XOFs are
/// squeezed one byte past a block.
#[test]
fn keccak_hash_message_bit_lengths() {
    for f in &FUNCTIONS {
        let out_bits = f.digest.unwrap_or(f.rate + 8);
        for len in near_blocks(f.rate) {
            let (m, bits) = message(len, len as u64);
            assert_eq!(
                keccak_hash(f, &m, len, len / 16, out_bits),
                b2h(&(f.spec)(&bits, Nat::from_usize(out_bits))),
                "{}, message length {len} bits",
                f.name
            );
        }
    }
}

/// XOF outputs of every bit length within 16 of the empty output and of the
/// first two block boundaries. XKCP squeezes whole bytes only, so the
/// Standard's `d`-bit output is compared against the first `d` bits of
/// XKCP's `⌈d / 8⌉` bytes: the sponge's output is a prefix of a longer one.
#[test]
fn xofs_output_bit_lengths() {
    for f in FUNCTIONS.iter().filter(|f| f.digest.is_none()) {
        let (m, bits) = message(100, 1);
        for d in near_blocks(f.rate) {
            let out = keccak_hash(f, &m, 100, 5, 8 * d.div_ceil(8));
            assert_eq!(
                h2b(&out, Nat::from_usize(d)),
                (f.spec)(&bits, Nat::from_usize(d)),
                "{}, output length {d} bits",
                f.name
            );
        }
    }
}

/// `Keccak_HashFinal` followed by `Keccak_HashSqueeze`s of every length
/// `around_blocks` gives, for both XOFs.
#[test]
fn keccak_hash_squeeze_splits() {
    for f in FUNCTIONS.iter().filter(|f| f.digest.is_none()) {
        let block = f.rate / 8;
        let (m, bits) = message(8 * block + 3, 2);
        let out_len = 2 * block + 1;
        let expected = b2h(&(f.spec)(&bits, Nat::from_usize(8 * out_len)));
        for split in around_blocks(block) {
            let mut st = (f.xkcp)();
            st.update(&m, 8 * block + 3);
            st.finalize(&mut []);
            let mut out = vec![0u8; out_len];
            let (a, b) = out.split_at_mut(split);
            st.squeeze(a);
            st.squeeze(b);
            assert_eq!(out, expected, "{}, output split {split}", f.name);
        }
    }
}

/// `KECCAK[c]` with no suffix -- Keccak as submitted to the SHA-3
/// competition, before FIPS 202 added its suffixes -- through `KeccakHash`,
/// at every capacity of Keccak's four fixed-length instances, on messages of
/// bit lengths near the block boundaries.
#[test]
fn keccak_hash_keccak_c() {
    for c in [448, 512, 768, 1024] {
        let r = 1600 - c;
        for len in near_blocks(r).into_iter().step_by(3) {
            let (m, bits) = message(len, len as u64);
            let mut st = Hash::new(r, c, c / 2, 0x01);
            st.update(&m, len);
            let mut out = vec![0u8; c / 16];
            st.finalize(&mut out);
            assert_eq!(
                out,
                b2h(&keccak_c(c, &bits, Nat::from_usize(c / 2))),
                "KECCAK[{c}], message length {len} bits"
            );
        }
    }
}

// ------------------------------------------------------------------
// Random contents at random lengths.
// ------------------------------------------------------------------

proptest! {
    #![proptest_config(ProptestConfig::with_cases(32))]

    /// A random function of FIPS 202 on a random message of a random number
    /// of bits, split at a random byte.
    #[test]
    fn fips202_random(
        f in 0..FUNCTIONS.len(),
        m in prop::collection::vec(any::<u8>(), 0..400),
        drop in 0usize..8,
        split in 0usize..400,
        xof_out in 1usize..400,
    ) {
        let f = &FUNCTIONS[f];
        let bits = (8 * m.len()).saturating_sub(drop);
        let out_bits = f.digest.unwrap_or(8 * xof_out);
        prop_assert_eq!(
            keccak_hash(f, &m, bits, split, out_bits),
            b2h(&(f.spec)(&h2b(&m, Nat::from_usize(bits)), Nat::from_usize(out_bits)))
        );
    }

    /// The sponge at a random width and rate, on a random message with a
    /// random suffix.
    #[test]
    fn sponge_random(
        b in prop::sample::select(WIDTHS.to_vec()),
        r_bytes in 1usize..200,
        m in prop::collection::vec(any::<u8>(), 0..300),
        suffix in 1u8..=u8::MAX,
        out in 0usize..300,
    ) {
        let r = 8 * (1 + (r_bytes - 1) % (b / 8 - 1));
        let n = h2b_full(&m).concat(&suffix_bits(suffix));
        prop_assert_eq!(
            xkcp::sponge(b, r, &m, suffix, out),
            b2h(&spec_sponge(b, r, &n, Nat::from_usize(8 * out)))
        );
    }

    /// `KECCAK-p[b, n_r]` on a random state.
    #[test]
    fn keccak_p_random(
        b in prop::sample::select(WIDTHS.to_vec()),
        state in prop::collection::vec(any::<u8>(), 200),
        n_r in 1usize..=24,
    ) {
        let n_r = 1 + (n_r - 1) % xkcp::max_rounds(b);
        let state = &state[..b / 8];
        prop_assert_eq!(xkcp::keccak_p(b, state, n_r), spec_keccak_p(b, state, n_r));
    }
}
