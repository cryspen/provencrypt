//! Safe bindings to `ref/fips202.c` of the ML-KEM C reference implementation,
//! <https://github.com/pq-crystals/kyber>, vendored verbatim in `c/`.
//!
//! That file is the SHA-3 code ML-KEM's `G`, `H`, `J`, `PRF` and `XOF` are
//! built from (`ref/symmetric-shake.c`). It offers `SHA3-256`, `SHA3-512`,
//! `SHAKE128` and `SHAKE256`, each one-shot, and the two XOFs also as an
//! incremental absorb/squeeze API; all of it is bound here, so the tests can
//! hold every entry point against `pedantic-sha3`.

/// `SHAKE128_RATE` from `fips202.h`, in bytes.
pub const SHAKE128_RATE: usize = 168;
/// `SHAKE256_RATE` from `fips202.h`, in bytes.
pub const SHAKE256_RATE: usize = 136;
/// `SHA3_256_RATE` from `fips202.h`, in bytes.
pub const SHA3_256_RATE: usize = 136;
/// `SHA3_512_RATE` from `fips202.h`, in bytes.
pub const SHA3_512_RATE: usize = 72;

mod ffi {
    use std::os::raw::c_uint;

    /// `keccak_state` from `fips202.h`.
    #[repr(C)]
    pub struct KeccakState {
        pub s: [u64; 25],
        pub pos: c_uint,
    }

    // `fips202.h` renames every function through `FIPS202_NAMESPACE`, so the
    // linked symbols carry the `pqcrystals_kyber_fips202_ref_` prefix.
    extern "C" {
        pub fn pqcrystals_kyber_fips202_ref_shake128_init(state: *mut KeccakState);
        pub fn pqcrystals_kyber_fips202_ref_shake128_absorb(
            state: *mut KeccakState,
            input: *const u8,
            inlen: usize,
        );
        pub fn pqcrystals_kyber_fips202_ref_shake128_finalize(state: *mut KeccakState);
        pub fn pqcrystals_kyber_fips202_ref_shake128_squeeze(
            out: *mut u8,
            outlen: usize,
            state: *mut KeccakState,
        );
        pub fn pqcrystals_kyber_fips202_ref_shake128_absorb_once(
            state: *mut KeccakState,
            input: *const u8,
            inlen: usize,
        );
        pub fn pqcrystals_kyber_fips202_ref_shake128_squeezeblocks(
            out: *mut u8,
            nblocks: usize,
            state: *mut KeccakState,
        );

        pub fn pqcrystals_kyber_fips202_ref_shake256_init(state: *mut KeccakState);
        pub fn pqcrystals_kyber_fips202_ref_shake256_absorb(
            state: *mut KeccakState,
            input: *const u8,
            inlen: usize,
        );
        pub fn pqcrystals_kyber_fips202_ref_shake256_finalize(state: *mut KeccakState);
        pub fn pqcrystals_kyber_fips202_ref_shake256_squeeze(
            out: *mut u8,
            outlen: usize,
            state: *mut KeccakState,
        );
        pub fn pqcrystals_kyber_fips202_ref_shake256_absorb_once(
            state: *mut KeccakState,
            input: *const u8,
            inlen: usize,
        );
        pub fn pqcrystals_kyber_fips202_ref_shake256_squeezeblocks(
            out: *mut u8,
            nblocks: usize,
            state: *mut KeccakState,
        );

        pub fn pqcrystals_kyber_fips202_ref_shake128(
            out: *mut u8,
            outlen: usize,
            input: *const u8,
            inlen: usize,
        );
        pub fn pqcrystals_kyber_fips202_ref_shake256(
            out: *mut u8,
            outlen: usize,
            input: *const u8,
            inlen: usize,
        );
        pub fn pqcrystals_kyber_fips202_ref_sha3_256(h: *mut u8, input: *const u8, inlen: usize);
        pub fn pqcrystals_kyber_fips202_ref_sha3_512(h: *mut u8, input: *const u8, inlen: usize);
    }
}

/// `sha3_256` from `fips202.c`.
pub fn sha3_256(m: &[u8]) -> [u8; 32] {
    let mut h = [0u8; 32];
    unsafe { ffi::pqcrystals_kyber_fips202_ref_sha3_256(h.as_mut_ptr(), m.as_ptr(), m.len()) };
    h
}

/// `sha3_512` from `fips202.c`.
pub fn sha3_512(m: &[u8]) -> [u8; 64] {
    let mut h = [0u8; 64];
    unsafe { ffi::pqcrystals_kyber_fips202_ref_sha3_512(h.as_mut_ptr(), m.as_ptr(), m.len()) };
    h
}

/// `shake128` from `fips202.c`, with the output length in bytes.
pub fn shake128(m: &[u8], out_bytes: usize) -> Vec<u8> {
    let mut out = vec![0u8; out_bytes];
    unsafe {
        ffi::pqcrystals_kyber_fips202_ref_shake128(out.as_mut_ptr(), out.len(), m.as_ptr(), m.len())
    };
    out
}

/// `shake256` from `fips202.c`, with the output length in bytes.
pub fn shake256(m: &[u8], out_bytes: usize) -> Vec<u8> {
    let mut out = vec![0u8; out_bytes];
    unsafe {
        ffi::pqcrystals_kyber_fips202_ref_shake256(out.as_mut_ptr(), out.len(), m.as_ptr(), m.len())
    };
    out
}

macro_rules! xof {
    ($(#[$meta:meta])* $name:ident, $rate:expr,
     $init:ident, $absorb:ident, $finalize:ident, $squeeze:ident,
     $absorb_once:ident, $squeezeblocks:ident) => {
        $(#[$meta])*
        pub struct $name(ffi::KeccakState);

        impl $name {
            /// The rate in bytes, i.e. the block length of [`Self::squeezeblocks`].
            pub const RATE: usize = $rate;

            /// `*_init`: an empty state, ready to [`Self::absorb`].
            pub fn init() -> Self {
                let mut st = ffi::KeccakState { s: [0; 25], pos: 0 };
                unsafe { ffi::$init(&mut st) };
                Self(st)
            }

            /// `*_absorb`: may be called any number of times before
            /// [`Self::finalize`].
            pub fn absorb(&mut self, m: &[u8]) {
                unsafe { ffi::$absorb(&mut self.0, m.as_ptr(), m.len()) };
            }

            /// `*_finalize`: pads and ends the absorbing phase.
            pub fn finalize(&mut self) {
                unsafe { ffi::$finalize(&mut self.0) };
            }

            /// `*_squeeze`: any number of bytes, callable repeatedly after
            /// [`Self::finalize`] or [`Self::absorb_once`].
            pub fn squeeze(&mut self, out: &mut [u8]) {
                unsafe { ffi::$squeeze(out.as_mut_ptr(), out.len(), &mut self.0) };
            }

            /// `*_absorb_once`: absorbs and finalizes in one call.
            pub fn absorb_once(m: &[u8]) -> Self {
                let mut st = ffi::KeccakState { s: [0; 25], pos: 0 };
                unsafe { ffi::$absorb_once(&mut st, m.as_ptr(), m.len()) };
                Self(st)
            }

            /// `*_squeezeblocks`: `out.len() / RATE` whole blocks. It is only
            /// meant to follow [`Self::absorb_once`] or other whole blocks,
            /// and it does not update the position [`Self::squeeze`] reads.
            pub fn squeezeblocks(&mut self, out: &mut [u8]) {
                assert!(out.len() % Self::RATE == 0, "squeezeblocks takes whole blocks");
                unsafe { ffi::$squeezeblocks(out.as_mut_ptr(), out.len() / Self::RATE, &mut self.0) };
            }
        }
    };
}

xof!(
    /// The incremental `shake128_*` API of `fips202.c`.
    Shake128, SHAKE128_RATE,
    pqcrystals_kyber_fips202_ref_shake128_init,
    pqcrystals_kyber_fips202_ref_shake128_absorb,
    pqcrystals_kyber_fips202_ref_shake128_finalize,
    pqcrystals_kyber_fips202_ref_shake128_squeeze,
    pqcrystals_kyber_fips202_ref_shake128_absorb_once,
    pqcrystals_kyber_fips202_ref_shake128_squeezeblocks
);
xof!(
    /// The incremental `shake256_*` API of `fips202.c`.
    Shake256, SHAKE256_RATE,
    pqcrystals_kyber_fips202_ref_shake256_init,
    pqcrystals_kyber_fips202_ref_shake256_absorb,
    pqcrystals_kyber_fips202_ref_shake256_finalize,
    pqcrystals_kyber_fips202_ref_shake256_squeeze,
    pqcrystals_kyber_fips202_ref_shake256_absorb_once,
    pqcrystals_kyber_fips202_ref_shake256_squeezeblocks
);
