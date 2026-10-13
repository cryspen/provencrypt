//! Safe bindings to the reference code of the eXtended Keccak Code Package,
//! <https://github.com/XKCP/XKCP>, vendored verbatim in `c/`.
//!
//! XKCP is the Keccak team's own code. Three of its layers are bound here:
//!
//! * the permutations, `KeccakP<b>_Permute_Nrounds`, which is
//!   `KECCAK-p[b, n_r]` for any `n_r` up to `12 + 2l`. `b = 1600` comes from
//!   the current XKCP (`c/4affab4`); `b` = 200, 400 and 800 from the last
//!   commit that has them (`c/fa7033a`), since XKCP has since dropped them;
//! * the sponge on top of each, `KeccakWidth<b>_Sponge`, at any rate that is a
//!   multiple of 8, with up to seven bits of suffix appended to the message;
//!   at `b = 1600` also incrementally, as [`Sponge1600`];
//! * the FIPS 202 interfaces: `SimpleFIPS202.c`'s one-shot functions, and
//!   `KeccakHash.c`'s [`Hash`], which is the one place XKCP takes a message
//!   whose length is not a whole number of bytes.

use std::os::raw::{c_int, c_uchar, c_uint};

mod ffi {
    use super::*;

    /// `KeccakP1600_plain8_state` from `KeccakP-1600-SnP.h`.
    #[repr(C)]
    #[derive(Clone, Copy)]
    pub struct KeccakP1600State {
        pub a: [u8; 200],
    }

    /// `KeccakWidth1600_SpongeInstance` from `KeccakSponge.h`.
    #[repr(C)]
    #[derive(Clone, Copy)]
    pub struct KeccakWidth1600SpongeInstance {
        pub state: KeccakP1600State,
        pub rate: c_uint,
        pub byte_io_index: c_uint,
        pub squeezing: c_int,
    }

    /// `Keccak_HashInstance` from `KeccakHash.h`.
    #[repr(C)]
    #[derive(Clone, Copy)]
    pub struct KeccakHashInstance {
        pub sponge: KeccakWidth1600SpongeInstance,
        pub fixed_output_length: c_uint,
        pub delimited_suffix: c_uchar,
    }

    /// The state the `void *` of `KeccakP200`, `KeccakP400` and `KeccakP800`
    /// points to: `KeccakP<b>_stateSizeInBytes` bytes, at most 100, aligned to
    /// `KeccakP<b>_stateAlignment`, at most 4.
    #[repr(C, align(8))]
    pub struct SmallState(pub [u8; 100]);

    macro_rules! small_width {
        ($init:ident, $overwrite:ident, $permute:ident, $extract:ident, $sponge:ident) => {
            pub fn $init(state: *mut SmallState);
            pub fn $overwrite(
                state: *mut SmallState,
                data: *const u8,
                offset: c_uint,
                length: c_uint,
            );
            pub fn $permute(state: *mut SmallState, nrounds: c_uint);
            pub fn $extract(
                state: *const SmallState,
                data: *mut u8,
                offset: c_uint,
                length: c_uint,
            );
            pub fn $sponge(
                rate: c_uint,
                capacity: c_uint,
                input: *const u8,
                input_byte_len: usize,
                suffix: c_uchar,
                output: *mut u8,
                output_byte_len: usize,
            ) -> c_int;
        };
    }

    extern "C" {
        small_width!(
            KeccakP200_Initialize,
            KeccakP200_OverwriteBytes,
            KeccakP200_Permute_Nrounds,
            KeccakP200_ExtractBytes,
            KeccakWidth200_Sponge
        );
        small_width!(
            KeccakP400_Initialize,
            KeccakP400_OverwriteBytes,
            KeccakP400_Permute_Nrounds,
            KeccakP400_ExtractBytes,
            KeccakWidth400_Sponge
        );
        small_width!(
            KeccakP800_Initialize,
            KeccakP800_OverwriteBytes,
            KeccakP800_Permute_Nrounds,
            KeccakP800_ExtractBytes,
            KeccakWidth800_Sponge
        );

        pub fn KeccakP1600_Initialize(state: *mut KeccakP1600State);
        pub fn KeccakP1600_OverwriteBytes(
            state: *mut KeccakP1600State,
            data: *const u8,
            offset: c_uint,
            length: c_uint,
        );
        pub fn KeccakP1600_Permute_Nrounds(state: *mut KeccakP1600State, nrounds: c_uint);
        pub fn KeccakP1600_ExtractBytes(
            state: *const KeccakP1600State,
            data: *mut u8,
            offset: c_uint,
            length: c_uint,
        );

        pub fn KeccakWidth1600_Sponge(
            rate: c_uint,
            capacity: c_uint,
            input: *const u8,
            input_byte_len: usize,
            suffix: c_uchar,
            output: *mut u8,
            output_byte_len: usize,
        ) -> c_int;
        pub fn KeccakWidth1600_SpongeInitialize(
            instance: *mut KeccakWidth1600SpongeInstance,
            rate: c_uint,
            capacity: c_uint,
        ) -> c_int;
        pub fn KeccakWidth1600_SpongeAbsorb(
            instance: *mut KeccakWidth1600SpongeInstance,
            data: *const u8,
            data_byte_len: usize,
        ) -> c_int;
        pub fn KeccakWidth1600_SpongeAbsorbLastFewBits(
            instance: *mut KeccakWidth1600SpongeInstance,
            delimited_data: c_uchar,
        ) -> c_int;
        pub fn KeccakWidth1600_SpongeSqueeze(
            instance: *mut KeccakWidth1600SpongeInstance,
            data: *mut u8,
            data_byte_len: usize,
        ) -> c_int;

        pub fn Keccak_HashInitialize(
            instance: *mut KeccakHashInstance,
            rate: c_uint,
            capacity: c_uint,
            hashbitlen: c_uint,
            delimited_suffix: c_uchar,
        ) -> c_int;
        pub fn Keccak_HashUpdate(
            instance: *mut KeccakHashInstance,
            data: *const u8,
            databitlen: usize,
        ) -> c_int;
        pub fn Keccak_HashFinal(instance: *mut KeccakHashInstance, hashval: *mut u8) -> c_int;
        pub fn Keccak_HashSqueeze(
            instance: *mut KeccakHashInstance,
            data: *mut u8,
            databitlen: usize,
        ) -> c_int;

        pub fn SHAKE128(
            output: *mut u8,
            output_byte_len: usize,
            input: *const u8,
            input_byte_len: usize,
        ) -> c_int;
        pub fn SHAKE256(
            output: *mut u8,
            output_byte_len: usize,
            input: *const u8,
            input_byte_len: usize,
        ) -> c_int;
        pub fn SHA3_224(output: *mut u8, input: *const u8, input_byte_len: usize) -> c_int;
        pub fn SHA3_256(output: *mut u8, input: *const u8, input_byte_len: usize) -> c_int;
        pub fn SHA3_384(output: *mut u8, input: *const u8, input_byte_len: usize) -> c_int;
        pub fn SHA3_512(output: *mut u8, input: *const u8, input_byte_len: usize) -> c_int;
    }
}

/// The widths `b` XKCP has a permutation for.
pub const WIDTHS: [usize; 4] = [200, 400, 800, 1600];

/// `12 + 2l`, the number of rounds of `KECCAK-f[b]`, and the most
/// `KeccakP<b>_Permute_Nrounds` takes.
pub fn max_rounds(b: usize) -> usize {
    match b {
        200 => 18,
        400 => 20,
        800 => 22,
        1600 => 24,
        _ => panic!("XKCP has no KECCAK-p[{b}]"),
    }
}

/// `KECCAK-p[b, n_r]` on a state of `b / 8` bytes, in the byte order of
/// FIPS 202, App. B.1: `KeccakP<b>_Initialize`, `_OverwriteBytes`,
/// `_Permute_Nrounds` and `_ExtractBytes`.
pub fn keccak_p(b: usize, state: &[u8], n_r: usize) -> Vec<u8> {
    assert!(
        state.len() == b / 8,
        "a KECCAK-p[{b}] state is {} bytes",
        b / 8
    );
    assert!(
        1 <= n_r && n_r <= max_rounds(b),
        "XKCP takes 1 to {} rounds of KECCAK-p[{b}]",
        max_rounds(b)
    );
    let len = state.len() as c_uint;
    let n_r = n_r as c_uint;
    let mut out = vec![0u8; state.len()];
    macro_rules! small {
        ($init:ident, $overwrite:ident, $permute:ident, $extract:ident) => {{
            let mut st = ffi::SmallState([0; 100]);
            unsafe {
                ffi::$init(&mut st);
                ffi::$overwrite(&mut st, state.as_ptr(), 0, len);
                ffi::$permute(&mut st, n_r);
                ffi::$extract(&st, out.as_mut_ptr(), 0, len);
            }
        }};
    }
    match b {
        200 => small!(
            KeccakP200_Initialize,
            KeccakP200_OverwriteBytes,
            KeccakP200_Permute_Nrounds,
            KeccakP200_ExtractBytes
        ),
        400 => small!(
            KeccakP400_Initialize,
            KeccakP400_OverwriteBytes,
            KeccakP400_Permute_Nrounds,
            KeccakP400_ExtractBytes
        ),
        800 => small!(
            KeccakP800_Initialize,
            KeccakP800_OverwriteBytes,
            KeccakP800_Permute_Nrounds,
            KeccakP800_ExtractBytes
        ),
        1600 => {
            let mut st = ffi::KeccakP1600State { a: [0; 200] };
            unsafe {
                ffi::KeccakP1600_Initialize(&mut st);
                ffi::KeccakP1600_OverwriteBytes(&mut st, state.as_ptr(), 0, len);
                ffi::KeccakP1600_Permute_Nrounds(&mut st, n_r);
                ffi::KeccakP1600_ExtractBytes(&st, out.as_mut_ptr(), 0, len);
            }
        }
        _ => unreachable!("checked by `max_rounds`"),
    }
    out
}

/// `KeccakWidth<b>_Sponge`: the sponge on `KECCAK-f[b]` with rate `rate` (in
/// bits, a multiple of 8) and `pad10*1`, on the bytes `input` followed by the
/// bits of `suffix`, squeezed for `out_bytes` bytes.
///
/// `suffix` is XKCP's "delimited" byte: the suffix bits from the least
/// significant up, then a single `1` that marks where they end. `0x01` is the
/// empty suffix, `0x06` is SHA-3's `01`, `0x1F` is SHAKE's `1111`.
pub fn sponge(b: usize, rate: usize, input: &[u8], suffix: u8, out_bytes: usize) -> Vec<u8> {
    let f = match b {
        200 => ffi::KeccakWidth200_Sponge,
        400 => ffi::KeccakWidth400_Sponge,
        800 => ffi::KeccakWidth800_Sponge,
        1600 => ffi::KeccakWidth1600_Sponge,
        _ => panic!("XKCP has no sponge on KECCAK-f[{b}]"),
    };
    let mut out = vec![0u8; out_bytes];
    let ret = unsafe {
        f(
            rate as c_uint,
            (b - rate) as c_uint,
            input.as_ptr(),
            input.len(),
            suffix,
            out.as_mut_ptr(),
            out.len(),
        )
    };
    assert!(
        ret == 0,
        "KeccakWidth{b}_Sponge refused rate {rate}, suffix {suffix:#04x}"
    );
    out
}

/// The incremental `KeccakWidth1600_Sponge*` API of `KeccakSponge.h`.
pub struct Sponge1600(ffi::KeccakWidth1600SpongeInstance);

impl Sponge1600 {
    /// `KeccakWidth1600_SpongeInitialize`, at rate `rate` bits, a multiple of 8.
    pub fn new(rate: usize) -> Self {
        let mut st = ffi::KeccakWidth1600SpongeInstance {
            state: ffi::KeccakP1600State { a: [0; 200] },
            rate: 0,
            byte_io_index: 0,
            squeezing: 0,
        };
        let ret = unsafe {
            ffi::KeccakWidth1600_SpongeInitialize(&mut st, rate as c_uint, (1600 - rate) as c_uint)
        };
        assert!(
            ret == 0,
            "KeccakWidth1600_SpongeInitialize refused rate {rate}"
        );
        Self(st)
    }

    /// `KeccakWidth1600_SpongeAbsorb`: any number of calls, each any number of
    /// whole bytes.
    pub fn absorb(&mut self, data: &[u8]) {
        let ret =
            unsafe { ffi::KeccakWidth1600_SpongeAbsorb(&mut self.0, data.as_ptr(), data.len()) };
        assert!(ret == 0, "KeccakWidth1600_SpongeAbsorb failed");
    }

    /// `KeccakWidth1600_SpongeAbsorbLastFewBits`: the delimited suffix of
    /// [`sponge`], then the padding; ends the absorbing phase.
    pub fn absorb_last_few_bits(&mut self, suffix: u8) {
        let ret = unsafe { ffi::KeccakWidth1600_SpongeAbsorbLastFewBits(&mut self.0, suffix) };
        assert!(ret == 0, "KeccakWidth1600_SpongeAbsorbLastFewBits failed");
    }

    /// `KeccakWidth1600_SpongeSqueeze`: any number of calls, each any number of
    /// whole bytes. The first call pads with the empty suffix if
    /// [`Self::absorb_last_few_bits`] has not been called.
    pub fn squeeze(&mut self, out: &mut [u8]) {
        let ret =
            unsafe { ffi::KeccakWidth1600_SpongeSqueeze(&mut self.0, out.as_mut_ptr(), out.len()) };
        assert!(ret == 0, "KeccakWidth1600_SpongeSqueeze failed");
    }
}

/// The `Keccak_Hash*` API of `KeccakHash.h`.
pub struct Hash(ffi::KeccakHashInstance);

impl Hash {
    /// `Keccak_HashInitialize`: `KECCAK[c]` at `r + c = 1600`, `r` a multiple
    /// of 8, for a fixed output of `hashbitlen` bits, or for squeezing if it
    /// is 0. `suffix` is delimited as for [`sponge`].
    pub fn new(rate: usize, capacity: usize, hashbitlen: usize, suffix: u8) -> Self {
        let mut st = ffi::KeccakHashInstance {
            sponge: ffi::KeccakWidth1600SpongeInstance {
                state: ffi::KeccakP1600State { a: [0; 200] },
                rate: 0,
                byte_io_index: 0,
                squeezing: 0,
            },
            fixed_output_length: 0,
            delimited_suffix: 0,
        };
        let ret = unsafe {
            ffi::Keccak_HashInitialize(
                &mut st,
                rate as c_uint,
                capacity as c_uint,
                hashbitlen as c_uint,
                suffix,
            )
        };
        assert!(
            ret == 0,
            "Keccak_HashInitialize refused r = {rate}, c = {capacity}"
        );
        Self(st)
    }

    /// `Keccak_HashInitialize_SHA3_224`.
    pub fn sha3_224() -> Self {
        Self::new(1152, 448, 224, 0x06)
    }
    /// `Keccak_HashInitialize_SHA3_256`.
    pub fn sha3_256() -> Self {
        Self::new(1088, 512, 256, 0x06)
    }
    /// `Keccak_HashInitialize_SHA3_384`.
    pub fn sha3_384() -> Self {
        Self::new(832, 768, 384, 0x06)
    }
    /// `Keccak_HashInitialize_SHA3_512`.
    pub fn sha3_512() -> Self {
        Self::new(576, 1024, 512, 0x06)
    }
    /// `Keccak_HashInitialize_SHAKE128`.
    pub fn shake128() -> Self {
        Self::new(1344, 256, 0, 0x1F)
    }
    /// `Keccak_HashInitialize_SHAKE256`.
    pub fn shake256() -> Self {
        Self::new(1088, 512, 0, 0x1F)
    }

    /// `Keccak_HashUpdate` with the first `bits` bits of `data`, the last of
    /// them in the least significant bits of the last byte -- the order of
    /// FIPS 202, App. B.1. Only the last call may take a `bits` that is not a
    /// multiple of 8.
    pub fn update(&mut self, data: &[u8], bits: usize) {
        assert!(
            bits <= 8 * data.len(),
            "{bits} bits of {} bytes",
            data.len()
        );
        let ret = unsafe { ffi::Keccak_HashUpdate(&mut self.0, data.as_ptr(), bits) };
        assert!(ret == 0, "Keccak_HashUpdate failed");
    }

    /// `Keccak_HashFinal`: pads, and writes the fixed output of
    /// `hashbitlen / 8` bytes to `out`, which must be that long.
    pub fn finalize(&mut self, out: &mut [u8]) {
        assert!(
            out.len() == self.0.fixed_output_length as usize / 8,
            "Keccak_HashFinal writes {} bytes",
            self.0.fixed_output_length / 8
        );
        let ret = unsafe { ffi::Keccak_HashFinal(&mut self.0, out.as_mut_ptr()) };
        assert!(ret == 0, "Keccak_HashFinal failed");
    }

    /// `Keccak_HashSqueeze`, after [`Self::finalize`]: any number of calls,
    /// each any number of whole bytes.
    pub fn squeeze(&mut self, out: &mut [u8]) {
        let ret = unsafe { ffi::Keccak_HashSqueeze(&mut self.0, out.as_mut_ptr(), 8 * out.len()) };
        assert!(ret == 0, "Keccak_HashSqueeze failed");
    }
}

macro_rules! simple_hash {
    ($(#[$meta:meta])* $name:ident, $c:ident, $bytes:expr) => {
        $(#[$meta])*
        pub fn $name(m: &[u8]) -> [u8; $bytes] {
            let mut h = [0u8; $bytes];
            let ret = unsafe { ffi::$c(h.as_mut_ptr(), m.as_ptr(), m.len()) };
            assert!(ret == 0, concat!(stringify!($c), " failed"));
            h
        }
    };
}

macro_rules! simple_xof {
    ($(#[$meta:meta])* $name:ident, $c:ident) => {
        $(#[$meta])*
        pub fn $name(m: &[u8], out_bytes: usize) -> Vec<u8> {
            let mut out = vec![0u8; out_bytes];
            let ret = unsafe { ffi::$c(out.as_mut_ptr(), out.len(), m.as_ptr(), m.len()) };
            assert!(ret == 0, concat!(stringify!($c), " failed"));
            out
        }
    };
}

simple_hash!(
    /// `SHA3_224` from `SimpleFIPS202.c`.
    sha3_224, SHA3_224, 28);
simple_hash!(
    /// `SHA3_256` from `SimpleFIPS202.c`.
    sha3_256, SHA3_256, 32);
simple_hash!(
    /// `SHA3_384` from `SimpleFIPS202.c`.
    sha3_384, SHA3_384, 48);
simple_hash!(
    /// `SHA3_512` from `SimpleFIPS202.c`.
    sha3_512, SHA3_512, 64);
simple_xof!(
    /// `SHAKE128` from `SimpleFIPS202.c`, with the output length in bytes.
    shake128, SHAKE128);
simple_xof!(
    /// `SHAKE256` from `SimpleFIPS202.c`, with the output length in bytes.
    shake256, SHAKE256);
