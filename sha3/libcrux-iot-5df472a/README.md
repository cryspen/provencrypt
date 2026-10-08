# libcrux-iot SHA-3 and SHAKE Verification

> ⚠️
> Do not use this crate in production. It is an example of a realistic
> implementation proved equivalent to a specification, and it is not maintained
> as a library. For production use, take the implementation this one is based
> on, from [libcrux-iot](https://github.com/celabshq/libcrux-iot).

We prove the one-shot API of the SHA-3 crate of [libcrux-iot](https://github.com/celabshq/libcrux-iot) functionally correct in Lean. We prove that it is
equivalent to the [`pedantic-sha3`](../spec/README.md) specification,
which is our Rust transcript of the [FIPS 202 standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf).

We use a snapshot of the libcrux-iot repo, and apply a couple of patches
to adjust the hax annotations to our needs.
The patches are stored in [`annotation-patches/`](annotation-patches/) and the
patched snapshot is committed in [`annotated-upstream/`](annotated-upstream/).
Both this implementation and the specification are extracted into Lean
via [hax](https://hax.cryspen.com/). In Lean, we prove the equivalence
as stated in the hax annotations that our patched source code contains.
The extracted Lean code and the proofs are committed in [`proofs/`](proofs/).
Most of the verification code is AI-generated.

## The annotated upstream crate

To reproduce the patched sources by downloading them from the libcrux-iot repo
and applying the patches, run either of the following commands:
```bash
make          # download the crate and apply the patches
make check    # the same, and fail if the result differs from what is committed
```

There are three patches:

* [`0001-drop-old-annotations.patch`](annotation-patches/0001-drop-old-annotations.patch)
  drops some of upstream's hax annotations: the `charon` tool registration and
  the `hax_lib::lean::before` attributes that hax 0.4 rejects, the
  `#[hax_lib::opaque]` markers and `loop_invariant!`s written for upstream's F*
  proof, the contracts on internal functions and on the incremental API, which
  the proof does not discharge, and the `u32::MAX` bound on the payload and on
  the SHAKE output length in the `#[requires]` clauses of the public functions.
  Upstream's other hax annotations are kept.
* [`0002-contracts.patch`](annotation-patches/0002-contracts.patch) adds the `#[ensures]`
  clauses that state functional correctness against the specification, and the
  dependency on it.
* [`0003-drop-length-debug-asserts.patch`](annotation-patches/0003-drop-length-debug-asserts.patch)
  drops the `debug_assert!`s of the `u32::MAX` bound on the payload, so that the
  public functions accept inputs of every length, as their contracts do.

## Main theorems

The top-level results are the contracts of thirteen SHA-3 and SHAKE functions, tabulated
below. How they are proved is described under
[Proof architecture](#proof-architecture).

### SHA-3 and SHAKE

Functional correctness of the SHA-3 and SHAKE functions in [`annotated-upstream/src/lib.rs`](annotated-upstream/src/lib.rs)
is specified using Rust annotations directly on the functions. For example:

```rust
#[hax_lib::ensures(|out| out.declassify()[..]
    == pedantic_sha3::bytes::shake128(data.declassify_ref(), BYTES)[..])]
pub fn shake128<const BYTES: usize>(data: &[U8]) -> [U8; BYTES]
```
Informally: the implementation's `shake128` yields the same result as
the specification's `pedantic_sha3::bytes::shake128`, for every input and every output length.

We must call `declassify()`
to convert between the implementation's custom integer type `U8` and Rust's integers
`u8`. The `[..]` are needed because hax's model of Rust core has no `PartialEq` implementation for comparing an array with a `Vec`.

All of the SHA-3 and SHAKE functions also come in a variant
for external memory allocation. For those, we need to provide an
output slice to write into. For example:
```rust
#[hax_lib::requires(digest.len() == SHA3_256_DIGEST_SIZE)]
#[hax_lib::ensures(|_| future(digest).declassify_ref()
        == &pedantic_sha3::bytes::sha3_256(payload.declassify_ref())[..])]
pub fn sha256_ema(digest: &mut [U8], payload: &[U8])
```
Informally: the implementation's `sha256_ema` yields the same result as
the specification's `pedantic_sha3::bytes::sha3_256`, for all inputs,
provided that the `digest` slice has the expected length.
If `digest` has the wrong length, our verification makes no claims about
what the function might do.

In the `hax_lib::ensures` annotation, we can refer to the value of `digest` after the function ran as `future(digest)`.

Every function in the table below carries an annotation of one of those two shapes --
comparing a returned array, or the buffer a `&mut` argument was written into. hax
generates a proof obligation for each
in [`Extraction/ProofObligations.lean`](proofs/LibcruxIotSha3/Extraction/ProofObligations.lean), and they are discharged by Lean theorems in
[`Verification/ProofObligations.lean`](proofs/LibcruxIotSha3/Verification/ProofObligations.lean).

| impl function | spec function (`pedantic_sha3::bytes`) | Lean theorem |
|---|---|---|
| `hash` | one of the four below, by `Algorithm` | `hash_spec_proof` |
| `sha224` | `sha3_224` | `sha224_spec_proof` |
| `sha224_ema` | `sha3_224` | `sha224_ema_spec_proof` |
| `sha256` | `sha3_256` | `sha256_spec_proof` |
| `sha256_ema` | `sha3_256` | `sha256_ema_spec_proof` |
| `sha384` | `sha3_384` | `sha384_spec_proof` |
| `sha384_ema` | `sha3_384` | `sha384_ema_spec_proof` |
| `sha512` | `sha3_512` | `sha512_spec_proof` |
| `sha512_ema` | `sha3_512` | `sha512_ema_spec_proof` |
| `shake128` | `shake128` | `shake128_spec_proof` |
| `shake128_ema` | `shake128` | `shake128_ema_spec_proof` |
| `shake256` | `shake256` | `shake256_spec_proof` |
| `shake256_ema` | `shake256` | `shake256_ema_spec_proof` |

### Assumptions

All of the main theorems presented above are proved using only
Lean's three standard axioms `propext`,
`Classical.choice`, and `Quot.sound`.
This set of axioms is checked on every build by `#guard_msgs` guards in
[`Verification/ProofObligations.lean`](proofs/LibcruxIotSha3/Verification/ProofObligations.lean).

Beyond Lean's axioms, the proof trusts the hand-written models in
[`Assumptions/`](proofs/LibcruxIotSha3/Assumptions/), which stand in for what hax leaves external.
`FunsExternal.lean` models the `libcrux_secrets` helpers the extraction does
not define. We do not verify secret-independence, so these are modeled as identities
and no-ops.

Moreover, the correctness of the verification depends on:
* the specification correctly reflecting the FIPS standard;
* hax extracting the specification faithfully;
* the extraction of the specification being pinned correctly in the lakefile;
* hax extracting the implementation faithfully;
* hax's Lean libraries modeling Rust faithfully;
* Lean checking the proofs correctly (we could aim for more confidence here by using [comparator](https://github.com/leanprover/comparator), but this is not set up yet);
* the Rust compiler correctly translating into machine code;
* the environment on which the compilation, extraction, and verification is executed functioning correctly.

### What is left out

We do not verify the incremental API here (neither buffered nor unbuffered), and we do not
verify the `Digest`/`Hasher` implementations. The unbuffered API is not even extracted:
`hax.toml` does not enable the `unbuffered-xof` feature, so nothing under
`#[cfg(feature = "unbuffered-xof")]` reaches Lean. The `Digest`/`Hasher` impls are
`charon::exclude`d.

We only verify functional correctness here: the Lean verification does not contain any claims
about absence of side channel vulnerabilities.

## Proof architecture

The proof meets in the middle, at a *lane model*: the Keccak permutation and sponge
written as ordinary Lean functions on 25 `u64` lanes. One half proves that the
implementation computes the lane model; the other proves that the lane model computes
the specification. Nothing rests on the lane model being right: the contracts are stated
against the specification, and both halves are proved.

```
  implementation (Extraction/)                  pedantic-sha3 (FIPS 202)
          │                                              │
  Permutation/  keccakf1600_equiv_lanes          Fips/   keccakF_lanesToBits
  Sponge/       keccak_keccak_spec                       *_lanes_agree
          │                                              │
          └──────────────►  Model/ (lane model)  ◄───────┘
                                   │
                   Verification/ProofObligations: the 13 contracts
```

### `Model/`: the lane model

[`LaneModel.lean`](proofs/LibcruxIotSha3/Model/LaneModel.lean) defines the five step mappings on lanes and
`keccakFLanes`; [`SpongeModel.lean`](proofs/LibcruxIotSha3/Model/SpongeModel.lean) defines the sponge one
byte-rate block at a time (`absorbBlockLanes`, `padBlockList`, `squeezeLanes`,
`keccakLanes`); [`Tables.lean`](proofs/LibcruxIotSha3/Model/Tables.lean) holds the round constants and the
ρ offsets. They are total functions over `List`s and `Nat`s, with no proofs attached.

### [`Permutation/`](proofs/LibcruxIotSha3/Permutation/): the implementation's permutation is the lane model's

Main theorem: `keccakf1600_equiv_lanes` in [`Keccakf1600.lean`](proofs/LibcruxIotSha3/Permutation/Keccakf1600.lean),

```lean
theorem keccakf1600_equiv_lanes (s : state.KeccakState) (h_i : s.i = 0#usize) :
    ⦃ ⌜ True ⌝ ⦄
    keccak.keccakf1600 s
    ⦃ ⇓ r_impl => ⌜ keccakFLanes (Permutation.lift s) = Permutation.lift r_impl ⌝ ⦄
```

The implementation keeps each lane as two bit-interleaved 32-bit halves, and implements π
by relabelling storage rather than moving data: each round reads its lanes from different
physical positions, and some lanes are stored with their halves swapped.
[`Lift.lean`](proofs/LibcruxIotSha3/Permutation/Lift.lean) reads such a state back as `u64` lanes:
`lift_perm s p sw` through the relabelling `p` and swap pattern `sw` of a given round.
Both have period four (`impl_perm⁴ = id`, `impl_swap_k 4 = impl_swap_k 0`), so after four
rounds the state reads through the plain `lift` again.

- `ThetaLift*` and `PrcLift*` relate the implementation's θ (eleven sub-functions) and its
  π ρ χ ι (two halves of the state) to the lane model, for each of the four rounds of a
  group; [`RoundEquiv.lean`](proofs/LibcruxIotSha3/Permutation/RoundEquiv.lean) combines them into one round
  of the lane model per implementation round. The round proofs work with step functions
  written out cell by cell; `LaneEq.lean` shows they are `LaneModel`'s.
- `Keccakf1600.lean` chains the four rounds of a group and runs the implementation's loop
  over six groups.

### [`Sponge/`](proofs/LibcruxIotSha3/Sponge/): the implementation's sponge is the lane model's

Main theorem: `keccak.keccak_keccak_spec` in [`Keccak.lean`](proofs/LibcruxIotSha3/Sponge/Keccak.lean): the
internal `keccak` function computes `keccakLanes`. The Rust function carries no contract;
this theorem is its correctness statement.

- [`Opaque.lean`](proofs/LibcruxIotSha3/Sponge/Opaque.lean) seals `keccakf1600` and `keccakFLanes`, so the
  sponge proof uses the permutation only through `keccakf1600_equiv_lanes`.
- `Bytes`, `Interleave`, `LoopSpecs` and `XorBlockSpec` relate loading and storing a block
  of bytes to the interleaved lanes; `AbsorbBlock`, `Absorb` and `AbsorbFinal` cover
  absorbing, `SqueezeBlock` and `Squeeze` squeezing.
- `Shake` and `Wrappers` instantiate the theorem at each function's rate and delimiter.

### [`Fips/`](proofs/LibcruxIotSha3/Fips/): the lane model is the specification

Main theorems: the six `*_lanes_agree` in [`LaneSqueeze.lean`](proofs/LibcruxIotSha3/Fips/LaneSqueeze.lean),
each saying that the lane model's function equals `pedantic_sha3::bytes::*`. The
specification works on a state array of bits and absorbs bit strings, so the bridge is
bit-level, in two steps:

1. Characterise each extracted specification function as a pure function: the step
   mappings as functions of the bits (`Theta`, `Rho`, `Pi`, `Chi`, `Iota`; `RoundConstants`
   checks by `decide` that Algorithm 5's LFSR gives the tabulated round constants), the
   rounds and `Keccak-p` (`Round`, `Permutation`, `Bits`, `KeccakP`), the sponge (`BitsOps`,
   `Padding`, `Sponge`, `KeccakC`) and the byte layer (`Bytes`, `Sha3`).
2. Relate the lane model to those: the permutation in `Lanes` (ending in
   `keccakF_lanesToBits`), the sponge in `LaneSponge`, `LaneAbsorb` and `LaneSqueeze`.

Two correspondences make the last step work. The implementation's delimiter byte is the
domain-separation suffix followed by the `1` that opens `pad10*1` (`0x06` is `01` then
`1`, `0x1f` is `1111` then `1`), and the `0x80` it ORs into the last byte of the block is
that padding's trailing `1`. On the output side, `b2h` inverts `h2b`.

`StateMap`, `Grid` and `LoopEq` provide the state-array accessors and the equational loop
lemmas the rest is written with.

### [`Verification/`](proofs/LibcruxIotSha3/Verification/): the contracts

[`ProofObligations.lean`](proofs/LibcruxIotSha3/Verification/ProofObligations.lean) discharges each of the
thirteen generated obligations by composing the sponge result for that function (from
`Sponge/Shake.lean` or `Sponge/Wrappers.lean`) with its `*_lanes_agree` theorem, so the
generated post is produced, not weakened. The main results are pinned by `#guard_msgs` to
Lean's three standard axioms.

[`Support/`](proofs/LibcruxIotSha3/Support/) holds small facts about Hoare triples and the closed form of
slice equality; [`Assumptions/`](proofs/LibcruxIotSha3/Assumptions/) holds the hand-written models described
under [Assumptions](#assumptions).

## Reproduction

### Prerequisites

- For running the proofs:
  - [Lean](https://lean-lang.org/install/)
- For extraction:
  - [cargo](https://rust-lang.org/tools/install/)
  - [cargo-run-bin](https://github.com/dustinblackman/cargo-run-bin), which
    provides the `cargo bin` that the `cargo hax` alias runs
  - optionally [cargo-binstall](https://github.com/cargo-bins/cargo-binstall#installation),
    which `cargo bin` uses to download hax instead of building it
  - (hax, charon, and aeneas will be installed automatically)

### Running the proofs

From [`proofs/`](proofs/):

```bash
lake exe cache get        # downloading the Mathlib cache
lake build                # building the project
```

### Rust tests

[`tests/`](tests/) runs the implementation against `pedantic-sha3`, the
specification the contracts name, as a sanity check next to the proof:

```bash
cargo test -p libcrux-iot-sha3-spec-tests --release
```

It compares all thirteen contracted functions at input lengths around every multiple
of the rate up to two blocks, the XOFs also at output lengths around the same
boundaries, and the incremental `Xof` API, which the proof does not cover, with the
input split at those boundaries; then random contents at random lengths. It is a crate
of its own so that `annotated-upstream/` stays upstream's crate plus the patches.

Upstream's own tests run with `cargo test -p libcrux-iot-sha3`. Besides the
known-answer tests, they compare the implementation with upstream's specification,
`hacspec_sha3` from [libcrux](https://github.com/cryspen/libcrux), in
`annotated-upstream/src/keccak.rs` and
[`annotated-upstream/tests/cross_spec_proptests.rs`](annotated-upstream/tests/cross_spec_proptests.rs).

### Extraction from Rust into Lean

From the repository root, which is where `hax.toml` names both scenarios:

```bash
# Spec side -- the transcript, which is what the contracts name:
cargo hax extract pedantic-sha3

# Impl side:
cargo hax extract libcrux-iot-sha3
```
