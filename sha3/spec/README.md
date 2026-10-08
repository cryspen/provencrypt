# A specification of SHA-3, closely following FIPS 202

> ⚠️
> Do not use this crate in production. It is a specification, written to be read
> next to FIPS 202 and to serve in proofs, not to be fast or to resist side
> channels.

This is a specification of SHA-3 written in Rust,
closely following the [FIPS 202 standard](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.202.pdf). Its structure and implementation details mirror the FIPS 202 standard as precisely as possible, so it can easily
be checked to be equivalent to the standard's pseudocode:

* every function is one numbered Algorithm, with the Steps in the Standard's
  order, under the Standard's names;
* nothing is precomputed that the Standard computes: `ρ`'s offsets come out of
  the `(x, y)` walk in Algorithm 2 and `ι`'s round constants out of the `rc`
  function in Algorithm 5, rather than from tables;
* the permutation is generic in the width — `KECCAK-p[b, n_r]` for any of the
  seven `b` of Table 1, not only `b = 1600`.

This specification is AI-generated. By staying close to the
standard's pseudocode, we are still confident that this specification faithfully
reflects the standard. Since this specification is executable,
we can increase our confidence further by extensive [testing](#testing).


One obstacle with representing the FIPS 202 standard in Rust is that the
standard's bit strings are unbounded and Rust arrays are not.
Rust's arrays have a theoretical maximum length of `usize::MAX` (only actually
reachable using zero-sized types). To resolve this,
we introduce two special Rust types that get custom semantics in Lean
(see `Assumptions/FunsExternal.lean`):
`bits::BitStr` models a list of bits of any length, and `nat::Nat`
models an arbitrary non-negative number. In Rust, these are simply
wrappers for `Vec<u8>` and `u128`, and thus, when executed, our specification
only works for reasonably small inputs. The Lean model, however,
faithfully models the standard.

## Where each section lives

| FIPS 202 | module |
|---|---|
| Sec. 2.3 basic operations; App. B.1 `h2b` / `b2h` (Algorithms 10, 11) | `bits` |
| Sec. 3.1 state, state array, and the two conversions | `state_array` |
| Sec. 3.2 Algorithms 1-6: `θ`, `ρ`, `π`, `χ`, `ι`, and `rc` | `step_mappings` |
| Sec. 3.3 Algorithm 7 `KECCAK-p[b, n_r]`; Sec. 3.4 `KECCAK-f[b]` | `keccak_p` |
| Sec. 4 Algorithm 8 `SPONGE`; Sec. 5.1 Algorithm 9 `pad10*1`; Sec. 5.2 `KECCAK[c]` | `sponge` |
| Sec. 6.1-6.2 the four hash functions and the two XOFs | `sha3` |
| — byte-aligned wrappers, `h2b` in front and `b2h` behind | `bytes` |
| — the nonnegative integers the Standard counts with | `nat` |

## Testing

To run all tests for the specification, use
```
cargo test -p pedantic-sha3 --release
```

We use the following references to test correctness of our specification:

* **FIPS 202 itself.** `fips202.rs` checks the standard's own examples
  and its structural statements.
* **NIST's CAVP vectors.** `cavp.rs` runs the byte-oriented SHA-3 and SHAKE
  short-message, long-message and variable-output files, via `libcrux-kats`.
  `cavp_bits.rs` runs the bit-oriented short-message, long-message,
  variable-output and Monte Carlo files: messages of every bit length up to a
  block or two and long ones not a whole number of bytes, and output lengths
  that are not whole bytes either, given to the Standard's functions as bit
  strings. These files are not in the repository; the first run downloads
  NIST's two archives (about 6 MB) with `curl`, checks their SHA-256, and
  unpacks them with `unzip` into Cargo's temporary directory. Offline, those
  tests print a notice and pass, unless `PEDANTIC_SHA3_REQUIRE_VECTORS` is set.
  Without `--release`, only the first three of each Monte Carlo file's hundred
  checkpoints are checked.
* **Widths other than 1600.** `widths.rs` checks `KECCAK-f[b]` for
  `b` = 200, 400, 800 and 1600 against the Keccak team's XKCP test vectors,
  and `KECCAK-p[b, n_r]` at all seven widths and every round count up to
  `12 + 2l` against a lane-oriented formulation with tabulated round constants
  and `ρ` offsets.
* **Independent implementations**, compared at input and output lengths around
  every block boundary, on random messages and output lengths (`proptest`), and
  through their incremental APIs:
  * the SHA-3 code of the ML-KEM C reference implementation, in the separate
    crate [`mlkem-c-ref`](mlkem-c-ref/README.md);
  * `libcrux-sha3`, in `compare_ref.rs`, including its `Xof` API and the block
    API ML-KEM samples with.

Two more files test the types whose Lean models are hand-written, and so part
of the trusted base: `bitstr.rs` checks `BitStr` against a naive `Vec<bool>`
implementation, and `nat.rs` checks `Nat`
against properties of nonnegative integers.

## Lean extraction

- For extraction:
  - [cargo](https://rust-lang.org/tools/install/)
  - [cargo-run-bin](https://github.com/dustinblackman/cargo-run-bin), which
    provides the `cargo bin` that the `cargo hax` alias runs
  - optionally [cargo-binstall](https://github.com/cargo-bins/cargo-binstall#installation),
    which `cargo bin` uses to download hax instead of building it
  - (hax, charon, and aeneas will be installed automatically)
- For Lean compilation:
  - [Lean](https://lean-lang.org/install/)

To reproduce the extracted Lean code and compile it, use the following commands
from the repository root:
```
cargo hax extract pedantic-sha3
cd sha3/spec/proofs/pedantic-sha3/lean && lake build
```
There are no proofs
about this crate itself; the proofs in
[`sha3/libcrux-iot-5df472a`](../libcrux-iot-5df472a/README.md) use it as their
specification.

## Workarounds for limitations of hax

We fill two gaps in hax's core models, in
`Assumptions/FunsExternal.lean`:

* `RangeInclusive`. CoreModels declares the type, with Rust's `exhausted`
  flag, but ships no `new` and no `Iterator` instance, so `for j in a..=b` does
  not extract without one. The model here follows the Rust standard library's
  `next` -- yield `start` and step it forward while `start < end`, then yield
  `end` once more and set `exhausted` -- in about thirty lines, so it iterates
  every range as Rust does, including one that ends at `A::MAX`. It covers all
  three of the Standard's inclusive loops: "For `j` from 0 to `l`"
  (Algorithm 6), "For `i` from 1 to `t mod 255`" (Algorithm 5), and "For `i_r`
  from `12+2l-n_r` to `12+2l-1`" (Algorithm 7).
* `Copy` for `bool`. CoreModels has `marker.Copy` for every integer and
  `clone.Clone` for `Bool`, but not the instance those two determine, so
  `copy_from_slice` on a `[bool]` does not resolve without it. One line,
  nothing assumed. It is what lets Step 3a of Algorithm 5 (`R = 0 || R`) be a
  slice copy.

In some cases, we need to formulate the Rust specification in a certain way to
make hax extraction work:

* The Standard's ι updates `A′[0,0,z] = A′[0,0,z] ⊕ RC[z]` in place. Here lane
  (0,0) is read out, updated and written back: a compound assignment through
  the nested projection `out.a[0][0][z]` makes aeneas fail with `Unreachable`.
* Assert messages must be ASCII: a `⊕` in one came out as an invalid escape in
  the generated Lean, and being a parse error it then cascaded into twenty
  phantom "unknown constant" reports. `assert_eq!` is also out, since
  formatting the two operands needs a `core::fmt::Arguments::from_str`
  CoreModels does not have; plain `assert!(cond, "…")` extracts to a `massert`
  and is what the stated conditions use.
* `Vec::extend` and `to_vec` have no model -- and unlike `Copy for bool`,
  `Extend` is not declared in CoreModels at all -- so `concat`, `trunc` and
  `zeros` use loops instead.
* The derived `Debug` is `cfg`-gated out; its generated instance does not
  match the core model.
