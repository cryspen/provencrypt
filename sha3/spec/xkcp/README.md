# `pedantic-sha3` against XKCP

Tests of the FIPS 202 transcript in [`sha3/spec`](../README.md) against the
reference code of the eXtended Keccak Code Package,
<https://github.com/XKCP/XKCP>, the Keccak team's own implementation.

```
cargo test -p sha3-xkcp-tests --release
```

`c/` holds files of XKCP verbatim, at their paths in that repository, from two
commits, together with XKCP's `LICENSE` (CC0, except `brg_endian.h`, which
is under Brian Gladman's BSD-style terms given there):

* `c/4affab4`, from commit `4affab454735d54e78156880b3b44e38dcbf765c`: the
  64-bit reference implementation of `KECCAK-p[1600, n_r]`
  (`lib/low/KeccakP-1600/ref-64bits`), the sponge on top of it
  (`lib/high/Keccak/KeccakSponge.*`), and the FIPS 202 interfaces
  `KeccakHash` and `SimpleFIPS202` (`lib/high/Keccak/FIPS202`).
* `c/fa7033a`, from commit `fa7033a212c831249b7e17e785ee1a4e24fc04c4`: the
  reference implementations of `KECCAK-p[200]`, `[400]` and `[800]`
  (`lib/low/KeccakP-{200,400,800}/ref`) and the sponge of that time, which
  covers them. The commit after this one removed these widths from XKCP.

`config/` holds a `config.h` for each: XKCP's build system generates that file
to list the permutations it compiled in, and these list the ones above.
`build.rs` compiles both sets with the `cc` crate, and `src/lib.rs` binds
them. This is a crate of its own, rather than tests inside `sha3/spec`, so
that the specification itself does not need a C compiler.

`tests/xkcp.rs` compares:

* `KECCAK-p[b, n_r]` for `b` = 200, 400, 800 and 1600 and every `n_r` from 1
  to `12 + 2l`, on the all-zero state and on random ones;
* `SPONGE[KECCAK-f[b], pad10*1, r]` at each of those widths and every rate
  `r` that is a whole number of bytes, with input lengths on either side of a
  block boundary; at `b = 1600` this is `KECCAK[c]` for every such `c`;
* the same sponge with each of the 255 suffixes of zero to seven bits that
  XKCP can append to a message, including the case where the suffix fills the
  block and the padding spills into a new one;
* XKCP's incremental sponge, with the input and the output each split in two
  at every block boundary;
* `SHA3-224`, `SHA3-256`, `SHA3-384`, `SHA3-512`, `SHAKE128` and `SHAKE256`
  one-shot at input lengths `0`, `1` and `k·rate - 1`, `k·rate`,
  `k·rate + 1` for `k = 1, 2`, and for the XOFs at the same output lengths;
* the same six functions through `KeccakHash`, on messages of every bit
  length within 16 bits of `0`, `rate` and `2·rate` -- messages that are not
  a whole number of bytes, given to the Standard's functions as bit strings;
* the XOFs at every output length in bits within 16 bits of the same
  boundaries, by truncating XKCP's whole-byte output;
* `KECCAK[c]` with no suffix, Keccak as it was before FIPS 202, at the
  capacities of its four fixed-length instances;
* random messages, bit lengths, splits, widths, rates, suffixes and round
  counts, via `proptest`.
