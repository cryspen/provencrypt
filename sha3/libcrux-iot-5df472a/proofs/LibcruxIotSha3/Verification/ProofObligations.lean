/-
  # Discharging the generated contracts

  For each Rust function with a `#[hax_lib::requires]` or `#[hax_lib::ensures]`,
  hax generates in `Extraction/Specs.lean`

    * `<fn>.pre  : … → RustM Bool`, the `requires` clause,
    * `<fn>.post : … → RustM Bool`, the `ensures` clause, and
    * `<fn>.spec : Prop := (<fn>.pre args).holds → ⦃⌜True⌝⦄ <fn> args ⦃⇓ res => ⌜post⌝⦄`.

  It also writes `Extraction/ProofObligations.lean`, stating each `<fn>.spec` with
  `sorry`. The build leaves that file out (the lakefile builds only the root
  module's import tree), and this file proves all thirteen instead: the public
  SHA-3 and SHAKE functions, whose `#[ensures]` compare the output with
  `pedantic_sha3::bytes::*`.

  Each proof produces the generated post rather than weakening it. The sponge
  results in `Sponge/Shake.lean` and `Sponge/Wrappers.lean` say the function
  computes the lane model's `keccakLanes`; the `pedantic_*` lemmas below restate
  `Fips/`'s agreement theorems, which say `keccakLanes` is the specification; and
  the rest is the plumbing from slices and arrays to the generated `==`.

  The preconditions are read off the generated `.pre`, not restated by hand: the
  digest length of the `*_ema` functions and `LEN == digest_size(algorithm)` for
  `hash`. That checks the hypotheses the sponge theorems take against the
  annotations themselves.
-/
import LibcruxIotSha3.Extraction
import LibcruxIotSha3.Sponge.Shake
import LibcruxIotSha3.Sponge.Wrappers
import LibcruxIotSha3.Support.SliceEq
import LibcruxIotSha3.Fips.LaneSqueeze

open CoreModels Aeneas Aeneas.Std Std.Do
open LibcruxIotSha3.LaneModel
open LibcruxIotSha3.SpongeModel

namespace libcrux_iot_sha3.Verification

open libcrux_iot_sha3.Support (triple_exists_ok)
open Hax (triple_of_ok)

/-! ## Small bridges between the generated shapes and the Lean theorems -/

/-- Decoding a generated precondition. `<fn>.pre` is a `RustM Bool` while
    `RustM.holds` wants a `RustM Prop`, so the generated `.spec` inserts a
    `(· = true) <$> ·`; on an `ok` that collapses to the plain boolean fact. -/
private theorem bool_of_holds_map_ok {b : Bool}
    (h : RustM.holds ((fun a => a = true) <$> (RustM.ok b : RustM Bool))) :
    b = true := by
  have hmap : ((fun a => a = true) <$> (RustM.ok b : RustM Bool))
      = RustM.ok (b = true) := rfl
  rw [hmap] at h
  simpa [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] using h

/-- Converse of `bool_of_holds_map_ok`: build a generated `post`'s `.holds` from
    the plain boolean fact. -/
private theorem holds_map_ok_of_bool {b : Bool} (h : b = true) :
    RustM.holds ((fun a => a = true) <$> (RustM.ok b : RustM Bool)) := by
  have hmap : ((fun a => a = true) <$> (RustM.ok b : RustM Bool))
      = RustM.ok (b = true) := rfl
  rw [hmap]
  simpa [RustM.holds, Std.Do.Triple, WP.wp, PredTrans.apply] using h

/-! ## Shared machinery for the functional-correctness posts

    All six generated posts end the same way: declassify, call the transcript, take
    `[..]` of its array output, and compare slices. These five lemmas are that
    shape, factored out. -/

/-- `declassify_ref` on a shared slice is the identity (Assumptions/FunsExternal). -/
private theorem decl_ref_eq (s : Slice Std.U8) :
    libcrux_secrets.SharedASlice.Insts.Libcrux_secretsTraitsDeclassifyRefSharedASlice.declassify_ref
      libcrux_secrets.U8.Insts.Libcrux_secretsTraitsScalar s = .ok s := rfl

/-- `arr[..]` is `arr` viewed as a slice. -/
private theorem range_full_index_eq {N : Std.Usize} (arr : Std.Array Std.U8 N) :
    (CoreModels.core.Array.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.Slice.Insts.CoreOpsIndexIndex
        (CoreModels.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U8))
      arr ()) = .ok (Aeneas.Std.Array.to_slice arr) := by
  simp [CoreModels.core.Array.Insts.CoreOpsIndexIndex.index,
    CoreModels.core.array.Array.as_slice,
    CoreModels.rust_primitives.slice.array_as_slice,
    CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index,
    CoreModels.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get]

/-- Elementwise agreement over a common length gives list equality. The theorems
    state their posts elementwise because the digest is a `Slice` while the
    transcript's output is an `Array`, so the two are not the same Lean type. -/
private theorem val_eq_of_bytes {N : Nat} {v : Slice Std.U8} {M : Std.Usize}
    {spec_out : Std.Array Std.U8 M}
    (hv_len : v.val.length = N) (hso : spec_out.val.length = N)
    (hbytes : ∀ k : Nat, k < N → v.val[k]! = spec_out.val[k]!) :
    v.val = (Aeneas.Std.Array.to_slice spec_out).val := by
  rw [Aeneas.Std.Array.val_to_slice]
  apply List.ext_getElem (by rw [hv_len, hso])
  intro k h1 _h2
  have h1' : k < N := by rw [hv_len] at h1; exact h1
  have hk := hbytes k h1'
  rwa [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem (show k < spec_out.val.length by rw [hso]; exact h1')] at hk

/-- The `shake` variant: both sides are arrays of the same length `M`, so the
    length side conditions come from the types. -/
private theorem to_slice_val_eq_of_bytes {M : Std.Usize}
    {v spec_out : Std.Array Std.U8 M}
    (hbytes : ∀ k : Nat, k < M.val → v.val[k]! = spec_out.val[k]!) :
    (Aeneas.Std.Array.to_slice v).val = (Aeneas.Std.Array.to_slice spec_out).val := by
  rw [Aeneas.Std.Array.val_to_slice, Aeneas.Std.Array.val_to_slice]
  have hv : v.val.length = M.val := by simp
  have hs : spec_out.val.length = M.val := by simp
  apply List.ext_getElem (by rw [hv, hs])
  intro k h1 _h2
  have h1' : k < M.val := by rw [hv] at h1; exact h1
  have hk := hbytes k h1'
  rwa [List.getElem!_eq_getElem?_getD, List.getElem!_eq_getElem?_getD,
    List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem (show k < spec_out.val.length by rw [hs]; exact h1')] at hk

/-- The slice comparison that ends every one of these posts returns `true`.
    `Support.slice_eq_spec` is the closed form for
    `core::cmp::PartialEq for [T]`, which CoreModels implements as a loop. -/
private theorem slice_eq_true {a b : Slice Std.U8} (h : a.val = b.val) :
    CoreModels.core.Slice.Insts.CoreCmpPartialEqSlice.eq
      CoreModels.core.U8.Insts.CoreCmpPartialEqU8 a b = .ok true := by
  obtain ⟨r, hr_eq, hr_iff⟩ := triple_exists_ok
    (Support.slice_eq_spec CoreModels.core.U8.Insts.CoreCmpPartialEqU8
      Support.lawful_partialEq_u8 a b)
  rw [hr_eq, hr_iff.mpr h]

/-- `CoreModels`' `Slice::len` as an equation. The `_ema` posts call it to get the
    output length the transcript's SHAKE takes as an argument. -/
private theorem slice_len_eq (s : Slice Std.U8) :
    CoreModels.core.slice.Slice.len s = .ok (Aeneas.Std.Slice.len s) := by
  unfold CoreModels.core.slice.Slice.len; rfl

/-- `declassify` of an array of scalars is the identity (Assumptions/FunsExternal). -/
private theorem decl_array_eq {T : Type} {N : Std.Usize} {inst : libcrux_secrets.traits.Scalar T}
    (x : Std.Array T N) :
    libcrux_secrets.Array.Insts.Libcrux_secretsTraitsDeclassifyArray.declassify inst x = .ok x :=
  rfl

/-! ## Transporting the lane-model results onto the FIPS-202 transcript

    The `#[ensures]` clauses name `pedantic-sha3`, the FIPS 202 transcript;
    the Lean theorems in `Sponge/` are stated against the lane model's
    `keccakLanes`.  `Fips/` proves the two agree, and these six
    lemmas are that agreement in the shape the posts want. -/

private theorem pedantic_sha3_224 {payload : Slice Std.U8} :
    pedantic_sha3.bytes.sha3_224 payload
      = .ok (keccakLanes 28#usize (144#usize : Std.Usize).val 6#u8 payload.val) :=
  LibcruxIotSha3.Fips.sha3_224_lanes_agree payload

private theorem pedantic_sha3_256 {payload : Slice Std.U8} :
    pedantic_sha3.bytes.sha3_256 payload
      = .ok (keccakLanes 32#usize (136#usize : Std.Usize).val 6#u8 payload.val) :=
  LibcruxIotSha3.Fips.sha3_256_lanes_agree payload

private theorem pedantic_sha3_384 {payload : Slice Std.U8} :
    pedantic_sha3.bytes.sha3_384 payload
      = .ok (keccakLanes 48#usize (104#usize : Std.Usize).val 6#u8 payload.val) :=
  LibcruxIotSha3.Fips.sha3_384_lanes_agree payload

private theorem pedantic_sha3_512 {payload : Slice Std.U8} :
    pedantic_sha3.bytes.sha3_512 payload
      = .ok (keccakLanes 64#usize (72#usize : Std.Usize).val 6#u8 payload.val) :=
  LibcruxIotSha3.Fips.sha3_512_lanes_agree payload

private theorem pedantic_shake128 {BYTES : Std.Usize} {data : Slice Std.U8} :
    ∃ v : CoreModels.alloc.vec.Vec Std.U8,
      pedantic_sha3.bytes.shake128 data BYTES = .ok v ∧
        v.val = (keccakLanes BYTES (168#usize : Std.Usize).val 31#u8 data.val).val :=
  LibcruxIotSha3.Fips.shake128_lanes_agree BYTES data

private theorem pedantic_shake256 {BYTES : Std.Usize} {data : Slice Std.U8} :
    ∃ v : CoreModels.alloc.vec.Vec Std.U8,
      pedantic_sha3.bytes.shake256 data BYTES = .ok v ∧
        v.val = (keccakLanes BYTES (136#usize : Std.Usize).val 31#u8 data.val).val :=
  LibcruxIotSha3.Fips.shake256_lanes_agree BYTES data

/-- `vec[..]` is the vector viewed as a slice (the SHAKE posts end on a `Vec`,
    since the FIPS-202 transcript's SHAKE returns one). -/
private theorem vec_range_full_index_eq (v : CoreModels.alloc.vec.Vec Std.U8) :
    (CoreModels.alloc.vec.Vec.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice
        Std.U8) v ()) = .ok ⟨v.val, v.property⟩ := by
  simp [CoreModels.alloc.vec.Vec.Insts.CoreOpsIndexIndex.index,
    CoreModels.alloc.vec.Vec.Insts.CoreOpsDerefDerefSlice.deref,
    CoreModels.alloc.vec.Vec.as_slice, CoreModels.rust_primitives.sequence.seq_to_slice,
    CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index,
    CoreModels.core.ops.range.RangeFull.Insts.CoreSliceIndexSliceIndexSliceSlice.get]

/-! ## SHAKE128 / SHAKE256

    Discharged OUTRIGHT with the full functional-correctness post; there is no
    `pre`.

    The contract compares `out.declassify()[..]` to the transcript's
    `shake128(data, BYTES)[..]`, so the post ends in CoreModels' slice `==`,
    closed by `slice_eq_true` once the two lists are shown equal from the
    per-byte agreement. `post` is applied as `post data v`, `BYTES` inferred
    from `v`'s type. -/

theorem shake128_spec_proof (BYTES : Std.Usize) (data : Slice Std.U8) :
    libcrux_iot_sha3.shake128.spec BYTES data := by
  obtain ⟨v, hv_eq, hv_bytes⟩ :=
    triple_exists_ok (Sponge.shake128_spec BYTES data)
  obtain ⟨pv, hpv, hpvv⟩ :=
    pedantic_shake128 (BYTES := BYTES) (data := data)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.shake128.post data v = .ok true := by
    simp only [libcrux_iot_sha3.shake128.post]
    rw [decl_array_eq v, Aeneas.Std.bind_tc_ok, range_full_index_eq v,
      Aeneas.Std.bind_tc_ok, decl_ref_eq data, Aeneas.Std.bind_tc_ok,
      hpv, Aeneas.Std.bind_tc_ok, vec_range_full_index_eq pv, Aeneas.Std.bind_tc_ok]
    refine slice_eq_true ?_
    show (Aeneas.Std.Array.to_slice v).val = pv.val
    rw [hpvv, Aeneas.Std.Array.val_to_slice]
    have h := to_slice_val_eq_of_bytes hv_bytes
    rwa [Aeneas.Std.Array.val_to_slice, Aeneas.Std.Array.val_to_slice] at h
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem shake256_spec_proof (BYTES : Std.Usize) (data : Slice Std.U8) :
    libcrux_iot_sha3.shake256.spec BYTES data := by
  obtain ⟨v, hv_eq, hv_bytes⟩ :=
    triple_exists_ok (Sponge.shake256_spec BYTES data)
  obtain ⟨pv, hpv, hpvv⟩ :=
    pedantic_shake256 (BYTES := BYTES) (data := data)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.shake256.post data v = .ok true := by
    simp only [libcrux_iot_sha3.shake256.post]
    rw [decl_array_eq v, Aeneas.Std.bind_tc_ok, range_full_index_eq v,
      Aeneas.Std.bind_tc_ok, decl_ref_eq data, Aeneas.Std.bind_tc_ok,
      hpv, Aeneas.Std.bind_tc_ok, vec_range_full_index_eq pv, Aeneas.Std.bind_tc_ok]
    refine slice_eq_true ?_
    show (Aeneas.Std.Array.to_slice v).val = pv.val
    rw [hpvv, Aeneas.Std.Array.val_to_slice]
    have h := to_slice_val_eq_of_bytes hv_bytes
    rwa [Aeneas.Std.Array.val_to_slice, Aeneas.Std.Array.val_to_slice] at h
  rw [hpost]
  exact holds_map_ok_of_bool rfl

/-! ## SHA3-224/256/384/512 (EMA)

    Discharged OUTRIGHT with the full functional-correctness post. The generated
    `pre` is `digest.len() == SIZE`, and the correctness theorems want exactly
    that fact as a hypothesis.

    Each `#[ensures]` names the corresponding transcript function directly, so the generated
    `post` says the digest IS the FIPS-202 digest of the payload rather than
    merely that it has the right length. -/

theorem sha224_ema_spec_proof (digest payload : Slice Std.U8) :
    libcrux_iot_sha3.sha224_ema.spec digest payload := by
  intro hpre
  simp only [libcrux_iot_sha3.sha224_ema.pre,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    Aeneas.Std.bind_tc_ok] at hpre
  have hd : digest.len = libcrux_iot_sha3.SHA3_224_DIGEST_SIZE :=
    of_decide_eq_true (bool_of_holds_map_ok hpre)
  have hlen : digest.val.length = 28 := by
    have hv := congrArg Aeneas.Std.UScalar.val hd
    rw [Aeneas.Std.Slice.len_val] at hv
    simpa [libcrux_iot_sha3.SHA3_224_DIGEST_SIZE] using hv
  -- all four conjuncts of the theorem's post are used below
  obtain ⟨v, hv_eq, hv_len, hv_bytes⟩ :=
    triple_exists_ok
      (Sponge.sha224_ema_spec digest payload hlen)
  have hped := pedantic_sha3_224 (payload := payload)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.sha224_ema.post digest payload v = .ok true := by
    simp only [libcrux_iot_sha3.sha224_ema.post]
    rw [decl_ref_eq v, Aeneas.Std.bind_tc_ok,
      decl_ref_eq payload, Aeneas.Std.bind_tc_ok, hped, Aeneas.Std.bind_tc_ok,
      range_full_index_eq
        (keccakLanes 28#usize (144#usize : Std.Usize).val 6#u8 payload.val),
      Aeneas.Std.bind_tc_ok]
    exact slice_eq_true (val_eq_of_bytes hv_len (by simp) hv_bytes)
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem sha256_ema_spec_proof (digest payload : Slice Std.U8) :
    libcrux_iot_sha3.sha256_ema.spec digest payload := by
  intro hpre
  simp only [libcrux_iot_sha3.sha256_ema.pre,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    Aeneas.Std.bind_tc_ok] at hpre
  have hd : digest.len = libcrux_iot_sha3.SHA3_256_DIGEST_SIZE :=
    of_decide_eq_true (bool_of_holds_map_ok hpre)
  have hlen : digest.val.length = 32 := by
    have hv := congrArg Aeneas.Std.UScalar.val hd
    rw [Aeneas.Std.Slice.len_val] at hv
    simpa [libcrux_iot_sha3.SHA3_256_DIGEST_SIZE] using hv
  -- all four conjuncts of the theorem's post are used below
  obtain ⟨v, hv_eq, hv_len, hv_bytes⟩ :=
    triple_exists_ok
      (Sponge.sha256_ema_spec digest payload hlen)
  have hped := pedantic_sha3_256 (payload := payload)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.sha256_ema.post digest payload v = .ok true := by
    simp only [libcrux_iot_sha3.sha256_ema.post]
    rw [decl_ref_eq v, Aeneas.Std.bind_tc_ok,
      decl_ref_eq payload, Aeneas.Std.bind_tc_ok, hped, Aeneas.Std.bind_tc_ok,
      range_full_index_eq
        (keccakLanes 32#usize (136#usize : Std.Usize).val 6#u8 payload.val),
      Aeneas.Std.bind_tc_ok]
    exact slice_eq_true (val_eq_of_bytes hv_len (by simp) hv_bytes)
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem sha384_ema_spec_proof (digest payload : Slice Std.U8) :
    libcrux_iot_sha3.sha384_ema.spec digest payload := by
  intro hpre
  simp only [libcrux_iot_sha3.sha384_ema.pre,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    Aeneas.Std.bind_tc_ok] at hpre
  have hd : digest.len = libcrux_iot_sha3.SHA3_384_DIGEST_SIZE :=
    of_decide_eq_true (bool_of_holds_map_ok hpre)
  have hlen : digest.val.length = 48 := by
    have hv := congrArg Aeneas.Std.UScalar.val hd
    rw [Aeneas.Std.Slice.len_val] at hv
    simpa [libcrux_iot_sha3.SHA3_384_DIGEST_SIZE] using hv
  -- all four conjuncts of the theorem's post are used below
  obtain ⟨v, hv_eq, hv_len, hv_bytes⟩ :=
    triple_exists_ok
      (Sponge.sha384_ema_spec digest payload hlen)
  have hped := pedantic_sha3_384 (payload := payload)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.sha384_ema.post digest payload v = .ok true := by
    simp only [libcrux_iot_sha3.sha384_ema.post]
    rw [decl_ref_eq v, Aeneas.Std.bind_tc_ok,
      decl_ref_eq payload, Aeneas.Std.bind_tc_ok, hped, Aeneas.Std.bind_tc_ok,
      range_full_index_eq
        (keccakLanes 48#usize (104#usize : Std.Usize).val 6#u8 payload.val),
      Aeneas.Std.bind_tc_ok]
    exact slice_eq_true (val_eq_of_bytes hv_len (by simp) hv_bytes)
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem sha512_ema_spec_proof (digest payload : Slice Std.U8) :
    libcrux_iot_sha3.sha512_ema.spec digest payload := by
  intro hpre
  simp only [libcrux_iot_sha3.sha512_ema.pre,
    CoreModels.core.slice.Slice.len, CoreModels.rust_primitives.slice.slice_length,
    Aeneas.Std.bind_tc_ok] at hpre
  have hd : digest.len = libcrux_iot_sha3.SHA3_512_DIGEST_SIZE :=
    of_decide_eq_true (bool_of_holds_map_ok hpre)
  have hlen : digest.val.length = 64 := by
    have hv := congrArg Aeneas.Std.UScalar.val hd
    rw [Aeneas.Std.Slice.len_val] at hv
    simpa [libcrux_iot_sha3.SHA3_512_DIGEST_SIZE] using hv
  -- all four conjuncts of the theorem's post are used below
  obtain ⟨v, hv_eq, hv_len, hv_bytes⟩ :=
    triple_exists_ok
      (Sponge.sha512_ema_spec digest payload hlen)
  have hped := pedantic_sha3_512 (payload := payload)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.sha512_ema.post digest payload v = .ok true := by
    simp only [libcrux_iot_sha3.sha512_ema.post]
    rw [decl_ref_eq v, Aeneas.Std.bind_tc_ok,
      decl_ref_eq payload, Aeneas.Std.bind_tc_ok, hped, Aeneas.Std.bind_tc_ok,
      range_full_index_eq
        (keccakLanes 64#usize (72#usize : Std.Usize).val 6#u8 payload.val),
      Aeneas.Std.bind_tc_ok]
    exact slice_eq_true (val_eq_of_bytes hv_len (by simp) hv_bytes)
  rw [hpost]
  exact holds_map_ok_of_bool rfl

/-! ## The wrapper entry points

    `hash`, the four allocating `shaN` and the two `_ema` XOF wrappers. Each is
    discharged by producing the `ok` from the matching lemma in
    `Sponge/Wrappers.lean`, whose `keccakLanes` value is then transported onto
    the transcript. -/

theorem shake128_ema_spec_proof (out data : Slice Std.U8) :
    libcrux_iot_sha3.shake128_ema.spec out data := by
  have hlen_out : (Aeneas.Std.Slice.len out).val = out.val.length :=
    Aeneas.Std.Slice.len_val out
  obtain ⟨v, hv_eq, hv_len, hv_bytes⟩ :=
    triple_exists_ok (Sponge.shake128_ema_spec out data)
  obtain ⟨pv, hpv, hpvv⟩ :=
    pedantic_shake128 (BYTES := Aeneas.Std.Slice.len out) (data := data)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.shake128_ema.post out data v = .ok true := by
    simp only [libcrux_iot_sha3.shake128_ema.post]
    rw [decl_ref_eq v, Aeneas.Std.bind_tc_ok, decl_ref_eq data, Aeneas.Std.bind_tc_ok,
      slice_len_eq out, Aeneas.Std.bind_tc_ok, hpv, Aeneas.Std.bind_tc_ok,
      vec_range_full_index_eq pv, Aeneas.Std.bind_tc_ok]
    refine slice_eq_true ?_
    show v.val = pv.val
    rw [hpvv]
    have h := val_eq_of_bytes (N := out.val.length) hv_len (by simp) hv_bytes
    rwa [Aeneas.Std.Array.val_to_slice] at h
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem shake256_ema_spec_proof (out data : Slice Std.U8) :
    libcrux_iot_sha3.shake256_ema.spec out data := by
  have hlen_out : (Aeneas.Std.Slice.len out).val = out.val.length :=
    Aeneas.Std.Slice.len_val out
  obtain ⟨v, hv_eq, hv_len, hv_bytes⟩ :=
    triple_exists_ok (Sponge.shake256_ema_spec out data)
  obtain ⟨pv, hpv, hpvv⟩ :=
    pedantic_shake256 (BYTES := Aeneas.Std.Slice.len out) (data := data)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.shake256_ema.post out data v = .ok true := by
    simp only [libcrux_iot_sha3.shake256_ema.post]
    rw [decl_ref_eq v, Aeneas.Std.bind_tc_ok, decl_ref_eq data, Aeneas.Std.bind_tc_ok,
      slice_len_eq out, Aeneas.Std.bind_tc_ok, hpv, Aeneas.Std.bind_tc_ok,
      vec_range_full_index_eq pv, Aeneas.Std.bind_tc_ok]
    refine slice_eq_true ?_
    show v.val = pv.val
    rw [hpvv]
    have h := val_eq_of_bytes (N := out.val.length) hv_len (by simp) hv_bytes
    rwa [Aeneas.Std.Array.val_to_slice] at h
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem sha224_spec_proof (payload : Slice Std.U8) :
    libcrux_iot_sha3.sha224.spec payload := by
  obtain ⟨v, hv_eq, hv_bytes⟩ := triple_exists_ok (Sponge.sha224_spec payload)
  have hped := pedantic_sha3_224 (payload := payload)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.sha224.post payload v = .ok true := by
    simp only [libcrux_iot_sha3.sha224.post]
    rw [decl_array_eq v, Aeneas.Std.bind_tc_ok, range_full_index_eq v,
      Aeneas.Std.bind_tc_ok, decl_ref_eq payload, Aeneas.Std.bind_tc_ok,
      hped, Aeneas.Std.bind_tc_ok,
      range_full_index_eq
        (keccakLanes 28#usize ((144#usize : Std.Usize)).val 6#u8 payload.val),
      Aeneas.Std.bind_tc_ok]
    exact slice_eq_true (to_slice_val_eq_of_bytes (fun k hk => hv_bytes k (by simpa using hk)))
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem sha256_spec_proof (payload : Slice Std.U8) :
    libcrux_iot_sha3.sha256.spec payload := by
  obtain ⟨v, hv_eq, hv_bytes⟩ := triple_exists_ok (Sponge.sha256_spec payload)
  have hped := pedantic_sha3_256 (payload := payload)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.sha256.post payload v = .ok true := by
    simp only [libcrux_iot_sha3.sha256.post]
    rw [decl_array_eq v, Aeneas.Std.bind_tc_ok, range_full_index_eq v,
      Aeneas.Std.bind_tc_ok, decl_ref_eq payload, Aeneas.Std.bind_tc_ok,
      hped, Aeneas.Std.bind_tc_ok,
      range_full_index_eq
        (keccakLanes 32#usize ((136#usize : Std.Usize)).val 6#u8 payload.val),
      Aeneas.Std.bind_tc_ok]
    exact slice_eq_true (to_slice_val_eq_of_bytes (fun k hk => hv_bytes k (by simpa using hk)))
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem sha384_spec_proof (payload : Slice Std.U8) :
    libcrux_iot_sha3.sha384.spec payload := by
  obtain ⟨v, hv_eq, hv_bytes⟩ := triple_exists_ok (Sponge.sha384_spec payload)
  have hped := pedantic_sha3_384 (payload := payload)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.sha384.post payload v = .ok true := by
    simp only [libcrux_iot_sha3.sha384.post]
    rw [decl_array_eq v, Aeneas.Std.bind_tc_ok, range_full_index_eq v,
      Aeneas.Std.bind_tc_ok, decl_ref_eq payload, Aeneas.Std.bind_tc_ok,
      hped, Aeneas.Std.bind_tc_ok,
      range_full_index_eq
        (keccakLanes 48#usize ((104#usize : Std.Usize)).val 6#u8 payload.val),
      Aeneas.Std.bind_tc_ok]
    exact slice_eq_true (to_slice_val_eq_of_bytes (fun k hk => hv_bytes k (by simpa using hk)))
  rw [hpost]
  exact holds_map_ok_of_bool rfl

theorem sha512_spec_proof (payload : Slice Std.U8) :
    libcrux_iot_sha3.sha512.spec payload := by
  obtain ⟨v, hv_eq, hv_bytes⟩ := triple_exists_ok (Sponge.sha512_spec payload)
  have hped := pedantic_sha3_512 (payload := payload)
  refine triple_of_ok hv_eq ?_
  have hpost : libcrux_iot_sha3.sha512.post payload v = .ok true := by
    simp only [libcrux_iot_sha3.sha512.post]
    rw [decl_array_eq v, Aeneas.Std.bind_tc_ok, range_full_index_eq v,
      Aeneas.Std.bind_tc_ok, decl_ref_eq payload, Aeneas.Std.bind_tc_ok,
      hped, Aeneas.Std.bind_tc_ok,
      range_full_index_eq
        (keccakLanes 64#usize ((72#usize : Std.Usize)).val 6#u8 payload.val),
      Aeneas.Std.bind_tc_ok]
    exact slice_eq_true (to_slice_val_eq_of_bytes (fun k hk => hv_bytes k (by simpa using hk)))
  rw [hpost]
  exact holds_map_ok_of_bool rfl

/-- The dispatcher. The precondition ties `LEN` to `digest_size algorithm`, so each
    branch runs the `shaN` whose digest size is `LEN`, and the generated post -- a
    four-way `digest_matches` against the transcript -- is produced branch by branch. -/
theorem hash_spec_proof (LEN : Std.Usize) (algorithm : libcrux_iot_sha3.Algorithm)
    (payload : Slice Std.U8) :
    libcrux_iot_sha3.hash.spec LEN algorithm payload := by
  intro hpre
  simp only [libcrux_iot_sha3.hash.pre] at hpre
  cases algorithm with
  | Sha224 =>
    simp only [libcrux_iot_sha3.digest_size, Aeneas.Std.bind_tc_ok] at hpre
    have hL : LEN = 28#usize := by
      have hd : LEN = libcrux_iot_sha3.SHA3_224_DIGEST_SIZE :=
        of_decide_eq_true (bool_of_holds_map_ok hpre)
      rw [hd]; unfold libcrux_iot_sha3.SHA3_224_DIGEST_SIZE; rfl
    subst hL
    obtain ⟨v, hv_eq, hv_bytes⟩ := triple_exists_ok (Sponge.sha224_spec payload)
    have hped := pedantic_sha3_224 (payload := payload)
    have hhash : libcrux_iot_sha3.hash 28#usize .Sha224 payload = .ok v := by
      rw [Sponge.hash_eq_sha224 payload]; exact hv_eq
    refine triple_of_ok hhash ?_
    have hpost : libcrux_iot_sha3.hash.post .Sha224 payload v = .ok true := by
      simp only [libcrux_iot_sha3.hash.post]
      rw [decl_ref_eq payload, Aeneas.Std.bind_tc_ok, decl_array_eq v,
        Aeneas.Std.bind_tc_ok, range_full_index_eq v, Aeneas.Std.bind_tc_ok]
      simp only [libcrux_iot_sha3.digest_matches]
      rw [hped, Aeneas.Std.bind_tc_ok,
        range_full_index_eq
          (keccakLanes 28#usize ((144#usize : Std.Usize)).val 6#u8 payload.val),
        Aeneas.Std.bind_tc_ok]
      exact slice_eq_true (to_slice_val_eq_of_bytes (fun k hk => hv_bytes k (by simpa using hk)))
    rw [hpost]
    exact holds_map_ok_of_bool rfl
  | Sha256 =>
    simp only [libcrux_iot_sha3.digest_size, Aeneas.Std.bind_tc_ok] at hpre
    have hL : LEN = 32#usize := by
      have hd : LEN = libcrux_iot_sha3.SHA3_256_DIGEST_SIZE :=
        of_decide_eq_true (bool_of_holds_map_ok hpre)
      rw [hd]; unfold libcrux_iot_sha3.SHA3_256_DIGEST_SIZE; rfl
    subst hL
    obtain ⟨v, hv_eq, hv_bytes⟩ := triple_exists_ok (Sponge.sha256_spec payload)
    have hped := pedantic_sha3_256 (payload := payload)
    have hhash : libcrux_iot_sha3.hash 32#usize .Sha256 payload = .ok v := by
      rw [Sponge.hash_eq_sha256 payload]; exact hv_eq
    refine triple_of_ok hhash ?_
    have hpost : libcrux_iot_sha3.hash.post .Sha256 payload v = .ok true := by
      simp only [libcrux_iot_sha3.hash.post]
      rw [decl_ref_eq payload, Aeneas.Std.bind_tc_ok, decl_array_eq v,
        Aeneas.Std.bind_tc_ok, range_full_index_eq v, Aeneas.Std.bind_tc_ok]
      simp only [libcrux_iot_sha3.digest_matches]
      rw [hped, Aeneas.Std.bind_tc_ok,
        range_full_index_eq
          (keccakLanes 32#usize ((136#usize : Std.Usize)).val 6#u8 payload.val),
        Aeneas.Std.bind_tc_ok]
      exact slice_eq_true (to_slice_val_eq_of_bytes (fun k hk => hv_bytes k (by simpa using hk)))
    rw [hpost]
    exact holds_map_ok_of_bool rfl
  | Sha384 =>
    simp only [libcrux_iot_sha3.digest_size, Aeneas.Std.bind_tc_ok] at hpre
    have hL : LEN = 48#usize := by
      have hd : LEN = libcrux_iot_sha3.SHA3_384_DIGEST_SIZE :=
        of_decide_eq_true (bool_of_holds_map_ok hpre)
      rw [hd]; unfold libcrux_iot_sha3.SHA3_384_DIGEST_SIZE; rfl
    subst hL
    obtain ⟨v, hv_eq, hv_bytes⟩ := triple_exists_ok (Sponge.sha384_spec payload)
    have hped := pedantic_sha3_384 (payload := payload)
    have hhash : libcrux_iot_sha3.hash 48#usize .Sha384 payload = .ok v := by
      rw [Sponge.hash_eq_sha384 payload]; exact hv_eq
    refine triple_of_ok hhash ?_
    have hpost : libcrux_iot_sha3.hash.post .Sha384 payload v = .ok true := by
      simp only [libcrux_iot_sha3.hash.post]
      rw [decl_ref_eq payload, Aeneas.Std.bind_tc_ok, decl_array_eq v,
        Aeneas.Std.bind_tc_ok, range_full_index_eq v, Aeneas.Std.bind_tc_ok]
      simp only [libcrux_iot_sha3.digest_matches]
      rw [hped, Aeneas.Std.bind_tc_ok,
        range_full_index_eq
          (keccakLanes 48#usize ((104#usize : Std.Usize)).val 6#u8 payload.val),
        Aeneas.Std.bind_tc_ok]
      exact slice_eq_true (to_slice_val_eq_of_bytes (fun k hk => hv_bytes k (by simpa using hk)))
    rw [hpost]
    exact holds_map_ok_of_bool rfl
  | Sha512 =>
    simp only [libcrux_iot_sha3.digest_size, Aeneas.Std.bind_tc_ok] at hpre
    have hL : LEN = 64#usize := by
      have hd : LEN = libcrux_iot_sha3.SHA3_512_DIGEST_SIZE :=
        of_decide_eq_true (bool_of_holds_map_ok hpre)
      rw [hd]; unfold libcrux_iot_sha3.SHA3_512_DIGEST_SIZE; rfl
    subst hL
    obtain ⟨v, hv_eq, hv_bytes⟩ := triple_exists_ok (Sponge.sha512_spec payload)
    have hped := pedantic_sha3_512 (payload := payload)
    have hhash : libcrux_iot_sha3.hash 64#usize .Sha512 payload = .ok v := by
      rw [Sponge.hash_eq_sha512 payload]; exact hv_eq
    refine triple_of_ok hhash ?_
    have hpost : libcrux_iot_sha3.hash.post .Sha512 payload v = .ok true := by
      simp only [libcrux_iot_sha3.hash.post]
      rw [decl_ref_eq payload, Aeneas.Std.bind_tc_ok, decl_array_eq v,
        Aeneas.Std.bind_tc_ok, range_full_index_eq v, Aeneas.Std.bind_tc_ok]
      simp only [libcrux_iot_sha3.digest_matches]
      rw [hped, Aeneas.Std.bind_tc_ok,
        range_full_index_eq
          (keccakLanes 64#usize ((72#usize : Std.Usize)).val 6#u8 payload.val),
        Aeneas.Std.bind_tc_ok]
      exact slice_eq_true (to_slice_val_eq_of_bytes (fun k hk => hv_bytes k (by simpa using hk)))
    rw [hpost]
    exact holds_map_ok_of_bool rfl

/-! ## Axiom guards
    Pinned by `#guard_msgs`: the build fails if a result comes to depend on any axiom
    beyond Lean's standard three (an admitted `sorry`, or `Lean.ofReduceBool` from
    `bv_decide`/`native_decide`). -/
/--
info: 'libcrux_iot_sha3.Verification.shake128_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shake128_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.shake256_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shake256_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.sha224_ema_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha224_ema_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.sha256_ema_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha256_ema_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.sha384_ema_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha384_ema_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.sha512_ema_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha512_ema_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.shake128_ema_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shake128_ema_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.shake256_ema_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms shake256_ema_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.sha224_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha224_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.sha256_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha256_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.sha384_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha384_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.sha512_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sha512_spec_proof

/--
info: 'libcrux_iot_sha3.Verification.hash_spec_proof' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms hash_spec_proof

end libcrux_iot_sha3.Verification
