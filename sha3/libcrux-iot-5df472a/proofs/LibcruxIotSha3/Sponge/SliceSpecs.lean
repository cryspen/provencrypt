/-
  # Aeneas Std byte/slice `@[spec]` Triples

  Small `@[spec]` Triples used by the byte ↔ lane bridges in
  `Sponge/Bytes.lean`.

  ## Installed

  - `core_models_slice_Slice_len_spec` — `CoreModels.core.slice.Slice.len`
    returns the underlying list length.
  - `massert_spec` — `Aeneas.Std.massert b` succeeds (with `()`) when `b`.
  - `core_models_num_U32_from_le_bytes_spec`,
    `core_models_num_U32_to_le_bytes_spec` — byte ↔ u32 LE.
  - `core_models_num_U64_from_le_bytes_spec`,
    `core_models_num_U64_to_le_bytes_spec` — byte ↔ u64 LE.
  - `core_models_Slice_Insts_index_RangeUsize_spec` — slice subindexing
    over `Range<usize>` (used by load/store loops).
  - `core_models_Slice_Insts_index_mut_RangeUsize_spec` — mutable slice
    subindexing over `Range<usize>` (used by `store_block_2u32_loop.body`).
  - `core_models_result_Result_unwrap_spec` — `result.Result.unwrap` on
    `.Ok v` yields `v`.
  - `core_models_slice_Slice_copy_from_slice_spec` — write-into-slice;
    for `U8` slices of equal length the result is the source slice.
  - `core_models_array_try_from_slice_spec`
    (`Slice T → RustM (result.Result (Array T N) ...)`).
    The body invokes `CoreModels.rust_primitives.slice.array_from_fn` on the
    `try_from.closure`, whose Triple is established by induction over the
    closure's `call_mut` calls.
    See the closure-step lemma, the `array_from_fn_go` invariant, and the final
    Triple at the bottom of this file. General Aeneas Std bridge with no
    SHA-3 specificity (belongs in `rust-core-models` upstream).
-/
import LibcruxIotSha3.Sponge.Opaque

open Aeneas Aeneas.Std RustM Std.Do libcrux_iot_sha3
open LibcruxIotSha3.LaneModel
open LibcruxIotSha3.SpongeModel

-- `mvcgen` drives the two `to_le_bytes` proofs below; the tree already relies
-- on it elsewhere, and its experimental-feature warning is noise here.
set_option mvcgen.warning false

namespace libcrux_iot_sha3.Sponge

attribute [local irreducible] keccak.keccakf1600 keccakFLanes

/-! ## Prerequisite — Aeneas Std byte/slice `@[spec]` lemmas. -/

/-! ### `≤`-specs for sub-slicing.

Rust's `&xs[i..i]` is a valid empty slice. `Slice.subslice`,
`Slice.update_subslice` and `Array.update_subslice` guard on `start ≤ end`, so
the `≤` behaviour is a consequence of the definitions. The statements are in
existential-equation form, so no `Slice` length-invariant proof term is needed
at the use sites. -/

theorem Slice.subslice_le_eq {α : Type} (s : Aeneas.Std.Slice α)
    (r : Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ∃ ns : Aeneas.Std.Slice α, Aeneas.Std.Slice.subslice s r = .ok ns ∧
      ns.val = s.val.slice r.start.val r.end.val := by
  unfold Aeneas.Std.Slice.subslice
  rw [if_pos (show r.start.val ≤ r.end.val ∧ r.end.val ≤ s.length from ⟨h0, h1⟩)]
  exact ⟨_, rfl, rfl⟩

theorem Slice.update_subslice_le_eq {α : Type} (s : Aeneas.Std.Slice α)
    (r : Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize) (ss : Aeneas.Std.Slice α)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length)
    (h2 : ss.val.length = r.end.val - r.start.val) :
    ∃ ns : Aeneas.Std.Slice α, Aeneas.Std.Slice.update_subslice s r ss = .ok ns ∧
      ns.val = s.val.setSlice! r.start.val ss.val := by
  unfold Aeneas.Std.Slice.update_subslice
  rw [dif_pos (show r.start.val ≤ r.end.val ∧ r.end.val ≤ s.length ∧
        ss.val.length = r.end.val - r.start.val from ⟨h0, h1, h2⟩)]
  exact ⟨_, rfl, rfl⟩

theorem Array.update_subslice_le_eq {α : Type} {n : Aeneas.Std.Usize} (a : Aeneas.Std.Array α n)
    (r : Aeneas.Std.core.ops.range.Range Aeneas.Std.Usize) (ss : Aeneas.Std.Slice α)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ a.val.length)
    (h2 : ss.val.length = r.end.val - r.start.val) :
    ∃ na : Aeneas.Std.Array α n, Aeneas.Std.Array.update_subslice a r ss = .ok na ∧
      na.val = a.val.setSlice! r.start.val ss.val := by
  unfold Aeneas.Std.Array.update_subslice
  rw [dif_pos (show r.start.val ≤ r.end.val ∧ r.end.val ≤ a.length ∧
        ss.val.length = r.end.val - r.start.val from ⟨h0, h1, h2⟩)]
  exact ⟨_, rfl, rfl⟩

/-! ### Bounded array `index_usize` / `update` (existential form).

Aeneas's `Array.index_usize_spec` / `Array.update_spec` are `partialSpec`s
(no bound argument). These give bounded `∃`-results directly. -/

theorem Array.index_usize_exists {α : Type} [Inhabited α] {n : Aeneas.Std.Usize}
    (v : Aeneas.Std.Array α n) (i : Aeneas.Std.Usize) (h : i.val < v.val.length) :
    ∃ x, Aeneas.Std.Array.index_usize v i = .ok x ∧ x = v.val[i.val]'h :=
  ⟨v.val[i.val]'h, by
    simp only [Aeneas.Std.Array.index_usize, Aeneas.Std.Array.getElem?_Usize_eq,
               List.getElem?_eq_getElem h], rfl⟩

theorem Array.update_exists {α : Type} {n : Aeneas.Std.Usize}
    (v : Aeneas.Std.Array α n) (i : Aeneas.Std.Usize) (x : α) (h : i.val < v.val.length) :
    ∃ nv, Aeneas.Std.Array.update v i x = .ok nv ∧ nv = v.set i x := by
  refine ⟨v.set i x, ?_, rfl⟩
  simp only [Aeneas.Std.Array.update, Aeneas.Std.Array.getElem?_Usize_eq,
             List.getElem?_eq_getElem h]
  rfl

/-! ### `CoreModels.core.slice.Slice.len` -/

/-- The hax `CoreModels.core.slice.Slice.len` is a thin `pure`-wrapper around
    `Aeneas.Std.Slice.len`. Always succeeds with the underlying list length
    (as a `Usize`). -/
@[spec]
theorem core_models_slice_Slice_len_spec {T : Type} (s : Slice T) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.slice.Slice.len s
    ⦃ ⇓ r => ⌜ r.val = s.val.length ⌝ ⦄ := by
  -- CoreModels routes this through `rust_primitives.slice.slice_length`,
  -- so unfolding `Slice.len` alone leaves the body untouched.
  unfold CoreModels.core.slice.Slice.len
    CoreModels.rust_primitives.slice.slice_length
  simp [Triple, WP.wp, PredTrans.apply]

/-! ### `Aeneas.Std.massert` -/

/-- `massert b` succeeds with `()` iff `b` holds. -/
@[spec]
theorem massert_spec (b : Prop) [Decidable b] (h : b) :
    ⦃ ⌜ True ⌝ ⦄
    massert b
    ⦃ ⇓ r => ⌜ r = () ⌝ ⦄ := by
  unfold massert
  simp [Triple, WP.wp, PredTrans.apply, h]

/-! ### `CoreModels.core.num.U32.from_le_bytes` / `U32.to_le_bytes` -/

/-- The four-byte LE-load `U32.from_le_bytes` always succeeds with
    `core.num.U32.from_le_bytes` applied to the input array. -/
@[spec]
theorem core_models_num_U32_from_le_bytes_spec (bytes : Std.Array Std.U8 4#usize) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U32.from_le_bytes bytes
    ⦃ ⇓ r => ⌜ r = Std.core.num.U32.from_le_bytes bytes ⌝ ⦄ := by
  unfold CoreModels.core.num.U32.from_le_bytes CoreModels.rust_primitives.arithmetic.from_le_bytes_u32
  simp [Triple, WP.wp, PredTrans.apply]

/-- The four-byte LE-store `U32.to_le_bytes` always succeeds with
    `core.num.U32.to_le_bytes` applied to the input integer. -/
@[spec]
theorem core_models_num_U32_to_le_bytes_spec (x : Std.U32) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U32.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = Std.core.num.U32.to_le_bytes x ⌝ ⦄ := by
  unfold CoreModels.core.num.U32.to_le_bytes CoreModels.rust_primitives.slice.array_from_fn
  simp only [show ((4#usize : Std.Usize).val) = 4 from rfl,
    CoreModels.rust_primitives.slice.array_from_fn_go,
    CoreModels.core.num.U32.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut]
  mvcgen
  · apply Subtype.ext
    simp_all [Std.core.num.U32.to_le_bytes, BitVec.toLEBytes, Std.UScalar.cast,
      show ((0#32#uscalar : Std.U32).val) = 0 from rfl,
      show ((1#32#uscalar : Std.U32).val) = 1 from rfl,
      show ((2#32#uscalar : Std.U32).val) = 2 from rfl,
      show ((3#32#uscalar : Std.U32).val) = 3 from rfl]
    and_intros <;>
      apply BitVec.eq_of_getLsbD_eq_iff.mpr <;>
      intro i hi <;>
      simp +arith [hi] <;> omega
  all_goals
    (exfalso
     simp_all [Std.UScalar.cast,
       show ((0#32#uscalar : Std.U32).val) = 0 from rfl,
       show ((1#32#uscalar : Std.U32).val) = 1 from rfl,
       show ((2#32#uscalar : Std.U32).val) = 2 from rfl,
       show ((3#32#uscalar : Std.U32).val) = 3 from rfl] <;> scalar_tac)

/-! ### `CoreModels.core.num.U64.from_le_bytes` / `U64.to_le_bytes` -/

/-- The eight-byte LE-load `U64.from_le_bytes` always succeeds with
    `core.num.U64.from_le_bytes` applied to the input array. -/
@[spec]
theorem core_models_num_U64_from_le_bytes_spec (bytes : Std.Array Std.U8 8#usize) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U64.from_le_bytes bytes
    ⦃ ⇓ r => ⌜ r = Std.core.num.U64.from_le_bytes bytes ⌝ ⦄ := by
  unfold CoreModels.core.num.U64.from_le_bytes CoreModels.rust_primitives.arithmetic.from_le_bytes_u64
  simp [Triple, WP.wp, PredTrans.apply]

/-- The eight-byte LE-store `U64.to_le_bytes` always succeeds with
    `core.num.U64.to_le_bytes` applied to the input integer. -/
@[spec]
theorem core_models_num_U64_to_le_bytes_spec (x : Std.U64) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.num.U64.to_le_bytes x
    ⦃ ⇓ r => ⌜ r = Std.core.num.U64.to_le_bytes x ⌝ ⦄ := by
  unfold CoreModels.core.num.U64.to_le_bytes CoreModels.rust_primitives.slice.array_from_fn
  simp only [show ((8#usize : Std.Usize).val) = 8 from rfl,
    CoreModels.rust_primitives.slice.array_from_fn_go,
    CoreModels.core.num.U64.to_le_bytes.closure.Insts.CoreOpsFunctionFnMutTupleUsizeU8.call_mut]
  mvcgen
  · apply Subtype.ext
    simp_all [Std.core.num.U64.to_le_bytes, BitVec.toLEBytes, Std.UScalar.cast,
      show ((0#32#uscalar : Std.U32).val) = 0 from rfl,
      show ((1#32#uscalar : Std.U32).val) = 1 from rfl,
      show ((2#32#uscalar : Std.U32).val) = 2 from rfl,
      show ((3#32#uscalar : Std.U32).val) = 3 from rfl,
      show ((4#32#uscalar : Std.U32).val) = 4 from rfl,
      show ((5#32#uscalar : Std.U32).val) = 5 from rfl,
      show ((6#32#uscalar : Std.U32).val) = 6 from rfl,
      show ((7#32#uscalar : Std.U32).val) = 7 from rfl]
    and_intros <;>
      apply BitVec.eq_of_getLsbD_eq_iff.mpr <;>
      intro i hi <;>
      simp +arith [hi] <;> omega
  all_goals
    (exfalso
     simp_all [Std.UScalar.cast,
       show ((0#32#uscalar : Std.U32).val) = 0 from rfl,
       show ((1#32#uscalar : Std.U32).val) = 1 from rfl,
       show ((2#32#uscalar : Std.U32).val) = 2 from rfl,
       show ((3#32#uscalar : Std.U32).val) = 3 from rfl,
       show ((4#32#uscalar : Std.U32).val) = 4 from rfl,
       show ((5#32#uscalar : Std.U32).val) = 5 from rfl,
       show ((6#32#uscalar : Std.U32).val) = 6 from rfl,
       show ((7#32#uscalar : Std.U32).val) = 7 from rfl] <;> scalar_tac)

/-! ### `CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index` over `Range Usize` -/

/-- Slice subindexing over a `Range<usize>` succeeds whenever the range is
    in bounds, returning the sub-`Slice` whose `val` is the contiguous
    slice `s.val[start..end]`. -/
@[spec]
theorem core_models_Slice_Insts_index_RangeUsize_spec
    {T : Type} (s : Slice T) (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ r' => ⌜ r'.val = s.val.slice r.start.val r.end.val ∧
                r'.val.length = r.end.val - r.start.val ⌝ ⦄ := by
  obtain ⟨ns, hns_eq, hns_val⟩ := Slice.subslice_le_eq s ⟨r.start, r.end⟩ h0 h1
  unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndex.index
         CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
         CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get
         CoreModels.rust_primitives.slice.slice_slice
         CoreModels.rust_primitives.slice.slice_length
  simp only [Triple, WP.wp, PredTrans.apply]
  simp [hns_eq, h0, h1, Aeneas.Std.Slice.len,
        hns_val, List.slice_length]
  omega

/-! ### `CoreModels.core.result.Result.unwrap`

The hax `Result.unwrap` on the `core_models` `result.Result` enum panics on
`Err` and returns the inner `T` on `Ok`. We give a Triple-style spec under
the precondition `r = .Ok v`.

NB: the `try_from` Triple (for `Slice T → Array T N`) is proved at the
bottom of this file. -/

/-- `Result.unwrap` of a `.Ok`-valued `r` returns the inner value.

    We state both the precondition (`∃ v, r = .Ok v`) and the post
    (`r = .Ok r'`), leaving `v` quantified inside `mvcgen`'s assertion
    bag. This avoids the mvcgen unification quirk where the explicit
    `v` argument gets eagerly bound to the first matching local of the
    right type. -/
@[spec]
theorem core_models_result_Result_unwrap_spec
    {T E : Type} (dbg : CoreModels.core.fmt.Debug E)
    (r : CoreModels.core.result.Result T E)
    (h : ∃ v, r = .Ok v) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.result.Result.unwrap dbg r
    ⦃ ⇓ r' => ⌜ r = .Ok r' ⌝ ⦄ := by
  obtain ⟨v, hv⟩ := h
  unfold CoreModels.core.result.Result.unwrap
  subst hv
  simp [Triple, WP.wp, PredTrans.apply]

/-! ### `CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut` over `Range Usize`

Used by `state.store_block_2u32_loop.body` to obtain a
mutable sub-slice and a write-back closure. -/

/-- Mutable slice subindexing over a `Range<usize>` returns both the
    sub-slice (same `val` as the non-mut `index`) and a write-back
    closure that overwrites `s.val[r.start.val..]` with the argument's
    `val`. -/
-- The write-back carries an `s'.length = end - start` side condition; the range
-- bound is `≤` via the subslice specs at the top of this file.
@[spec]
theorem core_models_Slice_Insts_index_mut_RangeUsize_spec
    {T : Type} (s : Slice T) (r : CoreModels.core.ops.range.Range Std.Usize)
    (h0 : r.start.val ≤ r.end.val) (h1 : r.end.val ≤ s.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
      (CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice T) s r
    ⦃ ⇓ p => ⌜ p.1.val = s.val.slice r.start.val r.end.val ∧
                p.1.val.length = r.end.val - r.start.val ∧
                ∀ s', s'.val.length = r.end.val - r.start.val →
                      (p.2 s').val = s.val.setSlice! r.start.val s'.val ⌝ ⦄ := by
  obtain ⟨ns, hns_eq, hns_val⟩ := Slice.subslice_le_eq s ⟨r.start, r.end⟩ h0 h1
  -- CoreModels supplies this instance itself: `index_mut` delegates to
  -- the `SliceIndex`'s `get_unchecked_mut`, which for `Range<usize>` is
  -- `rust_primitives.slice.slice_slice_mut`. That model's write-back is directly
  -- `fun ss => ⟨s.val.setSlice! start ss.val, _⟩`, so the third conjunct is `rfl`.
  unfold CoreModels.core.Slice.Insts.CoreOpsIndexIndexMut.index_mut
  simp only [CoreModels.core.ops.range.RangeUsize.Insts.CoreSliceIndexSliceIndexSliceSlice.get_unchecked_mut,
             CoreModels.rust_primitives.slice.slice_slice_mut, hns_eq]
  simp only [Triple, WP.wp, PredTrans.apply, bind_tc_ok,
             Std.Do.SPred.pure, Std.Do.SPred.entails]
  intro _
  refine ⟨hns_val, ?_, ?_⟩
  · simp only [hns_val, List.slice_length]; omega
  · intro s' _
    -- the model's write-back is literally `fun ss => ⟨setSlice! .. ss.val, _⟩`,
    -- so the simp above already closed this.
    trivial

/-! ### `CoreModels.core.slice.Slice.copy_from_slice` -/

/-- `l.mapM cl = .ok l` for an effect-free `cl`. -/
private theorem mapM_id_of_clone_id {T : Type} (cl : T → RustM T)
    (hcl : ∀ x : T, cl x = .ok x) : ∀ l : List T, l.mapM cl = .ok l := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, hcl, ih]; rfl

/-- Plain equation form, shared with the call sites that discharge a
    `copy_from_slice` inside a larger `have` chain. -/
theorem core_models_slice_Slice_copy_from_slice_eq
    {T : Type} (cpy : CoreModels.core.marker.Copy T) (dst src : Slice T)
    (h : dst.val.length = src.val.length)
    (hclone : ∀ x : T, cpy.cloneCloneInst.clone x = .ok x) :
    CoreModels.core.slice.Slice.copy_from_slice cpy dst src = .ok src := by
  unfold CoreModels.core.slice.Slice.copy_from_slice
    CoreModels.rust_primitives.slice.slice_clone_from_slice
  have hmap : src.val.mapM cpy.cloneCloneInst.clone = .ok src.val :=
    mapM_id_of_clone_id _ hclone src.val
  simp only [Std.Slice.length, h, if_pos]
  -- the `clone` chain is a *dependent* match (`match h : .. with`), so its
  -- discriminant cannot simply be rewritten; split and use the equation each
  -- branch carries.
  split
  · rename_i cloned heq
    rw [hmap] at heq
    have hc : cloned = src.val := (RustM.ok.inj heq).symm
    subst hc
    rfl
  · rename_i e heq
    rw [hmap] at heq; exact absurd heq (by simp)
  · rename_i heq
    rw [hmap] at heq; exact absurd heq (by simp)

/-- `copy_from_slice dst src` succeeds with the source slice `src`, for `U8`
    slices of equal length.

    Why this is stated at `U8` and not generically: CoreModels routes
    `copy_from_slice` through `rust_primitives.slice.slice_clone_from_slice`,
    which clones every element -- "Cloned, so `clone`'s effects are observable
    and cannot be skipped". So `r = src` holds only when the element `clone` is
    effect-free. The general statement above
    (`core_models_slice_Slice_copy_from_slice_eq`) keeps that as an explicit
    `hclone` hypothesis; this `@[spec]` form fixes the instance to
    `U8.Insts.CoreMarkerCopy`, whose `clone` is literally `ok self`, and
    discharges it once by `rfl`.

    The specialization is deliberate: as an `@[spec]`, a `clone` hypothesis
    would become a side goal at every `mvcgen` site that steps over a
    `copy_from_slice`, and those sites have no way to close it. `U8` is the only
    element type this crate copies. For another one, use the general `_eq` and
    supply the proof. -/
@[spec]
theorem core_models_slice_Slice_copy_from_slice_spec
    (dst src : Slice Std.U8)
    (h : dst.val.length = src.val.length) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.slice.Slice.copy_from_slice
      CoreModels.core.U8.Insts.CoreMarkerCopy dst src
    ⦃ ⇓ r => ⌜ r = src ⌝ ⦄ := by
  rw [core_models_slice_Slice_copy_from_slice_eq _ dst src h (by intro x; rfl)]
  simp [Triple, WP.wp, PredTrans.apply]

/-! ### `CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from`

The body invokes `CoreModels.rust_primitives.slice.array_from_fn` on the `try_from`
closure (whose state is just the source `Slice T`). The proof has three
parts:

1. Closure step: `call_mut s i = .ok (s.val[i.val]!, s)` for `i.val <
   s.length` — the closure reads the slice and preserves its state.
2. `array_from_fn_go` invariant: induction on `n` shows that running the
   closure on the first `n` indices returns `(s.val.take n, s)` when
   `n ≤ s.length`.
3. Final assembly: `array_from_fn N closure s = .ok (Array.make N s.val)`
   when `s.length = N.val`, hence `try_from N inst s = .ok (.Ok a)` with
   `a.val = s.val`. -/

/-- Numeric helper: `(⟨BitVec.ofNat _ n⟩ : Usize).val = n` when
    `n ≤ Std.Usize.max` (equivalently, `n < 2^Usize.numBits`).
    We state the bit-vector size as `UScalarTy.Usize.numBits` since this
    is the form `Usize.val` unfolds to. -/
private theorem bv_ofNat_usize_val_eq (n : Nat) (hn : n ≤ Std.Usize.max) :
    (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n := by
  show (BitVec.ofNat _ n).toNat = n
  simp only [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  -- `Std.Usize.max = 2^Std.Usize.numBits - 1`, hence `n ≤ max` means `n < 2^numBits`.
  have hmax : Std.Usize.max + 1 = 2 ^ Std.UScalarTy.Usize.numBits := by
    simp [Std.Usize.max, Std.Usize.numBits]
  omega

/-- Closure step lemma. The `try_from` closure's state is the source
    `Slice T`; `call_mut` reads the `i`-th element and preserves state.

    We state this on the unfolded form `...call_mut.call_mut cpy s i`
    because that's what the FnMut instance's `call_mut` field reduces to
    after Lean unfolds the structure projection. -/
private theorem try_from_closure_call_mut_eq
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (i : Std.Usize) (h : i.val < s.val.length) :
    CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
      (T := T) (N := N) cpy s i =
      .ok (s.val[i.val]!, s) := by
  -- Reduces to `do let t ← slice_index s i; ok (t, s)`.
  unfold CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT.call_mut
  unfold CoreModels.rust_primitives.slice.slice_index Std.Slice.index_usize
  -- Now `s[i]?` matches; for `i.val < s.length`, `s[i]? = some s.val[i.val]!`.
  have hsome : s[i]? = some s.val[i.val]! := by
    simp only [Std.Slice.getElem?_Usize_eq]
    rw [List.getElem?_eq_getElem h, List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem h]
    rfl
  rw [hsome]
  rfl

/-- `array_from_fn_go` invariant for the `try_from` closure: running the first
    `n` indices yields `s.val.take n`, with the closure state (the slice itself)
    unchanged.

    CoreModels builds the array by structural recursion on the index count;
    the recursion carries no accumulator. -/
private theorem array_from_fn_go_try_from_invariant
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hmax : s.val.length ≤ Std.Usize.max) :
    ∀ n : Nat, n ≤ s.val.length →
      CoreModels.rust_primitives.slice.array_from_fn_go
        (CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
          (T := T) (N := N) cpy) s n
      = .ok (s.val.take n, s) := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [CoreModels.rust_primitives.slice.array_from_fn_go]
  | succ n ih =>
      intro hn
      have hn_lt : n < s.val.length := by omega
      have hn_max : n ≤ Std.Usize.max := by omega
      have hval : (⟨BitVec.ofNat Std.UScalarTy.Usize.numBits n⟩ : Std.Usize).val = n :=
        bv_ofNat_usize_val_eq n hn_max
      have hcall := try_from_closure_call_mut_eq (T := T) (N := N) cpy s
                      ⟨BitVec.ofNat _ n⟩ (by rw [hval]; exact hn_lt)
      rw [hval] at hcall
      have htake : s.val.take n ++ [s.val[n]!] = s.val.take (n + 1) := by
        rw [List.take_add_one]
        simp [List.getElem?_eq_getElem hn_lt, List.getElem!_eq_getElem?_getD]
      simp only [CoreModels.rust_primitives.slice.array_from_fn_go, ih (by omega),
                 bind_tc_ok, hcall, htake]

/-- `array_from_fn N (try_from closure) s = .ok (Array.make N s.val)`
    when `s.length = N.val`. -/
private theorem array_from_fn_try_from_eq_ok
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    CoreModels.rust_primitives.slice.array_from_fn N
      (CoreModels.core.convert.TryFromArrayShared0SliceTryFromSliceError.try_from.closure.Insts.CoreOpsFunctionFnMutTupleUsizeT
        (T := T) (N := N) cpy) s
    = .ok (Std.Array.make N s.val (by simp [hlen])) := by
  have hN_max : s.val.length ≤ Std.Usize.max := s.property
  have h_go :=
    array_from_fn_go_try_from_invariant (T := T) (N := N) cpy s hN_max N.val (by omega)
  have h_take : s.val.take N.val = s.val := List.take_of_length_le (by omega)
  rw [h_take] at h_go
  unfold CoreModels.rust_primitives.slice.array_from_fn
  rw [h_go]
  simp only [bind_tc_ok]
  rw [dif_pos (by simp [hlen] : (s.val).length = N.val)]
  rfl

/-- The main Triple: `try_from N cpy s` succeeds with `Ok (Array.make N s.val _)`,
    whenever `s.val.length = N.val`. -/
@[spec]
theorem core_models_array_try_from_slice_spec
    {T : Type} [Inhabited T] {N : Std.Usize} (cpy : CoreModels.core.marker.Copy T)
    (s : Slice T) (hlen : s.val.length = N.val) :
    ⦃ ⌜ True ⌝ ⦄
    CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
      N cpy s
    ⦃ ⇓ r => ⌜ r = CoreModels.core.result.Result.Ok
                    (Std.Array.make N s.val (by simp [hlen])) ⌝ ⦄ := by
  -- Unfold try_from and reduce the `do` chain step-by-step.
  unfold CoreModels.core.Array.Insts.CoreConvertTryFromShared0SliceTryFromSliceError.try_from
  -- `CoreModels.rust_primitives.slice.slice_length x` is `ok (Slice.len x)`.
  unfold CoreModels.rust_primitives.slice.slice_length
  -- The if-decision: `Slice.len s = N` reduces to `s.val.length = N.val`.
  have hi_eq : (Std.Slice.len s) = N := by
    apply Std.UScalar.eq_of_val_eq
    simp [hlen]
  -- Reduce the array_from_fn call to .ok.
  have h_afn := array_from_fn_try_from_eq_ok (T := T) (N := N) cpy s hlen
  simp only [Triple, WP.wp,bind_tc_ok, hi_eq, if_true, h_afn]
  intro _
  trivial

/-! ## `!`-valued index override for the sponge layer.

The Aeneas `Array.index_usize_spec` post is the total `getElem`
`v.val[i]`, whereas the sponge proofs are written with `getElem!`. The
sponge accessors (`get_lane`/`set_lane`/the `Lane2U32` `Index` instance) all
unfold to `Array.index_usize`, so a single high-priority `@[spec]` override
of the index post (which `mvcgen` prefers over the auto-generated default)
makes every unfolded read come out as `!` — the `getElem!` form the sponge
proofs use, with no per-site bridging. `@[spec high]`
ensures it wins over the Aeneas default without disabling it (disabling
would just make `mvcgen` unfold `index_usize` to the total form instead). -/
@[spec high]
theorem index_usize_bang_spec {α : Type _} [Inhabited α] {n : Std.Usize}
    (v : Std.Array α n) (i : Std.Usize) (hbound : i.val < v.length) :
    ⦃ ⌜ True ⌝ ⦄ v.index_usize i ⦃ ⇓ x => ⌜ x = v.val[i.val]! ⌝ ⦄ := by
  have h_idx : i.val < v.val.length := hbound
  have hbang : v.val[i.val]! = v.val[i.val]'h_idx := by
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h_idx]; rfl
  have hidx : v.index_usize i = ok (v.val[i.val]'h_idx) := by
    simp only [Std.Array.index_usize, Std.Array.getElem?_Usize_eq,
               List.getElem?_eq_getElem h_idx]
  rw [hidx]
  simp [Triple, WP.wp, PredTrans.apply, hbang]

end libcrux_iot_sha3.Sponge
