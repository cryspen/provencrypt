import LibcruxIotSha3.Fips.Padding
/-!
# The sponge (FIPS 202, Algorithm 8)

`SPONGE[f, pad, r](N, d)` pads `N` to a multiple of the rate, absorbs it block by
block into a `b`-bit state, then squeezes `r` bits at a time until `d` are out.

The two loops are characterised against pure recursions over the permutation
`F`, which stays abstract here: the spec takes `f` and `pad` as closures, and
`keccak_c` instantiates them with `Keccak-p[1600, 24]` and `pad10*1`.  `absorbFrom` and
`squeezeFrom` are written in the order the loops run them, so the loop
invariants need no re-association -- that is worth the fuel argument
`squeezeFrom` carries (the squeeze loop is the one loop in this development
whose exit test lives in its body rather than in a range).
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Fips

/-- One absorb step: XOR the next block (zero-extended to the full width) into
    the state and permute (Algorithm 8, step 6). -/
def absorbStep (F : List Bool → List Bool) (r c : Nat) (p s : List Bool) (i : Nat) : List Bool :=
  F (List.zipWith (· ^^ ·) s ((p.drop (i * r)).take r ++ List.replicate c false))

/-- Absorbing blocks `i0, i0+1, …`, `k` of them. -/
def absorbFrom (F : List Bool → List Bool) (r c : Nat) (p : List Bool) :
    List Bool → Nat → Nat → List Bool
  | s, _, 0 => s
  | s, i0, k + 1 => absorbFrom F r c p (absorbStep F r c p s i0) (i0 + 1) k

/-- Squeezing (Algorithm 8, steps 8-10): emit `r` bits, stop once `d` are out.
    The loop is a `do`-while -- it always emits at least once -- so the fuel `k`
    counts *further* iterations, and `0` means "this is the last one". -/
def squeezeFrom (F : List Bool → List Bool) (r d : Nat) :
    Nat → List Bool → List Bool → List Bool
  | 0, s, z => z ++ s.take r
  | k + 1, s, z =>
    let z' := z ++ s.take r
    if d ≤ z'.length then z' else squeezeFrom F r d k (F s) z'

/-! ### The absorb loop -/

section Absorb

variable {Fty : Type}
  (fInst : core.ops.function.Fn Fty (Slice Bool) (alloc.vec.Vec Bool)) (f : Fty)
  (F : List Bool → List Bool) (b : Nat)

/-- What the closure `f` has to satisfy: it takes `b` bits to `b` bits, and it
    is the pure function `F`. -/
def PermSpec : Prop :=
  ∀ s : Slice Bool, s.val.length = b →
    ∃ o : alloc.vec.Vec Bool, fInst.call f s = ok o ∧ o.val = F s.val ∧ (F s.val).length = b

/-- `Nat::to_usize`, the one place a length goes back down to the fixed-width
    layer. It is partial there, and that is the only partiality this file
    inherits from the machine: every call site hands it the rate, which Table 1
    bounds by 1600. -/
theorem to_usize_eq (x : Nat) (hx : x ≤ Std.Usize.max) :
    ∃ u : Std.Usize, pedantic_sha3.nat.Nat.to_usize x = ok u ∧ u.val = x := by
  have h := Std.UScalar.tryMk_eq .Usize x
  unfold pedantic_sha3.nat.Nat.to_usize
  cases hc : Std.UScalar.tryMk .Usize x with
  | ok u => rw [hc] at h; exact ⟨u, rfl, h.1⟩
  | fail e => rw [hc] at h; exact absurd (show Std.UScalar.inBounds .Usize x by scalar_tac) h
  | div => rw [hc] at h; exact absurd h (by simp)

theorem absorb_body_cont (hF : PermSpec fInst f F b)
    (r : Nat) (c : Std.Usize) (hrc : r + c.val = b) (_hb : b ≤ 1600)
    (p : pedantic_sha3.bits.BitStr) (_hr : 0 < r)
    (blocks : Nat) (hblocks : blocks * r = p.length)
    (i : Nat) (hi : i < blocks)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ s' : alloc.vec.Vec Bool,
      s'.val = absorbStep F r c.val p s.val i ∧
      pedantic_sha3.sponge.sponge_loop0.body fInst f r p blocks c s i
        = ok (.cont (s', i + 1)) := by
  -- `i * r` and `(i+1) * r` are both within the string. That is all there is to
  -- check about them: the cursor is a `Nat`, so neither can overflow.
  have hir : i * r + r ≤ p.length := by
    rw [← hblocks]
    calc i * r + r = (i + 1) * r := by ring
      _ ≤ blocks * r := Nat.mul_le_mul_right _ (by omega)
  -- the block: `r` bits of `p` from `i * r`, zero-extended to the full width
  have hslice : pedantic_sha3.bits.BitStr.slice p (i * r) r
      = ok ((p.drop (i * r)).take r) := by
    unfold pedantic_sha3.bits.BitStr.slice
    rw [if_pos hir]
  have hsl : ((p.drop (i * r)).take r).length = r := by
    simp only [List.length_take, List.length_drop]; omega
  have hto : pedantic_sha3.bits.BitStr.to_bits ((p.drop (i * r)).take r)
      = ok ⟨(p.drop (i * r)).take r, by rw [hsl]; scalar_tac⟩ := by
    unfold pedantic_sha3.bits.BitStr.to_bits
    exact dif_pos (by rw [hsl]; scalar_tac)
  obtain ⟨zs, hzs, hzsv⟩ := zeros_eq c
  obtain ⟨blk, hblk, hblkv⟩ := concat_eq
    ⟨(p.drop (i * r)).take r, by rw [hsl]; scalar_tac⟩ zs (by
      simp only [hsl, hzsv, List.length_replicate]; scalar_tac)
  have hblkv' : blk.val = (p.drop (i * r)).take r ++ zs.val := by simpa using hblkv
  have hblklen : blk.val.length = b := by
    rw [hblkv']
    simp only [List.length_append, hsl, hzsv, List.length_replicate]
    omega
  -- XOR into the state and permute
  obtain ⟨xs, hxs, hxsv⟩ := xor_eq s blk (by simp [hs, hblklen])
  obtain ⟨o, ho, hov, holen⟩ := hF xs (by simp only [hxsv]; simp [hs, hblklen])
  refine ⟨o, ?_, ?_⟩
  · have hxsv' : xs.val = List.zipWith (· ^^ ·) s.val blk.val := by simpa using hxsv
    rw [hov, hxsv', hblkv', hzsv]
    rfl
  · unfold pedantic_sha3.sponge.sponge_loop0.body
      pedantic_sha3.nat.Nat.Insts.CoreCmpPartialOrdNat.lt
      pedantic_sha3.nat.Nat.Insts.CoreOpsArithMulNatNat.mul
      pedantic_sha3.nat.Nat.Insts.CoreOpsArithAddNatNat.add
      pedantic_sha3.nat.Nat.new
    simp [hi, hslice, hto, hzs, vec_deref_eq, hblk, hxs, ho]

theorem absorb_body_done (r : Nat) (c : Std.Usize)
    (p : pedantic_sha3.bits.BitStr)
    (blocks : Nat) (s : alloc.vec.Vec Bool) :
    pedantic_sha3.sponge.sponge_loop0.body fInst f r p blocks c s blocks
      = ok (.done s) := by
  unfold pedantic_sha3.sponge.sponge_loop0.body
    pedantic_sha3.nat.Nat.Insts.CoreCmpPartialOrdNat.lt
  simp

/-- The absorb loop of Algorithm 8, steps 5-6. -/
theorem absorb_loop_eq (hF : PermSpec fInst f F b)
    (r : Nat) (c : Std.Usize) (hrc : r + c.val = b) (hb : b ≤ 1600) (hr : 0 < r)
    (p : pedantic_sha3.bits.BitStr)
    (blocks : Nat) (hblocks : blocks * r = p.length)
    (s : alloc.vec.Vec Bool) (hs : s.val.length = b) :
    ∃ s' : alloc.vec.Vec Bool,
      pedantic_sha3.sponge.sponge_loop0 fInst f r p blocks c s 0
        = ok s' ∧
      s'.val = absorbFrom F r c.val p s.val 0 blocks ∧ s'.val.length = b := by
  have h := loop_counter_eq_inv_nat (β := alloc.vec.Vec Bool) (γ := alloc.vec.Vec Bool)
    (fun q => pedantic_sha3.sponge.sponge_loop0.body fInst f r p blocks c q.1 q.2)
    blocks
    (fun _ acc => acc.val.length = b)
    (fun i acc r' => r'.val = absorbFrom F r c.val p acc.val i (blocks - i)
      ∧ r'.val.length = b)
    ?hstep ?hdone blocks 0 s (by simp) hs
  case hstep =>
    intro i acc hi hinv
    obtain ⟨s', hs', hbody⟩ :=
      absorb_body_cont fInst f F b hF r c hrc hb p hr blocks hblocks i hi acc hinv
    refine ⟨s', ?_, hbody, ?_⟩
    · rw [hs']
      obtain ⟨o, _, hov, holen⟩ := hF ⟨List.zipWith (· ^^ ·) acc.val
          ((p.drop (i * r)).take r ++ List.replicate c.val false), by
        have := acc.property
        simp only [List.length_zipWith]
        scalar_tac⟩ (by
        simp only [List.length_zipWith, List.length_append, List.length_replicate, hinv]
        have hlen : ((p.drop (i * r)).take r).length = r := by
          have hub : i * r + r ≤ p.length := by
            rw [← hblocks]
            calc i * r + r = (i + 1) * r := by ring
              _ ≤ blocks * r := Nat.mul_le_mul_right _ (by omega)
          simp only [List.length_take, List.length_drop]
          omega
        rw [hlen]
        omega)
      simpa only [absorbStep] using holen
    · rintro r' ⟨hr', hrlen⟩
      refine ⟨?_, hrlen⟩
      rw [hr', hs', show blocks - i = (blocks - (i + 1)) + 1 by omega]
      rfl
  case hdone =>
    intro acc hinv
    refine ⟨acc, absorb_body_done fInst f r c p blocks acc, ?_, hinv⟩
    rw [show blocks - blocks = 0 by omega]
    rfl
  obtain ⟨s', hloop, hval, hlen⟩ := h
  refine ⟨s', ?_, ?_, hlen⟩
  · unfold pedantic_sha3.sponge.sponge_loop0
    exact hloop
  · rw [hval]
    simp

end Absorb


/-! ### The squeeze loop

The only loop here that is not over a range: its exit test (`d ≤ |Z|`) lives in
its body, so the induction is on the output still owed rather than on an index. -/

section Squeeze

variable {Fty : Type}
  (fInst : core.ops.function.Fn Fty (Slice Bool) (alloc.vec.Vec Bool)) (f : Fty)
  (F : List Bool → List Bool) (b : Nat)

theorem squeeze_body_eq (hF : PermSpec fInst f F b) (r : Nat) (d : Nat)
    (hr : r ≤ b) (_hb : b ≤ 1600) (s : alloc.vec.Vec Bool)
    (z : pedantic_sha3.bits.BitStr) (hs : s.val.length = b) :
    ∃ z1 : pedantic_sha3.bits.BitStr, z1 = z ++ s.val.take r ∧
      ((d ≤ z1.length ∧
          pedantic_sha3.sponge.sponge_loop1.body fInst f r d s z
            = ok (.done z1)) ∨
       (¬ (d ≤ z1.length) ∧ ∃ s' : alloc.vec.Vec Bool, s'.val = F s.val ∧
          pedantic_sha3.sponge.sponge_loop1.body fInst f r d s z
            = ok (.cont (s', z1)))) := by
  -- each turn takes the rate down to a `usize` for `Trunc_r`; it fits, being
  -- at most the width
  obtain ⟨rU, hrU, hrUv⟩ := to_usize_eq r (by scalar_tac)
  obtain ⟨head, hhead, hheadv⟩ := trunc_eq s rU (by omega)
  have hheadlen : head.val.length = r := by
    rw [hheadv]; simp; omega
  refine ⟨z ++ head.val, by rw [hheadv, hrUv], ?_⟩
  by_cases hd : d ≤ (z ++ head.val).length
  · refine Or.inl ⟨hd, ?_⟩
    have hdn : d ≤ z.length + head.val.length := by simpa using hd
    unfold pedantic_sha3.sponge.sponge_loop1.body
      pedantic_sha3.bits.BitStr.from_bits
      pedantic_sha3.bits.BitStr.concat
      pedantic_sha3.bits.BitStr.len
      pedantic_sha3.nat.Nat.Insts.CoreCmpPartialOrdNat.le
    simp [vec_deref_eq, hrU, hhead, hdn]
  · obtain ⟨s', hs', hs'v, -⟩ := hF s (by omega)
    refine Or.inr ⟨hd, s', hs'v, ?_⟩
    have hdn : ¬ (d ≤ z.length + head.val.length) := by simpa using hd
    unfold pedantic_sha3.sponge.sponge_loop1.body
      pedantic_sha3.bits.BitStr.from_bits
      pedantic_sha3.bits.BitStr.concat
      pedantic_sha3.bits.BitStr.len
      pedantic_sha3.nat.Nat.Insts.CoreCmpPartialOrdNat.le
    simp [vec_deref_eq, hrU, hhead, hdn, hs']


/-- The squeeze loop: it emits `r` bits per turn until `d` are out.

    The fuel is what says the loop terminates; there is no second hypothesis
    about `Z` fitting a word, because `len(Z)` is a `Nat`. -/
theorem squeeze_loop_eq (hF : PermSpec fInst f F b) (r : Nat) (d : Nat)
    (hr : r ≤ b) (hb : b ≤ 1600) :
    ∀ (k : Nat) (s : alloc.vec.Vec Bool) (z : pedantic_sha3.bits.BitStr),
      s.val.length = b →
      d ≤ z.length + (k + 1) * r →
      ∃ out : pedantic_sha3.bits.BitStr,
        pedantic_sha3.sponge.sponge_loop1 fInst f r d s z = ok out ∧
        out = squeezeFrom F r d k s.val z := by
  intro k
  induction k with
  | zero =>
    intro s z hs hfuel
    obtain ⟨z1, hz1v, hcase⟩ :=
      squeeze_body_eq fInst f F b hF r d hr hb s z hs
    have hd : d ≤ z1.length := by
      rw [hz1v]
      simp only [List.length_append, List.length_take]
      omega
    rcases hcase with ⟨_, hbody⟩ | ⟨hne, _⟩
    · refine ⟨z1, ?_, ?_⟩
      · unfold pedantic_sha3.sponge.sponge_loop1
        simp [loop.eq_def, hbody]
      · rw [hz1v]
        rfl
    · exact absurd hd hne
  | succ k ih =>
    intro s z hs hfuel
    obtain ⟨z1, hz1v, hcase⟩ :=
      squeeze_body_eq fInst f F b hF r d hr hb s z hs
    have hz1len : z1.length = z.length + r := by
      rw [hz1v]
      simp only [List.length_append, List.length_take]
      omega
    rcases hcase with ⟨hd, hbody⟩ | ⟨hne, s', hs'v, hbody⟩
    · refine ⟨z1, ?_, ?_⟩
      · unfold pedantic_sha3.sponge.sponge_loop1
        simp [loop.eq_def, hbody]
      · rw [hz1v]
        show _ = (if d ≤ (z ++ s.val.take r).length then _ else _)
        rw [if_pos (by rw [← hz1v]; exact hd)]
    · obtain ⟨out, hout, houtv⟩ := ih s' z1 (by
        rw [hs'v]
        obtain ⟨_, _, _, hlen⟩ := hF s (by omega)
        exact hlen) (by
        have : (k + 1 + 1) * r = r + (k + 1) * r := by ring
        omega)
      refine ⟨out, ?_, ?_⟩
      · unfold pedantic_sha3.sponge.sponge_loop1
        rw [loop.eq_def]
        simp only [hbody]
        exact hout
      · rw [houtv, hz1v, hs'v]
        show _ = (if d ≤ (z ++ s.val.take r).length then _ else _)
        rw [if_neg (by rw [← hz1v]; exact hne)]

end Squeeze


/-! ### The sponge -/

/-- Squeezing to completion: enough turns for `d` bits at `r` per turn. -/
def squeezeAll (F : List Bool → List Bool) (r d : Nat) (s : List Bool) : List Bool :=
  squeezeFrom F r d (d / r) s []

/-- Squeezing really does produce at least `d` bits. -/
theorem squeezeFrom_len {b : Nat} (F : List Bool → List Bool)
    (hFlen : ∀ x : List Bool, x.length = b → (F x).length = b)
    (r d : Nat) (_hr : 0 < r) (hrb : r ≤ b) :
    ∀ (k : Nat) (s z : List Bool), s.length = b → d ≤ z.length + (k + 1) * r →
      d ≤ (squeezeFrom F r d k s z).length := by
  intro k
  induction k with
  | zero =>
    intro s z hs hfuel
    simp only [squeezeFrom, List.length_append, List.length_take, hs]
    omega
  | succ k ih =>
    intro s z hs hfuel
    by_cases hd : d ≤ (z ++ s.take r).length
    · show d ≤ (List.length (if d ≤ (z ++ s.take r).length then (z ++ s.take r) else _))
      rw [if_pos hd]
      exact hd
    · show d ≤ (List.length (if d ≤ (z ++ s.take r).length then (z ++ s.take r) else _))
      rw [if_neg hd]
      refine ih (F s) (z ++ s.take r) (hFlen s hs) ?_
      simp only [List.length_append, List.length_take, hs] at *
      have : (k + 1 + 1) * r = r + (k + 1) * r := by ring
      omega

section Sponge

variable {Fty Pty : Type}
  (fInst : core.ops.function.Fn Fty (Slice Bool) (alloc.vec.Vec Bool)) (f : Fty)
  (padInst : core.ops.function.Fn Pty
    (pedantic_sha3.nat.Nat × pedantic_sha3.nat.Nat) pedantic_sha3.bits.BitStr)
  (pad : Pty) (F : List Bool → List Bool) (b : Nat)

/-- What the closure `pad` has to be: FIPS 202's `pad10*1`.

    No bound on `m`, and none on `r` beyond Sec. 4's own: the lengths are
    `nat::Nat`, and `pad10*1` is total on them. -/
def PadSpec : Prop :=
  ∀ r m : Nat, 0 < r → padInst.call pad (r, m) = ok (padBits r m)

/-- The padded message is a whole number of blocks -- the point of `pad10*1`. -/
theorem padBits_len (x m : Nat) (_hx : 0 < x) :
    (padBits x m).length = ((-(m : Int) - 2) % (x : Int)).toNat + 2 := by
  simp [padBits]

theorem padBits_length (x m : Nat) (hx : 0 < x) :
    (m + (padBits x m).length) % x = 0 := by
  have hj : (((-(m : Int) - 2) % (x : Int)).toNat : Int) = (-(m : Int) - 2) % (x : Int) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
  have hint : ((m + (padBits x m).length : Nat) : Int) % (x : Int) = 0 := by
    rw [padBits_len x m hx]
    push_cast
    rw [hj]
    have hre : ((m : Int) + ((-(m : Int) - 2) % (x : Int) + 2))
        = (((m : Int) + 2) + ((-(m : Int) - 2) % (x : Int))) := by ring
    rw [hre, Int.add_emod, Int.emod_emod_of_dvd _ dvd_rfl, ← Int.add_emod]
    ring_nf
    exact Int.zero_emod _
  have hcast : (((m + (padBits x m).length) % x : Nat) : Int) = 0 := by
    rw [Int.natCast_mod]
    exact hint
  exact_mod_cast hcast

/-- `SPONGE[f, pad, r](N, d)` (FIPS 202, Algorithm 8).

    The message is an arbitrary-length `BitStr` and its length is a `nat::Nat`,
    so nothing here is bounded: what this theorem asks is Sec. 4's own
    `0 < r < b` and Table 1's `b ≤ 1600`, and that is all. -/
theorem sponge_eq (hF : PermSpec fInst f F b) (hP : PadSpec padInst pad)
    (bU : Std.Usize) (r d : Nat) (hbU : bU.val = b) (hb : b ≤ 1600)
    (hr0 : 0 < r) (hrb : r < b)
    (n : pedantic_sha3.bits.BitStr) :
    ∃ out : pedantic_sha3.bits.BitStr,
      pedantic_sha3.sponge.sponge fInst padInst f bU pad r n d = ok out ∧
      out =
        (squeezeAll F r d
          (absorbFrom F r (b - r) (n ++ padBits r n.length)
            (List.replicate b false) 0
            ((n ++ padBits r n.length).length / r))).take d := by
  have hFlen : ∀ x : List Bool, x.length = b → (F x).length = b := by
    intro x hx
    obtain ⟨_, _, _, hlen⟩ := hF ⟨x, by scalar_tac⟩ hx
    exact hlen
  -- 1. `len(N)`, then `pad(r, len(N))`, then `P = N || pad`, then `len(P)`. `len`
  --    is total, so both lengths are equations rather than facts about a word.
  have hnlen : pedantic_sha3.bits.BitStr.len n = ok n.length := rfl
  have hpad : padInst.call pad (r, n.length) = ok (padBits r n.length) := hP r n.length hr0
  set P : pedantic_sha3.bits.BitStr := n ++ padBits r n.length with hPdef
  have hPlen : P.length = n.length + (padBits r n.length).length := by rw [hPdef]; simp
  have hplenok : pedantic_sha3.bits.BitStr.len P = ok P.length := rfl
  have hpmod : P.length % r = 0 := by
    rw [hPlen]
    exact padBits_length r n.length hr0
  -- 2. blocks, capacity, the zero state
  have hrne : ¬ (r = 0) := by omega
  have hblocks : pedantic_sha3.nat.Nat.Insts.CoreOpsArithDivNatNat.div P.length r
      = ok (P.length / r) := by
    unfold pedantic_sha3.nat.Nat.Insts.CoreOpsArithDivNatNat.div
    rw [if_neg hrne]
  have hblocksn : (P.length / r) * r = P.length :=
    Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hpmod)
  obtain ⟨rU, hrU, hrUv⟩ := to_usize_eq r (by scalar_tac)
  obtain ⟨cU, hc, hcv⟩ := usize_sub_eq bU rU (by rw [hrUv]; omega)
  obtain ⟨s1, hs1, hs1v⟩ := zeros_eq bU
  have hs1len : s1.val.length = b := by rw [hs1v]; simp; omega
  -- 3. absorb, then squeeze
  obtain ⟨s2, habs, habsv, habslen⟩ :=
    absorb_loop_eq fInst f F b hF r cU (by rw [hcv, hrUv]; omega) hb hr0 P
      (P.length / r) hblocksn s1 hs1len
  obtain ⟨z1, hsq, hsqv⟩ := squeeze_loop_eq fInst f F b hF r d (by omega) hb
    (d / r) s2 [] habslen
    (by
      simp only [List.length_nil, Nat.zero_add]
      have h1 : d / r * r + d % r = d := by
        have h0 : r * (d / r) + d % r = d := Nat.div_add_mod _ _
        have hcomm : d / r * r = r * (d / r) := Nat.mul_comm _ _
        omega
      have h2 : d % r < r := Nat.mod_lt _ hr0
      have : (d / r + 1) * r = d / r * r + r := by ring
      omega)
  -- 4. the squeeze really produced `d` bits, so the final truncation is in range
  have hz1len : d ≤ z1.length := by
    rw [hsqv]
    refine squeezeFrom_len F hFlen r d hr0 (by omega) _ s2.val [] habslen ?_
    have h1 : d / r * r + d % r = d := by
      have h0 : r * (d / r) + d % r = d := Nat.div_add_mod _ _
      have hcomm : d / r * r = r * (d / r) := Nat.mul_comm _ _
      omega
    have h2 : d % r < r := Nat.mod_lt _ hr0
    have : (d / r + 1) * r = d / r * r + r := by ring
    simp
    omega
  refine ⟨z1.take d, ?_, ?_⟩
  · have hcat : pedantic_sha3.bits.BitStr.concat n (padBits r n.length) = ok P := rfl
    have hempty : (pedantic_sha3.bits.BitStr.empty : RustM pedantic_sha3.bits.BitStr)
        = ok ([] : List Bool) := rfl
    have hnew0 : pedantic_sha3.nat.Nat.new 0#u128 = ok 0 := rfl
    have htr : pedantic_sha3.bits.BitStr.trunc z1 d = ok (z1.take d) := if_pos hz1len
    -- Sec. 4's `0 < r < b`, which the function checks before anything else
    have hgt : pedantic_sha3.nat.Nat.Insts.CoreCmpPartialOrdNat.gt r 0 = ok true := by
      unfold pedantic_sha3.nat.Nat.Insts.CoreCmpPartialOrdNat.gt; simp [hr0]
    have hfromb : pedantic_sha3.nat.Nat.from_usize bU = ok b := by
      unfold pedantic_sha3.nat.Nat.from_usize; rw [hbU]
    have hlt : pedantic_sha3.nat.Nat.Insts.CoreCmpPartialOrdNat.lt r b = ok true := by
      unfold pedantic_sha3.nat.Nat.Insts.CoreCmpPartialOrdNat.lt; simp [hrb]
    have hmt : (massert true : RustM Unit) = ok () := rfl
    -- Step 4's `len(P) ≡ 0 (mod r)`, which the function checks before dividing
    have hrem : pedantic_sha3.nat.Nat.Insts.CoreOpsArithRemNatNat.rem P.length r = ok 0 := by
      unfold pedantic_sha3.nat.Nat.Insts.CoreOpsArithRemNatNat.rem
      rw [if_neg hrne, hpmod]
    have heq : pedantic_sha3.nat.Nat.Insts.CoreCmpPartialEqNat.eq 0 0 = ok true := rfl
    unfold pedantic_sha3.sponge.sponge
    rw [hnew0, bind_tc_ok, hgt, bind_tc_ok, hmt, bind_tc_ok, hfromb, bind_tc_ok, hlt,
      bind_tc_ok, hmt, bind_tc_ok,
      hnlen, bind_tc_ok, hpad, bind_tc_ok, hcat, bind_tc_ok, hplenok, bind_tc_ok,
      hrem, bind_tc_ok, heq, bind_tc_ok, hmt, bind_tc_ok, hblocks, bind_tc_ok, hrU, bind_tc_ok, hc, bind_tc_ok,
      hs1, bind_tc_ok, habs, bind_tc_ok, hempty, bind_tc_ok, hsq, bind_tc_ok]
    exact htr
  · rw [hsqv, habsv, hs1v]
    simp only [squeezeAll, hcv, hrUv, hbU, hPdef]

end Sponge

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Fips.sponge_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms sponge_eq

end LibcruxIotSha3.Fips
