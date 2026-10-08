import LibcruxIotSha3.Fips.Sponge
import LibcruxIotSha3.Fips.KeccakP
/-!
# `KECCAK[c]` (FIPS 202, Sec. 5.2)

`KECCAK[c](N, d) = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 - c](N, d)`.  Both
of the sponge's abstract members are discharged here: the permutation is the one
`Fips/KeccakP` pins down, and the padding is `pad10*1`.
-/

open CoreModels Aeneas
open Aeneas.Std hiding namespace core alloc
open RustM ControlFlow
open Std.Do

namespace LibcruxIotSha3.Fips

/-- A bit string read as a state array. -/
def bitsOfList (s : List Bool) : Nat → Nat → Nat → Bool := fun x y z => s[bitPos x y z]!

theorem bitsOf_eq (s : Slice Bool) : bitsOf s = bitsOfList s.val := rfl

/-- `Keccak-p[1600, 24]` as a function on bit strings. -/
def keccakF (s : List Bool) : List Bool :=
  (List.range 1600).map (fun p =>
    roundsFrom (bitsOfList s) 0 24 ((p / 64) % 5) (p / 320) (p % 64))

theorem keccakF_len (s : List Bool) : (keccakF s).length = 1600 := by
  simp [keccakF]

/-- The extracted permutation is `keccakF`. -/
theorem keccak_p_1600_eq (s : Slice Bool) (hs : s.val.length = 1600) :
    ∃ out : alloc.vec.Vec Bool,
      pedantic_sha3.keccak_p.keccak_p 64#usize s 24#usize = ok out ∧
      out.val = keccakF s.val := by
  obtain ⟨out, hout, hlen, hbits⟩ := keccak_p_eq s hs 24#usize (by simp) (by simp)
  refine ⟨out, hout, ?_⟩
  apply List.ext_getElem (by rw [hlen, keccakF_len])
  intro p h1 h2
  rw [hlen] at h1
  have hp := hbits p h1
  rw [getElem!_pos out.val p (by omega)] at hp
  rw [hp, bitsOf_eq]
  simp only [keccakF, List.getElem_map, List.getElem_range]
  norm_num

/-- The closure `keccak_c` passes as `f`. -/
abbrev keccakFInst :=
  pedantic_sha3.sponge.keccak_c.closure.Insts.CoreOpsFunctionFnTupleSharedSliceBoolVecBool

/-- The closure `keccak_c` passes as `pad`. -/
abbrev keccakPadInst :=
  pedantic_sha3.sponge.keccak_c.closure_1.Insts.CoreOpsFunctionFnPairNatNatBitStr

/-- The sponge's two abstract members, for `KECCAK[c]`. -/
theorem keccak1600_perm : PermSpec keccakFInst () keccakF 1600 := by
  intro s hs
  obtain ⟨out, hout, houtv⟩ := keccak_p_1600_eq s hs
  exact ⟨out, hout, houtv, keccakF_len s.val⟩

theorem keccak1600_pad : PadSpec keccakPadInst () := by
  intro r m hr0
  exact pad10_star_1_eq r m hr0


/-- `KECCAK[c](N, d)` (FIPS 202, Sec. 5.2).

    `N` is an arbitrary-length bit string and `d` a `nat::Nat`: nothing here is
    bounded but the capacity, which Sec. 5.2 bounds itself. -/
theorem keccak_c_eq (c : Std.Usize) (hc0 : 0 < c.val) (hc : c.val < 1600)
    (n : pedantic_sha3.bits.BitStr) (d : Nat) :
    ∃ out : pedantic_sha3.bits.BitStr,
      pedantic_sha3.sponge.keccak_c c n d = ok out ∧
      out =
        (squeezeAll keccakF (1600 - c.val) d
          (absorbFrom keccakF (1600 - c.val) c.val
            (n ++ padBits (1600 - c.val) n.length) (List.replicate 1600 false) 0
            ((n ++ padBits (1600 - c.val) n.length).length / (1600 - c.val)))).take
          d := by
  have hB : (pedantic_sha3.sponge.B).val = 1600 := by
    simp [pedantic_sha3.sponge.B]
  obtain ⟨rU, hrU, hrUv⟩ := usize_sub_eq pedantic_sha3.sponge.B c (by omega)
  have hrUn : rU.val = 1600 - c.val := by rw [hrUv, hB]
  -- the rate crosses to `nat::Nat`, where the bit lengths live
  have hfrom : pedantic_sha3.nat.Nat.from_usize rU = ok rU.val := rfl
  obtain ⟨out, hout, houtv⟩ :=
    sponge_eq keccakFInst () keccakPadInst () keccakF 1600 keccak1600_perm keccak1600_pad
      pedantic_sha3.sponge.B rU.val d hB (by omega) (by omega) (by omega) n
  refine ⟨out, ?_, ?_⟩
  · unfold pedantic_sha3.sponge.keccak_c
    rw [hrU, bind_tc_ok, hfrom, bind_tc_ok]
    exact hout
  · rw [houtv, hrUn, show 1600 - (1600 - c.val) = c.val from by omega]

-- Pinned by `#guard_msgs`: the build fails if this comes to depend on any axiom
-- beyond Lean's standard three.
/--
info: 'LibcruxIotSha3.Fips.keccak_c_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms keccak_c_eq

end LibcruxIotSha3.Fips
