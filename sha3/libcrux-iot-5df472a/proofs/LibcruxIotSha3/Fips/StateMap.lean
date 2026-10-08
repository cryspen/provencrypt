import PedanticSha3
import LibcruxIotSha3.Model.LaneModel
/-!
# The state correspondence between the lane model and the transcript

The lane model keeps the Keccak state as 25 `u64` lanes, `state[5*y + x]` holding
the lane `A[x, y]` (FIPS 202, Sec. 3.1.2); `pedantic-sha3` keeps it as the
FIPS state array itself, `A.a[x][y][z] : Bool`.  With `w = 64` the two are the
same data, related by "bit `z` of the lane is `A[x, y, z]`" -- which is exactly
the lane convention of Sec. 3.1.2, `S[w(5y + x) + z] = A[x, y, z]`, read
little-endian within the lane.

This module provides the state array at `w = 64` (`SA`), reading a bit of it
(`bitAt`), building one from a bit function (`mkSA`), and extensionality.  The
step mappings in `Theta.lean`, ..., `Iota.lean` are characterised as bit functions
through these.
-/

open Aeneas Aeneas.Std
open LibcruxIotSha3.LaneModel

namespace LibcruxIotSha3.Fips

/-- The pedantic state array at the Keccak-f[1600] lane width, `w = 64`. -/
abbrev SA : Type := pedantic_sha3.state_array.StateArray 64#usize

/-! ### Reading a state array

`A[x][y][z]`, with out-of-range indices reading `false`.  Indices stay `Nat`
here (rather than `Fin`): the extracted definitions index with `Usize` values
whose bounds are proof obligations discharged inside `RustM`, and matching that
shape keeps the step-mapping lemmas free of index coercions. -/
def bitAt (A : SA) (x y z : Nat) : Bool := A.a.val[x]!.val[y]!.val[z]!

/-! ### The two directions -/

/-- The state array whose bits are given by `f` (a "`ofFn` for state arrays").
    Every characterisation of an extracted step mapping below has the shape
    `step A = ok (mkSA <FIPS formula in bitAt A>)`, so this is the one place
    where a state array is built. -/
def mkSA (f : Nat → Nat → Nat → Bool) : SA :=
  { a := ⟨(List.ofFn fun x : Fin 5 =>
            (⟨(List.ofFn fun y : Fin 5 =>
                (⟨List.ofFn fun z : Fin 64 => f x.val y.val z.val, by simp⟩ :
                  Array Bool 64#usize)), by simp⟩ :
              Array (Array Bool 64#usize) 5#usize)), by simp⟩ }

/-! ### Projection and extensionality

`mkSA` is projected by `bitAt` (in range), and two state arrays with the same
bits are equal.  Both are proved by `getElem!` rewriting rather than `simp`:
unfolding the three nested `List.ofFn`s of `mkSA` produces a literal
5 x 5 x 64 list, which is unusable downstream. -/

@[simp]
theorem bitAt_mkSA (f : Nat → Nat → Nat → Bool) {x y z : Nat}
    (hx : x < 5) (hy : y < 5) (hz : z < 64) :
    bitAt (mkSA f) x y z = f x y z := by
  simp only [bitAt, mkSA, List.getElem!_eq_getElem?_getD, List.length_ofFn,
    List.getElem?_eq_getElem, hx, hy, hz, List.getElem_ofFn, Option.getD_some]

/-- Extensionality for the Aeneas fixed-size arrays the state array is built
    from, in terms of the `[i]!` accessor `bitAt` uses. -/
private theorem array_ext_getElem! {α : Type} [Inhabited α] {n : Std.Usize}
    (a b : Array α n) (h : ∀ i, i < n.val → a.val[i]! = b.val[i]!) : a = b := by
  apply Subtype.ext
  apply List.ext_getElem (by rw [a.property, b.property])
  intro i h1 h2
  have hi : i < n.val := by rw [a.property] at h1; exact h1
  have hab := h i hi
  rwa [getElem!_pos a.val i (by omega), getElem!_pos b.val i (by omega)] at hab

theorem ext {A B : SA} (h : ∀ x y z, x < 5 → y < 5 → z < 64 → bitAt A x y z = bitAt B x y z) :
    A = B := by
  have h5 : (5#usize).val = 5 := by simp
  have h64 : (64#usize).val = 64 := by simp
  obtain ⟨a⟩ := A; obtain ⟨b⟩ := B
  congr 1
  refine array_ext_getElem! _ _ (fun x hx => array_ext_getElem! _ _ (fun y hy =>
    array_ext_getElem! _ _ (fun z hz => ?_)))
  exact h x y z (by omega) (by omega) (by omega)

/-- `mkSA` is surjective onto state arrays: rebuilding a state array from its own
    bits gives it back.  Loop invariants below are stated with `mkSA`, and this is
    how they are started from an arbitrary initial state array. -/
@[simp]
theorem mkSA_bitAt (A : SA) : mkSA (bitAt A) = A :=
  ext (fun _ _ _ hx hy hz => bitAt_mkSA _ hx hy hz)

/-- Two state arrays built from functions agreeing in range are equal. -/
theorem mkSA_congr {f g : Nat → Nat → Nat → Bool}
    (h : ∀ x y z, x < 5 → y < 5 → z < 64 → f x y z = g x y z) : mkSA f = mkSA g :=
  ext (fun x y z hx hy hz => by
    rw [bitAt_mkSA _ hx hy hz, bitAt_mkSA _ hx hy hz]; exact h x y z hx hy hz)

end LibcruxIotSha3.Fips
