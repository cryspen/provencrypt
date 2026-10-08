import Aeneas
import Hax
/-!
# Small facts about Hoare triples over `RustM`

Combining two posts about the same computation, moving a pure precondition into
the context, and `(pure P).holds ↔ P`.
-/

open Aeneas Aeneas.Std Std.Do

namespace libcrux_iot_sha3.Support

/-- `RustM` is deterministic, so two posts proved separately about the same
    computation hold together. -/
theorem triple_conj_post {α} {e : Aeneas.Std.RustM α} {Q R : α → Prop}
    (hQ : ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄)
    (hR : ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜R r⌝⦄) :
    ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r ∧ R r⌝⦄ := by
  cases e
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]

/-- Move a pure precondition `⌜P⌝` into the context. -/
theorem triple_imp_intro {α} {e : Aeneas.Std.RustM α} {P : Prop} {Q : α → Prop}
    (h : P → ⦃⌜True⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄) :
    ⦃⌜P⌝⦄ e ⦃⇓ r => ⌜Q r⌝⦄ := by
  cases e
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]
  · simp_all [Std.Do.Triple, WP.wp, PredTrans.apply]

theorem pure_prop_holds {P : Prop} (h : P) : (pure P : RustM Prop).holds := by
  simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, WP.wp]
  intro _
  exact h

theorem of_pure_prop_holds {P : Prop} (h : (pure P : RustM Prop).holds) : P := by
  simp only [Aeneas.Std.RustM.holds, Std.Do.Triple, WP.wp] at h
  exact h trivial

/-- A triple with a `noThrow` post means the computation returns a value
    satisfying the post. -/
theorem triple_exists_ok {α : Type} {x : RustM α} {P : α → Prop}
    (h : ⦃ ⌜ True ⌝ ⦄ x ⦃ ⇓ r => ⌜ P r ⌝ ⦄) : ∃ v, x = .ok v ∧ P v := by
  match hx : x with
  | .ok v =>
      refine ⟨v, rfl, ?_⟩
      have h' := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at h'; exact h'
  | .fail e =>
      exfalso; have h' := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at h'
  | .div =>
      exfalso; have h' := h; simp [Std.Do.Triple, WP.wp, PredTrans.apply] at h'

end libcrux_iot_sha3.Support
