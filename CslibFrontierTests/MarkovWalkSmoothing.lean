/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Probability.MarkovChain.RotationSmoothing

/-! The lazy walk of the two-point swap is uniform after either of its first two steps. Its
averaged rotation map has eight labels. Padding to seventeen requires one holding label. -/

open Cslib Finset
open scoped BigOperators

example : ∃ R : RotationMap Bool (Fin 17), ∀ (f : Bool → ℝ), (∀ v, 0 ≤ f v) →
    (f false + f true) / 2 ≤ 2 * R.walk f false := by
  let G : RotationMap Bool Unit :=
    { rot p := (!p.1, p.2)
      rot_involutive := by rintro ⟨v, d⟩; cases v <;> rfl }
  have hswap (f : Bool → ℝ) (v : Bool) : G.walk f v = f (!v) := by
    simp [RotationMap.walk_apply, RotationMap.neighbor, G]
  have havg (f : Bool → ℝ) :
      (𝔼 h : Fin 2, (G.lazy.walk ^ (h.val + 1)) f false) = (f false + f true) / 2 := by
    rw [Fintype.expect_eq_sum_div_card, Fin.sum_univ_two]
    change (G.lazy.walk f false + G.lazy.walk (G.lazy.walk f) false) / 2 = _
    simp only [RotationMap.walk_lazy_apply, hswap, Bool.not_false, Bool.not_true]
    ring
  obtain ⟨R, hR⟩ := G.exists_padded_lazy_cesaro (T := Fin 17) (t := 2) (by decide) (by decide)
  exact ⟨R, fun f hf => (havg f).symm.trans_le (hR f hf false)⟩
