/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.OddCycle
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Pentagon

public section

open SimpleGraph Real
open scoped RealInnerProductSpace

namespace Cslib.Tests.OddCycle

/-! ### Both representations are instances for odd `n ≥ 3` -/

example : (cycleGraph 7).IsOrthonormalRepresentation (oddCycleFourier 7) :=
  isOrthonormalRepresentation_oddCycleFourier (by decide) (by norm_num)

example : (cycleGraph 7)ᶜ.IsOrthonormalRepresentation (oddCycleComplUmbrella 7) :=
  isOrthonormalRepresentation_oddCycleComplUmbrella (by decide) (by norm_num)

/-- The Fourier representation of `C₅` is not a representation of `C₅ᶜ`: the vertices `0` and `1`
are nonadjacent in `C₅ᶜ` (adjacent in `C₅`) and have inner product `(2 cos (π/5))⁻¹ > 0`. -/
example : ¬(cycleGraph 5)ᶜ.IsOrthonormalRepresentation (oddCycleFourier 5) := by
  intro h
  have h0 := h.inner_eq_zero (v := 0) (w := 1) (by decide) (by decide)
  rw [inner_oddCycleFourier_of_adj (by decide) (by norm_num) (by decide)] at h0
  push_cast at h0
  rw [cos_pi_div_five] at h0
  have hpos : (0 : ℝ) < (2 * ((1 + √5) / 4))⁻¹ := by positivity
  linarith

/-- Conversely, the umbrella of `C₅ᶜ` is not a representation of `C₅`: the vertices `0` and `2`
are nonadjacent in `C₅`, yet their umbrella vectors have positive inner product. -/
example : ¬(cycleGraph 5).IsOrthonormalRepresentation (oddCycleComplUmbrella 5) := by
  intro h
  have h0 := h.inner_eq_zero (v := 0) (w := 2) (by decide) (by decide)
  rw [inner_oddCycleComplUmbrella (by norm_num)] at h0
  have harg : (π - π / ((5 : ℕ) : ℝ)) * ((0 : Fin 5) : ℕ) -
      (π - π / ((5 : ℕ) : ℝ)) * ((2 : Fin 5) : ℕ) = -(2 * π - 2 * π / 5) := by
    change (π - π / ((5 : ℕ) : ℝ)) * (0 : ℕ) - (π - π / ((5 : ℕ) : ℝ)) * (2 : ℕ) = _
    push_cast
    ring
  rw [harg, cos_neg, cos_two_pi_sub] at h0
  have hc1 : 0 < cos (π / ((5 : ℕ) : ℝ)) := by
    push_cast
    rw [cos_pi_div_five]
    positivity
  have hc2 : 0 < cos (2 * π / 5) := by
    apply cos_pos_of_mem_Ioo
    constructor <;> linarith [pi_pos]
  have hpos : (0 : ℝ) < cos (π / ((5 : ℕ) : ℝ)) / (1 + cos (π / ((5 : ℕ) : ℝ))) +
      1 / (1 + cos (π / ((5 : ℕ) : ℝ))) * cos (2 * π / 5) := by
    positivity
  linarith

/-! ### Edge cases of the odd-cycle formula -/

/-- For `n = 3` the formula gives `ϑ(C₃) = 1` and `ϑ(C₃ᶜ) = 3`. -/
example : (cycleGraph 3).lovaszTheta = 1 ∧ (cycleGraph 3)ᶜ.lovaszTheta = 3 := by
  rw [lovaszTheta_cycleGraph_of_odd (by decide) le_rfl,
    lovaszTheta_compl_cycleGraph_of_odd (by decide) le_rfl]
  push_cast
  rw [cos_pi_div_three]
  norm_num

/-- For `n = 5` the formula agrees with `ϑ(C₅) = √5` from the pentagon umbrella. -/
example : (5 : ℕ) * cos (π / (5 : ℕ)) / (1 + cos (π / (5 : ℕ))) = (cycleGraph 5).lovaszTheta := by
  rw [lovaszTheta_cycleGraph_five]
  push_cast
  rw [cos_pi_div_five]
  have h5 : √5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h5pos : 0 < √5 := by positivity
  field_simp
  linear_combination -h5

/-- `ϑ(C₅) ϑ(C₅ᶜ) = 5` and `5 ≤ α(C₅ ⊠ C₅ᶜ)`. -/
example : (cycleGraph 5).lovaszTheta * (cycleGraph 5)ᶜ.lovaszTheta = 5 ∧
    5 ≤ (cycleGraph 5 ⊠ (cycleGraph 5)ᶜ).indepNum := by
  refine ⟨?_, ?_⟩
  · exact_mod_cast lovaszTheta_cycleGraph_mul_compl_of_odd (n := 5) (by decide) (by norm_num)
  · simpa using natCard_le_indepNum_strongProd_compl (G := cycleGraph 5)

/-! ### The heptagon: `3 ≤ ϑ(C₇)` and `Θ(C₇) < 7/2` -/

example : (3 : ℝ) ≤ (cycleGraph 7).lovaszTheta := by
  have hind : (cycleGraph 7).IsIndepSet ({0, 2, 4} : Finset (Fin 7)) := by
    have : ∀ x ∈ ({0, 2, 4} : Finset (Fin 7)), ∀ y ∈ ({0, 2, 4} : Finset (Fin 7)), x ≠ y →
        ¬(cycleGraph 7).Adj x y := by decide
    exact fun x hx y hy => this x hx y hy
  have h3 : (3 : ℝ) ≤ ((cycleGraph 7).indepNum : ℝ) := by
    exact_mod_cast (by simpa using hind.card_le_indepNum : 3 ≤ (cycleGraph 7).indepNum)
  exact h3.trans indepNum_le_lovaszTheta

example : (cycleGraph 7).shannonCapacity < 7 / 2 := by
  have hc : 0 < cos (π / (7 : ℕ)) := by
    apply cos_pos_of_mem_Ioo
    constructor <;> push_cast <;> linarith [pi_pos]
  have hc1 : cos (π / (7 : ℕ)) < 1 := by
    rw [← cos_zero]
    apply cos_lt_cos_of_nonneg_of_le_pi le_rfl
    · push_cast; linarith [pi_pos]
    · push_cast; positivity
  refine (shannonCapacity_cycleGraph_le_of_odd (by decide) (by norm_num)).trans_lt ?_
  rw [div_lt_div_iff₀ (by positivity) two_pos]
  push_cast at hc hc1 ⊢
  nlinarith

/-! ### Strict inequality in `|V| ≤ ϑ(G) ϑ(Gᶜ)` (`K₂ ⊕ K₁`, Knuth §23 (23.1)) -/

/-- `K₂ ⊕ K₁` on `Fin 3` (single edge `{0, 1}`) has `ϑ(G) = 2` and `ϑ(Gᶜ) = 2`, witnessing strict
inequality `3 = |V| < 4 = ϑ(G) ϑ(Gᶜ)` in `natCard_le_lovaszTheta_mul_lovaszTheta_compl`. -/
example :
    let G : SimpleGraph (Fin 3) :=
      { Adj := fun u v => (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0)
        symm := ⟨fun _ _ h => by tauto⟩
        loopless := ⟨fun u h => by rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> contradiction⟩ }
    (Nat.card (Fin 3) : ℝ) < G.lovaszTheta * Gᶜ.lovaszTheta := by
  intro G
  let : DecidableRel G.Adj := fun u v => by
    change Decidable ((u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0))
    infer_instance
  have hG : (2 : ℝ) ≤ G.lovaszTheta := by
    have hind : G.IsIndepSet ({0, 2} : Finset (Fin 3)) := by
      have : ∀ x ∈ ({0, 2} : Finset (Fin 3)), ∀ y ∈ ({0, 2} : Finset (Fin 3)), x ≠ y →
          ¬G.Adj x y := by decide
      exact fun x hx y hy => this x hx y hy
    exact (by exact_mod_cast (by simpa using hind.card_le_indepNum : 2 ≤ G.indepNum) :
      (2 : ℝ) ≤ (G.indepNum : ℝ)).trans indepNum_le_lovaszTheta
  have hGc : (2 : ℝ) ≤ Gᶜ.lovaszTheta := by
    have hind : Gᶜ.IsIndepSet ({0, 1} : Finset (Fin 3)) := by
      have : ∀ x ∈ ({0, 1} : Finset (Fin 3)), ∀ y ∈ ({0, 1} : Finset (Fin 3)), x ≠ y →
          ¬Gᶜ.Adj x y := by decide
      exact fun x hx y hy => this x hx y hy
    exact (by exact_mod_cast (by simpa using hind.card_le_indepNum : 2 ≤ Gᶜ.indepNum) :
      (2 : ℝ) ≤ (Gᶜ.indepNum : ℝ)).trans indepNum_le_lovaszTheta
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  norm_num
  nlinarith

end Cslib.Tests.OddCycle
