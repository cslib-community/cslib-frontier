/-
Copyright (c) 2026 Matthew Doty, Nick L. Leppelmeier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty, Nick L. Leppelmeier
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Berge
public import CslibFrontier.Foundations.Analysis.Kakutani
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Tests for Brouwer on the simplex, Berge's maximum theorem, and Kakutani's fixed-point theorem

* Brouwer on the simplex (`Cslib.Brouwer.exists_isFixedPt_simplex`): coordinate-swap map on the
  2-simplex `Fin 2 → ℝ`.
* Brouwer on compact convex sets (`Cslib.Kakutani.exists_isFixedPt_of_isCompact_convex`): linear
  contraction on `[-1, 1]`.
* Concrete Berge witness: maximizing `u x y = x * y` over `Γ x = [0, 1]` yields continuous value
  `maxValue Γ u x = max x 0`, and its maximizer correspondence is upper hemicontinuous.
* Concrete Kakutani witness via `Cslib.Kakutani.exists_mem_of_isClosed_graph`: the sign-flipped
  correspondence on `K = [-1, 1]` given by `F x = {1}` for `x < 0`, `F x = {-1}` for `x > 0`, and
  `F 0 = [-1, 1]` satisfies all hypotheses of Kakutani's theorem.
* Convexity counterexample: removing convexity (`F 0 = {-1, 1}`) destroys existence of a fixed
  point.
-/

@[expose] public section

namespace Cslib.Analysis.BergeKakutaniTests

open Set Filter Topology

section BrouwerTests

theorem exists_isFixedPt_swap_simplex :
    ∃ p : Fin 2 → ℝ, ((∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1) ∧
      Function.IsFixedPt (fun q : Fin 2 → ℝ => ![q 1, q 0]) p := by
  let f : (Fin 2 → ℝ) → Fin 2 → ℝ := fun q => ![q 1, q 0]
  have hf : MapsTo f {p | (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1}
      {p | (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1} := by
    rintro p ⟨hp0, hpsum⟩
    refine ⟨fun a => ?_, ?_⟩
    · fin_cases a <;> simp [f, hp0]
    · simpa [f, Fin.sum_univ_two, add_comm] using hpsum
  have hc : ContinuousOn f {p | (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1} := by
    refine Continuous.continuousOn ?_
    refine continuous_pi fun a => ?_
    fin_cases a <;> simp [f, continuous_apply]
  exact Cslib.Brouwer.exists_isFixedPt_simplex hf hc

end BrouwerTests

section BergeWitness

/-- Linear objective `u x y = x * y` on `Γ x = [0, 1]`. -/
def linΓ (_ : ℝ) : Set ℝ := Icc 0 1

/-- Objective `x * y`. -/
def linU (x y : ℝ) : ℝ := x * y

theorem maxValue_linU_pos {x : ℝ} (hx : 0 ≤ x) : Cslib.Berge.maxValue linΓ linU x = x := by
  have h1 : (1 : ℝ) ∈ Cslib.Berge.argmaxSet linΓ linU x := by
    refine ⟨⟨zero_le_one, le_rfl⟩, fun z hz => ?_⟩
    dsimp [linU]
    nlinarith [hz.1, hz.2]
  simpa [linU] using (Cslib.Berge.maxValue_eq_of_mem_argmaxSet h1).symm

theorem maxValue_linU_nonpos {x : ℝ} (hx : x ≤ 0) : Cslib.Berge.maxValue linΓ linU x = 0 := by
  have h0 : (0 : ℝ) ∈ Cslib.Berge.argmaxSet linΓ linU x := by
    refine ⟨⟨le_rfl, zero_le_one⟩, fun z hz => ?_⟩
    dsimp [linU]
    nlinarith [hz.1, hz.2]
  simpa [linU] using (Cslib.Berge.maxValue_eq_of_mem_argmaxSet h0).symm

private theorem linΓ_uhc : UpperHemicontinuousOn linΓ univ :=
  upperHemicontinuousOn_iff_forall_isOpen.mpr fun _ _ _ _ h => Eventually.of_forall fun _ => h

private theorem linΓ_lhc : LowerHemicontinuousOn linΓ univ :=
  lowerHemicontinuousOn_iff.mpr fun _ _ =>
    lowerHemicontinuousWithinAt_iff.mpr fun _ _ h => Eventually.of_forall fun _ => h

theorem continuous_maxValue_linU : Continuous (Cslib.Berge.maxValue linΓ linU) := by
  rw [← continuousOn_univ]
  exact Cslib.Berge.continuousOn_maxValue
    (fun _ _ => ⟨0, le_rfl, zero_le_one⟩)
    (fun _ _ => isCompact_Icc)
    linΓ_uhc linΓ_lhc
    (continuous_fst.mul continuous_snd).continuousOn

theorem upperHemicontinuous_argmaxSet_linU :
    UpperHemicontinuousOn (Cslib.Berge.argmaxSet linΓ linU) univ :=
  Cslib.Berge.upperHemicontinuousOn_argmaxSet
    (fun _ _ => ⟨0, le_rfl, zero_le_one⟩)
    (fun _ _ => isCompact_Icc)
    linΓ_uhc linΓ_lhc
    (continuous_fst.mul continuous_snd).continuousOn

end BergeWitness

section KakutaniWitness

/-- Compact convex interval `[-1, 1]` embedded in `Fin 1 → ℝ`. -/
def unitInterval1 : Set (Fin 1 → ℝ) := {x | -1 ≤ x 0 ∧ x 0 ≤ 1}

private theorem unitInterval1_eq_pi : unitInterval1 = univ.pi fun _ => Icc (-1 : ℝ) 1 := by
  ext x
  simp only [unitInterval1, mem_ofPred_eq, mem_univ_pi, mem_Icc, Fin.forall_fin_one]

private theorem unitInterval1_nonempty : unitInterval1.Nonempty :=
  ⟨0, by simp [unitInterval1]⟩

private theorem unitInterval1_isCompact : IsCompact unitInterval1 := by
  rw [unitInterval1_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_Icc

private theorem unitInterval1_convex : Convex ℝ unitInterval1 := by
  rw [unitInterval1_eq_pi]
  exact convex_pi fun _ _ => convex_Icc (-1 : ℝ) 1

theorem exists_isFixedPt_negHalf :
    ∃ x ∈ unitInterval1, Function.IsFixedPt (fun v : Fin 1 → ℝ => fun _ => -(v 0) / 2) x := by
  let f : (Fin 1 → ℝ) → Fin 1 → ℝ := fun v _ => -(v 0) / 2
  have hf : MapsTo f unitInterval1 unitInterval1 := fun x hx =>
    ⟨by dsimp [f]; linarith [hx.2], by dsimp [f]; linarith [hx.1]⟩
  have hc : ContinuousOn f unitInterval1 :=
    (continuous_pi fun _ => ((continuous_apply 0).neg).div_const 2).continuousOn
  exact Cslib.Kakutani.exists_isFixedPt_of_isCompact_convex
    unitInterval1_nonempty unitInterval1_isCompact unitInterval1_convex hf hc

/-- Classic upper hemicontinuous sign-flipped correspondence on `[-1, 1]`. -/
noncomputable def signFlip (x : Fin 1 → ℝ) : Set (Fin 1 → ℝ) :=
  if x 0 < 0 then {fun _ => 1}
  else if 0 < x 0 then {fun _ => -1}
  else unitInterval1

/-- Non-convex variant at `0` with no fixed point. -/
noncomputable def signFlipNonConvex (x : Fin 1 → ℝ) : Set (Fin 1 → ℝ) :=
  if x 0 < 0 then {fun _ => 1}
  else if 0 < x 0 then {fun _ => -1}
  else {fun _ => -1, fun _ => 1}

theorem exists_mem_signFlip : ∃ x ∈ unitInterval1, x ∈ signFlip x := by
  refine Cslib.Kakutani.exists_mem_of_isClosed_graph
    unitInterval1_nonempty unitInterval1_isCompact unitInterval1_convex ?_ ?_ ?_ ?_
  · intro x _
    dsimp [signFlip]
    split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · exact unitInterval1_nonempty
  · intro x _
    dsimp [signFlip]
    split_ifs
    · rintro y rfl
      exact ⟨by norm_num, by norm_num⟩
    · rintro y rfl
      exact ⟨by norm_num, by norm_num⟩
    · exact Subset.rfl
  · intro x _
    dsimp [signFlip]
    split_ifs
    · exact convex_singleton _
    · exact convex_singleton _
    · exact unitInterval1_convex
  · have hEq : {p : (Fin 1 → ℝ) × (Fin 1 → ℝ) | p.1 ∈ unitInterval1 ∧ p.2 ∈ signFlip p.1} =
        {p | (-1 ≤ p.1 0 ∧ p.1 0 ≤ 1) ∧ (-1 ≤ p.2 0 ∧ p.2 0 ≤ 1) ∧
          p.1 0 * p.2 0 ≤ 0 ∧ (p.1 0 = 0 ∨ |p.2 0| = 1)} := by
      ext ⟨x, y⟩
      dsimp [unitInterval1, signFlip]
      by_cases hx1 : x 0 < 0
      · simp only [hx1, ↓reduceIte, mem_singleton_iff]
        constructor
        · rintro ⟨hx, rfl⟩
          exact ⟨hx, ⟨by norm_num, by norm_num⟩, by linarith, Or.inr (by norm_num)⟩
        · rintro ⟨hx, _, hmul, _ | h1⟩
          · linarith
          · refine ⟨hx, ?_⟩
            ext a
            fin_cases a
            rcases abs_eq zero_le_one |>.mp h1 with hpos | hneg
            · exact hpos
            · exfalso
              have : 0 < x 0 * y 0 := mul_pos_of_neg_of_neg hx1 (by linarith)
              linarith
      · by_cases hx2 : 0 < x 0
        · simp only [hx1, ↓reduceIte, hx2, mem_singleton_iff]
          constructor
          · rintro ⟨hx, rfl⟩
            exact ⟨hx, ⟨by norm_num, by norm_num⟩, by linarith, Or.inr (by norm_num)⟩
          · rintro ⟨hx, _, hmul, _ | h1⟩
            · linarith
            · refine ⟨hx, ?_⟩
              ext a
              fin_cases a
              rcases abs_eq zero_le_one |>.mp h1 with hpos | hneg
              · exfalso
                have : 0 < x 0 * y 0 := mul_pos hx2 (by linarith)
                linarith
              · exact hneg
        · have hx0 : x 0 = 0 := le_antisymm (not_lt.mp hx2) (not_lt.mp hx1)
          simp only [hx1, ↓reduceIte, hx2, mem_ofPred_eq]
          constructor
          · rintro ⟨hx, hy⟩
            exact ⟨hx, hy, by simp [hx0], Or.inl hx0⟩
          · rintro ⟨hx, hy, _⟩
            exact ⟨hx, hy⟩
    rw [hEq]
    have hx_eval : Continuous fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => p.1 0 :=
      (continuous_apply 0).comp continuous_fst
    have hy_eval : Continuous fun p : (Fin 1 → ℝ) × (Fin 1 → ℝ) => p.2 0 :=
      (continuous_apply 0).comp continuous_snd
    refine ((isClosed_Ici.preimage hx_eval).inter (isClosed_Iic.preimage hx_eval)).inter
      (((isClosed_Ici.preimage hy_eval).inter (isClosed_Iic.preimage hy_eval)).inter
        ((isClosed_Iic.preimage (hx_eval.mul hy_eval)).inter
          ((isClosed_singleton.preimage hx_eval).union
            (isClosed_singleton.preimage hy_eval.abs))))

theorem not_exists_mem_signFlipNonConvex :
    ¬ ∃ x ∈ unitInterval1, x ∈ signFlipNonConvex x := by
  rintro ⟨x, _, hx⟩
  dsimp [signFlipNonConvex] at hx
  split_ifs at hx with h1 h2
  · have := congrFun hx 0
    linarith
  · have := congrFun hx 0
    linarith
  · rcases hx with hneg | hpos
    · have := congrFun hneg 0
      linarith
    · have := congrFun hpos 0
      linarith

end KakutaniWitness

end Cslib.Analysis.BergeKakutaniTests
