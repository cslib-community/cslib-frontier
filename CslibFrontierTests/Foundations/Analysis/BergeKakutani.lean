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
import Mathlib.Tactic.Ring

/-!
# Tests for Brouwer on the simplex, Berge's maximum theorem, and Kakutani's fixed-point theorem

* Brouwer on the simplex (`Cslib.Brouwer.exists_isFixedPt_simplex`): coordinate-swap map on the
  2-simplex `Fin 2 → ℝ`.
* Brouwer on compact convex sets (`Cslib.Brouwer.exists_isFixedPt_of_isCompact_convex`): linear
  contraction directly on `Icc (-1 : ℝ) 1 : Set ℝ`.
* Concrete Berge witness: maximizing `u x y = x * y` over `Γ x = [0, 1]` yields continuous value
  `maxValue Γ u x = max x 0`, and its maximizer correspondence is upper hemicontinuous.
* Convex and strictly quasiconcave Berge witness: maximizing `-(y - x)^2` over `[0, 1]` yields
  convex `argmaxSet`, subsingleton maximizers, and a continuous unique maximizer selection via
  `Cslib.Berge.exists_unique_continuousOn_argmaxSet`.
* Concrete Kakutani witness via `Cslib.Kakutani.exists_mem_of_isClosed_graph`: the sign-flipped
  correspondence on `Icc (-1 : ℝ) 1` given by `F x = {1}` for `x < 0`, `F x = {-1}` for `x > 0`,
  and `F 0 = Icc (-1) 1` satisfies all hypotheses of Kakutani's theorem.
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

theorem continuous_maxValue_linU : Continuous (Cslib.Berge.maxValue linΓ linU) := by
  rw [← continuousOn_univ]
  exact Cslib.Berge.continuousOn_maxValue
    (fun _ _ => ⟨0, le_rfl, zero_le_one⟩)
    (fun _ _ => isCompact_Icc)
    UpperHemicontinuousOn.const LowerHemicontinuousOn.const
    (continuous_fst.mul continuous_snd).continuousOn

theorem upperHemicontinuous_argmaxSet_linU :
    UpperHemicontinuousOn (Cslib.Berge.argmaxSet linΓ linU) univ :=
  Cslib.Berge.upperHemicontinuousOn_argmaxSet
    (fun _ _ => ⟨0, le_rfl, zero_le_one⟩)
    (fun _ _ => isCompact_Icc)
    UpperHemicontinuousOn.const LowerHemicontinuousOn.const
    (continuous_fst.mul continuous_snd).continuousOn

/-- Strictly concave quadratic objective `-((y - x) ^ 2)`. -/
def quadU (x y : ℝ) : ℝ := -((y - x) ^ 2)

private theorem quadU_strict_concave_ineq (x y₁ y₂ : ℝ) {a b : ℝ} (hab : a + b = 1) :
    a * quadU x y₁ + b * quadU x y₂ + a * b * (y₁ - y₂) ^ 2 = quadU x (a • y₁ + b • y₂) := by
  have hb : b = 1 - a := by linarith
  subst hb
  dsimp [quadU]
  ring

theorem quadU_strictQuasiconcaveOn (x : ℝ) ⦃y₁ y₂ : ℝ⦄ (_ : y₁ ∈ linΓ x) (_ : y₂ ∈ linΓ x)
    (hne : y₁ ≠ y₂) ⦃a b : ℝ⦄ (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    min (quadU x y₁) (quadU x y₂) < quadU x (a • y₁ + b • y₂) := by
  have hsq : 0 < a * b * (y₁ - y₂) ^ 2 :=
    mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.2 hne))
  have hid := quadU_strict_concave_ineq x y₁ y₂ hab
  have h1 : a * min (quadU x y₁) (quadU x y₂) ≤ a * quadU x y₁ :=
    mul_le_mul_of_nonneg_left (min_le_left _ _) ha.le
  have h2 : b * min (quadU x y₁) (quadU x y₂) ≤ b * quadU x y₂ :=
    mul_le_mul_of_nonneg_left (min_le_right _ _) hb.le
  have hsum : min (quadU x y₁) (quadU x y₂) =
      a * min (quadU x y₁) (quadU x y₂) + b * min (quadU x y₁) (quadU x y₂) := by
    rw [← add_mul, hab, one_mul]
  linarith

theorem quadU_argmaxSet_convex (x : ℝ) : Convex ℝ (Cslib.Berge.argmaxSet linΓ quadU x) := by
  refine Cslib.Berge.convex_argmaxSet (convex_Icc 0 1) fun c y₁ hy₁ y₂ hy₂ a b ha hb hab => ?_
  refine ⟨convex_Icc 0 1 hy₁.1 hy₂.1 ha hb hab, ?_⟩
  have hsq : 0 ≤ a * b * (y₁ - y₂) ^ 2 :=
    mul_nonneg (mul_nonneg ha hb) (sq_nonneg _)
  have hid := quadU_strict_concave_ineq x y₁ y₂ hab
  have h1 : a * c ≤ a * quadU x y₁ := mul_le_mul_of_nonneg_left hy₁.2 ha
  have h2 : b * c ≤ b * quadU x y₂ := mul_le_mul_of_nonneg_left hy₂.2 hb
  have hsum : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
  linarith

theorem quadU_argmaxSet_subsingleton (x : ℝ) : (Cslib.Berge.argmaxSet linΓ quadU x).Subsingleton :=
  Cslib.Berge.subsingleton_argmaxSet_of_strictQuasiconcaveOn (convex_Icc 0 1)
    (quadU_strictQuasiconcaveOn x)

theorem exists_unique_continuous_quadU_argmaxSet :
    ∃ sel : ℝ → ℝ, ContinuousOn sel (Icc 0 1) ∧
      ∀ x ∈ Icc (0 : ℝ) 1, Cslib.Berge.argmaxSet linΓ quadU x = {sel x} :=
  Cslib.Berge.exists_unique_continuousOn_argmaxSet
    (fun _ _ => ⟨0, le_rfl, zero_le_one⟩)
    (fun _ _ => isCompact_Icc)
    (fun _ _ => convex_Icc 0 1)
    UpperHemicontinuousOn.const LowerHemicontinuousOn.const
    (((continuous_snd.sub continuous_fst).pow 2).neg).continuousOn
    fun x _ => quadU_strictQuasiconcaveOn x

end BergeWitness

section KakutaniWitness

theorem exists_isFixedPt_negHalf :
    ∃ x ∈ Icc (-1 : ℝ) 1, Function.IsFixedPt (fun v : ℝ => -v / 2) x := by
  let f : ℝ → ℝ := fun v => -v / 2
  have hf : MapsTo f (Icc (-1 : ℝ) 1) (Icc (-1 : ℝ) 1) := fun x hx =>
    ⟨by dsimp [f]; linarith [hx.2], by dsimp [f]; linarith [hx.1]⟩
  have hc : ContinuousOn f (Icc (-1 : ℝ) 1) := (continuous_neg.div_const 2).continuousOn
  exact Cslib.Brouwer.exists_isFixedPt_of_isCompact_convex
    (nonempty_Icc.mpr (by norm_num)) isCompact_Icc (convex_Icc (-1 : ℝ) 1) hf hc

/-- Classic upper hemicontinuous sign-flipped correspondence on `[-1, 1]`. -/
noncomputable def signFlip (x : ℝ) : Set ℝ :=
  if x < 0 then {1}
  else if 0 < x then {-1}
  else Icc (-1 : ℝ) 1

/-- Non-convex variant at `0` with no fixed point. -/
noncomputable def signFlipNonConvex (x : ℝ) : Set ℝ :=
  if x < 0 then {1}
  else if 0 < x then {-1}
  else {-1, 1}

theorem exists_mem_signFlip : ∃ x ∈ Icc (-1 : ℝ) 1, x ∈ signFlip x := by
  refine Cslib.Kakutani.exists_mem_of_isClosed_graph
    (nonempty_Icc.mpr (by norm_num)) isCompact_Icc (convex_Icc (-1 : ℝ) 1) ?_ ?_ ?_ ?_
  · intro x _
    dsimp [signFlip]
    split_ifs
    · exact ⟨1, rfl⟩
    · exact ⟨-1, rfl⟩
    · exact ⟨0, by norm_num, by norm_num⟩
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
    · exact convex_Icc (-1 : ℝ) 1
  · have hEq : {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ∈ signFlip p.1} =
        {p | (-1 ≤ p.1 ∧ p.1 ≤ 1) ∧ (-1 ≤ p.2 ∧ p.2 ≤ 1) ∧
          p.1 * p.2 ≤ 0 ∧ (p.1 = 0 ∨ |p.2| = 1)} := by
      ext ⟨x, y⟩
      dsimp [signFlip]
      by_cases hx1 : x < 0
      · simp only [hx1, ↓reduceIte, mem_singleton_iff, mem_Icc]
        constructor
        · rintro ⟨hx, rfl⟩
          exact ⟨hx, ⟨by norm_num, by norm_num⟩, by linarith, Or.inr (by norm_num)⟩
        · rintro ⟨hx, _, hmul, _ | h1⟩
          · linarith
          · refine ⟨hx, ?_⟩
            rcases abs_eq zero_le_one |>.mp h1 with hpos | hneg
            · exact hpos
            · exfalso
              have : 0 < x * y := mul_pos_of_neg_of_neg hx1 (by linarith)
              linarith
      · by_cases hx2 : 0 < x
        · simp only [hx1, ↓reduceIte, hx2, mem_singleton_iff, mem_Icc]
          constructor
          · rintro ⟨hx, rfl⟩
            exact ⟨hx, ⟨by norm_num, by norm_num⟩, by linarith, Or.inr (by norm_num)⟩
          · rintro ⟨hx, _, hmul, _ | h1⟩
            · linarith
            · refine ⟨hx, ?_⟩
              rcases abs_eq zero_le_one |>.mp h1 with hpos | hneg
              · exfalso
                have : 0 < x * y := mul_pos hx2 (by linarith)
                linarith
              · exact hneg
        · have hx0 : x = 0 := le_antisymm (not_lt.mp hx2) (not_lt.mp hx1)
          simp only [hx1, ↓reduceIte, hx2, mem_Icc]
          constructor
          · rintro ⟨hx, hy⟩
            exact ⟨hx, hy, by simp [hx0], Or.inl hx0⟩
          · rintro ⟨hx, hy, _⟩
            exact ⟨hx, hy⟩
    rw [hEq]
    refine ((isClosed_Ici.preimage continuous_fst).inter
      (isClosed_Iic.preimage continuous_fst)).inter
      (((isClosed_Ici.preimage continuous_snd).inter (isClosed_Iic.preimage continuous_snd)).inter
        ((isClosed_Iic.preimage (continuous_fst.mul continuous_snd)).inter
          ((isClosed_singleton.preimage continuous_fst).union
            (isClosed_singleton.preimage continuous_snd.abs))))

theorem not_exists_mem_signFlipNonConvex :
    ¬ ∃ x ∈ Icc (-1 : ℝ) 1, x ∈ signFlipNonConvex x := by
  rintro ⟨x, _, hx⟩
  dsimp [signFlipNonConvex] at hx
  split_ifs at hx with h1 h2
  · simp only [mem_singleton_iff] at hx; linarith
  · simp only [mem_singleton_iff] at hx; linarith
  · simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> linarith

end KakutaniWitness

end Cslib.Analysis.BergeKakutaniTests
