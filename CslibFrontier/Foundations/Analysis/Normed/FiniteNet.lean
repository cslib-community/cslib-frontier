/-
Copyright (c) 2021 Sébastien Gouëzel, Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Tactic.Linarith

/-!
# Finite nets for symmetric operator norms

The unit ball in a finite-dimensional real normed space has a `1 / q`-net containing at most
`(2 * q + 1) ^ dim` points. For a symmetric operator, a bound on its quadratic form on a single
net bounds its norm, with approximation factor `1 / (1 - 2 * ε)` for a net of radius `ε < 1/2`.

The packing argument generalizes Mathlib's `Besicovitch.card_le_of_separated` from a ball of
radius two to an arbitrary natural radius. The operator estimate uses Mathlib's characterization
of the norm of a symmetric operator by its Rayleigh quotients.

## Main results

* `NormedSpace.exists_natInverseNet`: a net of radius `1 / q` with `(2 * q + 1) ^ dim` centers.
* `ContinuousLinearMap.opNorm_le_of_quadratic_net`: the quadratic-form net bound.
-/

public section

namespace NormedSpace

open Metric Set MeasureTheory Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

open scoped Function in
private theorem card_le_pow_of_separated (s : Finset E) (q : ℕ)
    (hs : ∀ x ∈ s, ‖x‖ ≤ q)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 1 ≤ ‖x - y‖) :
    s.card ≤ (2 * q + 1) ^ Module.finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  let δ : ℝ := 1 / 2
  let ρ : ℝ := (2 * q + 1) / 2
  have hδ : 0 < δ := by norm_num [δ]
  have hρ : 0 < ρ := by positivity
  let A := ⋃ x ∈ s, ball (x : E) δ
  have hdisj : Set.Pairwise (s : Set E) (Disjoint on fun x => ball (x : E) δ) := by
    intro x hx y hy hxy
    apply ball_disjoint_ball
    simpa only [δ, dist_eq_norm, show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num]
      using hsep x hx y hy hxy
  have hsub : A ⊆ ball (0 : E) ρ := by
    refine iUnion₂_subset fun x hx => ball_subset_ball' ?_
    rw [dist_zero_right]
    dsimp only [δ, ρ]
    linarith [hs x hx]
  have hvol : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) * μ (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) * μ (ball 0 1) = μ A := by
        rw [measure_biUnion_finset hdisj fun x _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) ρ) := measure_mono hsub
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have hcancel : (s.card : ℝ≥0∞) * ENNReal.ofReal (δ ^ finrank ℝ E) ≤
      ENNReal.ofReal (ρ ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos μ 0 zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hvol
  have hreal := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) hcancel
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (pow_nonneg hδ.le _)] at hreal
  have hbound : (s.card : ℝ) / (2 : ℝ) ^ finrank ℝ E ≤
      (2 * q + 1 : ℝ) ^ finrank ℝ E / (2 : ℝ) ^ finrank ℝ E := by
    simpa only [δ, ρ, div_pow, one_pow, mul_one_div] using hreal
  have := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ finrank ℝ E)).1 hbound
  exact_mod_cast this

private theorem card_le_pow_of_inverseSeparated (s : Finset E) (q : ℕ) (hq : 0 < q)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / q ≤ ‖x - y‖) :
    s.card ≤ (2 * q + 1) ^ Module.finrank ℝ E := by
  classical
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  let t := s.image fun x => (q : ℝ) • x
  have hinj : Function.Injective (fun x : E => (q : ℝ) • x) :=
    smul_right_injective E hq'.ne'
  have hcard : t.card = s.card := Finset.card_image_of_injective _ hinj
  rw [← hcard]
  apply card_le_pow_of_separated t q
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hq', mul_one]
      using mul_le_mul_of_nonneg_left (hs y hy) hq'.le
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun h => hxy (congrArg _ h)
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hq']
    simpa only [mul_comm] using (div_le_iff₀ hq').1 (hsep u hu v hv huv)

/-- The unit ball has a net of radius `1 / q` with at most `(2 * q + 1) ^ dim` centers,
all of which belong to the unit ball. -/
theorem exists_natInverseNet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (q : ℕ) (hq : 0 < q) :
    ∃ s : Finset E, s.card ≤ (2 * q + 1) ^ Module.finrank ℝ E ∧
      (∀ x ∈ s, ‖x‖ ≤ 1) ∧ ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 : ℝ) / q := by
  classical
  let P : Finset E → Prop := fun s => (∀ x ∈ s, ‖x‖ ≤ 1) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / q ≤ ‖x - y‖
  let sizes : Set ℕ := {m | ∃ s : Finset E, s.card = m ∧ P s}
  have hne : sizes.Nonempty := ⟨0, ∅, by simp [P]⟩
  have hbd : BddAbove sizes := ⟨(2 * q + 1) ^ Module.finrank ℝ E, by
    rintro m ⟨s, rfl, hs, hsep⟩
    exact card_le_pow_of_inverseSeparated s q hq hs hsep⟩
  obtain ⟨s, hsmax, hs, hsep⟩ := Nat.sSup_mem hne hbd
  refine ⟨s, card_le_pow_of_inverseSeparated s q hq hs hsep, hs, ?_⟩
  intro x hx
  by_contra hnot
  have hfar : ∀ y ∈ s, (1 : ℝ) / q < ‖x - y‖ := by
    simpa only [not_exists, not_and, not_le] using hnot
  have hxs : x ∉ s := by
    intro hxs
    have := hfar x hxs
    simp only [sub_self, norm_zero] at this
    exact (not_lt_of_ge (by positivity : (0 : ℝ) ≤ 1 / q)) this
  have hnew : P (insert x s) := by
    constructor
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact hx
      · exact hs y hy
    · intro y hy z hz hyz
      rcases Finset.mem_insert.mp hy with hyx | hys
      · subst y
        rcases Finset.mem_insert.mp hz with hzx | hzs
        · exact (hyz hzx.symm).elim
        · exact (hfar z hzs).le
      · rcases Finset.mem_insert.mp hz with hzx | hzs
        · subst z
          simpa only [norm_sub_rev] using (hfar y hys).le
        · exact hsep y hys z hzs hyz
  have hbound : (insert x s).card ≤ sSup sizes :=
    le_csSup hbd ⟨insert x s, rfl, hnew⟩
  rw [Finset.card_insert_of_notMem hxs, ← hsmax] at hbound
  omega

end NormedSpace

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quadratic form on an `ε`-net of the unit ball bounds the norm of a symmetric operator,
with approximation factor `1 / (1 - 2 * ε)`. -/
theorem opNorm_le_of_quadratic_net (T : E →L[ℝ] E) (hT : T.IsSymmetric) (s : Finset E)
    {ε C : ℝ} (hε : 0 ≤ ε) (hε' : ε < 1 / 2) (hC : 0 ≤ C)
    (hs : ∀ y ∈ s, ‖y‖ ≤ 1)
    (hnet : ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ s, ‖x - y‖ ≤ ε)
    (hbound : ∀ y ∈ s, |inner ℝ (T y) y| ≤ C) : ‖T‖ ≤ C / (1 - 2 * ε) := by
  have hstep : ‖T‖ ≤ C + 2 * ε * ‖T‖ := by
    conv_lhs => rw [T.norm_eq_iSup_rayleighQuotient hT]
    apply ciSup_le
    intro x
    by_cases hx : x = 0
    · simp only [hx, rayleighQuotient_apply_zero, abs_zero]
      positivity
    let u := ‖x‖⁻¹ • x
    have hu : ‖u‖ = 1 := norm_smul_inv_norm hx
    have hq : T.rayleighQuotient u = T.rayleighQuotient x :=
      T.rayleigh_smul x (inv_ne_zero (norm_ne_zero_iff.mpr hx))
    rw [← hq]
    simp only [rayleighQuotient, reApplyInnerSelf_apply, RCLike.re_to_real, hu, one_pow, div_one]
    obtain ⟨y, hy, huy⟩ := hnet u hu.le
    have hTu : ‖T (u - y)‖ ≤ ‖T‖ * ε :=
      (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left huy (norm_nonneg T))
    have hTy : ‖T y‖ ≤ ‖T‖ := by
      simpa only [mul_one] using
        (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hs y hy) (norm_nonneg T))
    have hd : |inner ℝ (T u) u - inner ℝ (T y) y| ≤ 2 * ε * ‖T‖ := by
      calc
        |inner ℝ (T u) u - inner ℝ (T y) y| =
            |inner ℝ (T (u - y)) u + inner ℝ (T y) (u - y)| := by
          rw [map_sub, inner_sub_left, inner_sub_right]
          congr 1
          ring
        _ ≤ |inner ℝ (T (u - y)) u| + |inner ℝ (T y) (u - y)| := abs_add_le _ _
        _ ≤ ‖T (u - y)‖ * ‖u‖ + ‖T y‖ * ‖u - y‖ :=
          add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
        _ ≤ ‖T‖ * ε * 1 + ‖T‖ * ε := by gcongr; exact hu.le
        _ = 2 * ε * ‖T‖ := by ring
    calc
      |inner ℝ (T u) u| =
          |inner ℝ (T y) y + (inner ℝ (T u) u - inner ℝ (T y) y)| := by congr 1; ring
      _ ≤ |inner ℝ (T y) y| + |inner ℝ (T u) u - inner ℝ (T y) y| := abs_add_le _ _
      _ ≤ C + 2 * ε * ‖T‖ := add_le_add (hbound y hy) hd
  apply (le_div_iff₀ (by linarith : 0 < 1 - 2 * ε)).2
  nlinarith

end ContinuousLinearMap
