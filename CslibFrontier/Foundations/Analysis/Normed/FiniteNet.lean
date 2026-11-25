/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Tactic.Linarith

/-!
# Finite nets for operator norms

The unit ball in a finite-dimensional real normed space has a `1/2`-net containing at most
`5 ^ dim` points. Applying the net approximation first to a linear functional and then to an
operator bounds the operator norm by four times its largest bilinear form on two copies of the
net. The planted-clique random-matrix estimate uses this finite reduction.

## Main results

* `NormedSpace.exists_halfNet`: a half-net in the unit ball with at most `5 ^ dim` points.
* `ContinuousLinearMap.opNorm_le_four_mul_of_halfNet`: the two-net bound for an operator.
-/

public section

namespace NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]

private theorem card_le_five_pow_of_halfSeparated (s : Finset E)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 2 ≤ ‖x - y‖) :
    s.card ≤ 5 ^ Module.finrank ℝ E := by
  classical
  let t := s.image fun x => (2 : ℝ) • x
  have hinj : Function.Injective (fun x : E => (2 : ℝ) • x) :=
    smul_right_injective E (by norm_num : (2 : ℝ) ≠ 0)
  have hcard : t.card = s.card := Finset.card_image_of_injective _ hinj
  rw [← hcard]
  apply Besicovitch.card_le_of_separated
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_one]
      using mul_le_mul_of_nonneg_left (hs y hy) (by norm_num : (0 : ℝ) ≤ 2)
  · intro x hx y hy hxy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
    have huv : u ≠ v := fun h => hxy (congrArg _ h)
    have h := hsep u hu v hv huv
    rw [← smul_sub, norm_smul]
    norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

/-- The unit ball has a half-net of cardinality at most `5 ^ dim`, with all centers in the ball. -/
theorem exists_halfNet (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ s : Finset E, s.card ≤ 5 ^ Module.finrank ℝ E ∧
      (∀ x ∈ s, ‖x‖ ≤ 1) ∧ ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 : ℝ) / 2 := by
  classical
  let P : Finset E → Prop := fun s => (∀ x ∈ s, ‖x‖ ≤ 1) ∧
    ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1 : ℝ) / 2 ≤ ‖x - y‖
  let sizes : Set ℕ := {m | ∃ s : Finset E, s.card = m ∧ P s}
  have hne : sizes.Nonempty := ⟨0, ∅, by simp [P]⟩
  have hbd : BddAbove sizes := ⟨5 ^ Module.finrank ℝ E, by
    rintro m ⟨s, rfl, hs, hsep⟩
    exact card_le_five_pow_of_halfSeparated s hs hsep⟩
  obtain ⟨s, hsmax, hs, hsep⟩ := Nat.sSup_mem hne hbd
  refine ⟨s, card_le_five_pow_of_halfSeparated s hs hsep, hs, ?_⟩
  intro x hx
  by_contra hnot
  have hfar : ∀ y ∈ s, (1 : ℝ) / 2 < ‖x - y‖ := by
    simpa only [not_exists, not_and, not_le] using hnot
  have hxs : x ∉ s := by
    intro hxs
    have := hfar x hxs
    simp only [sub_self, norm_zero] at this
    linarith
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

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A half-net controls the norm of a linear map with a factor of two. -/
theorem opNorm_le_two_mul_of_halfNet (T : E →L[ℝ] F) (s : Finset E)
    (hs : ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 : ℝ) / 2)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ y ∈ s, ‖T y‖ ≤ C) : ‖T‖ ≤ 2 * C := by
  have hstep : ‖T‖ ≤ C + ‖T‖ / 2 := by
    apply opNorm_le_of_unit_norm (by positivity)
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hs x hx.le
    calc
      ‖T x‖ = ‖T y + T (x - y)‖ := by rw [← map_add]; congr 1; abel_nf
      _ ≤ ‖T y‖ + ‖T (x - y)‖ := norm_add_le _ _
      _ ≤ C + ‖T‖ * ‖x - y‖ := add_le_add (hbound y hy) (T.le_opNorm _)
      _ ≤ C + ‖T‖ / 2 := by nlinarith [norm_nonneg T]
  linarith

/-- Two half-nets control every bilinear form of an operator, with a factor of four. -/
theorem opNorm_le_four_mul_of_halfNet {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] (T : E →L[ℝ] F) (s : Finset E) (t : Finset F)
    (hs : ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ s, ‖x - y‖ ≤ (1 : ℝ) / 2)
    (ht : ∀ x, ‖x‖ ≤ 1 → ∃ y ∈ t, ‖x - y‖ ≤ (1 : ℝ) / 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x ∈ s, ∀ y ∈ t, |inner ℝ (T x) y| ≤ C) : ‖T‖ ≤ 4 * C := by
  have hx : ∀ x ∈ s, ‖T x‖ ≤ 2 * C := by
    intro x hx
    simpa only [innerSL_apply_norm] using
      opNorm_le_two_mul_of_halfNet (innerSL ℝ (T x)) t ht hC (fun y hy => by
        simpa only [innerSL_apply_apply, Real.norm_eq_abs] using hbound x hx y hy)
  have := opNorm_le_two_mul_of_halfNet T s hs (by positivity : 0 ≤ 2 * C) hx
  linarith

end ContinuousLinearMap
