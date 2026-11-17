/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate (Mathlib, quantitative power iteration)

public import CslibFrontier.Foundations.Analysis.InnerProductSpace.RankOnePerturbation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quantitative power iteration from all basis columns

Apply a power of a real operator to each vector of an orthonormal seed basis, and choose a
column of maximal squared norm. If an orthonormal eigenbasis has one positive eigenvalue
`α` and all other eigenvalues have magnitude at most `β`, the selected column is nonzero.
Its normalized direction has squared distance at most `2 dim(E) (β / α)^(2 t)` from one
orientation of the selected eigenvector.

The supplied eigenbasis need not order the eigenvalues. In particular, this estimate applies
to polynomial spectral filters using the original operator's eigenbasis.

## Main results

* `OrthonormalBasis.exists_sign_normalize_pow_column_sub_sq_le`: quantitative approximation
  from a column of maximal squared norm, with no assumption on a chosen seed's overlap.
-/

public section

open Finset
open scoped RealInnerProductSpace

namespace OrthonormalBasis

variable {E ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

private theorem repr_apply_of_eigenvectors (b : OrthonormalBasis ι ℝ E)
    (T : E →ₗ[ℝ] E) (μ : ι → ℝ) (heigen : ∀ i, T (b i) = μ i • b i)
    (x : E) (i : ι) : b.repr (T x) i = μ i * b.repr x i := by
  classical
  conv_lhs => rw [← b.sum_repr x]
  simp [map_sum, map_smul, heigen, smul_smul, b.repr_self,
    Pi.single_apply, mul_comm]

private theorem repr_pow_apply_of_eigenvectors (b : OrthonormalBasis ι ℝ E)
    (T : E →ₗ[ℝ] E) (μ : ι → ℝ) (heigen : ∀ i, T (b i) = μ i • b i)
    (t : ℕ) (x : E) (i : ι) : b.repr ((T ^ t) x) i = μ i ^ t * b.repr x i := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ', mul_apply_eq_comp,
      repr_apply_of_eigenvectors b T μ heigen, ih, pow_succ']
    ring

private theorem pow_sub_projection_sq_le (b : OrthonormalBasis ι ℝ E)
    (T : E →ₗ[ℝ] E) (μ : ι → ℝ) (heigen : ∀ i, T (b i) = μ i • b i)
    (j : ι) {β : ℝ} (hβ : 0 ≤ β) (hbound : ∀ i, i ≠ j → |μ i| ≤ β)
    (t : ℕ) (x : E) :
    ‖(T ^ t) x - b.repr ((T ^ t) x) j • b j‖ ^ 2 ≤ (β ^ t) ^ 2 * ‖x‖ ^ 2 := by
  classical
  rw [← b.sum_sq_inner_right, ← b.sum_sq_inner_right x, Finset.mul_sum]
  simp only [← b.repr_apply_apply]
  apply Finset.sum_le_sum
  intro i _
  simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply,
    b.repr_self, PiLp.single_apply, smul_eq_mul]
  simp only [repr_pow_apply_of_eigenvectors b T μ heigen]
  by_cases hij : i = j
  · subst i
    simp only [ite_true, mul_one, sub_self, zero_pow (by omega : 2 ≠ 0)]
    positivity
  · simp only [hij, ite_false, mul_zero, sub_zero]
    have hp : |μ i ^ t| ≤ β ^ t := by
      simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg (μ i)) (hbound i hij) t
    have hs : (μ i ^ t) ^ 2 ≤ (β ^ t) ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (μ i ^ t)) (pow_nonneg hβ t)).mpr hp
      simpa only [sq_abs] using h
    simpa only [mul_pow] using mul_le_mul_of_nonneg_right hs (sq_nonneg (b.repr x i))

/-- A maximal power column approximates an isolated eigenvector without a supplied seed-overlap
assumption. The estimate is informative when `β < μ j`; no contraction assumption is needed
for the inequality itself. -/
theorem exists_sign_normalize_pow_column_sub_sq_le (b : OrthonormalBasis ι ℝ E)
    (T : E →ₗ[ℝ] E) (μ : ι → ℝ) (heigen : ∀ i, T (b i) = μ i • b i)
    (c : OrthonormalBasis κ ℝ E) (j : ι) (hμ : 0 < μ j)
    {β : ℝ} (hβ : 0 ≤ β) (hbound : ∀ i, i ≠ j → |μ i| ≤ β)
    (t : ℕ) (k : κ)
    (hmax : ∀ l, ‖(T ^ t) (c l)‖ ^ 2 ≤ ‖(T ^ t) (c k)‖ ^ 2) :
    (T ^ t) (c k) ≠ 0 ∧
      ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
        ‖‖(T ^ t) (c k)‖⁻¹ • (T ^ t) (c k) - s • b j‖ ^ 2 ≤
          2 * (Fintype.card κ : ℝ) * (β / μ j) ^ (2 * t) := by
  classical
  let z := (T ^ t) (c k)
  have hproj (l : κ) :
      (μ j ^ t) ^ 2 * (b.repr (c l) j) ^ 2 ≤ ‖(T ^ t) (c l)‖ ^ 2 := by
    have hi := abs_real_inner_le_norm (b j) ((T ^ t) (c l))
    rw [b.norm_eq_one, one_mul] at hi
    have hs := (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr hi
    rw [sq_abs, ← b.repr_apply_apply, repr_pow_apply_of_eigenvectors b T μ heigen,
      mul_pow] at hs
    exact hs
  have hsum : ∑ l : κ, (b.repr (c l) j) ^ 2 = 1 := by
    simp only [b.repr_apply_apply]
    rw [c.sum_sq_inner_left, b.norm_eq_one, one_pow]
  have hlower : (μ j ^ t) ^ 2 ≤ (Fintype.card κ : ℝ) * ‖z‖ ^ 2 := by
    calc
      (μ j ^ t) ^ 2 = (μ j ^ t) ^ 2 * ∑ l : κ, (b.repr (c l) j) ^ 2 := by
        rw [hsum, mul_one]
      _ = ∑ l : κ, (μ j ^ t) ^ 2 * (b.repr (c l) j) ^ 2 := Finset.mul_sum _ _ _
      _ ≤ ∑ l : κ, ‖(T ^ t) (c l)‖ ^ 2 := Finset.sum_le_sum fun l _ => hproj l
      _ ≤ ∑ _l : κ, ‖z‖ ^ 2 := Finset.sum_le_sum fun l _ => hmax l
      _ = _ := by simp
  have hz : z ≠ 0 := by
    intro heq
    have hp : 0 < (μ j ^ t) ^ 2 := sq_pos_of_pos (pow_pos hμ t)
    rw [heq, norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero] at hlower
    exact (not_le_of_gt hp) hlower
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have herror : ‖z - b.repr z j • b j‖ ^ 2 ≤ (β ^ t) ^ 2 := by
    simpa only [c.norm_eq_one, one_pow, mul_one] using
      pow_sub_projection_sq_le b T μ heigen j hβ hbound t (c k)
  have hrelative :
      ‖‖z‖⁻¹ • z - (‖z‖⁻¹ * b.repr z j) • b j‖ ^ 2 ≤
        (Fintype.card κ : ℝ) * (β / μ j) ^ (2 * t) := by
    rw [mul_smul, ← smul_sub, norm_smul_of_nonneg (inv_nonneg.mpr hzpos.le), mul_pow]
    have hinv : ‖z‖⁻¹ ^ 2 ≤ (Fintype.card κ : ℝ) / (μ j ^ t) ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos (pow_pos hμ t))).mpr
      calc
        ‖z‖⁻¹ ^ 2 * (μ j ^ t) ^ 2 ≤
            ‖z‖⁻¹ ^ 2 * ((Fintype.card κ : ℝ) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hlower (sq_nonneg _)
        _ = Fintype.card κ := by field_simp
    calc
      ‖z‖⁻¹ ^ 2 * ‖z - b.repr z j • b j‖ ^ 2 ≤
          ((Fintype.card κ : ℝ) / (μ j ^ t) ^ 2) * (β ^ t) ^ 2 :=
        mul_le_mul hinv herror (sq_nonneg _) (by positivity)
      _ = _ := by rw [div_pow, pow_mul, mul_comm 2 t]; ring
  obtain ⟨s, hs, hdist⟩ := exists_sign_norm_sub_sq_le
    (norm_smul_inv_norm (𝕜 := ℝ) hz) (b.norm_eq_one j) (‖z‖⁻¹ * b.repr z j)
  refine ⟨hz, s, hs, hdist.trans ?_⟩
  exact (mul_le_mul_of_nonneg_left hrelative (by norm_num)).trans_eq (by ring)

end OrthonormalBasis
