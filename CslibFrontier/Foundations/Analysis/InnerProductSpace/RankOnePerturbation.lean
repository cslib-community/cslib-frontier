/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate (Mathlib, next to Analysis/InnerProductSpace/Spectrum)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.TracePower
import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Power growth and approximation of a rank-one direction

A symmetric operator with a direction of sufficiently large squared growth has a basis vector
whose orbit exhibits large growth within `dim E + 1` steps. The argument compares the lower
spectral bound on the trace of an even power with an upper bound from every basis-vector orbit.
The candidate is recognized by comparing squared norms, so finding it does not require computing
an eigenvector or a quotient.

The geometric estimate compares a unit vector close to a line with one of the two unit vectors
on that line. Together these statements support integer matrix-power recovery algorithms.

## Main results

* `LinearMap.IsSymmetric.exists_power_growth`: a finite search finds a nonzero growing iterate.
* `exists_sign_norm_sub_sq_le`: unit-vector approximation from approximation by a scalar multiple.
* `exists_sign_normalize_sub_sq_le_of_growth`: a growing vector with a small rank-one residual
  approximates the planted direction, up to sign.

These are elementary auxiliary estimates, proved here for the planted-clique algorithm.
-/

public section

open Finset Module
open scoped RealInnerProductSpace

namespace LinearMap

variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι]

/-- The trace of an even power of a symmetric operator is the sum of the squared norms of its
half-power on any orthonormal basis. -/
theorem IsSymmetric.trace_sq_pow_eq_sum_norm_sq {T : E →ₗ[ℝ] E}
    (hT : T.IsSymmetric) (b : OrthonormalBasis ι ℝ E) (t : ℕ) :
    trace ℝ E ((T ^ 2) ^ t) = ∑ i, ‖(T ^ t) (b i)‖ ^ 2 := by
  have hp : (T ^ 2) ^ t = T ^ t * T ^ t := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [hp, trace_eq_sum_inner _ b]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_apply_eq_comp, ← hT.pow t, real_inner_self_eq_norm_sq]

/-- If a symmetric operator has squared growth at least `2 c` in some unit direction, then
some orthonormal-basis vector has a nonzero iterate whose squared growth is at least `c`,
within the first `card ι + 1` steps. The criterion uses multiplication only. -/
theorem IsSymmetric.exists_power_growth [FiniteDimensional ℝ E]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric)
    (b : OrthonormalBasis ι ℝ E) {v : E} (hv : ‖v‖ = 1) {c : ℝ} (hc : 0 < c)
    (hgain : 2 * c ≤ ‖T v‖ ^ 2) :
    ∃ i : ι, ∃ s < Fintype.card ι + 1,
      (T ^ (s + 1)) (b i) ≠ 0 ∧
        c * ‖(T ^ s) (b i)‖ ^ 2 ≤ ‖(T ^ (s + 1)) (b i)‖ ^ 2 := by
  classical
  by_contra! hnone
  have hstep (i : ι) {s : ℕ} (hs : s < Fintype.card ι + 1) :
      ‖(T ^ (s + 1)) (b i)‖ ^ 2 ≤ c * ‖(T ^ s) (b i)‖ ^ 2 := by
    by_cases hz : (T ^ (s + 1)) (b i) = 0
    · simp only [hz, norm_zero, zero_pow (by omega : 2 ≠ 0)]
      positivity
    · exact (hnone i s hs hz).le
  have hbound (s : ℕ) (hs : s ≤ Fintype.card ι + 1) (i : ι) :
      ‖(T ^ s) (b i)‖ ^ 2 ≤ c ^ s := by
    induction s with
    | zero => simp [b.norm_eq_one]
    | succ s ih =>
      calc ‖(T ^ (s + 1)) (b i)‖ ^ 2 ≤ c * ‖(T ^ s) (b i)‖ ^ 2 :=
            hstep i (by omega)
        _ ≤ c * c ^ s := mul_le_mul_of_nonneg_left (ih (by omega)) hc.le
        _ = c ^ (s + 1) := (pow_succ' c s).symm
  have hpositive : (T ^ 2).IsPositive := by
    simpa only [hT.adjoint_eq, ← Module.End.mul_eq_comp, pow_two] using
      isPositive_adjoint_comp_self T
  have hquadratic : 2 * c ≤ inner ℝ v ((T ^ 2) v) := by
    rw [pow_two, mul_apply_eq_comp, ← hT, real_inner_self_eq_norm_sq]
    exact hgain
  have hlower := hpositive.pow_le_re_trace_pow hv (by positivity : 0 ≤ 2 * c)
    hquadratic (Fintype.card ι + 1)
  simp only [RCLike.re_to_real, hT.trace_sq_pow_eq_sum_norm_sq b] at hlower
  have hupper : (∑ i, ‖(T ^ (Fintype.card ι + 1)) (b i)‖ ^ 2) ≤
      (Fintype.card ι : ℝ) * c ^ (Fintype.card ι + 1) := by
    calc (∑ i, ‖(T ^ (Fintype.card ι + 1)) (b i)‖ ^ 2)
        ≤ ∑ _i : ι, c ^ (Fintype.card ι + 1) :=
          sum_le_sum fun i _ => hbound _ le_rfl i
      _ = _ := by simp
  have hp : (2 : ℝ) ^ (Fintype.card ι + 1) ≤ Fintype.card ι := by
    apply le_of_mul_le_mul_right _ (pow_pos hc (Fintype.card ι + 1))
    simpa only [mul_pow] using hlower.trans hupper
  have hnat : Fintype.card ι < 2 ^ (Fintype.card ι + 1) :=
    (Nat.lt_succ_self _).trans Nat.lt_two_pow_self
  have : (Fintype.card ι : ℝ) < (2 : ℝ) ^ (Fintype.card ι + 1) := by exact_mod_cast hnat
  exact this.not_ge hp

end LinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A unit vector approximated by any scalar multiple of a unit vector is approximated,
up to twice the squared error, by one of its two unit directions. -/
theorem exists_sign_norm_sub_sq_le {x v : E} (hx : ‖x‖ = 1) (hv : ‖v‖ = 1) (a : ℝ) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ‖x - s • v‖ ^ 2 ≤ 2 * ‖x - a • v‖ ^ 2 := by
  have habs : |inner ℝ x v| ≤ 1 := by
    simpa only [hx, hv, one_mul] using abs_real_inner_le_norm x v
  have hform (b : ℝ) : ‖x - b • v‖ ^ 2 = 1 + b ^ 2 - 2 * b * inner ℝ x v := by
    rw [norm_sub_sq_real, hx, norm_smul, Real.norm_eq_abs, hv, mul_one,
      sq_abs, inner_smul_right]
    ring
  rcases le_or_gt 0 (inner ℝ x v) with h | h
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [hform, hform]
    have hle := (abs_le.mp habs).2
    nlinarith [sq_nonneg (a - inner ℝ x v), mul_nonneg h (sub_nonneg.mpr hle)]
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [hform, hform]
    have hle := (abs_le.mp habs).1
    nlinarith [sq_nonneg (a - inner ℝ x v), mul_nonneg (neg_nonneg.mpr h.le)
      (by linarith : 0 ≤ 1 + inner ℝ x v)]

/-- Relative error from a line gives an absolute error from one of its unit directions after
normalization. -/
theorem exists_sign_normalize_sub_sq_le_of_relative_error {z v : E}
    (hv : ‖v‖ = 1) (hz : z ≠ 0) {a ε : ℝ} (hε : 0 ≤ ε)
    (herror : ‖z - a • v‖ ≤ ε * ‖z‖) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖‖z‖⁻¹ • z - s • v‖ ^ 2 ≤ 2 * ε ^ 2 := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnormalized : ‖‖z‖⁻¹ • z - (‖z‖⁻¹ * a) • v‖ ≤ ε := by
    rw [mul_smul, ← smul_sub, norm_smul_of_nonneg (inv_nonneg.mpr hz'.le)]
    calc ‖z‖⁻¹ * ‖z - a • v‖ ≤ ‖z‖⁻¹ * (ε * ‖z‖) :=
          mul_le_mul_of_nonneg_left herror (inv_nonneg.mpr hz'.le)
      _ = ε := by rw [mul_left_comm, inv_mul_cancel₀ hz'.ne', mul_one]
  obtain ⟨s, hs, hdist⟩ :=
    exists_sign_norm_sub_sq_le (norm_smul_inv_norm (𝕜 := ℝ) hz) hv (‖z‖⁻¹ * a)
  refine ⟨s, hs, hdist.trans ?_⟩
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hε).mpr hnormalized)
    (by norm_num)

/-- A vector with squared growth at least `k² / 4` and rank-one residual at most `k / 16`
times the input norm has normalized squared distance at most `1 / 32` from one of the two
unit directions of the rank-one part. -/
theorem exists_sign_normalize_sub_sq_le_of_growth {y z v : E}
    (hv : ‖v‖ = 1) (hz : z ≠ 0) {a k : ℝ} (hk : 0 < k)
    (herror : ‖z - a • v‖ ≤ k / 16 * ‖y‖)
    (hgain : k ^ 2 * ‖y‖ ^ 2 ≤ 4 * ‖z‖ ^ 2) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      ‖‖z‖⁻¹ • z - s • v‖ ^ 2 ≤ 1 / 32 := by
  have hnormgain : k * ‖y‖ ≤ 2 * ‖z‖ := by
    apply (sq_le_sq₀ (mul_nonneg hk.le (norm_nonneg _)) (by positivity)).mp
    nlinarith [hgain]
  have hrelative : ‖z - a • v‖ ≤ (1 / 8 : ℝ) * ‖z‖ := by
    nlinarith [herror]
  obtain ⟨s, hs, hdist⟩ :=
    exists_sign_normalize_sub_sq_le_of_relative_error hv hz (by norm_num) hrelative
  exact ⟨s, hs, by norm_num at hdist ⊢; exact hdist⟩

namespace LinearMap

/-- A perturbation of size at most `k / 16` of a unit rank-one signal has enough growth in the
signal direction for `IsSymmetric.exists_power_growth` with threshold `k² / 4`. -/
theorem half_sq_le_norm_apply_sq {T : E →ₗ[ℝ] E} {v : E} (hv : ‖v‖ = 1)
    {k : ℝ} (hk : 0 < k) (herror : ‖T v - k • v‖ ≤ k / 16) :
    2 * (k ^ 2 / 4) ≤ ‖T v‖ ^ 2 := by
  have hnorm : k ≤ ‖T v - k • v‖ + ‖T v‖ := by
    calc k = ‖k • v‖ := by rw [norm_smul_of_nonneg hk.le, hv, mul_one]
      _ ≤ ‖k • v - T v‖ + ‖T v‖ := norm_le_norm_sub_add _ _
      _ = ‖T v - k • v‖ + ‖T v‖ := by rw [norm_sub_rev]
  have hbound : 15 * k ≤ 16 * ‖T v‖ := by linarith
  have hsquared : (15 * k) ^ 2 ≤ (16 * ‖T v‖) ^ 2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hbound
  nlinarith [sq_nonneg k]

/-- A symmetric operator approximating scalar multiplication by `k` in some unit direction
admits a nonzero basis-vector iterate with squared growth at least `k² / 4`. -/
theorem IsSymmetric.exists_power_growth_of_sub_smul_le [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι]
    {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) (b : OrthonormalBasis ι ℝ E)
    {v : E} (hv : ‖v‖ = 1) {k : ℝ} (hk : 0 < k)
    (herror : ‖T v - k • v‖ ≤ k / 16) :
    ∃ i : ι, ∃ s < Fintype.card ι + 1,
      (T ^ (s + 1)) (b i) ≠ 0 ∧
        k ^ 2 * ‖(T ^ s) (b i)‖ ^ 2 ≤ 4 * ‖(T ^ (s + 1)) (b i)‖ ^ 2 := by
  obtain ⟨i, s, hs, hz, hgrowth⟩ := hT.exists_power_growth b hv
    (by positivity : 0 < k ^ 2 / 4) (half_sq_le_norm_apply_sq hv hk herror)
  exact ⟨i, s, hs, hz, by nlinarith [hgrowth]⟩

end LinearMap
