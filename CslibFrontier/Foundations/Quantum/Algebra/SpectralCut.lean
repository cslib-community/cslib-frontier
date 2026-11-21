/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.SpectralCut
public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
import CslibFrontier.Foundations.Quantum.Algebra.Consistency
import Mathlib.Analysis.Matrix.Order

/-!
# Measurement estimates for spectral cuts

For a measurement written in an eigenbasis of a density matrix, agreement with its transpose
in the corresponding Schmidt state weights each squared matrix entry by the geometric mean
of the two eigenvalues. The agreement deficit bounds the average commutator with the cuts.
The bound is independent of the outcome count and matrix dimension. It is an intermediate step
toward [Vidick, Theorem 3.1][Vidick2022].
-/

public section

open Matrix
open scoped MatrixOrder ComplexOrder

namespace Cslib.Quantum.Measurement

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- Effects are Hermitian, so exchanging the row and column preserves an entry's norm. -/
theorem norm_effect_entry_swap (M : Measurement α (Matrix ι ι ℂ)) (a : α) (i j : ι) :
    ‖M.effect a i j‖ = ‖M.effect a j i‖ := by
  rw [← (Matrix.nonneg_iff_posSemidef.mp (M.nonneg a)).isHermitian.apply i j, norm_star]

open scoped Matrix.Norms.L2Operator in
/-- The squared row mass of a measurement, summed over outcomes, is at most one. -/
theorem sum_norm_effect_row_sq_le_one (M : Measurement α (Matrix ι ι ℂ)) (i : ι) :
    ∑ a, ∑ j, ‖M.effect a i j‖ ^ 2 ≤ 1 := by
  have hentry (a : α) :
      ((M.effect a * M.effect a) i i).re = ∑ j, ‖M.effect a i j‖ ^ 2 := by
    have he := (Matrix.nonneg_iff_posSemidef.mp (M.nonneg a)).isHermitian.isSelfAdjoint
    simpa only [he.star_eq, M.norm_effect_entry_swap a _ i] using
      Matrix.re_star_mul_self_diag (M.effect a) i
  calc
    _ = ∑ a, ((M.effect a * M.effect a) i i).re := by simp only [hentry]
    _ ≤ ∑ a, (M.effect a i i).re := by
      refine Finset.sum_le_sum fun a _ => ?_
      have h := Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (M.effect_mul_self_le a))
      have hi := (Complex.nonneg_iff.mp (h.diag_nonneg (i := i))).1
      change 0 ≤ (M.effect a i i - (M.effect a * M.effect a) i i).re at hi
      exact sub_nonneg.mp (by simpa only [Complex.sub_re] using hi)
    _ = 1 := by
      rw [← Complex.re_sum, ← Matrix.sum_apply, M.sum_effect, Matrix.one_apply_eq, Complex.one_re]

open scoped Matrix.Norms.Frobenius in
/-- The normalized spectral cut bound for a measurement in a Schmidt basis. -/
theorem sum_diagonalCutWidth_norm_commutator_sq_le (M : Measurement α (Matrix ι ι ℂ))
    (d : ι → ℝ) (hd : ∀ i, 0 ≤ d i) (htrace : ∑ i, d i = 1) (δ : ℝ)
    (hagree : 1 - δ ≤ ∑ i, ∑ j, (Real.sqrt (d i) * Real.sqrt (d j)) *
      ∑ a, ‖M.effect a i j‖ ^ 2) :
    let P := fun s : Finset ι => diagonal fun i => if i ∈ s then (1 : ℂ) else 0
    (∑ s : {s : Finset ι // s.Nonempty}, diagonalCutWidth d s *
        ∑ a, ‖M.effect a * P s.val - P s.val * M.effect a‖ ^ 2) ≤
      2 * Real.sqrt (2 * δ) := by
  have hrow (i : ι) : ∑ j, ∑ a, ‖M.effect a i j‖ ^ 2 ≤ 1 := by
    rw [Finset.sum_comm]
    exact M.sum_norm_effect_row_sq_le_one i
  have hcol (j : ι) : ∑ i, ∑ a, ‖M.effect a i j‖ ^ 2 ≤ 1 := by
    simpa only [M.norm_effect_entry_swap _ j _] using hrow j
  have h := Matrix.sum_diagonalCutWidth_norm_commutator_sq_le_of_agreement d hd (fun _ => 1)
    (fun _ => zero_le_one) M.effect δ
  simp only [one_mul, htrace] at h
  have hbound := h hrow hcol hagree
  have hsqrt : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [mul_one, hsqrt, mul_comm] at hbound
  exact hbound

/-- Compress the effects to the coordinates of an embedded basis. The effects still sum
to the identity on that smaller space. -/
def principalSubmatrix {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Measurement α (Matrix ι ι ℂ)) (e : κ ↪ ι) : Measurement α (Matrix κ κ ℂ) where
  effect a := (M.effect a).submatrix e e
  nonneg a :=
    Matrix.nonneg_iff_posSemidef.mpr ((Matrix.nonneg_iff_posSemidef.mp (M.nonneg a)).submatrix e)
  sum_effect := by
    ext i j
    rw [Matrix.sum_apply]
    simp only [Matrix.submatrix_apply]
    have he := congrArg (fun A : Matrix ι ι ℂ => A (e i) (e j)) M.sum_effect
    simp only [Matrix.sum_apply, Matrix.one_apply, e.injective.eq_iff] at he ⊢
    exact he

@[simp] theorem principalSubmatrix_effect_apply {κ : Type*} [Fintype κ] [DecidableEq κ]
    (M : Measurement α (Matrix ι ι ℂ)) (e : κ ↪ ι) (a : α) (i j : κ) :
    (M.principalSubmatrix e).effect a i j = M.effect a (e i) (e j) := by
  unfold principalSubmatrix
  rfl

end Cslib.Quantum.Measurement

namespace Cslib.Quantum.AlgState

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The state of the normalized trace on a nonempty finite matrix algebra. -/
noncomputable def normalizedMatrixTrace : AlgState (Matrix ι ι ℂ) where
  toFun A := (Fintype.card ι : ℂ)⁻¹ * Matrix.trace A
  map_add' A B := by rw [Matrix.trace_add, mul_add]
  map_smul' c A := by
    rw [Matrix.trace_smul, smul_eq_mul, smul_eq_mul, RingHom.id_apply, mul_left_comm]
  monotone' A B h := by
    have hn : 0 ≤ (Fintype.card ι : ℂ)⁻¹ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv]
      exact Complex.zero_le_real.mpr (by positivity)
    apply sub_nonneg.mp
    rw [← mul_sub, ← Matrix.trace_sub]
    exact mul_nonneg hn ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)).trace_nonneg)
  map_one' := by
    have hcard : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [Matrix.trace_one, inv_mul_cancel₀ hcard]

theorem normalizedMatrixTrace_apply (A : Matrix ι ι ℂ) :
    (normalizedMatrixTrace : AlgState (Matrix ι ι ℂ)) A =
      (Fintype.card ι : ℂ)⁻¹ * Matrix.trace A := by
  unfold normalizedMatrixTrace
  rfl

open scoped Matrix.Norms.Frobenius in
/-- The normalized trace's squared state seminorm is the squared Frobenius norm
divided by the dimension. -/
theorem norm_sq_normalizedMatrixTrace (A : Matrix ι ι ℂ) :
    (normalizedMatrixTrace : AlgState (Matrix ι ι ℂ)).norm A ^ 2 =
      ‖A‖ ^ 2 / (Fintype.card ι : ℝ) := by
  have htrace : (Matrix.trace (star A * A)).re = ‖A‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Complex.re_sum, Matrix.re_star_mul_self_diag,
      Matrix.frobenius_norm_sq_eq_sum]
    rw [Finset.sum_comm]
  rw [AlgState.norm_sq, normalizedMatrixTrace_apply, ← Complex.ofReal_natCast,
    ← Complex.ofReal_inv, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    htrace, mul_comm, ← div_eq_mul_inv]

end Cslib.Quantum.AlgState
