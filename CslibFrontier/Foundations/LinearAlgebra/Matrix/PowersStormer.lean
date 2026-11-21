/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, a matrix trace inequality)

public import CslibFrontier.Foundations.LinearAlgebra.Matrix.PolarDecomposition
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The Powers–Størmer inequality

The Powers–Størmer inequality [Powers and Størmer][PowersStormer1970], specialized
from the tracial form in [Szabó and Wouters, Lemma 1.19][SzaboWouters2025], printed p. 1397.
Multiplying by the matrix dimension converts normalized trace to ordinary trace.

For positive matrices `P` and `Q`, the trace of `(P - Q)²` is at most the trace norm of
`P² - Q²`. In an eigenbasis of `P - Q`, pairing `P² - Q²` with the diagonal sign unitary
bounds each squared eigenvalue by the absolute eigenvalue times the diagonal of `P + Q`.
-/

public section

namespace Matrix

open scoped MatrixOrder ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Powers–Størmer inequality for positive factors, including singular matrices. -/
theorem trace_sub_mul_self_le_traceNorm_mul_self_sub (P Q : Matrix ι ι ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    ((P - Q) * (P - Q)).trace.re ≤ (P * P - Q * Q).traceNorm := by
  classical
  have hd := hP.isHermitian.sub hQ.isHermitian
  let U := star hd.eigenvectorUnitary
  let F := Unitary.conjStarAlgAut ℂ _ U
  let X := F P
  let Y := F Q
  let e := hd.eigenvalues
  let D := diagonal (fun i => (e i : ℂ))
  have hXY : X - Y = D := by
    dsimp only [X, Y]
    rw [← map_sub]
    exact hd.conjStarAlgAut_star_eigenvectorUnitary
  have hX : X.PosSemidef := hP.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  have hY : Y.PosSemidef := hQ.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  let s (i : ι) : ℝ := if 0 ≤ e i then 1 else -1
  let S := diagonal (fun i => (s i : ℂ))
  have hS : S ∈ unitaryGroup ι ℂ := by
    rw [mem_unitaryGroup_iff', star_eq_conjTranspose]
    unfold S
    rw [diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    by_cases hi : 0 ≤ e i <;> simp [s, hi]
  have hs : Sᴴ = S := by
    unfold S
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal (s i)
  have hdiag (i : ι) : (X i i).re - (Y i i).re = e i := by
    have h := congrArg (fun M : Matrix ι ι ℂ => (M i i).re) hXY
    simpa only [Matrix.sub_apply, Complex.sub_re, D, diag_diagonal, diagonal_apply_eq,
      Complex.ofReal_re] using h
  have hid : X * X - Y * Y = D * X + Y * D := by
    rw [← hXY]
    noncomm_ring
  have hterm (i : ι) :
      (e i) ^ 2 ≤ ((S * (X * X - Y * Y)) i i).re := by
    rw [hid]
    simp only [S, diagonal_mul, Matrix.add_apply, D, mul_diagonal]
    have hxi := (Complex.nonneg_iff.mp (hX.diag_nonneg (i := i))).1
    have hyi := (Complex.nonneg_iff.mp (hY.diag_nonneg (i := i))).1
    simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero]
    by_cases h : 0 ≤ e i
    · simp only [s, ite_eq_left h, one_mul]
      nlinarith [hdiag i, mul_nonneg h hyi]
    · have hn := le_of_lt (lt_of_not_ge h)
      simp only [s, ite_eq_right h, neg_mul, one_mul]
      nlinarith [hdiag i, mul_nonpos_of_nonpos_of_nonneg hn hxi]
  have hleft : ((P - Q) * (P - Q)).trace.re = ∑ i, (e i) ^ 2 := by
    rw [← trace_conjStarAlgAut U, map_mul, map_sub]
    change ((X - Y) * (X - Y)).trace.re = _
    rw [hXY, diagonal_mul_diagonal, trace_diagonal, Complex.re_sum]
    simp [pow_two]
  rw [hleft, ← traceNorm_conjStarAlgAut U, map_sub, map_mul, map_mul]
  change (∑ i, (e i) ^ 2) ≤ (X * X - Y * Y).traceNorm
  have hbound := re_trace_conjTranspose_mul_le_traceNorm (X * X - Y * Y) S hS
  rw [hs, Matrix.trace, Complex.re_sum] at hbound
  exact (Finset.sum_le_sum fun i _ => hterm i).trans hbound

end Matrix
