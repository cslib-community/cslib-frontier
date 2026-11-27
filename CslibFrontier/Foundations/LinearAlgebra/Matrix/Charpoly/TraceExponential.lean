/-
Copyright (c) 2026 lean-canny contributors and Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/Charpoly/TraceExponential`)

public import CslibFrontier.Init
public import Mathlib.Algebra.Polynomial.OfFn
public import CslibFrontier.Foundations.Data.Polynomial.FiniteExponential
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import CslibFrontier.Foundations.RingTheory.Derivation.Determinant
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring

/-!
# Characteristic coefficients from power traces

Newton's characteristic-coefficient recurrence holds over every commutative ring.
Over a field where `1, …, D` are nonzero, the first `D + 1` coefficients of the reverse
characteristic polynomial agree with the finite exponential of the polynomial with
coefficients `-trace (M^j) / j`. The polynomial of these coefficients is Mathlib's
`Polynomial.ofFn`; there is one finite-exponential construction throughout.

The finite-exponential proof is adapted from
[lean-canny](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/TraceExponentialNewton.lean).
Jacobi's identity is obtained from the existing `Derivation.map_det`.
-/

public section

namespace Matrix

open Polynomial
open scoped BigOperators

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]

private theorem derivative_det_adjugate (M : Matrix ι ι R[X]) :
    derivative M.det = (M.adjugate * M.map derivative).trace := by
  classical
  have h := Derivation.map_det (Polynomial.derivative' (R := R)) M
  change derivative M.det = ∑ i, (M.updateCol i (fun j => derivative (M j i))).det at h
  rw [h, Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec]
  rfl

/-- The adjugate of `1 - X M`, regarded as a polynomial of matrices. -/
private noncomputable def reverseAdjugate (M : Matrix ι ι R) : (Matrix ι ι R)[X] :=
  matPolyEquiv ((1 - (X : R[X]) • M.map C).adjugate)

private theorem reverseAdjugate_relation (M : Matrix ι ι R) :
    reverseAdjugate M * (1 - X * C M) =
      M.charpolyRev.map (algebraMap R (Matrix ι ι R)) := by
  classical
  have h := congrArg (matPolyEquiv (R := R))
    (Matrix.adjugate_mul (1 - (X : R[X]) • M.map C))
  simpa only [reverseAdjugate, Matrix.charpolyRev, map_mul, map_sub, map_one,
    matPolyEquiv_map_smul, map_X, matPolyEquiv_map_C, matPolyEquiv_smul_one, mul_one] using h

private theorem reverseAdjugate_coeff_zero (M : Matrix ι ι R) :
    (reverseAdjugate M).coeff 0 = algebraMap R (Matrix ι ι R) (M.charpolyRev.coeff 0) := by
  classical
  have h := congrArg (fun p : (Matrix ι ι R)[X] => p.coeff 0) (reverseAdjugate_relation M)
  simpa only [mul_sub, mul_one, ← mul_assoc, coeff_sub, coeff_mul_C,
    coeff_mul_X_zero, zero_mul, sub_zero, coeff_map] using h

private theorem reverseAdjugate_coeff_succ (M : Matrix ι ι R) (k : ℕ) :
    (reverseAdjugate M).coeff (k + 1) =
      algebraMap R (Matrix ι ι R) (M.charpolyRev.coeff (k + 1)) +
        (reverseAdjugate M).coeff k * M := by
  classical
  have h := congrArg (fun p : (Matrix ι ι R)[X] => p.coeff (k + 1))
    (reverseAdjugate_relation M)
  simp only [mul_sub, mul_one, ← mul_assoc, coeff_sub, coeff_mul_C,
    coeff_mul_X, coeff_map] at h
  exact sub_eq_iff_eq_add.mp h

private theorem reverseAdjugate_coeff (M : Matrix ι ι R) (k : ℕ) :
    (reverseAdjugate M).coeff k =
      ∑ j ∈ Finset.range (k + 1), M.charpolyRev.coeff (k - j) • M ^ j := by
  classical
  induction k with
  | zero => simpa [Algebra.algebraMap_eq_smul_one] using reverseAdjugate_coeff_zero M
  | succ k ih =>
    rw [reverseAdjugate_coeff_succ, ih, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_sub_add_right, pow_zero, Nat.sub_zero]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [pow_succ, smul_mul_assoc]
    · exact Algebra.algebraMap_eq_smul_one _

private theorem derivative_charpolyRev (M : Matrix ι ι R) :
    derivative M.charpolyRev =
      -(((1 - (X : R[X]) • M.map C).adjugate) * M.map C).trace := by
  classical
  have h := derivative_det_adjugate (1 - (X : R[X]) • M.map C)
  have hder : (1 - (X : R[X]) • M.map C).map derivative = -M.map C := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      derivative_sub, derivative_mul, derivative_X, derivative_C, one_mul,
      mul_zero, add_zero, Matrix.neg_apply]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [hder, Matrix.mul_neg, Matrix.trace_neg] at h
  exact h

private theorem matrix_trace_coeff (M : Matrix ι ι R[X]) (k : ℕ) :
    M.trace.coeff k = ((matPolyEquiv M).coeff k).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag_apply, finsetSum_coeff, matPolyEquiv_coeff_apply]

/-- Newton's characteristic-coefficient recurrence over an arbitrary
 commutative ring. No inverses or eigenvalues occur in this identity. -/
theorem charpolyRev_newton (M : Matrix ι ι R) (k : ℕ) :
    (k + 1 : ℕ) * M.charpolyRev.coeff (k + 1) =
      -(∑ j ∈ Finset.range (k + 1),
        M.charpolyRev.coeff (k - j) * (M ^ (j + 1)).trace) := by
  classical
  have h := congrArg (fun p : R[X] => p.coeff k) (derivative_charpolyRev M)
  rw [coeff_derivative, coeff_neg, matrix_trace_coeff, map_mul, matPolyEquiv_map_C,
    coeff_mul_C] at h
  change M.charpolyRev.coeff (k + 1) * ((k : R) + 1) =
    -((reverseAdjugate M).coeff k * M).trace at h
  rw [reverseAdjugate_coeff, Finset.sum_mul, Matrix.trace_sum] at h
  simp only [smul_mul_assoc, ← pow_succ, Matrix.trace_smul, smul_eq_mul] at h
  simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h

/-- Within the matrix dimension, reversing the index identifies a coefficient of
`charpolyRev` with the corresponding coefficient of `charpoly`. -/
theorem coeff_charpolyRev_card_sub (M : Matrix ι ι R)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    M.charpolyRev.coeff (Fintype.card ι - k) = M.charpoly.coeff k := by
  nontriviality R
  rw [← reverse_charpoly, coeff_reverse, charpoly_natDegree_eq_dim,
    revAt_le (Nat.sub_le _ _), Nat.sub_sub_self hk]

end Matrix

namespace Polynomial

open Matrix
open scoped BigOperators

variable {K : Type*} [Field K]

/-- Newton recurrence determines all coefficients through a degree where
 its integer multipliers are nonzero. -/
theorem coefficients_eq_of_newton (D : ℕ) (t : ℕ → K) (P Q : K[X])
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0)
    (hzero : P.coeff 0 = Q.coeff 0)
    (hP : ∀ k < D, (k + 1 : ℕ) * P.coeff (k + 1) =
      -(∑ j ∈ Finset.range (k + 1), P.coeff (k - j) * t (j + 1)))
    (hQ : ∀ k < D, (k + 1 : ℕ) * Q.coeff (k + 1) =
      -(∑ j ∈ Finset.range (k + 1), Q.coeff (k - j) * t (j + 1)))
    (k : ℕ) (hk : k ≤ D) : P.coeff k = Q.coeff k := by
  classical
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    cases k with
    | zero => exact hzero
    | succ k =>
      apply mul_left_cancel₀ (hK (k + 1) (by omega) hk)
      rw [hP k (by omega), hQ k (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [ih (k - j) (by omega) (by omega)]

end Polynomial

namespace Matrix

open Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] [DecidableEq K]

private theorem trace_logarithm_derivative_coeff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (D : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0) (k : ℕ) (hk : k < D) :
    (derivative (ofFn (D + 1) (fun j => -(M ^ (j : ℕ)).trace / ((j : ℕ) : K)))).coeff k =
      -(M ^ (k + 1)).trace := by
  classical
  rw [coeff_derivative, ofFn_coeff_eq_val_of_lt _ (by omega : k + 1 < D + 1)]
  convert div_mul_cancel₀ (-(M ^ (k + 1)).trace) (hK (k + 1) (by omega) (by omega)) using 1;
    simp only [Nat.cast_add, Nat.cast_one]

/-- The explicit finite exponential satisfies Newton's recurrence in
 every field whose small integer denominators are nonzero. -/
private theorem trace_exponential_newton {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (D : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0) (k : ℕ) (hk : k < D) :
    (k + 1 : ℕ) * (finiteExponential D
      (ofFn (D + 1) (fun j => -(M ^ (j : ℕ)).trace / ((j : ℕ) : K)))).coeff (k + 1) =
      -(∑ j ∈ Finset.range (k + 1),
        (finiteExponential D
          (ofFn (D + 1) (fun j => -(M ^ (j : ℕ)).trace / ((j : ℕ) : K)))).coeff (k - j) *
          (M ^ (j + 1)).trace) := by
  classical
  let G := ofFn (D + 1) (fun j => -(M ^ (j : ℕ)).trace / ((j : ℕ) : K))
  have hG : G.coeff 0 = 0 := by simp [G]
  have h := finiteExponential_differential_coeff D G hG hK k hk
  rw [coeff_derivative, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  have hsum : (∑ j ∈ Finset.range (k + 1),
      (derivative G).coeff j *
        (finiteExponential D G).coeff (k - j)) =
      -(∑ j ∈ Finset.range (k + 1),
        (finiteExponential D G).coeff (k - j) *
          (M ^ (j + 1)).trace) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show (derivative G).coeff j = -(M ^ (j + 1)).trace from
      trace_logarithm_derivative_coeff M D hK j (by have := Finset.mem_range.mp hj; omega)]
    ring
  exact (by simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h.trans hsum)

/-- The finite exponential has exactly the characteristic coefficients
 through the requested truncation degree. -/
theorem trace_exponential_coeff_eq_charpolyRev {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (D : ℕ)
    (hK : ∀ j, 1 ≤ j → j ≤ D → (j : K) ≠ 0) (k : ℕ) (hk : k ≤ D) :
    (finiteExponential D
      (ofFn (D + 1) (fun j => -(M ^ (j : ℕ)).trace / ((j : ℕ) : K)))).coeff k =
      M.charpolyRev.coeff k := by
  classical
  apply coefficients_eq_of_newton D (fun j => (M ^ j).trace) _ _ hK ?_
    (trace_exponential_newton M D hK) (fun j _ => charpolyRev_newton M j) k hk
  have hG : (ofFn (D + 1) (fun j => -(M ^ (j : ℕ)).trace / ((j : ℕ) : K))).coeff 0 = 0 := by
    simp
  change (finiteExponential D _).coeff 0 = M.charpolyRev.coeff 0
  rw [finiteExponential_coeff_zero D _ hG, coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

/-- Reversal turns the constructed exponential coefficients into the
 actual characteristic polynomial coefficients of the matrix. -/
theorem trace_exponential_coeff_eq_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K)
    (hK : ∀ j, 1 ≤ j → j ≤ Fintype.card ι → (j : K) ≠ 0)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    (finiteExponential (Fintype.card ι)
      (ofFn (Fintype.card ι + 1)
        (fun j => -(M ^ (j : ℕ)).trace / ((j : ℕ) : K)))).coeff (Fintype.card ι - k) =
          M.charpoly.coeff k := by
  classical
  rw [trace_exponential_coeff_eq_charpolyRev M _ hK _ (Nat.sub_le _ _),
    Matrix.coeff_charpolyRev_card_sub M k hk]

end Matrix
