/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, pure-power polynomial quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.Relations
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import CslibFrontier.Foundations.Data.MvPolynomial.DividedDifferences
import CslibFrontier.Foundations.Data.MvPolynomial.Determinant
import CslibFrontier.Foundations.Data.MvPolynomial.ReproducingKernel
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.Tactic.Ring

/-!
# The normalized kernel of a pure-power polynomial system

For a system `X i ^ (d + 1) - r i` with `totalDegree (r i) ≤ d` and `d ≥ 1`, every common
zero has a polynomial reproducing kernel for the finite residue functional. Its evaluation
at that zero is the Jacobian determinant, even for a multiple zero and over an arbitrary
commutative coefficient ring (`purePower_reproducing_kernel`).

The kernel is constructed as the determinant of a divided-difference matrix. Its leading
part is diagonal, giving residue one by determinant coefficient stability; the adjugate
identity then proves annihilation of all coordinate differences. No kernel or nonsingularity
hypothesis is supplied by the caller.

Ported and simplified from the
[divided-difference matrix](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/PurePowerDifferenceMatrix.lean)
and
[normalized kernel construction](https://github.com/edemaine/lean-canny/blob/970f28a5ecefc1327402ade16c068aa4b1b2c183/LeanCanny/CountingHierarchy/PurePowerKernel.lean)
in lean-canny.
-/

public section

namespace MvPolynomial.PurePower

open MvPolynomial Matrix
open scoped BigOperators

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The lower parts determine a divided-difference matrix. Its highest
 degree part is diagonal and its diagonal evaluation is the Jacobian. -/
private theorem purePower_difference_matrix (x : Fin n → A) (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) A) (hr : ∀ i, (r i).totalDegree ≤ d)
    (hx : ∀ i, eval x (r i) = x i ^ (d + 1)) :
    ∃ W : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) A),
      (∀ i, ∑ j, W i j * (C (x j) - X j) = -(X i ^ (d + 1) - r i)) ∧
      (∀ i j, (W i j).totalDegree ≤ d) ∧
      (∀ i j, (W i j - Matrix.diagonal (fun j => X j ^ d) i j).totalDegree < d) ∧
      (∀ i j, eval x (W i j) = eval x (pderiv j (X i ^ (d + 1) - r i))) := by
  classical
  have hr' (i : Fin n) : (r i).totalDegree ≤ (d - 1) + 1 := by have := hr i; omega
  choose D hdiff hdegree hdiag using
    (fun i => polynomial_divided_differences x (r i) (d - 1) (hr' i))
  let W : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n) A) := fun i j =>
    (if i = j then purePowerDifference (x i) i d else 0) - D i j
  refine ⟨W, ?_, ?_, ?_, ?_⟩
  · intro i
    simp only [W, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
    rw [purePowerDifference_mul, ← hdiff i, hx i]
    ring
  · intro i j
    have hD := hdegree i j
    have hg : (if i = j then purePowerDifference (x i) i d else
        (0 : MvPolynomial (Fin n) A)).totalDegree ≤ d := by
      split_ifs
      · exact purePowerDifference_degree _ _ _
      · simp
    exact (totalDegree_sub _ _).trans (max_le hg (by omega))
  · intro i j
    have hD := hdegree i j
    by_cases hij : i = j
    · subst j
      have heq : W i i - Matrix.diagonal (fun j => X j ^ d) i i =
          (purePowerDifference (x i) i d - X i ^ d) - D i i := by
        simp only [W, ↓reduceIte, Matrix.diagonal_apply_eq]
        ring
      rw [heq]
      exact (totalDegree_sub _ _).trans_lt (max_lt (purePowerDifference_lower_degree _ _ hd)
        (by omega))
    · simp only [W, hij, ↓reduceIte, zero_sub, Matrix.diagonal_apply_ne _ hij,
        sub_zero, totalDegree_neg]
      omega
  · intro i j
    simp only [W, map_sub, hdiag, pderiv_pow, pderiv_X, Pi.single_apply,
      map_mul, map_natCast, map_pow, eval_X]
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte, purePowerDifference_diagonal, Nat.add_sub_cancel,
        mul_one, map_one]
    · simp [hij]

/-- The adjugate identity descends to any ideal, without requiring the
 determinant to be a unit. -/
private theorem determinant_annihilates_mod_ideal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι A) (z : ι → A) (I : Ideal A)
    (h : ∀ i, ∑ j, M i j * z j ∈ I) (j : ι) : M.det * z j ∈ I := by
  classical
  let φ := Ideal.Quotient.mk I
  have hv : M.map φ *ᵥ (fun j => φ (z j)) = 0 := by
    ext i
    change (∑ j, φ (M i j) * φ (z j)) = 0
    simp only [← map_mul]
    rw [← map_sum φ (fun j => M i j * z j)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (h i)
  have hz := congrArg (fun v => ((M.map φ).adjugate *ᵥ v) j) hv
  simp only [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec,
    Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, Matrix.mulVec_zero, Pi.zero_apply] at hz
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  simpa only [φ, map_mul, RingHom.map_det, RingHom.mapMatrix_apply] using hz

/-- A pure-power system has an actual polynomial reproducing kernel.
 Its diagonal is the Jacobian determinant, even at multiple zeros. -/
theorem purePower_reproducing_kernel (x : Fin n → A) (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) A) (hr : ∀ i, (r i).totalDegree ≤ d)
    (hx : ∀ i, eval x (r i) = x i ^ (d + 1)) :
    ∃ K : MvPolynomial (Fin n) A,
      (∀ q, residue (d + 1) r (K * q) = eval x q) ∧
      eval x K = Matrix.det (fun i j => eval x (pderiv j (X i ^ (d + 1) - r i))) := by
  classical
  obtain ⟨W, hrow, hdegree, htop, hdiag⟩ := purePower_difference_matrix x d hd r hr hx
  have hell : 1 ≤ d + 1 := by omega
  have hr' (i : Fin n) : (r i).totalDegree < d + 1 := by have := hr i; omega
  let top : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => d)
  have hnormal : residue (d + 1) r W.det = 1 := by
    rw [residue_low_degree hell r hr' W.det (by
      simpa only [Nat.add_sub_cancel, Fintype.card_fin] using totalDegree_det_le W d hdegree)]
    have hN (i j : Fin n) :
        (Matrix.diagonal (fun j => (X j : MvPolynomial (Fin n) A) ^ d) i j).totalDegree ≤ d := by
      rw [Matrix.diagonal_apply]
      split_ifs
      · exact (totalDegree_pow _ _).trans (by
          simpa only [Nat.mul_one] using Nat.mul_le_mul_left d (totalDegree_X_le (R := A) i))
      · simp
    have he : n * d ≤ top.degree := by
      simp [top, Finsupp.degree_eq_sum]
    have hc := coeff_det_eq_of_totalDegree_sub_lt W (Matrix.diagonal (fun j => X j ^ d))
      d hdegree hN htop top he
    have hp : (∏ i : Fin n, (X i : MvPolynomial (Fin n) A) ^ d) =
        monomial top 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      rfl
    change W.det.coeff top = 1
    simp only [hc, Matrix.det_diagonal, hp, coeff_monomial, ↓reduceIte]
  have hann (j : Fin n) : W.det * (C (x j) - X j) ∈ relationIdeal (d + 1) r :=
    determinant_annihilates_mod_ideal W _ _ (fun i => by
      rw [hrow]; exact (relationIdeal (d + 1) r).neg_mem (Ideal.subset_span ⟨i, rfl⟩)) j
  refine ⟨W.det, fun q => ?_, ?_⟩
  · refine polynomial_kernel_reproduces (linear hell r hr') W.det x hnormal (fun i v => ?_) q
    apply linear_mem_ideal hell r hr'
    rw [show W.det * v * (X i - C (x i)) = -(v * (W.det * (C (x i) - X i))) by ring]
    exact (relationIdeal (d + 1) r).neg_mem ((relationIdeal (d + 1) r).mul_mem_left v (hann i))
  · rw [RingHom.map_det]
    exact congrArg det (Matrix.ext hdiag)

end MvPolynomial.PurePower
