/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root tests)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseRootProduct
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.Charpoly.EvalDeterminant
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# An integer determinant criterion for qualifying characteristic roots

For an integer matrix with separable characteristic polynomial over `ℂ`, a
short derivative-sign label and a bounded shift give a negative determinant
exactly when a qualifying real characteristic root exists.

Adapted from `QuotientRootLabelCriterion` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the matrix directly.
-/

public section

namespace Matrix

open Polynomial

/-- A real characteristic root at which `q` is positive exists exactly when
some short derivative-sign list and bounded natural shift give a negative
integer determinant of the shifted label evaluated at `M`. -/
theorem exists_eval₂_pos_at_charpoly_root_iff_neg_shiftedRootLabel_det
    {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℤ) {q : Polynomial ℤ}
    {D N b : ℕ} (hD : 0 < D) (hcard : Fintype.card ι ≤ D) (hDN : D ≤ 2 ^ N)
    (hqD : q.natDegree ≤ D) (hMb : M.charpoly.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b)
    (hsep : (M.charpoly.map (algebraMap ℤ ℂ)).Separable) :
    (∃ x : ℝ, M.charpoly.eval₂ (Int.castRingHom ℝ) x = 0 ∧
        0 < q.eval₂ (Int.castRingHom ℝ) x) ↔
      ∃ L : List (Fin D × SignType), L.length ≤ N ∧ ∃ e : ℕ, e ≤ D ∧
        (Polynomial.aeval M (shiftedRootLabel D e
          (sparseIntegerRootLabel M.charpoly q N b L))).det < 0 := by
  have hdeg := (M.charpoly_natDegree_eq_dim).trans_le hcard
  have h := exists_eval₂_pos_at_root_iff_neg_shiftedRootLabel_prod
    M.charpoly_monic.ne_zero hD hdeg hDN hqD hMb hqb
  have hdet (g : Polynomial ℤ) :
      (∏ z ∈ (M.charpoly.aroots ℂ).toFinset, Polynomial.aeval z g).re =
        ((Polynomial.aeval M g).det : ℝ) := by
    have he := algebraMap_det_aeval_eq_prod_aroots_toFinset M g
      (IsAlgClosed.splits _) (IsAlgClosed.splits _) hsep
    simpa only [algebraMap_int_eq, Int.coe_castRingHom, Complex.intCast_re] using
      (congrArg Complex.re he).symm
  simpa only [hdet, Int.cast_lt_zero] using h

end Matrix
