/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, matrix characteristic polynomial)

public import CslibFrontier.Init
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.Ring

/-!
# Determinants of polynomial evaluations at matrices

Factoring the test polynomial gives a resultant with the characteristic
polynomial. When the characteristic polynomial also splits, the determinant
is the product of the test values at its roots, counted with multiplicity.
After a coefficient extension in which the characteristic polynomial is
separable, the product can be taken over distinct roots.

Adapted from `NormPolynomialEvaluation` and `QuotientRealSpectralProduct` in
lean-canny at `970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the matrix directly.
-/

public section

namespace Matrix

open Polynomial

section Field

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The determinant of a split polynomial evaluated at a matrix is its
resultant against the characteristic polynomial, with the characteristic polynomial first. -/
theorem det_aeval_eq_charpoly_resultant (M : Matrix ι ι K) (g : Polynomial K) (hg : g.Splits) :
    (Polynomial.aeval M g).det = M.charpoly.resultant g := by
  let q := M.charpoly
  have hqdeg : q.natDegree = Fintype.card ι := charpoly_natDegree_eq_dim M
  let d : Polynomial K →* K := detMonoidHom.comp (Polynomial.aeval M).toMonoidHom
  have hconst (c : K) : d (C c) = c ^ Fintype.card ι := by
    change (Polynomial.aeval M (C c)).det = _
    rw [aeval_C, algebraMap_eq_diagonal, det_diagonal]
    change (∏ _ : ι, c) = _
    rw [Finset.prod_const, Finset.card_univ]
  have hlinear (c : K) : d (X - C c) = (-1 : K) ^ Fintype.card ι * q.eval c := by
    change (Polynomial.aeval M (X - C c)).det = _
    rw [map_sub, aeval_X, aeval_C, algebraMap_eq_diagonal]
    change (M - scalar ι c).det = _ * M.charpoly.eval c
    rw [eval_charpoly, ← det_neg, neg_sub]
  have hprod : d g = g.leadingCoeff ^ Fintype.card ι *
      (g.roots.map (fun c => (-1 : K) ^ Fintype.card ι * q.eval c)).prod := by
    conv_lhs => rw [hg.eq_prod_roots]
    simp only [map_mul, hconst, map_multiset_prod, Multiset.map_map, Function.comp_apply, hlinear]
  change d g = q.resultant g
  rw [hprod, resultant_comm, resultant_eq_prod_eval _ _ _ le_rfl hg, hqdeg,
    Multiset.prod_map_mul]
  simp only [Multiset.map_const', Multiset.prod_replicate, ← pow_mul, ← hg.natDegree_eq_card_roots]
  rw [mul_comm (Fintype.card ι) g.natDegree]
  ring

/-- The determinant of a polynomial evaluated at a matrix is the product of
its values at the characteristic roots, counted with multiplicity, when both polynomials split. -/
theorem det_aeval_eq_prod_charpoly_roots (M : Matrix ι ι K) (g : Polynomial K) (hg : g.Splits)
    (hM : M.charpoly.Splits) :
    (Polynomial.aeval M g).det = (M.charpoly.roots.map g.eval).prod := by
  rw [det_aeval_eq_charpoly_resultant M g hg, resultant_eq_prod_eval _ _ _ le_rfl hM,
    M.charpoly_monic.leadingCoeff, one_pow, one_mul]

end Field

/-- Extend coefficients to a field in which both polynomials split. If the
characteristic polynomial is separable there, the image of the source determinant
is the product of the test values over distinct characteristic roots. -/
theorem algebraMap_det_aeval_eq_prod_aroots_toFinset {ι R K : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] [Field K] [DecidableEq K] [Algebra R K] (M : Matrix ι ι R) (g : Polynomial R)
    (hg : (g.map (algebraMap R K)).Splits) (hM : (M.charpoly.map (algebraMap R K)).Splits)
    (hsep : (M.charpoly.map (algebraMap R K)).Separable) :
    algebraMap R K (Polynomial.aeval M g).det =
      ∏ z ∈ (M.charpoly.aroots K).toFinset, Polynomial.aeval z g := by
  classical
  let f := algebraMap R K
  have hmap : f.mapMatrix (Polynomial.aeval M g) =
      Polynomial.aeval (M.map f) (g.map f) := by
    apply Polynomial.map_aeval_eq_aeval_map
    apply RingHom.ext
    intro c
    exact (Matrix.map_algebraMap c f (map_zero f) (by simp [f])).symm
  rw [RingHom.map_det, hmap]
  have hs : (M.map f).charpoly.Splits := by rwa [Matrix.charpoly_map]
  rw [det_aeval_eq_prod_charpoly_roots _ _ hg hs, Matrix.charpoly_map]
  rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, (Polynomial.nodup_roots hsep).dedup]
  simp only [Polynomial.aeval_def, Polynomial.eval_map, f]

end Matrix
