/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, polynomial root tests)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ShiftedLabel
public import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.SparseIntegerRootLabel
public import Mathlib.LinearAlgebra.Complex.Module
import CslibFrontier.Foundations.Algebra.Polynomial.RealRoot.ConjugateProduct
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# A spectral-product criterion for a qualifying real root

A short list of derivative signs and a bounded shift suffice to make the
product of the shifted integer label over distinct complex roots negative
exactly when the qualifying polynomial is positive at some real root.

Adapted from `RootLabelProductCriterion` and `SparseRootProductCriterion` in
lean-canny at commit `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Polynomial

open Finset

/-- Existence of a root of `p` at which `q` is positive is equivalent to a
negative spectral product for some short integer label and bounded shift. -/
theorem exists_eval₂_pos_at_root_iff_neg_shiftedRootLabel_prod {D N b : ℕ}
    {p q : Polynomial ℤ} (hp : p ≠ 0) (hD : 0 < D) (hpD : p.natDegree ≤ D)
    (hDN : D ≤ 2 ^ N) (hqD : q.natDegree ≤ D)
    (hpb : p.coeffNorm1 ≤ 2 ^ b) (hqb : q.coeffNorm1 ≤ 2 ^ b) :
    (∃ x : ℝ, p.eval₂ (Int.castRingHom ℝ) x = 0 ∧ 0 < q.eval₂ (Int.castRingHom ℝ) x) ↔
      ∃ L : List (Fin D × SignType), L.length ≤ N ∧ ∃ e : ℕ, e ≤ D ∧
        (∏ z ∈ (p.aroots ℂ).toFinset,
          aeval z (shiftedRootLabel D e (sparseIntegerRootLabel p q N b L))).re < 0 := by
  classical
  let realRoots := (p.map (algebraMap ℤ ℝ)).roots.toFinset
  let upperRoots := (p.aroots ℂ).toFinset.filter fun z => 0 < z.im
  let label (L : List (Fin D × SignType)) := sparseIntegerRootLabel p q N b L
  let labelEval (g : Polynomial ℤ) (x : ℝ) := g.eval₂ (Int.castRingHom ℝ) x
  have hpMap : p.map (algebraMap ℤ ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff Int.cast_injective).mpr hp
  have hmem (x : ℝ) : x ∈ realRoots ↔ labelEval p x = 0 := by
    change x ∈ (p.map (algebraMap ℤ ℝ)).roots.toFinset ↔ labelEval p x = 0
    rw [Multiset.mem_toFinset, mem_roots hpMap, IsRoot.def, eval_map, algebraMap_int_eq]
  have hfactor (g : Polynomial ℤ) :
      (∏ z ∈ (p.aroots ℂ).toFinset, aeval z g).re =
        (∏ x ∈ realRoots, labelEval g x) * ∏ z ∈ upperRoots, Complex.normSq (aeval z g) := by
    have heval (z : ℂ) : aeval z (g.map (algebraMap ℤ ℝ)) = aeval z g :=
      (aeval_eq_aeval_map (IsScalarTower.algebraMap_eq ℤ ℝ ℂ).symm g z).symm
    have h := congrArg Complex.re
      (prod_aeval_aroots_toFinset_eq (p.map (algebraMap ℤ ℝ)) (g.map (algebraMap ℤ ℝ)))
    simp only [aroots_map, heval, Complex.ofReal_re, eval_map] at h
    simpa only [realRoots, upperRoots, labelEval, algebraMap_int_eq] using h
  have hmarg (L : List (Fin D × SignType)) (hL : L.length ≤ N) {x : ℝ}
      (hx : labelEval p x = 0) :=
    eval₂_sparseIntegerRootLabel_margin hp L hL hpD hqD hpb hqb hx
  have hsign (L : List (Fin D × SignType)) (hL : L.length ≤ N) {e : ℕ} (he : e ≤ D)
      {x : ℝ} (hx : labelEval p x = 0) :
      SignType.sign (labelEval (shiftedRootLabel D e (label L)) x) =
        -SignType.sign (labelEval (label L) x) := by
    have hm : (1 : ℝ) / 2 ≤ ((label L).map (Int.castRingHom ℝ)).eval x ∨
        ((label L).map (Int.castRingHom ℝ)).eval x ≤ -(1 : ℝ) / 2 := by
      simpa only [eval_map] using (hmarg L hL hx).1
    have hmap : (shiftedRootLabel D e (label L)).map (Int.castRingHom ℝ) =
        shiftedRootLabel D e ((label L).map (Int.castRingHom ℝ)) := by
      simp only [shiftedRootLabel, Polynomial.map_add, Polynomial.map_mul, map_C]
      simp only [_root_.map_neg, _root_.map_mul, map_ofNat, map_natCast]
    simpa only [← hmap, eval_map, labelEval] using sign_eval_shiftedRootLabel hD he hm
  constructor
  · intro hex
    obtain ⟨L, hL, x, hx, _, hpos, hother⟩ :=
      exists_sparseIntegerRootLabel hp hpD hDN hqD hpb hqb hex
    obtain ⟨e, he, hnz⟩ := exists_aeval_shiftedRootLabel_ne_zero (A := ℂ) p (label L) hpD
    let g := shiftedRootLabel D e (label L)
    have hxneg : labelEval g x < 0 := sign_eq_neg_one_iff.mp (by
      rw [hsign L hL he hx, sign_pos hpos])
    have hreal : (∏ y ∈ realRoots, labelEval g y) < 0 := by
      rw [← mul_prod_erase realRoots (labelEval g) ((hmem x).mpr hx)]
      refine mul_neg_of_neg_of_pos hxneg (prod_pos fun y hy => ?_)
      obtain ⟨hne, hy⟩ := mem_erase.mp hy
      have hy0 := (hmem y).mp hy
      exact sign_eq_one_iff.mp (by rw [hsign L hL he hy0, sign_neg (hother y hy0 hne), neg_neg])
    have hupper : 0 < ∏ z ∈ upperRoots, Complex.normSq (aeval z g) :=
      prod_pos fun z hz => Complex.normSq_pos.mpr
        (hnz z (Multiset.mem_toFinset.mp (mem_filter.mp hz).1))
    exact ⟨L, hL, e, he, (hfactor g).trans_lt (mul_neg_of_neg_of_pos hreal hupper)⟩
  · rintro ⟨L, hL, e, he, hprod⟩
    by_contra! hn
    let g := shiftedRootLabel D e (label L)
    have hreal : 0 ≤ ∏ x ∈ realRoots, labelEval g x := by
      refine prod_nonneg fun x hx => le_of_not_gt fun hneg => ?_
      have hx0 := (hmem x).mp hx
      have hs := sign_neg hneg
      change SignType.sign (labelEval (shiftedRootLabel D e (label L)) x) = -1 at hs
      rw [hsign L hL he hx0, neg_inj] at hs
      exact (not_lt_of_ge (hn x hx0)) ((hmarg L hL hx0).2.mp (sign_eq_one_iff.mp hs)).1
    have hupper : 0 ≤ ∏ z ∈ upperRoots, Complex.normSq (aeval z g) :=
      prod_nonneg fun z _ => Complex.normSq_nonneg _
    exact (not_lt_of_ge (mul_nonneg hreal hupper)) ((hfactor g).symm.trans_lt hprod)

end Polynomial
