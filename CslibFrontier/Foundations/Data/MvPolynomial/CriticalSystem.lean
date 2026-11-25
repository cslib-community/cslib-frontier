/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/

module
-- upstream: candidate (Mathlib, multivariate polynomial derivatives)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.MvPolynomial.PDerivDegree
public import Mathlib.Algebra.MvPolynomial.CommRing
import CslibFrontier.Foundations.Data.MvPolynomial.Degrees
import Mathlib.Tactic.Ring

/-!
# Polynomial critical equations for a separated power potential

The gradient of a perturbed separated potential is a scalar multiple of the pure-power
relations `X i ^ ell - criticalLower ... i`. The lower parts have degree below `ell` when
the input polynomial has degree at most `ell`. These identities hold over any commutative
coefficient ring; identifying gradient zeros with relation zeros additionally requires that
the scalar `ell + 1` can be cancelled.

This algebraic step is ported from `LeanCanny.CountingHierarchy.SeparatedCriticalPolynomial`
and the center definition in `SeparatedCriticalValues` at lean-canny commit
`970f28a5ecefc1327402ade16c068aa4b1b2c183`. No real geometric or feasibility claim is made here.
-/

public section

namespace MvPolynomial.CriticalSystem

open MvPolynomial
open scoped BigOperators

/-- The separated natural centers, indexed from zero. -/
@[expose] def separatedCenters {n : ℕ} (ell : ℕ) (i : Fin n) : ℕ :=
  (4 * ell) ^ (i.val + 1)

variable {S T : Type*} [CommRing S] [CommRing T] {n : ℕ}

open Classical in
/-- The sum of separated pure-power potentials. -/
@[expose] noncomputable def potentialPolynomial (ell : ℕ) (a : Fin n → S) :
    MvPolynomial (Fin n) S :=
  ∑ i, (X i ^ (ell + 1) - C ((ell + 1 : ℕ) * a i ^ ell) * X i +
    C ((ell + 1 : ℕ) * a i ^ (ell + 1)))

/-- The separated potential perturbed by a scaled input polynomial. -/
@[expose] noncomputable def deformedPolynomial (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) : MvPolynomial (Fin n) S :=
  potentialPolynomial ell a + C ((ell + 1 : ℕ) * u) * F

/-- At each point, the deformed value is affine in the deformation parameter. -/
theorem eval_deformedPolynomial (ell : ℕ) (a x : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) :
    eval x (deformedPolynomial ell a u F) =
      eval x (potentialPolynomial ell a) + u * ((ell + 1 : ℕ) * eval x F) := by
  rw [deformedPolynomial, map_add, map_mul, eval_C]; ring

/-- The lower part of the pure-power critical relation. -/
@[expose] noncomputable def criticalLower (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (i : Fin n) : MvPolynomial (Fin n) S :=
  C (a i ^ ell) - C u * pderiv i F

/-- Coefficient maps transport the separated potential. -/
theorem potentialPolynomial_map (φ : S →+* T) (ell : ℕ) (a : Fin n → S) :
    (potentialPolynomial ell a).map φ = potentialPolynomial ell (fun i => φ (a i)) := by
  classical
  simp only [potentialPolynomial, map_sum, map_add, map_sub, map_mul, map_pow, map_X,
    map_C, map_natCast]

/-- Coefficient maps transport the lower critical relations. -/
theorem criticalLower_map (φ : S →+* T) (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (i : Fin n) :
    (criticalLower ell a u F i).map φ =
      criticalLower ell (fun j => φ (a j)) (φ u) (F.map φ) i := by
  simp only [criticalLower, map_sub, map_mul, map_C, map_pow, pderiv_map]

/-- Coefficient maps transport the deformed potential. -/
theorem deformedPolynomial_map (φ : S →+* T) (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) :
    (deformedPolynomial ell a u F).map φ =
      deformedPolynomial ell (fun i => φ (a i)) (φ u) (F.map φ) := by
  simp only [deformedPolynomial, map_add, potentialPolynomial_map, map_mul, map_C, map_natCast]

/-- The potential has separated pure-power partial derivatives. -/
theorem pderiv_potentialPolynomial (ell : ℕ) (a : Fin n → S) (j : Fin n) :
    pderiv j (potentialPolynomial ell a) =
      C ((ell + 1 : ℕ) : S) * (X j ^ ell - C (a j ^ ell)) := by
  classical
  rw [potentialPolynomial, map_sum, Finset.sum_eq_single j]
  · simp only [map_add, map_sub, pderiv_pow, pderiv_C_mul, pderiv_X_self,
      pderiv_C, Nat.add_sub_cancel, mul_one, add_zero]
    simp only [map_mul, map_natCast]; ring
  · intro i _ hij; simp [hij]
  · simp

/-- The deformation gradient gives the actual pure-power critical relations. -/
theorem pderiv_deformedPolynomial (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (i : Fin n) :
    pderiv i (deformedPolynomial ell a u F) =
      C ((ell + 1 : ℕ) : S) * (X i ^ ell - criticalLower ell a u F i) := by
  classical
  rw [deformedPolynomial, map_add, pderiv_potentialPolynomial, pderiv_C_mul, criticalLower,
    map_mul]
  ring

/-- Each lower relation has degree strictly below its leading pure power. -/
theorem criticalLower_degree (ell : ℕ) (hell : 1 ≤ ell) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (hF : F.totalDegree ≤ ell) (i : Fin n) :
    (criticalLower ell a u F i).totalDegree < ell := by
  classical
  have hp := totalDegree_pderiv_le F i
  have hm := totalDegree_mul (C u) (pderiv i F)
  have hs := totalDegree_sub (C (a i ^ ell)) (C u * pderiv i F)
  rw [totalDegree_C] at hm hs
  exact lt_of_le_of_lt hs (by omega)

/-- The separated potential has degree at most `ell + 1`. -/
theorem totalDegree_potentialPolynomial_le (ell : ℕ) (a : Fin n → S) :
    (potentialPolynomial ell a).totalDegree ≤ ell + 1 := by
  classical
  refine totalDegree_finsetSum_le fun i _ => (totalDegree_add _ _).trans
    (max_le ((totalDegree_sub _ _).trans (max_le ?_ ?_))
      ((totalDegree_C _).trans_le (Nat.zero_le _)))
  · simpa only [mul_one] using (totalDegree_pow _ _).trans
      (Nat.mul_le_mul_left (ell + 1) (totalDegree_X_le (R := S) i))
  · have hm := totalDegree_mul (C ((ell + 1 : ℕ) * a i ^ ell)) (X i)
    rw [totalDegree_C, zero_add] at hm
    exact hm.trans ((totalDegree_X_le i).trans (by omega))

/-- The scalar deformation preserves the larger of the potential and input degree bounds. -/
theorem totalDegree_deformedPolynomial_le (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (hF : F.totalDegree ≤ ell + 1) :
    (deformedPolynomial ell a u F).totalDegree ≤ ell + 1 := by
  have hm := totalDegree_mul (C ((ell + 1 : ℕ) * u)) F
  rw [totalDegree_C, zero_add] at hm
  exact (totalDegree_add _ _).trans
    (max_le (totalDegree_potentialPolynomial_le ell a) (hm.trans hF))

end MvPolynomial.CriticalSystem
