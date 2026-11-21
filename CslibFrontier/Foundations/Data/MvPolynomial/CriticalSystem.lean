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

variable {S : Type*} [CommRing S] {n : ℕ}

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

/-- The lower part of the pure-power critical relation. -/
@[expose] noncomputable def criticalLower (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (i : Fin n) : MvPolynomial (Fin n) S :=
  C (a i ^ ell) - C u * pderiv i F

/-- The potential has separated pure-power partial derivatives. -/
theorem pderiv_potentialPolynomial (ell : ℕ) (a : Fin n → S) (j : Fin n) :
    pderiv j (potentialPolynomial ell a) =
      C ((ell + 1 : ℕ) : S) * (X j ^ ell - C (a j ^ ell)) := by
  classical
  have hentry (i : Fin n) : pderiv j
      (X i ^ (ell + 1) - C ((ell + 1 : ℕ) * a i ^ ell) * X i +
        C ((ell + 1 : ℕ) * a i ^ (ell + 1))) =
      if i = j then C ((ell + 1 : ℕ) : S) * (X j ^ ell - C (a j ^ ell)) else 0 := by
    by_cases hij : i = j
    · subst i
      simp only [map_add, map_sub, pderiv_pow, pderiv_C_mul, pderiv_X_self,
        pderiv_C, Nat.add_sub_cancel, mul_one, add_zero, ↓reduceIte]
      simp only [map_mul, map_natCast]
      ring
    · simp [hij]
  rw [potentialPolynomial, map_sum]
  simp_rw [hentry]
  simp

/-- The deformation gradient gives the actual pure-power critical relations. -/
theorem pderiv_deformedPolynomial (ell : ℕ) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (i : Fin n) :
    pderiv i (deformedPolynomial ell a u F) =
      C ((ell + 1 : ℕ) : S) * (X i ^ ell - criticalLower ell a u F i) := by
  classical
  rw [deformedPolynomial, map_add, pderiv_potentialPolynomial, pderiv_C_mul,
    criticalLower, map_mul]
  ring

/-- Each lower relation has degree strictly below its leading pure power. -/
theorem criticalLower_degree (ell : ℕ) (hell : 1 ≤ ell) (a : Fin n → S) (u : S)
    (F : MvPolynomial (Fin n) S) (hF : F.totalDegree ≤ ell) (i : Fin n) :
    (criticalLower ell a u F i).totalDegree < ell := by
  classical
  have hp := totalDegree_pderiv_le F i
  have hm := totalDegree_mul (C u) (pderiv i F)
  rw [totalDegree_C] at hm
  have hs := totalDegree_sub (C (a i ^ ell)) (C u * pderiv i F)
  rw [totalDegree_C] at hs
  change (C (a i ^ ell) - C u * pderiv i F).totalDegree < ell
  omega
end MvPolynomial.CriticalSystem
