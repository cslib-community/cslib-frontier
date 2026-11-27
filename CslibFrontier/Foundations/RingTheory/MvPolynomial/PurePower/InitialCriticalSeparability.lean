/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate (Mathlib, critical equations in pure-power quotients)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.CriticalValuePolynomial
public import Mathlib.FieldTheory.Separable
public import Mathlib.Analysis.Complex.Basic
import CslibFrontier.Foundations.RingTheory.MvPolynomial.PurePower.SeparatedCriticalValues
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Separability at the initial deformation parameter

At parameter zero, tuples of roots of unity give distinct values of the separated potential,
and each value is a characteristic root of the actual normalized quotient. The number of
distinct roots is the characteristic degree, which proves separability over the complex numbers.

Adapted from `InitialCriticalSeparable` and `ParametricCriticalSpecialization` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace MvPolynomial.CriticalSystem

open PurePower

/-- The symbolic critical-value characteristic polynomial specializes at zero to a
separable complex polynomial. -/
theorem parametricValuePolynomial_at_zero_separable {n ell : ℕ} (hell : 1 ≤ ell)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ ell) :
    ((parametricValuePolynomial hell F hF).map
      (Polynomial.eval₂RingHom (Int.castRingHom ℂ) 0)).Separable := by
  classical
  rw [parametricValuePolynomial_map_eval₂]
  let a (i : Fin n) : ℂ := separatedCenters ell i
  let G := F.map (Int.castRingHom ℂ)
  have hG : G.totalDegree ≤ ell := (totalDegree_map_le _ F).trans hF
  let r := criticalLower ell a 0 G
  let q := valuePolynomial hell a 0 G hG
  change q.Separable
  let ζ := Complex.exp (2 * Real.pi * Complex.I / ell)
  have hζ : IsPrimitiveRoot ζ ell := Complex.isPrimitiveRoot_exp ell (by omega)
  let z (b : NormalIndex n ell) (i : Fin n) := ζ ^ (b i).val
  let x (b : NormalIndex n ell) (i : Fin n) := a i * z b i
  let v (b : NormalIndex n ell) := eval (x b) (potentialPolynomial ell a)
  have hz (b : NormalIndex n ell) (i : Fin n) : z b i ^ ell = 1 := by
    dsimp only [z]
    rw [pow_right_comm, hζ.pow_eq_one, one_pow]
  have hv : Function.Injective v := by
    intro b c hbc
    have heq := eq_of_eval_potentialPolynomial_eq_of_pow_eq_one hell (hz b) (hz c) hbc
    funext i
    exact Fin.ext (hζ.pow_inj (b i).isLt (c i).isLt (congrFun heq i))
  have hroot (b : NormalIndex n ell) : q.IsRoot (v b) := by
    have hx (i : Fin n) : aeval (x b) (r i) = x b i ^ ell := by
      simp [r, criticalLower, x, mul_pow, hz]
    have h := isRoot_charpoly_multiplicationMatrix_of_aeval_eq hell r
      (criticalLower_degree ell hell a 0 G hG) (deformedPolynomial ell a 0 G) (x b) hx
    simpa [q, valuePolynomial, v, deformedPolynomial, aeval_eq_eval] using h
  have hq : q ≠ 0 := (valuePolynomial_monic hell a 0 G hG).ne_zero
  let root (b : NormalIndex n ell) : q.roots.toFinset :=
    ⟨v b, Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr (hroot b))⟩
  have hinj : Function.Injective root := fun _ _ h => hv (congrArg Subtype.val h)
  have hcard : Fintype.card (NormalIndex n ell) = q.natDegree := by
    rw [valuePolynomial_natDegree]
    simp [NormalIndex]
  have hle := Fintype.card_le_of_injective root hinj
  rw [hcard, Fintype.card_coe] at hle
  apply (Polynomial.nodup_roots_iff_of_splits hq (IsAlgClosed.splits q)).mp
  exact Multiset.toFinset_card_eq_card_iff_nodup.mp
    (le_antisymm (Multiset.toFinset_card_le q.roots) ((Polynomial.card_roots' q).trans hle))

end MvPolynomial.CriticalSystem
