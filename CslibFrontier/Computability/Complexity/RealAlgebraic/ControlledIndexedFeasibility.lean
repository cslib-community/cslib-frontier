/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledPositivity
import CslibFrontier.Computability.Complexity.RealAlgebraic.ControlledBoundedSum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic

/-!
# One controlled polynomial for indexed real feasibility

A system with binary-addressed equations and strict inequalities has a single
sum-of-squares equation. One auxiliary variable per strict inequality realizes its
positivity test. When the row families have common polynomial-time bounds, the
resulting modular evaluator costs one additional counting level.

Adapted from lean-canny's `IndexedEquationPositivity` and `ControlledIndexedSystem`
at `970f28a5ecefc1327402ade16c068aa4b1b2c183`.
-/

public section

namespace Cslib.Complexity.RealAlgebraic

open Turing.MultiTapeTM ComputableInPolyTime MvPolynomial
open scoped BigOperators

/-- Sum the squared equations and the squared auxiliary equations for strict inequalities.
The first `n` variables are original. The final `k` variables serve the strict inequalities. -/
noncomputable def indexedFeasibilityPolynomial {n : ℕ}
    (P Q : ℕ → MvPolynomial (Fin n) ℤ) (e k : ℕ) : MvPolynomial (Fin (n + k)) ℤ :=
  (∑ j ∈ Finset.range e, MvPolynomial.rename (Fin.castAdd k) (P j) ^ 2) +
    ∑ j ∈ Finset.range k, positivityEquation (Q j) k j ^ 2

/-- Assemble a controlled feasibility polynomial at one extra counting level.
The equation count is binary. The inequality count is unary because it determines the
size of the auxiliary variable block. The common bounds need only hold for rows in range. -/
noncomputable def Controlled.indexedFeasibility {α : Type} {n : α → ℕ}
    {enc : α ↪ List Bool} {a : ℕ} {P Q : (q : α × ℕ) → MvPolynomial (Fin (n q.1)) ℤ}
    (CP : Controlled P (encPair enc encNat) a) (CQ : Controlled Q (encPair enc encNat) a)
    (E : Decoder enc) (e k D b cutoff : α → ℕ)
    (he : ComputableInPolyTime e enc encNat) (hk : ComputableInPolyTime k enc encUnary)
    (hD : ComputableInPolyTime D enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (hcut : ComputableInPolyTime cutoff enc encNat)
    (hPdeg : ∀ w j, j < e w → (P (w, j)).totalDegree ≤ D w)
    (hQdeg : ∀ w j, j < k w → (Q (w, j)).totalDegree ≤ D w)
    (hPmass : ∀ w j, j < e w → (P (w, j)).coeffNorm1 ≤ 2 ^ b w)
    (hQmass : ∀ w j, j < k w → (Q (w, j)).coeffNorm1 ≤ 2 ^ b w)
    (hPcut : ∀ w j, j < e w → CP.cutoff (w, j) ≤ cutoff w)
    (hQcut : ∀ w j, j < k w → CQ.cutoff (w, j) ≤ cutoff w) :
    Controlled (fun w => indexedFeasibilityPolynomial (fun j => P (w, j)) (fun j => Q (w, j))
      (e w) (k w)) enc (a + 1) :=
  let hn : ComputableInPolyTime n enc encUnary := CP.arity_computable.comp (id'.prod (.const 0))
  let hvars := unary_add' hn hk
  let Ppad := CP.appendVariables (fun q => k q.1) (hk.comp (fst enc encNat))
  let Qeq := CQ.positivityEquations k hk
  let Psquares := Ppad.sumSquares (P := fun w j => MvPolynomial.rename (Fin.castAdd (k w))
      (P (w, j))) E hvars e D b cutoff he hD hb hcut
    (fun w j hj => (totalDegree_rename_le _ _).trans (hPdeg w j hj))
    (fun w j hj => (coeffNorm1_rename_le _ _).trans (hPmass w j hj))
    (fun w j hj => by simpa only [Ppad, Controlled.cutoff_appendVariables] using hPcut w j hj)
  let hmass (w : α) (j : ℕ) (hj : j < k w) :
      (positivityEquation (Q (w, j)) (k w) j).coeffNorm1 ≤ 2 ^ (b w + 1) := by
    apply (coeffNorm1_positivityEquation_le _ _ _).trans
    have hpow : 1 ≤ 2 ^ b w := Nat.one_le_two_pow
    rw [pow_succ, Nat.mul_two]
    exact Nat.add_le_add (hQmass w j hj) hpow
  let Qsquares := Qeq.sumSquares (P := fun w j => positivityEquation (Q (w, j)) (k w) j)
    E hvars k (fun w => D w + 2) (fun w => b w + 1) cutoff (unary_to_binary.comp hk)
    (binary_add' hD (.const 2)) (binary_add' hb (.const 1)) hcut
    (fun w j hj => (totalDegree_positivityEquation_le _ _ _).trans
      (Nat.add_le_add_right (hQdeg w j hj) 2)) hmass
    (fun w j hj => by simpa only [Qeq, Controlled.cutoff_positivityEquations] using hQcut w j hj)
  Psquares.add Qsquares

attribute [local irreducible] indexedFeasibilityPolynomial

/-- Evaluate the squared equation rows on the original coordinates and the squared positivity
rows using their respective auxiliary coordinates. -/
theorem eval₂_indexedFeasibilityPolynomial {n : ℕ} {R : Type*} [CommRing R] (f : ℤ →+* R)
    (P Q : ℕ → MvPolynomial (Fin n) ℤ) (e k : ℕ) (z : Fin (n + k) → R) :
    MvPolynomial.eval₂ f z (indexedFeasibilityPolynomial P Q e k) =
      (∑ j ∈ Finset.range e, MvPolynomial.eval₂ f (fun i => z (i.castAdd k)) (P j) ^ 2) +
        ∑ i : Fin k,
          (MvPolynomial.eval₂ f (fun j => z (j.castAdd k)) (Q i.val) *
            z (i.natAdd n) ^ 2 - 1) ^ 2 := by
  simp only [indexedFeasibilityPolynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_pow, MvPolynomial.eval₂_rename, Function.comp_def]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpoint : Fin.addCases (fun j : Fin n => z (j.castAdd k))
      (fun j : Fin k => z (j.natAdd n)) = z := funext (Fin.addCases_castAdd_natAdd z)
  rw [← eval₂_positivityEquation f (Q i.val) (fun j => z (j.castAdd k))
    (fun j => z (j.natAdd n)) i, hpoint]

private theorem eval₂_indexedFeasibilityPolynomial_zero_iff {n : ℕ}
    (P Q : ℕ → MvPolynomial (Fin n) ℤ) (e k : ℕ) (x : Fin n → ℝ) (s : Fin k → ℝ) :
    MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases x s)
      (indexedFeasibilityPolynomial P Q e k) = 0 ↔
    (∀ j < e, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P j) = 0) ∧
      ∀ j < k, MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases x s)
        (positivityEquation (Q j) k j) = 0 := by
  simp only [eval₂_indexedFeasibilityPolynomial, Fin.addCases_left, Fin.addCases_right]
  simp_rw [← eval₂_positivityEquation (Int.castRingHom ℝ) _ x s]
  rw [add_eq_zero_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  simp only [Finset.sum_sq_eq_zero_iff, Finset.mem_range, Finset.mem_univ, true_implies,
    Fin.forall_iff]

/-- The combined polynomial has a real zero exactly when the original equations and strict
inequalities are feasible. The auxiliary coordinates can be chosen independently. -/
theorem exists_indexedFeasibilityPolynomial_zero_iff {n : ℕ}
    (P Q : ℕ → MvPolynomial (Fin n) ℤ) (e k : ℕ) :
    (∃ z : Fin (n + k) → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) z (indexedFeasibilityPolynomial P Q e k) = 0) ↔
    ∃ x : Fin n → ℝ, (∀ j < e, MvPolynomial.eval₂ (Int.castRingHom ℝ) x (P j) = 0) ∧
      ∀ j < k, 0 < MvPolynomial.eval₂ (Int.castRingHom ℝ) x (Q j) := by
  constructor
  · rintro ⟨z, hz⟩
    let x (i : Fin n) := z (i.castAdd k)
    let s (i : Fin k) := z (i.natAdd n)
    have hpoint : Fin.addCases x s = z := funext (Fin.addCases_castAdd_natAdd z)
    have hzero : MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases x s)
        (indexedFeasibilityPolynomial P Q e k) = 0 := by
      rw [hpoint]
      exact hz
    obtain ⟨hP, hQ⟩ := (eval₂_indexedFeasibilityPolynomial_zero_iff P Q e k x s).mp hzero
    exact ⟨x, hP, (exists_positivityEquations_zero_iff Q k x).mp ⟨s, hQ⟩⟩
  · rintro ⟨x, hx, hxQ⟩
    obtain ⟨s, hs⟩ := (exists_positivityEquations_zero_iff Q k x).mpr hxQ
    have hzero := (eval₂_indexedFeasibilityPolynomial_zero_iff P Q e k x s).mpr ⟨hx, hs⟩
    let z : Fin (n + k) → ℝ := Fin.addCases x s
    exact ⟨z, hzero⟩

end Cslib.Complexity.RealAlgebraic
