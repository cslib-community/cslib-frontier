/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.GeneralIntegerProgramming
public import CslibFrontier.Computability.Complexity.Problems.IntegerProgramming
import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-!
# NP-completeness of integer inequality feasibility

The reduction from zero-one equality programming replaces each equality by its two inequalities
and imposes `0 ≤ x j ≤ 1`. The target allows arbitrary integer assignments; the added rows
force exactly the Boolean assignments needed by the source problem.

This proves the integer-coefficient feasibility problem in [Goldreich, Exercise 2.23,
printed p. 110 / PDF p. 135 of the December 2006 draft][Goldreich2007Draft]. The native
multitape model uses a unary dimension and signed-binary coefficient lists; the encoding is
`IntegerProgram.enc`. The source leaves its reasonable instance encoding implicit. This does
not define rational-coefficient inputs or certify a denominator-clearing algorithm.

## Main results

* `Cslib.Complexity.IntegerProgram.ofZeroOne_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.IntegerProgram.computableInPolyTime_ofZeroOne`: native polynomial time.
* `Cslib.Complexity.IntegerProgram.npComplete`: integer inequality feasibility is NP-complete.
-/

public section

namespace Cslib.Complexity
open Finset Turing.MultiTapeTM ComputableInPolyTime

namespace IntegerProgram

private def unitCoeffs (n j : ℕ) (s : ℤ) : List ℤ :=
  (List.range n).map fun k => if k = j then s else 0

private lemma sum_unitCoeffs {n j : ℕ} (hj : j < n) (s : ℤ) (x : Fin n → ℤ) :
    ∑ k : Fin n, (unitCoeffs n j s).getD k 0 * x k = s * x ⟨j, hj⟩ := by
  have heq : ∀ k : Fin n, (unitCoeffs n j s).getD k 0 = if k = ⟨j, hj⟩ then s else 0 := by
    intro k
    simp [unitCoeffs, List.getD_eq_getElem?_getD, Fin.ext_iff, k.isLt]
  simp only [heq, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Convert zero-one equalities into unrestricted integer inequalities: the encoded source
length is the unary target dimension; each equality has both signs, and every variable has
upper bound one and lower bound zero. -/
def ofZeroOne (C : List ZeroOneIP.Equation) : IntegerProgram :=
  let n := (encZeroOneIP C).length
  ⟨n, (C.flatMap fun c =>
      [⟨c.coeffs.map (fun (a : ℕ) => (a : ℤ)), c.rhs⟩,
       ⟨c.coeffs.map (fun (a : ℕ) => -(a : ℤ)), -(c.rhs : ℤ)⟩]) ++
    ((List.range n).flatMap fun j =>
      [⟨unitCoeffs n j 1, 1⟩, ⟨unitCoeffs n j (-1), 0⟩])⟩

private lemma ofZeroOne_feasible_iff (C : List ZeroOneIP.Equation) :
    ofZeroOne C ∈ Feasible ↔ ∃ x : Fin (encZeroOneIP C).length → ℤ,
      (∀ j, 0 ≤ x j ∧ x j ≤ 1) ∧
      ∀ c ∈ C, ∑ j : Fin (encZeroOneIP C).length, (c.coeffs.getD j 0 : ℤ) * x j = c.rhs := by
  have hpos (a : List ℕ) (j : ℕ) :
      (a.map (fun (a : ℕ) => (a : ℤ))).getD j 0 = (a.getD j 0 : ℤ) :=
    List.getD_map (l := a) (d := 0) (n := j) (fun (a : ℕ) => (a : ℤ))
  have hneg (a : List ℕ) (j : ℕ) :
      (a.map (fun (a : ℕ) => -(a : ℤ))).getD j 0 = -(a.getD j 0 : ℤ) :=
    List.getD_map (l := a) (d := 0) (n := j) (fun (a : ℕ) => -(a : ℤ))
  simp only [Feasible, Set.mem_ofPred_eq, ofZeroOne, List.mem_append, List.mem_flatMap,
    List.mem_cons, List.not_mem_nil, or_false, List.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, fun j => ?_, fun c hc => ?_⟩
    · have h1 := hx _ (Or.inr ⟨j.val, j.isLt, Or.inl rfl⟩)
      have h2 := hx _ (Or.inr ⟨j.val, j.isLt, Or.inr rfl⟩)
      simp only [sum_unitCoeffs j.isLt, one_mul, neg_one_mul] at h1 h2
      exact ⟨by linarith, h1⟩
    · have h1 := hx _ (Or.inl ⟨c, hc, Or.inl rfl⟩)
      have h2 := hx _ (Or.inl ⟨c, hc, Or.inr rfl⟩)
      simp only [hpos, hneg, neg_mul,
        Finset.sum_neg_distrib] at h1 h2
      omega
  · rintro ⟨x, hx, hC⟩
    refine ⟨x, fun c hc => ?_⟩
    rcases hc with ⟨c, hc, rfl | rfl⟩ | ⟨j, hj, rfl | rfl⟩
    · simpa only [hpos] using (hC c hc).le
    · simpa only [hpos, hneg, neg_mul,
        Finset.sum_neg_distrib] using neg_le_neg (hC c hc).ge
    · simpa only [sum_unitCoeffs hj, one_mul] using (hx ⟨j, hj⟩).2
    · simpa only [sum_unitCoeffs hj, neg_one_mul, neg_nonpos] using (hx ⟨j, hj⟩).1

/-- Correctness of the zero-one-to-integer-inequality reduction. -/
theorem ofZeroOne_mem_iff (C : List ZeroOneIP.Equation) :
    ofZeroOne C ∈ Feasible ↔ C ∈ ZeroOneIP := by
  classical
  let n := (encZeroOneIP C).length
  have hlen : ∀ c ∈ C, c.coeffs.length ≤ n := fun c hc =>
    (length_le_length_encList _ _).trans ((ZeroOneIP.encEquation_coeffs_length_le c).trans
      (length_le_encList_of_mem _ hc))
  have hsum (c : ZeroOneIP.Equation) (hc : c ∈ C) (x : ℕ → ℤ) :
      ∑ j : Fin n, (c.coeffs.getD j 0 : ℤ) * x j =
      ∑ j ∈ range c.coeffs.length, (c.coeffs.getD j 0 : ℤ) * x j :=
    Fin.sum_eq_sum_range_of_eq_zero (hlen c hc)
      (fun j => (c.coeffs.getD j 0 : ℤ) * x j) fun j hj => by
      rw [List.getD_eq_default _ _ hj, Nat.cast_zero, zero_mul]
  rw [ofZeroOne_feasible_iff]
  constructor
  · rintro ⟨x, hx, hC⟩
    let z : ℕ → ℤ := fun j => if hj : j < n then x ⟨j, hj⟩ else 0
    have hz : ∀ j, z j = 0 ∨ z j = 1 := by
      intro j
      by_cases hj : j < n
      · have h := hx ⟨j, hj⟩
        simpa only [z, dite_eq_left hj] using
          (show x ⟨j, hj⟩ = 0 ∨ x ⟨j, hj⟩ = 1 by omega)
      · simp [z, hj]
    refine ⟨fun j => decide (z j = 1), fun c hc => ?_⟩
    have h := hC c hc
    have h' : ∑ j : Fin n, (c.coeffs.getD j 0 : ℤ) * z j = c.rhs := by
      simpa only [z, Fin.is_lt, dite_true, Fin.eta] using h
    rw [hsum c hc z] at h'
    have heq : ∀ j, ((decide (z j = 1)).toNat : ℤ) = z j := by
      intro j
      rcases hz j with h | h <;> simp [h]
    apply Int.ofNat_inj.mp
    push_cast
    simpa only [heq] using h' 
  · rintro ⟨x, hx⟩
    refine ⟨fun j => ((x j).toNat : ℤ), fun j => ?_, fun c hc => ?_⟩
    · have h := Bool.toNat_le (x j)
      exact ⟨by positivity, show ((x j.val).toNat : ℤ) ≤ 1 by exact_mod_cast h⟩
    · have h := hx c hc
      have h' : ∑ j ∈ range c.coeffs.length,
          (c.coeffs.getD j 0 : ℤ) * ((x j).toNat : ℤ) = c.rhs := by exact_mod_cast h
      rwa [← hsum c hc (fun j => ((x j).toNat : ℤ))] at h'

open scoped ZeroOneIP IntegerProgram in
/-- The reduction to integer inequalities runs in native polynomial time. -/
theorem computableInPolyTime_ofZeroOne :
    ComputableInPolyTime ofZeroOne encZeroOneIP enc := by
  have hlen : ComputableInPolyTime (fun C => (encZeroOneIP C).length)
      encZeroOneIP encUnary := encoding_length encZeroOneIP
  unfold ofZeroOne unitCoeffs
  apply enc_mk_polyTime hlen
  apply listAppend' ?_ ?_
  · apply flatMapWithInput (by fun_prop)
    fun_prop
  · apply flatMapWithInput (by fun_prop)
    fun_prop

/-- Integer inequality feasibility is NP-complete, with unrestricted integer unknowns, unary
dimension and signed-binary integer coefficients [Goldreich, Exercise 2.23][Goldreich2007Draft]. -/
theorem npComplete : NPComplete enc Feasible :=
  ⟨mem_NP, ZeroOneIP_npHard.trans
    ⟨ofZeroOne, computableInPolyTime_ofZeroOne, fun C => (ofZeroOne_mem_iff C).symm⟩⟩

end IntegerProgram
end Cslib.Complexity
