/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree.Slices
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Roots

/-! # A diagonal slice retains the original line degree -/

set_option linter.privateModule false

open Cslib.PCP.LowIndividualDegree Polynomial

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private abbrev F := ZMod 3
private abbrev L := linePoints (0 : Point F 1) (1 : Point F 1)

private def square (u : L) : F := (u.val 0) ^ 2

private theorem degree_two : LineHasDegree square 2 := by
  refine ⟨0, 1, rfl, X ^ 2, by simp, fun t => ?_⟩
  simp [square, Pi.smul_apply, smul_eq_mul]

private theorem not_degree_one : ¬ LineHasDegree square 1 := by
  intro h
  obtain ⟨p, hp, he⟩ := h.exists_polynomial
  have hEval (t : F) : p.eval t = ((X : Polynomial F) ^ 2).eval t := by
    simpa [square, Pi.smul_apply, smul_eq_mul] using (he t).symm
  have hEq : p = (X : Polynomial F) ^ 2 := by
    apply eq_of_natDegree_lt_card_of_eval_eq p _ Function.injective_id hEval
    rw [natDegree_X_pow, ZMod.card]
    omega
  rw [hEq, natDegree_X_pow] at hp
  omega

/-- For `d = 1` the two-coordinate cap is two and the one-coordinate cap is one.
The larger diagonal predicate accepts the quadratic answer, but the smaller one rejects it. -/
example :
    lineAgrees 2 (appendLine (0 : F) L) (appendPoint 0 0) (appendLineAnswer 0 ⟨L, square⟩) 0 ∧
      ¬ lineAgrees 1 L 0 ⟨L, square⟩ 0 := by
  constructor
  · apply (lineAgrees_append_iff 0 0 1 0 2 square 0).mpr
    refine ⟨rfl, degree_two, ?_⟩
    have hzero : (0 : Point F 1) ∈ L := by
      simpa using mem_linePoints (0 : Point F 1) (1 : Point F 1) (0 : F)
    exact ⟨hzero, by simp [square]⟩
  · exact fun h => not_degree_one h.2.1
