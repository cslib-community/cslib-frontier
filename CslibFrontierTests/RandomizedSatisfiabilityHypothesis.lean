/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Computability.Complexity.FineGrained.RandomizedSatisfiabilityHypothesis

/-! Exercise the randomized SH interface at power `1 / 2` from an ordinary module client. -/

set_option linter.privateModule false

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.PromiseProblem Turing.MultiTapeTM

example (h : rSH) :
    ¬SolvesWithErrorInPowerExpTime (ofSet SAT) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length + φ.vars.length) (1 / 2) :=
  h _ (by norm_num) (by norm_num)

example (h : rSH) :
    ¬DecidableInPowerExpTime SAT encCNF (fun φ => φ.numVars + φ.length + φ.vars.length) (1 / 2) :=
  h.sh _ (by norm_num) (by norm_num)

-- The identity reduction allows the variable-plus-clause bound with the same power and error.
example (h : SolvesWithErrorInPowerExpTime (ofSet ThreeSAT) encCNF ErrorModel.bounded
    CNF.numVars (1 / 2)) :
    SolvesWithErrorInPowerExpTime (ofSet ThreeSAT) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length) (1 / 2) := by
  have hsize (φ : CNF ℕ) :
      (φ.numVars + 1 : ℝ) ≤ (↑(0 : ℕ) + 1 : ℝ) *
        ((φ.numVars + φ.length : ℕ) + 1 : ℝ) ^ (1 : ℝ) := by
    rw [Nat.cast_zero, zero_add, one_mul, Real.rpow_one]
    exact_mod_cast Nat.add_le_add_right (Nat.le_add_right φ.numVars φ.length) 1
  simpa only [one_mul] using h.of_polyTime_promiseReduction
    (r := id) (ComputableInPolyTime.id' : ComputableInPolyTime id encCNF encCNF)
    (A := ofSet ThreeSAT) (fun _ ha => ha) (fun _ ha => ha) (K := 0) hsize zero_le_one
    (by norm_num)
