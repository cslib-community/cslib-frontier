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

example (h : rSH) :
    ¬SolvesWithErrorInPowerExpTime (ofSet (KSAT 4)) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length) (1 / 2) :=
  (rSH_iff_KSAT (k := 4) (by decide)).mp h _ (by norm_num) (by norm_num)

example (h : ∀ p : ℝ, 0 < p → p < 1 →
    ¬SolvesWithErrorInPowerExpTime (ofSet ThreeSAT) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length) p) : rSH :=
  (rSH_iff_KSAT (k := 3) le_rfl).mpr h

-- The general transfer applies at a fixed exponent to a concrete deterministic reduction.
example (h : rSH) :
    ¬SolvesWithErrorInPowerExpTime (ofSet ThreeSAT) encCNF ErrorModel.bounded
      (fun φ => φ.numVars + φ.length) (1 / 2) := by
  have hpoly : ComputableInPolyTime id encCNF encCNF := ComputableInPolyTime.id'
  obtain ⟨e, he⟩ := ComputableInExpTime.of_computableInPolyTime (μ := fun _ => 0) hpoly
  refine h.not_solvesWithErrorInPowerExpTime_of_reduction (f := id) (q := 0) (b := 1)
    zero_lt_one zero_lt_one (by norm_num) (by norm_num)
    ⟨0, e, by simpa only [Nat.cast_zero, zero_mul] using he⟩
    (fun _ hφ => hφ) (fun _ hφ => hφ) ?_
  intro η hη
  refine ⟨0, fun φ => ?_⟩
  have hbase : (1 : ℝ) ≤ ((φ.numVars + φ.length : ℕ) + 1 : ℝ) :=
    le_add_of_nonneg_left (Nat.cast_nonneg _)
  rw [Nat.cast_zero, zero_add, one_mul]
  simpa only [id_eq, Real.rpow_one] using
    Real.rpow_le_rpow_of_exponent_le hbase (show (1 : ℝ) ≤ 1 + η from le_add_of_nonneg_right hη.le)

-- A unary input supplies the repetition schedule. At input 1, two zero-bit trials agree.
example :
    acceptCount (fun p : ℕ × List Bool =>
      Cslib.BitString.listStrictMajority (repeatVotes (2 * p.1) 0 (fun _ => true) p) != true)
      1 0 = 0 := by
  have hr : ComputableInO (fun n : ℕ => n) encUnary encUnary
      (fun n => (encUnary n).length) (fun n => (encUnary n).length) :=
    ComputableInO.of_eq fun _ => rfl
  have hV := ComputableInO.const (encIn := encPair encUnary encBits) (encMid := encBool) true
  obtain ⟨_, _, _, _, _, _, _, herr⟩ := computableInO_amplifySeededMajority
    (ComputableInO.const (encMid := encUnary) 0) hr hV
    (R := fun a => (encPair encUnary encBits (a, [])).length)
    (fun a w hw => by
      obtain rfl := List.length_eq_zero_iff.mp hw
      exact le_rfl)
  have h := herr 1 true (ε := 0) le_rfl (by norm_num) (by simp)
  simp only [pow_one, pow_zero, mul_zero, zero_mul] at h
  exact Nat.eq_zero_of_le_zero (by exact_mod_cast h)
