/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Computability.PropertyTesting.Majority
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # Clients of the strict majority tester -/

namespace Cslib.BitString

open scoped BigOperators

-- Two ones suffice at length three. The same probe budget rejects the far all-zero string.
example :
    (2 / 3 : ℝ) ≤ (majorityTester 3 64 (1 / 2)).acceptProb (fun i => decide (i.val < 2)) ∧
    (majorityTester 3 64 (1 / 2)).acceptProb (fun _ => false) ≤ 1 / 3 := by
  have h := majorityTester_spec (n := 3) (k := 64) (δ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨h.2.1 _ ?_, h.2.2 _ ?_⟩
  · decide
  · intro y hy
    have hweight := strictMajority_eq_true_iff.mp hy
    change _ ≤ (hammingDist (0 : BitString 3) y : ℝ)
    rw [hammingDist_zero_left, ← weight_eq_hammingNorm]
    have htwo : (2 : ℝ) ≤ weight y := by exact_mod_cast hweight
    norm_num
    linarith

-- Length zero has no members, so even its vacuous farness promise gets a rejection bound.
example (δ : ℝ) (hδ : 0 < δ) :
    ∃ (k : ℕ) (T : (Fin k → BitString (Nat.log 2 0 + 1)) → DecisionTree (Fin 0) Bool),
      (∀ r, (T r).depth ≤ k) ∧
      ∀ x, (𝔼 r, if (T r).eval x = true then (1 : ℝ) else 0) ≤ 1 / 3 := by
  obtain ⟨k, T, hdepth, _, hno⟩ := exists_majorityTester_probeBound hδ
  refine ⟨k, T 0, hdepth 0, fun x => hno 0 x ?_⟩
  intro y hy
  have := strictMajority_eq_true_iff.mp hy
  have := weight_le_length y
  omega

end Cslib.BitString
