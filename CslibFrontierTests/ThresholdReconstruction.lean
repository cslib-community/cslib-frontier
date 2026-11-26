/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Circuit.Boolean.ThresholdReconstruction

/-!
# Threshold reconstruction boundary checks

The native circuit witness uses the window `[3, 5]` modulo four, whose image crosses zero.
It computes the threshold at three on all three-bit inputs, including weights below the lower
promise, in the uncertainty interval and at the exact threshold. Separate scalar checks cover
the upper endpoint and show why zero-radius boundary promises cannot hold at the threshold.
-/

set_option linter.privateModule false

open Cslib Cslib.Circuits Cslib.Circuits.Boolean
open ThresholdReconstruction

-- A modular interval must include the residues after crossing a multiple of the modulus.
example : residueTest 3 1 4 4 = true := by decide
example : residueTest 3 1 4 5 = true := by decide
example : residueTest 3 1 4 2 = false := by decide

-- Both approximate comparisons settle the far regions even when the residue vote is wrong.
example : maj3 false false (residueTest 7 1 4 3) = false := by decide
example : maj3 true true (residueTest 7 1 4 10) = true := by decide

-- Exact and uncertainty boundaries at k - 2t, k - 1, k, k + 2t - 1, k + 2t.
example : maj3 false false (residueTest 7 1 4 5) = false := by decide
example : ∀ lower : Bool, maj3 lower false (residueTest 7 1 4 6) = false := by decide
example : maj3 true false (residueTest 7 1 4 7) = true := by decide
example : ∀ upper : Bool, maj3 true upper (residueTest 7 1 4 8) = true := by decide
example : maj3 true true (residueTest 7 1 4 9) = true := by decide

-- If the mathematical lower endpoint is negative, its zero promise is empty, not truncated.
example : ∀ lower : Bool, maj3 lower false (residueTest 1 1 4 0) = false := by decide

-- At t = 0 the two boundary promises for a comparison contradict each other at w = k.
example (lower : Bool)
    (hzero : 3 + 2 * 0 ≤ 3 → lower = false) (hone : 3 ≤ 3 → lower = true) : False := by
  have h0 := hzero (by decide)
  have h1 := hone (by decide)
  simp_all

private def lower : Formula signature 3 :=
  ((Formula.input 0).and (.input 1)).and (.input 2)

private def upper : Circuit signature 3 1 :=
  Circuit.oneGate (.const false) Fin.elim0

private def residue : Formula signature 3 :=
  (((Formula.input 0).xor (.input 1)).xor (.input 2)).or
    (((Formula.input 0).or ((Formula.input 1).or (.input 2))).not)

-- A full-domain native circuit witness whose modular window crosses zero.
example : (circuit lower.toCircuit upper residue.toCircuit).Computes interpretation
    (single (threshold 3 3)) := by
  refine computes_threshold_of_approx _ _ _ (t := 1) (R := 4) (by decide) ?_ ?_ ?_ ?_ ?_
  all_goals
    intro x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
      simp only [lower, upper, residue, Formula.eval_toCircuit, Formula.eval_and, Formula.eval_or,
        Formula.eval_not, Formula.eval_xor, Formula.eval_input, Circuit.eval_oneGate,
        BitString.weight_eq_sum_toNat, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two, h0, h1, h2, interpretation] <;> decide
