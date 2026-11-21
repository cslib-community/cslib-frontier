/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootScanLedger
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt

open Cslib.Complexity.CountingSimulation Cslib.Circuits.Frontier

-- One shared source bound also covers a scan at every ancestor on the selected branch.
example (k states C rate : ℕ) :
    ∃ K, ∀ {t d m p : ℕ}, 2 ≤ rootEdges k states t →
      ContractionSchedule.Active C (rootEdges k states t) d m p →
      (d + 1) * (rate * (numBlocks t + 1)) ≤
        K * (t / (Nat.log 2 (t + 2)).sqrt + 1) := by
  obtain ⟨K, h⟩ := exists_repeated_root_charge k states C rate
  refine ⟨K, fun {t d m p} ht ha => ?_⟩
  have hdepth : d + 1 ≤ 16 ^ d :=
    (Nat.lt_two_pow_self (n := d)).trans_le (Nat.pow_le_pow_left (by decide : 2 ≤ 16) d)
  exact (Nat.mul_le_mul_right _ hdepth).trans (h ht ha)

-- This clock is not a power of two and has a partial last block.
example : blockLength 257 = 9 ∧ numBlocks 257 = 29 ∧
    (numBlocks 257 + 1) * (Nat.log 2 259).sqrt = 60 := by
  norm_num [numBlocks, blockLength, Nat.ceilDiv_eq_add_pred_div]
