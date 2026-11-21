/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.RootBalanceTime

open Cslib.Complexity.CountingSimulation Turing Turing.MultiTapeATM

-- The source-time clock is uniform in the schedule, label length, seed and both source inputs.
example (k states : ℕ) : ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q)
    (K : ℕ), VerifiesRootBalance atm k states
      (fun t => K * (t / (Nat.log 2 (t + 2)).sqrt + 2)) :=
  exists_rootBalance_verifier_div_sqrt_log k states

-- The additive allowance also bounds the smallest finite clocks.
example : ∀ t ∈ [0, 1, 2, 3, 4], numBlocks t + 1 ≤ t / (Nat.log 2 (t + 2)).sqrt + 2 := by
  intro t _
  exact Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one t)

-- A consumer can unpack the public specification for an individual proposed seed and schedule.
example {u k states : ℕ} {Q : Type} {atm : MultiTapeATM u Bool Q} (clock : ℕ → ℕ)
    (h : VerifiesRootBalance atm k states clock) {S : Type} (M : MultiTapePTM k Bool S)
    (st : S ≃ Fin states) (input : List Bool) (t σ a : ℕ) (ha : 64 ^ a ≤ rootEdges k states t)
    (seed : Cslib.BalancedSchedules.SeededLabels.Seed (rootVertices k states t) (6 * a)) :
    atm.HaltsWithin (clock t) (atm.toPTM.toNTM.initCfg (MultiTapeTM.RootBalanceRequest.encPublic
      (RootPackingBalance.graphPublic k (numBlocks t) (rootCopies k states t) σ a seed))) :=
  (h M st input t σ a ha seed).1
