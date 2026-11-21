/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorQuery
import Mathlib.Tactic.FinCases

open Cslib Turing Turing.MultiTapeTM RootPredecessorQuery

private def requestAt (raw : List Bool) (edge candidate : ℕ) : Input :=
  ⟨raw, 1, ⟨32, 0, 0, 0, 0, 0, edge, candidate⟩⟩

private def cases : Fin 4 → Input × Bool := ![
  (requestAt (List.replicate 8 false) 10 0, true),
  (requestAt (List.replicate 8 false) 10 10, false),
  (requestAt [false, false, true, true] 1 0, false),
  (requestAt (List.replicate 8 false) (2 ^ 100) 0, false)]

private theorem query_cases (i : Fin 4) : query 1 (cases i).1 = (cases i).2 := by
  fin_cases i
  · change SeededPredecessorFinish.run ⟨_, some (1, 12), some (0, 10)⟩ = true
    simp only [SeededPredecessorFinish.run_some, SeededPredecessor.test,
      SeededPredecessor.hash, TrinomialArithmetic.runSelected, TrinomialArithmetic.hash4,
      TrinomialArithmetic.eval4, TrinomialArithmetic.mul, TrinomialArithmetic.reduce,
      clmul_eq_foldr_bits, Probability.trinomialStep, Probability.trinomialTargetBits,
      Probability.trinomialStepAux_eq_findGreatest]
    decide
  · change SeededPredecessorFinish.run ⟨_, some (1, 12), some (1, 12)⟩ = false
    simp [SeededPredecessor.test, SeededPredecessor.Context.withEndpoints, cases, requestAt]
  · rfl
  · rfl

-- Empty labels put all genuine edges in one label class. The same native machine must accept
-- the earlier genuine candidate, reject self-comparison, and reject malformed or padded inputs.
example : ∃ (d c K : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM K Bool Q), ∀ i,
    let a := (cases i).1
    let budget := c * (a.raw.length + shortSize a ^ d + 1)
    tm.ComputesInTimeAndSpace (encInput a) (encBool (cases i).2) budget budget := by
  obtain ⟨d, c, ⟨K, Q, hQ, tm, htm⟩, _⟩ := exists_computableInO 1
  exact ⟨d, c, K, Q, hQ, tm, fun i => by simpa only [query_cases] using htm (cases i).1⟩
