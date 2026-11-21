/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededChildWitness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NormalForm
import Mathlib.Tactic.FinCases

open Cslib Turing Turing.MultiTapeTM SeededChildWitness

-- The linear seed assigns the endpoints 5 and 1 their own digits. The column edge
-- starts immediately after three row ports. Packet 321 starts after eight retained vertices.
private def col : Input :=
  ⟨⟨32, 1, 0, 1, 0, 0, 9, 0⟩, 0, 1, 3, (5, 1), (1, 329), ⟨2, 0, 3, 1, 8, 1⟩⟩

private def cases : Fin 5 → Input × Bool := ![
  (col, true), ({col with group := 5, child := 2}, true),
  ({col with child := 2}, false), ({col with answer := (1, 321)}, false),
  ({col with counts := {col.counts with classRank := 0}}, false)]

private theorem cases_run (i : Fin 5) : run (cases i).1 = (cases i).2 := by
  fin_cases i <;>
    simp only [cases, col, run, RootPortFinish.symbol, SeededPacketPlacement.run,
      SeededPacketPlacement.code, TrinomialArithmetic.runSelected, TrinomialArithmetic.hash4,
      TrinomialArithmetic.eval4, TrinomialArithmetic.mul, TrinomialArithmetic.reduce,
      clmul_eq_foldr_bits, Probability.trinomialStep, Probability.trinomialTargetBits,
      Probability.trinomialStepAux_eq_findGreatest] <;> decide

-- One finite machine checks all five claims, including both port orientations and wrong offsets.
example : ∃ (c d k : ℕ) (Q : Type) (_ : Finite Q) (tm : MultiTapeTM k Bool Q), ∀ i,
    let word := encInput (cases i).1
    let budget := c * (word.length + 1) ^ d
    tm.ComputesTidilyInTimeAndSpace word (encBool (cases i).2) budget budget := by
  obtain ⟨c, d, k, Q, hQ, tm, htm⟩ := Internal.NormalForm.polyTime computableInPolyTime_run
  exact ⟨c, d, k, Q, hQ, tm, fun i => by simpa only [cases_run] using htm (cases i).1⟩

-- The word round-trips with another phase's choices appended, including for a high rank bit.
example (tail : List Bool) :
    let p : Proposal := ⟨3, (6, 9), ⟨1, 2, 3, 4, 5, 2 ^ 70⟩⟩
    parse 71 (word 71 p ++ tail) = p := by
  exact parse_word _ _ (by simp [Proposal.fields]) _

-- With zero width, the existential machine chooses the unique all-zero tuple.
example : Turing.MultiTapeATM.QuantifiedWord.plays
    (fun xs => (parse 0 xs).fields = List.replicate 9 0) [] (List.replicate (9 * 0) false) := by
  apply (Turing.MultiTapeATM.SeededChildCounts.plays_proposal 0
    (fun p => p.fields = List.replicate 9 0)).2
  exact ⟨⟨0, (0, 0), ⟨0, 0, 0, 0, 0, 0⟩⟩, by simp [Proposal.fields], rfl⟩
