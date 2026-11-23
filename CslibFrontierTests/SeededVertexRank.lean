/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.SeededVertexRank

public section

open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery
open Turing.MultiTapeATM QuantifiedWord SeededVertexRank

private def seed : SeededLabels.Seed 1 6 := fun _ => 0
private noncomputable def group : ℕ := (Labels.ofSeed 1 1 seed 0 0).symbol 0
private def parent : EndpointQuery := ⟨0, fun _ _ => False⟩

private theorem rank_one : ((Labels.ofSeed 1 1 seed 0 group).split parent).vertexRank 5 = 1 := by
  have hg : ((Labels.ofSeed 1 1 seed 0 group).split parent).label 0 = group := rfl
  change ([0] : List ℕ).countP
    (fun v => decide (((Labels.ofSeed 1 1 seed 0 group).split parent).label v = group)) = 1
  simp [hg]

/-- A one-vertex universe uses a fixed word, even when the supplied prefix is empty. -/
theorem Turing.MultiTapeATM.SeededVertexRank.Tests.singleton_flags :
    flags 1 = [false, false, true] := by decide

/-- The first retained vertex has no predecessors in its exclusive prefix. -/
example : plays (fun xs => program (Query.ofSeed (a := 1) seed 0 group 0 0, xs) = true) []
    (flags 1) :=
  (plays_program (a := 1) seed 0 group 0 0 parent).2 (by simp [Split.vertexRank])

/-- A prefix beyond the universe still counts exactly its one vertex. -/
example : plays (fun xs => program (Query.ofSeed (a := 1) seed 0 group 5 1, xs) = true) []
    (flags 1) :=
  (plays_program (a := 1) seed 0 group 5 1 parent).2 rank_one.symm

/-- The same quantified machine rejects an oversized proposed retained count. -/
example : ¬ plays (fun xs => program (Query.ofSeed (a := 1) seed 0 group 5 2, xs) = true) []
    (flags 1) := by
  rw [plays_program (a := 1) seed 0 group 5 2 parent, rank_one]
  decide

/-- No choices are needed for an empty universe, whose only accepted total is zero. -/
example (s : SeededLabels.Seed 0 6) (g bound value : ℕ) :
    plays (fun xs => program (Query.ofSeed (a := 1) s 0 g bound value, xs) = true) [] (flags 0) ↔
      value = 0 := by
  rw [plays_program (a := 1) s 0 g bound value parent]
  simp [Split.vertexRank, Labels.split, Labels.ofSeed]
