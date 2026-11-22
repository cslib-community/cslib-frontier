/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

import CslibFrontier.Computability.Complexity.Problems.NCL.PSPACE.EdgeToEdge

/-! One-move legality and the polynomial-space membership theorem. -/

open Cslib.Complexity Cslib.Complexity.NCL

namespace CslibFrontierTests.NCL

open Turing.MultiTapeTM

example {E : Type} (encE : E ↪ List Bool) (p : Port E) :
    encPort encE p = encPair encE encBool (p.edge, p.dir) := rfl

example {E : Type} (encE : E ↪ List Bool) (v : Vertex E) :
    encVertex encE v =
      encPair (encList (encPair (encPort encE) encNat)) encNat (v.ports, v.minInflow) := rfl

private def graphData : AndOrGraph :=
  ⟨[.or ⟨0, true⟩ ⟨1, true⟩ ⟨2, true⟩,
    .or ⟨0, false⟩ ⟨1, false⟩ ⟨2, false⟩], 3⟩

private theorem valid : graphData.Valid :=
  (AndOrGraph.checkValid_eq_true_iff _).1 (by decide +kernel)

example : graphData.checkStep [true, false, false] [true, true, false] = true := by decide +kernel

example : graphData.checkStep [true, false, false] [true, false, false] = false := by decide +kernel

example : graphData.checkStep [true, false, false] [false, true, false] = false := by decide +kernel

-- Declaring an extra edge introduces an index with no endpoints.
example : AndOrGraph.checkValid {graphData with edgeCount := 4} = false := by decide +kernel

private theorem one_move : graphData.graph.Step
    (graphData.config [true, false, false]) (graphData.config [true, true, false]) :=
  ((AndOrGraph.checkStep_eq_true_iff _ valid.1 valid.2.1 _ _).1 (by decide +kernel)).2.2

example : ⟨graphData, [true, false, false], 1⟩ ∈ AndOrNCLEdge :=
  ⟨by decide, valid, rfl, one_move.legal_left,
    graphData.config [true, true, false], .single one_move, by decide +kernel⟩

-- The directional question also includes a start that already meets the target direction.
example : ⟨graphData, ⟨0, true⟩, ⟨0, true⟩⟩ ∈ AndOrNCLEdgeToEdge :=
  ⟨by decide, by decide, valid, graphData.config [true, false, false],
    graphData.config [true, false, false], one_move.legal_left, rfl, rfl, .refl⟩

-- Use a checked move to establish search correctness without evaluating the search procedure.
example : Cslib.Reachability.savitch graphData.checkStep 3 3
    [true, false, false] [true, true, false] = true :=
  (AndOrGraph.savitch_eq_true_iff _ valid.1 valid.2.1 _ _ rfl rfl).2 (.single one_move)

-- Reflexive reachability still requires a legal initial configuration in the language.
example : ⟨graphData, [false, false, false], [false, false, false]⟩ ∉ AndOrNCL := by
  rintro ⟨_, _, _, hl, _⟩
  have hh := (AndOrGraph.checkLegal_eq_true_iff _ valid.1 valid.2.1 _).2 hl
  change false = true at hh
  cases hh

-- Configuration lengths and edge bounds are part of the languages.
example : ⟨⟨[], 0⟩, [false], []⟩ ∉ AndOrNCL := by
  rintro ⟨_, h, _⟩
  cases h

example : ⟨⟨[], 0⟩, [], 0⟩ ∉ AndOrNCLEdge := by
  rintro ⟨h, _⟩
  exact Nat.not_lt_zero _ h

example : ⟨⟨[], 0⟩, ⟨0, false⟩, ⟨0, false⟩⟩ ∉ AndOrNCLEdgeToEdge := by
  rintro ⟨h, _⟩
  exact Nat.not_lt_zero _ h

/-- info: 'Cslib.Complexity.NCL.AndOrNCL_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AndOrNCL_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.AndOrNCLEdge_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AndOrNCLEdge_mem_PSPACE

/-- info: 'Cslib.Complexity.NCL.AndOrNCLEdgeToEdge_mem_PSPACE' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AndOrNCLEdgeToEdge_mem_PSPACE

end CslibFrontierTests.NCL
