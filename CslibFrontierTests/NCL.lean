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

example {E : Type} (encE : E ↪ List Bool) (p : WeightedPort E) :
    encWeightedPort encE p = encPair (encPort encE) encNat (p.port, p.weight) := rfl

example {E : Type} (encE : E ↪ List Bool) (v : Vertex E) :
    encVertex encE v = encPair (encList (encPair (encPort encE) encNat)) encNat
      (v.ports.map (fun p => (p.port, p.weight)), v.minInflow) := by
  change frame (v.ports.flatMap _) ++ encNat v.minInflow =
    frame ((v.ports.map _).flatMap _) ++ encNat v.minInflow
  simp only [List.flatMap_map, Function.comp_def, encWeightedPort_apply]

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
  ((AndOrGraph.checkStep_eq_true_iff _ valid.1 _ _).1 (by decide +kernel)).2.2

example : ⟨graphData, [true, false, false], 1⟩ ∈ AndOrNCLEdge :=
  ⟨by decide, valid, rfl, one_move.legal_left,
    graphData.config [true, true, false], .single one_move, by decide +kernel⟩

-- The directional question also includes a start that already meets the target direction.
example : ⟨graphData, ⟨0, true⟩, ⟨0, true⟩⟩ ∈ AndOrNCLEdgeToEdge :=
  ⟨by decide, by decide, valid, graphData.config [true, false, false],
    graphData.config [true, false, false], one_move.legal_left, rfl, rfl, .refl⟩

-- Use a checked move to establish search correctness without evaluating the search procedure.
example : Cslib.Reachability.reach graphData.checkStep 3 3
    [true, false, false] [true, true, false] = true :=
  (AndOrGraph.reach_eq_true_iff _ valid.1 _ _ rfl rfl).2 (.single one_move)

-- Reflexive reachability still requires a legal initial configuration in the language.
example : ⟨graphData, [false, false, false], [false, false, false]⟩ ∉ AndOrNCL := by
  rintro ⟨_, _, _, hl, _⟩
  have hh := (AndOrGraph.checkLegal_eq_true_iff _ valid.1 _).2 hl
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

private def loopGraph : AndOrGraph :=
  ⟨[.and ⟨0, false⟩ ⟨0, true⟩ ⟨2, true⟩, .or ⟨1, false⟩ ⟨1, true⟩ ⟨2, false⟩], 3⟩

private theorem loopValid : loopGraph.Valid :=
  (AndOrGraph.checkValid_eq_true_iff _).1 (by decide +kernel)

-- The red loop supplies one unit of inflow at the AND vertex in either orientation.
example : loopGraph.checkStep [false, false, true] [false, false, false] = false := by
  decide +kernel

private theorem loopMove : loopGraph.graph.Step
    (loopGraph.config [false, false, true]) (loopGraph.config [true, false, true]) :=
  ((AndOrGraph.checkStep_eq_true_iff _ loopValid.1 _ _).1 (by decide +kernel)).2.2

example : ⟨loopGraph, [false, false, true], [true, false, true]⟩ ∈ AndOrNCL :=
  ⟨loopValid, rfl, rfl, loopMove.legal_left, .single loopMove⟩

example : ⟨loopGraph, [false, false, true], 0⟩ ∈ AndOrNCLEdge :=
  ⟨by decide, loopValid, rfl, loopMove.legal_left, loopGraph.config [true, false, true],
    .single loopMove, by decide +kernel⟩

example : ⟨loopGraph, ⟨0, false⟩, ⟨0, true⟩⟩ ∈ AndOrNCLEdgeToEdge :=
  ⟨by decide, by decide, loopValid, loopGraph.config [false, false, true],
    loopGraph.config [true, false, true], loopMove.legal_left, rfl, rfl, .single loopMove⟩

end CslibFrontierTests.NCL
