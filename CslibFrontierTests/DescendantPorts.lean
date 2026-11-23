/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantPorts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.Pairwise

public section

namespace Turing.MultiTapeTM.DescendantPorts.Tests

open Cslib Cslib.Circuits.Frontier NativeChild MultiTapeATM QuantifiedWord SeededChildCounts

/-- Distinct edge numbers include two parallel edges; the last vertex is isolated. -/
private def graph : DescribedNetwork Unit :=
  ⟨3, [([0, 2], ()), ([1], ()), ([0, 1, 2], ()), ([], ())]⟩

private def endpoint : EndpointQuery :=
  ⟨graph.numEdges, fun e p => e < graph.numEdges ∧ graph.edgeEnds.getD e (0, 0) = p⟩

private theorem endpoint_represents : endpoint.Represents graph.edgeEnds := by
  constructor
  · decide
  · intro e p
    rfl

private theorem specification (vertex : ℕ) (ports : List ℕ) :
    plays (fun xs => Joined.holds endpoint (program (⟨3, 4, vertex, ports⟩, xs))) []
      (flags ⟨3, 4, vertex, ports⟩) ↔
      ∃ hv : vertex < graph.vertices.length, ports = graph.vertices[vertex].1 :=
  plays_program_network graph (r := 2) (by decide) (by decide) endpoint
    endpoint_represents vertex ports

-- The executable parser preserves one genuine edge and its two common guessed endpoints.
example : program (⟨3, 4, 0, [0, 2]⟩,
    [false, true] ++ [false, false, false] ++ [false, true, false] ++ [true]) =
      .inr (2, (0, 2)) := by decide

-- The padding challenge emits a verdict without asking for a nonexistent edge.
example : program (⟨3, 4, 0, [0, 2]⟩,
    [true, true] ++ [false, false, false] ++ [false, true, false] ++ [true]) =
      .inl true := by decide

-- Both parallel edges are required, in numerical order.
example : plays (fun xs => Joined.holds endpoint (program (⟨3, 4, 0, [0, 2]⟩, xs))) []
    (flags ⟨3, 4, 0, [0, 2]⟩) := (specification 0 [0, 2]).mpr ⟨by decide, rfl⟩

-- An omitted edge cannot be hidden by a guessed endpoint pair.
example : ¬ plays (fun xs => Joined.holds endpoint (program (⟨3, 4, 0, [0]⟩, xs))) []
    (flags ⟨3, 4, 0, [0]⟩) := by
  rw [specification]
  decide

-- Correct membership alone is insufficient: permutation and duplicate candidates are rejected.
example : ¬ plays (fun xs => Joined.holds endpoint (program (⟨3, 4, 0, [2, 0]⟩, xs))) []
    (flags ⟨3, 4, 0, [2, 0]⟩) := by
  rw [specification]
  decide

example : ¬ plays (fun xs => Joined.holds endpoint (program (⟨3, 4, 0, [0, 0, 2]⟩, xs))) []
    (flags ⟨3, 4, 0, [0, 0, 2]⟩) := by
  rw [specification]
  decide

example : ¬ plays (fun xs => Joined.holds endpoint (program (⟨3, 4, 0, [0, 2, 3]⟩, xs))) []
    (flags ⟨3, 4, 0, [0, 2, 3]⟩) := by
  rw [specification]
  decide

example : plays (fun xs => Joined.holds endpoint (program (⟨3, 4, 3, []⟩, xs))) []
    (flags ⟨3, 4, 3, []⟩) := (specification 3 []).mpr ⟨by decide, rfl⟩

example : ¬ plays (fun xs => Joined.holds endpoint (program (⟨3, 4, 4, []⟩, xs))) []
    (flags ⟨3, 4, 4, []⟩) := by
  rw [specification]
  decide

-- With no edges, the remaining universal selector must still check vertex validity.
private def noEdges : EndpointQuery := ⟨0, fun _ _ => False⟩

example : plays (fun xs => Joined.holds noEdges (program (⟨0, 1, 0, []⟩, xs))) []
    (flags ⟨0, 1, 0, []⟩) := by
  rw [plays_program _ noEdges [] ⟨rfl, by simp [noEdges]⟩ rfl (by simp)]
  decide

example : ¬ plays (fun xs => Joined.holds noEdges (program (⟨0, 0, 0, []⟩, xs))) []
    (flags ⟨0, 0, 0, []⟩) := by
  rw [plays_program _ noEdges [] ⟨rfl, by simp [noEdges]⟩ rfl (by simp)]
  decide

-- The shared pairwise machine handles asymmetric relations and an empty element type.
/-- A non-symmetric relation is covered by the shared native pairwise certificate. -/
theorem native_pairwise_lt :
    ComputableInPolyTime (fun xs : List ℕ => decide (xs.Pairwise (· < ·)))
    (encList encNat) encBool :=
  ComputableInPolyTime.pairwise encNat (· < ·) ComputableInPolyTime.binary_lt

example (enc : Empty ↪ List Bool) :
    ComputableInPolyTime (fun xs : List Empty => decide (xs.Pairwise (fun _ _ => False)))
      (encList enc) encBool :=
  ComputableInPolyTime.pairwise enc _ (ComputableInPolyTime.const false)

end Turing.MultiTapeTM.DescendantPorts.Tests
