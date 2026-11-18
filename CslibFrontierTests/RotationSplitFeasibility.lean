/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: local-only (tests of the directed split feasibility theorem)

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.Recognition.SplitFeasibility
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases

/-! Ordinary-import clients split an actual loop end, a proper directed block and a full
fiber in a graph containing parallel edges and an isolated vertex. All feasibility witnesses
come from a checked original successor certificate, without a query-completeness premise. -/

public section

open Cslib.Complexity.Graph Cslib.Complexity.Graph.RotationRecognition

namespace Cslib.Tests.RotationSplitFeasibility

/-- A loop, two parallel occurrences, and an isolated vertex. -/
@[expose] def input : FixedRotationInput :=
  ⟨⟨[0, 1, 2], [(0, 0), (0, 1), (0, 1)]⟩, List.replicate 3 none⟩

private def cert : RotationCertificate := ⟨[1, 2, 4, 5, 0, 3]⟩

private theorem hvalid : Valid input := validate_eq_true_iff input |>.mp (by decide +kernel)

private theorem fiber_zero : fiber input.graph 0 = [0, 1, 2, 4] := rfl

private theorem hrotation : RotationCertificate.verifyRotation input.graph cert = true := by
  decide +kernel

private noncomputable def rotation : RotationSystem input.graph :=
  RotationCertificate.decode input.graph cert hrotation

private theorem hgenus : rotation.NumericalGenusZero := by
  obtain ⟨_, h⟩ := (RotationCertificate.verifyGenusZero_eq_true_iff input.graph cert).mp
    (by decide +kernel)
  exact h

private theorem hrealizes : Realizes input rotation := by
  intro v word hv
  change (List.replicate 3 (none : Option (List ℕ))).getD v none = some word at hv
  rw [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq] at hv
  contradiction

private theorem step (d : Dart input.graph) :
    (rotation.rotate d).index = cert.successor.getD d.index 0 :=
  RotationCertificate.index_decode_rotate hrotation d

private theorem hsingleton : Consecutive rotation [0] := consecutive_singleton rotation 0

private theorem hproper : Consecutive rotation [1, 2] := by
  intro i hi d hd
  have hz : i = 0 := by simp only [List.length_cons, List.length_nil] at hi; omega
  subst i
  change d.index = 1 at hd
  change (rotation.rotate d).index = 2
  rw [step, hd]
  rfl

private theorem hfull : Consecutive rotation [0, 1, 2, 4] := by
  intro i hi d hd
  have hb : i < 3 := by simp only [List.length_cons, List.length_nil] at hi; omega
  interval_cases i <;> rw [step, hd] <;> rfl

-- The selected loop end and the connector are parallel hub--old-vertex edges, so the
-- connector is on a cycle. The theorem must not require it to be a bridge.
example : (split input 0 [0]).graph.edges = [(3, 0), (0, 1), (0, 1), (3, 0)] := rfl

/-- An actual loop-end split is feasible even though its connector is not a bridge. -/
theorem loopEnd_split_feasible : Feasible (split input 0 [0]) :=
  (feasible_split_iff hvalid (by decide) (by rfl) (by decide) (by decide)
    (by simp [fiber_zero])).mpr ⟨rotation, hgenus, hrealizes, hsingleton⟩

example : Feasible (split input 0 [1, 2]) :=
  (feasible_split_iff hvalid (by decide) (by rfl) (by decide) (by decide)
    (by simp [fiber_zero])).mpr ⟨rotation, hgenus, hrealizes, hproper⟩

-- Moving the entire fiber retains old vertex 0 as the connector's singleton cycle.
example : fiber (split input 0 [0, 1, 2, 4]).graph 0 = [7] := rfl

example : Feasible (split input 0 [0, 1, 2, 4]) :=
  (feasible_split_iff hvalid (by decide) (by rfl) (by decide) (by decide)
    (by simp [fiber_zero])).mpr ⟨rotation, hgenus, hrealizes, hfull⟩

example : ¬ Consecutive rotation [2, 1] := by
  intro h
  let d : Dart input.graph := (⟨1, by decide⟩, false)
  have hs := h 0 (by decide) d rfl
  rw [step] at hs
  change 4 = 1 at hs
  contradiction

-- Consume the contraction direction as an ordinary module client, not merely its signature.
example (h : Feasible (split input 0 [1, 2])) :
    ∃ r : RotationSystem input.graph, r.NumericalGenusZero ∧ Consecutive r [1, 2] := by
  obtain ⟨r, hg, _, hc⟩ := (feasible_split_iff hvalid (by decide) (by rfl)
    (by decide) (by decide) (by simp [fiber_zero])).mp h
  exact ⟨r, hg, hc⟩

end Cslib.Tests.RotationSplitFeasibility
