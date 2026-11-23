/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DescendantEndpointCorrect

/-! # Compressed endpoint routing at repeated-edge and ancestry boundaries -/

public section

namespace Turing.MultiTapeTM.DescendantEndpoint.Tests

open Turing.MultiTapeTM Turing.MultiTapeTM.DescendantEndpoint
open Turing.MultiTapeATM Turing.MultiTapeATM.SeededChildCounts
open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery

private def seed : SeededLabels.Seed 1 6 := fun _ => 0
private noncomputable def group := (Labels.ofSeed 1 1 seed 0 0).symbol 0
private noncomputable def labels := Labels.ofSeed 1 1 seed 0 group
private def rootEdges : List (ℕ × ℕ) := [(0, 0), (0, 0)]
private noncomputable def seedFrame : Frame := Frame.ofSeed (U := 1) (a := 1) 2 seed 0 group
private def base : EndpointQuery := ⟨2, fun e p => e < 2 ∧ p = (0, 0)⟩

private theorem base_represents : base.Represents rootEdges := by
  refine ⟨rfl, fun e p => ?_⟩
  by_cases he : e < 2
  · have : e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl <;> simp [base, rootEdges, eq_comm]
  · simp [base, rootEdges, he]
    omega

private theorem frames_represents : Represents 1 rootEdges [seedFrame]
    (labels.groups.count group + (labels.packing rootEdges).numPackets)
    (labels.edges rootEdges) := by
  apply Represents.cons (U := 1) (a := 1) Represents.nil seed 0 group
  intro p hp
  simp only [rootEdges, List.mem_cons, List.not_mem_nil, or_false, or_self] at hp
  subst p
  decide

/-- An extra isolated parent vertex changes the seed universe and the packet-vertex offset.
Endpoint-key bounds alone would allow it, but the exact-count representation does not. -/
theorem rejects_extra_root_vertex (f : Frame) (hf : f.vertices = 1)
    (es : List (ℕ × ℕ)) (vertices : ℕ) (edges : List (ℕ × ℕ)) :
    ¬ Represents 2 es [f] vertices edges := by
  have first {U V : ℕ} {es es' : List (ℕ × ℕ)} {f : Frame}
      (h : Represents U es [f] V es') : f.vertices = U := by
    cases h with
    | cons parent _ _ _ _ => cases parent; rfl
  intro h
  have hv := first h
  omega

example (vertices : ℕ) (edges : List (ℕ × ℕ)) :
    ¬ Represents 2 rootEdges [seedFrame] vertices edges :=
  rejects_extra_root_vertex seedFrame rfl rootEdges vertices edges

private theorem groups_eq : labels.groups = [group] := rfl

-- Both occurrences of the self-loop survive separately on each side of the child.
private theorem child_length : (labels.edges rootEdges).length = 4 := by
  rw [Labels.edges, length_childEdgeList_eq_ports _ _ _ _ (by simp), groups_eq,
    show labels.group = group from rfl]
  simp [portEdges, rootEdges, List.range_succ]

-- A genuine edge is accepted, while index four cannot use the default endpoint pair.
example : accepts base [seedFrame] 0 ((labels.edges rootEdges).getD 0 (0, 0)) ∧
    ¬ accepts base [seedFrame] 4 (0, 0) := by
  constructor
  · apply (accepts_iff_of_represents base base_represents frames_represents 0 _).2
    exact ⟨by rw [child_length]; decide, rfl⟩
  · rw [accepts_iff_of_represents base base_represents frames_represents, child_length]
    simp

private def routingFrame : Frame := ⟨5, 6, 1, 0, 1, 0, 1, 0, 0⟩
private def proposal : SeededChildWitness.Proposal := ⟨4, (1, 2), ⟨3, 0, 3, 1, 5, 2⟩⟩
private def parentWord : List Bool := SeededChildWitness.word 3 proposal ++
  (Cslib.BitString.lowBits 3 1 ++ Cslib.BitString.lowBits 2 1)

-- A direct parent branch pops exactly one frame and initializes its predecessor. Its unused
-- count suffix may be absent; the deterministic dispatch ignores its own dummy choice.
example (copies : ℕ) (older : Frame) :
    let p := { root copies [routingFrame, older] 3 (1, 329) with
      pending := [], choices := parentWord }
    next p false = root copies [older] 4 (1, 2) ∧
      next p true = root copies [older] 4 (1, 2) := by
  have hp := Joined.program_of_dispatch_parent
    (h := routingFrame.header 3 (1, 329)) (xs := parentWord) (p := proposal) rfl
  constructor <;>
    simp only [next, root, Option.isSome_none, Bool.false_eq_true, ite_false, hp, proposal]

-- An initialized empty stack hands the unchanged query and copy count to the root checker.
example (copies edge row column : ℕ) :
    player (root copies [] edge (row, column)) = none ∧
      terminal (root copies [] edge (row, column)) = .inr (edge, (row, column)) ∧
      (next (root copies [] edge (row, column)) true).copies = copies := by
  exact ⟨rfl, rfl, rfl⟩

end Turing.MultiTapeTM.DescendantEndpoint.Tests
