/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.DescendantEndpoint
import Mathlib.Data.List.GetD

/-! # One fixed machine on a genuine nonempty descendant stack -/

public section

namespace Turing.MultiTapeTM.DescendantEndpoint.Tests

open Turing Turing.MultiTapeTM Turing.MultiTapePTM Turing.MultiTapeATM
open Turing.MultiTapeTM.DescendantEndpoint
open Cslib BalancedSchedules Circuits.Frontier.NativeChild EndpointQuery

private def source : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def code : BlockLetter 0 Unit 1 → Fin 1 → Bool := fun _ _ => false
private def raw := ScheduleBits.rows (List.ofFn (scheduleOfNat 0 1 1))
private noncomputable def original := RootPortGraph.ends (q := 1) source [] 1 1 code
private def seed : SeededLabels.Seed 3 6 := fun _ => 0

-- Selecting the first source endpoint's group guarantees a real child edge without making any
-- assumption about the seeded hash's other values.
private noncomputable def group :=
  (Labels.ofSeed 3 1 seed 0 0).symbol (original.getD 0 (0, 0)).1
private noncomputable def labels := Labels.ofSeed 3 1 seed 0 group
private noncomputable def seedFrame : Frame :=
  Frame.ofSeed (U := 3) (a := 1) original.length seed 0 group
private noncomputable def children := labels.edges original
private noncomputable def childVertices :=
  labels.groups.count group + (labels.packing original).numPackets

/-- The actual root uses the canonical two-bit stationary input-head schedule. -/
theorem stationary_schedule_encoding :
    ScheduleBits.rows (List.ofFn (scheduleOfNat 0 1 1)) = [false, false] := by decide

private theorem original_keys (p : ℕ × ℕ) (hp : p ∈ original) : p.1 < 3 ∧ p.2 < 3 := by
  change p ∈ List.ofFn _ at hp
  obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hp
  exact ⟨(explicitVertexEquiv 0 1 1
    (.inl (RootPredecessorGraph.rowOf source [] 1 1 code e))).isLt,
    (explicitVertexEquiv 0 1 1 (.inr (RootPredecessorGraph.colOf 0 1 1 e))).isLt⟩

private theorem selected_group :
    labels.groups.getD (original.getD 0 (0, 0)).1 0 = group := by
  have h0 : 0 < original.length := by simp [original]
  have hm : original.getD 0 (0, 0) ∈ original := by
    rw [List.getD_eq_getElem _ _ h0]
    exact List.getElem_mem _
  have hv := (original_keys _ hm).1
  rw [List.getD_eq_getElem _ _ (by simpa [Labels.groups, labels, Labels.ofSeed] using hv)]
  simp only [Labels.groups, List.getElem_map, List.getElem_range]
  rfl

private theorem children_nonempty : 0 < children.length := by
  have hm : 0 ∈ portEdges labels.groups group original Prod.fst := by
    simp only [portEdges, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨by simp [original], selected_group⟩
  have hn := List.length_pos_of_mem hm
  rw [children, Labels.edges, length_childEdgeList_eq_ports _ _ _ _ (by simp)]
  exact hn.trans_le (Nat.le_add_right _ _)

private theorem frames_represents : Represents 3 original [seedFrame] childVertices children :=
  Represents.cons (U := 3) (a := 1) Represents.nil seed 0 group original_keys

-- The next seed is typed over the exact previous child universe, including every packet
-- vertex. Its input-key bounds are derived from the actual first child, not assumed.
example :
    let nextSeed : SeededLabels.Seed childVertices 6 := fun _ => 0
    let nextLabels := Labels.ofSeed childVertices 1 nextSeed 0 0
    Represents 3 original
      [Frame.ofSeed (U := childVertices) (a := 1) children.length nextSeed 0 0, seedFrame]
      (nextLabels.groups.count 0 + (nextLabels.packing children).numPackets)
      (nextLabels.edges children) := by
  intro nextSeed nextLabels
  exact Represents.cons (frames := [seedFrame]) (edges := children)
    (U := childVertices) (a := 1) frames_represents nextSeed 0 0 (labels.edges_keys original)

/-- The machine and constants are shared by the accepting and rejecting requests. The schedule
is a real one-interval block computation, and the frame is a genuine seeded child. A padded
index cannot be accepted by treating the default endpoint pair as a genuine edge. -/
private theorem exists_nonempty_stack_machine :
    ∃ (U : ℕ) (schedule query : Fin U) (S : Type) (_ : Finite S)
    (atm : MultiTapeATM U Bool S) (C D : ℕ), schedule ≠ query ∧
    ∀ (input : List Bool) (real : Bool),
      let edge := if real then 0 else children.length
      let answer := if real then children.getD 0 (0, 0) else (0, 0)
      let p := root 1 [seedFrame] edge answer
      let start := (TwoWordInput.ready schedule query input raw (encPosition p)).withState
        (some atm.toPTM.initial)
      let time := C * (raw.length + ((encPosition p).length + raw.length.size + 1) ^ D + 1)
      atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔ real = true) := by
  obtain ⟨U, schedule, query, S, hS, atm, C, D, hne, hrun⟩ :=
    Turing.MultiTapeATM.DescendantEndpoint.exists_actual_evaluator 0
  refine ⟨U, schedule, query, S, hS, atm, C, D, hne, ?_⟩
  intro input real edge answer p start time
  have h := hrun source [] 1 1 1 1 code [seedFrame] childVertices children frames_represents
    input edge answer
  refine ⟨h.1, h.2.trans ?_⟩
  cases real <;> simp [edge, answer, children_nonempty]

end Turing.MultiTapeTM.DescendantEndpoint.Tests
