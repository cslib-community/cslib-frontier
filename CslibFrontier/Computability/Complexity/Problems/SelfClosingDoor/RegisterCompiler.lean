/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.RegisterEncoding
import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Wiring
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Enum

/-!
# Compiling Boolean register programs to symmetric self-closing doors

One door stores each register. Its tunnels form a directed cycle with two wiring arcs. Each
instruction opens a private return marker, enters the register's guarded tunnel, and returns
only from the side representing its prescribed written value. Diode doors implement the
wiring. Arbitrary extra core cycles preserve the guard and return contract.

The compiler traverses the explicit register, instruction and jump lists. Enumerated indices
are unary counters converted to binary labels before the constant-size location arithmetic.
This original construction implements [AniBosboomDemaineEtAl2021, Section 2.1].

## Main definitions

* `RegisterProgram.compile`: the explicit door network of a register program.

## Main results

* `RegisterProgram.compile_reachability_iff`: the network accepts exactly the program's runs.
* `RegisterProgram.computableInPolyTime_compile`: compilation is polynomial-time.

## References

* [Ani et al.][AniBosboomDemaineEtAl2021, Section 2.1]
-/

public section

namespace Cslib.Complexity.SelfClosingDoor.RegisterProgram

namespace Compiler

/-- External control labels occupy residue zero modulo six. -/
private def external (v : ℕ) : ℕ := 6 * v

/-- A private instruction entry occupies residue one modulo six. -/
private def entry (j : ℕ) : ℕ := 6 * j + 1

/-- The register tunnel enabled by `b` starts in residue two or four modulo six. -/
private def input (r : ℕ) (b : Bool) : ℕ := 6 * r + if b then 4 else 2

/-- The corresponding tunnel exits in residue three or five modulo six. -/
private def output (r : ℕ) (b : Bool) : ℕ := input r b + 1

/-- A register door flips its bit between the two halves of its directed core cycle. -/
private def registerDoor (r : ℕ) (b : Bool) : Door :=
  ⟨⟨input r false, output r false⟩, ⟨input r true, output r true⟩, b⟩

/-- An instruction's return latch opens only at its private entry. -/
private def markerDoor (j : ℕ) (i : Instruction) : Door :=
  ⟨⟨entry j, entry j⟩,
    ⟨output i.register (!i.write), external i.target⟩, false⟩

/-- Register doors, in the same order as the program's initial registers. -/
private def registerDoors (p : Program) : List Door :=
  p.initial.zipIdx.map fun (b, r) => registerDoor r b

/-- Return markers, in the same order as the program's instructions. -/
private def markerDoors (p : Program) : List Door :=
  p.instructions.zipIdx.map fun (i, j) => markerDoor j i

/-- The two directed connectors of each register's core cycle. -/
private def coreWiring (p : Program) : List Tunnel :=
  (List.range p.initial.length).flatMap fun r =>
    [⟨output r false, input r true⟩, ⟨output r true, input r false⟩]

/-- Each instruction has a one-way entry and a one-way guarded approach to its register. -/
private def instructionWiring (p : Program) : List Tunnel :=
  p.instructions.zipIdx.flatMap fun (i, j) =>
    [⟨external i.source, entry j⟩, ⟨entry j, input i.register i.guard⟩]

/-- Source jumps, register-core connectors and guarded instruction approaches. -/
private def wiring (p : Program) : List Tunnel :=
  p.jumps.map (fun a => ⟨external a.source, external a.target⟩) ++
    coreWiring p ++ instructionWiring p

/-- The registers and return markers, before replacing directed wiring by diode doors. -/
private def principalDoors (p : Program) : List Door := registerDoors p ++ markerDoors p

end Compiler

/-- Compile an arbitrary finite register program to an explicit door network. Out-of-range
register instructions enter a core with no register door and have no successful return. -/
def compile (p : Program) : Instance :=
  Wiring.compile (Compiler.principalDoors p) (Compiler.wiring p)
    (Compiler.external p.start) (Compiler.external p.target)

open Compiler

private inductive Place where
  | external (v : ℕ)
  | entry (j : ℕ)
  | input (r : ℕ) (b : Bool)
  | output (r : ℕ) (b : Bool)
  deriving DecidableEq

private def Place.code : Place → ℕ
  | .external v => Compiler.external v
  | .entry j => Compiler.entry j
  | .input r b => Compiler.input r b
  | .output r b => Compiler.output r b

private theorem Place.code_injective : Function.Injective Place.code := by
  intro x y h
  cases x <;> cases y <;>
    simp only [Place.code, Compiler.external, Compiler.entry, Compiler.input, Compiler.output] at h
  all_goals (try split_ifs at h) <;> simp_all <;> omega

private structure MachineState where
  location : Place
  registers : List Bool
  markers : List Bool

private def MachineState.toState (s : MachineState) : State :=
  ⟨s.location.code, s.registers ++ s.markers⟩

private def MachineState.Valid (p : Program) (s : MachineState) : Prop :=
  s.registers.length = p.initial.length ∧ s.markers.length = p.instructions.length

private inductive MachineStep (p : Program) : MachineState → MachineState → Prop
  | jump {registers markers : List Bool} {a : Tunnel} (ha : a ∈ p.jumps) :
      MachineStep p ⟨.external a.source, registers, markers⟩
        ⟨.external a.target, registers, markers⟩
  | enter {registers markers : List Bool} (j : Fin p.instructions.length) :
      MachineStep p ⟨.external p.instructions[j].source, registers, markers⟩
        ⟨.entry j.val, registers, markers⟩
  | approach {registers markers : List Bool} (j : Fin p.instructions.length) :
      MachineStep p ⟨.entry j.val, registers, markers⟩
        ⟨.input p.instructions[j].register p.instructions[j].guard, registers, markers⟩
  | connect {registers markers : List Bool} (r : Fin p.initial.length) (b : Bool) :
      MachineStep p ⟨.output r.val b, registers, markers⟩
        ⟨.input r.val (!b), registers, markers⟩
  | register {registers markers : List Bool} (r : Fin p.initial.length) (b : Bool)
      (hb : registers.getD r.val false = b) :
      MachineStep p ⟨.input r.val b, registers, markers⟩
        ⟨.output r.val b, registers.set r.val (!b), markers⟩
  | openMarker {registers markers : List Bool} (j : Fin p.instructions.length)
      (hb : markers.getD j.val false = false) :
      MachineStep p ⟨.entry j.val, registers, markers⟩
        ⟨.entry j.val, registers, markers.set j.val true⟩
  | returnMarker {registers markers : List Bool} (j : Fin p.instructions.length)
      (hb : markers.getD j.val false = true) :
      MachineStep p ⟨.output p.instructions[j].register (!p.instructions[j].write),
          registers, markers⟩
        ⟨.external p.instructions[j].target, registers, markers.set j.val false⟩

private theorem MachineStep.valid_target {p : Program} {s t : MachineState}
    (h : MachineStep p s t) (hs : s.Valid p) : t.Valid p := by
  cases h <;> simpa only [MachineState.Valid, List.length_set] using hs

private theorem registerDoors_length (p : Program) :
    (registerDoors p).length = p.initial.length := by
  simp [registerDoors]

private theorem markerDoors_length (p : Program) :
    (markerDoors p).length = p.instructions.length := by
  simp [markerDoors]

private theorem registerDoors_get (p : Program) (r : Fin p.initial.length) :
    (registerDoors p)[r.val]'(by simpa only [registerDoors_length] using r.isLt) =
      registerDoor r.val p.initial[r] := by
  simp [registerDoors, List.getElem_zipIdx, Fin.getElem_fin]

private theorem markerDoors_get (p : Program) (j : Fin p.instructions.length) :
    (markerDoors p)[j.val]'(by simpa only [markerDoors_length] using j.isLt) =
      markerDoor j.val p.instructions[j] := by
  simp [markerDoors, List.getElem_zipIdx, Fin.getElem_fin]

private theorem MachineState.actual_valid {p : Program} {s : MachineState} (hs : s.Valid p) :
    s.toState.Valid (principalDoors p) := by
  simp only [State.Valid, MachineState.toState, principalDoors, List.length_append,
    registerDoors_length, markerDoors_length]
  exact congrArg₂ (· + ·) hs.1 hs.2

private theorem register_tunnel (r : ℕ) (initial b : Bool) :
    (registerDoor r initial).tunnel b = ⟨input r b, output r b⟩ := by
  cases b <;> rfl

private theorem marker_tunnel_false (j : ℕ) (i : Instruction) :
    (markerDoor j i).tunnel false = ⟨entry j, entry j⟩ := rfl

private theorem marker_tunnel_true (j : ℕ) (i : Instruction) :
    (markerDoor j i).tunnel true = ⟨output i.register (!i.write), external i.target⟩ := rfl

private theorem principal_register_get (p : Program) (r : Fin p.initial.length) :
    (principalDoors p)[r.val]'(by
      simp only [principalDoors, List.length_append, registerDoors_length, markerDoors_length]
      omega) = registerDoor r.val p.initial[r] := by
  unfold principalDoors
  rw [List.getElem_append_left (by simpa only [registerDoors_length] using r.isLt),
    registerDoors_get]

private theorem principal_marker_get (p : Program) (j : Fin p.instructions.length) :
    (principalDoors p)[p.initial.length + j.val]'(by
      simp only [principalDoors, List.length_append, registerDoors_length, markerDoors_length]
      omega) = markerDoor j.val p.instructions[j] := by
  unfold principalDoors
  rw [List.getElem_append_right (by simp [registerDoors_length])]
  simpa only [registerDoors_length, Nat.add_sub_cancel_left] using markerDoors_get p j

private theorem actual_register_step (p : Program) (registers markers : List Bool)
    (hr : registers.length = p.initial.length) (hm : markers.length = p.instructions.length)
    (r : Fin p.initial.length) (b : Bool) (hb : registers.getD r.val false = b) :
    SelfClosingDoor.Step (principalDoors p)
      ⟨input r.val b, registers ++ markers⟩
      ⟨output r.val b, registers.set r.val (!b) ++ markers⟩ := by
  have hi : r.val < registers.length := by omega
  have hd := principal_register_get p r
  have hbits : (registers ++ markers).getD r.val false = b :=
    (List.getD_append _ _ _ _ hi).trans hb
  refine ⟨?_, ⟨r.val, by
    simp only [principalDoors, List.length_append, registerDoors_length, markerDoors_length]
    omega⟩, ?_, ?_⟩
  · simp only [State.Valid, List.length_append, principalDoors, registerDoors_length,
      markerDoors_length, hr, hm]
  · simp only [Fin.getElem_fin, hd, hbits, register_tunnel]
  · simp only [Fin.getElem_fin, hd, hbits, register_tunnel, List.set_append_left _ _ hi]

private theorem actual_marker_step (p : Program) (registers markers : List Bool)
    (hr : registers.length = p.initial.length) (hm : markers.length = p.instructions.length)
    (j : Fin p.instructions.length) (b : Bool) (hb : markers.getD j.val false = b) :
    let d := markerDoor j.val p.instructions[j]
    SelfClosingDoor.Step (principalDoors p)
      ⟨(d.tunnel b).source, registers ++ markers⟩
      ⟨(d.tunnel b).target, registers ++ markers.set j.val (!b)⟩ := by
  have hd := principal_marker_get p j
  have hbits : (registers ++ markers).getD (p.initial.length + j.val) false = b := by
    rw [List.getD_append_right _ _ _ _ (by omega), hr, Nat.add_sub_cancel_left, hb]
  have hset : (registers ++ markers).set (p.initial.length + j.val) (!b) =
      registers ++ markers.set j.val (!b) := by
    rw [List.set_append_right _ _ (by omega), hr, Nat.add_sub_cancel_left]
  refine ⟨?_, ⟨p.initial.length + j.val, by
    simp only [principalDoors, List.length_append, registerDoors_length, markerDoors_length]
    omega⟩, ?_, ?_⟩
  · simp only [State.Valid, List.length_append, principalDoors, registerDoors_length,
      markerDoors_length, hr, hm]
  · simp only [Fin.getElem_fin, hd, hbits]
  · simp only [Fin.getElem_fin, hd, hbits, hset]

private theorem indexed_instruction_mem (p : Program) (j : Fin p.instructions.length) :
    (p.instructions[j], j.val) ∈ p.instructions.zipIdx := by
  simp [List.mk_mem_zipIdx_iff_getElem?, Fin.getElem_fin]

private theorem MachineStep.actual {p : Program} {s t : MachineState}
    (h : MachineStep p s t) (hs : s.Valid p) :
    Wiring.Step (principalDoors p) (wiring p) s.toState t.toState := by
  have hv := MachineState.actual_valid hs
  cases h with
  | @jump registers markers a ha =>
    exact Or.inr ⟨hv, ⟨external a.source, external a.target⟩,
      List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, ha, rfl⟩)), rfl, rfl⟩
  | enter j =>
    exact Or.inr ⟨hv, ⟨external p.instructions[j].source, entry j.val⟩,
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, indexed_instruction_mem p j, by simp⟩),
      rfl, rfl⟩
  | approach j =>
    exact Or.inr ⟨hv, ⟨entry j.val, input p.instructions[j].register p.instructions[j].guard⟩,
      List.mem_append_right _ (List.mem_flatMap.mpr ⟨_, indexed_instruction_mem p j, by simp⟩),
      rfl, rfl⟩
  | connect r b =>
    exact Or.inr ⟨hv, ⟨output r.val b, input r.val (!b)⟩, List.mem_append_left _
      (List.mem_append_right _ (List.mem_flatMap.mpr ⟨r.val, List.mem_range.mpr r.isLt,
        by cases b <;> simp⟩)), rfl, rfl⟩
  | register r b hb =>
    exact Or.inl (actual_register_step p _ _ hs.1 hs.2 r b hb)
  | openMarker j hb =>
    exact Or.inl (actual_marker_step p _ _ hs.1 hs.2 j false hb)
  | returnMarker j hb =>
    exact Or.inl (actual_marker_step p _ _ hs.1 hs.2 j true hb)

private theorem actual_door_complete {p : Program} {s : MachineState} {t : State}
    (hs : s.Valid p) (h : SelfClosingDoor.Step (principalDoors p) s.toState t) :
    ∃ u, MachineStep p s u ∧ u.toState = t := by
  rcases s with ⟨location, registers, markers⟩
  obtain ⟨_, i, hp, rfl⟩ := h
  have hr : registers.length = p.initial.length := hs.1
  by_cases hi : i.val < p.initial.length
  · let r : Fin p.initial.length := ⟨i.val, hi⟩
    let b := registers.getD i.val false
    have hd : (principalDoors p)[i.val] = registerDoor i.val p.initial[r] :=
      principal_register_get p r
    have hb : (registers ++ markers).getD i.val false = b :=
      List.getD_append _ _ _ _ (by omega)
    obtain rfl : location = .input i.val b := Place.code_injective (by
      simpa only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, register_tunnel]
        using hp)
    refine ⟨⟨.output i.val b, registers.set i.val (!b), markers⟩,
      MachineStep.register r b rfl, ?_⟩
    simp only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb,
      register_tunnel, List.set_append_left _ _ (by omega : i.val < registers.length)]
  · have hj : i.val - p.initial.length < p.instructions.length := by
      have := i.isLt
      simp only [principalDoors, List.length_append, registerDoors_length,
        markerDoors_length] at this
      omega
    let j : Fin p.instructions.length := ⟨i.val - p.initial.length, hj⟩
    have hd : (principalDoors p)[i.val] = markerDoor j.val p.instructions[j] := by
      simpa only [j, Nat.add_sub_of_le (by omega : p.initial.length ≤ i.val)] using
        principal_marker_get p j
    have hb : (registers ++ markers).getD i.val false = markers.getD j.val false := by
      rw [List.getD_append_right _ _ _ _ (by omega), hr]
    have hset (b : Bool) : (registers ++ markers).set i.val b =
        registers ++ markers.set j.val b := by
      rw [List.set_append_right _ _ (by omega), hr]
    cases hmj : markers.getD j.val false with
    | false =>
      obtain rfl : location = .entry j.val := Place.code_injective (by
        simpa only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, hmj,
          marker_tunnel_false] using hp)
      refine ⟨⟨.entry j.val, registers, markers.set j.val true⟩,
        MachineStep.openMarker j hmj, ?_⟩
      simp only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, hmj,
        marker_tunnel_false, Bool.not_false, hset]
    | true =>
      obtain rfl : location = .output p.instructions[j].register (!p.instructions[j].write) :=
        Place.code_injective (by
          simpa only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, hmj,
            marker_tunnel_true] using hp)
      refine ⟨⟨.external p.instructions[j].target, registers, markers.set j.val false⟩,
        MachineStep.returnMarker j hmj, ?_⟩
      simp only [MachineState.toState, Place.code, Fin.getElem_fin, hd, hb, hmj,
        marker_tunnel_true, Bool.not_true, hset]

private theorem actual_step_complete {p : Program} {s : MachineState} {t : State}
    (hs : s.Valid p) (h : Wiring.Step (principalDoors p) (wiring p) s.toState t) :
    ∃ u, MachineStep p s u ∧ u.toState = t := by
  rcases h with h | ⟨_, a, ha, hp, rfl⟩
  · exact actual_door_complete hs h
  · rcases s with ⟨location, registers, markers⟩
    simp only [wiring, List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
      obtain rfl : location = .external b.source := Place.code_injective hp
      exact ⟨⟨.external b.target, registers, markers⟩, MachineStep.jump hb, rfl⟩
    · obtain ⟨r, hr, ha⟩ := List.mem_flatMap.1 ha
      have hr := List.mem_range.1 hr
      rcases (by simpa using ha : a = _ ∨ a = _) with rfl | rfl
      · obtain rfl : location = .output r false := Place.code_injective hp
        exact ⟨⟨.input r true, registers, markers⟩, MachineStep.connect ⟨r, hr⟩ false, rfl⟩
      · obtain rfl : location = .output r true := Place.code_injective hp
        exact ⟨⟨.input r false, registers, markers⟩, MachineStep.connect ⟨r, hr⟩ true, rfl⟩
    · obtain ⟨⟨i, j⟩, hj, ha⟩ := List.mem_flatMap.1 ha
      obtain ⟨hbound, hi⟩ := List.mem_zipIdx' hj
      rcases (by simpa [hi] using ha : a = _ ∨ a = _) with rfl | rfl
      · obtain rfl : location = .external p.instructions[j].source := Place.code_injective hp
        exact ⟨⟨.entry j, registers, markers⟩, MachineStep.enter ⟨j, hbound⟩, rfl⟩
      · obtain rfl : location = .entry j := Place.code_injective hp
        exact ⟨⟨.input p.instructions[j].register p.instructions[j].guard, registers, markers⟩,
          MachineStep.approach ⟨j, hbound⟩, rfl⟩

private def closedMarkers (p : Program) : List Bool :=
  List.replicate p.instructions.length false

private def selectedMarkers (p : Program) (j : Fin p.instructions.length) (b : Bool) :
    List Bool := (closedMarkers p).set j.val b

private theorem selectedMarkers_false (p : Program) (j : Fin p.instructions.length) :
    selectedMarkers p j false = closedMarkers p := by
  simp [selectedMarkers, closedMarkers]

private theorem selectedMarkers_self (p : Program) (j : Fin p.instructions.length) (b : Bool) :
    (selectedMarkers p j b).getD j.val false = b := by
  simp [selectedMarkers, closedMarkers, List.getD_eq_getElem?_getD]

private theorem selectedMarkers_true {p : Program} {j k : Fin p.instructions.length} {b : Bool}
    (h : (selectedMarkers p j b).getD k.val false = true) : k = j ∧ b = true := by
  by_cases hkj : k.val = j.val
  · obtain rfl := Fin.ext hkj
    exact ⟨rfl, (selectedMarkers_self p k b).symm.trans h⟩
  · simp [selectedMarkers, closedMarkers, List.getD_eq_getElem?_getD,
      List.getElem_set_ne (Ne.symm hkj)] at h

private inductive Certified (p : Program) : MachineState → Prop
  | boundary (s : State) (hr : p.Reachable p.initialState s) :
      Certified p ⟨.external s.location, s.bits, closedMarkers p⟩
  | entry (s : State) (hr : p.Reachable p.initialState s)
      (j : Fin p.instructions.length) (hp : s.location = p.instructions[j].source) (m : Bool) :
      Certified p ⟨.entry j.val, s.bits, selectedMarkers p j m⟩
  | ready (s : State) (hr : p.Reachable p.initialState s)
      (j : Fin p.instructions.length) (hp : s.location = p.instructions[j].source) (m : Bool) :
      Certified p ⟨.input p.instructions[j].register p.instructions[j].guard,
        s.bits, selectedMarkers p j m⟩
  | input (s : State) (hr : p.Reachable p.initialState s)
      (j : Fin p.instructions.length) (hp : s.location = p.instructions[j].source)
      (hg : s.bits.getD p.instructions[j].register false = p.instructions[j].guard)
      (hreg : p.instructions[j].register < s.bits.length) (m b : Bool) :
      Certified p ⟨.input p.instructions[j].register b,
        s.bits.set p.instructions[j].register b, selectedMarkers p j m⟩
  | output (s : State) (hr : p.Reachable p.initialState s)
      (j : Fin p.instructions.length) (hp : s.location = p.instructions[j].source)
      (hg : s.bits.getD p.instructions[j].register false = p.instructions[j].guard)
      (hreg : p.instructions[j].register < s.bits.length) (m b : Bool) :
      Certified p ⟨.output p.instructions[j].register b,
        s.bits.set p.instructions[j].register (!b), selectedMarkers p j m⟩

private theorem Certified.step {p : Program} {s t : MachineState}
    (hs : Certified p s) (hstep : MachineStep p s t) : Certified p t := by
  generalize hsource : s = u at hstep
  cases hs <;> cases hstep
  all_goals
    obtain ⟨hloc, hregs, hmarkers⟩ := MachineState.mk.inj hsource
    try cases hloc
  all_goals subst hregs hmarkers
  case boundary.jump source hr a ha =>
    exact Certified.boundary ⟨a.target, source.bits⟩
      (hr.tail ⟨hr.length rfl, Or.inl ⟨a, ha, Place.external.inj hloc, rfl⟩⟩)
  case boundary.enter source hr j =>
    rw [← selectedMarkers_false p j]
    exact Certified.entry source hr j (Place.external.inj hloc) false
  case entry.approach source hr j hp m k =>
    exact Fin.ext (Place.entry.inj hloc) ▸ Certified.ready source hr j hp m
  case entry.openMarker source hr j hp m k hb =>
    simpa only [← Fin.ext (Place.entry.inj hloc), selectedMarkers, List.set_set] using
      Certified.entry source hr j hp true
  case ready.register source hr j hp m r b hb =>
    obtain ⟨hri, hbi⟩ := Place.input.inj hloc
    have hg : source.bits.getD p.instructions[j].register false = p.instructions[j].guard := by
      simpa only [hri, hbi] using hb
    have hreg : p.instructions[j].register < source.bits.length := by
      simpa only [hri, hr.length rfl] using r.isLt
    simpa only [hri, hbi] using
      Certified.output source hr j hp hg hreg m p.instructions[j].guard
  case input.register source hr j hp hg hreg m b₀ r b hb =>
    obtain ⟨hri, hbi⟩ := Place.input.inj hloc
    simpa only [hri, hbi, List.set_set] using Certified.output source hr j hp hg hreg m b₀
  case output.connect source hr j hp hg hreg m b₀ r b =>
    obtain ⟨hri, hbi⟩ := Place.output.inj hloc
    simpa only [hri, hbi] using Certified.input source hr j hp hg hreg m (!b₀)
  case output.returnMarker source hr j hp hg hreg m b k hb =>
    obtain ⟨he, rfl⟩ := selectedMarkers_true hb
    subst k
    have hbit : b = !p.instructions[j].write := (Place.output.inj hloc).2
    let next : State := ⟨p.instructions[j].target, source.bits.set p.instructions[j].register
      p.instructions[j].write⟩
    have hnext : p.Step source next :=
      ⟨hr.length rfl, Or.inr ⟨p.instructions[j], List.getElem_mem j.isLt,
        hreg, hp, hg, rfl⟩⟩
    simpa only [next, hbit, Bool.not_not, selectedMarkers, List.set_set,
      closedMarkers, List.set_replicate_self] using Certified.boundary next (hr.tail hnext)

private def boundary (p : Program) (s : State) : MachineState :=
  ⟨.external s.location, s.bits, List.replicate p.instructions.length false⟩

private theorem machine_instruction_path (p : Program) (j : Fin p.instructions.length)
    (s t : State) (hs : s.bits.length = p.initial.length) (hi : p.instructions[j].Step s t) :
    Relation.ReflTransGen (MachineStep p) (boundary p s) (boundary p t) := by
  obtain ⟨hr, hsource, hguard, rfl⟩ := hi
  let r : Fin p.initial.length := ⟨p.instructions[j].register, by omega⟩
  let off := List.replicate p.instructions.length false
  let on := off.set j.val true
  have hoff : off.getD j.val false = false := by
    simp [off, List.getD_eq_getElem?_getD]
  have hon : on.getD j.val false = true := by
    simp [on, off, List.getD_eq_getElem?_getD, j.isLt]
  have hstart : MachineStep p (boundary p s) ⟨.entry j.val, s.bits, off⟩ := by
    simpa only [boundary, hsource] using
      (MachineStep.enter (registers := s.bits) (markers := off) j)
  have hprefix := ((Relation.ReflTransGen.single hstart).tail
    (MachineStep.openMarker j hoff)).tail (MachineStep.approach j)
  have hfirst := hprefix.tail (MachineStep.register r p.instructions[j].guard hguard)
  have hready : Relation.ReflTransGen (MachineStep p) (boundary p s)
      ⟨.output p.instructions[j].register (!p.instructions[j].write),
        s.bits.set p.instructions[j].register p.instructions[j].write, on⟩ := by
    by_cases hsame : p.instructions[j].guard = p.instructions[j].write
    · have hsecond : (s.bits.set r.val (!p.instructions[j].guard)).getD r.val false =
          !p.instructions[j].guard := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hr, Option.getD_some]
      have hcycle := (hfirst.tail (MachineStep.connect r p.instructions[j].guard)).tail
        (MachineStep.register r (!p.instructions[j].guard) hsecond)
      simpa only [r, hsame, Bool.not_not, List.set_set] using hcycle
    · have hother : p.instructions[j].guard = !p.instructions[j].write := by grind
      simpa only [r, hother, Bool.not_not] using hfirst
  have hfinish := hready.tail (MachineStep.returnMarker j hon)
  simpa only [boundary, on, List.set_set, List.set_replicate_self, off] using hfinish

private theorem machine_program_path {p : Program} {s t : State}
    (hs : s.bits.length = p.initial.length) (hr : p.Reachable s t) :
    Relation.ReflTransGen (MachineStep p) (boundary p s) (boundary p t) := by
  induction hr with
  | refl => exact .refl
  | @tail u v hprefix hstep ih =>
    obtain ⟨_, h | ⟨i, hi, hist⟩⟩ := hstep
    · obtain ⟨a, ha, hsource, rfl⟩ := h
      exact ih.tail (by
        simpa only [boundary, hsource] using
          (MachineStep.jump (registers := u.bits)
            (markers := List.replicate p.instructions.length false) ha))
    · obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hi
      exact ih.trans (machine_instruction_path p ⟨j, hj⟩ u v
        (Program.Reachable.length hprefix hs) hist)

private theorem machine_reachable_valid {p : Program} {s t : MachineState}
    (hs : s.Valid p) (hr : Relation.ReflTransGen (MachineStep p) s t) : t.Valid p := by
  induction hr with
  | refl => exact hs
  | tail _ hstep ih => exact hstep.valid_target ih

private theorem machine_reachable_actual {p : Program} {s t : MachineState}
    (hs : s.Valid p) (hr : Relation.ReflTransGen (MachineStep p) s t) :
    Wiring.Reachable (principalDoors p) (wiring p) s.toState t.toState := by
  induction hr with
  | refl => exact .refl
  | tail hprefix hstep ih =>
    exact ih.tail (hstep.actual (machine_reachable_valid hs hprefix))

private theorem actual_reachable_complete {p : Program} {s : MachineState} {t : State}
    (hs : s.Valid p) (hr : Wiring.Reachable (principalDoors p) (wiring p) s.toState t) :
    ∃ u, Relation.ReflTransGen (MachineStep p) s u ∧ u.toState = t := by
  induction hr with
  | refl => exact ⟨s, .refl, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨u, hu, rfl⟩ := ih
    obtain ⟨v, hv, he⟩ := actual_step_complete (machine_reachable_valid hs hu) hstep
    exact ⟨v, hu.tail hv, he⟩

private theorem certified_reachable {p : Program} {s : MachineState}
    (hr : Relation.ReflTransGen (MachineStep p) (boundary p p.initialState) s) :
    Certified p s := by
  induction hr with
  | refl => exact Certified.boundary p.initialState .refl
  | tail _ hstep ih => exact ih.step hstep

private theorem Certified.accepts {p : Program} {s : MachineState}
    (hs : Certified p s) (hp : s.location = .external p.target) : p.Accepts := by
  cases hs with
  | boundary source hr => exact ⟨source, hr, Place.external.inj hp⟩
  | entry | ready | input | output => cases hp

private theorem principal_initial (p : Program) :
    (principalDoors p).map Door.initial = p.initial ++ closedMarkers p := by
  simp [principalDoors, registerDoors, markerDoors, registerDoor, markerDoor,
    List.zipIdx_map_fst, List.map_const', Function.comp_def, closedMarkers]

/-- The explicit symmetric-door network accepts precisely the executions of its register
program, including instructions with out-of-range register indices. -/
theorem compile_reachability_iff (p : Program) :
    compile p ∈ SelfClosingDoor.Reachability ↔ p.Accepts := by
  change Wiring.compile (principalDoors p) (wiring p) (external p.start) (external p.target) ∈
    SelfClosingDoor.Reachability ↔ p.Accepts
  rw [Wiring.compile_reachability_iff, principal_initial]
  have hs : (boundary p p.initialState).Valid p := ⟨rfl, List.length_replicate⟩
  constructor
  · rintro ⟨t, hr, hp⟩
    obtain ⟨u, hu, he⟩ := actual_reachable_complete hs hr
    exact (certified_reachable hu).accepts
      (Place.code_injective ((congrArg State.location he).trans hp))
  · rintro ⟨t, hr, hp⟩
    exact ⟨(boundary p t).toState, machine_reachable_actual hs (machine_program_path rfl hr),
      by simp only [boundary, MachineState.toState, Place.code, hp]⟩

open _root_.Turing.MultiTapeTM Compiler

private theorem external_polyTime :
    ComputableInPolyTime external encNat encNat := by
  unfold external
  fun_prop

private theorem entry_polyTime : ComputableInPolyTime entry encNat encNat := by
  unfold entry
  fun_prop

private theorem input_polyTime :
    ComputableInPolyTime (fun q : ℕ × Bool => input q.1 q.2)
      (encPair encNat encBool) encNat := by
  unfold input
  fun_prop

private theorem output_polyTime :
    ComputableInPolyTime (fun q : ℕ × Bool => output q.1 q.2)
      (encPair encNat encBool) encNat := by
  have hi := input_polyTime
  unfold output
  fun_prop

private theorem registerDoor_polyTime :
    ComputableInPolyTime (fun q : Bool × ℕ => registerDoor q.2 q.1)
      (encPair encBool encUnary) encDoor := by
  have hr : ComputableInPolyTime (fun q : Bool × ℕ => q.2)
      (encPair encBool encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have hi := input_polyTime
  have ho := output_polyTime
  unfold registerDoor
  fun_prop

private theorem markerDoor_polyTime :
    ComputableInPolyTime (fun q : Instruction × ℕ => markerDoor q.2 q.1)
      (encPair encInstruction encUnary) encDoor := by
  have hj : ComputableInPolyTime (fun q : Instruction × ℕ => q.2)
      (encPair encInstruction encUnary) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  have he := entry_polyTime
  have hx := external_polyTime
  have ho := output_polyTime
  unfold markerDoor
  fun_prop

private theorem diode_polyTime : ComputableInPolyTime Wiring.diode encTunnel encDoor := by
  unfold Wiring.diode
  fun_prop

private theorem registerDoors_polyTime :
    ComputableInPolyTime registerDoors encProgram (encList encDoor) := by
  have hi : ComputableInPolyTime Program.initial encProgram (encList encBool) :=
    ComputableInPolyTime.bitsToList.comp (by fun_prop)
  have hz := (ComputableInPolyTime.zipIdx encBool).comp hi
  have hm := registerDoor_polyTime
  unfold registerDoors
  fun_prop

private theorem markerDoors_polyTime :
    ComputableInPolyTime markerDoors encProgram (encList encDoor) := by
  have hz : ComputableInPolyTime (fun p : Program => p.instructions.zipIdx)
      encProgram (encList (encPair encInstruction encUnary)) := by fun_prop
  have hm := markerDoor_polyTime
  unfold markerDoors
  fun_prop

private theorem coreWiring_polyTime :
    ComputableInPolyTime coreWiring encProgram (encList encTunnel) := by
  have hn : ComputableInPolyTime (fun p : Program => p.initial.length) encProgram encUnary :=
    (ComputableInPolyTime.length encBool).comp (ComputableInPolyTime.bitsToList.comp (by fun_prop))
  have hr : ComputableInPolyTime (fun r : ℕ => r) encUnary encNat :=
    ComputableInPolyTime.unary_to_binary
  have hb : ComputableInPolyTime
      (fun r => [Tunnel.mk (output r false) (input r true),
        Tunnel.mk (output r true) (input r false)]) encUnary (encList encTunnel) := by
    have hi := input_polyTime
    have ho := output_polyTime
    fun_prop
  unfold coreWiring
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (ComputableInPolyTime.flatten encTunnel).comp ((ComputableInPolyTime.map hb).comp
      (by fun_prop : ComputableInPolyTime (fun p : Program => List.range p.initial.length)
        encProgram (encList encUnary)))

private theorem instructionWiring_polyTime :
    ComputableInPolyTime instructionWiring encProgram (encList encTunnel) := by
  have hz : ComputableInPolyTime (fun p : Program => p.instructions.zipIdx)
      encProgram (encList (encPair encInstruction encUnary)) := by fun_prop
  have hb : ComputableInPolyTime
      (fun q : Instruction × ℕ =>
        [Tunnel.mk (external q.1.source) (entry q.2),
          Tunnel.mk (entry q.2) (input q.1.register q.1.guard)])
      (encPair encInstruction encUnary) (encList encTunnel) := by
    have hj : ComputableInPolyTime (fun q : Instruction × ℕ => q.2)
        (encPair encInstruction encUnary) encNat :=
      ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
    have hx := external_polyTime
    have he := entry_polyTime
    have hi := input_polyTime
    fun_prop
  unfold instructionWiring
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (ComputableInPolyTime.flatten encTunnel).comp ((ComputableInPolyTime.map hb).comp hz)

private theorem wiring_polyTime :
    ComputableInPolyTime wiring encProgram (encList encTunnel) := by
  have hcore := coreWiring_polyTime
  have hinstructions := instructionWiring_polyTime
  have hj : ComputableInPolyTime
      (fun a : Tunnel => Tunnel.mk (external a.source) (external a.target))
      encTunnel encTunnel := by
    have hx := external_polyTime
    fun_prop
  unfold wiring
  fun_prop

/-- The complete explicit door network of a finite register program is computable in
polynomial time, with binary labels and the explicitly listed register contents. -/
@[fun_prop] theorem computableInPolyTime_compile :
    ComputableInPolyTime compile encProgram encInstance := by
  have hr := registerDoors_polyTime
  have hm := markerDoors_polyTime
  have hw := wiring_polyTime
  have hd := diode_polyTime
  have hx := external_polyTime
  unfold compile Wiring.compile principalDoors
  fun_prop

end Cslib.Complexity.SelfClosingDoor.RegisterProgram
