/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Basic

/-!
# Guarded Boolean register programs

A finite control graph carries directed jumps and instructions that test and write one Boolean
register. These programs are the intermediate representation in the reduction from constraint
logic to directed symmetric self-closing doors. Registers are explicit bit lists; control labels
and register indices are natural numbers.

## Main definitions

* `Cslib.Complexity.SelfClosingDoor.RegisterProgram.Instruction`: a guarded one-register update.
* `Cslib.Complexity.SelfClosingDoor.RegisterProgram.Program`: a finite register program.
* `Cslib.Complexity.SelfClosingDoor.RegisterProgram.Program.Step`: its operational semantics.
-/

public section

namespace Cslib.Complexity.SelfClosingDoor.RegisterProgram

/-- A directed control edge testing one register and replacing its value. -/
structure Instruction where
  /-- Source control label. -/
  source : ℕ
  /-- Target control label. -/
  target : ℕ
  /-- The register accessed by this instruction. -/
  register : ℕ
  /-- The value required before execution. -/
  guard : Bool
  /-- The value written on execution. -/
  write : Bool
  deriving DecidableEq, Inhabited

/-- A finite Boolean register program with a designated accepting control label. -/
structure Program where
  /-- Guarded register instructions. -/
  instructions : List Instruction
  /-- Directed jumps preserving every register. -/
  jumps : List Tunnel
  /-- Initial register values. -/
  initial : List Bool
  /-- Initial control label. -/
  start : ℕ
  /-- Accepting control label. -/
  target : ℕ
  deriving DecidableEq, Inhabited

/-- Test the old value at an allocated register and write the prescribed new value. -/
@[expose] def Instruction.Step (i : Instruction) (s t : State) : Prop :=
  i.register < s.bits.length ∧ s.location = i.source ∧
    s.bits.getD i.register false = i.guard ∧
    t = ⟨i.target, s.bits.set i.register i.write⟩

/-- The initial control label and register word of a program. -/
@[expose] def Program.initialState (p : Program) : State := ⟨p.start, p.initial⟩

/-- A directed jump or a guarded register update. -/
@[expose] def Program.Step (p : Program) (s t : State) : Prop :=
  s.bits.length = p.initial.length ∧
    ((∃ a ∈ p.jumps, s.location = a.source ∧ t = ⟨a.target, s.bits⟩) ∨
      ∃ i ∈ p.instructions, i.Step s t)

/-- Finite program execution. -/
abbrev Program.Reachable (p : Program) := Relation.ReflTransGen p.Step

/-- Acceptance constrains the final control label and leaves the final registers arbitrary. -/
@[expose] def Program.Accepts (p : Program) : Prop :=
  ∃ t, p.Reachable p.initialState t ∧ t.location = p.target

/-- Every instruction preserves the number of registers. -/
theorem Instruction.Step.length {i : Instruction} {s t : State} (h : i.Step s t) :
    t.bits.length = s.bits.length := by
  rcases h with ⟨_, _, _, rfl⟩
  exact List.length_set

/-- Every program step preserves its register width. -/
theorem Program.Step.length {p : Program} {s t : State} (h : p.Step s t) :
    t.bits.length = p.initial.length := by
  rcases h with ⟨hs, h | h⟩
  · rcases h with ⟨_, _, _, rfl⟩
    exact hs
  · rcases h with ⟨i, _, hi⟩
    exact hi.length.trans hs

/-- Finite execution preserves the width of a well-formed register state. -/
theorem Program.Reachable.length {p : Program} {s t : State} (h : p.Reachable s t)
    (hs : s.bits.length = p.initial.length) : t.bits.length = p.initial.length := by
  induction h with
  | refl => exact hs
  | tail _ h _ => exact h.length

end Cslib.Complexity.SelfClosingDoor.RegisterProgram
