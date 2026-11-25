/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import CslibFrontier.Computability.Machines.Memory.DA
import CslibFrontier.Computability.Machines.Memory.DPDA
import CslibFrontier.Computability.Machines.Memory.SingleTape
import CslibFrontier.Computability.Machines.Memory.Tape
import CslibFrontier.Computability.Machines.Memory.URM

/-!
# Tests for memory modules and memory machines

A parity automaton run as a memory computer, accepting and rejecting, and the space bound on its
runs; a pushdown automaton for `aⁿbⁿ` whose memory machine pops the stack; a URM program
computing `2`; a product of `k` tapes and a work tape; and the reason modules are not lenses:
after a tape write and a move, the head does not see the written symbol.
-/

namespace CslibFrontierTests.MemoryMachine

open Cslib Cslib.Machines Cslib.Automata Relation

/-- The automaton that tracks the parity of the number of `true`s and accepts odd parity. -/
def parity : DA.FinAcc Bool Bool where
  tr q a := q ^^ a
  start := false
  accept := {true}

/-- The memory machine of `parity` consumes `[true, false, true]` in three steps, with even
parity. -/
example :
    RelatesInSteps parity.toMemoryComputer.Step (false, [true, false, true]) (false, []) 3 :=
  parity.relatesInSteps_toMemoryComputer false [true, false, true]

/-- `[true, true, true]` is accepted: the memory computer outputs `True`. -/
example : parity.toMemoryComputer.eval [true, true, true] = Part.some True := by
  rw [parity.eval_toMemoryComputer]
  simp [Acceptor.Accepts, parity, FLTS.mtr]

/-- `[true, true]` is rejected: the memory computer outputs `False`. -/
example : parity.toMemoryComputer.eval [true, true] = Part.some False := by
  rw [parity.eval_toMemoryComputer]
  simp [Acceptor.Accepts, parity, FLTS.mtr]

/-- The unread input never grows, so every configuration reachable on `[true, true]` holds at
most `2 + 2` symbols: the space bound `size_le_of_haltsIn` with `size` the unread length. -/
example (c : Bool × List Bool)
    (hc : ReflTransGen parity.toMemoryComputer.Step (false, [true, true]) c) :
    c.2.length ≤ 4 :=
  parity.toMemoryComputer.size_le_of_haltsIn (fun c => c.2.length)
    (fun x y hxy => by
      obtain ⟨q, _ | ⟨a, w⟩⟩ := x
      · simp [MemoryMachine.Step] at hxy
      · simp only [MemoryMachine.Step, DA.FinAcc.step_toMemoryComputer_cons, Option.mem_def,
          Option.some.injEq] at hxy
        subst hxy
        simp only [List.length_cons]
        omega)
    ⟨parity.relatesInSteps_toMemoryComputer false [true, true], rfl⟩ hc

/-- A pushdown automaton for `aⁿbⁿ` (`a = false`, `b = true`): in state `false` it pushes a
marker for each `a`; on the first `b` it moves to state `true` and pops. -/
def anbn : DPDA Bool Bool (Option Unit) where
  start := false
  bottom := none
  accept := {true}
  transition q γ a :=
    match q, γ, a with
    | false, _, some false => some ⟨false, [some (), γ]⟩
    | _, some (), some true => some ⟨true, []⟩
    | _, _, _ => none
  epsilon_exclusive q γ a h := by
    rcases q with _ | _ <;> rcases γ with _ | ⟨⟩ <;> simp at h

/-- On `ab`, the memory machine of `anbn` pushes a marker, pops it, and reaches the bottom of
the stack in state `true` with the input consumed, where it halts. -/
example : RelatesInSteps anbn.toMemoryMachine.Step (false, [false, true], [none])
    (true, [], [none]) 2 ∧ anbn.toMemoryMachine.step (true, [], [none]) = none :=
  ⟨.head _ (false, [true], [some (), none]) _ _ rfl (.head _ _ _ _ rfl (.refl _)), rfl⟩

/-- The URM program `S 0; S 0` computes `2` from no inputs, in two steps of its memory
computer. -/
example : URM.eval [.S 0, .S 0] [] = Part.some 2 := by
  rw [← URM.eval_toMemoryComputer, Part.eq_some_iff, MemoryComputer.mem_eval_iff]
  exact ⟨2, _, 2, le_rfl, ⟨.head _ _ _ _ rfl (.head _ _ _ _ rfl (.refl _)), rfl⟩, rfl⟩

/-- Three tapes side by side: one operation updates each tape. -/
example :
    (MemoryModule.pi fun _ : Fin 3 => MemoryModule.biTape Bool).read
      ((MemoryModule.pi fun _ : Fin 3 => MemoryModule.biTape Bool).tr
        (fun _ => Turing.BiTape.nil) fun i => ⟨some (decide (i = 0)), none⟩) =
      fun i : Fin 3 => some (decide (i = 0)) := rfl

/-- A work tape: write at the origin and step right, then step back and read the written
symbol. -/
example :
    let T := MemoryModule.workTape Bool
    T.read (T.tr (T.tr ⟨fun _ => none, 0⟩ (some (some true), 1)) (none, -1)) = some true := by
  simp [MemoryModule.workTape]

/-- Modules are not lenses: a write followed by a move does not read back the written symbol. -/
example : (MemoryModule.biTape Bool).read
    ((MemoryModule.biTape Bool).tr Turing.BiTape.nil ⟨some true, some .right⟩) = none := rfl

end CslibFrontierTests.MemoryMachine
