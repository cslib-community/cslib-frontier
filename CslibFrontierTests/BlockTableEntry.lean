/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.BlockTableEntry

/-! A native single-entry compiler checks a real one-coin interval, a control sink, and a
subdivision vertex. Invalid letter codes, wrong letter kinds and unequal subdivision bits are
rejected. The local assignment is binary and no table is supplied. -/

namespace CslibFrontierTests.BlockTableEntry

open Turing MultiTapeMachine MultiTapePTM MultiTapeTM MultiTapeATM
open MultiTapeNTM.ChoiceTable Cslib.Turing

private def coin : MultiTapePTM 0 Bool (Fin 1) where
  initial := 0
  tr _ _ _ _ bit := .step
    { inputTape := 0, workTapes := Fin.elim0, output := some bit, state := none }
    Empty.elim Empty.elim

private def vertex (kind : Fin 6) : ℕ := if kind < 3 then 0 else if kind = 3 then 1 else 2

private def assignment (kind : Fin 6) : ℕ :=
  if kind = 1 then 31 else if kind = 2 then 6 else if kind = 4 then 3 else 1

/-- The six fixture entries have values one, zero, zero, one, one, zero. -/
public def value (kind : Fin 6) : Bool := decide (kind = 0 ∨ kind = 3 ∨ kind = 4)

/-- One of six local-entry cases, with a nonempty original input and a binary assignment. -/
public def request (kind : Fin 6) (bit : Fin 2) (claim : Bool) : BlockTableEntry.Request :=
  ⟨[true], 1, 1, 1, vertex kind, assignment kind, bit.val, claim⟩

-- The entry list is only a mathematical reference; the request supplies none of its contents.
private theorem entry_value (kind : Fin 6) :
    tableEntryNum (Equiv.refl (Fin 1)) 1 coin [true] 1 1 (vertex kind)
      (explicitPortsNum 0 1 (letterBits 0 1 1) 1 (vertex kind)) (assignment kind) =
        (value kind).toNat := by
  fin_cases kind <;> decide

-- The source halves, target halves and subdivision pair use the actual network numbering.
example : explicitPortsNum 0 1 (letterBits 0 1 1) 1 0 = [0, 1, 2, 3, 4] := by decide
example : explicitPortsNum 0 1 (letterBits 0 1 1) 1 1 = [5, 6, 7, 8, 9] := by decide
example : explicitPortsNum 0 1 (letterBits 0 1 1) 1 2 = [0, 5] := by decide

-- The compiled format retains binary assignments, including values far above the port count.
example (a : BlockTableEntry.Request) : BlockTableEntry.encRequest a =
    encPair encBits (encPair encUnary (encPair encUnary (encPair encNat
      (encPair encUnary (encPair encNat (encPair encNat encBool))))))
      (a.input, a.width, a.intervals, a.schedule, a.vertex, a.assignment, a.bit, a.claim) := rfl

/-- One actual finite machine handles both requested bits and both claims in all six cases:
the interval count, invalid codes and kinds, control acceptance, and subdivision equality. -/
public theorem native_table_entries :
    ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C E : ℕ),
      ∀ (host : List Bool) (kind : Fin 6) (bit : Fin 2) (claim : Bool),
        let a := request kind bit claim
        let cfg := SharedWordFork.start src atm host (BlockTableEntry.encRequest a) 0
        let time := C * (a.input.length +
          ((BlockTableEntry.encRequest { a with input := [] }).length + 1) ^ E + 1)
        atm.HaltsWithin time cfg ∧ (atm.AcceptsWithin time cfg ↔
          (value kind && decide (bit.val = 0)) = claim) := by
  obtain ⟨u, src, Q, hQ, atm, C, E, h⟩ :=
    BlockTableEntry.exists_evaluator (Equiv.refl (Fin 1)) coin
  refine ⟨u, src, Q, hQ, atm, C, E, ?_⟩
  intro host kind bit claim a cfg time
  obtain ⟨hh, ha⟩ := h host a (by change 0 < 1; decide) (by exact bit.isLt)
  refine ⟨hh, ha.trans ?_⟩
  change (tableEntryNum (Equiv.refl (Fin 1)) 1 coin [true] 1 1 (vertex kind)
    (explicitPortsNum 0 1 (letterBits 0 1 1) 1 (vertex kind))
      (assignment kind)).testBit bit.val = claim ↔ _
  rw [entry_value]
  cases value kind <;> fin_cases bit <;> rfl

end CslibFrontierTests.BlockTableEntry
