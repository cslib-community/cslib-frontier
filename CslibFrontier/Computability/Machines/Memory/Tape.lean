/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Memory.Basic
public import Cslib.Computability.Machines.Turing.MultiTape.Configuration

/-!
# Tapes as memory modules

Tapes whose cells are a function from positions to optional symbols (`none` is blank), as in the
multi-tape machines of `Turing.Cfg`, rather than the zipper `Cslib.Turing.BiTape`:

* `MemoryModule.workTape Symbol`: a read-write tape over the integers with one head, the work
  tape of `Turing.Cfg`. An operation optionally writes the cell under the head and then displaces
  the head.
* `MemoryModule.boundedInput input`: the read-only input tape of `Turing.Cfg`, whose head stays
  within one cell of either end of `input` (`Turing.moveInputPos`). It is the input of
  sublinear-space machines.
* `MemoryModule.output Symbol`: a write-only output tape, which an operation extends by at most
  one symbol and which the controller does not see.

The work tape, the input tape and the output tape are those of `Turing.Cfg`
(`Turing.MultiTapeTM.step_toMemoryMachine`, using `boundedInput_read`).

## Main definitions

* `Cslib.Machines.CellTape`, `MemoryModule.workTape`.
* `MemoryModule.boundedInput`, `MemoryModule.output`.
-/

public section

namespace Cslib.Machines

/-- A tape over the integers, with blank cells `none`, and the position of its head. -/
@[ext] structure CellTape (Symbol : Type*) where
  /-- The contents of each cell. -/
  cells : ℤ → Option Symbol
  /-- The position of the head. -/
  head : ℤ

namespace MemoryModule

variable (Symbol : Type*)

/-- A read-write tape with one head. The controller sees the cell under the head; an operation
`(write, move)` writes `s` there if `write = some s`, and then adds `move` to the head
position. -/
@[expose] def workTape :
    MemoryModule (CellTape Symbol) (Option Symbol) (Option (Option Symbol) × ℤ) where
  tr t
    | (write, move) => ⟨write.elim t.cells (Function.update t.cells t.head), t.head + move⟩
  read t := t.cells t.head

variable {Symbol}

/-- The read-only input tape holding `input`, with head positions `0, …, input.length + 1`: the
controller sees the input symbol under the head, or `none` on the two boundary cells, and an
operation moves the head by at most one cell without leaving these positions. -/
@[expose] def boundedInput (input : List Symbol) :
    MemoryModule (Fin (input.length + 2)) (Option Symbol) SignType where
  tr := Turing.moveInputPos
  read p := if p.val = 0 then none else input[p.val - 1]?

/-- The input tape read by `boundedInput` is the one read by a `Turing.Cfg`. -/
theorem boundedInput_read {k : ℕ} {State : Type*} {input : List Symbol}
    (cfg : Turing.Cfg k Symbol State input) :
    (boundedInput input).read cfg.inputPos = cfg.inputSymbol := by
  have := cfg.inputPos.isLt
  simp only [boundedInput, Turing.Cfg.inputSymbol]
  split_ifs with h₀ h₁ h₂ <;> grind

variable (Symbol)

/-- A write-only output tape: the controller sees nothing, and an operation appends at most one
symbol. -/
@[expose] def output : MemoryModule (List Symbol) Unit (Option Symbol) where
  tr l o := l ++ o.toList
  read _ := ()

end MemoryModule

end Cslib.Machines
