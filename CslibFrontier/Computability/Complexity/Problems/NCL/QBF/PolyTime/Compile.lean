/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.QBF.PolyTime.Emit
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Fixed

/-!
# Compiling circuit instructions

The QBF fragment table instantiates the finite-alphabet compiler. Its primitive word expansion,
wire stack, edge counter and emitted vertices agree with the source emitter. Compilation uses
unary offsets and produces ordinary binary graph data in polynomial time.

## Main definitions

* `Cslib.Complexity.NCL.QBF.Emit.language`: the circuit instruction table.
* `Cslib.Complexity.NCL.QBF.Emit.run`, `Cslib.Complexity.NCL.QBF.Emit.compile`: instruction
  execution and graph compilation.

## Main results

* `Cslib.Complexity.NCL.QBF.Emit.run_eq_expand`,
  `Cslib.Complexity.NCL.QBF.Emit.compile_eq_expand`: primitive word agreement.
* `Cslib.Complexity.NCL.QBF.Emit.computableInPolyTime_compile`: polynomial-time compilation.
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

open _root_.Turing.MultiTapeTM

/-- The fixed primitive fragment table of the QBF instruction emitter. -/
@[expose] def language : Word.Fixed.Language where
  Opcode := Opcode
  enumeration := inferInstance
  fragment := Opcode.fragment

/-- Execute circuit instructions on the wire stack and accumulated graph data. -/
@[expose] def run (p : Program) (st : Word.State) : Word.State := language.run p st

/-- Instruction execution agrees with primitive word expansion. -/
theorem run_eq_expand (p : Program) (st : Word.State) : run p st = Word.run (expand p) st :=
  language.run_eq_expand p st

/-- Compile instructions to their vertex list and binary edge count. -/
@[expose] def compile (p : Program) : AndOrGraph :=
  let st := run p ⟨[], 0, []⟩
  ⟨st.verts, st.next⟩

/-- Instruction compilation agrees with primitive word compilation. -/
theorem compile_eq_expand (p : Program) : compile p = Word.compile (expand p) :=
  language.compile_eq_expand p

/-- Compile circuit instructions to ordinary binary graph data in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_compile : ComputableInPolyTime compile encProgram encAndOrGraph :=
  language.computableInPolyTime_compile

end Cslib.Complexity.NCL.QBF.Emit
