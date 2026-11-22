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

* `Cslib.Complexity.NCL.QBF.Emit.language`: the QBF fragment table for the generic compiler.
-/

public section

namespace Cslib.Complexity.NCL.QBF.Emit

/-- The fixed primitive fragment table of the QBF instruction emitter. -/
@[expose] def language : Word.Fixed.Language where
  Opcode := Opcode
  enumeration := inferInstance
  fragment := Opcode.fragment

end Cslib.Complexity.NCL.QBF.Emit
