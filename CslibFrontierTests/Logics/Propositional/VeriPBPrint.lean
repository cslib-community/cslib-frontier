/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Logics.Propositional.PseudoBoolean.Print

/-! The printers of OPB instances and DIMACS formulas under the ordinary imports of their API:
the kernel evaluates `CNF.toDIMACS` and `reread` (`decide +kernel`), and the round-trip theorems
apply to an instance with an objective, a constant and a negative literal, and to a CNF formula.
`printOPB`, its private word builders and the parsers have no exposed bodies;
`CslibFrontierTests.Logics.Propositional.VeriPBPrintDecide` evaluates them in the kernel, the
printed text of both instances included. -/

@[expose] public section

namespace CslibFrontierTests.Logics.Propositional.VeriPBPrint

open Cslib.Logic.PL Cslib.Logic.PL.VeriPB Cslib.Logic.PL.VeriPB.Text

/-- Minimize `x1 + x2 + x3` subject to `x1 + x2 >= 1` and `x2 + x3 >= 1`. -/
def cover : Instance :=
  ⟨[⟨[(1, (0, true)), (1, (1, true))], 1⟩, ⟨[(1, (1, true)), (1, (2, true))], 1⟩],
    some ⟨[(0, 1), (1, 1), (2, 1)], 0⟩, none⟩


/-- An instance with a negative literal, a negative weight, a constant and a preserved set. -/
def mixed : Instance :=
  ⟨[⟨[(2, (0, true)), (3, (4, false))], 3⟩, ⟨[], 0⟩], some ⟨[(4, -2), (0, 0)], 7⟩, some [4, 0]⟩

-- Both are in the normal form of the parser, so they are read back exactly.
example : parseOPB (printOPB cover) = some cover := parseOPB_printOPB_of_normal (by decide)
example : parseOPB (printOPB mixed) = some mixed := parseOPB_printOPB_of_normal (by decide)

-- Outside it, the terms on one variable are merged: `x1 + x1 + ~x1 >= 2` is read back as
-- `x1 >= 1`, with the same solutions.
example : reread ⟨[⟨[(1, (0, true)), (1, (0, true)), (1, (0, false))], 2⟩], none, none⟩ =
    ⟨[⟨[(1, (0, true))], 1⟩], none, none⟩ := by
  decide +kernel

example : ¬ Normal ⟨[⟨[(1, (0, true)), (1, (0, true))], 2⟩], none, none⟩ := by decide

/-- A CNF formula with a repeated literal and an empty clause. -/
def φ : CNF ℕ := [[(0, true), (2, false)], [(1, true), (1, true)], []]

example : CNF.toDIMACS φ = "p cnf 3 3\n1 -3 0\n2 2 0\n0\n" := by decide +kernel
example : parseDIMACS (CNF.toDIMACS φ) = some φ := parseDIMACS_toDIMACS φ
example : CNF.ofDIMACS (CNF.toDIMACS φ) = .ok φ := CNF.ofDIMACS_toDIMACS φ

end CslibFrontierTests.Logics.Propositional.VeriPBPrint

end
