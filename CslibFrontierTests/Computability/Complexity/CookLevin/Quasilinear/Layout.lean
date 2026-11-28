/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Clause

/-!
# Tests for the layout of the quasilinear formula

Concrete checks, by `decide` on the layout of one work tape, a two-bit state code, input length
`1` and slack `0`, for
`CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Layout` and `.Clause`:

* the derived widths and the number of constraints of each family;
* the numbering of the families (`Family.index`, `Family.ofIndex?`);
* the bit codes of symbols, writes, moves and views of the output decode back
  (`decSym`, `decWrite`, `decMove`, `decOut`), and decoding a state out of range gives `none`;
* the literals of a field of a record (`fieldLits`);
* `clauseAt` at the index of the first gate is the clause of that gate, and at an index that
  names no gate it is the tautology (`tautClause`), which every assignment satisfies.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.Layout

open Cslib.Complexity.CookLevin.Quasilinear Cslib.Logic.PL Turing

/-- The layout of one work tape, a state code of width `2`, input length `1` and slack `0`. -/
def Λ : Layout := ⟨1, 2, 1, 0⟩

/-- No allowed pairs of finite parts. -/
def D : MachineData := ⟨[], [], []⟩

/-! ### The widths -/

/-- The derived widths: `τ = 2` bits of time, `N = 4` records, and so on. -/
example : Λ.τ = 2 ∧ Λ.N = 4 ∧ Λ.W = 4 ∧ Λ.I = 3 ∧ Λ.C = 18 ∧ Λ.RB = 25 ∧ Λ.P = 10 ∧
    Λ.L = 3 := by decide

/-- The number of constraints of each family, in the order of the numbering. -/
example : Family.all.map Λ.count = [1, 1, 1, 3, 27, 12, 3, 120, 4] := by decide

/-- `countAt` is `count` of the family with that number, and `0` past the last family. -/
example : (List.range 10).map Λ.countAt = [1, 1, 1, 3, 27, 12, 3, 120, 4, 0] := by decide

/-- The numbering of the families is the position in `Family.all`. -/
example : Family.all.map Family.index = [0, 1, 2, 3, 4, 5, 6, 7, 8] ∧
    Family.ofIndex? 3 = some .step ∧ Family.ofIndex? 9 = none := by decide

/-- The first record's variables are numbered after the constants. -/
example : Layout.vTT = 0 ∧ Layout.vFF = 1 ∧ Λ.vRec 0 0 = 2 ∧ Λ.vRec 1 0 = 202 := by decide

/-! ### Codes -/

/-- Symbols, writes and moves decode from their bits. -/
example : ([none, some false, some true].all fun s => decSym (symBit s) == s) = true ∧
    ([none, some none, some (some false), some (some true)].all
      fun w => decWrite (writeBit w) == w) = true ∧
    ([SignType.zero, .pos, .neg].all fun m => decMove (moveBit m) == m) = true ∧
    ([OutView.empty, .one false, .one true, .many].all
      fun o => decOut (outBit o) == o) = true := by decide

/-- A state code out of range decodes to no state: the all-ones code is `7`, above the `3`
states of `Option Bool`. -/
example : decState (State := Bool) (fun _ => true) = none := by decide

/-- The width of the code of states of `Option Bool`. -/
example : stWidth Bool = 3 := by decide

/-! ### Literals and clauses -/

/-- The literals saying that the bits of record `2` from offset `1` are `[true, false]`. -/
example : Λ.fieldLits 2 1 [true, false] = [(Λ.vRec 2 1, true), (Λ.vRec 2 2, false)] := by decide

/-- Clause `0` is slot `0` of the first gate, the gate `¬ v_FF` defining the first fresh
variable. -/
example :
    Λ.clauseAt D [true] 0 = (Gate.mk .not (Λ.vAux 0 .consts 0 0) Layout.vFF 0 0).clause 0 := by
  decide

/-- An index in the family with number `9`, which there is none of, names no gate. -/
example : Λ.clauseAt D [true] (4 * Λ.G 0 * Λ.MAXI * 9) = Layout.tautClause := by decide

/-- The tautology is satisfied by every assignment. -/
example : ∀ b : Bool, Clause.eval (fun _ => b) Layout.tautClause = true := by decide

/-- The tautology has three literals, like every clause of the formula. -/
example : Layout.tautClause.length = 3 := rfl

end CslibFrontierTests.Computability.Complexity.CookLevin.Quasilinear.Layout
