/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Yates
import CslibFrontier.Algorithms.WordRAM.Yates

/-!
# Tests for Yates's algorithm on tables

Concrete kernel-checked examples (using `decide +kernel`, never `native_decide`) of
`CslibFrontier.Algorithms.Lean.Yates` and `CslibFrontier.Algorithms.WordRAM.Yates`:

* the cells of subsets (`maskIndex`, `maskSet`);
* the pure fast zeta and Möbius transforms on tables with `4` and `8` cells and the degenerate
  table with one cell (`n = 0`), together with `getElem_zeta_maskIndex`;
* checked `O((n + 1) · 2 ^ n)` standard-basis word-RAM executions (`zetaNatProgram`,
  `zetaIntProgram`, `mobiusIntProgram`) at explicit fitting word widths (`FitsWidth`).
-/

namespace CslibFrontierTests.Algorithms.Lean.Yates

open Cslib.Algorithms.Lean.Yates Cslib.BitString
open Cslib.Algorithms.WordRAM.Yates Cslib.WordRAM

/-! ### Cells -/

/-- The cell of `{0, 2} ⊆ Fin 3` is `0b101 = 5`. -/
example : (maskIndex ({0, 2} : Finset (Fin 3)) : ℕ) = 5 := by decide +kernel

/-- The set of cell `6 = 0b110` is `{1, 2}`. -/
example : maskSet 3 6 = {1, 2} := by decide +kernel

/-! ### Pure zeta and Möbius transforms -/

/-- Cells `∅, {0}, {1}, {0, 1}` hold `1, 2, 3, 4`; their subset sums are `1, 3, 4, 10`. -/
example : zeta (n := 2) #v[1, 2, 3, 4] = #v[1, 3, 4, 10] := by decide +kernel

/-- The fast Möbius transform inverts it. -/
example : mobius (n := 2) #v[(1 : ℤ), 3, 4, 10] = #v[1, 2, 3, 4] := by decide +kernel

/-- Eight cells, all `1`: the subset sums are the powers of two `2 ^ #S`. -/
example : zeta (n := 3) (Vector.replicate 8 1) = #v[1, 2, 2, 4, 2, 4, 4, 8] := by
  decide +kernel

/-- Edge case `n = 0`: one cell, no passes. -/
example : zeta (n := 0) #v[5] = #v[5] := by decide +kernel

/-- The run above, read at the cell of `{0, 1}`, against `getElem_zeta_maskIndex`. -/
example : subsetZeta (fun T => (#v[1, 2, 3, 4] : Vector ℕ (2 ^ 2))[(maskIndex T : ℕ)])
    (Finset.univ : Finset (Fin 2)) = 10 := by
  rw [← getElem_zeta_maskIndex]
  decide +kernel

/-! ### Word-RAM certificates (`O((n + 1) · 2 ^ n)`) -/

def natEx2 : NatInstance where
  n := 2
  entries := #v[1, 2, 3, 4]

example : natEx2.FitsWidth 7 := by
  unfold NatInstance.FitsWidth NatInstance.wordBound NatInstance.totalSum
  decide +kernel

example : ∃ steps ≤ 40 * ((natEx2.n + 1) * 2 ^ natEx2.n),
    ExecutesList 7 zetaNatProgram (State.init natEx2.encode) [1, 3, 4, 10] steps := by
  have h := executesList_zetaNatProgram (w := 7) natEx2 (by
    unfold NatInstance.FitsWidth NatInstance.wordBound NatInstance.totalSum
    decide +kernel)
  have hvec : (zeta natEx2.entries).toList = [1, 3, 4, 10] := by decide +kernel
  simpa [hvec] using h

def intEx2 : IntInstance where
  n := 2
  entries := #v[(1 : ℤ), -2, 3, 4]

example : intEx2.FitsWidth 8 := by
  unfold IntInstance.FitsWidth IntInstance.wordBound IntInstance.sumAbs
  decide +kernel

example : ∃ steps ≤ 48 * ((intEx2.n + 1) * 2 ^ intEx2.n),
    ExecutesList 8 zetaIntProgram (State.init intEx2.encode)
      ([1, -1, 4, 6].map Signed.encode) steps := by
  have h := executesList_zetaIntProgram (w := 8) intEx2 (by
    unfold IntInstance.FitsWidth IntInstance.wordBound IntInstance.sumAbs
    decide +kernel)
  have hvec : (zeta intEx2.entries).toList = [(1 : ℤ), -1, 4, 6] := by decide +kernel
  simpa [hvec] using h

example : ∃ steps ≤ 48 * ((intEx2.n + 1) * 2 ^ intEx2.n),
    ExecutesList 8 mobiusIntProgram (State.init intEx2.encode)
      ([1, -3, 2, 4].map Signed.encode) steps := by
  have h := executesList_mobiusIntProgram (w := 8) intEx2 (by
    unfold IntInstance.FitsWidth IntInstance.wordBound IntInstance.sumAbs
    decide +kernel)
  have hvec : (mobius intEx2.entries).toList = [(1 : ℤ), -3, 2, 4] := by decide +kernel
  simpa [hvec] using h

/-- Edge case `n = 0` on the Word-RAM. -/
example : ∃ steps ≤ 40,
    ExecutesList 7 zetaNatProgram (State.init (NatInstance.mk 0 #v[5]).encode) [5] steps := by
  simpa [zeta, transform, pass] using
    executesList_zetaNatProgram (NatInstance.mk 0 #v[5]) (by
      unfold NatInstance.FitsWidth NatInstance.wordBound NatInstance.totalSum
      decide +kernel)

end CslibFrontierTests.Algorithms.Lean.Yates
