/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Yates
import CslibFrontier.Algorithms.WordRAM.Yates

/-!
# Tests for Yates's algorithm on tables (pure and Word-RAM)

Concrete kernel-checked examples (using `decide +kernel`, never `native_decide`) of
`CslibFrontier.Algorithms.Lean.Yates` and `CslibFrontier.Algorithms.WordRAM.Yates` as an
encapsulated downstream `module` client:

* the cells of subsets (`maskIndex`, `maskSet`);
* the pure fast zeta and Möbius transforms on tables with `4` and `8` cells and the degenerate
  table with one cell (`n = 0`), together with `getElem_zeta_maskIndex` and
  `getElem_mobius_maskIndex`;
* checked `O((n + 1) · 2 ^ n)` width-blind deterministic standard-basis word-RAM executions
  (`exists_zetaNat_program`, `exists_zetaInt_program`, `exists_mobiusInt_program`) on `n = 0, 2, 3`
  at explicit fitting word widths (`FitsWidth`).
-/

set_option linter.privateModule false

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
example : zeta (n := 0) #v[5] = #v[5] ∧ mobius (n := 0) #v[(-5 : ℤ)] = #v[-5] := by
  decide +kernel

/-- Reading `zeta` at the cell of `{0, 1}` via `getElem_zeta_maskIndex`. -/
example : subsetZeta (fun T => (#v[1, 2, 3, 4] : Vector ℕ (2 ^ 2))[(maskIndex T : ℕ)])
    (Finset.univ : Finset (Fin 2)) = 10 := by
  rw [← getElem_zeta_maskIndex]
  decide +kernel

/-- Reading `mobius` at the cell of `{0, 1}` via `getElem_mobius_maskIndex`. -/
example : subsetMobius (fun T => (#v[(1 : ℤ), 3, 4, 10] : Vector ℤ (2 ^ 2))[(maskIndex T : ℕ)])
    (Finset.univ : Finset (Fin 2)) = 4 := by
  rw [← getElem_mobius_maskIndex]
  decide +kernel

/-! ### Word-RAM certificates (`O((n + 1) · 2 ^ n)`) -/

def natEx2 : NatInstance where
  n := 2
  entries := #v[1, 2, 3, 4]

def natEx3 : NatInstance where
  n := 3
  entries := Vector.replicate 8 1

def natEx0 : NatInstance where
  n := 0
  entries := #v[5]

example : natEx2.FitsWidth 7 := by decide +kernel

/-- Unsigned fast zeta Word-RAM program on `n = 2`, `n = 3`, and boundary `n = 0`. -/
example : ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
    (∃ t₂, ExecutesList 7 prog (State.init natEx2.encode) [1, 3, 4, 10] t₂ ∧ t₂ ≤ C * 12) ∧
    (∃ t₃, ExecutesList 8 prog (State.init natEx3.encode) [1, 2, 2, 4, 2, 4, 4, 8] t₃ ∧
      t₃ ≤ C * 32) ∧
    (∃ t₀, ExecutesList 7 prog (State.init natEx0.encode) [5] t₀ ∧ t₀ ≤ C) := by
  obtain ⟨r, C, prog, hnw, hrf, hprog⟩ := exists_zetaNat_program
  have hf₂ : natEx2.FitsWidth 7 := by decide +kernel
  have hf₃ : natEx3.FitsWidth 8 := by decide +kernel
  have hf₀ : natEx0.FitsWidth 7 := by decide +kernel
  obtain ⟨t₂, he₂, hl₂⟩ := hprog natEx2 7 hf₂ (natEx2.inputFits hf₂)
  obtain ⟨t₃, he₃, hl₃⟩ := hprog natEx3 8 hf₃ (natEx3.inputFits hf₃)
  obtain ⟨t₀, he₀, hl₀⟩ := hprog natEx0 7 hf₀ (natEx0.inputFits hf₀)
  exact ⟨r, C, prog, hnw, hrf,
    ⟨t₂, (show (zeta natEx2.entries).toList = [1, 3, 4, 10] by decide +kernel) ▸ he₂,
      by simpa [natEx2] using hl₂⟩,
    ⟨t₃, (show (zeta natEx3.entries).toList = [1, 2, 2, 4, 2, 4, 4, 8] by decide +kernel) ▸ he₃,
      by simpa [natEx3] using hl₃⟩,
    ⟨t₀, (show (zeta natEx0.entries).toList = [5] by decide +kernel) ▸ he₀,
      by simpa [natEx0] using hl₀⟩⟩

def intEx2 : IntInstance where
  n := 2
  entries := #v[(1 : ℤ), -2, 3, 4]

def intEx0 : IntInstance where
  n := 0
  entries := #v[(-5 : ℤ)]

example : intEx2.FitsWidth 8 := by decide +kernel

/-- Signed fast zeta Word-RAM program on mixed-sign `n = 2` and boundary `n = 0`. -/
example : ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
    (∃ t₂, ExecutesList 8 prog (State.init intEx2.encode)
      ([1, -1, 4, 6].map Signed.encode) t₂ ∧ t₂ ≤ C * 12) ∧
    (∃ t₀, ExecutesList 8 prog (State.init intEx0.encode) [Signed.encode (-5)] t₀ ∧ t₀ ≤ C) := by
  obtain ⟨r, C, prog, hnw, hrf, hprog⟩ := exists_zetaInt_program
  have hf₂ : intEx2.FitsWidth 8 := by decide +kernel
  have hf₀ : intEx0.FitsWidth 8 := by decide +kernel
  obtain ⟨t₂, he₂, hl₂⟩ := hprog intEx2 8 hf₂ (intEx2.inputFits hf₂)
  obtain ⟨t₀, he₀, hl₀⟩ := hprog intEx0 8 hf₀ (intEx0.inputFits hf₀)
  exact ⟨r, C, prog, hnw, hrf,
    ⟨t₂, (show (zeta intEx2.entries).toList = [(1 : ℤ), -1, 4, 6] by decide +kernel) ▸ he₂,
      by simpa [intEx2] using hl₂⟩,
    ⟨t₀, (show (zeta intEx0.entries).toList.map Signed.encode = [Signed.encode (-5)] by
        decide +kernel) ▸ he₀,
      by simpa [intEx0] using hl₀⟩⟩

/-- Signed fast Möbius Word-RAM program on mixed-sign `n = 2` and boundary `n = 0`. -/
example : ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
    (∃ t₂, ExecutesList 8 prog (State.init intEx2.encode)
      ([1, -3, 2, 4].map Signed.encode) t₂ ∧ t₂ ≤ C * 12) ∧
    (∃ t₀, ExecutesList 8 prog (State.init intEx0.encode) [Signed.encode (-5)] t₀ ∧ t₀ ≤ C) := by
  obtain ⟨r, C, prog, hnw, hrf, hprog⟩ := exists_mobiusInt_program
  have hf₂ : intEx2.FitsWidth 8 := by decide +kernel
  have hf₀ : intEx0.FitsWidth 8 := by decide +kernel
  obtain ⟨t₂, he₂, hl₂⟩ := hprog intEx2 8 hf₂ (intEx2.inputFits hf₂)
  obtain ⟨t₀, he₀, hl₀⟩ := hprog intEx0 8 hf₀ (intEx0.inputFits hf₀)
  exact ⟨r, C, prog, hnw, hrf,
    ⟨t₂, (show (mobius intEx2.entries).toList = [(1 : ℤ), -3, 2, 4] by decide +kernel) ▸ he₂,
      by simpa [intEx2] using hl₂⟩,
    ⟨t₀, (show (mobius intEx0.entries).toList.map Signed.encode = [Signed.encode (-5)] by
        decide +kernel) ▸ he₀,
      by simpa [intEx0] using hl₀⟩⟩

end CslibFrontierTests.Algorithms.Lean.Yates
