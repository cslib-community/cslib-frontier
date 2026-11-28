/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandProgram
public import CslibFrontier.Algorithms.MatrixMultiplication.Schonhage.MaskTable

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged native binary-mask population scans

## Main results

* `BandPreparation.exec_population`: the actual remainder/division loop computes the
  population in `6L+5` instructions, preserves memory and changes only its four local registers.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.MatrixMultiplication.Schonhage.MaskTable

/-- Popcount is a native loop, with a fit derived for each arithmetic operation from a
bound on its original mask and depth. No memory cell is touched. -/
theorem exec_population {w : ℕ} (L a : ℕ) (x : Data 96)
    (hl : x.regs levels = L) (ha : x.regs mask = a)
    (ho : x.regs one = 1) (ht : x.regs two = 2) (hfit : Fits w (a + L + 2)) :
    ∃ y, ExecWithin w populationCode x y (6 * L + 5) ∧
      y.regs population = MaskTable.population L a ∧ y.mem = x.mem ∧
      (∀ i, i ≠ residue → i ≠ population → i ≠ counter → i ≠ digit →
        y.regs i = x.regs i) := by
  let P (j : ℕ) (y : Data 96) : Prop :=
    y.mem = x.mem ∧ y.regs levels = L ∧ y.regs one = 1 ∧ y.regs two = 2 ∧
      y.regs residue ≤ a ∧
      y.regs population + MaskTable.population (L - j) (y.regs residue) =
        MaskTable.population L a
  have hb (y : Data 96) (hy : P (y.regs counter) y) (hjL : y.regs counter < L) :
      ∃ z, ExecWithin w (ram[
          digit ← residue % two; population ← population + digit;
          residue ← residue / two; counter ← counter + one ]) y z 4 ∧
        P (y.regs counter + 1) z ∧ z.regs counter = y.regs counter + 1 := by
    obtain ⟨hm, hL, h1, h2, hr, hp⟩ := hy
    have hrec : MaskTable.population (L - y.regs counter) (y.regs residue) =
        y.regs residue % 2 +
          MaskTable.population (L - (y.regs counter + 1)) (y.regs residue / 2) := by
      rw [show L - y.regs counter = (L - (y.regs counter + 1)) + 1 by omega, population_succ]
    have hpop := population_le L a
    wram_exec *
    dsimp only [P]
    wram_simp *
    exact ⟨hm, (Nat.div_le_self _ _).trans hr, by omega⟩
  suffices ∃ y, ExecWithin w populationCode x y (6 * L + 5) ∧
      y.regs population = MaskTable.population L a ∧ y.mem = x.mem by
    obtain ⟨y, he, hp, hm⟩ := this
    exact ⟨y, he, hp, hm, fun i hr hp' hc hd => he.regs_eq (by decide +revert)⟩
  wram_exec * [populationCode]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.2.1) hb (by wram_simp; exact Nat.zero_le L)
    (by dsimp only [P]; wram_simp [hl, ho, ht]; exact le_rfl))
    with y ⟨⟨hymem, _, _, _, _, hypop⟩, hcnt⟩
  refine ⟨by wram_simp [hcnt]; omega, ?_, hymem⟩
  simpa only [hcnt, Nat.sub_self, population_zero, Nat.add_zero] using hypop

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
