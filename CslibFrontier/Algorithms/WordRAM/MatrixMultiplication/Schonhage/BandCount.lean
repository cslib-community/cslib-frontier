/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPopulation

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Native counting of all valid subset masks

## Main results

* `BandPreparation.exec_countMasks`: the complete binary-mask scan computes the binomial
  coefficient, with its inner population loops and all outer controls charged.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open MaskTable

/-- Scanning all masks computes `K L m`; neither that count nor a valid table is supplied
as an input. Every mask-counter and accepted-counter fit follows from the scan range. -/
theorem exec_countMasks {w : ℕ} (L m : ℕ) (x : Data 96)
    (hL : x.regs levels = L) (hm : x.regs inner = m) (hM : x.regs masks = 2 ^ L)
    (h1 : x.regs one = 1) (h2 : x.regs two = 2) (hfit : Fits w (2 ^ L + L + 4)) :
    ∃ y, ExecWithin w countMasks x y ((6 * L + 11) * 2 ^ L + 4) ∧
      y.regs count = K L m ∧ y.regs mask = 2 ^ L ∧ y.mem = x.mem ∧
      (∀ i, i ≠ mask → i ≠ count → i ≠ residue → i ≠ population → i ≠ counter →
        i ≠ digit → y.regs i = x.regs i) := by
  let P (j : ℕ) (y : Data 96) : Prop :=
    y.mem = x.mem ∧ y.regs levels = L ∧ y.regs inner = m ∧ y.regs masks = 2 ^ L ∧
      y.regs one = 1 ∧ y.regs two = 2 ∧
      y.regs count = prefixCount L m j
  have hb (y : Data 96) (hy : P (y.regs mask) y) (htlt : y.regs mask < 2 ^ L) :
      ∃ z, ExecWithin w countBody y z (6 * L + 9) ∧ P (y.regs mask + 1) z ∧
        z.regs mask = y.regs mask + 1 := by
    obtain ⟨hmem, hL, hm, hM, h1, h2, hcount⟩ := hy
    have hpc := prefixCount_le L m (y.regs mask)
    refine WP.exists_execWithin ?_
    unfold countBody
    wram_call (exec_population L (y.regs mask) y hL rfl h1 h2 (hfit.of_le (by omega)))
      with u ⟨hpop, humem, huf⟩
    wram_exec *
    · dsimp only [P]
      wram_simp * [prefixCount_succ, hc]
      exact humem.trans hmem
    · dsimp only [P]
      wram_simp * [prefixCount_succ, hc]
      exact humem.trans hmem
  suffices ∃ y, ExecWithin w countMasks x y ((6 * L + 11) * 2 ^ L + 4) ∧
      y.regs count = K L m ∧ y.regs mask = 2 ^ L ∧ y.mem = x.mem by
    obtain ⟨y, he, hc, ht, hm'⟩ := this
    refine ⟨y, he, hc, ht, hm', fun i h1' h2' h3' h4' h5' h6' => he.regs_eq ?_⟩
    revert i h1' h2' h3' h4' h5' h6'
    simp only [countMasks, countBody, populationCode, Code.Preserves, Op.dest, Op.bin]
    decide
  wram_exec * [countMasks]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.2.2.2.1) hb
    (by wram_simp; exact Nat.zero_le _)
    (by dsimp only [P]; wram_simp [hL, hm, hM, h1, h2, prefixCount_zero]))
    with y ⟨⟨hymem, _, _, _, _, _, hycount⟩, ht⟩
  refine ⟨?_, by simpa only [ht, prefixCount_full] using hycount, ht, hymem⟩
  wram_simp [ht]
  nlinarith

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
