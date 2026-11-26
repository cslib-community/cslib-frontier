/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandCopy
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandParameters
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Charged copies into the shared band catalogue

## Main results

* `BandPreparation.catalogue_block_le`: each band has one disjoint catalogue block.
* `BandPreparation.exec_collectBand`: the real native encoder-output copy, including
  every address calculation and the unchanged copy kernel's instruction count.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every complete band block lies in the catalogue allocation. -/
theorem catalogue_block_le {L m N β : ℕ} (side : Bool) (hβ : β < numBands L m N) :
    catalogueAddress L m N side β 0 + 10 ^ L ≤ memoryEnd L m N := by
  have ht : 0 < 10 ^ L := Nat.pow_pos (by decide)
  unfold catalogueAddress memoryEnd
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero]
  all_goals nlinarith only [hβ, ht]

/-- No band output is placed in the protected snapshot, tables or native workspace. -/
theorem catalogue_le_address (L m N β : ℕ) (side : Bool) :
    catalogueBase L m N ≤ catalogueAddress L m N side β 0 := by
  unfold catalogueAddress
  omega

/-- Address arithmetic and the full copy are charged. The copy's source and destination are
disjoint by the concrete allocation; arbitrary words outside its destination are retained. -/
theorem exec_collectBand {w L m N : ℕ} (side : Bool) (β : ℕ) (x : Data 96)
    (hx : BandParameters L m N x) (hβ : β < numBands L m N) (hb : x.regs band = β)
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w (collectBand side) x y (7 * 10 ^ L + 10) ∧
      y.mem = ArrayCopy.copyPrefix x.mem (Encoding.outputBase L)
        (catalogueAddress L m N side β 0) (10 ^ L) ∧
      BandParameters L m N y ∧ y.regs band = β := by
  let b := (if side then numBands L m N else 0) + β
  let dest := catalogueAddress L m N side β 0
  have hdest : Fits w (dest + 10 ^ L) := (memory_fits hfit).of_le (catalogue_block_le side hβ)
  have h10pos : 0 < 10 ^ L := Nat.pow_pos (by decide)
  have hbmul : b ≤ b * 10 ^ L := Nat.le_mul_of_pos_right _ h10pos
  have hs : Fits w (7 ^ L + 2) := (encoder_fits hfit).of_le (by
    have h7 := Nat.pow_le_pow_left (by decide : 7 ≤ 10) L
    unfold Encoding.addressBound
    nlinarith only [h7, Nat.zero_le L, Nat.zero_le (10 ^ L)])
  have hws : 7 ^ L + 2 + 10 ^ L ≤ snapshotBase L m N := by
    have h := workspace_le_snapshot L m N
    unfold Encoding.scratchBase Encoding.outputBase at h
    omega
  have hsrc : Fits w (7 ^ L + 2 + 10 ^ L) :=
    ((memory_fits hfit).of_le (snapshot_le_memoryEnd L m N)).of_le hws
  have hsep : 7 ^ L + 2 + 10 ^ L ≤ dest := by
    have hcat := catalogue_le_address L m N β side
    have : 0 ≤ 2 ^ L := Nat.zero_le _
    unfold catalogueBase tableBase inverseBase at hcat
    omega
  dsimp only [dest, catalogueAddress, b] at hdest hbmul hsep ⊢
  unfold collectBand collectHead
  cases side <;> (
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero] at hdest hbmul hsep ⊢
    wram_exec *
    wram_call (exec_copyKernel _ (small_fits hfit (by decide)) (by wram_simp; exact hsrc)
      (by wram_simp; exact hdest) (Or.inl (by wram_simp; exact hsep))) with y ⟨hm, hf⟩
    refine ⟨by wram_simp; omega, ?_, by regs_frame, by regs_frame⟩
    wram_simp at hm
    simpa only [Encoding.outputBase, Nat.add_comm 2 (7 ^ L)] using hm)

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
