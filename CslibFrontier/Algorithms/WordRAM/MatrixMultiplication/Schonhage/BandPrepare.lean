/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandRead

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Complete native padded-band preparation

## Main results

* `BandPreparation.exec_prepareBand`: initialize and fill every band-array cell by actual
  native digit decoding, inverse-table lookup and guarded signed matrix loads.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Every prepared-band cell is below the protected original input. -/
theorem band_input_le_snapshot (L m N : ℕ) : 2 + 7 ^ L ≤ snapshotBase L m N := by
  have h := workspace_le_snapshot L m N
  unfold Encoding.scratchBase Encoding.outputBase at h
  have := Nat.zero_le (10 ^ L)
  omega

/-- The entire input band is materialized with charged initialization, digit/index work,
padding and loop control. No cell outside the depth header and the band input is changed. -/
theorem exec_prepareBand {w L m N : ℕ} (side : Bool) (β : ℕ) (x : Data 96)
    (hx : BandParameters L m N x) (hβ : β < numBands L m N) (hb : x.regs band = β)
    (htable : ∀ t < 2 ^ L, x.mem (inverseBase L m N + t) = MaskTable.lookup L m t)
    (matrix : ℕ → ℕ → ℤ)
    (hmat : ∀ r < N, ∀ k < D m,
      x.mem (matrixAddress L m N side r k) = encode (matrix r k))
    (hfit : Fits w (wordBudget L m N)) :
    ∃ y, ExecWithin w (prepareBand side) x y ((13 * L + 39) * 7 ^ L + 5) ∧
      BandParameters L m N y ∧ y.regs band = β ∧ y.mem 1 = L ∧
      (∀ a < 7 ^ L, y.mem (2 + a) = encode (bandValue L m N β side matrix a)) ∧
      (∀ b, ¬(1 ≤ b ∧ b < 2 + 7 ^ L) → y.mem b = x.mem b) := by
  have hL : Fits w L := (local_fits hfit).of_le (by
    nlinarith only [Nat.zero_le L, Nat.zero_le N, Nat.zero_le (N * D m),
      Nat.zero_le (2 ^ L), Nat.zero_le (10 ^ L)])
  have h1fit : Fits w 1 := small_fits hfit (by decide)
  let P (j : ℕ) (y : Data 96) : Prop := BandParameters L m N y ∧ y.regs band = β ∧
    y.mem 1 = L ∧
    (∀ a < j, y.mem (2 + a) = encode (bandValue L m N β side matrix a)) ∧
    (∀ b, ¬(1 ≤ b ∧ b < 2 + 7 ^ L) → y.mem b = x.mem b)
  have hbody (y : Data 96) (hy : P (y.regs index) y) (hc : y.regs index < 7 ^ L) :
      ∃ z, ExecWithin w (prepareBody side) y z (13 * L + 37) ∧
        P (y.regs index + 1) z ∧ z.regs index = y.regs index + 1 := by
    obtain ⟨hyp, hyb, hym1, hyin, hyout⟩ := hy
    let i := y.regs index
    have hi : i < 7 ^ L := hc
    have hlow := band_input_le_snapshot L m N
    have hadd : Fits w (i + 2) :=
      ((memory_fits hfit).of_le (snapshot_le_memoryEnd L m N)).of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold prepareBody
    wram_call (exec_split L i y ⟨hyp.fixed.levels, hyp.fixed.one, hyp.fixed.two,
      hyp.fixed.three, hyp.fixed.four, hyp.fixed.seven⟩ rfl (split_fits hfit hi))
      with s ⟨_, hmask, houter, hinner, hsmem⟩
    have htable' (t : ℕ) (ht : t < 2 ^ L) :
        s.mem (inverseBase L m N + t) = MaskTable.lookup L m t := by
      rw [hsmem, hyout _ (by unfold inverseBase; omega)]
      exact htable t ht
    have hmat' (r : ℕ) (hr : r < N) (k : ℕ) (hk : k < D m) :
        s.mem (matrixAddress L m N side r k) = encode (matrix r k) := by
      rw [hsmem, hyout _ (by unfold matrixAddress; omega)]
      exact hmat r hr k hk
    wram_call (exec_readCell side ⟨i, hi⟩ β s (by regs_frame) hβ (by regs_frame)
      hmask houter hinner htable' matrix hmat' hfit) with t ⟨hv, htmem⟩
    have htindex : t.regs index = i := by cases side <;> regs_frame
    have htone : t.regs one = 1 := by cases side <;> regs_frame
    have httwo : t.regs two = 2 := by cases side <;> regs_frame
    wram_exec [htindex, htone, httwo, hv]
    refine ⟨⟨by cases side <;> regs_frame, by cases side <;> regs_frame, ?_, ?_, ?_⟩,
      by wram_simp; rfl⟩
    · wram_simp [htmem, hsmem, hym1]
    · intro a ha
      by_cases hai : a = i
      · subst a; wram_simp
      · wram_simp [htmem, hsmem]
        exact hyin a (by omega)
    · intro b hbb
      wram_simp [htmem, hsmem]
      exact hyout b hbb
  wram_exec * [prepareBand, prepareHead]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1.cells) hbody
    (by wram_simp; exact Nat.zero_le _) ?_)
    with y ⟨⟨hyp, hyb, hym1, hyin, hyout⟩, hidx⟩
  · refine ⟨by wram_simp [hidx]; nlinarith only [Nat.zero_le (7 ^ L)],
      hyp, hyb, hym1, ?_, hyout⟩
    simpa only [hidx] using hyin
  · refine ⟨by regs_frame, by regs_frame, by wram_simp, by wram_simp; nofun, ?_⟩
    intro b hbb
    have := Nat.one_le_pow L 7 (by decide)
    wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
