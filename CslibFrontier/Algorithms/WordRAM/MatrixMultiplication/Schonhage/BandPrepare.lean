/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandRead

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

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
  let start := ((x.set address 1).write 1 L).set index 0
  have hs : ExecWithin w prepareHead x start 3 := by
    ram_eval [prepareHead, start, hx.fixed.levels, hL,
      small_fits hfit (by decide : 1 ≤ 256), address, index, levels, Fin.mk.injEq]
  have hsp : BandParameters L m N start := by regs_frame
  let P (j : ℕ) (y : Data 96) : Prop := BandParameters L m N y ∧ y.regs band = β ∧
    y.mem 1 = L ∧
    (∀ a < j, y.mem (2 + a) = encode (bandValue L m N β side matrix a)) ∧
    (∀ b, ¬(1 ≤ b ∧ b < 2 + 7 ^ L) → y.mem b = x.mem b)
  have hstart : P (start.regs index) start := by
    refine ⟨hsp, ?_, ?_, ?_, ?_⟩
    · simpa [start, band, address, index] using hb
    · simp [start]
    · simp [start]
    · intro b hbb
      have hne : b ≠ 1 := by
        have := Nat.one_le_pow L 7 (by decide)
        omega
      simp [start, hne]
  have hbody (y : Data 96) (hy : P (y.regs index) y) (hc : y.regs index < 7 ^ L) :
      ∃ z, ExecWithin w (prepareBody side) y z (13 * L + 37) ∧
        P (y.regs index + 1) z ∧ z.regs index = y.regs index + 1 := by
    obtain ⟨hyp, hyb, hym1, hyin, hyout⟩ := hy
    let i := y.regs index
    have hi : i < 7 ^ L := hc
    have hsplit : SplitParameters L y := ⟨hyp.fixed.levels, hyp.fixed.one,
      hyp.fixed.two, hyp.fixed.three, hyp.fixed.four, hyp.fixed.seven⟩
    obtain ⟨s, hes, _, hmask, houter, hinner, hsmem⟩ :=
      exec_split L i y hsplit rfl (split_fits hfit hi)
    have hsp : BandParameters L m N s := by regs_frame
    have hsband : s.regs band = β := by regs_frame
    have hsindex : s.regs index = i := by regs_frame
    have htable' (t : ℕ) (ht : t < 2 ^ L) :
        s.mem (inverseBase L m N + t) = MaskTable.lookup L m t := by
      rw [hsmem, hyout _ (by
        have hlow := band_input_le_snapshot L m N
        unfold inverseBase
        omega)]
      exact htable t ht
    have hmat' (r : ℕ) (hr : r < N) (k : ℕ) (hk : k < D m) :
        s.mem (matrixAddress L m N side r k) = encode (matrix r k) := by
      rw [hsmem, hyout _ (by
        have hlow := band_input_le_snapshot L m N
        unfold matrixAddress
        omega)]
      exact hmat r hr k hk
    obtain ⟨t, het, hv, htmem⟩ := exec_readCell side ⟨i, hi⟩ β s hsp hβ hsband
      hmask houter hinner htable' matrix hmat' hfit
    have htindex : t.regs index = i := by cases side <;> regs_frame
    have htone : t.regs one = 1 := by cases side <;> regs_frame
    have httwo : t.regs two = 2 := by cases side <;> regs_frame
    have hadd : Fits w (i + 2) :=
      ((memory_fits hfit).of_le (snapshot_le_memoryEnd L m N)).of_le (by
        have hlow := band_input_le_snapshot L m N
        omega)
    have hinc : Fits w (i + 1) := hadd.of_le (by omega)
    let z := ((t.set address (i + 2)).write (i + 2)
      (encode (bandValue L m N β side matrix i))).set index (i + 1)
    have hez : ExecWithin w (ram[
        address ← index + two; *address ← value; index ← index + one ]) t z 3 := by
      ram_eval [z, htindex, htone, httwo, hv, hadd, hinc,
        address, index, two, one, value, Fin.mk.injEq]
    have he : ExecWithin w (prepareBody side) y z (13 * L + 37) := by
      simpa only [prepareBody, Nat.add_assoc] using hes.seq (het.seq hez)
    have hzindex : z.regs index = i + 1 := by simp [z]
    have hzmem : z.mem = Function.update y.mem (i + 2)
        (encode (bandValue L m N β side matrix i)) := by
      simp only [z, Data.set_mem, Data.write_mem, htmem, hsmem]
    refine ⟨z, he, ?_, hzindex⟩
    · refine ⟨by cases side <;> regs_frame, by cases side <;> regs_frame, ?_, ?_, ?_⟩
      · rw [hzmem, Function.update_of_ne (by omega : 1 ≠ i + 2)]
        exact hym1
      · intro a ha
        rw [hzmem]
        by_cases hai : a = i
        · subst a; rw [Nat.add_comm 2 i, Function.update_self]
        · rw [Function.update_of_ne (by omega : 2 + a ≠ i + 2)]
          exact hyin a (by omega)
      · intro b hbb
        rw [hzmem, Function.update_of_ne (by omega : b ≠ i + 2)]
        exact hyout b hbb
  obtain ⟨y, he, ⟨hyp, hyb, hym1, hyin, hyout⟩, _⟩ := ExecWithin.loop_count P
    (fun _ hy => hy.1.cells) hbody (by simp [start]) hstart
  refine ⟨y, ?_, hyp, hyb, hym1, hyin, hyout⟩
  · apply (hs.seq he).mono
    have hzero : start.regs index = 0 := by simp [start]
    rw [hzero, Nat.sub_zero]
    nlinarith only [Nat.zero_le (7 ^ L)]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BandPreparation
