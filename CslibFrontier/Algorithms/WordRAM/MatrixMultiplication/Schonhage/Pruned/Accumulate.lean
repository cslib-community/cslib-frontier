/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.AccumulateStep
public import CslibFrontier.Computability.WordRAM.Heap

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Complete native accumulation over a distinct parent list

## Main results

* `PrunedQuery.exec_accumulateLoop`: the native loop adds a returned child exactly once at
  each contributing listed parent query, within `31 N + 3` instructions.

The loop invariant uses Mathlib's existing `Finset.piecewise` for the updated memory cells.
The source list and child values are preserved by the concrete block separations.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM Cslib.WordRAM.Signed Finset

/-- This is the real indexed signed-add loop. The list's distinctness is its ordinary memory
property, established by the preceding native timestamp scan, not a query-decision oracle. -/
theorem exec_accumulateLoop {w N capacity : ℕ} (x : Data registers) (input : ℕ → ℕ)
    (V B : ℕ → ℤ) (hN : x.regs count = N)
    (hinput : ∀ i < N, x.mem (x.regs listBase + i) = input i)
    (hcode : ∀ i < N, input i < capacity)
    (hinj : Set.InjOn input {i | i < N})
    (hparent : ∀ i < N, x.mem (x.regs valueBase + input i) = encode (V (input i)))
    (hchild : ∀ i < N, selected true (x.regs term) (input i) →
      x.mem (x.regs childValues + input i / 10) = encode (B (input i / 10)))
    (hV : ∀ i < N, GenericRAM.Signed.Fits w (V (input i)))
    (hB : ∀ i < N, GenericRAM.Signed.Fits w (B (input i / 10)))
    (hsepSource : x.regs listBase + N ≤ x.regs valueBase ∨
      x.regs valueBase + capacity ≤ x.regs listBase)
    (hsepChild : x.regs valueBase + capacity ≤ x.regs childValues ∨
      x.regs childValues + capacity ≤ x.regs valueBase)
    (h1 : x.regs one = 1) (h9 : x.regs nine = 9) (h10 : x.regs ten = 10)
    (hw : Fits (w + 2) (x.regs listBase + N + x.regs valueBase + capacity +
      x.regs childValues + capacity + N + 16)) :
    ∃ y, ExecWithin (w + 2) accumulateLoop x y (31 * N + 3) ∧ y.regs index = N ∧
      y.mem = (((range N).filter fun i => selected true (x.regs term) (input i)).image
        fun i => x.regs valueBase + input i).piecewise
          (fun a => encode (V (a - x.regs valueBase) + B ((a - x.regs valueBase) / 10))) x.mem ∧
      Modifies (Block.mk (x.regs valueBase) capacity).footprint x.mem y.mem ∧
      (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
      (∀ i, ¬AccumulateStepLocal i → y.regs i = x.regs i) := by
  let written (k : ℕ) := (((range k).filter fun i =>
    selected true (x.regs term) (input i)).image fun i => x.regs valueBase + input i)
  let newValue (a : ℕ) :=
    encode (V (a - x.regs valueBase) + B ((a - x.regs valueBase) / 10))
  let P (j : ℕ) (y : Data registers) : Prop :=
    y.mem = (written j).piecewise newValue x.mem ∧
    (∀ i, ¬AccumulateStepLocal i → y.regs i = x.regs i)
  have houtside (j : ℕ) (y : Data registers) (hj : j ≤ N) (hy : P j y) (a : ℕ)
      (ha : ¬(Block.mk (x.regs valueBase) capacity).Owns a) : y.mem a = x.mem a := by
    have hnot : a ∉ written j := by
      rintro h
      obtain ⟨i, hi, rfl⟩ := mem_image.mp h
      have := hcode i ((mem_range.mp (mem_filter.mp hi).1).trans_le hj)
      exact ha (show x.regs valueBase ≤ _ ∧ _ < x.regs valueBase + capacity by omega)
    simp only [hy.1, Finset.piecewise, hnot, ↓reduceIte]
  have hread (j : ℕ) (y : Data registers) (hj : j ≤ N) (hy : P j y) (i : ℕ) (hi : i < N) :
      y.mem (x.regs listBase + i) = input i := by
    refine (houtside j y hj hy _ fun h => ?_).trans (hinput i hi)
    dsimp only [Block.Owns] at h
    rcases hsepSource with hs | hs <;> omega
  have hstep (y : Data registers) (hy : P (y.regs index) y) (hk : y.regs index < N) :
      ∃ z, ExecWithin (w + 2) accumulateStep y z 29 ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1 := by
    obtain ⟨hmem, hf⟩ := hy
    have hb := hf listBase (by decide)
    have hv := hf valueBase (by decide)
    have hcptr := hf childValues (by decide)
    have ht := hf term (by decide)
    have hq := hcode (y.regs index) hk
    have hquot : input (y.regs index) / 10 < capacity := (Nat.div_le_self _ _).trans_lt hq
    have hnot : x.regs valueBase + input (y.regs index) ∉ written (y.regs index) := by
      rintro h
      obtain ⟨j, hj, he⟩ := mem_image.mp h
      have hjk := mem_range.mp (mem_filter.mp hj).1
      exact absurd (hinj (hjk.trans_le hk.le) hk (Nat.add_left_cancel he)) (by omega)
    have hleft : y.mem (y.regs valueBase + input (y.regs index)) =
        encode (V (input (y.regs index))) := by
      simp only [hv, hmem, Finset.piecewise, hnot, ↓reduceIte, hparent _ hk]
    have hright (hs : selected true (y.regs term) (input (y.regs index))) :
        y.mem (y.regs childValues + input (y.regs index) / 10) =
          encode (B (input (y.regs index) / 10)) := by
      rw [hcptr, houtside (y.regs index) y hk.le ⟨hmem, hf⟩]
      · exact hchild _ hk (ht ▸ hs)
      · intro h
        dsimp only [Block.Owns] at h
        rcases hsepChild with hc | hc <;> omega
    obtain ⟨z, hz, hi, hm, hregs⟩ := exec_accumulateStep (hV _ hk) (hB _ hk) y
      (input (y.regs index)) (by rw [hb]; exact hread (y.regs index) y hk.le ⟨hmem, hf⟩ _ hk)
      (by regs_frame) (by regs_frame) (by regs_frame) (fun _ => hleft) hright
      (hw.of_le (by omega)) (hw.of_le (by rw [hb]; omega))
      (hw.of_le (by rw [hv]; omega)) (hw.of_le (by rw [hcptr]; omega)) (hw.of_le (by omega))
    refine ⟨z, hz, ⟨?_, fun i hi => (hregs i hi).trans (hf i hi)⟩, hi⟩
    have hnext : written (y.regs index + 1) =
        if selected true (x.regs term) (input (y.regs index)) then
          insert (x.regs valueBase + input (y.regs index)) (written (y.regs index))
        else written (y.regs index) := by
      by_cases hs : selected true (x.regs term) (input (y.regs index)) <;>
        simp [written, range_add_one, filter_insert, hs]
    rw [hm, ht, hv, hmem, hnext]
    funext a
    by_cases hs : selected true (x.regs term) (input (y.regs index)) <;>
      by_cases he : a = x.regs valueBase + input (y.regs index) <;>
      simp [hs, he, Finset.piecewise, newValue]
  refine WP.exists_execWithin ?_
  wram_exec [accumulateLoop]
  wram_call (ExecWithin.loop_count P (fun _ hy => (hy.2 count (by decide)).trans hN) hstep
    (by wram_simp; exact Nat.zero_le _)
    ⟨by wram_simp; funext a; simp [written, Finset.piecewise], fun i hi => by
      have hne : i ≠ index := fun h => by subst h; exact hi (by decide)
      wram_simp [hne]⟩)
    with y ⟨hIy, hindex⟩
  exact ⟨by wram_simp; omega, hindex, hIy.1,
    fun a ha => houtside N y le_rfl hIy a (by simpa only [Block.mem_footprint] using ha),
    hread N y le_rfl hIy, hIy.2⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
