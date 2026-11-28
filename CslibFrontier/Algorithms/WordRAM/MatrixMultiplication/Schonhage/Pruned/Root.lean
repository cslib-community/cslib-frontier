/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Scan
public import CslibFrontier.Computability.WordRAM.Heap
import CslibFrontier.Computability.WordRAM.MemoryView
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Initialization of the actual root stack frame

## Main results

* `PrunedQuery.exec_rootFinish`: write the computed root count and enter its first phase.

The count comes from the preceding native deduplication. The frame words are ordinary stores,
not an externally supplied traversal certificate.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers assigned after the actual root query list has been computed. -/
def RootFinishLocal (i : Fin registers) : Prop :=
  i = address ∨ i = level ∨ i = mode ∨ i = active

instance (i : Fin registers) : Decidable (RootFinishLocal i) :=
  inferInstanceAs (Decidable (i = address ∨ i = level ∨ i = mode ∨ i = active))

/-- Eleven native instructions write the root's computed count, zero prefix, unit stride and
zero term, then set the controller to its entry phase. -/
theorem exec_rootFinish {w : ℕ} (x : Data registers) (h0 : x.regs nil = 0)
    (h1 : x.regs one = 1) (hw : Fits w (x.regs frames + 3)) :
    ∃ y, ExecWithin w rootFinish x y 11 ∧ y.regs level = 0 ∧ y.regs mode = 0 ∧
      y.regs active = 1 ∧
      y.mem = Function.update (Function.update (Function.update (Function.update x.mem
        (x.regs frames) (x.regs childCount)) (x.regs frames + 1) 0)
        (x.regs frames + 2) 1) (x.regs frames + 3) 0 ∧
      Modifies (Block.mk (x.regs frames) 4).footprint x.mem y.mem ∧
      (∀ i, ¬RootFinishLocal i → y.regs i = x.regs i) := by
  have hf1 : Fits w (x.regs frames + 1) := hw.of_le (by omega)
  have hf2 : Fits w (x.regs frames + 2) := hw.of_le (by omega)
  refine WP.exists_execWithin ?_
  wram_exec [rootFinish, h0, h1, hw, hf1, hf2]
  refine ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, ?_, fun i hi => ?_⟩
  · intro a ha
    have hnot : ¬(x.regs frames ≤ a ∧ a < x.regs frames + 4) := by
      simpa only [Block.mem_footprint, Block.Owns] using ha
    wram_simp
  · simp only [RootFinishLocal, not_or] at hi
    rcases hi with ⟨h1', h2', h3', h4'⟩
    wram_simp

/-- Registers written by root-list construction and its first frame initialization. -/
def RootLocal (i : Fin registers) : Prop :=
  ScanLocal i ∨ RootFinishLocal i ∨ i = listBase ∨ i = count ∨ i = childList

instance (i : Fin registers) : Decidable (RootLocal i) :=
  inferInstanceAs (Decidable
    (ScanLocal i ∨ RootFinishLocal i ∨ i = listBase ∨ i = count ∨ i = childList))

/-- Construct the actual distinct root list and frame. Repeated input queries are read and
removed by the native timestamp scan, rather than supplied as a mathematical set. The frame,
list and timestamp intervals are the only possible memory writes. -/
theorem exec_rootList {w N capacity : ℕ} (x : Data registers) (input : ℕ → ℕ)
    (hN : x.regs queryCount = N)
    (hinput : ∀ i < N, x.mem (x.regs queries + i) = input i)
    (hcodes : ∀ i < N, input i < capacity)
    (hsep : x.regs lists + capacity ≤ x.regs stamps)
    (hsrcOut : x.regs queries + N ≤ x.regs lists)
    (hframeList : x.regs frames + 4 ≤ x.regs lists)
    (hsrcFrame : x.regs queries + N ≤ x.regs frames)
    (hmarks : ∀ q < capacity, x.mem (x.regs stamps + q) ≤ x.regs epoch)
    (h0 : x.regs nil = 0) (h1 : x.regs one = 1)
    (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (hw : Fits w (x.regs queries + N + x.regs lists + capacity +
      x.regs stamps + capacity + N + capacity + x.regs epoch + x.regs frames + 16)) :
    ∃ y, ExecWithin w rootList x y (20 * N + 19) ∧
      y.regs level = 0 ∧ y.regs mode = 0 ∧ y.regs active = 1 ∧
      y.regs epoch = x.regs epoch + 1 ∧
      ScanMemory y.mem (x.regs lists) (x.regs stamps) (x.regs epoch + 1) capacity
        ((Finset.range N).image input) ∧
      y.mem (x.regs frames) = ((Finset.range N).image input).card ∧
      y.mem (x.regs frames + 1) = 0 ∧ y.mem (x.regs frames + 2) = 1 ∧
      y.mem (x.regs frames + 3) = 0 ∧
      (∀ i < N, y.mem (x.regs queries + i) = input i) ∧
      (∀ a, ¬(Block.mk (x.regs lists) capacity).Owns a →
        ¬(Block.mk (x.regs stamps) capacity).Owns a →
        ¬(Block.mk (x.regs frames) 4).Owns a → y.mem a = x.mem a) ∧
      (∀ i, ¬RootLocal i → y.regs i = x.regs i) := by
  refine WP.exists_execWithin ?_
  wram_exec [rootList, rootScanSetup, hN]
  wram_call (exec_scan (N := N) (capacity := capacity) false _ input
    (by wram_simp) (by wram_simp; exact hinput)
    (by simpa only [shortened, Bool.false_eq_true, ↓reduceIte] using hcodes)
    (Or.inl (by wram_simp; exact hsep)) (Or.inl (by wram_simp; exact hsrcOut))
    (Or.inl (by wram_simp; exact hsrcOut.trans (Nat.le_trans (Nat.le_add_right _ _) hsep)))
    (by wram_simp; exact hmarks) (by wram_simp [h1]) (by wram_simp [h10]) (by wram_simp [h9])
    (hw.of_le (by wram_simp; omega)))
    with v ⟨_, hve, hvc, htable, _, hscanFrame, hvreg⟩
  wram_simp at hve hvc htable hscanFrame
  rw [scanSet_root] at hvc htable
  have hvf : v.regs frames = x.regs frames := by regs_frame
  wram_call (exec_rootFinish v (by regs_frame) (by regs_frame) (hw.of_le (by rw [hvf]; omega)))
    with y ⟨hyl, hym, hya, hmem, hfinishFrame, hyreg⟩
  rw [hvf] at hmem hfinishFrame
  have hyoutside (a : ℕ) (ha : ¬(Block.mk (x.regs frames) 4).Owns a) : y.mem a = v.mem a :=
    hfinishFrame a (by simpa only [Block.mem_footprint] using ha)
  refine ⟨by omega, hyl, hym, hya, by regs_frame, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_⟩
  · ram_keep htable using hyoutside
  · rw [hmem]; simp [hvc]
  · rw [hmem]; simp
  · rw [hmem]; simp
  · rw [hmem]; simp
  · intro i hi
    rw [hyoutside _ (by change ¬(x.regs frames ≤ _ ∧ _ < x.regs frames + 4); omega), hscanFrame]
    · exact hinput i hi
    · change ¬(x.regs lists ≤ _ ∧ _ < x.regs lists + capacity); omega
    · change ¬(x.regs stamps ≤ _ ∧ _ < x.regs stamps + capacity); omega
  · intro a hao has haf
    exact (hyoutside a haf).trans (hscanFrame a hao has)
  · simp only [RootLocal, not_or] at hi
    rcases hi with ⟨hscan, hfin, hb, hc, hl⟩
    rw [hyreg i hfin, hvreg i hscan]
    wram_simp

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
