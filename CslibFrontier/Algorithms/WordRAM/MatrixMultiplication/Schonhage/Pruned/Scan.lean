/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.ScanInsert

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Complete charged native query scans

## Main results

* `PrunedQuery.exec_scan`: the fixed native loop reads, filters and deduplicates its source
  list in at most `20 N + 5` instructions, without clearing a dense directory.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers changed by the whole scan, including its fresh-epoch initialization. -/
def ScanLocal (i : Fin registers) : Prop := ScanStepLocal i ∨ i = epoch

instance (i : Fin registers) : Decidable (ScanLocal i) :=
  inferInstanceAs (Decidable (ScanStepLocal i ∨ i = epoch))

/-- The actual native scan constructs a distinct query list and its membership timestamps.
All width premises concern ordinary addresses, lengths and the incoming epoch. Source/output/
directory separation is checked on concrete intervals. No child list is supplied in advance. -/
theorem exec_scan {w N capacity : ℕ} (child : Bool) (x : Data registers) (input : ℕ → ℕ)
    (hN : x.regs count = N)
    (hinput : ∀ i < N, x.mem (x.regs listBase + i) = input i)
    (hcodes : ∀ i < N, shortened child (input i) < capacity)
    (hsep : x.regs childList + capacity ≤ x.regs stamps ∨
      x.regs stamps + capacity ≤ x.regs childList)
    (hsrcOut : x.regs listBase + N ≤ x.regs childList ∨
      x.regs childList + capacity ≤ x.regs listBase)
    (hsrcStamp : x.regs listBase + N ≤ x.regs stamps ∨
      x.regs stamps + capacity ≤ x.regs listBase)
    (hmarks : ∀ q < capacity, x.mem (x.regs stamps + q) ≤ x.regs epoch)
    (h1 : x.regs one = 1) (h10 : x.regs ten = 10) (h9 : x.regs nine = 9)
    (hwidth : Fits w (x.regs listBase + N + x.regs childList + capacity +
      x.regs stamps + capacity + N + capacity + x.regs epoch + 12)) :
    ∃ y, ExecWithin w (scan child) x y (20 * N + 5) ∧ y.regs index = N ∧
      y.regs epoch = x.regs epoch + 1 ∧
      y.regs childCount = (scanSet child (x.regs term) input N).card ∧
      ScanMemory y.mem (x.regs childList) (x.regs stamps) (x.regs epoch + 1) capacity
        (scanSet child (x.regs term) input N) ∧
      (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
      (∀ a, ¬(Block.mk (x.regs childList) capacity).Owns a →
        ¬(Block.mk (x.regs stamps) capacity).Owns a → y.mem a = x.mem a) ∧
      (∀ i, ¬ScanLocal i → y.regs i = x.regs i) := by
  let E := x.regs epoch + 1
  have hE : Fits w E := hwidth.of_le (by dsimp [E]; omega)
  let P (j : ℕ) (y : Data registers) : Prop :=
    y.regs epoch = E ∧
    y.regs childCount = (scanSet child (x.regs term) input j).card ∧
    ScanMemory y.mem (x.regs childList) (x.regs stamps) E capacity
      (scanSet child (x.regs term) input j) ∧
    (∀ i < N, y.mem (x.regs listBase + i) = input i) ∧
    (∀ a, ¬(Block.mk (x.regs childList) capacity).Owns a →
      ¬(Block.mk (x.regs stamps) capacity).Owns a → y.mem a = x.mem a) ∧
    (∀ i, ¬ScanLocal i → y.regs i = x.regs i)
  have hstep (y : Data registers) (hy : P (y.regs index) y) (hk : y.regs index < N) :
      ∃ z, ExecWithin w (scanStep child) y z 18 ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1 := by
    obtain ⟨hye, hcount, htable, hread, hframe, hfrozen⟩ := hy
    have hyb := hfrozen listBase (by decide)
    have hyo := hfrozen childList (by decide)
    have hys := hfrozen stamps (by decide)
    have hyt := hfrozen term (by decide)
    have hq := hcodes (y.regs index) hk
    have hcap := htable.card_le
    obtain ⟨z, hz, hidx, hcz, htz, hmf, hrf⟩ := exec_scanInsert child y
      (scanSet child (x.regs term) input (y.regs index)) (input (y.regs index))
      (by rw [hyb]; exact hread _ hk) hcount
      (by simpa only [hyo, hys, hye] using htable) hq
      (by simpa only [hyo, hys] using hsep)
      (by regs_frame) (by regs_frame) (by regs_frame)
      (hwidth.of_le (by omega)) (hwidth.of_le (by rw [hyb]; omega))
      (hwidth.of_le (by rw [hys]; omega)) (hwidth.of_le (by rw [hyo, hcount]; omega))
      (hwidth.of_le (by rw [hcount]; omega)) (hwidth.of_le (by omega))
    have hsource (i : ℕ) (hi : i < N) : z.mem (x.regs listBase + i) = input i := by
      rw [hmf _ (by simp only [hyo, Block.Owns]; omega) (by simp only [hys, Block.Owns]; omega)]
      exact hread i hi
    refine ⟨z, hz, ⟨(hrf epoch (by decide)).trans hye, ?_, ?_, hsource, ?_, ?_⟩, hidx⟩
    · simpa only [hyt, ← scanSet_succ] using hcz
    · simpa only [hyo, hys, hye, hyt, ← scanSet_succ] using htz
    · exact fun a hao has => (hmf a (by simpa only [hyo] using hao)
        (by simpa only [hys] using has)).trans (hframe a hao has)
    · exact fun i hi => (hrf i (fun h => hi (Or.inl h))).trans (hfrozen i hi)
  refine WP.exists_execWithin ?_
  dsimp only [E] at hE
  wram_exec [scan, scanSetup, h1, hE]
  wram_call (ExecWithin.loop_count P (fun _ hy => (hy.2.2.2.2.2 count (by decide)).trans hN)
    hstep (by wram_simp; exact Nat.zero_le _)
    ⟨by wram_simp; rfl, by wram_simp; simp [scanSet_zero],
      by wram_simp; simpa only [scanSet_zero] using
        ScanMemory.empty (out := x.regs childList) (epoch := E)
          (fun q hq => Nat.lt_succ_of_le (hmarks q hq)),
      hinput, fun _ _ _ => rfl, fun i hi => by
        have h1' : i ≠ epoch := fun h => hi (Or.inr h)
        have h2' : i ≠ childCount := fun h => by subst h; exact hi (by decide)
        have h3' : i ≠ index := fun h => by subst h; exact hi (by decide)
        wram_simp [h1', h2', h3']⟩)
    with y ⟨⟨hye, hcount, htable, hread, hframe, hfrozen⟩, hindex⟩
  exact ⟨by wram_simp; omega, hindex, hye, hcount, htable, hread, hframe, hfrozen⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
