/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
public import CslibFrontier.Computability.WordRAM.Heap

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Returning queried values in the actual input order

## Main results

* `PrunedQuery.exec_report`: the native reporting loop preserves duplicate requests and writes
  their corresponding values in order, charging every load, address, store and loop test.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

open Cslib.WordRAM

/-- Registers used while reporting the explicitly supplied query list. -/
def ReportLocal (i : Fin registers) : Prop :=
  i = index ∨ i = address ∨ i = query ∨ i = temporary

instance (i : Fin registers) : Decidable (ReportLocal i) :=
  inferInstanceAs (Decidable (i = index ∨ i = address ∨ i = query ∨ i = temporary))

/-- The finite native loop reads the original requests, including duplicates. Its only writes
are the `N` output cells; the value directory and original requests remain unchanged. -/
theorem exec_report {w N capacity : ℕ} (x : Data registers) (codes : ℕ → ℕ)
    (hN : x.regs queryCount = N)
    (hinput : ∀ i < N, x.mem (x.regs queries + i) = codes i)
    (hcodes : ∀ i < N, codes i < capacity)
    (hsrc : x.regs queries + N ≤ x.regs output ∨
      x.regs output + N ≤ x.regs queries)
    (hvals : x.regs values + capacity ≤ x.regs output ∨
      x.regs output + N ≤ x.regs values)
    (h1 : x.regs one = 1)
    (hw : Fits w (x.regs queries + N + x.regs values + capacity +
      x.regs output + N + N + 12)) :
    ∃ y, ExecWithin w report x y (9 * N + 3) ∧ y.regs index = N ∧
      (∀ i < N, y.mem (x.regs output + i) = x.mem (x.regs values + codes i)) ∧
      Modifies (Block.mk (x.regs output) N).footprint x.mem y.mem ∧
      (∀ i, ¬ReportLocal i → y.regs i = x.regs i) := by
  let P (j : ℕ) (y : Data registers) : Prop :=
    (∀ i < j, y.mem (x.regs output + i) = x.mem (x.regs values + codes i)) ∧
    (∀ i < N, y.mem (x.regs queries + i) = codes i) ∧
    (∀ q < capacity, y.mem (x.regs values + q) = x.mem (x.regs values + q)) ∧
    Modifies (Block.mk (x.regs output) N).footprint x.mem y.mem ∧
    (∀ i, ¬ReportLocal i → y.regs i = x.regs i)
  have hstep (y : Data registers) (hy : P (y.regs index) y) (hk : y.regs index < N) :
      ∃ z, ExecWithin w reportStep y z 7 ∧ P (y.regs index + 1) z ∧
        z.regs index = y.regs index + 1 := by
    obtain ⟨hdone, hread, hvalue, hframe, hfrozen⟩ := hy
    have hq := hfrozen queries (by decide)
    have hv := hfrozen values (by decide)
    have ho := hfrozen output (by decide)
    have hread' : y.mem (x.regs queries + y.regs index) = codes (y.regs index) :=
      hread (y.regs index) hk
    have hval' : y.mem (x.regs values + codes (y.regs index)) =
        x.mem (x.regs values + codes (y.regs index)) :=
      hvalue (codes (y.regs index)) (hcodes (y.regs index) hk)
    have hqa : Fits w (x.regs queries + y.regs index) := hw.of_le (by omega)
    have hva : Fits w (x.regs values + codes (y.regs index)) :=
      hw.of_le (by have := hcodes (y.regs index) hk; omega)
    have hoa : Fits w (x.regs output + y.regs index) := hw.of_le (by omega)
    have hki : Fits w (y.regs index + 1) := hw.of_le (by omega)
    have hawaySrc (i : ℕ) (hi : i < N) : x.regs queries + i ≠ x.regs output + y.regs index := by
      rcases hsrc with h | h <;> omega
    have hawayVal (q : ℕ) (hq' : q < capacity) :
        x.regs values + q ≠ x.regs output + y.regs index := by
      rcases hvals with h | h <;> omega
    refine WP.exists_execWithin ?_
    wram_exec * [reportStep, hread', hval', hqa, hva, hoa, hki]
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, by wram_simp⟩
    · intro i hi
      by_cases he : i = y.regs index
      · subst he
        wram_simp
      · wram_simp
        exact hdone i (by omega)
    · intro i hi
      have hne := hawaySrc i hi
      wram_simp [hne]
      exact hread i hi
    · intro q hq'
      have hne := hawayVal q hq'
      wram_simp [hne]
      exact hvalue q hq'
    · intro a ha
      have hnot : a ≠ x.regs output + y.regs index := by
        intro he
        apply ha
        rw [Block.mem_footprint]
        change x.regs output ≤ a ∧ a < x.regs output + N
        omega
      wram_simp [hnot]
      exact hframe a ha
    · intro i hi
      simp only [ReportLocal, not_or] at hi
      rcases hi with ⟨h1', h2', h3', h4'⟩
      wram_simp
      exact hfrozen i (by simp [ReportLocal, h1', h2', h3', h4'])
  refine WP.exists_execWithin ?_
  wram_exec [report]
  wram_call (ExecWithin.loop_count P
    (fun _ ⟨_, _, _, _, hf⟩ => (hf queryCount (by decide)).trans hN)
    hstep (by wram_simp; exact Nat.zero_le _)
    ⟨by wram_simp; simp, hinput, fun _ _ => rfl, Modifies.refl _ _, fun i hi => by
      simp only [ReportLocal, not_or] at hi; rcases hi with ⟨h1', _, _, _⟩; wram_simp⟩)
    with y ⟨⟨hdone, _, _, hframe, hfrozen⟩, hidx⟩
  exact ⟨by wram_simp; omega, hidx, hdone, hframe, hfrozen⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery
