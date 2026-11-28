/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted.CountStep

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Complete native count pass for wanted positions

## Main results

* `Wanted.exec_clearCounts`: initialize exactly the actual tile-count cells.
* `Wanted.exec_countQueries`: all original occurrences, including repetitions, are counted
  by the actual coordinate-loading and tile-index code in linear charged time.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual dense initialization of tile counts. It touches no query or computed table. -/
theorem exec_clearCounts {w L m N Q : ℕ} (x : Data 96) (hx : Parameters L m N Q x)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w clearCounts x y (5 * numBands L m N ^ 2 + 3) ∧
      Parameters L m N Q y ∧
      (∀ t < numBands L m N ^ 2, y.mem (countAddress L Q + t) = 0) ∧
      (∀ a, a < countAddress L Q ∨ countAddress L Q + numBands L m N ^ 2 ≤ a →
        y.mem a = x.mem a) := by
  let T := numBands L m N ^ 2
  let body : Code .standard 96 := ram[
    pointer ← counts + index; *pointer ← BandPreparation.zero;
    index ← index + BandPreparation.one ]
  let P (k : ℕ) (z : Data 96) : Prop := Parameters L m N Q z ∧
    (∀ t < k, z.mem (countAddress L Q + t) = 0) ∧
    (∀ a, a < countAddress L Q ∨ countAddress L Q + T ≤ a → z.mem a = x.mem a)
  have hb (z : Data 96) (hz : P (z.regs index) z) (hn : z.regs index < T) :
      ∃ u, ExecWithin w body z u 3 ∧ P (z.regs index + 1) u ∧
        u.regs index = z.regs index + 1 := by
    obtain ⟨hzp, hzt, hza⟩ := hz
    have hl := local_fits hfit
    have hend := memoryLimit_eq L m N Q
    have h10 := Nat.zero_le (10 ^ L)
    have hfaddr : Fits w (countAddress L Q + z.regs index) := hl.of_le (by
      unfold countAddress tableAddress inputLimit
      dsimp [T] at hn
      omega)
    have hnext : Fits w (z.regs index + 1) := hl.of_le (by dsimp [T] at hn; omega)
    refine WP.exists_execWithin ?_
    dsimp only [body]
    wram_exec * [hfaddr, hnext]
    refine ⟨⟨by regs_frame, ?_, ?_⟩, by wram_simp⟩
    · intro t ht
      by_cases h : t = z.regs index
      · subst h; wram_simp
      · wram_simp; exact hzt t (by omega)
    · intro a ha
      have hne : a ≠ countAddress L Q + z.regs index := by rcases ha with ha | ha <;> omega
      wram_simp [hne]
      exact hza a ha
  refine WP.exists_execWithin ?_
  wram_exec [clearCounts]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1.tileCount) hb
    (by wram_simp; exact Nat.zero_le _)
    ⟨by regs_frame, by wram_simp; simp, fun _ _ => rfl⟩)
    with y ⟨⟨hyp, hyzero, hyframe⟩, _⟩
  exact ⟨by wram_simp; omega, hyp, hyzero, hyframe⟩

/-- Every original query is loaded and its actual tile computed. Duplicate input pairs
increase counts independently; the readonly input and both computed tables are preserved. -/
theorem exec_countQueries {w L m N Q : ℕ} (hm : m ≤ L) (pairs : ℕ → ℕ × ℕ)
    (hpairs : ∀ i < Q, (pairs i).1 < N ∧ (pairs i).2 < N) (x : Data 96)
    (hx : Parameters L m N Q x)
    (hinput : ∀ i < Q, x.mem (5 + 2 * i) = (pairs i).1 ∧
      x.mem (5 + 2 * i + 1) = (pairs i).2)
    (hzero : ∀ t < numBands L m N ^ 2, x.mem (countAddress L Q + t) = 0)
    (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w countQueries x y (16 * Q + 3) ∧ Parameters L m N Q y ∧
      (∀ t < numBands L m N ^ 2,
        y.mem (countAddress L Q + t) = Nat.count (fun k => (tileKey L m N ∘ pairs) k = t) Q) ∧
      (∀ a, a < countAddress L Q ∨ countAddress L Q + numBands L m N ^ 2 ≤ a →
        y.mem a = x.mem a) := by
  let key := tileKey L m N ∘ pairs
  let T := numBands L m N ^ 2
  let P (k : ℕ) (z : Data 96) : Prop := Parameters L m N Q z ∧
    (∀ i < Q, z.mem (5 + 2 * i) = (pairs i).1 ∧
      z.mem (5 + 2 * i + 1) = (pairs i).2) ∧
    (∀ t < T, z.mem (countAddress L Q + t) = Nat.count (fun k => key k = t) k) ∧
    (∀ a, a < countAddress L Q ∨ countAddress L Q + T ≤ a → z.mem a = x.mem a)
  have hb (z : Data 96) (hz : P (z.regs index) z) (hn : z.regs index < Q) :
      ∃ u, ExecWithin w countStep z u 14 ∧
        P (z.regs index + 1) u ∧ u.regs index = z.regs index + 1 := by
    obtain ⟨u, he, hu, hidx, hcounts, hf⟩ := exec_countStep hm pairs hn (hpairs _ hn)
      z hz.1 rfl (hz.2.1 _ hn) hz.2.2.1 hfit
    refine ⟨u, he, ⟨hu, ?_, hcounts, fun a ha => (hf a ha).trans (hz.2.2.2 a ha)⟩, hidx⟩
    intro i hi
    have ha : 5 + 2 * i + 1 < countAddress L Q := by
      have h2 := Nat.zero_le (2 ^ L)
      unfold countAddress tableAddress inputLimit
      omega
    rw [hf _ (Or.inl (by omega)), hf _ (Or.inl ha)]
    exact hz.2.1 i hi
  refine WP.exists_execWithin ?_
  wram_exec [countQueries]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1.queryCount) hb
    (by wram_simp; exact Nat.zero_le _)
    ⟨by regs_frame, hinput, fun t ht => by wram_simp [hzero t ht, Nat.count_zero],
      fun _ _ => rfl⟩)
    with y ⟨⟨hyp, _, hycounts, hyframe⟩, _⟩
  exact ⟨by wram_simp; omega, hyp, hycounts, hyframe⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Wanted
