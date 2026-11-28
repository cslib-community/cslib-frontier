/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.Transfer

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# One charged timestamp initialization for all product tiles

## Main results

* `QueriedProduct.exec_initializeDirectory`: clear the actual shared directory once and set
  the initial epoch and tile index, with a complete outside frame.

Subsequent kernel calls propagate their returned epoch. This initialization is not repeated
per tile or request.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM

/-- Actual directory stores and loop control, followed by the epoch/index setup. -/
public theorem exec_initializeDirectory {w L m N Q : ℕ} (x : Data 160)
    (hp : Parameters L m N Q x) (hfit : Fits w (wordBudget L m N Q)) :
    ∃ y, ExecWithin w initializeDirectory x y (5 * 10 ^ L + 5) ∧
      Parameters L m N Q y ∧ y.regs Reg.epoch = 0 ∧ y.regs Reg.index = 0 ∧
      (∀ j < 10 ^ L, y.mem (stampBase L m N Q + j) = 0) ∧
      (∀ a, a < stampBase L m N Q ∨ memoryEnd L m N Q ≤ a → y.mem a = x.mem a) := by
  let H := 10 ^ L
  let body : Code .standard 160 := ram[
    Reg.address ← Reg.stamps + Reg.index; *Reg.address ← Reg.zero; Reg.index ← Reg.index + Reg.one ]
  let P (k : ℕ) (z : Data 160) : Prop := Parameters L m N Q z ∧
    (∀ j < k, z.mem (stampBase L m N Q + j) = 0) ∧
    (∀ a, a < stampBase L m N Q ∨ memoryEnd L m N Q ≤ a → z.mem a = x.mem a)
  have hbody (z : Data 160) (hz : P (z.regs Reg.index) z) (hi : z.regs Reg.index < H) :
      ∃ u, ExecWithin w body z u 3 ∧ P (z.regs Reg.index + 1) u ∧
        u.regs Reg.index = z.regs Reg.index + 1 := by
    obtain ⟨hzp, hzj, hza⟩ := hz
    have ha : Fits w (stampBase L m N Q + z.regs Reg.index) := allocated_fits hfit (by
      unfold memoryEnd
      dsimp only [H] at hi
      omega)
    have hn : Fits w (z.regs Reg.index + 1) := allocated_fits hfit (by
      unfold memoryEnd
      dsimp only [H] at hi
      omega)
    refine WP.exists_execWithin ?_
    wram_exec * [ha, hn]
    refine ⟨⟨by regs_frame, ?_, ?_⟩, by wram_simp⟩
    · intro j hj
      by_cases h : j = z.regs Reg.index
      · subst h
        wram_simp
      · wram_simp
        exact hzj j (by omega)
    · intro a ha'
      have hne : a ≠ stampBase L m N Q + z.regs Reg.index := by
        unfold memoryEnd at ha'
        dsimp only [H] at hi
        rcases ha' with ha' | ha' <;> omega
      wram_simp [hne]
      exact hza a ha'
  refine WP.exists_execWithin ?_
  wram_exec [initializeDirectory]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1.leaves) hbody
    (by wram_simp; exact Nat.zero_le _)
    ⟨by regs_frame, by wram_simp; simp, fun _ _ => rfl⟩) with y ⟨⟨hyp, hyj, hya⟩, _⟩
  wram_exec
  exact ⟨by regs_frame, by wram_simp, by wram_simp, hyj, hya⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
