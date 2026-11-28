/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Product.SavedGroups

import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Actual reconstruction in original request order

## Main results

* `QueriedProduct.exec_reconstruct`: read the stored original indices and grouped answers,
  then scatter every answer to its original request position, charging every instruction.

The existing stable-position bijection proves that no earlier answer is overwritten.
Neither an inverse permutation nor a scatter execution is supplied to the program.
-/

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- Actual reconstruction retains repeated input occurrences, input words and outside memory.
Only the designated original-order answer block is written. -/
public theorem exec_reconstruct {w L m N : ℕ}
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (old : ℕ → ℕ) (x : Data 160)
    (hp : Parameters L m N qs.length x) (hg : SavedGroups L m N qs.length old x.mem)
    (horiginals : ∀ i : Fin qs.length,
      old (Wanted.originalAddress L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) = i.val)
    (hanswers : ∀ i : Fin qs.length,
      x.mem (groupedBase L m N qs.length +
          CountingSort.position (Wanted.tileKey L m N ∘ Wanted.inputPairs qs) qs.length i) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2))
    (hfit : Fits w (wordBudget L m N qs.length)) :
    ∃ y, ExecWithin w reconstruct x y (9 * qs.length + 3) ∧
      Parameters L m N qs.length y ∧
      (∀ i : Fin qs.length, y.mem (outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
      (∀ a, a < outputBase L m N qs.length ∨ scratchBase L m N qs.length ≤ a →
        y.mem a = x.mem a) := by
  let key := Wanted.tileKey L m N ∘ Wanted.inputPairs qs
  let pos := CountingSort.position key qs.length
  let P (k : ℕ) (z : Data 160) : Prop := Parameters L m N qs.length z ∧
    (∀ i : Fin qs.length, pos i.val < k →
      z.mem (outputBase L m N qs.length + i.val) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2)) ∧
    (∀ a, a < outputBase L m N qs.length ∨ scratchBase L m N qs.length ≤ a → z.mem a = x.mem a)
  have hout : outputBase L m N qs.length + qs.length = scratchBase L m N qs.length := rfl
  have hgroup : groupedBase L m N qs.length + qs.length = outputBase L m N qs.length := rfl
  have horig : originalBase L m N qs.length + qs.length = groupedBase L m N qs.length := rfl
  have hfree : scratchBase L m N qs.length ≤ memoryEnd L m N qs.length := by
    unfold memoryEnd stampBase
    have h10 := Nat.zero_le (10 ^ L)
    omega
  have hbody (z : Data 160) (hz : P (z.regs Reg.index) z) (hi : z.regs Reg.index < qs.length) :
      ∃ u, ExecWithin w reconstructStep z u 7 ∧
        P (z.regs Reg.index + 1) u ∧ u.regs Reg.index = z.regs Reg.index + 1 := by
    obtain ⟨hzp, hzj, hza⟩ := hz
    obtain ⟨i, hip⟩ :=
      (CountingSort.position_bijective key qs.length).surjective ⟨z.regs Reg.index, hi⟩
    have hpos := congrArg (fun j : Fin qs.length => j.val) hip
    change pos i.val = z.regs Reg.index at hpos
    have hreadIndex : z.mem (originalBase L m N qs.length + z.regs Reg.index) = i.val := by
      rw [hza _ (Or.inl (by omega)), hg.originals _ hi, ← hpos]
      exact horiginals i
    have hreadValue : z.mem (groupedBase L m N qs.length + z.regs Reg.index) =
        Signed.encode ((X * Y) (qs.get i).1 (qs.get i).2) := by
      rw [hza _ (Or.inl (by omega)), ← hpos]
      exact hanswers i
    have fo : Fits w (originalBase L m N qs.length + z.regs Reg.index) :=
      allocated_fits hfit (by omega)
    have fg : Fits w (groupedBase L m N qs.length + z.regs Reg.index) :=
      allocated_fits hfit (by omega)
    have fy : Fits w (outputBase L m N qs.length + i.val) := allocated_fits hfit (by
      have h := i.isLt
      omega)
    have fn : Fits w (z.regs Reg.index + 1) := allocated_fits hfit (by omega)
    refine WP.exists_execWithin ?_
    wram_exec * [reconstructStep, hreadIndex, hreadValue, fo, fg, fy, fn]
    refine ⟨⟨by regs_frame, ?_, ?_⟩, by wram_simp⟩
    · intro j hj
      by_cases hij : j = i
      · subst hij
        wram_simp
      · have hne : j.val ≠ i.val := fun heq => hij (Fin.ext heq)
        wram_simp [hne]
        have hpne : pos j.val ≠ pos i.val := fun heq => hij
          (CountingSort.position_injective key qs.length heq)
        exact hzj j (by omega)
    · intro a ha
      have hne : a ≠ outputBase L m N qs.length + i.val := by
        have h := i.isLt
        rcases ha with ha | ha <;> omega
      wram_simp [hne]
      exact hza a ha
  refine WP.exists_execWithin ?_
  wram_exec [reconstruct]
  wram_call (ExecWithin.loop_count P (fun _ hy => hy.1.queryCount) hbody
    (by wram_simp; exact Nat.zero_le _)
    ⟨by regs_frame, by wram_simp; simp, fun _ _ => rfl⟩) with y ⟨⟨hyp, hyj, hya⟩, _⟩
  exact ⟨by wram_simp; omega, hyp, fun i => hyj i (CountingSort.position_lt key i.isLt), hya⟩

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.QueriedProduct
