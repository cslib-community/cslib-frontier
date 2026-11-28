/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.LookupLoop
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Values
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Native lookup in the computed compact box table

The real code scans the original cube digits and reads its computed directory rank
and signed table word. The caller supplies ordinary memory readback, as obtained from
the native catalogue and value constructors. All scan and address arithmetic is charged;
the lookup preserves all memory and registers outside its documented scalar workspace.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The complete scalar workspace modified by native lookup, including returned fields. -/
@[expose] def LookupWholeLocal (i : Fin registers) : Prop :=
  LookupLocal i ∨ i = Reg.nil ∨ i = Reg.one ∨ i = Reg.ten ∨ i = Reg.nine ∨
    i = Reg.three ∨ i = Reg.found ∨ i = Reg.answer ∨ i = Reg.childSlot ∨ i = Reg.childRank

instance (i : Fin registers) : Decidable (LookupWholeLocal i) :=
  inferInstanceAs (Decidable (LookupLocal i ∨ i = Reg.nil ∨ i = Reg.one ∨ i = Reg.ten ∨
    i = Reg.nine ∨ i = Reg.three ∨ i = Reg.found ∨ i = Reg.answer ∨
    i = Reg.childSlot ∨ i = Reg.childRank))

/-- Read the genuine signed word at a valid box's computed compact rank. -/
theorem exec_lookup {w L m t C D V : ℕ} (x : Data registers) (π : Cube L)
    (a b : Leaf L → ℤ) (hπ : IsBox m t π)
    (hL : x.regs Reg.levels = L) (hH : x.regs Reg.height = m - t)
    (hT : x.regs Reg.span = 10 ^ L) (hC : x.regs Reg.cube = C)
    (hD : x.regs Reg.directory = D) (hV : x.regs Reg.values = V)
    (hread : ∀ i < L, x.mem (C + i) = rawCubeDigit π i)
    (hdir : ∀ s < (m - t + 1) * 10 ^ L, x.mem (D + s) = directoryWord L (m - t) s)
    (hvalues : ∀ s < (m - t + 1) * 10 ^ L, Eligible L (m - t) s →
      x.mem (V + Nat.count (Eligible L (m - t)) s) = Signed.encode (slotValue a b s))
    (hfit : Fits w (C + D + V + (m - t + 1) * 10 ^ L + 10 ^ L + L + 30)) :
    ∃ y, ExecWithin w lookup x y (18 * L + 32) ∧ y.mem = x.mem ∧
      y.regs Reg.found = 1 ∧
      y.regs Reg.answer = Signed.encode (boxValue a b π.starLevels.card π) ∧
      (∀ i, ¬LookupWholeLocal i → y.regs i = x.regs i) := by
  suffices ∃ y, ExecWithin w lookup x y (18 * L + 32) ∧ y.mem = x.mem ∧
      y.regs Reg.found = 1 ∧
      y.regs Reg.answer = Signed.encode (boxValue a b π.starLevels.card π) by
    obtain ⟨y, he, hm, hf, ha'⟩ := this
    exact ⟨y, he, hm, hf, ha',
      fun i hi => he.regs_eq (by unfold LookupWholeLocal LookupLocal at hi; decide +revert)⟩
  let s := cubeSlot π
  let r := Nat.count (Eligible L (m - t)) s
  have hs : s < (m - t + 1) * 10 ^ L := cubeSlot_lt hπ
  have hv : Eligible L (m - t) s := eligible_cubeSlot hπ
  have hr : r ≤ s := Nat.count_le _
  have hslot : π.starLevels.card * 10 ^ L + (Encoding.leafIndex π.starsToP0).val = s := rfl
  have hnH := hπ.1
  refine WP.exists_execWithin ?_
  unfold lookup lookupSetup constants lookupFinish
  wram_exec [*]
  wram_call (exec_lookupLoop (C := C) _ π hπ (by constructor <;> wram_simp [*])
    (by simpa only [Data.set_mem] using hread)
    (by wram_simp) (by wram_simp) (by wram_simp) (by wram_simp)
    (by wram_simp) (by wram_simp) (by wram_simp) (hfit.of_le (by omega)))
    with z ⟨hzm, hzp, _, _, hzc, hzs, hzf, hzi, hframez⟩
  have hmem : z.mem = x.mem := by simpa only [Data.set_mem] using hzm
  have zH : z.regs Reg.height = m - t := by regs_frame
  have zT : z.regs Reg.span = 10 ^ L := by regs_frame
  have zD : z.regs Reg.directory = D := by regs_frame
  have zV : z.regs Reg.values = V := by regs_frame
  have hz0 : z.regs Reg.nil = 0 := hzp.nil
  have hz1 : z.regs Reg.one = 1 := hzp.one
  have hdw : directoryWord L (m - t) s = r + 1 := by
    rw [directoryWord, ite_eq_left hv]
  have hvalue : x.mem (V + r) = Signed.encode (slotValue a b s) := hvalues s hs hv
  wram_exec [*]
  refine ⟨by simpa only [Data.set_mem] using hmem, by wram_simp, ?_⟩
  have hval : slotValue a b s = boxValue a b π.starLevels.card π := by
    have hstars : recordStars L s = π.starLevels.card := by
      dsimp only [s, cubeSlot]; rw [recordStars_slot]
    rw [slotValue, hstars, slotCube_cubeSlot hπ]
  wram_simp [hval]

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
