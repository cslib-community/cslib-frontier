/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Power.Rename
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.CatalogueLoop
public import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Index
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call

/-!
# Complete shared native box geometry

The actual program computes its power, directory extent, compact count and value-table
base from the original scalar parameters. It assigns every directory slot and writes
exactly the catalogue records counted by the existing finite box family.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM

private theorem powerRegisters_injective : Function.Injective powerRegisters := by decide

/-- The existing power routine computes the actual native span with unchanged memory. -/
theorem exec_span {w L : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (h10 : x.regs Reg.ten = 10)
    (hfit : Fits w (10 ^ L + L + 2)) :
    ∃ y, ExecWithin w (Power.program.rename powerRegisters) x y (4 * L + 5) ∧
      y.regs Reg.span = 10 ^ L ∧ y.regs Reg.one = 1 ∧ y.mem = x.mem ∧
      (∀ i, i ≠ Reg.span → i ≠ Reg.level → i ≠ Reg.one → y.regs i = x.regs i) := by
  obtain ⟨y, he, hv, _, ho, hm, _, _, -⟩ :=
    Power.exec_rename powerRegisters powerRegisters_injective 10 L (by decide) x h10 hL hfit
  refine ⟨y, he, hv, ho, hm, ?_⟩
  intro i hv hc ho
  apply he.regs_eq
  simp [Power.program, Power.body, Code.rename, Code.Preserves, Op.rename, Op.dest,
    Op.bin, powerRegisters, Power.value, Power.counter, Power.base, Power.exponent,
    Power.one, Ne.symm hv, Ne.symm hc, Ne.symm ho]

/-- Explicit scalar initialization, also valid when every old temporary is dirty. -/
theorem exec_constants {w : ℕ} (x : Data registers) (hfit : Fits w 10) :
    ∃ y, ExecWithin w constants x y 5 ∧ y.regs Reg.nil = 0 ∧
      y.regs Reg.one = 1 ∧ y.regs Reg.ten = 10 ∧ y.regs Reg.nine = 9 ∧
      y.regs Reg.three = 3 ∧ y.mem = x.mem ∧
      (∀ i, i ≠ Reg.nil → i ≠ Reg.one → i ≠ Reg.ten → i ≠ Reg.nine →
        i ≠ Reg.three → y.regs i = x.regs i) := by
  suffices ∃ y, ExecWithin w constants x y 5 ∧ y.regs Reg.nil = 0 ∧
      y.regs Reg.one = 1 ∧ y.regs Reg.ten = 10 ∧ y.regs Reg.nine = 9 ∧
      y.regs Reg.three = 3 ∧ y.mem = x.mem by
    obtain ⟨y, he, h0, h1, h10, h9, h3, hm⟩ := this
    refine ⟨y, he, h0, h1, h10, h9, h3, hm, fun i hi0 hi1 hi10 hi9 hi3 =>
      he.regs_eq (by simp [constants, Code.Preserves, Op.dest,
        Ne.symm hi0, Ne.symm hi1, Ne.symm hi10, Ne.symm hi9, Ne.symm hi3])⟩
  unfold constants
  wram_exec
  wram_simp

/-- Actual extent setup and its complete persistent parameter readback. -/
theorem exec_geometrySetup {w L m t D : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (hm : x.regs Reg.inner = m)
    (ht : x.regs Reg.threshold = t) (hD : x.regs Reg.directory = D)
    (hT : x.regs Reg.span = 10 ^ L) (h1 : x.regs Reg.one = 1)
    (h10 : x.regs Reg.ten = 10) (h9 : x.regs Reg.nine = 9)
    (h3 : x.regs Reg.three = 3) (h0 : x.regs Reg.nil = 0)
    (hfit : Fits w (D + (m - t + 1) * 10 ^ L + m + 12)) :
    ∃ y, ExecWithin w geometrySetup x y 6 ∧
      CatalogueParameters L (m - t) D (D + (m - t + 1) * 10 ^ L) y ∧
      y.regs Reg.slot = 0 ∧ y.regs Reg.count = 0 ∧ y.mem = x.mem := by
  have h1le : m - t + 1 ≤ (m - t + 1) * 10 ^ L :=
    Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
  unfold geometrySetup
  wram_exec *
  exact ⟨by constructor <;> wram_simp [*], by wram_simp, by wram_simp, by wram_simp⟩

/-- Actual shared setup, including all digit scans and descriptor writes. -/
theorem exec_geometry {w L m t D : ℕ} (x : Data registers)
    (hL : x.regs Reg.levels = L) (hm : x.regs Reg.inner = m)
    (ht : x.regs Reg.threshold = t) (hD : x.regs Reg.directory = D)
    (hfit : Fits w (D + (D + (m - t + 1) * 10 ^ L) +
      6 * ((m - t + 1) * 10 ^ L) + 10 ^ L + L + m + 12)) :
    ∃ y, ExecWithin w geometry x y
        (4 * L + 20 + (11 * L + 28) * ((m - t + 1) * 10 ^ L)) ∧
      CatalogueParameters L (m - t) D (D + (m - t + 1) * 10 ^ L) y ∧
      y.regs Reg.count = (Cslib.Algorithms.MatrixMultiplication.Schonhage.boxes L m t).card ∧
      y.regs Reg.values = D + (m - t + 1) * 10 ^ L +
        3 * (Cslib.Algorithms.MatrixMultiplication.Schonhage.boxes L m t).card ∧
      CataloguePrefix L (m - t) D (D + (m - t + 1) * 10 ^ L)
        ((m - t + 1) * 10 ^ L) x.mem y.mem := by
  have hS : Nat.count (Eligible L (m - t)) ((m - t + 1) * 10 ^ L) ≤ (m - t + 1) * 10 ^ L :=
    Nat.count_le _
  have hB := count_eligible_eq_card_boxes L m t
  refine WP.exists_execWithin ?_
  unfold geometry geometryFinish
  wram_call (exec_constants x (hfit.of_le ((by decide : 10 ≤ 12).trans (Nat.le_add_left _ _))))
    with a ⟨a0, a1, a10, a9, a3, am, af⟩
  wram_call (exec_span a (by regs_frame) a10 (by fits))
    with b ⟨bT, b1, bm, bf⟩
  wram_call (exec_geometrySetup b (by regs_frame) (by regs_frame) (by regs_frame)
    (by regs_frame) bT b1 (by regs_frame) (by regs_frame) (by regs_frame) (by regs_frame)
    (by fits)) with c ⟨cp, cs, cc, cm⟩
  wram_call (exec_catalogueLoop c cp cs cc (Nat.le_refl _) (by fits))
    with d ⟨dp, _, dc, dmem⟩
  have dr : d.regs Reg.records = D + (m - t + 1) * 10 ^ L := dp.records
  have d3 : d.regs Reg.three = 3 := dp.three
  wram_exec [*]
  refine ⟨by regs_frame, by wram_simp [dc, hB], ?_, ?_⟩
  · wram_simp [hB]; omega
  · simpa only [Data.set_mem, cm, bm, am] using dmem

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
