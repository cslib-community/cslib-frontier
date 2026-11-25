/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Hungarian.MemLayout
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Foundations.Data.Matrix.PairChunks

/-!
# Alternating-tree extension and slack relaxation (`extendCode`)

Internal `O(n)` subroutine applying `hgExtend` and updating `bestRow` and `minv`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Reg

/-- Update `bestRow[idx]` if `idx` is unused and relaxing via `ri0` strictly lowers slack. -/
private def relaxBestRowBody : Code .standard 28 := ram[
  addr ← baseBestRow + idx; val2 ← *addr;
  addr ← baseUsed + idx; val ← *addr;
  if val = zero then [
    addr ← ri0 * rn; addr ← addr + idx; addr ← baseC + addr; val ← *addr;
    addr ← baseNZ + idx; tmp ← *addr; val ← val + tmp;
    addr ← baseY + ri0; tmp ← *addr; val ← val - tmp;
    addr ← baseMinv + idx; tmp ← *addr;
    if val < tmp then [ val2 ← ri0 ] else [ tmp ← zero ]
  ] else [ tmp ← zero ];
  addr ← baseBestRow + idx; *addr ← val2; idx ← idx + one ]

/-- Update `bestRow` across all columns. -/
private def relaxBestRowCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) relaxBestRowBody)

/-- Update `minv[idx]` if `idx` is unused and relaxing via `ri0` lowers slack. -/
private def relaxMinvBody : Code .standard 28 := ram[
  addr ← baseMinv + idx; val2 ← *addr;
  addr ← baseUsed + idx; val ← *addr;
  if val = zero then [
    addr ← ri0 * rn; addr ← addr + idx; addr ← baseC + addr; val ← *addr;
    addr ← baseNZ + idx; tmp ← *addr; val ← val + tmp;
    addr ← baseY + ri0; tmp ← *addr; val ← val - tmp;
    if val < val2 then [ val2 ← val ] else [ tmp ← zero ]
  ] else [ tmp ← zero ];
  addr ← baseMinv + idx; *addr ← val2; idx ← idx + one ]

/-- Update `minv` across all columns. -/
private def relaxMinvCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) relaxMinvBody)

/-- Extend the tree by `rj1` and its mate `ri0`, then relax `bestRow` and `minv`. -/
def extendCode : Code .standard 28 :=
  .seq (ram[ addr ← baseUsed + rj1; *addr ← one; addr ← baseTree + ri0; *addr ← one ])
    (.seq relaxBestRowCode relaxMinvCode)

theorem exec_extendCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ i₀ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hC : CostMem bC C x.mem) (hSM : StepMem bC s bestRow x.mem)
    (hrj1 : x.regs rj1 = j₁.val) (hri0 : x.regs ri0 = i₀.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w extendCode x y (48 * n + 10) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      StepMem bC (hgExtend (fun p => (C p : ℤ)) s j₁ i₀)
        (fun j => if vget (vset s.used j₁ true) j = false ∧
          hgRed (fun p => (C p : ℤ)) s.y s.z i₀ j < vget s.minv j then i₀ else bestRow j) y.mem ∧
      (∀ a, a < bC + n * n ∨ bC + n * n + 7 * n ≤ a → y.mem a = x.mem a) := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  let used' := vset s.used j₁ true
  let tree' := vset s.tree i₀ true
  let bestRow' : Fin n → Fin n := fun j =>
    if vget used' j = false ∧ hgRed c s.y s.z i₀ j < vget s.minv j then i₀ else bestRow j
  have hf_u1 : Fits w (bC + n * n + 3 * n + j₁.val) := hfit.of_le (by have := j₁.isLt; omega)
  have hf_t0 : Fits w (bC + n * n + 4 * n + i₀.val) := hfit.of_le (by have := i₀.isLt; omega)
  have hstep₀ : ∃ y₀,
      ExecWithin w (ram[ addr ← baseUsed + rj1; *addr ← one; addr ← baseTree + ri0; *addr ← one ])
        x y₀ 4 ∧
      (∀ i : Fin 28, i.val < 21 → y₀.regs i = x.regs i) ∧
      y₀.mem = Function.update (Function.update x.mem (bC + n * n + 3 * n + j₁.val) 1)
        (bC + n * n + 4 * n + i₀.val) 1 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb.hbaseUsed, hb.hbaseTree, hb.hone, hrj1, hri0, hf_u1, hf_t0]
    exact ⟨fun i hi => by wram_simp, rfl⟩
  obtain ⟨y₀, he₀, hr₀, hm₀⟩ := hstep₀
  have hused₀ : ∀ j : Fin n, y₀.mem (bC + n * n + 3 * n + j.val) =
      if vget used' j = true then 1 else 0 := by
    intro j
    rw [hm₀, Function.update_of_ne (by have := j.isLt; have := i₀.isLt; omega)]
    by_cases hjj : j = j₁
    · subst hjj
      simp [used']
    · have hne : bC + n * n + 3 * n + j.val ≠ bC + n * n + 3 * n + j₁.val := fun h =>
        hjj (Fin.ext (by omega))
      rw [Function.update_of_ne hne, hSM.hused j]
      simp [used', vget_vset_ne _ _ (Ne.symm hjj)]
  have htree₀ : ∀ i : Fin n, y₀.mem (bC + n * n + 4 * n + i.val) =
      if vget tree' i = true then 1 else 0 := by
    intro i
    rw [hm₀]
    by_cases hii : i = i₀
    · subst hii
      simp [tree']
    · have hne : bC + n * n + 4 * n + i.val ≠ bC + n * n + 4 * n + i₀.val := fun h =>
        hii (Fin.ext (by omega))
      rw [Function.update_of_ne hne,
        Function.update_of_ne (by have := i.isLt; have := j₁.isLt; omega), hSM.htree i]
      simp [tree', vget_vset_ne _ _ (Ne.symm hii)]
  have hout₀ : ∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 5 * n) → y₀.mem a = x.mem a := by
    intro a ha
    rw [hm₀, Function.update_of_ne (by have := i₀.isLt; omega),
      Function.update_of_ne (by have := j₁.isLt; omega)]
  -- Loop 1: relaxBestRowCode
  let dB := bC + n * n + 6 * n
  have hb₀ : BaseRegs n bC M y₀ := hb.of_eq fun i hi => hr₀ i (by omega)
  have hri0₀ : y₀.regs ri0 = i₀.val := (hr₀ ri0 (by decide)).trans hri0
  obtain ⟨y₁, he₁, hr₁, hbest₁, hf₁⟩ := exec_prefixWriteLoop (w := w) (T := 23) (d := dB)
      (body := relaxBestRowBody) y₀ (fun j => (bestRow' j).val) hb₀.hrn (by decide) <| by
    intro y hr hlt hf
    set j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb₀.of_eq fun i hi => hr i (by omega)
    have hri0_y : y.regs ri0 = i₀.val := (hr ri0 (by decide)).trans hri0₀
    have hbest_j : y.mem (bC + n * n + 6 * n + y.regs idx) = (bestRow j).val := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by have := j.isLt; omega)]
      exact hSM.hbest j
    have hu_j : y.mem (bC + n * n + 3 * n + y.regs idx) =
        if vget used' j = true then 1 else 0 := by
      rw [hf _ (by simp only [dB]; omega)]
      exact hused₀ j
    have hmul : i₀.val * n + y.regs idx < n * n := Cslib.Matrix.pairIndex_lt (i₀, j)
    obtain ⟨hle_sub, hsum_le, hred_eq⟩ := hgRed_nat_eq (hCW i₀ j) (hSI.y_bounds i₀)
      (hSI.z_bounds j) (hSI.feas i₀ j)
    have hC_ij : y.mem (bC + (i₀.val * n + y.regs idx)) = C (i₀, j) := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hC i₀ j
    have hnz_j : y.mem (bC + n * n + n + y.regs idx) = (-vget s.z j).toNat := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hSM.hnz j
    have hy_i : y.mem (bC + n * n + i₀.val) = (vget s.y i₀).toNat := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by have := i₀.isLt; omega)]
      exact hSM.hy i₀
    have hm_j : y.mem (bC + n * n + 5 * n + y.regs idx) = (vget s.minv j).toNat := by
      rw [hf _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hSM.hminv j
    have hm_nonneg := (hSI.minv_bounds j).1
    have hred_nonneg : 0 ≤ hgRed c s.y s.z i₀ j := hSI.feas i₀ j
    have hred_eq' : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat =
        (hgRed c s.y s.z i₀ j).toNat := hred_eq
    have hf1 : Fits w (dB + y.regs idx) := hfit.of_le (by simp only [dB]; omega)
    have hf2 : Fits w (bC + n * n + 3 * n + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (i₀.val * n) := hfit.of_le (by omega)
    have hf4 : Fits w (i₀.val * n + y.regs idx) := hfit.of_le (by omega)
    have hf5 : Fits w (bC + (i₀.val * n + y.regs idx)) := hfit.of_le (by omega)
    have hf6 : Fits w (bC + n * n + n + y.regs idx) := hfit.of_le (by omega)
    have hf7 : Fits w (C (i₀, j) + (-vget s.z j).toNat) := hfit.of_le (by omega)
    have hf8 : Fits w (bC + n * n + i₀.val) := hfit.of_le (by have := i₀.isLt; omega)
    have hf9 : Fits w (C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat) :=
      hfit.of_le (by omega)
    have hf10 : Fits w (bC + n * n + 5 * n + y.regs idx) := hfit.of_le (by omega)
    have hf11 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold relaxBestRowBody
    by_cases hu : vget used' j = true
    · have hu_val : (if vget used' j = true then 1 else 0) = 1 := ite_eq_left hu
      have heq_e : (bestRow j).val = (bestRow' j).val := by
        simp [bestRow', hu]
      wram_exec [hby.hbaseBestRow, hby.hbaseUsed, hby.hzero, hby.hone,
        hbest_j, hu_j, hu_val, hf1, hf2, hf11]
      exact ⟨by wram_simp [dB, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
    · have huf : vget used' j = false := Bool.eq_false_iff.mpr hu
      have hu_val : (if vget used' j = true then 1 else 0) = 0 := ite_eq_right hu
      by_cases hlt_r : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat <
          (vget s.minv j).toNat
      · have hlt_z : hgRed c s.y s.z i₀ j < vget s.minv j := by
          rw [hred_eq'] at hlt_r
          omega
        have heq_e : i₀.val = (bestRow' j).val := by
          simp [bestRow', huf, hlt_z]
        wram_exec [hby.hbaseBestRow, hby.hbaseUsed, hby.hzero, hby.hone, hby.hrn, hby.hbaseC,
          hby.hbaseNZ, hby.hbaseY, hby.hbaseMinv, hri0_y, hbest_j, hu_j, hu_val,
          hC_ij, hnz_j, hy_i, hm_j, hle_sub, hlt_r,
          hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11]
        exact ⟨by wram_simp [dB, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      · have hlt_z : ¬hgRed c s.y s.z i₀ j < vget s.minv j := by
          rw [hred_eq'] at hlt_r
          omega
        have heq_e : (bestRow j).val = (bestRow' j).val := by
          simp [bestRow', huf, hlt_z]
        wram_exec [hby.hbaseBestRow, hby.hbaseUsed, hby.hzero, hby.hone, hby.hrn, hby.hbaseC,
          hby.hbaseNZ, hby.hbaseY, hby.hbaseMinv, hri0_y, hbest_j, hu_j, hu_val,
          hC_ij, hnz_j, hy_i, hm_j, hle_sub, hlt_r,
          hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11]
        exact ⟨by wram_simp [dB, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
  -- Loop 2: relaxMinvCode
  let dM := bC + n * n + 5 * n
  have hb₁ : BaseRegs n bC M y₁ := hb₀.of_eq fun i hi => hr₁ i (by omega)
  have hri0₁ : y₁.regs ri0 = i₀.val := (hr₁ ri0 (by decide)).trans hri0₀
  obtain ⟨y₂, he₂, hr₂, hminv₂, hf₂⟩ := exec_prefixWriteLoop (w := w) (T := 21) (d := dM)
      (body := relaxMinvBody) y₁ (fun j => (vget (hgExtend c s j₁ i₀).minv j).toNat) hb₁.hrn
      (by decide) <| by
    intro y hr hlt hf
    set j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb₁.of_eq fun i hi => hr i (by omega)
    have hri0_y : y.regs ri0 = i₀.val := (hr ri0 (by decide)).trans hri0₁
    have hm_j : y.mem (bC + n * n + 5 * n + y.regs idx) = (vget s.minv j).toNat := by
      rw [hf _ (by simp only [dM]; omega), hf₁ _ (by simp only [dB]; omega),
        hout₀ _ (by omega)]
      exact hSM.hminv j
    have hu_j : y.mem (bC + n * n + 3 * n + y.regs idx) =
        if vget used' j = true then 1 else 0 := by
      rw [hf _ (by simp only [dM]; omega), hf₁ _ (by simp only [dB]; omega)]
      exact hused₀ j
    have hmul : i₀.val * n + y.regs idx < n * n := Cslib.Matrix.pairIndex_lt (i₀, j)
    obtain ⟨hle_sub, hsum_le, hred_eq⟩ := hgRed_nat_eq (hCW i₀ j) (hSI.y_bounds i₀)
      (hSI.z_bounds j) (hSI.feas i₀ j)
    have hC_ij : y.mem (bC + (i₀.val * n + y.regs idx)) = C (i₀, j) := by
      rw [hf _ (by simp only [dM]; omega), hf₁ _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hC i₀ j
    have hnz_j : y.mem (bC + n * n + n + y.regs idx) = (-vget s.z j).toNat := by
      rw [hf _ (by simp only [dM]; omega), hf₁ _ (by simp only [dB]; omega), hout₀ _ (by omega)]
      exact hSM.hnz j
    have hy_i : y.mem (bC + n * n + i₀.val) = (vget s.y i₀).toNat := by
      rw [hf _ (by simp only [dM]; have := i₀.isLt; omega),
        hf₁ _ (by simp only [dB]; have := i₀.isLt; omega),
        hout₀ _ (by have := i₀.isLt; omega)]
      exact hSM.hy i₀
    have hm_nonneg := (hSI.minv_bounds j).1
    have hred_nonneg : 0 ≤ hgRed c s.y s.z i₀ j := hSI.feas i₀ j
    have hred_eq' : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat =
        (hgRed c s.y s.z i₀ j).toNat := hred_eq
    have hf1 : Fits w (dM + y.regs idx) := hfit.of_le (by simp only [dM]; omega)
    have hf2 : Fits w (bC + n * n + 3 * n + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (i₀.val * n) := hfit.of_le (by omega)
    have hf4 : Fits w (i₀.val * n + y.regs idx) := hfit.of_le (by omega)
    have hf5 : Fits w (bC + (i₀.val * n + y.regs idx)) := hfit.of_le (by omega)
    have hf6 : Fits w (bC + n * n + n + y.regs idx) := hfit.of_le (by omega)
    have hf7 : Fits w (C (i₀, j) + (-vget s.z j).toNat) := hfit.of_le (by omega)
    have hf8 : Fits w (bC + n * n + i₀.val) := hfit.of_le (by have := i₀.isLt; omega)
    have hf9 : Fits w (C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat) :=
      hfit.of_le (by omega)
    have hf10 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hminv_ext : vget (hgExtend c s j₁ i₀).minv j =
        if vget used' j = true then vget s.minv j
        else min (vget s.minv j) (hgRed c s.y s.z i₀ j) := by
      simpa only [hgExtend] using hgRelax_minv (c := c) _ i₀ j₁ j
    refine WP.exists_execWithin ?_
    unfold relaxMinvBody
    by_cases hu : vget used' j = true
    · have hu_val : (if vget used' j = true then 1 else 0) = 1 := ite_eq_left hu
      have heq_e : (vget s.minv j).toNat = (vget (hgExtend c s j₁ i₀).minv j).toNat := by
        rw [hminv_ext, ite_eq_left hu]
      wram_exec [hby.hbaseMinv, hby.hbaseUsed, hby.hzero, hby.hone,
        hm_j, hu_j, hu_val, hf1, hf2, hf10]
      exact ⟨by wram_simp [dM, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
    · have hu_val : (if vget used' j = true then 1 else 0) = 0 := ite_eq_right hu
      by_cases hlt_r : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat <
          (vget s.minv j).toNat
      · have heq_e : C (i₀, j) + (-vget s.z j).toNat - (vget s.y i₀).toNat =
            (vget (hgExtend c s j₁ i₀).minv j).toNat := by
          rw [hminv_ext, ite_eq_right hu, hred_eq']
          simp only [min_def]
          split_ifs <;> omega
        wram_exec [hby.hbaseMinv, hby.hbaseUsed, hby.hzero, hby.hone, hby.hrn, hby.hbaseC,
          hby.hbaseNZ, hby.hbaseY, hri0_y, hm_j, hu_j, hu_val,
          hC_ij, hnz_j, hy_i, hle_sub, hlt_r,
          hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
        exact ⟨by wram_simp [dM, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      · have heq_e : (vget s.minv j).toNat = (vget (hgExtend c s j₁ i₀).minv j).toNat := by
          rw [hminv_ext, ite_eq_right hu]
          rw [hred_eq'] at hlt_r
          simp only [min_def]
          split_ifs <;> omega
        wram_exec [hby.hbaseMinv, hby.hbaseUsed, hby.hzero, hby.hone, hby.hrn, hby.hbaseC,
          hby.hbaseNZ, hby.hbaseY, hri0_y, hm_j, hu_j, hu_val,
          hC_ij, hnz_j, hy_i, hle_sub, hlt_r,
          hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10]
        exact ⟨by wram_simp [dM, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
  have hout : ∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 7 * n) → y₂.mem a = x.mem a :=
    fun a ha => (hf₂ a (by simp only [dM]; omega)).trans
      ((hf₁ a (by simp only [dB]; omega)).trans (hout₀ a (by omega)))
  refine ⟨y₂, (he₀.seq (he₁.seq he₂)).mono (by omega),
    fun i hi => ((hr₂ i hi).trans (hr₁ i hi)).trans (hr₀ i hi),
    ⟨⟨fun i => ?_, fun j => ?_, fun j => ?_, fun j i hm => ?_, fun i hm => ?_⟩,
      fun j => ?_, fun i => ?_, hminv₂, fun j => ?_⟩,
    fun a ha => hout a (by omega)⟩
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hy i)
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hnz j)
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hcol j)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hrow_some j i hm)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hrow_none i hm)
  · rw [hf₂ _ (by simp only [dM]; have := j.isLt; omega),
      hf₁ _ (by simp only [dB]; have := j.isLt; omega)]
    exact hused₀ j
  · rw [hf₂ _ (by simp only [dM]; have := i.isLt; omega),
      hf₁ _ (by simp only [dB]; have := i.isLt; omega)]
    exact htree₀ i
  · rw [hf₂ _ (by simp only [dM]; have := j.isLt; omega)]
    exact hbest₁ j


end Cslib.Algorithms.WordRAM.Hungarian
