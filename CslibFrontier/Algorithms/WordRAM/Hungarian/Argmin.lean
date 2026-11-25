/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Hungarian.MemLayout
import CslibFrontier.Foundations.Data.List.RowMajor

/-!
# Minimum-slack unused-column scan (`argminCode`)

Internal `O(n)` subroutine computing `hgArgmin` for one Hungarian alternating-tree round.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Reg

/-- Scan one column `idx` for the minimum-slack unused column. -/
private def argminBody : Code .standard 28 := ram[
  addr ← baseUsed + idx; val ← *addr;
  if val = zero then [
    addr ← baseMinv + idx; val2 ← *addr;
    if rj1 = rn then [ rj1 ← idx; rdelta ← val2 ]
    else [ if val2 < rdelta then [ rj1 ← idx; rdelta ← val2 ] else [ tmp ← zero ] ]
  ] else [ tmp ← zero ];
  idx ← idx + one ]

/-- Compute `hgArgmin s` into `rj1` and its slack into `rdelta`. -/
def argminCode : Code .standard 28 :=
  .seq (ram[ rj1 ← rn; rdelta ← #0; idx ← #0 ]) (.loop (.lt idx rn) argminBody)

theorem exec_argminCode {w n bC M W : ℕ} {c : Fin n × Fin n → ℤ} {r : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hSI : HgStepInv c W r s bestRow) (x : Data 28)
    (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y j₁, ExecWithin w argminCode x y (13 * n + 5) ∧
      (∀ i : Fin 28, i.val < 18 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧
      hgArgmin s = some j₁ ∧
      y.regs rj1 = j₁.val ∧
      y.regs rdelta = (vget s.minv j₁).toNat := by
  let bAt (k : ℕ) : Option (Fin n) := ((List.finRange n).take k).foldl (hgArgminStep s) none
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 18 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧
      match bAt k with
      | none => y.regs rj1 = n
      | some j₀ => y.regs rj1 = j₀.val ∧ y.regs rdelta = (vget s.minv j₀).toNat
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w argminBody y z 11 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hmem, hbAt⟩ := hy
    let j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hused_j : y.mem (bC + n * n + 3 * n + y.regs idx) =
        if vget s.used j = true then 1 else 0 := by
      rw [hmem]
      exact hSM.hused j
    have hminv_j : y.mem (bC + n * n + 5 * n + y.regs idx) = (vget s.minv j).toNat := by
      rw [hmem]
      exact hSM.hminv j
    have hb_step : bAt (y.regs idx + 1) = hgArgminStep s (bAt (y.regs idx)) j := by
      simp only [bAt, List.take_succ_finRange hlt, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rfl
    refine WP.exists_execWithin ?_
    unfold argminBody
    by_cases hu : vget s.used j = true
    · wram_exec [hby.hbaseUsed, hby.hzero, hby.hone, hused_j, hu]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_⟩, by wram_simp⟩
      rw [hb_step]
      unfold hgArgminStep
      rw [ite_eq_left hu]
      cases hbk : bAt (y.regs idx) with
      | none =>
        rw [hbk] at hbAt
        wram_simp [hbAt]
      | some j₀ =>
        rw [hbk] at hbAt
        exact ⟨by wram_simp [hbAt.1], by wram_simp [hbAt.2]⟩
    · have huf : vget s.used j = false := Bool.eq_false_iff.mpr hu
      cases hbk : bAt (y.regs idx) with
      | none =>
        rw [hbk] at hbAt
        wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hzero, hby.hone, hby.hrn,
          hused_j, huf, hminv_j, hbAt]
        refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_⟩, by wram_simp⟩
        rw [hb_step]
        unfold hgArgminStep
        rw [ite_eq_right hu, hbk]
        exact ⟨by wram_simp; rfl, by wram_simp⟩
      | some j₀ =>
        rw [hbk] at hbAt
        obtain ⟨hrj1, hrdelta⟩ := hbAt
        have hj₀_ne : j₀.val ≠ n := ne_of_lt j₀.isLt
        have hm_j := (hSI.minv_bounds j).1
        have hm_j₀ := (hSI.minv_bounds j₀).1
        wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hzero, hby.hone, hby.hrn,
          hused_j, huf, hminv_j, hrj1, hrdelta, hj₀_ne]
        all_goals
          refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_⟩, by wram_simp⟩
          rw [hb_step]
          unfold hgArgminStep
          rw [ite_eq_right hu, hbk]
          dsimp only
        · rw [ite_eq_left (show vget s.minv j < vget s.minv j₀ by omega)]
          exact ⟨by wram_simp; rfl, by wram_simp⟩
        · rw [ite_eq_right (show ¬vget s.minv j < vget s.minv j₀ by omega)]
          exact ⟨by wram_simp [hrj1], by wram_simp [hrdelta]⟩
  have hsetup : ∃ y₀,
      ExecWithin w (ram[ rj1 ← rn; rdelta ← #0; idx ← #0 ] : Code .standard 28) x y₀ 3 ∧
      P 0 y₀ ∧ y₀.regs idx = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb.hrn]
    exact ⟨⟨fun i hi => by wram_simp, rfl, by
      dsimp only [bAt, List.take, List.foldl]
      wram_simp [hb.hrn]⟩, by wram_simp⟩
  obtain ⟨y₀, hs₀, hP₀, hidx₀⟩ := hsetup
  obtain ⟨y, hl, hPn, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (by omega) (hidx₀ ▸ hP₀)
  obtain ⟨hr, hmem, hb_n⟩ := hPn
  have hbn_eq : bAt n = hgArgmin s := by
    simp [bAt, hgArgmin, List.take_of_length_le (show (List.finRange n).length ≤ n by simp)]
  rw [hbn_eq] at hb_n
  cases ha : hgArgmin s with
  | none =>
    have h1 := usedCount_all (hgArgmin_none ha)
    have h2 := usedCount_le hSI.matching hSI.used_mate
    have h3 := card_lt_of_root_free hSI.matching hSI.root_free
    omega
  | some j₁ =>
    rw [ha] at hb_n
    exact ⟨y, j₁, (hs₀.seq hl).mono (by rw [hidx₀]; omega), hr, hmem, rfl, hb_n.1, hb_n.2⟩


end Cslib.Algorithms.WordRAM.Hungarian
