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
# Dual potential and slack adjustment (`dualCode`)

Internal `O(n)` subroutine applying `hgDual` across `y`, `nz`, and `minv`.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Reg

/-- Conditional vector addition body: if `flag[idx] = 1` then `target[idx] += rdelta`. -/
private def condAddBody (flagBase targetBase : Fin 28) : Code .standard 28 := ram[
  addr ← flagBase + idx; val ← *addr;
  addr ← targetBase + idx; val2 ← *addr;
  if val = one then [ val2 ← val2 + rdelta ] else [ tmp ← zero ];
  *addr ← val2; idx ← idx + one ]

/-- Conditional vector addition loop over `0 .. n - 1`. -/
private def condAddCode (flagBase targetBase : Fin 28) : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) (condAddBody flagBase targetBase))

/-- Dual slack update body (`minv[j] -= rdelta` on unused columns). -/
private def dualMinvBody : Code .standard 28 := ram[
  addr ← baseUsed + idx; val ← *addr;
  addr ← baseMinv + idx; val2 ← *addr;
  if val = zero then [ val2 ← val2 - rdelta ] else [ tmp ← zero ];
  *addr ← val2; idx ← idx + one ]

/-- Dual slack update loop. -/
private def dualMinvCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) dualMinvBody)

/-- Complete `O(n)` dual update `hgDual s (vget s.minv j₁)`. -/
def dualCode : Code .standard 28 :=
  .seq (condAddCode baseTree baseY) (.seq (condAddCode baseUsed baseNZ) dualMinvCode)

private theorem exec_condAddCode {w n bC M : ℕ}
    (flagBase targetBase : Fin 28) (hf_lt : flagBase.val < 21) (ht_lt : targetBase.val < 21)
    {bF bT delta : ℕ} {flag : Fin n → Bool} {cur : Fin n → ℕ}
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hbF : x.regs flagBase = bF) (hbT : x.regs targetBase = bT)
    (hdisj : bT + n ≤ bF ∨ bF + n ≤ bT)
    (hdelta : x.regs rdelta = delta)
    (hflag : ∀ k : Fin n, x.mem (bF + k.val) = if flag k = true then 1 else 0)
    (hcur : ∀ k : Fin n, x.mem (bT + k.val) = cur k)
    (hfitF : Fits w (bF + n)) (hfitT : Fits w (bT + n)) (hfitN : Fits w (n + 1))
    (hfitAdd : ∀ k : Fin n, flag k = true → Fits w (cur k + delta)) :
    ∃ y, ExecWithin w (condAddCode flagBase targetBase) x y (11 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ k : Fin n, y.mem (bT + k.val) = if flag k = true then cur k + delta else cur k) ∧
      (∀ a, ¬(bT ≤ a ∧ a < bT + n) → y.mem a = x.mem a) := by
  let e : ℕ → ℕ := fun k =>
    if hk : k < n then if flag ⟨k, hk⟩ = true then cur ⟨k, hk⟩ + delta else cur ⟨k, hk⟩ else 0
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (bT + j) = e j) ∧
      (∀ a, ¬(bT ≤ a ∧ a < bT + k) → y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w (condAddBody flagBase targetBase) y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let k₀ : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hbF_y : y.regs flagBase = bF := (hr flagBase hf_lt).trans hbF
    have hbT_y : y.regs targetBase = bT := (hr targetBase ht_lt).trans hbT
    have hdel_y : y.regs rdelta = delta := (hr rdelta (by decide)).trans hdelta
    have hfk : y.mem (bF + y.regs idx) = if flag k₀ = true then 1 else 0 := by
      rw [hf _ (by omega)]
      exact hflag k₀
    have hck : y.mem (bT + y.regs idx) = cur k₀ := by
      rw [hf _ (by omega)]
      exact hcur k₀
    have hf1 : Fits w (bF + y.regs idx) := hfitF.of_le (by omega)
    have hf2 : Fits w (bT + y.regs idx) := hfitT.of_le (by omega)
    have hf3 : Fits w (y.regs idx + 1) := hfitN.of_le (by omega)
    have hta : targetBase ≠ addr := fun h => by subst h; simp at ht_lt
    have htv : targetBase ≠ val := fun h => by subst h; simp at ht_lt
    have hstep : ∃ z, ExecWithin w (condAddBody flagBase targetBase) y z 9 ∧
        z.mem = Function.update y.mem (bT + y.regs idx) (e (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold condAddBody
      by_cases ht : flag k₀ = true
      · have ht_val : (if flag k₀ = true then 1 else 0) = 1 := ite_eq_left ht
        have heq_e : cur k₀ + delta = e (y.regs idx) := by
          simp only [e, hlt, dite_true]
          exact (ite_eq_left ht).symm
        have hf4 : Fits w (cur k₀ + delta) := hfitAdd k₀ ht
        wram_exec [hbF_y, hbT_y, hta, htv, hby.hone, hby.hzero, hdel_y,
          hfk, ht_val, hck, hf1, hf2, hf3, hf4]
        exact ⟨by wram_simp [hta, htv, hbT_y, heq_e], fun i hi => by wram_simp [hr i hi],
          by wram_simp⟩
      · have ht_val : (if flag k₀ = true then 1 else 0) = 0 := ite_eq_right ht
        have heq_e : cur k₀ = e (y.regs idx) := by
          simp only [e, hlt, dite_true]
          exact (ite_eq_right ht).symm
        wram_exec [hbF_y, hbT_y, hta, htv, hby.hone, hby.hzero, hdel_y,
          hfk, ht_val, hck, hf1, hf2, hf3]
        exact ⟨by wram_simp [hta, htv, hbT_y, hck, heq_e], fun i hi => by wram_simp [hr i hi],
          by wram_simp⟩
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  obtain ⟨y, he, hr, hm, hf⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := x)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun _ _ => rfl⟩
  refine ⟨y, he.mono (by omega), hr, fun k => ?_, hf⟩
  simpa [e, k.isLt] using hm k.val k.isLt

private theorem exec_dualYCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j)
    (x : Data 28) (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hdelta : x.regs rdelta = (vget s.minv j₁).toNat)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w (condAddCode baseTree baseY) x y (11 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ i : Fin n, y.mem (bC + n * n + i.val) = (vget (hgDual s (vget s.minv j₁)).y i).toNat) ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + n) → y.mem a = x.mem a) := by
  have hSD := hgStepInv_dual (c := fun p => (C p : ℤ))
    (fun u v => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u v)⟩) hSI hj₁ hmin
  obtain ⟨y, he, hr, hm, hf⟩ := exec_condAddCode baseTree baseY (by decide) (by decide)
    x hb hb.hbaseTree hb.hbaseY (.inl (by omega)) hdelta hSM.htree hSM.hy
    (hfit.of_le (by omega)) (hfit.of_le (by omega)) (hfit.of_le (by omega)) fun i₀ ht => by
      have hyb := hSI.y_bounds i₀
      have hdb := hSI.minv_bounds j₁
      have hyDb := hSD.y_bounds i₀
      rw [hgDual_y, ite_eq_left ht] at hyDb
      exact hfit.of_le (by omega)
  refine ⟨y, he, hr, fun i₀ => ?_, hf⟩
  rw [hm i₀, hgDual_y]
  have hyb := hSI.y_bounds i₀
  have hdb := hSI.minv_bounds j₁
  by_cases ht : vget s.tree i₀ = true
  · rw [ite_eq_left ht, ite_eq_left ht]; omega
  · rw [ite_eq_right ht, ite_eq_right ht]

private theorem exec_dualNZCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j)
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hused_x : ∀ j : Fin n, x.mem (bC + n * n + 3 * n + j.val) =
      if vget s.used j = true then 1 else 0)
    (hnz_x : ∀ j : Fin n, x.mem (bC + n * n + n + j.val) = (-vget s.z j).toNat)
    (hdelta : x.regs rdelta = (vget s.minv j₁).toNat)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w (condAddCode baseUsed baseNZ) x y (11 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j : Fin n,
        y.mem (bC + n * n + n + j.val) = (-vget (hgDual s (vget s.minv j₁)).z j).toNat) ∧
      (∀ a, ¬(bC + n * n + n ≤ a ∧ a < bC + n * n + 2 * n) → y.mem a = x.mem a) := by
  have hSD := hgStepInv_dual (c := fun p => (C p : ℤ))
    (fun u v => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u v)⟩) hSI hj₁ hmin
  obtain ⟨y, he, hr, hm, hf⟩ := exec_condAddCode baseUsed baseNZ (by decide) (by decide)
    x hb hb.hbaseUsed hb.hbaseNZ (.inl (by omega)) hdelta hused_x hnz_x
    (hfit.of_le (by omega)) (hfit.of_le (by omega)) (hfit.of_le (by omega)) fun j hu => by
      have hzb := hSI.z_bounds j
      have hdb := hSI.minv_bounds j₁
      have hzDb := hSD.z_bounds j
      rw [hgDual_z, ite_eq_left hu] at hzDb
      exact hfit.of_le (by omega)
  refine ⟨y, he, hr, fun j => ?_, fun a ha => hf a (by omega)⟩
  rw [hm j, hgDual_z]
  have hzb := hSI.z_bounds j
  have hdb := hSI.minv_bounds j₁
  by_cases hu : vget s.used j = true
  · rw [ite_eq_left hu, ite_eq_left hu]; omega
  · rw [ite_eq_right hu, ite_eq_right hu]

private theorem exec_dualMinvCode {w n bC M W : ℕ} {c : Fin n × Fin n → ℤ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hSI : HgStepInv c W r s bestRow)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j)
    (x : Data 28) (hb : BaseRegs n bC M x)
    (hused_x : ∀ j : Fin n, x.mem (bC + n * n + 3 * n + j.val) =
      if vget s.used j = true then 1 else 0)
    (hminv_x : ∀ j : Fin n, x.mem (bC + n * n + 5 * n + j.val) = (vget s.minv j).toNat)
    (hdelta : x.regs rdelta = (vget s.minv j₁).toNat)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w dualMinvCode x y (11 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j : Fin n, y.mem (bC + n * n + 5 * n + j.val) =
        (vget (hgDual s (vget s.minv j₁)).minv j).toNat) ∧
      (∀ a, ¬(bC + n * n + 5 * n ≤ a ∧ a < bC + n * n + 6 * n) → y.mem a = x.mem a) := by
  let d := bC + n * n + 5 * n
  let e : ℕ → ℕ := fun k =>
    if hk : k < n then (vget (hgDual s (vget s.minv j₁)).minv ⟨k, hk⟩).toNat else 0
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (d + j) = e j) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + k) → y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w dualMinvBody y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hdel_y : y.regs rdelta = (vget s.minv j₁).toNat := (hr rdelta (by decide)).trans hdelta
    have hu_j : y.mem (bC + n * n + 3 * n + y.regs idx) =
        if vget s.used j = true then 1 else 0 := by
      rw [hf _ (by omega)]
      exact hused_x j
    have hm_j : y.mem (bC + n * n + 5 * n + y.regs idx) = (vget s.minv j).toNat := by
      rw [hf _ (by simp only [d]; omega)]
      exact hminv_x j
    have hmb := hSI.minv_bounds j
    have hdb := hSI.minv_bounds j₁
    have hf1 : Fits w (bC + n * n + 3 * n + y.regs idx) := hfit.of_le (by omega)
    have hf2 : Fits w (d + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hstep : ∃ z, ExecWithin w dualMinvBody y z 9 ∧
        z.mem = Function.update y.mem (d + y.regs idx) (e (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold dualMinvBody
      by_cases hu : vget s.used j = true
      · have hu_val : (if vget s.used j = true then 1 else 0) = 1 := ite_eq_left hu
        have heq_e : (vget s.minv j).toNat = e (y.regs idx) := by
          simp only [e, hlt, dite_true]
          change _ = (vget (hgDual s (vget s.minv j₁)).minv j).toNat
          rw [hgDual_minv, ite_eq_left hu]
        wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hone, hby.hzero, hdel_y,
          hu_j, hu_val, hm_j, hf1, hf2, hf3]
        exact ⟨by wram_simp [d, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      · have huf : vget s.used j = false := Bool.eq_false_iff.mpr hu
        have hu_val : (if vget s.used j = true then 1 else 0) = 0 := ite_eq_right hu
        have hle_m : (vget s.minv j₁).toNat ≤ (vget s.minv j).toNat := by
          have := hmin j huf
          omega
        have heq_e : (vget s.minv j).toNat - (vget s.minv j₁).toNat = e (y.regs idx) := by
          simp only [e, hlt, dite_true]
          change _ = (vget (hgDual s (vget s.minv j₁)).minv j).toNat
          rw [hgDual_minv, ite_eq_right hu]
          have := hmin j huf
          omega
        have hf4 : Fits w ((vget s.minv j).toNat - (vget s.minv j₁).toNat) := hfit.of_le (by omega)
        wram_exec [hby.hbaseUsed, hby.hbaseMinv, hby.hone, hby.hzero, hdel_y,
          hu_j, hu_val, hm_j, hle_m, hf1, hf2, hf3, hf4]
        exact ⟨by wram_simp [d, heq_e], fun i hi => by wram_simp [hr i hi], by wram_simp⟩
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  obtain ⟨y, he, hr, hm, hf⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := x)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun _ _ => rfl⟩
  refine ⟨y, he.mono (by omega), hr, fun j => ?_, fun a ha => hf a (by simp only [d]; omega)⟩
  simpa [d, e, j.isLt] using hm j.val j.isLt

theorem exec_dualCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ} {r j₁ : Fin n}
    {s : HgState n} {bestRow : Fin n → Fin n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hSI : HgStepInv (fun p => (C p : ℤ)) W r s bestRow)
    (hj₁ : vget s.used j₁ = false)
    (hmin : ∀ j, vget s.used j = false → vget s.minv j₁ ≤ vget s.minv j)
    (x : Data 28) (hb : BaseRegs n bC M x) (hSM : StepMem bC s bestRow x.mem)
    (hdelta : x.regs rdelta = (vget s.minv j₁).toNat)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w dualCode x y (33 * n + 9) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      StepMem bC (hgDual s (vget s.minv j₁)) bestRow y.mem ∧
      (∀ a, a < bC + n * n ∨ bC + n * n + 6 * n ≤ a → y.mem a = x.mem a) := by
  obtain ⟨y₁, he₁, hr₁, hy₁, hf₁⟩ := exec_dualYCode hCW hSI hj₁ hmin x hb hSM hdelta hfit
  have hb₁ : BaseRegs n bC M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  have hdel₁ : y₁.regs rdelta = (vget s.minv j₁).toNat := (hr₁ rdelta (by decide)).trans hdelta
  have hused₁ : ∀ j : Fin n, y₁.mem (bC + n * n + 3 * n + j.val) =
      if vget s.used j = true then 1 else 0 :=
    fun j => (hf₁ _ (by have := j.isLt; omega)).trans (hSM.hused j)
  have hnz₁ : ∀ j : Fin n, y₁.mem (bC + n * n + n + j.val) = (-vget s.z j).toNat :=
    fun j => (hf₁ _ (by have := j.isLt; omega)).trans (hSM.hnz j)
  obtain ⟨y₂, he₂, hr₂, hnz₂, hf₂⟩ :=
    exec_dualNZCode hCW hSI hj₁ hmin y₁ hb₁ hused₁ hnz₁ hdel₁ hfit
  have hb₂ : BaseRegs n bC M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  have hdel₂ : y₂.regs rdelta = (vget s.minv j₁).toNat := (hr₂ rdelta (by decide)).trans hdel₁
  have hused₂ : ∀ j : Fin n, y₂.mem (bC + n * n + 3 * n + j.val) =
      if vget s.used j = true then 1 else 0 :=
    fun j => (hf₂ _ (by have := j.isLt; omega)).trans (hused₁ j)
  have hminv₂ : ∀ j : Fin n, y₂.mem (bC + n * n + 5 * n + j.val) = (vget s.minv j).toNat :=
    fun j => (hf₂ _ (by have := j.isLt; omega)).trans
      ((hf₁ _ (by have := j.isLt; omega)).trans (hSM.hminv j))
  obtain ⟨y₃, he₃, hr₃, hminv₃, hf₃⟩ :=
    exec_dualMinvCode hSI hmin y₂ hb₂ hused₂ hminv₂ hdel₂ hfit
  have hout : ∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 2 * n) ∧
      ¬(bC + n * n + 5 * n ≤ a ∧ a < bC + n * n + 6 * n) → y₃.mem a = x.mem a :=
    fun a ⟨ha1, ha2⟩ => (hf₃ a ha2).trans ((hf₂ a (by omega)).trans (hf₁ a (by omega)))
  refine ⟨y₃, (he₁.seq (he₂.seq he₃)).mono (by omega),
    fun i hi => ((hr₃ i hi).trans (hr₂ i hi)).trans (hr₁ i hi),
    ⟨⟨fun i => ?_, fun j => ?_, fun j => ?_, fun j i hm => ?_, fun i hm => ?_⟩,
      fun j => ?_, fun i => ?_, hminv₃, fun j => ?_⟩,
    fun a ha => hout a (by omega)⟩
  · rw [hf₃ _ (by have := i.isLt; omega), hf₂ _ (by have := i.isLt; omega)]
    exact hy₁ i
  · rw [hf₃ _ (by have := j.isLt; omega)]
    exact hnz₂ j
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hcol j)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hrow_some j i hm)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.hrow_none i hm)
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hused j)
  · exact (hout _ (by have := i.isLt; omega)).trans (hSM.htree i)
  · exact (hout _ (by have := j.isLt; omega)).trans (hSM.hbest j)


end Cslib.Algorithms.WordRAM.Hungarian
