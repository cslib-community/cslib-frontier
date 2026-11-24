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
import Mathlib.Tactic.Linarith

/-!
# Outer potential initialization and per-phase array initialization

Internal subroutines `initOuterCode` and `initPhaseCode` for the Word-RAM Hungarian solver.
-/

public section

namespace Cslib.Algorithms.WordRAM.Hungarian

open Cslib.WordRAM
open Cslib.Algorithms.Lean.MaxFlow
open Reg

/-- Inner loop body scanning row `idx` for its minimum entry. -/
private def rowMinBody : Code .standard 28 := ram[
  addr ← idx * rn; addr ← addr + idx2; addr ← baseC + addr; val ← *addr;
  if val < acc then [ acc ← val ] else [ tmp ← zero ];
  idx2 ← idx2 + one ]

/-- Compute `hgRowMin` of row `idx` into `acc`. -/
private def rowMinCode : Code .standard 28 :=
  .seq (ram[ addr ← idx * rn; addr ← addr + idx; addr ← baseC + addr; acc ← *addr; idx2 ← #0 ])
    (.loop (.lt idx2 rn) rowMinBody)

private theorem exec_rowMinCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    (hCW : ∀ u v, C (u, v) ≤ W) (u : Fin n) (x : Data 28)
    (hb : BaseRegs n bC M x) (hC : CostMem bC C x.mem) (hu : x.regs idx = u.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w rowMinCode x y (10 * n + 7) ∧
      (∀ i : Fin 28, i.val < 22 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧
      y.regs acc = (hgRowMin (fun p => (C p : ℤ)) u).toNat := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 22 → y.regs i = x.regs i) ∧
      y.mem = x.mem ∧
      y.regs acc ≤ W ∧
      (y.regs acc : ℤ) = ((List.finRange n).take k).foldl (fun a v => min a (c (u, v))) (c (u, u))
  have hstepBody (y : Data 28) (hy : P (y.regs idx2) y) (hlt : y.regs idx2 < n) :
      ∃ z, ExecWithin w rowMinBody y z 8 ∧ P (y.regs idx2 + 1) z ∧
        z.regs idx2 = y.regs idx2 + 1 := by
    obtain ⟨hr, hmem, haccW, haccEq⟩ := hy
    let v : Fin n := ⟨y.regs idx2, hlt⟩
    have hidx : y.regs idx = u.val := (hr idx (by decide)).trans hu
    have hrn_y : y.regs rn = n := (hr rn (by decide)).trans hb.hrn
    have hbC_y : y.regs baseC = bC := (hr baseC (by decide)).trans hb.hbaseC
    have hz_y : y.regs zero = 0 := (hr zero (by decide)).trans hb.hzero
    have ho_y : y.regs one = 1 := (hr one (by decide)).trans hb.hone
    have hmul_lt : u.val * n + y.regs idx2 < n * n := Cslib.Matrix.pairIndex_lt (u, v)
    have hf1 : Fits w (u.val * n) := hfit.of_le (by omega)
    have hf2 : Fits w (u.val * n + y.regs idx2) := hfit.of_le (by omega)
    have hf3 : Fits w (bC + (u.val * n + u.val)) :=
      hfit.of_le (by have : u.val * n + u.val < n * n := Cslib.Matrix.pairIndex_lt (u, u); omega)
    have hf3' : Fits w (bC + (u.val * n + y.regs idx2)) := hfit.of_le (by omega)
    have hf4 : Fits w (y.regs idx2 + 1) := hfit.of_le (by omega)
    have hload : y.mem (bC + (u.val * n + y.regs idx2)) = C (u, v) := by
      rw [hmem]
      exact hC u v
    have htk := List.take_succ_finRange hlt
    refine WP.exists_execWithin ?_
    unfold rowMinBody
    by_cases hcmp : C (u, v) < y.regs acc
    · wram_exec [hidx, hrn_y, hbC_y, hz_y, ho_y, hload, hcmp, hf1, hf2, hf3', hf4]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_, ?_⟩, by wram_simp⟩
      · wram_simp
        exact hCW u v
      · wram_simp
        rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, ← haccEq]
        dsimp only [c, v] at hcmp ⊢
        simp only [min_def]
        split_ifs <;> omega
    · wram_exec [hidx, hrn_y, hbC_y, hz_y, ho_y, hload, hcmp, hf1, hf2, hf3', hf4]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], hmem, ?_, ?_⟩, by wram_simp⟩
      · wram_simp
        exact haccW
      · wram_simp
        rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, ← haccEq]
        dsimp only [c, v] at hcmp ⊢
        simp only [min_def]
        split_ifs <;> omega
  have hmul_uu : u.val * n + u.val < n * n := Cslib.Matrix.pairIndex_lt (u, u)
  have hf1 : Fits w (u.val * n) := hfit.of_le (by omega)
  have hf2 : Fits w (u.val * n + u.val) := hfit.of_le (by omega)
  have hf3 : Fits w (bC + (u.val * n + u.val)) := hfit.of_le (by omega)
  have hload0 : x.mem (bC + (u.val * n + u.val)) = C (u, u) := hC u u
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ addr ← idx * rn; addr ← addr + idx; addr ← baseC + addr; acc ← *addr; idx2 ← #0 ] :
        Code .standard 28)
      x s₀ 5 ∧ P 0 s₀ ∧ s₀.regs idx2 = 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [hu, hb.hrn, hb.hbaseC, hload0, hf1, hf2, hf3]
    exact ⟨⟨fun i hi => by wram_simp, rfl, by wram_simp; exact hCW u u,
      by wram_simp; simp [c]⟩, by wram_simp⟩
  obtain ⟨s₀, hes₀, hPs₀, hidxs₀⟩ := hs₀
  obtain ⟨y, hl, hPn, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hstepBody (by omega) (hidxs₀ ▸ hPs₀)
  obtain ⟨hr, hmem, _, haccEq⟩ := hPn
  refine ⟨y, (hes₀.seq hl).mono (by rw [hidxs₀]; omega), hr, hmem, ?_⟩
  have hfull : (List.finRange n).take n = List.finRange n :=
    List.take_of_length_le (by simp)
  rw [hfull] at haccEq
  change (y.regs acc : ℤ) = hgRowMin c u at haccEq
  have hnonneg := (hgRowMin_bounds (c := c)
    (fun u' v' => ⟨Nat.cast_nonneg _, Nat.cast_le.mpr (hCW u' v')⟩) u).1
  dsimp only [c] at haccEq hnonneg
  omega

/-- Body of `initYCode`: compute row minimum and store it into `y[idx]`. -/
private def initYBody : Code .standard 28 :=
  .seq rowMinCode (ram[ addr ← baseY + idx; *addr ← acc; idx ← idx + one ])

/-- Populate `y[0..n)` with `hgRowMin`. -/
private def initYCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) initYBody)

private theorem exec_initYCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    (hCW : ∀ u v, C (u, v) ≤ W) (x : Data 28)
    (hb : BaseRegs n bC M x) (hC : CostMem bC C x.mem)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w initYCode x y (10 * n * n + 12 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ u : Fin n, y.mem (bC + n * n + u.val) = (hgRowMin (fun p => (C p : ℤ)) u).toNat) ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + n) → y.mem a = x.mem a) := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  let d := bC + n * n
  let e : ℕ → ℕ := fun k => if hk : k < n then (hgRowMin c ⟨k, hk⟩).toNat else 0
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (d + j) = e j) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + k) → y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w initYBody y z (10 * n + 10) ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let u : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hCy : CostMem bC C y.mem := hC.of_outside fun a ha => hf a (by omega)
    obtain ⟨y₁, he₁, hr₁, hmem₁, hacc₁⟩ := exec_rowMinCode hCW u y hby hCy rfl hfit
    have hbY₁ : y₁.regs baseY = d :=
      ((hr₁ baseY (by decide)).trans (hr baseY (by decide))).trans hb.hbaseY
    have hidx₁ : y₁.regs idx = y.regs idx := hr₁ idx (by decide)
    have hone₁ : y₁.regs one = 1 :=
      ((hr₁ one (by decide)).trans (hr one (by decide))).trans hb.hone
    have hf_addr : Fits w (d + y.regs idx) := hfit.of_le (by omega)
    have hf_next : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hej : y₁.regs acc = e (y.regs idx) := by
      simp only [e, hlt, dite_true]
      exact hacc₁
    have hstep₂ : ∃ z, ExecWithin w
        (ram[ addr ← baseY + idx; *addr ← acc; idx ← idx + one ] : Code .standard 28) y₁ z 3 ∧
        z = ((y₁.set addr (d + y.regs idx)).write (d + y.regs idx) (e (y.regs idx))).set idx
          (y.regs idx + 1) := by
      refine WP.exists_execWithin ?_
      wram_exec [hbY₁, hidx₁, hone₁, hej, hf_addr, hf_next]
      rfl
    obtain ⟨z, he₂, rfl⟩ := hstep₂
    have hmem_z : (((y₁.set addr (d + y.regs idx)).write (d + y.regs idx) (e (y.regs idx))).set idx
        (y.regs idx + 1)).mem = Function.update y.mem (d + y.regs idx) (e (y.regs idx)) := by
      rw [← hmem₁]
      rfl
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmem_z
    refine ⟨_, (he₁.seq he₂).mono (by omega), ⟨fun i hi => ?_, hm', hf'⟩, by wram_simp⟩
    wram_simp [hr₁ i (by omega), hr i hi]
  obtain ⟨y, he, hr, hm, hf⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := x)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun _ _ => rfl⟩
  refine ⟨y, he.mono (by nlinarith), hr, fun u => ?_, hf⟩
  simpa [d, e, u.isLt] using hm u.val u.isLt

/-- Initialize `y`, `nz`, `colMate`, and `rowMate` before the first phase. -/
def initOuterCode : Code .standard 28 :=
  .seq initYCode
    (.seq (fillConst baseNZ zero)
      (.seq (fillConst baseColMate rn) (fillConst baseRowMate rn)))

theorem exec_initOuterCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    (hCW : ∀ u v, C (u, v) ≤ W) (x : Data 28)
    (hb : BaseRegs n bC M x) (hC : CostMem bC C x.mem)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w initOuterCode x y (10 * n * n + 27 * n + 12) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      OuterMem bC (Vector.ofFn (hgRowMin fun p => (C p : ℤ))) (Vector.replicate n 0)
        (Vector.replicate n none) y.mem ∧
      (∀ a, ¬(bC + n * n ≤ a ∧ a < bC + n * n + 8 * n + 1 ∧ a ≠ bC + n * n + 7 * n) →
        y.mem a = x.mem a) := by
  have hfit_a : Fits w (bC + n * n + 8 * n + 2) := hfit.of_le (by omega)
  obtain ⟨y₁, he₁, hr₁, hy₁, hf₁⟩ := exec_initYCode hCW x hb hC hfit
  have hb₁ : BaseRegs n bC M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂, hr₂, hnz₂, hf₂⟩ := exec_fillConst baseNZ zero (by decide) (by decide) y₁ hb₁
    (by rw [hb₁.hbaseNZ]; omega) hfit_a
  have hb₂ : BaseRegs n bC M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  obtain ⟨y₃, he₃, hr₃, hcm₃, hf₃⟩ := exec_fillConst baseColMate rn (by decide) (by decide) y₂ hb₂
    (by rw [hb₂.hbaseColMate]; omega) hfit_a
  have hb₃ : BaseRegs n bC M y₃ := hb₂.of_eq fun i hi => hr₃ i (by omega)
  obtain ⟨y₄, he₄, hr₄, hrm₄, hf₄⟩ := exec_fillConst baseRowMate rn (by decide) (by decide) y₃ hb₃
    (by rw [hb₃.hbaseRowMate]; omega) hfit_a
  refine ⟨y₄, (he₁.seq (he₂.seq (he₃.seq he₄))).mono (by nlinarith),
    fun i hi => (((hr₄ i hi).trans (hr₃ i hi)).trans (hr₂ i hi)).trans (hr₁ i hi),
    ⟨fun i => ?_, fun j => ?_, fun j => ?_, fun j i hm => ?_, fun i _ => ?_⟩, fun a ha => ?_⟩
  · rw [hf₄ _ (by rw [hb₃.hbaseRowMate]; have := i.isLt; omega),
      hf₃ _ (by rw [hb₂.hbaseColMate]; have := i.isLt; omega),
      hf₂ _ (by rw [hb₁.hbaseNZ]; have := i.isLt; omega), hy₁ i]
    simp [vget]
  · rw [hf₄ _ (by rw [hb₃.hbaseRowMate]; have := j.isLt; omega),
      hf₃ _ (by rw [hb₂.hbaseColMate]; have := j.isLt; omega)]
    have := hnz₂ j.val j.isLt
    rw [hb₁.hbaseNZ, hb₁.hzero] at this
    simpa [vget] using this
  · rw [hf₄ _ (by rw [hb₃.hbaseRowMate]; have := j.isLt; omega)]
    have := hcm₃ j.val j.isLt
    rw [hb₂.hbaseColMate, hb₂.hrn] at this
    simpa [vget, encodeOptFin] using this
  · simp [vget] at hm
  · have := hrm₄ i.val i.isLt
    rwa [hb₃.hbaseRowMate, hb₃.hrn] at this
  · rw [hf₄ a (by rw [hb₃.hbaseRowMate]; omega),
      hf₃ a (by rw [hb₂.hbaseColMate]; omega),
      hf₂ a (by rw [hb₁.hbaseNZ]; omega),
      hf₁ a (by omega)]

/-- Initialize `minv[j] := C[rr, j] + nz[j] - y[rr]` for `j = 0 .. n - 1`. -/
private def initMinvBody : Code .standard 28 := ram[
  addr ← rr * rn; addr ← addr + idx; addr ← baseC + addr; val ← *addr;
  addr ← baseNZ + idx; val2 ← *addr; val ← val + val2;
  addr ← baseY + rr; val2 ← *addr; val ← val - val2;
  addr ← baseMinv + idx; *addr ← val; idx ← idx + one ]

/-- Compute initial column slacks for phase `rr`. -/
private def initMinvCode : Code .standard 28 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx rn) initMinvBody)

private theorem exec_initMinvCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    {y₀ z₀ : Vector ℤ n} {mate₀ : Vector (Option (Fin n)) n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hOB : HgOuterBound (fun p => (C p : ℤ)) W y₀ z₀ mate₀)
    (r : Fin n) (x : Data 28) (hb : BaseRegs n bC M x)
    (hC : CostMem bC C x.mem) (hOM : OuterMem bC y₀ z₀ mate₀ x.mem)
    (hr_reg : x.regs rr = r.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w initMinvCode x y (15 * n + 3) ∧
      (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j : Fin n, y.mem (bC + n * n + 5 * n + j.val) =
        (hgRed (fun p => (C p : ℤ)) y₀ z₀ r j).toNat) ∧
      (∀ a, ¬(bC + n * n + 5 * n ≤ a ∧ a < bC + n * n + 6 * n) → y.mem a = x.mem a) := by
  let c : Fin n × Fin n → ℤ := fun p => (C p : ℤ)
  let d := bC + n * n + 5 * n
  let e : ℕ → ℕ := fun k => if hk : k < n then (hgRed c y₀ z₀ r ⟨k, hk⟩).toNat else 0
  let P (k : ℕ) (y : Data 28) : Prop :=
    (∀ i : Fin 28, i.val < 21 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (d + j) = e j) ∧
      (∀ a, ¬(d ≤ a ∧ a < d + k) → y.mem a = x.mem a)
  have hbody (y : Data 28) (hy : P (y.regs idx) y) (hlt : y.regs idx < n) :
      ∃ z, ExecWithin w initMinvBody y z 13 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let j : Fin n := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs n bC M y := hb.of_eq fun i hi => hr i (by omega)
    have hrr_y : y.regs rr = r.val := (hr rr (by decide)).trans hr_reg
    have hmul : r.val * n + y.regs idx < n * n := Cslib.Matrix.pairIndex_lt (r, j)
    obtain ⟨hle_sub, hsum_le, hred_eq⟩ := hgRed_nat_eq (hCW r j) (hOB.y_bounds r)
      (hOB.z_bounds j) (hOB.feas r j)
    have hC_rj : y.mem (bC + (r.val * n + y.regs idx)) = C (r, j) := by
      rw [hf _ (by omega)]
      exact hC r j
    have hnz_j : y.mem (bC + n * n + n + y.regs idx) = (-vget z₀ j).toNat := by
      rw [hf _ (by omega)]
      exact hOM.hnz j
    have hy_r : y.mem (bC + n * n + r.val) = (vget y₀ r).toNat := by
      rw [hf _ (by omega)]
      exact hOM.hy r
    have hf1 : Fits w (r.val * n) := hfit.of_le (by omega)
    have hf2 : Fits w (r.val * n + y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (bC + (r.val * n + y.regs idx)) := hfit.of_le (by omega)
    have hf4 : Fits w (bC + n * n + n + y.regs idx) := hfit.of_le (by omega)
    have hf5 : Fits w (C (r, j) + (-vget z₀ j).toNat) := hfit.of_le (by omega)
    have hf6 : Fits w (bC + n * n + r.val) := hfit.of_le (by have := r.isLt; omega)
    have hf7 : Fits w (C (r, j) + (-vget z₀ j).toNat - (vget y₀ r).toNat) := hfit.of_le (by omega)
    have hf8 : Fits w (d + y.regs idx) := hfit.of_le (by omega)
    have hf9 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hej : C (r, j) + (-vget z₀ j).toNat - (vget y₀ r).toNat = e (y.regs idx) := by
      simp only [e, hlt, dite_true]
      exact hred_eq
    have hstep : ∃ z, ExecWithin w initMinvBody y z 13 ∧
        z.mem = Function.update y.mem (d + y.regs idx) (e (y.regs idx)) ∧
        (∀ i : Fin 28, i.val < 21 → z.regs i = x.regs i) ∧
        z.regs idx = y.regs idx + 1 := by
      refine WP.exists_execWithin ?_
      unfold initMinvBody
      wram_exec [hrr_y, hby.hrn, hby.hbaseC, hby.hbaseNZ, hby.hbaseY, hby.hbaseMinv, hby.hone,
        hC_rj, hnz_j, hy_r, hle_sub, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9]
      refine ⟨?_, fun i hi => by wram_simp [hr i hi], by wram_simp⟩
      wram_simp [d, hej]
    obtain ⟨z, he, hmz, hrz, hiz⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf hmz
    exact ⟨z, he, ⟨hrz, hm', hf'⟩, hiz⟩
  obtain ⟨y, he, hr, hm, hf⟩ := exec_forLoop P
    (fun y hy => (hy.1 rn (by decide)).trans hb.hrn) hbody (x := x)
    ⟨fun i hi => by wram_simp, fun _ hj => by omega, fun _ _ => rfl⟩
  refine ⟨y, he.mono (by omega), hr, fun j => ?_, fun a ha => hf a (by simp only [d]; omega)⟩
  simpa [d, e, j.isLt] using hm j.val j.isLt

/-- Initialize all phase arrays (`used`, `tree`, `bestRow`, `minv`, and `augmented = 0`). -/
def initPhaseCode : Code .standard 28 :=
  .seq (fillConst baseUsed zero)
    (.seq (fillConst baseTree zero)
      (.seq (ram[ addr ← baseTree + rr; *addr ← one ])
        (.seq (fillConst baseBestRow rr)
          (.seq initMinvCode (ram[ augmented ← #0 ])))))

theorem exec_initPhaseCode {w n bC M W : ℕ} {C : Fin n × Fin n → ℕ}
    {y₀ z₀ : Vector ℤ n} {mate₀ : Vector (Option (Fin n)) n}
    (hCW : ∀ u v, C (u, v) ≤ W)
    (hOB : HgOuterBound (fun p => (C p : ℤ)) W y₀ z₀ mate₀)
    (r : Fin n) (x : Data 28) (hb : BaseRegs n bC M x)
    (hC : CostMem bC C x.mem) (hOM : OuterMem bC y₀ z₀ mate₀ x.mem)
    (hr_reg : x.regs rr = r.val)
    (hfit : Fits w (bC + n * n + 8 * n + 2 * W + 2)) :
    ∃ y, ExecWithin w initPhaseCode x y (30 * n + 15) ∧
      (∀ i : Fin 28, i.val < 17 → y.regs i = x.regs i) ∧
      y.regs augmented = 0 ∧
      StepMem bC (hgInit (fun p => (C p : ℤ)) y₀ z₀ mate₀ r) (fun _ => r) y.mem ∧
      (∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 7 * n) → y.mem a = x.mem a) := by
  have hfit_a : Fits w (bC + n * n + 8 * n + 2) := hfit.of_le (by omega)
  obtain ⟨y₁, he₁, hr₁, hused₁, hf₁⟩ := exec_fillConst baseUsed zero (by decide) (by decide) x hb
    (by rw [hb.hbaseUsed]; omega) hfit_a
  have hb₁ : BaseRegs n bC M y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂, hr₂, htree₂, hf₂⟩ := exec_fillConst baseTree zero (by decide) (by decide) y₁ hb₁
    (by rw [hb₁.hbaseTree]; omega) hfit_a
  have hb₂ : BaseRegs n bC M y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  have hrr₂ : y₂.regs rr = r.val := ((hr₂ rr (by decide)).trans (hr₁ rr (by decide))).trans hr_reg
  have hf_tr : Fits w (bC + n * n + 4 * n + r.val) := hfit.of_le (by have := r.isLt; omega)
  have hstep₃ : ∃ y₃,
      ExecWithin w (ram[ addr ← baseTree + rr; *addr ← one ] : Code .standard 28) y₂ y₃ 2 ∧
      y₃ = (y₂.set addr (bC + n * n + 4 * n + r.val)).write (bC + n * n + 4 * n + r.val) 1 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₂.hbaseTree, hrr₂, hb₂.hone, hf_tr]
    rfl
  obtain ⟨y₃, he₃, rfl⟩ := hstep₃
  have hb₃ : BaseRegs n bC M
      ((y₂.set addr (bC + n * n + 4 * n + r.val)).write (bC + n * n + 4 * n + r.val) 1) :=
    hb₂.of_eq fun i hi => by wram_simp
  have hrr₃ : ((y₂.set addr (bC + n * n + 4 * n + r.val)).write
      (bC + n * n + 4 * n + r.val) 1).regs rr = r.val := by wram_simp [hrr₂]
  obtain ⟨y₄, he₄, hr₄, hbest₄, hf₄⟩ := exec_fillConst baseBestRow rr (by decide) (by decide) _ hb₃
    (by rw [hb₃.hbaseBestRow]; omega) hfit_a
  have hb₄ : BaseRegs n bC M y₄ := hb₃.of_eq fun i hi => hr₄ i (by omega)
  have hrr₄ : y₄.regs rr = r.val := (hr₄ rr (by decide)).trans hrr₃
  have hout₄ : ∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 7 * n) → y₄.mem a = x.mem a := by
    intro a ha
    have hne_tr : a ≠ bC + n * n + 4 * n + r.val := by have := r.isLt; omega
    rw [hf₄ a (by rw [hb₃.hbaseBestRow]; omega)]
    change Function.update y₂.mem (bC + n * n + 4 * n + r.val) 1 a = x.mem a
    rw [Function.update_of_ne hne_tr, hf₂ a (by rw [hb₁.hbaseTree]; omega),
      hf₁ a (by rw [hb.hbaseUsed]; omega)]
  have hC₄ : CostMem bC C y₄.mem := hC.of_outside fun a ha => hout₄ a (by omega)
  have hOM₄ : OuterMem bC y₀ z₀ mate₀ y₄.mem :=
    ⟨fun i => (hout₄ _ (by have := i.isLt; omega)).trans (hOM.hy i),
     fun j => (hout₄ _ (by have := j.isLt; omega)).trans (hOM.hnz j),
     fun j => (hout₄ _ (by have := j.isLt; omega)).trans (hOM.hcol j),
     fun j i hm => (hout₄ _ (by have := i.isLt; omega)).trans (hOM.hrow_some j i hm),
     fun i hm => (hout₄ _ (by have := i.isLt; omega)).trans (hOM.hrow_none i hm)⟩
  obtain ⟨y₅, he₅, hr₅, hminv₅, hf₅⟩ := exec_initMinvCode hCW hOB r y₄ hb₄ hC₄ hOM₄ hrr₄ hfit
  have hstep₆ : ∃ y₆,
      ExecWithin w (ram[ augmented ← #0 ] : Code .standard 28) y₅ y₆ 1 ∧
      y₆ = y₅.set augmented 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨y₆, he₆, rfl⟩ := hstep₆
  have hout₅ : ∀ a, ¬(bC + n * n + 3 * n ≤ a ∧ a < bC + n * n + 7 * n) → y₅.mem a = x.mem a :=
    fun a ha => (hf₅ a (by omega)).trans (hout₄ a ha)
  refine ⟨_, (he₁.seq (he₂.seq (he₃.seq (he₄.seq (he₅.seq he₆))))).mono (by omega),
    fun i hi => ?_, by wram_simp, ?_, hout₅⟩
  · have h5 := hr₅ i (by omega)
    have h4 := hr₄ i (by omega)
    have h2 := hr₂ i (by omega)
    have h1 := hr₁ i (by omega)
    wram_simp [h5, h4, h2, h1]
  · refine ⟨⟨fun i => ?_, fun j => ?_, fun j => ?_, fun j i hm => ?_, fun i hm => ?_⟩,
      fun j => ?_, fun i => ?_, fun j => ?_, fun j => ?_⟩
    · change y₅.mem _ = _
      simpa only [hgInit_y] using (hout₅ _ (by have := i.isLt; omega)).trans (hOM.hy i)
    · change y₅.mem _ = _
      simpa only [hgInit_z] using (hout₅ _ (by have := j.isLt; omega)).trans (hOM.hnz j)
    · change y₅.mem _ = _
      simpa only [hgInit_mate] using (hout₅ _ (by have := j.isLt; omega)).trans (hOM.hcol j)
    · rw [hgInit_mate] at hm
      exact (hout₅ _ (by have := i.isLt; omega)).trans (hOM.hrow_some j i hm)
    · exact (hout₅ _ (by have := i.isLt; omega)).trans (hOM.hrow_none i hm)
    · change y₅.mem (bC + n * n + 3 * n + j.val) = _
      rw [hf₅ _ (by have := j.isLt; omega), hf₄ _ (by rw [hb₃.hbaseBestRow]; have := j.isLt; omega)]
      change Function.update y₂.mem (bC + n * n + 4 * n + r.val) 1 (bC + n * n + 3 * n + j.val) = _
      rw [Function.update_of_ne (by have := j.isLt; have := r.isLt; omega),
        hf₂ _ (by rw [hb₁.hbaseTree]; have := j.isLt; omega)]
      have hu := hused₁ j.val j.isLt
      rw [hb.hbaseUsed, hb.hzero] at hu
      simpa [hgInit_used] using hu
    · change y₅.mem (bC + n * n + 4 * n + i.val) = _
      rw [hf₅ _ (by have := i.isLt; omega), hf₄ _ (by rw [hb₃.hbaseBestRow]; have := i.isLt; omega),
        hgInit_tree]
      change Function.update y₂.mem (bC + n * n + 4 * n + r.val) 1 (bC + n * n + 4 * n + i.val) = _
      by_cases hir : i = r
      · subst hir
        simp
      · have hne : bC + n * n + 4 * n + i.val ≠ bC + n * n + 4 * n + r.val := fun h =>
          hir (Fin.ext (by omega))
        rw [Function.update_of_ne hne]
        have ht := htree₂ i.val i.isLt
        rw [hb₁.hbaseTree, hb₁.hzero] at ht
        simpa [hir] using ht
    · simpa [hgInit_minv] using hminv₅ j
    · change y₅.mem (bC + n * n + 6 * n + j.val) = r.val
      rw [hf₅ _ (by have := j.isLt; omega)]
      have hb_j := hbest₄ j.val j.isLt
      rwa [hb₃.hbaseBestRow, hrr₃] at hb_j


end Cslib.Algorithms.WordRAM.Hungarian
