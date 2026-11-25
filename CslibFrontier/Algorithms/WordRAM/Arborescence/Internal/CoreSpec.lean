/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.CoreProg
public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.ReducedCost
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.BasicSpec
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.BestEntryExitSpec
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.ContractSpec
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.ExpandSpec
import CslibFrontier.Foundations.Data.List.RowMajor

/-!
# Full `edmondsCoreProg_spec` correctness and `O(n³)` memory-cost theorem (internal)

Combines the forward contraction loop and backward expansion loop invariants to establish
`edmondsCoreProg_spec` with `O(n³)` total `memoryCost` and width-independent admissibility.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.Algorithms.Lean.Arborescence
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.Signed

attribute [local client_simps] StateTransitionSpec.clientState
  StateTransitionSpec.runClient_pure'
  runClient_read runClient_write runClient_allocDirty runClient_ite
  prog_clientState_ite

/-! ### Full solver `edmondsCoreProg_spec`, entry programs, and `O(n³)` Word-RAM theorems -/

private structure LevelFrame (n : ℕ) where
  parents : ParentTable n
  inCycle : Vector Bool n
  bEntry : Vector (Option (Fin n)) n
  bExit : Vector (Option (Fin n)) n
  x0 : Fin n

private def expandFrames {n : ℕ} : List (LevelFrame n) → ParentTable n → ParentTable n
  | [], q => q
  | fr :: rest, q =>
    expandParentTable fr.parents fr.inCycle fr.bEntry fr.bExit fr.x0 (expandFrames rest q)

private theorem expandFrames_append_singleton {n : ℕ} (frs : List (LevelFrame n))
    (fr : LevelFrame n) (q : ParentTable n) :
    expandFrames (frs ++ [fr]) q =
      expandFrames frs (expandParentTable fr.parents fr.inCycle fr.bEntry fr.bExit fr.x0 q) := by
  induction frs with
  | nil => rfl
  | cons _ _ ih => simp [expandFrames, ih]

private def FrameStored (ws n k : ℕ) (fr : LevelFrame n) (s : Memory.State) : Prop :=
  s.mem (frameRepAddr ws n k) = fr.x0.1 ∧
    (∀ v : Fin n, s.mem (frameParentBase ws n k + v.1) = (fr.parents[v.1]).1) ∧
    (∀ v : Fin n, s.mem (frameMaskBase ws n k + v.1) = if fr.inCycle[v.1] then 1 else 0) ∧
    (∀ v : Fin n, s.mem (frameBEntryBase ws n k + v.1) = optFinIdx fr.bEntry[v.1]) ∧
    (∀ v : Fin n, s.mem (frameBExitBase ws n k + v.1) = optFinIdx fr.bExit[v.1])

private theorem frameStored_congr {ws n k : ℕ} {fr : LevelFrame n} {s₁ s₂ : Memory.State}
    (h : FrameStored ws n k fr s₁)
    (heq : ∀ addr, frameBase ws n k ≤ addr → addr < frameBase ws n k + (4 * n + 1) →
      s₂.mem addr = s₁.mem addr) :
    FrameStored ws n k fr s₂ := by
  refine ⟨?_, fun v => ?_, fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [heq _ (by dsimp only [frameRepAddr]; omega) (by dsimp only [frameRepAddr]; omega)]
    exact h.1
  · have := v.isLt
    rw [heq _ (by dsimp only [frameParentBase]; omega) (by dsimp only [frameParentBase]; omega)]
    exact h.2.1 v
  · have := v.isLt
    rw [heq _ (by dsimp only [frameMaskBase]; omega) (by dsimp only [frameMaskBase]; omega)]
    exact h.2.2.1 v
  · have := v.isLt
    rw [heq _ (by dsimp only [frameBEntryBase]; omega) (by dsimp only [frameBEntryBase]; omega)]
    exact h.2.2.2.1 v
  · have := v.isLt
    rw [heq _ (by dsimp only [frameBExitBase]; omega) (by dsimp only [frameBExitBase]; omega)]
    exact h.2.2.2.2 v

private structure ContractRoundDisj (ws n k : ℕ) : Prop where
  fp_rep : ∀ v : Fin n, frameParentBase ws n k + v.1 ≠ frameRepAddr ws n k
  adj_rep : ∀ u col : Fin n, curAdjBase ws n + u.1 * n + col.1 ≠ frameRepAddr ws n k
  cost_rep : ∀ u col : Fin n, curCostBase ws n + u.1 * n + col.1 ≠ frameRepAddr ws n k
  adj_cm : ∀ u col : Fin n,
    ¬(frameMaskBase ws n k ≤ curAdjBase ws n + u.1 * n + col.1 ∧
      curAdjBase ws n + u.1 * n + col.1 < frameMaskBase ws n k + n)
  cost_cm : ∀ u col : Fin n,
    ¬(frameMaskBase ws n k ≤ curCostBase ws n + u.1 * n + col.1 ∧
      curCostBase ws n + u.1 * n + col.1 < frameMaskBase ws n k + n)
  fp_cm : ∀ v : Fin n,
    ¬(frameMaskBase ws n k ≤ frameParentBase ws n k + v.1 ∧
      frameParentBase ws n k + v.1 < frameMaskBase ws n k + n)
  adj_be : ∀ u col : Fin n,
    ¬((candPredBase ws n ≤ curAdjBase ws n + u.1 * n + col.1 ∧
        curAdjBase ws n + u.1 * n + col.1 < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ curAdjBase ws n + u.1 * n + col.1 ∧
        curAdjBase ws n + u.1 * n + col.1 < frameBEntryBase ws n k + n))
  cost_be : ∀ u col : Fin n,
    ¬((candPredBase ws n ≤ curCostBase ws n + u.1 * n + col.1 ∧
        curCostBase ws n + u.1 * n + col.1 < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ curCostBase ws n + u.1 * n + col.1 ∧
        curCostBase ws n + u.1 * n + col.1 < frameBEntryBase ws n k + n))
  mask_be : ∀ y : Fin n,
    ¬((candPredBase ws n ≤ frameMaskBase ws n k + y.1 ∧
        frameMaskBase ws n k + y.1 < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ frameMaskBase ws n k + y.1 ∧
        frameMaskBase ws n k + y.1 < frameBEntryBase ws n k + n))
  fp_be : ∀ v : Fin n,
    ¬((candPredBase ws n ≤ frameParentBase ws n k + v.1 ∧
        frameParentBase ws n k + v.1 < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ frameParentBase ws n k + v.1 ∧
        frameParentBase ws n k + v.1 < frameBEntryBase ws n k + n))
  adj_bx : ∀ u col : Fin n,
    ¬((candPredBase ws n ≤ curAdjBase ws n + u.1 * n + col.1 ∧
        curAdjBase ws n + u.1 * n + col.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ curAdjBase ws n + u.1 * n + col.1 ∧
        curAdjBase ws n + u.1 * n + col.1 < frameBExitBase ws n k + n))
  cost_bx : ∀ u col : Fin n,
    ¬((candPredBase ws n ≤ curCostBase ws n + u.1 * n + col.1 ∧
        curCostBase ws n + u.1 * n + col.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ curCostBase ws n + u.1 * n + col.1 ∧
        curCostBase ws n + u.1 * n + col.1 < frameBExitBase ws n k + n))
  mask_bx : ∀ y : Fin n,
    ¬((candPredBase ws n ≤ frameMaskBase ws n k + y.1 ∧
        frameMaskBase ws n k + y.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ frameMaskBase ws n k + y.1 ∧
        frameMaskBase ws n k + y.1 < frameBExitBase ws n k + n))
  fp_bx : ∀ v : Fin n,
    ¬((candPredBase ws n ≤ frameParentBase ws n k + v.1 ∧
        frameParentBase ws n k + v.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ frameParentBase ws n k + v.1 ∧
        frameParentBase ws n k + v.1 < frameBExitBase ws n k + n))
  be_bx : ∀ u : Fin n,
    ¬((candPredBase ws n ≤ frameBEntryBase ws n k + u.1 ∧
        frameBEntryBase ws n k + u.1 < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ frameBEntryBase ws n k + u.1 ∧
        frameBEntryBase ws n k + u.1 < frameBExitBase ws n k + n))
  out : ∀ addr,
    ¬((ws ≤ addr ∧ addr < ws + 4 * (n * n) + 2 * n) ∨
      (frameMaskBase ws n k ≤ addr ∧ addr < frameBase ws n k + (4 * n + 1))) →
    ¬(ws ≤ addr ∧ addr < ws + 4 * (n * n)) ∧
    ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ addr ∧ addr < frameBExitBase ws n k + n)) ∧
    ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ addr ∧ addr < frameBEntryBase ws n k + n)) ∧
    ¬(frameMaskBase ws n k ≤ addr ∧ addr < frameMaskBase ws n k + n) ∧
    addr ≠ frameRepAddr ws n k
  rep_all :
    ¬(ws ≤ frameRepAddr ws n k ∧ frameRepAddr ws n k < ws + 4 * (n * n)) ∧
    ¬((candPredBase ws n ≤ frameRepAddr ws n k ∧ frameRepAddr ws n k < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ frameRepAddr ws n k ∧
        frameRepAddr ws n k < frameBExitBase ws n k + n)) ∧
    ¬((candPredBase ws n ≤ frameRepAddr ws n k ∧ frameRepAddr ws n k < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ frameRepAddr ws n k ∧
        frameRepAddr ws n k < frameBEntryBase ws n k + n)) ∧
    ¬(frameMaskBase ws n k ≤ frameRepAddr ws n k ∧
      frameRepAddr ws n k < frameMaskBase ws n k + n)
  fp_ct : ∀ v : Fin n,
    ¬(ws ≤ frameParentBase ws n k + v.1 ∧ frameParentBase ws n k + v.1 < ws + 4 * (n * n))
  ct_mask : ∀ v : Fin n,
    ¬(ws ≤ frameMaskBase ws n k + v.1 ∧ frameMaskBase ws n k + v.1 < ws + 4 * (n * n))
  ct_be : ∀ v : Fin n,
    ¬(ws ≤ frameBEntryBase ws n k + v.1 ∧ frameBEntryBase ws n k + v.1 < ws + 4 * (n * n))
  ct_bx : ∀ v : Fin n,
    ¬(ws ≤ frameBExitBase ws n k + v.1 ∧ frameBExitBase ws n k + v.1 < ws + 4 * (n * n))

/-- Unfold the workspace layout and close an address-disjointness goal with `omega`. -/
local macro "layout_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [curAdjBase, curCostBase, candPredBase, candCostBase,
    frameParentBase, frameMaskBase, frameBEntryBase, frameBExitBase, frameRepAddr, frameBase] at *
  omega))

private theorem contractRoundDisj (ws n k : ℕ) : ContractRoundDisj ws n k where
  fp_rep v := by have := v.isLt; layout_omega
  adj_rep u col := by have := List.mul_add_lt_sq u.isLt col.isLt; layout_omega
  cost_rep u col := by have := List.mul_add_lt_sq u.isLt col.isLt; layout_omega
  adj_cm u col := by have := List.mul_add_lt_sq u.isLt col.isLt; layout_omega
  cost_cm u col := by have := List.mul_add_lt_sq u.isLt col.isLt; layout_omega
  fp_cm v := by have := v.isLt; layout_omega
  adj_be u col := by have := List.mul_add_lt_sq u.isLt col.isLt; layout_omega
  cost_be u col := by have := List.mul_add_lt_sq u.isLt col.isLt; layout_omega
  mask_be y := by have := y.isLt; layout_omega
  fp_be v := by have := v.isLt; layout_omega
  adj_bx u col := by have := List.mul_add_lt_sq u.isLt col.isLt; layout_omega
  cost_bx u col := by have := List.mul_add_lt_sq u.isLt col.isLt; layout_omega
  mask_bx y := by have := y.isLt; layout_omega
  fp_bx v := by have := v.isLt; layout_omega
  be_bx u := by have := u.isLt; layout_omega
  out addr haddr := by layout_omega
  rep_all := by layout_omega
  fp_ct v := by layout_omega
  ct_mask v := by layout_omega
  ct_be v := by layout_omega
  ct_bx v := by layout_omega

private theorem matrix_mem_congr {n base : ℕ} {P : ℕ → Prop} {s₁ s₂ : Memory.State}
    {val : Fin n → Fin n → ℕ}
    (hmod : ∀ addr, ¬P addr → s₂.mem addr = s₁.mem addr)
    (hdisj : ∀ u col : Fin n, ¬P (base + u.1 * n + col.1))
    (hprev : ∀ u col : Fin n, s₁.mem (base + u.1 * n + col.1) = val u col) :
    ∀ u col : Fin n, s₂.mem (base + u.1 * n + col.1) = val u col := fun u col =>
  (hmod _ (hdisj u col)).trans (hprev u col)

private theorem vec_mem_congr {n base : ℕ} {P : ℕ → Prop} {s₁ s₂ : Memory.State}
    {val : Fin n → ℕ}
    (hmod : ∀ addr, ¬P addr → s₂.mem addr = s₁.mem addr)
    (hdisj : ∀ x : Fin n, ¬P (base + x.1))
    (hprev : ∀ x : Fin n, s₁.mem (base + x.1) = val x) :
    ∀ x : Fin n, s₂.mem (base + x.1) = val x := fun x =>
  (hmod _ (hdisj x)).trans (hprev x)

private theorem contractRoundBodyProg_spec {w n ws k B_k : ℕ} (r x0 : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha : ∀ u col : Fin n,
      s₀.mem (curAdjBase ws n + u.1 * n + col.1) = if a[u.1][col.1] then 1 else 0)
    (hc : ∀ u col : Fin n,
      s₀.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c[u.1][col.1])
    (hfp : ∀ v : Fin n, s₀.mem (frameParentBase ws n k + v.1) = (f[v.1]).1)
    (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) :
    let ca : ContractArgs := ⟨n, r.1, x0.1, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (contractRoundBodyProg ca)
    let inCycle := cycleMask f x0
    let bEntry := bestEntryTable a c inCycle
    let bExit := reducedBestExitTable a c f inCycle
    let a' := contractAdjTable a inCycle bEntry bExit x0 r
    let c' := contractReducedCostTable a c f inCycle bEntry bExit x0
    ContractRoundBodySafe w ca s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (contractRoundBodyProg ca)) ∧
      memoryCost (contractRoundBodyProg ca) s₀ ≤ 36 * (n * n) + 8 * n + 1 ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬((ws ≤ addr ∧ addr < ws + 4 * (n * n) + 2 * n) ∨
        (frameMaskBase ws n k ≤ addr ∧ addr < frameBase ws n k + (4 * n + 1))) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ u col : Fin n,
        s'.mem (curAdjBase ws n + u.1 * n + col.1) = if a'[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n,
        s'.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c'[u.1][col.1]) ∧
      FrameStored ws n k ⟨f, inCycle, bEntry, bExit, x0⟩ s' := by
  let ca : ContractArgs := ⟨n, r.1, x0.1, ws, k⟩
  have hd := contractRoundDisj ws n k
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hfr_le := frame_le_frames hk
  have hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.1][col.1]) := by
    intro u col
    have hb := hB u col
    unfold Signed.encode
    exact hfit_diff.of_le (by split_ifs <;> linarith only [hb])
  have hrep_lt_fr : frameRepAddr ws n k < s₀.frontier := by
    dsimp only [wsSize, frameRepAddr, frameBase] at hf ⊢; linarith only [hf, hfr_le]
  have hx0_fit : Fits w x0.1 := hws.of_le (by have := x0.isLt; dsimp only [wsSize]; omega)
  let s0 : Memory.State := ⟨Function.update s₀.mem (frameRepAddr ws n k) x0.1, s₀.frontier⟩
  have hs0_mod : ∀ addr, ¬(addr = frameRepAddr ws n k) → s0.mem addr = s₀.mem addr :=
    fun _ hne => Function.update_of_ne hne _ _
  have hfp0 := vec_mem_congr hs0_mod hd.fp_rep hfp
  have ha0 := matrix_mem_congr hs0_mod hd.adj_rep ha
  have hc0 := matrix_mem_congr hs0_mod hd.cost_rep hc
  have hcm := cycleMaskProg_spec (parentBase := frameParentBase ws n k)
    (maskBase := frameMaskBase ws n k) f x0 s0 h1
    (hws.of_le (by dsimp only [wsSize, frameParentBase, frameBase]; linarith only [hfr_le]))
    (hws.of_le (by dsimp only [wsSize, frameMaskBase, frameBase]; linarith only [hfr_le]))
    (hws.of_le (by dsimp only [wsSize]; omega))
    (by dsimp only [s0, wsSize, frameParentBase, frameBase] at hf ⊢; linarith only [hf, hfr_le])
    (by dsimp only [s0, wsSize, frameMaskBase, frameBase] at hf ⊢; linarith only [hf, hfr_le])
    (Or.inl (by dsimp only [frameParentBase, frameMaskBase, frameBase]; omega))
    hfp0
  let cmArgs : CycleMaskArgs := ⟨n, frameParentBase ws n k, frameMaskBase ws n k, x0.1⟩
  dsimp only at hcm
  generalize hs1 : (Memory.spec 0).clientState s0 (cycleMaskProg cmArgs) = s1 at hcm
  generalize hinC : cycleMask f x0 = inCycle at hcm
  have hs1_fr : s1.frontier = s₀.frontier := hcm.2.2.2.1
  have ha1 := matrix_mem_congr hcm.2.2.2.2.1 hd.adj_cm ha0
  have hc1 := matrix_mem_congr hcm.2.2.2.2.1 hd.cost_cm hc0
  have hfp1 := vec_mem_congr hcm.2.2.2.2.1 hd.fp_cm hfp0
  have hm1 := hcm.2.2.2.2.2
  have hbe := bestEntryProg_spec r.pos a c inCycle s1 hk hws
    (by rw [hs1_fr]; exact hf) ha1 hc1 hm1 hfit_c
  let lvArgs : LevelArgs := ⟨n, ws, k⟩
  dsimp only at hbe
  generalize hs2 : (Memory.spec 0).clientState s1 (bestEntryProg lvArgs) = s2 at hbe
  generalize hbEn : bestEntryTable a c inCycle = bEntry at hbe
  have hs2_fr : s2.frontier = s₀.frontier := hbe.2.2.2.1.trans hs1_fr
  have ha2 := matrix_mem_congr hbe.2.2.2.2.1 hd.adj_be ha1
  have hc2 := matrix_mem_congr hbe.2.2.2.2.1 hd.cost_be hc1
  have hm2 := vec_mem_congr hbe.2.2.2.2.1 hd.mask_be hm1
  have hfp2 := vec_mem_congr hbe.2.2.2.2.1 hd.fp_be hfp1
  have hbx := bestExitProg_spec r.pos a c f inCycle
    s2 hk hws (by rw [hs2_fr]; exact hf) hfit_diff ha2 hc2 hm2 hfp2 hB
  dsimp only at hbx
  generalize hs3 : (Memory.spec 0).clientState s2 (bestExitProg lvArgs) = s3 at hbx
  generalize hbEx : reducedBestExitTable a c f inCycle = bExit at hbx
  have hs3_fr : s3.frontier = s₀.frontier := hbx.2.2.2.1.trans hs2_fr
  have ha3 := matrix_mem_congr hbx.2.2.2.2.1 hd.adj_bx ha2
  have hc3 := matrix_mem_congr hbx.2.2.2.2.1 hd.cost_bx hc2
  have hm3 := vec_mem_congr hbx.2.2.2.2.1 hd.mask_bx hm2
  have hfp3 := vec_mem_congr hbx.2.2.2.2.1 hd.fp_bx hfp2
  have hbe3 := vec_mem_congr hbx.2.2.2.2.1 hd.be_bx hbe.2.2.2.2.2
  have hct := contractTablesProg_spec r x0 a c f inCycle bEntry bExit s3
    hk hws (by rw [hs3_fr]; exact hf) hfit_diff ha3 hc3 hm3 hfp3 hbe3 hbx.2.2.2.2.2 hB
  dsimp only at hct
  generalize hs4 : (Memory.spec 0).clientState s3 (contractTablesProg ca) = s4 at hct
  have hs4_fr : s4.frontier = s₀.frontier := hct.2.2.2.1.trans hs3_fr
  have hs4_mod : ∀ addr,
      ¬((ws ≤ addr ∧ addr < ws + 4 * (n * n) + 2 * n) ∨
        (frameMaskBase ws n k ≤ addr ∧ addr < frameBase ws n k + (4 * n + 1))) →
      s4.mem addr = s₀.mem addr := fun addr haddr => by
    obtain ⟨hd1, hd2, hd3, hd4, hd5⟩ := hd.out addr haddr
    rw [hct.2.2.2.2.1 addr hd1, hbx.2.2.2.2.1 addr hd2, hbe.2.2.2.2.1 addr hd3,
      hcm.2.2.2.2.1 addr hd4]
    exact Function.update_of_ne hd5 _ _
  have hs4_frame : FrameStored ws n k ⟨f, inCycle, bEntry, bExit, x0⟩ s4 := by
    refine ⟨?_, vec_mem_congr hct.2.2.2.2.1 hd.fp_ct hfp3,
      vec_mem_congr hct.2.2.2.2.1 hd.ct_mask hm3,
      vec_mem_congr hct.2.2.2.2.1 hd.ct_be hbe3,
      vec_mem_congr hct.2.2.2.2.1 hd.ct_bx hbx.2.2.2.2.2⟩
    obtain ⟨hr1, hr2, hr3, hr4⟩ := hd.rep_all
    rw [hct.2.2.2.2.1 _ hr1, hbx.2.2.2.2.1 _ hr2, hbe.2.2.2.2.1 _ hr3, hcm.2.2.2.2.1 _ hr4]
    exact Function.update_self _ _ _
  have hst_eq : (Memory.spec 0).clientState s₀ (contractRoundBodyProg ca) = s4 := by
    unfold contractRoundBodyProg
    dsimp only [ca]
    rw [StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s0
      (cycleMaskProg cmArgs >>= fun _ => bestEntryProg lvArgs >>= fun _ =>
        bestExitProg lvArgs >>= fun _ => contractTablesProg ca) = s4
    rw [StateTransitionSpec.clientState_bind, hs1,
      StateTransitionSpec.clientState_bind, hs2,
      StateTransitionSpec.clientState_bind, hs3, hs4]
  subst hbEx hbEn hinC
  refine ⟨?_, ?_, ?_, hst_eq ▸ hs4_fr, fun addr haddr => hst_eq ▸ hs4_mod addr haddr,
    fun u col => hst_eq ▸ hct.2.2.2.2.2.1 u col,
    fun u col => hst_eq ▸ hct.2.2.2.2.2.2 u col,
    hst_eq ▸ hs4_frame⟩
  · subst hs4 hs3 hs2 hs1
    exact ⟨hk, hws, hcm.1.1, hcm.1.2, hbe.1, hbx.1, hct.1.1, hct.1.2⟩
  · subst hs4 hs3 hs2 hs1
    unfold contractRoundBodyProg
    dsimp only [ca]
    exact validHistory_write_bind hrep_lt_fr hx0_fit
      (validHistory_bind_step hcm.2.1
        (validHistory_bind_step hbe.2.1
          (validHistory_bind_step hbx.2.1 hct.2.1)))
  · have c1 := hcm.2.2.1
    have c2 := hbe.2.2.1
    have c3 := hbx.2.2.1
    have c4 := hct.2.2.1
    unfold contractRoundBodyProg
    dsimp only [ca]
    rw [memoryCost_bind', memoryCost_write]
    change 1 + memoryCost
      (cycleMaskProg cmArgs >>= fun _ => bestEntryProg lvArgs >>= fun _ =>
        bestExitProg lvArgs >>= fun _ => contractTablesProg ca) s0 ≤ _
    rw [memoryCost_bind', hs1, memoryCost_bind', hs2, memoryCost_bind', hs3]
    dsimp only [cmArgs, lvArgs, ca] at c1 c2 c3 c4 ⊢
    nlinarith only [c1, c2, c3, c4]

private theorem backwardProg_spec {w n ws depth : ℕ} (hpos : 0 < n)
    (frs : List (LevelFrame n)) (q₀ : ParentTable n) (s₀ : Memory.State)
    (hdepth_le : depth ≤ n) (hlen : frs.length = depth)
    (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hcur : ∀ v : Fin n, s₀.mem (curParentBase ws n + v.1) = (q₀[v.1]).1)
    (hfrs : ∀ k (hk : k < frs.length), FrameStored ws n k frs[k] s₀) :
    let ba : BackwardArgs := ⟨n, ws, depth⟩
    let s' := (Memory.spec 0).clientState s₀ (backwardProg ba)
    let pFinal := expandFrames frs q₀
    iterationSafe backwardStep BackwardStepSafe w ba depth 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (backwardProg ba)) ∧
      memoryCost (backwardProg ba) s₀ ≤ (7 * n + 4) * depth ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(curParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ v : Fin n, s'.mem (curParentBase ws n + v.1) = (pFinal[v.1]).1) := by
  let ba : BackwardArgs := ⟨n, ws, depth⟩
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith only [hf, hpos]
  have h := iterate_spec backwardStep BackwardStepSafe w ba (7 * n + 4) depth
    (fun j idx s =>
      idx = j ∧ s.frontier = s₀.frontier ∧
        (∀ k (hk : k < frs.length), FrameStored ws n k frs[k] s) ∧
        (∀ v : Fin n,
          s.mem (curParentBase ws n + v.1) = ((expandFrames (frs.drop (depth - j)) q₀)[v.1]).1))
    (fun addr => curParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n)
    (fun j hj idx s ⟨hidx, hfr, hfrs_s, hcur_s⟩ => by
      subst idx
      set k := depth - (j + 1)
      have hk_d : k < depth := by omega
      have hk_n : k < n := lt_of_lt_of_le hk_d hdepth_le
      have hk_len : k < frs.length := hlen ▸ hk_d
      have hstored := hfrs_s k hk_len
      set fr := frs[k]
      set q_j := expandFrames (frs.drop (depth - j)) q₀
      have hexp := expandLevelProg_spec fr.x0 fr.parents q_j fr.inCycle fr.bEntry fr.bExit s
        hk_n hws (by rw [hfr]; exact hf) hstored.1 hcur_s hstored.2.1 hstored.2.2.1
        hstored.2.2.2.1 hstored.2.2.2.2
      have hdrop_eq : frs.drop k = fr :: frs.drop (depth - j) := by
        have h1 : depth - j = k + 1 := by omega
        rw [h1, ← List.cons_getElem_drop_succ (h := hk_len)]
      refine ⟨by dsimp only [BackwardStepSafe, ba]; exact ⟨by omega,
          hws.of_le (by dsimp only [wsSize]; omega), hexp.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold backwardStep
        dsimp only [ba]
        exact validHistory_read_bind (by omega)
          (validHistory_bind_step hexp.2.1 (validHistory_pure w _ _))
      · unfold backwardStep
        dsimp only [ba]
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
        have hc_e : memoryCost (expandLevelProg ⟨n, ws, k⟩) s ≤ 7 * n + 3 := hexp.2.2.1
        dsimp only [k] at hc_e
        simp only [client_simps]
        omega
      · unfold backwardStep
        dsimp only [ba]
        have hexp_fr := hexp.2.2.2.1
        dsimp only [k] at hexp_fr ⊢
        simp [client_simps, hexp_fr, hfr]
      · intro addr haddr
        unfold backwardStep
        dsimp only [ba]
        have hexp_mod := hexp.2.2.2.2.1
        dsimp only [k] at hexp_mod ⊢
        simp only [client_simps]
        exact hexp_mod addr haddr
      · unfold backwardStep
        dsimp only [ba]
        have hexp_fr := hexp.2.2.2.1
        have hexp_mod := hexp.2.2.2.2.1
        have hexp_val := hexp.2.2.2.2.2
        dsimp only [k] at hexp_fr hexp_mod hexp_val ⊢
        simp only [client_simps]
        refine ⟨trivial, hexp_fr.trans hfr, ?_, ?_⟩
        · intro m hm
          exact frameStored_congr (hfrs_s m hm) fun addr hlo hhi =>
            hexp_mod addr (by
              dsimp only [curParentBase, nextParentBase, frameBase] at hlo ⊢; omega)
        · intro v
          change ((Memory.spec 0).clientState s (expandLevelProg ⟨n, ws, depth - (j + 1)⟩)).mem
            (curParentBase ws n + v.1) = ((expandFrames (frs.drop (depth - (j + 1))) q₀)[v.1]).1
          rw [show depth - (j + 1) = k from rfl, hdrop_eq]
          exact hexp_val v)
    0 s₀ ⟨rfl, rfl, hfrs, fun v => by
      have hdrop_all : frs.drop depth = [] := by simp [hlen]
      simpa [hdrop_all, expandFrames] using hcur v⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, hcur_end⟩ := h
  unfold backwardProg
  refine ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun v => ?_⟩
  simpa [Nat.sub_self] using hcur_end v

private theorem forwardStep_contract_math {n k M₀ : ℕ} {r x0 : Fin n}
    {a₀ a_k : AdjTable n} {c₀ cUnred cRed : CostTable ℤ n} {frs : List (LevelFrame n)}
    (hk : k < n) (hpot : RowPotEq a_k cUnred cRed)
    (heq_aux : edmondsTableAux r n a₀ c₀ =
      (edmondsTableAux r (n - k) a_k cUnred).map (expandFrames frs))
    (hfeas_b : (selectParents a_k cRed r).feasible = true)
    (hcyc_case : findCycleTable r (selectParents a_k cRed r).parents = some x0)
    (hbnd_k : ∀ u col : Fin n, -(M₀ : ℤ) ≤ cRed[u.1][col.1] ∧
      cRed[u.1][col.1] ≤ (k + 1 : ℤ) * M₀) :
    let f_k := (selectParents a_k cRed r).parents
    let inCycle := cycleMask f_k x0
    let bEntry := bestEntryTable a_k cRed inCycle
    let bExit := reducedBestExitTable a_k cRed f_k inCycle
    let other := otherCycleCost cUnred f_k inCycle
    let a' := contractAdjTable a_k inCycle bEntry bExit x0 r
    let cUnred' := contractCostTable cUnred inCycle other bEntry bExit x0
    let cRed' := contractReducedCostTable a_k cRed f_k inCycle bEntry bExit x0
    let newFr : LevelFrame n := ⟨f_k, inCycle, bEntry, bExit, x0⟩
    RowPotEq a' cUnred' cRed' ∧
      edmondsTableAux r n a₀ c₀ =
        (edmondsTableAux r (n - (k + 1)) a' cUnred').map (expandFrames (frs ++ [newFr])) ∧
      ∀ u col : Fin n, -(M₀ : ℤ) ≤ cRed'[u.1][col.1] ∧
        cRed'[u.1][col.1] ≤ ((k + 1 : ℕ) + 1 : ℤ) * M₀ := by
  have hsel_eq_unred : selectParents a_k cRed r = selectParents a_k cUnred r :=
    selectParents_of_rowPotEq r hpot
  obtain ⟨hfr_root, hfeas_v⟩ := selectParents_feasible_spec a_k cRed r hfeas_b
  obtain ⟨hx0_in, hnot_r⟩ :=
    not_inCycle_root r (selectParents a_k cRed r).parents hfr_root hcyc_case
  let f_k := (selectParents a_k cRed r).parents
  let inCycle := cycleMask f_k x0
  have hact : ∀ x : Fin n, inCycle[x.1] = true → a_k[x.1][f_k[x.1].1] = true :=
    fun x hx => (hfeas_v x (hnot_r x hx)).1
  have hopt : ∀ x : Fin n, inCycle[x.1] = true →
      ∀ w : Fin n, a_k[x.1][w.1] = true → w ≠ x → cRed[x.1][f_k[x.1].1] ≤ cRed[x.1][w.1] :=
    fun x hx => (hfeas_v x (hnot_r x hx)).2.2
  have hbe_eq : bestEntryTable a_k cRed inCycle = bestEntryTable a_k cUnred inCycle :=
    bestEntryTable_of_rowPotEq inCycle hpot
  have hbx_eq : reducedBestExitTable a_k cRed f_k inCycle =
      bestExitTable a_k cUnred inCycle (otherCycleCost cUnred f_k inCycle) :=
    reducedBestExitTable_eq_bestExitTable hpot hact
  have hfuel_eq : n - k = (n - (k + 1)) + 1 := by omega
  refine ⟨rowPotEq_contractReduced hpot hx0_in hact, ?_, fun u col => ?_⟩
  · rw [heq_aux, hfuel_eq]
    dsimp only [f_k, inCycle] at hbe_eq hbx_eq ⊢
    simp only [edmondsTableAux, ← hsel_eq_unred, hfeas_b, ↓reduceIte, hcyc_case, ← hbe_eq,
      ← hbx_eq, Option.map_map]
    congr 1
    funext q
    exact (expandFrames_append_singleton frs ⟨(selectParents a_k cRed r).parents,
      cycleMask (selectParents a_k cRed r).parents x0,
      bestEntryTable a_k cRed (cycleMask (selectParents a_k cRed r).parents x0),
      reducedBestExitTable a_k cRed (selectParents a_k cRed r).parents
        (cycleMask (selectParents a_k cRed r).parents x0), x0⟩ q).symm
  · have hb := contractReducedCostTable_bounds (bEntry := bestEntryTable a_k cRed inCycle)
      (x0 := x0) hbnd_k hopt u col
    exact ⟨hb.1, by push_cast; linarith only [hb.2]⟩

private theorem forwardProg_spec {w n ws M₀ : ℕ} (r : Fin n)
    (a₀ : AdjTable n) (c₀ : CostTable ℤ n) (s₀ : Memory.State)
    (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hwb : Fits w (wordBound n M₀))
    (ha₀ : ∀ u col : Fin n,
      s₀.mem (curAdjBase ws n + u.1 * n + col.1) = if a₀[u.1][col.1] then 1 else 0)
    (hc₀ : ∀ u col : Fin n,
      s₀.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c₀[u.1][col.1])
    (hB₀ : ∀ u col : Fin n, (c₀[u.1][col.1]).natAbs ≤ M₀) :
    let ca : CoreArgs := ⟨n, r.1, ws⟩
    let res := (Memory.spec 0).clientResult s₀ (forwardProg ca)
    let s1 := (Memory.spec 0).clientState s₀ (forwardProg ca)
    iterationSafe forwardStep ForwardStepSafe w ca n ⟨0, 0, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (forwardProg ca)) ∧
      memoryCost (forwardProg ca) s₀ ≤ (43 * (n * n) + 11 * n + 2) * n ∧
      s1.frontier = s₀.frontier ∧
      (∀ addr, ¬(ws ≤ addr ∧ addr < ws + wsSize n) → s1.mem addr = s₀.mem addr) ∧
      ((res.status = 1 ∧ res.depth ≤ n ∧
          ∃ (frs : List (LevelFrame n)) (q₀ : ParentTable n),
            frs.length = res.depth ∧
            edmondsTableAux r n a₀ c₀ = some (expandFrames frs q₀) ∧
            (∀ v : Fin n, s1.mem (curParentBase ws n + v.1) = (q₀[v.1]).1) ∧
            (∀ j (hj : j < frs.length), FrameStored ws n j frs[j] s1)) ∨
        (res.status ≠ 1 ∧ edmondsTableAux r n a₀ c₀ = none)) := by
  let ca : CoreArgs := ⟨n, r.1, ws⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hf_pos : 0 < s₀.frontier := by
    have hr_pos := r.pos
    dsimp only [wsSize] at hf
    nlinarith only [hf, hr_pos]
  have hdiff_fit : ∀ k < n, Fits w (4 * ((k + 1) * M₀) + 2) := by
    intro k hk
    have hmul : (k + 1) * M₀ ≤ (n + 1) * M₀ := Nat.mul_le_mul_right M₀ (by omega)
    have hsq1 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow 2 (n + 1) (Nat.succ_pos n)
    exact hwb.of_le (by dsimp only [wordBound]; linarith only [hmul, hsq1])
  have h := iterate_spec forwardStep ForwardStepSafe w ca (43 * (n * n) + 11 * n + 2) n
    (fun k st s =>
      st.k = k ∧ s.frontier = s₀.frontier ∧
        ((st.status = 0 ∧ st.depth = k ∧
            ∃ (a_k : AdjTable n) (cUnred cRed : CostTable ℤ n) (frs : List (LevelFrame n)),
              frs.length = k ∧
              RowPotEq a_k cUnred cRed ∧
              edmondsTableAux r n a₀ c₀ =
                (edmondsTableAux r (n - k) a_k cUnred).map (expandFrames frs) ∧
              (∀ u col : Fin n,
                s.mem (curAdjBase ws n + u.1 * n + col.1) = if a_k[u.1][col.1] then 1 else 0) ∧
              (∀ u col : Fin n,
                s.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode cRed[u.1][col.1]) ∧
              (∀ u col : Fin n,
                -(M₀ : ℤ) ≤ cRed[u.1][col.1] ∧ cRed[u.1][col.1] ≤ (k + 1 : ℤ) * M₀) ∧
              (∀ j (hj : j < frs.length), FrameStored ws n j frs[j] s)) ∨
          (st.status = 1 ∧ st.depth ≤ k ∧
            ∃ (frs : List (LevelFrame n)) (q₀ : ParentTable n),
              frs.length = st.depth ∧
              edmondsTableAux r n a₀ c₀ = some (expandFrames frs q₀) ∧
              (∀ v : Fin n, s.mem (curParentBase ws n + v.1) = (q₀[v.1]).1) ∧
              (∀ j (hj : j < frs.length), FrameStored ws n j frs[j] s)) ∨
          (st.status = 2 ∧ edmondsTableAux r n a₀ c₀ = none)))
    (fun addr => ws ≤ addr ∧ addr < ws + wsSize n)
    (fun k hk st s ⟨hst_k, hfr, hbranch⟩ => by
      rcases st with ⟨kIdx, status, depth⟩
      dsimp only at hst_k hbranch
      subst kIdx
      have hf_s : ws + wsSize n ≤ s.frontier := by rw [hfr]; exact hf
      have hf_s_pos : 0 < s.frontier := by rw [hfr]; exact hf_pos
      rcases hbranch with
          ⟨hst0, hdep, a_k, cUnred, cRed, frs, hlen, hpot, heq_aux, ha_k, hc_k, hbnd_k, hfrs_k⟩ |
          hrest
      · subst status depth
        have hfr_le_k := frame_le_frames hk
        have hfit_diff := hdiff_fit k hk
        have hfuel_eq : n - k = (n - (k + 1)) + 1 := by omega
        have hmul (j : ℕ) (hj : j < frs.length) :
            j * (4 * n + 1) + (4 * n + 1) ≤ k * (4 * n + 1) := by
          simpa [Nat.succ_mul] using Nat.mul_le_mul_right (4 * n + 1) (hlen ▸ hj : j < k)
        have hB_k : ∀ u col : Fin n, (cRed[u.1][col.1]).natAbs ≤ (k + 1) * M₀ := fun u col => by
          have h := hbnd_k u col
          have : (M₀ : ℤ) ≤ (k + 1 : ℤ) * M₀ := by nlinarith
          zify; rw [abs_le]; constructor <;> linarith
        have hsel := selectParentsProg_spec r a_k cRed s hk hws hf_s ha_k hc_k fun u col =>
          hfit_diff.of_le (by have := hB_k u col; unfold Signed.encode; split_ifs <;> omega)
        dsimp only at hsel
        obtain ⟨⟨-, hsel_safe⟩, hsel_vh, hsel_mc, hsel_fr, hsel_mod, hsel_res, hsel_par⟩ := hsel
        generalize hsSel : (Memory.spec 0).clientState s (selectParentsProg ⟨n, r.1, ws, k⟩) = sSel
          at hsel_fr hsel_mod hsel_par
        rw [hfr] at hsel_fr
        have hsel_eq_unred : selectParents a_k cRed r = selectParents a_k cUnred r :=
          selectParents_of_rowPotEq r hpot
        set sel := selectParents a_k cRed r
        have hf_sSel : ws + wsSize n ≤ sSel.frontier := hsel_fr ▸ hf
        have hsel_out (x : ℕ) (hx : ¬(ws ≤ x ∧ x < ws + wsSize n)) : sSel.mem x = s.mem x :=
          hsel_mod x (by
            dsimp only [wsSize, candPredBase, candCostBase, frameParentBase, frameBase] at hx ⊢
            omega)
        have ha_sel := matrix_mem_congr hsel_mod (fun u col => by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curAdjBase, candPredBase, candCostBase, frameParentBase, frameBase]
          omega) ha_k
        have hc_sel := matrix_mem_congr hsel_mod (fun u col => by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curCostBase, candPredBase, candCostBase, frameParentBase, frameBase]
          omega) hc_k
        have hfrs_sel (j : ℕ) (hj : j < frs.length) : FrameStored ws n j frs[j] sSel :=
          frameStored_congr (hfrs_k j hj) fun addr hlo hhi => hsel_mod addr (by
            have := hmul j hj
            dsimp only [candPredBase, candCostBase, frameParentBase, frameBase] at hlo hhi ⊢
            omega)
        obtain ⟨hfc_safe, hfc_vh, hfc_mc, hfc_st, hfc_res⟩ :=
          findCycleProg_spec r sel.parents sSel h1
            (hws.of_le (by
              dsimp only [wsSize, frameParentBase, frameBase]; linarith only [hfr_le_k]))
            (hws.of_le (by dsimp only [wsSize]; omega)) (by rw [hsel_fr]; exact hf_pos)
            (by dsimp only [wsSize, frameParentBase, frameBase] at hf_sSel ⊢;
                linarith only [hf_sSel, hfr_le_k])
            hsel_par
        have hsSel' := hsSel
        have hfc_st' := hfc_st
        simp only [StateTransitionSpec.clientState] at hsSel' hfc_st'
        cases hfeas_b : sel.feasible
        · have hres_sel :
              (Memory.spec 0).clientResult s (selectParentsProg ⟨n, r.1, ws, k⟩) = 0 := by
            simp only [hsel_res, hfeas_b, Bool.false_eq_true, ↓reduceIte]
          refine ⟨⟨hk, hws, fun _ => ⟨hsel_safe, fun h => absurd hres_sel h⟩⟩,
            validHistory_read_bind hf_s_pos (validHistory_bind_step hsel_vh ?_), ?_⟩
          · rw [hsSel, hres_sel, ite_eq_left rfl]
            exact validHistory_pure w _ _
          simp only [forwardStep, ca, client_simps, hsSel', hres_sel, ↓reduceIte]
          refine ⟨by nlinarith only [hsel_mc], hsel_fr.trans hfr.symm, hsel_out, trivial, hsel_fr,
            Or.inr (Or.inr ⟨trivial, ?_⟩)⟩
          rw [heq_aux, hfuel_eq]
          simp [edmondsTableAux, ← hsel_eq_unred, hfeas_b]
        have hres_sel : (Memory.spec 0).clientResult s (selectParentsProg ⟨n, r.1, ws, k⟩) = 1 := by
          simp only [hsel_res, hfeas_b, ↓reduceIte]
        cases hcyc : findCycleTable r sel.parents
        · have hx0 : (Memory.spec 0).clientResult sSel
              (findCycleProg ⟨n, r.1, frameParentBase ws n k⟩) = n := by rw [hfc_res, hcyc]; rfl
          have hcp := copyWordsProg_spec
            ⟨frameParentBase ws n k, curParentBase ws n, n⟩ sSel
            (by dsimp only [wsSize, frameParentBase, frameBase] at hf_sSel ⊢;
                linarith only [hf_sSel, hfr_le_k])
            (by dsimp only [wsSize, curParentBase] at hf_sSel ⊢; omega)
            (Or.inr (by dsimp only [curParentBase, frameParentBase, frameBase]; omega))
            (hws.of_le (by
              dsimp only [wsSize, frameParentBase, frameBase]; linarith only [hfr_le_k]))
            (hws.of_le (by dsimp only [wsSize, curParentBase]; omega))
            (hws.of_le (by dsimp only [wsSize]; omega))
            (fun i hi => by
              dsimp only
              rw [hsel_par ⟨i, hi⟩]
              exact hws.of_le (by have := (sel.parents[i]).isLt; dsimp only [wsSize]; omega))
          obtain ⟨hcp_safe, hcp_vh, hcp_mc, hcp_fr, hcp_mod, hcp_val⟩ := hcp
          refine ⟨?_, validHistory_read_bind hf_s_pos (validHistory_bind_step hsel_vh ?_), ?_⟩
          · dsimp only [ForwardStepSafe, ca]
            rw [hsSel, hfc_st, hx0]
            exact ⟨hk, hws, fun _ => ⟨hsel_safe, fun _ => ⟨hfc_safe, fun _ => hcp_safe,
              fun h => absurd rfl h⟩⟩⟩
          · rw [hsSel, hres_sel, ite_eq_right one_ne_zero]
            refine validHistory_bind_step hfc_vh ?_
            rw [hfc_st, hx0, ite_eq_left rfl]
            exact validHistory_bind_step hcp_vh (validHistory_pure w _ _)
          simp only [StateTransitionSpec.clientState] at hcp_fr hcp_mod hcp_val
          simp only [forwardStep, ca, client_simps, hsSel', hres_sel, one_ne_zero, hfc_st', hx0,
            ↓reduceIte]
          refine ⟨by nlinarith only [hsel_mc, hfc_mc, hcp_mc],
            hcp_fr.trans (hsel_fr.trans hfr.symm),
            fun x hx => (hcp_mod x (by dsimp only [wsSize, curParentBase] at hx ⊢; omega)).trans
              (hsel_out x hx),
            trivial, hcp_fr.trans hsel_fr,
            Or.inr (Or.inl ⟨trivial, by omega, frs, sel.parents, hlen, ?_,
              fun v => (hcp_val v.1 v.isLt).trans (hsel_par v), fun j hj =>
                frameStored_congr (hfrs_sel j hj) fun addr hlo hhi => hcp_mod addr (by
                  dsimp only [curParentBase, frameBase] at hlo ⊢; omega)⟩)⟩
          rw [heq_aux, hfuel_eq]
          simp [edmondsTableAux, ← hsel_eq_unred, hfeas_b, hcyc]
        · rename_i x0
          have hx0 : (Memory.spec 0).clientResult sSel
              (findCycleProg ⟨n, r.1, frameParentBase ws n k⟩) = x0.1 := by rw [hfc_res, hcyc]; rfl
          have hx0_ne : x0.1 ≠ n := x0.isLt.ne
          have hcrb := contractRoundBodyProg_spec r x0 a_k cRed sel.parents sSel hk hws hf_sSel
            hfit_diff ha_sel hc_sel hsel_par hB_k
          dsimp only at hcrb
          obtain ⟨hcrb_safe, hcrb_vh, hcrb_mc, hcrb_fr, hcrb_mod, hcrb_a, hcrb_c, hcrb_frm⟩ := hcrb
          obtain ⟨hpot', heq_aux', hbnd'⟩ :=
            forwardStep_contract_math hk hpot heq_aux hfeas_b hcyc hbnd_k
          refine ⟨?_, validHistory_read_bind hf_s_pos (validHistory_bind_step hsel_vh ?_), ?_⟩
          · dsimp only [ForwardStepSafe, ca]
            rw [hsSel, hfc_st, hx0]
            exact ⟨hk, hws, fun _ => ⟨hsel_safe, fun _ => ⟨hfc_safe, fun h => absurd h hx0_ne,
              fun _ => hcrb_safe⟩⟩⟩
          · rw [hsSel, hres_sel, ite_eq_right one_ne_zero]
            refine validHistory_bind_step hfc_vh ?_
            rw [hfc_st, hx0, ite_eq_right hx0_ne]
            exact validHistory_bind_step hcrb_vh (validHistory_pure w _ _)
          simp only [StateTransitionSpec.clientState] at hcrb_fr hcrb_mod hcrb_a hcrb_c hcrb_frm
          simp only [forwardStep, ca, client_simps, hsSel', hres_sel, one_ne_zero, hfc_st', hx0,
            hx0_ne, ↓reduceIte]
          refine ⟨by nlinarith only [hsel_mc, hfc_mc, hcrb_mc],
            hcrb_fr.trans (hsel_fr.trans hfr.symm),
            fun x hx => (hcrb_mod x (by
              dsimp only [wsSize, frameMaskBase, frameBase] at hx ⊢; omega)).trans (hsel_out x hx),
            trivial, hcrb_fr.trans hsel_fr, Or.inl ⟨trivial, trivial, _, _, _, _, by simp [hlen],
              hpot', heq_aux', hcrb_a, hcrb_c, hbnd', fun j hj => ?_⟩⟩
          rw [List.length_append, List.length_singleton] at hj
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
          · rw [List.getElem_append_left hlt]
            exact frameStored_congr (hfrs_sel j hlt) fun addr hlo hhi => hcrb_mod addr (by
              have := hmul j hlt
              dsimp only [frameMaskBase, frameBase] at hlo hhi ⊢; omega)
          · simp only [List.getElem_append_right (le_refl frs.length), Nat.sub_self,
              List.getElem_singleton]
            rw [hlen]
            exact hcrb_frm
      have hst : status ≠ 0 := by rcases hrest with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      refine ⟨⟨hk, hws, fun h => absurd h hst⟩, ?_⟩
      simp only [forwardStep, hst, ↓reduceIte]
      refine ⟨validHistory_read_bind hf_s_pos (validHistory_pure w _ _), ?_⟩
      simp only [client_simps]
      exact ⟨by omega, trivial, fun _ _ => trivial, trivial, hfr,
        Or.inr (hrest.imp (fun ⟨h1, hd, h⟩ => ⟨h1, by omega, h⟩) id)⟩)
    ⟨0, 0, 0⟩ s₀ ⟨rfl, rfl, Or.inl ⟨rfl, rfl, a₀, c₀, c₀, [], rfl,
      ⟨fun _ => 0, fun _ _ _ => by simp⟩,
      by simp [expandFrames], ha₀, hc₀,
      fun u col => by have := hB₀ u col; omega,
      fun _ hj => absurd hj (Nat.not_lt_zero _)⟩⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, hcases⟩ := h
  unfold forwardProg
  refine ⟨hsafe, hvh, hmc, hfr_e, hmod_e, ?_⟩
  rcases hcases with ⟨hst0, _, a_n, cUnred, cRed, frs, _, _, heq_aux, _⟩ | hst1 | ⟨hst2, hnone⟩
  · refine Or.inr ⟨by dsimp only [ca] at hst0 ⊢; omega, ?_⟩
    simpa [Nat.sub_self, edmondsTableAux] using heq_aux
  · exact Or.inl hst1
  · exact Or.inr ⟨by dsimp only [ca] at hst2 ⊢; omega, hnone⟩

public theorem edmondsCoreProg_spec {w n ws M₀ : ℕ} (r : Fin n)
    (a₀ : AdjTable n) (c₀ : CostTable ℤ n) (s₀ : Memory.State)
    (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hwb : Fits w (wordBound n M₀))
    (ha₀ : ∀ u col : Fin n,
      s₀.mem (curAdjBase ws n + u.1 * n + col.1) = if a₀[u.1][col.1] then 1 else 0)
    (hc₀ : ∀ u col : Fin n,
      s₀.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c₀[u.1][col.1])
    (hB₀ : ∀ u col : Fin n, (c₀[u.1][col.1]).natAbs ≤ M₀) :
    let ca : CoreArgs := ⟨n, r.1, ws⟩
    let res := (Memory.spec 0).clientResult s₀ (forwardProg ca)
    let s1 := (Memory.spec 0).clientState s₀ (forwardProg ca)
    let s' := (Memory.spec 0).clientState s₀ (edmondsCoreProg ca)
    let status := (Memory.spec 0).clientResult s₀ (edmondsCoreProg ca)
    (Fits w 1 ∧
      iterationSafe forwardStep ForwardStepSafe w ca n ⟨0, 0, 0⟩ s₀ ∧
      (res.status = 1 →
        iterationSafe backwardStep BackwardStepSafe w ⟨n, ws, res.depth⟩ res.depth 0 s1)) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (edmondsCoreProg ca)) ∧
      memoryCost (edmondsCoreProg ca) s₀ ≤ 43 * n ^ 3 + 18 * n ^ 2 + 6 * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(ws ≤ addr ∧ addr < ws + wsSize n) → s'.mem addr = s₀.mem addr) ∧
      match edmondsTableAux r n a₀ c₀ with
      | some p =>
        status = 1 ∧ ∀ v : Fin n, s'.mem (curParentBase ws n + v.1) = (p[v.1]).1
      | none =>
        status = 0 := by
  let ca : CoreArgs := ⟨n, r.1, ws⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hfwd := forwardProg_spec r a₀ c₀ s₀ hws hf hwb ha₀ hc₀ hB₀
  set res := (Memory.spec 0).clientResult s₀ (forwardProg ⟨n, r.1, ws⟩)
  set s1 := (Memory.spec 0).clientState s₀ (forwardProg ⟨n, r.1, ws⟩)
  have hf_s1 : ws + wsSize n ≤ s1.frontier := by rw [hfwd.2.2.2.1]; exact hf
  rcases hfwd.2.2.2.2.2 with ⟨hst1, hdep_le, frs, q₀, hlen, heq_some, hcur1, hfrs1⟩ |
      ⟨hst_ne, heq_none⟩
  · have hbwd := backwardProg_spec r.pos frs q₀ s1 hdep_le hlen hws hf_s1 hcur1 hfrs1
    unfold edmondsCoreProg
    dsimp only [ca]
    refine ⟨⟨h1, hfwd.1, fun _ => hbwd.1⟩, ?_, ?_, ?_, ?_, ?_⟩
    · refine validHistory_bind_step hfwd.2.1 ?_
      change (Memory.spec w).ValidHistory s1
        ((Memory.spec w).clientHistory s1
          (if res.status = 1 then backwardProg ⟨n, ws, res.depth⟩ >>= fun _ => pure 1 else pure 0))
      rw [ite_eq_left hst1]
      exact validHistory_bind_step hbwd.2.1 (validHistory_pure w _ _)
    · rw [memoryCost_bind']
      change memoryCost (forwardProg ⟨n, r.1, ws⟩) s₀ +
        memoryCost (if res.status = 1 then backwardProg ⟨n, ws, res.depth⟩ >>= fun _ => pure 1
          else pure 0) s1 ≤ _
      rw [ite_eq_left hst1]
      simp only [memoryCost_bind', client_simps]
      have cf := hfwd.2.2.1
      have cb := hbwd.2.2.1
      have hcb_n : (7 * n + 4) * res.depth ≤ (7 * n + 4) * n := Nat.mul_le_mul_left _ hdep_le
      have hid : (43 * (n * n) + 11 * n + 2) * n + (7 * n + 4) * n =
          43 * n ^ 3 + 18 * n ^ 2 + 6 * n := by ring
      linarith only [cf, cb, hcb_n, hid]
    · simp only [client_simps, hst1, ↓reduceIte]
      exact hbwd.2.2.2.1.trans hfwd.2.2.2.1
    · intro addr haddr
      simp only [client_simps, hst1, ↓reduceIte]
      rw [hbwd.2.2.2.2.1 addr (by
        dsimp only [wsSize, curParentBase, nextParentBase] at haddr ⊢; omega)]
      exact hfwd.2.2.2.2.1 addr haddr
    · rw [heq_some]
      simp only [client_simps, hst1, ↓reduceIte]
      exact ⟨trivial, hbwd.2.2.2.2.2⟩
  · unfold edmondsCoreProg
    dsimp only [ca]
    refine ⟨⟨h1, hfwd.1, fun h => absurd h hst_ne⟩, ?_, ?_, ?_, ?_, ?_⟩
    · refine validHistory_bind_step hfwd.2.1 ?_
      change (Memory.spec w).ValidHistory s1
        ((Memory.spec w).clientHistory s1
          (if res.status = 1 then backwardProg ⟨n, ws, res.depth⟩ >>= fun _ => pure 1 else pure 0))
      rw [ite_eq_right hst_ne]
      exact validHistory_pure w _ _
    · rw [memoryCost_bind']
      change memoryCost (forwardProg ⟨n, r.1, ws⟩) s₀ +
        memoryCost (if res.status = 1 then backwardProg ⟨n, ws, res.depth⟩ >>= fun _ => pure 1
          else pure 0) s1 ≤ _
      rw [ite_eq_right hst_ne]
      simp only [client_simps]
      have cf := hfwd.2.2.1
      have hnn := Nat.zero_le ((7 * n + 4) * n)
      have hid : (43 * (n * n) + 11 * n + 2) * n + (7 * n + 4) * n =
          43 * n ^ 3 + 18 * n ^ 2 + 6 * n := by ring
      linarith only [cf, hid, hnn]
    · simp only [client_simps, hst_ne, ↓reduceIte]
      exact hfwd.2.2.2.1
    · intro addr haddr
      simp only [client_simps, hst_ne, ↓reduceIte]
      exact hfwd.2.2.2.2.1 addr haddr
    · rw [heq_none]
      simp [client_simps, hst_ne]

end Cslib.Algorithms.WordRAM.Arborescence.Internal
