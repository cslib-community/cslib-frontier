/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.CoreProg
public import CslibFrontier.Algorithms.Lean.Arborescence.Table
public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.BasicSpec

/-!
# Specification for `expandLevelProg` (internal)

Proves admissibility, `O(n)` memory cost, and exact table correspondence with `expandParentsTable`.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.Algorithms.Lean.Arborescence
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

attribute [local client_simps] StateTransitionSpec.clientState
  StateTransitionSpec.runClient_pure'
  runClient_read runClient_write runClient_allocDirty runClient_ite
  prog_clientState_ite

private theorem fillExpandRowProg_spec {w n ws k : ℕ} (x0 : Fin n)
    (f q : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hcur : ∀ v : Fin n, s₀.mem (curParentBase ws n + v.1) = (q[v.1]).1)
    (hfp : ∀ v : Fin n, s₀.mem (frameParentBase ws n k + v.1) = (f[v.1]).1)
    (hm : ∀ v : Fin n, s₀.mem (frameMaskBase ws n k + v.1) = if inCycle[v.1] then 1 else 0)
    (hbe : ∀ v : Fin n, s₀.mem (frameBEntryBase ws n k + v.1) = optFinIdx bEntry[v.1]) :
    let ra : ExpandRowArgs := ⟨n, x0.1, (q[x0.1]).1, optFinIdx bExit[(q[x0.1]).1], ws, k⟩
    let s1 := (Memory.spec 0).clientState s₀ (fillExpandRowProg ra)
    iterationSafe expandRowStep ExpandRowStepSafe w ra n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (fillExpandRowProg ra)) ∧
      memoryCost (fillExpandRowProg ra) s₀ ≤ 5 * n ∧
      s1.frontier = s₀.frontier ∧
      (∀ addr, ¬(nextParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n) →
        s1.mem addr = s₀.mem addr) ∧
      (∀ j : Fin n,
        s1.mem (nextParentBase ws n + j.1) =
          ((expandParentTable f inCycle bEntry bExit x0 q)[j.1]).1) := by
  let ra : ExpandRowArgs := ⟨n, x0.1, (q[x0.1]).1, optFinIdx bExit[(q[x0.1]).1], ws, k⟩
  have hrow := iterate_spec expandRowStep ExpandRowStepSafe w ra 5 n
    (fun m idx sr =>
      idx = m ∧ sr.frontier = s₀.frontier ∧
        (∀ v : Fin n, sr.mem (curParentBase ws n + v.1) = (q[v.1]).1) ∧
        (∀ v : Fin n, sr.mem (frameParentBase ws n k + v.1) = (f[v.1]).1) ∧
        (∀ v : Fin n, sr.mem (frameMaskBase ws n k + v.1) = if inCycle[v.1] then 1 else 0) ∧
        (∀ v : Fin n, sr.mem (frameBEntryBase ws n k + v.1) = optFinIdx bEntry[v.1]) ∧
        (∀ j : Fin n, j.1 < m → sr.mem (nextParentBase ws n + j.1) =
          ((expandParentTable f inCycle bEntry bExit x0 q)[j.1]).1))
    (fun addr => nextParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n)
    (fun m hm idx sr ⟨hidx, hfr_r, hcur_r, hfp_r, hm_r, hbe_r, hdone_r⟩ => by
      subst idx
      have hm_m : sr.mem (frameMaskBase ws n k + m) = if inCycle[m] then 1 else 0 := hm_r ⟨m, hm⟩
      have hfp_m : sr.mem (frameParentBase ws n k + m) = (f[m]).1 := hfp_r ⟨m, hm⟩
      have hcur_m : sr.mem (curParentBase ws n + m) = (q[m]).1 := hcur_r ⟨m, hm⟩
      have hbe_m : sr.mem (frameBEntryBase ws n k + m) = optFinIdx bEntry[m] := hbe_r ⟨m, hm⟩
      have hout_eq :
          (if sr.mem (frameMaskBase ws n k + m) = 1 then
            if optFinIdx bExit[(q[x0.1]).1] < n then
              if m = optFinIdx bExit[(q[x0.1]).1] then (q[x0.1]).1
              else sr.mem (frameParentBase ws n k + m)
            else sr.mem (frameParentBase ws n k + m)
          else if sr.mem (curParentBase ws n + m) = x0.1 then
            if sr.mem (frameBEntryBase ws n k + m) < n then
              sr.mem (frameBEntryBase ws n k + m)
            else m
          else sr.mem (curParentBase ws n + m)) =
            ((expandParentTable f inCycle bEntry bExit x0 q)[m]).1 := by
        rw [hm_m, hfp_m, hcur_m, hbe_m,
          show (expandParentTable f inCycle bEntry bExit x0 q)[m] =
            (expandParentTable f inCycle bEntry bExit x0 q)[(⟨m, hm⟩ : Fin n).1] from rfl,
          getElem_expandParentTable]
        dsimp only
        cases hvC : inCycle[m]
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one, beq_iff_eq, Fin.ext_iff]
          by_cases hqx : (q[m]).1 = x0.1
          · simp only [hqx, ↓reduceIte]
            cases bEntry[m] with
            | none => simp [optFinIdx]
            | some ys => simp [optFinIdx, ys.isLt]
          · simp [hqx]
        · simp only [↓reduceIte, beq_iff_eq, Fin.ext_iff]
          cases bExit[(q[x0.1]).1] with
          | none => simp [optFinIdx]
          | some xs =>
            simp only [optFinIdx, xs.isLt, ↓reduceIte]
            by_cases hmx : m = xs.1 <;> simp [hmx]
      refine ⟨by dsimp only [ExpandRowStepSafe, ra]; exact ⟨hm, hk, hws⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold expandRowStep
        dsimp only [ra]
        refine validHistory_read_bind
          (by dsimp only [wsSize, frameMaskBase, frameBase] at hf hfr_r ⊢; nlinarith)
          (validHistory_read_bind
            (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr_r ⊢; nlinarith)
            (validHistory_read_bind
              (by dsimp only [wsSize, curParentBase] at hf hfr_r ⊢; nlinarith)
              (validHistory_read_bind
                (by dsimp only [wsSize, frameBEntryBase, frameBase] at hf hfr_r ⊢; nlinarith) ?_)))
        refine validHistory_write_bind
          (by dsimp only [wsSize, nextParentBase] at hf hfr_r ⊢; nlinarith) ?_
          (validHistory_pure w _ _)
        rw [hout_eq]
        exact hws.of_le (by
          have := ((expandParentTable f inCycle bEntry bExit x0 q)[m]).isLt
          dsimp only [wsSize]; nlinarith)
      · unfold expandRowStep
        dsimp only [ra]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [expandRowStep, ra, client_simps]
      · intro addr haddr
        dsimp only [nextParentBase] at haddr
        simp only [expandRowStep, ra, client_simps, nextParentBase]
        exact Function.update_of_ne (by omega) _ _
      · unfold expandRowStep
        dsimp only [ra]
        simp only [client_simps]
        refine ⟨trivial, hfr_r, ?_, ?_, ?_, ?_, ?_⟩
        · intro v
          have := v.isLt
          rw [Function.update_of_ne (by dsimp only [curParentBase, nextParentBase]; omega)]
          exact hcur_r v
        · intro v
          have := v.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameParentBase, frameBase, nextParentBase]; omega)]
          exact hfp_r v
        · intro v
          have := v.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameMaskBase, frameBase, nextParentBase]; omega)]
          exact hm_r v
        · intro v
          have := v.isLt
          rw [Function.update_of_ne
            (by dsimp only [frameBEntryBase, frameBase, nextParentBase]; omega)]
          exact hbe_r v
        · intro j hj
          by_cases hjm : j.1 = m
          · have hj_eq : j = ⟨m, hm⟩ := Fin.ext hjm
            subst hj_eq
            dsimp only
            rw [Function.update_self]
            exact hout_eq
          · rw [Function.update_of_ne (by omega)]
            exact hdone_r j (by omega))
    0 s₀ ⟨rfl, rfl, hcur, hfp, hm, hbe, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, _, _, hdone_end⟩ := hrow
  unfold fillExpandRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun j => hdone_end j j.isLt⟩

public theorem expandLevelProg_spec {w n ws k : ℕ} (x0 : Fin n)
    (f q : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hrep : s₀.mem (frameRepAddr ws n k) = x0.1)
    (hcur : ∀ v : Fin n, s₀.mem (curParentBase ws n + v.1) = (q[v.1]).1)
    (hfp : ∀ v : Fin n, s₀.mem (frameParentBase ws n k + v.1) = (f[v.1]).1)
    (hm : ∀ v : Fin n, s₀.mem (frameMaskBase ws n k + v.1) = if inCycle[v.1] then 1 else 0)
    (hbe : ∀ v : Fin n, s₀.mem (frameBEntryBase ws n k + v.1) = optFinIdx bEntry[v.1])
    (hbx : ∀ v : Fin n, s₀.mem (frameBExitBase ws n k + v.1) = optFinIdx bExit[v.1]) :
    let la : LevelArgs := ⟨n, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (expandLevelProg la)
    let p' := expandParentTable f inCycle bEntry bExit x0 q
    ExpandLevelSafe w la s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (expandLevelProg la)) ∧
      memoryCost (expandLevelProg la) s₀ ≤ 7 * n + 3 ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(curParentBase ws n ≤ addr ∧ addr < nextParentBase ws n + n) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ v : Fin n, s'.mem (curParentBase ws n + v.1) = (p'[v.1]).1) := by
  let la : LevelArgs := ⟨n, ws, k⟩
  have hqx0 : s₀.mem (curParentBase ws n + x0.1) = (q[x0.1]).1 := hcur x0
  have hbx_qx0 : s₀.mem (frameBExitBase ws n k + (q[x0.1]).1) = optFinIdx bExit[(q[x0.1]).1] :=
    hbx q[x0.1]
  let ra : ExpandRowArgs := ⟨n, x0.1, (q[x0.1]).1, optFinIdx bExit[(q[x0.1]).1], ws, k⟩
  have hrow := fillExpandRowProg_spec x0 f q inCycle bEntry bExit s₀ hk hws hf hcur hfp hm hbe
  set s1 := (Memory.spec 0).clientState s₀ (fillExpandRowProg ra)
  let ca : CopyArgs := ⟨nextParentBase ws n, curParentBase ws n, n⟩
  have hcopy := copyWordsProg_spec ca s1
    (by dsimp only [ca, wsSize, nextParentBase] at hf ⊢; rw [hrow.2.2.2.1]; nlinarith)
    (by dsimp only [ca, wsSize, curParentBase] at hf ⊢; rw [hrow.2.2.2.1]; nlinarith)
    (Or.inr (by dsimp only [ca, curParentBase, nextParentBase]; omega))
    (hws.of_le (by dsimp only [ca, wsSize, nextParentBase]; nlinarith))
    (hws.of_le (by dsimp only [ca, wsSize, curParentBase]; nlinarith))
    (hws.of_le (by dsimp only [ca, wsSize]; nlinarith))
    (fun i hi => by
      dsimp only [ca]
      rw [hrow.2.2.2.2.2 ⟨i, hi⟩]
      exact hws.of_le (by
        have := ((expandParentTable f inCycle bEntry bExit x0 q)[i]).isLt
        dsimp only [wsSize]; nlinarith))
  have hsafe : ExpandLevelSafe w la s₀ := by
    dsimp only [ExpandLevelSafe, la]
    rw [hrep, hqx0, hbx_qx0]
    exact ⟨hk, hws, x0.isLt, (q[x0.1]).isLt, hrow.1, hcopy.1⟩
  unfold expandLevelProg
  dsimp only [la]
  refine ⟨hsafe, ?_, ?_, ?_, ?_, ?_⟩
  · refine validHistory_read_bind
      (by dsimp only [wsSize, frameRepAddr, frameBase] at hf ⊢; nlinarith) ?_
    rw [hrep]
    refine validHistory_read_bind
      (by have := x0.isLt; dsimp only [wsSize, curParentBase] at hf ⊢; nlinarith) ?_
    rw [hqx0]
    refine validHistory_read_bind
      (by have := (q[x0.1]).isLt; dsimp only [wsSize, frameBExitBase, frameBase] at hf ⊢;
          nlinarith) ?_
    rw [hbx_qx0]
    exact validHistory_bind_step hrow.2.1 hcopy.2.1
  · rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hrep,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hqx0,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read, hbx_qx0,
      memoryCost_bind']
    have hr_c : memoryCost (fillExpandRowProg ra) s₀ ≤ 5 * n := hrow.2.2.1
    have hc_c : memoryCost (copyWordsProg ca) s1 ≤ 2 * n := hcopy.2.2.1
    dsimp only [ra, ca, s1] at hr_c hc_c ⊢
    omega
  · have hcopy_fr := hcopy.2.2.2.1
    dsimp only [s1, ra] at hcopy_fr
    simp only [client_simps, hrep, hqx0, hbx_qx0]
    exact hcopy_fr.trans hrow.2.2.2.1
  · intro addr haddr
    have hcopy_mod := hcopy.2.2.2.2.1
    dsimp only [s1, ra] at hcopy_mod
    simp only [client_simps, hrep, hqx0, hbx_qx0]
    rw [hcopy_mod addr (by dsimp only [ca, curParentBase, nextParentBase] at haddr ⊢; omega)]
    exact hrow.2.2.2.2.1 addr (by dsimp only [curParentBase, nextParentBase] at haddr ⊢; omega)
  · intro v
    have hcopy_val := hcopy.2.2.2.2.2
    dsimp only [s1, ra] at hcopy_val
    simp only [client_simps, hrep, hqx0, hbx_qx0]
    rw [show curParentBase ws n + v.1 = ca.dst + v.1 from rfl, hcopy_val v.1 v.isLt]
    exact hrow.2.2.2.2.2 v

end Cslib.Algorithms.WordRAM.Arborescence.Internal
