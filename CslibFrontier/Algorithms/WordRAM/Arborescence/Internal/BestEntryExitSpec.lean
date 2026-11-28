/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.CoreProg
public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.ReducedCost
public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.BasicSpec
import CslibFrontier.Foundations.Data.List.RowMajor

/-!
# Specifications for `bestEntryProg` and `bestExitProg` (internal)

Proves admissibility, `O(n²)` memory cost, and exact table correspondence with `bestEntryTable`
and `reducedBestExitTable`.
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
  prog_clientState_ite runClient_signedSubProg

@[local client_simps] private theorem local_fst_snd_signedSubProg (w : ℕ)
    (s : Memory.State) (d : ℕ × ℕ) :
    ((Memory.spec w).runClient s (signedSubProg d)).2.1 = s :=
  clientState_signedSubProg s d

private theorem fillBestEntryRowProg_spec {w n ws k : ℕ} (uFin : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (inCycle : Vector Bool n) (s : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (ha_s : ∀ u col : Fin n, s.mem (curAdjBase ws n + u.val * n + col.val) =
      if a[u.val][col.val] then 1 else 0)
    (hc_s : ∀ u col : Fin n, s.mem (curCostBase ws n + u.val * n + col.val) =
      Signed.encode c[u.val][col.val])
    (hm_s : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.val) = if inCycle[y.val] then 1 else 0)
    (hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.val][col.val])) :
    let rowArgs : BestEntryRowArgs :=
      ⟨n, uFin.val, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
        candPredBase ws n, candCostBase ws n⟩
    let s1 := (Memory.spec 0).clientState s (fillBestEntryRowProg rowArgs)
    iterationSafe bestEntryRowStep BestEntryRowStepSafe w rowArgs n 0 s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (fillBestEntryRowProg rowArgs)) ∧
      memoryCost (fillBestEntryRowProg rowArgs) s ≤ 5 * n ∧
      s1.frontier = s.frontier ∧
      (∀ addr, ¬(candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) →
        s1.mem addr = s.mem addr) ∧
      (∀ u col : Fin n, s1.mem (curAdjBase ws n + u.val * n + col.val) =
        if a[u.val][col.val] then 1 else 0) ∧
      (∀ u col : Fin n, s1.mem (curCostBase ws n + u.val * n + col.val) =
        Signed.encode c[u.val][col.val]) ∧
      (∀ z : Fin n, s1.mem (frameMaskBase ws n k + z.val) = if inCycle[z.val] then 1 else 0) ∧
      (∀ z : Fin n,
        s1.mem (candPredBase ws n + z.val) =
          (if inCycle[z.val] && a[uFin.val][z.val] then 1 else 0) ∧
        s1.mem (candCostBase ws n + z.val) = Signed.encode c[uFin.val][z.val]) := by
  let rowArgs : BestEntryRowArgs :=
    ⟨n, uFin.val, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
      candPredBase ws n, candCostBase ws n⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hu_lt := uFin.isLt
  have hfr_le := frame_le_frames hk
  have hrow := iterate_spec bestEntryRowStep BestEntryRowStepSafe w rowArgs 5 n
    (fun y idxR sr => idxR = y ∧ sr.frontier = s.frontier ∧
      (∀ u col : Fin n, sr.mem (curAdjBase ws n + u.val * n + col.val) =
        if a[u.val][col.val] then 1 else 0) ∧
      (∀ u col : Fin n, sr.mem (curCostBase ws n + u.val * n + col.val) =
        Signed.encode c[u.val][col.val]) ∧
      (∀ z : Fin n, sr.mem (frameMaskBase ws n k + z.val) = if inCycle[z.val] then 1 else 0) ∧
      (∀ z : Fin n, z.val < y →
        sr.mem (candPredBase ws n + z.val) =
          (if inCycle[z.val] && a[uFin.val][z.val] then 1 else 0) ∧
        sr.mem (candCostBase ws n + z.val) = Signed.encode c[uFin.val][z.val]))
    (fun addr => candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n)
    (fun y hy idxR sr ⟨hidxR, hfr_r, ha_r, hc_r, hm_r, hdone_r⟩ => by
      subst idxR
      have hcell_uy := List.mul_add_lt_sq hu_lt hy
      have hm_y : sr.mem (frameMaskBase ws n k + y) = if inCycle[y] then 1 else 0 := hm_r ⟨y, hy⟩
      have ha_my : sr.mem (curAdjBase ws n + uFin.val * n + y) = if a[uFin.val][y] then 1 else 0 :=
        ha_r uFin ⟨y, hy⟩
      have hc_my : sr.mem (curCostBase ws n + uFin.val * n + y) = Signed.encode c[uFin.val][y] :=
        hc_r uFin ⟨y, hy⟩
      have hout : ∀ addr, ¬(candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) →
          ((Memory.spec 0).clientState sr (bestEntryRowStep (rowArgs, y))).mem addr =
            sr.mem addr := by
        intro addr haddr
        dsimp only [candPredBase, candCostBase] at haddr
        simp only [bestEntryRowStep, rowArgs, client_simps, candPredBase, candCostBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      refine ⟨by dsimp only [BestEntryRowStepSafe, rowArgs]; exact ⟨h1,
          hws.of_le (by dsimp only [wsSize, frameMaskBase, frameBase]; omega),
          hws.of_le (by dsimp only [wsSize, curAdjBase]; omega),
          hws.of_le (by dsimp only [wsSize, curCostBase]; omega),
          hws.of_le (by dsimp only [wsSize, candPredBase]; omega),
          hws.of_le (by dsimp only [wsSize, candCostBase]; omega),
          hws.of_le (by dsimp only [wsSize]; omega)⟩,
        ?_, ?_, by simp [bestEntryRowStep, rowArgs, client_simps], hout,
        by simp [bestEntryRowStep, rowArgs, client_simps],
        by simpa [bestEntryRowStep, rowArgs, client_simps] using hfr_r,
        fun u col => (hout _ (by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curAdjBase, candPredBase, candCostBase]; omega)).trans (ha_r u col),
        fun u col => (hout _ (by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curCostBase, candPredBase, candCostBase]; omega)).trans (hc_r u col),
        fun z => (hout _ (by
          have := z.isLt
          dsimp only [frameMaskBase, frameBase, candPredBase, candCostBase]; omega)).trans (hm_r z),
        ?_⟩
      · unfold bestEntryRowStep
        dsimp only [rowArgs]
        exact validHistory_read_bind
          (by dsimp only [wsSize, frameMaskBase, frameBase] at hf hfr_r ⊢; omega)
          (validHistory_read_bind
            (by dsimp only [wsSize, curAdjBase] at hf hfr_r ⊢; omega)
            (validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; omega)
              (validHistory_write_bind
                (by dsimp only [wsSize, candPredBase] at hf hfr_r ⊢; omega)
                (by split_ifs <;> first | exact h1 | exact fits_zero w)
                (validHistory_write_bind
                  (by dsimp only [wsSize, candCostBase] at hf hfr_r ⊢; omega)
                  (hc_my ▸ hfit_c uFin ⟨y, hy⟩)
                  (validHistory_pure w _ _)))))
      · unfold bestEntryRowStep
        dsimp only [rowArgs]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · intro z hz
        simp only [bestEntryRowStep, rowArgs, client_simps]
        by_cases heq : z.val = y
        · have hz_eq : z = ⟨y, hy⟩ := Fin.ext heq
          subst hz_eq
          simp only [Function.update_self]
          rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
            Function.update_self]
          simp only [hm_y, ha_my, hc_my]
          refine ⟨?_, trivial⟩
          cases inCycle[y] <;> cases a[uFin.val][y] <;> simp
        · rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega)]
          exact hdone_r z (by omega))
    0 s ⟨rfl, rfl, ha_s, hc_s, hm_s, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, ha_end, hc_end, hm_end, hdone_end⟩ := hrow
  unfold fillBestEntryRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, ha_end, hc_end, hm_end, fun z => hdone_end z z.isLt⟩

public theorem bestEntryProg_spec {w n ws k : ℕ} (hpos : 0 < n)
    (a : AdjTable n) (c : CostTable ℤ n) (inCycle : Vector Bool n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (ha : ∀ u col : Fin n, s₀.mem (curAdjBase ws n + u.val * n + col.val) =
      if a[u.val][col.val] then 1 else 0)
    (hc : ∀ u col : Fin n, s₀.mem (curCostBase ws n + u.val * n + col.val) =
      Signed.encode c[u.val][col.val])
    (hm : ∀ y : Fin n, s₀.mem (frameMaskBase ws n k + y.val) = if inCycle[y.val] then 1 else 0)
    (hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.val][col.val])) :
    let la : LevelArgs := ⟨n, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (bestEntryProg la)
    let bEntry := bestEntryTable a c inCycle
    iterationSafe bestEntryOuterStep BestEntryOuterStepSafe w la n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (bestEntryProg la)) ∧
      memoryCost (bestEntryProg la) s₀ ≤ (7 * n + 2) * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
          (frameBEntryBase ws n k ≤ addr ∧ addr < frameBEntryBase ws n k + n)) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ u : Fin n, s'.mem (frameBEntryBase ws n k + u.val) = optFinIdx bEntry[u.val]) := by
  let la : LevelArgs := ⟨n, ws, k⟩
  have h2 : Fits w 2 := hws.of_le (by dsimp only [wsSize]; omega)
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec bestEntryOuterStep BestEntryOuterStepSafe w la (7 * n + 2) n
    (fun m idx s =>
      idx = m ∧ s.frontier = s₀.frontier ∧
        (∀ u col : Fin n, s.mem (curAdjBase ws n + u.val * n + col.val) =
          if a[u.val][col.val] then 1 else 0) ∧
        (∀ u col : Fin n, s.mem (curCostBase ws n + u.val * n + col.val) =
          Signed.encode c[u.val][col.val]) ∧
        (∀ y : Fin n, s.mem (frameMaskBase ws n k + y.val) = if inCycle[y.val] then 1 else 0) ∧
        (∀ j : Fin n, j.val < m →
          s.mem (frameBEntryBase ws n k + j.val) = optFinIdx (bestEntryTable a c inCycle)[j.val]))
    (fun addr => (candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
      (frameBEntryBase ws n k ≤ addr ∧ addr < frameBEntryBase ws n k + n))
    (fun m hm idx s ⟨hidx, hfr, ha_s, hc_s, hm_s, hdone_o⟩ => by
      subst idx
      set uFin : Fin n := ⟨m, hm⟩
      let rowArgs : BestEntryRowArgs :=
        ⟨n, m, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
          candPredBase ws n, candCostBase ws n⟩
      have hrow := fillBestEntryRowProg_spec uFin a c inCycle s hk hws (by rw [hfr]; exact hf)
        ha_s hc_s hm_s hfit_c
      set s1 := (Memory.spec 0).clientState s (fillBestEntryRowProg rowArgs)
      have harg := argMinArrayProg_spec (candPredBase ws n) (candCostBase ws n)
        (fun y => inCycle[y.val] && a[m][y.val]) (fun y => c[m][y.val]) s1
        h2
        (hws.of_le (by dsimp only [wsSize, candPredBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize, candCostBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize]; nlinarith))
        (by dsimp only [wsSize, candPredBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (by dsimp only [wsSize, candCostBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (fun y => (hrow.2.2.2.2.2.2.2.2 y).1)
        (fun y => (hrow.2.2.2.2.2.2.2.2 y).2)
      have harg_s := harg.2.2.2.1
      have harg_r := harg.2.2.2.2
      dsimp only [s1, rowArgs, uFin] at harg_s harg_r
      have hfr_step :
          ((Memory.spec 0).clientState s (bestEntryOuterStep (la, m))).frontier = s.frontier := by
        unfold bestEntryOuterStep
        dsimp only [la]
        have hrow_fr := hrow.2.2.2.1
        dsimp only [s1, rowArgs, uFin] at hrow_fr
        simp [client_simps, harg_s, hrow_fr]
      have hout : ∀ addr, ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
          (frameBEntryBase ws n k ≤ addr ∧ addr < frameBEntryBase ws n k + n)) →
          ((Memory.spec 0).clientState s (bestEntryOuterStep (la, m))).mem addr = s.mem addr := by
        intro addr haddr
        have hne_be : addr ≠ frameBEntryBase ws n k + m :=
          fun heq => haddr (Or.inr ⟨by omega, by omega⟩)
        unfold bestEntryOuterStep
        dsimp only [la]
        have hrow_mod := hrow.2.2.2.2.1
        dsimp only [s1, rowArgs, uFin] at hrow_mod
        simp only [client_simps, harg_s, Function.update_of_ne hne_be]
        exact hrow_mod addr (fun hc => haddr (Or.inl hc))
      have hfr_le := frame_le_frames hk
      refine ⟨by dsimp only [BestEntryOuterStepSafe, la]; exact ⟨hm, hk, hws, hrow.1, harg.1⟩,
        ?_, ?_, hfr_step, hout, by simp [bestEntryOuterStep, client_simps], hfr_step.trans hfr,
        fun u col => (hout _ (by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curAdjBase, candPredBase, candCostBase, frameBEntryBase, frameBase]
          omega)).trans (ha_s u col),
        fun u col => (hout _ (by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curCostBase, candPredBase, candCostBase, frameBEntryBase, frameBase]
          omega)).trans (hc_s u col),
        fun y => (hout _ (by
          have := y.isLt
          dsimp only [frameMaskBase, candPredBase, candCostBase, frameBEntryBase, frameBase]
          omega)).trans (hm_s y),
        fun j hj => ?_⟩
      · unfold bestEntryOuterStep
        dsimp only [la]
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_bind_step hrow.2.1 ?_
        refine validHistory_bind_step harg.2.1 ?_
        rw [harg.2.2.2.1]
        refine validHistory_write_bind
          (by dsimp only [wsSize, frameBEntryBase, frameBase] at hf hfr ⊢;
              rw [hrow.2.2.2.1]; omega)
          ?_ (validHistory_pure w _ _)
        rw [harg.2.2.2.2]
        cases argMinFin n (fun y => inCycle[y.val] && a[m][y.val]) (fun y => c[m][y.val]) with
        | none => exact hws.of_le (by dsimp only [optFinIdx, wsSize]; omega)
        | some j => exact hws.of_le (by have := j.isLt; dsimp only [optFinIdx, wsSize]; omega)
      · unfold bestEntryOuterStep
        dsimp only [la]
        rw [memoryCost_bind', memoryCost_read, clientState_read,
          memoryCost_bind', memoryCost_bind', harg.2.2.2.1, memoryCost_bind', memoryCost_write]
        have hc_r : memoryCost (fillBestEntryRowProg rowArgs) s ≤ 5 * n := hrow.2.2.1
        have hc_a : memoryCost (argMinArrayProg ⟨n, candPredBase ws n, candCostBase ws n⟩) s1 ≤
            2 * n := harg.2.2.1
        dsimp only [rowArgs, s1] at hc_r hc_a ⊢
        simp only [memoryCost_pure]
        omega
      · unfold bestEntryOuterStep
        dsimp only [la]
        simp only [client_simps, harg_s, harg_r]
        by_cases hjm : j.val = m
        · obtain rfl : j = uFin := Fin.ext hjm
          simp [bestEntryTable, uFin]
        · have hrow_mod := hrow.2.2.2.2.1
          dsimp only [s1, rowArgs, uFin] at hrow_mod
          rw [Function.update_of_ne (by omega), hrow_mod _ (by
            dsimp only [candPredBase, candCostBase, frameBEntryBase, frameBase]; omega)]
          exact hdone_o j (by omega))
    0 s₀ ⟨rfl, rfl, ha, hc, hm, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, _, hdone_end⟩ := h
  unfold bestEntryProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun u => hdone_end u u.isLt⟩

private theorem fillBestExitRowProg_spec {w n ws k B_k : ℕ} (colFin : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (s : Memory.State) (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha_s : ∀ u col : Fin n, s.mem (curAdjBase ws n + u.val * n + col.val) =
      if a[u.val][col.val] then 1 else 0)
    (hc_s : ∀ u col : Fin n, s.mem (curCostBase ws n + u.val * n + col.val) =
      Signed.encode c[u.val][col.val])
    (hm_s : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.val) = if inCycle[y.val] then 1 else 0)
    (hf_s : ∀ x : Fin n, s.mem (frameParentBase ws n k + x.val) = (f[x.val]).val)
    (hB : ∀ u col : Fin n, (c[u.val][col.val]).natAbs ≤ B_k) :
    let rowArgs : BestExitRowArgs :=
      ⟨n, colFin.val, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
        frameParentBase ws n k, candPredBase ws n, candCostBase ws n⟩
    let exitVal : Fin n → ℤ := fun x =>
      if inCycle[x.val] && a[x.val][colFin.val] then
        c[x.val][colFin.val] - c[x.val][f[x.val].val]
      else 0
    let s1 := (Memory.spec 0).clientState s (fillBestExitRowProg rowArgs)
    iterationSafe bestExitRowStep BestExitRowStepSafe w rowArgs n 0 s ∧
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (fillBestExitRowProg rowArgs)) ∧
      memoryCost (fillBestExitRowProg rowArgs) s ≤ 7 * n ∧
      s1.frontier = s.frontier ∧
      (∀ addr, ¬(candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) →
        s1.mem addr = s.mem addr) ∧
      (∀ u col : Fin n, s1.mem (curAdjBase ws n + u.val * n + col.val) =
        if a[u.val][col.val] then 1 else 0) ∧
      (∀ u col : Fin n, s1.mem (curCostBase ws n + u.val * n + col.val) =
        Signed.encode c[u.val][col.val]) ∧
      (∀ y : Fin n, s1.mem (frameMaskBase ws n k + y.val) = if inCycle[y.val] then 1 else 0) ∧
      (∀ z : Fin n, s1.mem (frameParentBase ws n k + z.val) = (f[z.val]).val) ∧
      (∀ z : Fin n,
        s1.mem (candPredBase ws n + z.val) =
          (if inCycle[z.val] && a[z.val][colFin.val] then 1 else 0) ∧
        s1.mem (candCostBase ws n + z.val) = Signed.encode (exitVal z)) := by
  let rowArgs : BestExitRowArgs :=
    ⟨n, colFin.val, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
      frameParentBase ws n k, candPredBase ws n, candCostBase ws n⟩
  let exitVal : Fin n → ℤ := fun x =>
    if inCycle[x.val] && a[x.val][colFin.val] then
      c[x.val][colFin.val] - c[x.val][f[x.val].val]
    else 0
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have h2 : Fits w 2 := hws.of_le (by dsimp only [wsSize]; omega)
  have hcol_lt := colFin.isLt
  have hfr_le := frame_le_frames hk
  have hrow := iterate_spec bestExitRowStep BestExitRowStepSafe w rowArgs 7 n
    (fun x idxR sr => idxR = x ∧ sr.frontier = s.frontier ∧
      (∀ u col : Fin n, sr.mem (curAdjBase ws n + u.val * n + col.val) =
        if a[u.val][col.val] then 1 else 0) ∧
      (∀ u col : Fin n, sr.mem (curCostBase ws n + u.val * n + col.val) =
        Signed.encode c[u.val][col.val]) ∧
      (∀ y : Fin n, sr.mem (frameMaskBase ws n k + y.val) = if inCycle[y.val] then 1 else 0) ∧
      (∀ z : Fin n, sr.mem (frameParentBase ws n k + z.val) = (f[z.val]).val) ∧
      (∀ z : Fin n, z.val < x →
        sr.mem (candPredBase ws n + z.val) =
          (if inCycle[z.val] && a[z.val][colFin.val] then 1 else 0) ∧
        sr.mem (candCostBase ws n + z.val) = Signed.encode (exitVal z)))
    (fun addr => candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n)
    (fun x hx idxR sr ⟨hidxR, hfr_r, ha_r, hc_r, hm_r, hf_r, hdone_r⟩ => by
      subst idxR
      set xFin : Fin n := ⟨x, hx⟩
      have hcell_xc := List.mul_add_lt_sq hx hcol_lt
      have hcell_xf := List.mul_add_lt_sq hx (f[x]).isLt
      have hm_x : sr.mem (frameMaskBase ws n k + x) = if inCycle[x] then 1 else 0 := hm_r xFin
      have ha_xm : sr.mem (curAdjBase ws n + x * n + colFin.val) =
          if a[x][colFin.val] then 1 else 0 :=
        ha_r xFin colFin
      have hc_xm : sr.mem (curCostBase ws n + x * n + colFin.val) =
          Signed.encode c[x][colFin.val] :=
        hc_r xFin colFin
      have hf_x : sr.mem (frameParentBase ws n k + x) = (f[x]).val := hf_r xFin
      have hc_xf : sr.mem (curCostBase ws n + x * n + (f[x]).val) = Signed.encode c[x][f[x].val] :=
        hc_r xFin f[x]
      have h1b := hB xFin colFin
      have h2b := hB xFin f[x]
      have hcxf_fit1 : Fits w (sr.mem (curCostBase ws n + x * n +
          sr.mem (frameParentBase ws n k + x)) + 1) := by
        rw [hf_x, hc_xf]
        unfold Signed.encode
        exact hfit_diff.of_le (by split_ifs <;> linarith only [h2b])
      have hsub_fit : Fits w (2 * (sr.mem (curCostBase ws n + x * n + colFin.val) / 2 +
          sr.mem (curCostBase ws n + x * n + sr.mem (frameParentBase ws n k + x)) / 2) + 1) := by
        rw [hc_xm, hf_x, hc_xf, Signed.encode_div_two, Signed.encode_div_two]
        exact hfit_diff.of_le (by linarith only [h1b, h2b])
      have hout : ∀ addr, ¬(candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) →
          ((Memory.spec 0).clientState sr (bestExitRowStep (rowArgs, x))).mem addr =
            sr.mem addr := by
        intro addr haddr
        dsimp only [candPredBase, candCostBase] at haddr
        have hne1 : addr ≠ ws + 4 * (n * n) + n + x := by omega
        have hne2 : addr ≠ ws + 4 * (n * n) + x := by omega
        unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [candPredBase, candCostBase, client_simps]
        split_ifs <;> simp only [client_simps, Function.update_of_ne hne1,
          Function.update_of_ne hne2]
      refine ⟨by dsimp only [BestExitRowStepSafe, rowArgs]; exact ⟨h2,
          hws.of_le (by dsimp only [wsSize, frameMaskBase, frameBase]; omega),
          hws.of_le (by dsimp only [wsSize, curAdjBase]; omega),
          hws.of_le (by dsimp only [wsSize, curCostBase]; omega),
          hws.of_le (by dsimp only [wsSize, frameParentBase, frameBase]; omega),
          hws.of_le (by dsimp only [wsSize, candPredBase]; omega),
          hws.of_le (by dsimp only [wsSize, candCostBase]; omega),
          hws.of_le (by dsimp only [wsSize]; omega),
          fun _ => ⟨by rw [hf_x]; exact hws.of_le (by dsimp only [wsSize, curCostBase]; omega),
            hcxf_fit1, hsub_fit⟩⟩,
        ?_, ?_, ?_, hout, ?_, ?_,
        fun u col => (hout _ (by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curAdjBase, candPredBase, candCostBase]; omega)).trans (ha_r u col),
        fun u col => (hout _ (by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curCostBase, candPredBase, candCostBase]; omega)).trans (hc_r u col),
        fun y => (hout _ (by
          have := y.isLt
          dsimp only [frameMaskBase, frameBase, candPredBase, candCostBase]; omega)).trans (hm_r y),
        fun z => (hout _ (by
          have := z.isLt
          dsimp only [frameParentBase, frameBase, candPredBase, candCostBase]; omega)).trans
            (hf_r z),
        ?_⟩
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        refine validHistory_read_bind
          (by dsimp only [wsSize, frameMaskBase, frameBase] at hf hfr_r ⊢; omega)
          (validHistory_read_bind
            (by dsimp only [wsSize, curAdjBase] at hf hfr_r ⊢; omega)
            (validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; omega)
              (validHistory_read_bind
                (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr_r ⊢; omega) ?_)))
        split_ifs
        · refine validHistory_read_bind
            (by rw [hf_x]; dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; omega) ?_
          refine validHistory_bind_step (validHistory_signedSubProg w _ _) ?_
          rw [clientState_signedSubProg, hc_xm, hf_x, hc_xf, clientResult_signedSubProg]
          refine validHistory_write_bind
            (by dsimp only [wsSize, candPredBase] at hf hfr_r ⊢; omega) h1
            (validHistory_write_bind
              (by dsimp only [wsSize, candCostBase] at hf hfr_r ⊢; omega) ?_
              (validHistory_pure w _ _))
          have hdiff_abs : (c[x][colFin.val] - c[x][f[x].val]).natAbs ≤ 2 * B_k :=
            (Int.natAbs_sub_le _ _).trans (by linarith only [h1b, h2b])
          unfold Signed.encode
          exact hfit_diff.of_le (by split_ifs <;> linarith only [hdiff_abs])
        · exact validHistory_write_bind
            (by dsimp only [wsSize, candPredBase] at hf hfr_r ⊢; omega) (fits_zero w)
            (validHistory_write_bind
              (by dsimp only [wsSize, candCostBase] at hf hfr_r ⊢; omega) (fits_zero w)
              (validHistory_pure w _ _))
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
        split_ifs
        · rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
            memoryCost_bind', memoryCost_signedSubProg, clientState_signedSubProg]
          simp only [memoryCost_bind', memoryCost_write, client_simps]
          omega
        · simp only [memoryCost_bind', memoryCost_write, client_simps]
          omega
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps]
        split_ifs <;> simp only [client_simps]
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps]
        split_ifs <;> simp only [client_simps]
      · unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps]
        split_ifs <;> simpa [client_simps] using hfr_r
      · intro z hz
        unfold bestExitRowStep
        dsimp only [rowArgs]
        simp only [client_simps, hm_x, ha_xm, hc_xm, hf_x]
        by_cases hcond : inCycle[x] = true ∧ a[x][colFin.val] = true
        · have hwcond : (if inCycle[x] = true then (1 : ℕ) else 0) = 1 ∧
              (if a[x][colFin.val] = true then (1 : ℕ) else 0) = 1 :=
            ⟨by simp [hcond.1], by simp [hcond.2]⟩
          simp only [hwcond, and_self, ↓reduceIte, hc_xf, clientResult_signedSubProg, client_simps]
          by_cases heq : z.val = x
          · have hz_eq : z = xFin := Fin.ext heq
            subst hz_eq
            simp only [Function.update_self, exitVal, hcond.1, hcond.2, Bool.and_self,
              ↓reduceIte, xFin]
            rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
              Function.update_self]
            simp
          · rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega)]
            exact hdone_r z (by omega)
        · have hnwcond : ¬((if inCycle[x] = true then (1 : ℕ) else 0) = 1 ∧
              (if a[x][colFin.val] = true then (1 : ℕ) else 0) = 1) := by
            rintro ⟨h1w, h2w⟩
            apply hcond
            constructor
            · by_cases h1b : inCycle[x] = true
              · exact h1b
              · simp [h1b] at h1w
            · by_cases h2b : a[x][colFin.val] = true
              · exact h2b
              · simp [h2b] at h2w
          have hbcond : (inCycle[x] && a[x][colFin.val]) = false :=
            Bool.and_eq_false_iff.mpr <| by
              by_cases h1b : inCycle[x] = true
              · exact Or.inr (Bool.eq_false_of_ne_true fun h2b => hcond ⟨h1b, h2b⟩)
              · exact Or.inl (Bool.eq_false_of_ne_true h1b)
          simp only [hnwcond, ↓reduceIte, client_simps]
          by_cases heq : z.val = x
          · have hz_eq : z = xFin := Fin.ext heq
            subst hz_eq
            simp only [Function.update_self, exitVal, hbcond, Bool.false_eq_true, ↓reduceIte,
              Signed.encode, lt_irrefl, Nat.add_zero, xFin]
            rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
              Function.update_self]
            exact ⟨rfl, rfl⟩
          · rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega)]
            exact hdone_r z (by omega))
    0 s ⟨rfl, rfl, ha_s, hc_s, hm_s, hf_s, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, ha_e, hc_e, hm_e, hf_e, hdone_e⟩ := hrow
  unfold fillBestExitRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, ha_e, hc_e, hm_e, hf_e, fun z => hdone_e z z.isLt⟩

public theorem bestExitProg_spec {w n ws k B_k : ℕ} (hpos : 0 < n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (s₀ : Memory.State) (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha : ∀ u col : Fin n, s₀.mem (curAdjBase ws n + u.val * n + col.val) =
      if a[u.val][col.val] then 1 else 0)
    (hc : ∀ u col : Fin n, s₀.mem (curCostBase ws n + u.val * n + col.val) =
      Signed.encode c[u.val][col.val])
    (hm : ∀ y : Fin n, s₀.mem (frameMaskBase ws n k + y.val) = if inCycle[y.val] then 1 else 0)
    (hfp : ∀ x : Fin n, s₀.mem (frameParentBase ws n k + x.val) = (f[x.val]).val)
    (hB : ∀ u col : Fin n, (c[u.val][col.val]).natAbs ≤ B_k) :
    let la : LevelArgs := ⟨n, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (bestExitProg la)
    let bExit := reducedBestExitTable a c f inCycle
    iterationSafe bestExitOuterStep BestExitOuterStepSafe w la n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (bestExitProg la)) ∧
      memoryCost (bestExitProg la) s₀ ≤ (9 * n + 2) * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
          (frameBExitBase ws n k ≤ addr ∧ addr < frameBExitBase ws n k + n)) →
        s'.mem addr = s₀.mem addr) ∧
      (∀ col : Fin n, s'.mem (frameBExitBase ws n k + col.val) = optFinIdx bExit[col.val]) := by
  let la : LevelArgs := ⟨n, ws, k⟩
  have h2 : Fits w 2 := hws.of_le (by dsimp only [wsSize]; omega)
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec bestExitOuterStep BestExitOuterStepSafe w la (9 * n + 2) n
    (fun m idx s =>
      idx = m ∧ s.frontier = s₀.frontier ∧
        (∀ u col : Fin n, s.mem (curAdjBase ws n + u.val * n + col.val) =
          if a[u.val][col.val] then 1 else 0) ∧
        (∀ u col : Fin n, s.mem (curCostBase ws n + u.val * n + col.val) =
          Signed.encode c[u.val][col.val]) ∧
        (∀ y : Fin n, s.mem (frameMaskBase ws n k + y.val) = if inCycle[y.val] then 1 else 0) ∧
        (∀ x : Fin n, s.mem (frameParentBase ws n k + x.val) = (f[x.val]).val) ∧
        (∀ j : Fin n, j.val < m →
          s.mem (frameBExitBase ws n k + j.val) =
            optFinIdx (reducedBestExitTable a c f inCycle)[j.val]))
    (fun addr => (candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
      (frameBExitBase ws n k ≤ addr ∧ addr < frameBExitBase ws n k + n))
    (fun m hm idx s ⟨hidx, hfr, ha_s, hc_s, hm_s, hfp_s, hdone_o⟩ => by
      subst idx
      set colFin : Fin n := ⟨m, hm⟩
      let rowArgs : BestExitRowArgs :=
        ⟨n, m, curAdjBase ws n, curCostBase ws n, frameMaskBase ws n k,
          frameParentBase ws n k, candPredBase ws n, candCostBase ws n⟩
      let exitVal : Fin n → ℤ := fun x =>
        if inCycle[x.val] && a[x.val][m] then c[x.val][m] - c[x.val][f[x.val].val] else 0
      have hrow := fillBestExitRowProg_spec colFin a c f inCycle s hk hws
        (by rw [hfr]; exact hf) hfit_diff ha_s hc_s hm_s hfp_s hB
      set s1 := (Memory.spec 0).clientState s (fillBestExitRowProg rowArgs)
      have harg := argMinArrayProg_spec (candPredBase ws n) (candCostBase ws n)
        (fun x => inCycle[x.val] && a[x.val][m]) exitVal s1
        h2
        (hws.of_le (by dsimp only [wsSize, candPredBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize, candCostBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize]; nlinarith))
        (by dsimp only [wsSize, candPredBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (by dsimp only [wsSize, candCostBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (fun x => (hrow.2.2.2.2.2.2.2.2.2 x).1)
        (fun x => (hrow.2.2.2.2.2.2.2.2.2 x).2)
      have hargmin_eq : argMinFin n (fun x => inCycle[x.val] && a[x.val][m]) exitVal =
          (reducedBestExitTable a c f inCycle)[m] := by
        simp only [reducedBestExitTable, Vector.getElem_ofFn]
        exact argMinFin_of_lt_iff _ _ _ fun x y hx hy => by
          simp only [Bool.and_eq_true] at hx hy
          simp [exitVal, hx.1, hx.2, hy.1, hy.2]
      have harg_s := harg.2.2.2.1
      have harg_r := harg.2.2.2.2
      dsimp only [s1, rowArgs, colFin] at harg_s harg_r
      have hfr_step :
          ((Memory.spec 0).clientState s (bestExitOuterStep (la, m))).frontier = s.frontier := by
        unfold bestExitOuterStep
        dsimp only [la]
        have hrow_fr := hrow.2.2.2.1
        dsimp only [s1, rowArgs, colFin] at hrow_fr
        simp [client_simps, harg_s, hrow_fr]
      have hout : ∀ addr, ¬((candPredBase ws n ≤ addr ∧ addr < candCostBase ws n + n) ∨
          (frameBExitBase ws n k ≤ addr ∧ addr < frameBExitBase ws n k + n)) →
          ((Memory.spec 0).clientState s (bestExitOuterStep (la, m))).mem addr = s.mem addr := by
        intro addr haddr
        have hne_bx : addr ≠ frameBExitBase ws n k + m :=
          fun heq => haddr (Or.inr ⟨by omega, by omega⟩)
        unfold bestExitOuterStep
        dsimp only [la]
        have hrow_mod := hrow.2.2.2.2.1
        dsimp only [s1, rowArgs, colFin] at hrow_mod
        simp only [client_simps, harg_s, Function.update_of_ne hne_bx]
        exact hrow_mod addr (fun hc => haddr (Or.inl hc))
      have hfr_le := frame_le_frames hk
      refine ⟨by dsimp only [BestExitOuterStepSafe, la]; exact ⟨hm, hk, hws, hrow.1, harg.1⟩,
        ?_, ?_, hfr_step, hout, by simp [bestExitOuterStep, client_simps], hfr_step.trans hfr,
        fun u col => (hout _ (by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curAdjBase, candPredBase, candCostBase, frameBExitBase, frameBase]
          omega)).trans (ha_s u col),
        fun u col => (hout _ (by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curCostBase, candPredBase, candCostBase, frameBExitBase, frameBase]
          omega)).trans (hc_s u col),
        fun y => (hout _ (by
          have := y.isLt
          dsimp only [frameMaskBase, candPredBase, candCostBase, frameBExitBase, frameBase]
          omega)).trans (hm_s y),
        fun x => (hout _ (by
          have := x.isLt
          dsimp only [frameParentBase, candPredBase, candCostBase, frameBExitBase, frameBase]
          omega)).trans (hfp_s x),
        fun j hj => ?_⟩
      · unfold bestExitOuterStep
        dsimp only [la]
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_bind_step hrow.2.1 ?_
        refine validHistory_bind_step harg.2.1 ?_
        rw [harg.2.2.2.1]
        refine validHistory_write_bind
          (by dsimp only [wsSize, frameBExitBase, frameBase] at hf hfr ⊢;
              rw [hrow.2.2.2.1]; omega)
          ?_ (validHistory_pure w _ _)
        rw [harg.2.2.2.2]
        cases argMinFin n (fun x => inCycle[x.val] && a[x.val][m]) exitVal with
        | none => exact hws.of_le (by dsimp only [optFinIdx, wsSize]; omega)
        | some j => exact hws.of_le (by have := j.isLt; dsimp only [optFinIdx, wsSize]; omega)
      · unfold bestExitOuterStep
        dsimp only [la]
        rw [memoryCost_bind', memoryCost_read, clientState_read,
          memoryCost_bind', memoryCost_bind', harg.2.2.2.1, memoryCost_bind', memoryCost_write]
        have hc_r : memoryCost (fillBestExitRowProg rowArgs) s ≤ 7 * n := hrow.2.2.1
        have hc_a : memoryCost (argMinArrayProg ⟨n, candPredBase ws n, candCostBase ws n⟩) s1 ≤
            2 * n := harg.2.2.1
        dsimp only [rowArgs, s1] at hc_r hc_a ⊢
        simp only [memoryCost_pure]
        omega
      · unfold bestExitOuterStep
        dsimp only [la]
        simp only [client_simps, harg_s, harg_r, hargmin_eq]
        by_cases hjm : j.val = m
        · simp [hjm]
        · have hrow_mod := hrow.2.2.2.2.1
          dsimp only [s1, rowArgs, colFin] at hrow_mod
          rw [Function.update_of_ne (by omega), hrow_mod _ (by
            dsimp only [candPredBase, candCostBase, frameBExitBase, frameBase]; omega)]
          exact hdone_o j (by omega))
    0 s₀ ⟨rfl, rfl, ha, hc, hm, hfp, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, _, _, hdone_end⟩ := h
  unfold bestExitProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun col => hdone_end col col.isLt⟩

end Cslib.Algorithms.WordRAM.Arborescence.Internal
