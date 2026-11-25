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
# Specification for `contractTablesProg` (internal)

Proves cell-by-cell equivalence, admissibility, `O(n²)` memory cost, and table correspondence
between `contractTablesProg` and `(contractAdjTable, contractReducedCostTable)`.
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

private theorem contractCostCellProg_eval {w n ws k B_k : ℕ} (r x0 u col : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha : ∀ x y : Fin n,
      s.mem (curAdjBase ws n + x.1 * n + y.1) = if a[x.1][y.1] then 1 else 0)
    (hc : ∀ x y : Fin n, s.mem (curCostBase ws n + x.1 * n + y.1) = Signed.encode c[x.1][y.1])
    (hm : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfp : ∀ x : Fin n, s.mem (frameParentBase ws n k + x.1) = (f[x.1]).1)
    (hbe : ∀ x : Fin n, s.mem (frameBEntryBase ws n k + x.1) = optFinIdx bEntry[x.1])
    (hbx : ∀ y : Fin n, s.mem (frameBExitBase ws n k + y.1) = optFinIdx bExit[y.1])
    (hB : ∀ x y : Fin n, (c[x.1][y.1]).natAbs ≤ B_k) :
    let q : ContractRowArgs × ℕ := (⟨n, r.1, x0.1, u.1, ws, k⟩, col.1)
    let c' := contractReducedCostTable a c f inCycle bEntry bExit x0
    ContractRowStepSafe w q s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (contractCostCellProg q)) ∧
      memoryCost (contractCostCellProg q) s ≤ 10 ∧
      (Memory.spec 0).clientState s (contractCostCellProg q) =
        ⟨Function.update s.mem (nextCostBase ws n + u.1 * n + col.1)
          (Signed.encode c'[u.1][col.1]), s.frontier⟩ := by
  let q : ContractRowArgs × ℕ := (⟨n, r.1, x0.1, u.1, ws, k⟩, col.1)
  have hu_lt := u.isLt
  have hc_lt := col.isLt
  have hcell_uc := List.mul_add_lt_sq hu_lt hc_lt
  have hfr_le := frame_le_frames hk
  have hm_u := hm u
  have hm_c := hm col
  have ha_uc := ha u col
  have hc_uc := hc u col
  have hbe_u := hbe u
  have hbx_c := hbx col
  have hfit_c' : Fits w (Signed.encode
      (contractReducedCostTable a c f inCycle bEntry bExit x0)[u.1][col.1]) := by
    have habs := contractReducedCostTable_natAbs_le a c f inCycle bEntry bExit x0 hB u col
    unfold Signed.encode
    exact hfit_diff.of_le (by split_ifs <;> linarith only [habs])
  have hsafe : ContractRowStepSafe w q s := by
    dsimp only [ContractRowStepSafe, q]
    refine ⟨hu_lt, hc_lt, hk, hws, fun _ _ _ hbx_lt => ?_⟩
    rw [hbx_c] at hbx_lt ⊢
    cases hb_case : bExit[col.1] with
    | none => simp [hb_case, optFinIdx] at hbx_lt
    | some xs =>
      simp only [optFinIdx]
      rw [hfp xs, hc xs col, hc xs f[xs.1], Signed.encode_div_two, Signed.encode_div_two]
      have h1b := hB xs col
      have h2b := hB xs f[xs.1]
      refine ⟨(f[xs.1]).isLt, ?_, hfit_diff.of_le (by linarith only [h1b, h2b])⟩
      unfold Signed.encode
      exact hfit_diff.of_le (by split_ifs <;> linarith only [h2b])
  refine ⟨hsafe, ?_, ?_, ?_⟩
  · unfold contractCostCellProg
    dsimp only [q]
    refine validHistory_read_bind
      (by dsimp only [wsSize, frameMaskBase, frameBase] at hf ⊢; omega)
      (validHistory_read_bind
        (by dsimp only [wsSize, frameMaskBase, frameBase] at hf ⊢; omega)
        (validHistory_read_bind
          (by dsimp only [wsSize, curAdjBase] at hf ⊢; omega)
          (validHistory_read_bind
            (by dsimp only [wsSize, curCostBase] at hf ⊢; omega)
            (validHistory_read_bind
              (by dsimp only [wsSize, frameBEntryBase, frameBase] at hf ⊢; omega)
              (validHistory_read_bind
                (by dsimp only [wsSize, frameBExitBase, frameBase] at hf ⊢; omega) ?_)))))
    rw [hm_u, hm_c, ha_uc, hc_uc, hbe_u, hbx_c]
    by_cases huC : inCycle[u.1] = true
    · simp only [huC, ↓reduceIte]
      by_cases hux : u = x0
      · subst hux
        simp only [↓reduceIte]
        by_cases hwC : inCycle[col.1] = true
        · simp only [hwC, ↓reduceIte, Nat.one_ne_zero, false_and]
          exact validHistory_write_bind
            (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
            (validHistory_pure w _ _)
        · simp only [hwC, Bool.false_eq_true, ↓reduceIte, true_and]
          cases hb_case : bExit[col.1] with
          | none =>
            simp only [optFinIdx, lt_irrefl, ↓reduceIte]
            exact validHistory_write_bind
              (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
              (validHistory_pure w _ _)
          | some xs =>
            have hcell_xc := List.mul_add_lt_sq xs.isLt hc_lt
            have hcell_xf := List.mul_add_lt_sq xs.isLt (f[xs.1]).isLt
            have hxs_lt := xs.isLt
            simp only [optFinIdx, hxs_lt, ↓reduceIte]
            refine validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf ⊢; omega)
              (validHistory_read_bind
                (by dsimp only [wsSize, frameParentBase, frameBase] at hf ⊢; omega) ?_)
            rw [hfp xs]
            refine validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf ⊢; omega) ?_
            refine validHistory_bind_step (validHistory_signedSubProg w _ _) ?_
            rw [clientState_signedSubProg, hc xs col, hc xs f[xs.1], clientResult_signedSubProg]
            refine validHistory_write_bind
              (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) ?_
              (validHistory_pure w _ _)
            simpa [getElem_contractReducedCostTable, huC, hwC, hb_case] using hfit_c'
      · have hux_v : u.1 ≠ x0.1 := fun h => hux (Fin.ext h)
        simp only [hux_v, ↓reduceIte]
        exact validHistory_write_bind
          (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
          (validHistory_pure w _ _)
    · simp only [huC, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
      by_cases hwC : inCycle[col.1] = true
      · simp only [hwC, ↓reduceIte]
        by_cases hcx : col = x0
        · subst hcx
          simp only [true_and]
          cases hbe_case : bEntry[u.1] with
          | none =>
            simp only [optFinIdx, lt_irrefl, ↓reduceIte]
            exact validHistory_write_bind
              (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
              (validHistory_pure w _ _)
          | some ys =>
            have hcell_uy := List.mul_add_lt_sq hu_lt ys.isLt
            simp only [optFinIdx, ys.isLt, ↓reduceIte]
            refine validHistory_read_bind
              (by dsimp only [wsSize, curCostBase] at hf ⊢; omega) ?_
            rw [hc u ys]
            refine validHistory_write_bind
              (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) ?_
              (validHistory_pure w _ _)
            simpa [getElem_contractReducedCostTable, huC, hwC, hbe_case] using hfit_c'
        · have hcx_v : col.1 ≠ x0.1 := fun h => hcx (Fin.ext h)
          simp only [hcx_v, false_and, ↓reduceIte]
          exact validHistory_write_bind
            (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
            (validHistory_pure w _ _)
      · simp only [hwC, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
        by_cases ha_b : a[u.1][col.1] = true
        · simp only [ha_b, ↓reduceIte]
          refine validHistory_write_bind
            (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) ?_
            (validHistory_pure w _ _)
          simpa [getElem_contractReducedCostTable, huC, hwC, ha_b] using hfit_c'
        · simp only [ha_b, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
          exact validHistory_write_bind
            (by dsimp only [wsSize, nextCostBase] at hf ⊢; omega) (fits_zero w)
            (validHistory_pure w _ _)
  · unfold contractCostCellProg
    dsimp only [q]
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
    split_ifs
    · simp only [memoryCost_bind', memoryCost_read, clientResult_read,
        memoryCost_signedSubProg, memoryCost_write, client_simps]
      omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
    · simp only [memoryCost_bind', memoryCost_read, memoryCost_write, client_simps]
      omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
    · simp only [memoryCost_bind', memoryCost_write, client_simps]; omega
  · unfold contractCostCellProg
    dsimp only [q]
    simp only [client_simps, hm_u, hm_c, ha_uc, hc_uc, hbe_u, hbx_c]
    rw [getElem_contractReducedCostTable]
    by_cases huC : inCycle[u.1] = true
    · simp only [huC, ↓reduceIte]
      by_cases hux : u = x0
      · subst hux
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases hwC : inCycle[col.1] = true
        · simp [hwC, Signed.encode, client_simps]
        · simp only [hwC, Bool.false_eq_true, ↓reduceIte, Bool.not_false, true_and]
          cases hb_case : bExit[col.1] with
          | none => simp [optFinIdx, Signed.encode, client_simps]
          | some xs =>
            simp [optFinIdx, xs.isLt, hc xs col, hfp xs, hc xs f[xs.1],
              clientResult_signedSubProg, client_simps]
      · have hux_v : u.1 ≠ x0.1 := fun h => hux (Fin.ext h)
        have hux_b : (u == x0) = false := beq_false_of_ne hux
        simp [hux_v, hux_b, Signed.encode, client_simps]
    · simp only [huC, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
      by_cases hwC : inCycle[col.1] = true
      · simp only [hwC, ↓reduceIte]
        by_cases hcx : col = x0
        · subst hcx
          simp only [beq_self_eq_true, ↓reduceIte, true_and]
          cases hbe_case : bEntry[u.1] with
          | none => simp [optFinIdx, Signed.encode, client_simps]
          | some ys => simp [optFinIdx, ys.isLt, hc u ys, client_simps]
        · have hcx_v : col.1 ≠ x0.1 := fun h => hcx (Fin.ext h)
          have hcx_b : (col == x0) = false := beq_false_of_ne hcx
          simp [hcx_v, hcx_b, Signed.encode, client_simps]
      · simp only [hwC, Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one]
        by_cases ha_b : a[u.1][col.1] = true
        · simp [ha_b, client_simps]
        · simp [ha_b, Signed.encode, client_simps]

private theorem contractAdjCellProg_eval {w n ws k : ℕ} (r x0 u col : Fin n)
    (a : AdjTable n) (inCycle : Vector Bool n) (bEntry bExit : Vector (Option (Fin n)) n)
    (s : Memory.State) (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (ha : ∀ x y : Fin n,
      s.mem (curAdjBase ws n + x.1 * n + y.1) = if a[x.1][y.1] then 1 else 0)
    (hm : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hbe : ∀ x : Fin n, s.mem (frameBEntryBase ws n k + x.1) = optFinIdx bEntry[x.1])
    (hbx : ∀ y : Fin n, s.mem (frameBExitBase ws n k + y.1) = optFinIdx bExit[y.1]) :
    let q : ContractRowArgs × ℕ := (⟨n, r.1, x0.1, u.1, ws, k⟩, col.1)
    let a' := contractAdjTable a inCycle bEntry bExit x0 r
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (contractAdjCellProg q)) ∧
      memoryCost (contractAdjCellProg q) s ≤ 6 ∧
      (Memory.spec 0).clientState s (contractAdjCellProg q) =
        ⟨Function.update s.mem (nextAdjBase ws n + u.1 * n + col.1)
          (if a'[u.1][col.1] then 1 else 0), s.frontier⟩ := by
  let q : ContractRowArgs × ℕ := (⟨n, r.1, x0.1, u.1, ws, k⟩, col.1)
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hu_lt := u.isLt
  have hc_lt := col.isLt
  have hcell_uc := List.mul_add_lt_sq hu_lt hc_lt
  have hfr_le := frame_le_frames hk
  have hm_u := hm u
  have hm_c := hm col
  have ha_uc := ha u col
  have hbe_u := hbe u
  have hbx_c := hbx col
  refine ⟨?_, ?_, ?_⟩
  · unfold contractAdjCellProg
    dsimp only [q]
    refine validHistory_read_bind
      (by dsimp only [wsSize, frameMaskBase, frameBase] at hf ⊢; omega)
      (validHistory_read_bind
        (by dsimp only [wsSize, frameMaskBase, frameBase] at hf ⊢; omega)
        (validHistory_read_bind
          (by dsimp only [wsSize, curAdjBase] at hf ⊢; omega)
          (validHistory_read_bind
            (by dsimp only [wsSize, frameBEntryBase, frameBase] at hf ⊢; omega)
            (validHistory_read_bind
              (by dsimp only [wsSize, frameBExitBase, frameBase] at hf ⊢; omega) ?_))))
    refine validHistory_write_bind
      (by dsimp only [wsSize, nextAdjBase] at hf ⊢; omega) ?_
      (validHistory_pure w _ _)
    rw [ha_uc]
    split_ifs <;> first | exact h1 | exact fits_zero w
  · unfold contractAdjCellProg
    dsimp only [q]
    rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_write]
  · unfold contractAdjCellProg
    dsimp only [q]
    simp only [client_simps, hm_u, hm_c, ha_uc, hbe_u, hbx_c, getElem_contractAdjTable]
    apply congrArg (fun v =>
      (⟨Function.update s.mem (nextAdjBase ws n + u.1 * n + col.1) v, s.frontier⟩ : Memory.State))
    cases hu_b : inCycle[u.1] <;> cases hc_b : inCycle[col.1]
    · cases a[u.1][col.1] <;> simp
    · by_cases hcx : col = x0
      · subst hcx
        cases bEntry[u.1] with
        | none => simp [optFinIdx]
        | some ys => simp [optFinIdx, ys.isLt]
      · have hcx_v : col.1 ≠ x0.1 := fun h => hcx (Fin.ext h)
        simp [hcx, hcx_v]
    · by_cases hux : u = x0
      · subst hux
        cases bExit[col.1] with
        | none => simp [optFinIdx]
        | some xs => simp [optFinIdx, xs.isLt]
      · have hux_v : u.1 ≠ x0.1 := fun h => hux (Fin.ext h)
        by_cases hcr : col = r
        · subst hcr; simp [hux, hux_v]
        · have hcr_v : col.1 ≠ r.1 := fun h => hcr (Fin.ext h)
          simp [hux, hux_v, hcr, hcr_v]
    · by_cases hux : u = x0
      · subst hux; simp
      · have hux_v : u.1 ≠ x0.1 := fun h => hux (Fin.ext h)
        by_cases hcr : col = r
        · subst hcr; simp [hux, hux_v]
        · have hcr_v : col.1 ≠ r.1 := fun h => hcr (Fin.ext h)
          simp [hux, hux_v, hcr, hcr_v]

private theorem fillContractRowProg_spec {w n ws k B_k : ℕ} (r x0 uFin : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha_s : ∀ u col : Fin n,
      s.mem (curAdjBase ws n + u.1 * n + col.1) = if a[u.1][col.1] then 1 else 0)
    (hc_s : ∀ u col : Fin n,
      s.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c[u.1][col.1])
    (hm_s : ∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfp_s : ∀ x : Fin n, s.mem (frameParentBase ws n k + x.1) = (f[x.1]).1)
    (hbe_s : ∀ u : Fin n, s.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1])
    (hbx_s : ∀ col : Fin n, s.mem (frameBExitBase ws n k + col.1) = optFinIdx bExit[col.1])
    (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) :
    let ra : ContractRowArgs := ⟨n, r.1, x0.1, uFin.1, ws, k⟩
    let sr' := (Memory.spec 0).clientState s (fillContractRowProg ra)
    iterationSafe contractRowStep ContractRowStepSafe w ra n 0 s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillContractRowProg ra)) ∧
      memoryCost (fillContractRowProg ra) s ≤ 16 * n ∧
      sr'.frontier = s.frontier ∧
      (∀ addr, ¬(nextAdjBase ws n + uFin.1 * n ≤ addr ∧ addr < nextAdjBase ws n + uFin.1 * n + n ∨
        nextCostBase ws n + uFin.1 * n ≤ addr ∧ addr < nextCostBase ws n + uFin.1 * n + n) →
        sr'.mem addr = s.mem addr) ∧
      (∀ col : Fin n,
        sr'.mem (nextAdjBase ws n + uFin.1 * n + col.1) =
          (if (contractAdjTable a inCycle bEntry bExit x0 r)[uFin.1][col.1] then 1 else 0) ∧
        sr'.mem (nextCostBase ws n + uFin.1 * n + col.1) =
          Signed.encode
            (contractReducedCostTable a c f inCycle bEntry bExit x0)[uFin.1][col.1]) := by
  let ra : ContractRowArgs := ⟨n, r.1, x0.1, uFin.1, ws, k⟩
  have hrow := iterate_spec contractRowStep ContractRowStepSafe w ra 16 n
    (fun col idxR sr =>
      idxR = col ∧ sr.frontier = s.frontier ∧
        (∀ u c0 : Fin n,
          sr.mem (curAdjBase ws n + u.1 * n + c0.1) = if a[u.1][c0.1] then 1 else 0) ∧
        (∀ u c0 : Fin n,
          sr.mem (curCostBase ws n + u.1 * n + c0.1) = Signed.encode c[u.1][c0.1]) ∧
        (∀ y : Fin n, sr.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0) ∧
        (∀ x : Fin n, sr.mem (frameParentBase ws n k + x.1) = (f[x.1]).1) ∧
        (∀ u : Fin n, sr.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1]) ∧
        (∀ c0 : Fin n, sr.mem (frameBExitBase ws n k + c0.1) = optFinIdx bExit[c0.1]) ∧
        (∀ c0 : Fin n, c0.1 < col →
          sr.mem (nextAdjBase ws n + uFin.1 * n + c0.1) =
            (if (contractAdjTable a inCycle bEntry bExit x0 r)[uFin.1][c0.1] then 1 else 0) ∧
          sr.mem (nextCostBase ws n + uFin.1 * n + c0.1) =
            Signed.encode
              (contractReducedCostTable a c f inCycle bEntry bExit x0)[uFin.1][c0.1]))
    (fun addr => nextAdjBase ws n + uFin.1 * n ≤ addr ∧ addr < nextAdjBase ws n + uFin.1 * n + n ∨
      nextCostBase ws n + uFin.1 * n ≤ addr ∧ addr < nextCostBase ws n + uFin.1 * n + n)
    (fun col hcol idxR sr ⟨hidxR, hfr_r, ha_r, hc_r, hm_r, hfp_r, hbe_r, hbx_r, hcur⟩ => by
      subst idxR
      set colFin : Fin n := ⟨col, hcol⟩
      have hu_lt := uFin.isLt
      have hcell_uc := List.mul_add_lt_sq hu_lt hcol
      have hcost_ev := contractCostCellProg_eval r x0 uFin colFin a c f inCycle bEntry bExit
        sr hk hws (by rw [hfr_r]; exact hf) hfit_diff ha_r hc_r hm_r hfp_r hbe_r hbx_r hB
      set sr1 : Memory.State :=
        ⟨Function.update sr.mem (nextCostBase ws n + uFin.1 * n + col)
          (Signed.encode (contractReducedCostTable a c f inCycle bEntry bExit x0)[uFin.1][col]),
          sr.frontier⟩
      have hadj_ev := contractAdjCellProg_eval r x0 uFin colFin a inCycle bEntry bExit
        sr1 hk hws (by dsimp only [sr1]; rw [hfr_r]; exact hf)
        (fun x y => by
          have := List.mul_add_lt_sq x.isLt y.isLt
          dsimp only [sr1]
          rw [Function.update_of_ne (by dsimp only [curAdjBase, nextCostBase]; omega)]
          exact ha_r x y)
        (fun y => by
          have := y.isLt
          dsimp only [sr1]
          rw [Function.update_of_ne
            (by dsimp only [frameMaskBase, frameBase, nextCostBase]; omega)]
          exact hm_r y)
        (fun x => by
          have := x.isLt
          dsimp only [sr1]
          rw [Function.update_of_ne
            (by dsimp only [frameBEntryBase, frameBase, nextCostBase]; omega)]
          exact hbe_r x)
        (fun y => by
          have := y.isLt
          dsimp only [sr1]
          rw [Function.update_of_ne
            (by dsimp only [frameBExitBase, frameBase, nextCostBase]; omega)]
          exact hbx_r y)
      have hcost_s := hcost_ev.2.2.2
      have hadj_s := hadj_ev.2.2
      dsimp only [ra, colFin] at hcost_s hadj_s
      refine ⟨hcost_ev.1, ?_, ?_, ?_, ?_, ?_⟩
      · unfold contractRowStep
        refine validHistory_bind_step hcost_ev.2.1 ?_
        rw [hcost_s]
        exact validHistory_bind_step hadj_ev.1 (validHistory_pure w _ _)
      · unfold contractRowStep
        rw [memoryCost_bind', hcost_s, memoryCost_bind']
        have h1c := hcost_ev.2.2.1
        have h2c := hadj_ev.2.1
        dsimp only [ra, colFin, sr1] at h1c h2c ⊢
        simp only [client_simps]
        omega
      · unfold contractRowStep
        dsimp only [ra, colFin]
        dsimp only [sr1] at hadj_s
        simp only [client_simps, hcost_s, hadj_s]
      · intro addr haddr
        unfold contractRowStep
        dsimp only [ra, colFin]
        simp only [client_simps, hcost_s, hadj_s, sr1]
        dsimp only [nextAdjBase, nextCostBase] at haddr ⊢
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · unfold contractRowStep
        dsimp only [ra, colFin]
        simp only [client_simps, hcost_s, hadj_s, sr1]
        refine ⟨trivial, hfr_r, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro u0 c0
          have := List.mul_add_lt_sq u0.isLt c0.isLt
          rw [Function.update_of_ne (by dsimp only [curAdjBase, nextAdjBase]; omega),
            Function.update_of_ne (by dsimp only [curAdjBase, nextCostBase]; omega)]
          exact ha_r u0 c0
        · intro u0 c0
          have := List.mul_add_lt_sq u0.isLt c0.isLt
          rw [Function.update_of_ne (by dsimp only [curCostBase, nextAdjBase]; omega),
            Function.update_of_ne (by dsimp only [curCostBase, nextCostBase]; omega)]
          exact hc_r u0 c0
        · intro y
          have := y.isLt
          rw [Function.update_of_ne
              (by dsimp only [frameMaskBase, frameBase, nextAdjBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameMaskBase, frameBase, nextCostBase]; omega)]
          exact hm_r y
        · intro x
          have := x.isLt
          rw [Function.update_of_ne
              (by dsimp only [frameParentBase, frameBase, nextAdjBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameParentBase, frameBase, nextCostBase]; omega)]
          exact hfp_r x
        · intro u0
          have := u0.isLt
          rw [Function.update_of_ne
              (by dsimp only [frameBEntryBase, frameBase, nextAdjBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameBEntryBase, frameBase, nextCostBase]; omega)]
          exact hbe_r u0
        · intro c0
          have := c0.isLt
          rw [Function.update_of_ne
              (by dsimp only [frameBExitBase, frameBase, nextAdjBase]; omega),
            Function.update_of_ne
              (by dsimp only [frameBExitBase, frameBase, nextCostBase]; omega)]
          exact hbx_r c0
        · intro c0 hc0
          by_cases heq : c0.1 = col
          · have hc0_eq : c0 = colFin := Fin.ext heq
            subst hc0_eq
            simp only [Function.update_self, colFin]
            rw [Function.update_of_ne (by dsimp only [nextAdjBase, nextCostBase]; omega),
              Function.update_self]
            simp
          · rw [Function.update_of_ne (by omega),
              Function.update_of_ne (by dsimp only [nextAdjBase, nextCostBase]; omega),
              Function.update_of_ne (by dsimp only [nextAdjBase, nextCostBase]; omega),
              Function.update_of_ne (by omega)]
            exact hcur c0 (by omega))
    0 s ⟨rfl, rfl, ha_s, hc_s, hm_s, hfp_s, hbe_s, hbx_s, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, _, _, _, _, hdone_end⟩ := hrow
  unfold fillContractRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun col => hdone_end col col.isLt⟩

public theorem contractTablesProg_spec {w n ws k B_k : ℕ} (r x0 : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (f : ParentTable n) (inCycle : Vector Bool n)
    (bEntry bExit : Vector (Option (Fin n)) n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (hfit_diff : Fits w (4 * B_k + 2))
    (ha : ∀ u col : Fin n,
      s₀.mem (curAdjBase ws n + u.1 * n + col.1) = if a[u.1][col.1] then 1 else 0)
    (hc : ∀ u col : Fin n,
      s₀.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c[u.1][col.1])
    (hm : ∀ y : Fin n, s₀.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0)
    (hfp : ∀ x : Fin n, s₀.mem (frameParentBase ws n k + x.1) = (f[x.1]).1)
    (hbe : ∀ u : Fin n, s₀.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1])
    (hbx : ∀ col : Fin n, s₀.mem (frameBExitBase ws n k + col.1) = optFinIdx bExit[col.1])
    (hB : ∀ u col : Fin n, (c[u.1][col.1]).natAbs ≤ B_k) :
    let ca : ContractArgs := ⟨n, r.1, x0.1, ws, k⟩
    let s1 := (Memory.spec 0).clientState s₀ (contractLoopProg ca)
    let cp : CopyArgs := ⟨nextAdjBase ws n, curAdjBase ws n, 2 * (n * n)⟩
    let s' := (Memory.spec 0).clientState s₀ (contractTablesProg ca)
    let a' := contractAdjTable a inCycle bEntry bExit x0 r
    let c' := contractReducedCostTable a c f inCycle bEntry bExit x0
    (iterationSafe contractOuterStep ContractOuterStepSafe w ca n 0 s₀ ∧
      iterationSafe copyStep CopyStepSafe w cp (2 * (n * n)) 0 s1) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (contractTablesProg ca)) ∧
      memoryCost (contractTablesProg ca) s₀ ≤ (16 * n + 1) * n + 4 * (n * n) ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(ws ≤ addr ∧ addr < ws + 4 * (n * n)) → s'.mem addr = s₀.mem addr) ∧
      (∀ u col : Fin n,
        s'.mem (curAdjBase ws n + u.1 * n + col.1) = if a'[u.1][col.1] then 1 else 0) ∧
      (∀ u col : Fin n,
        s'.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c'[u.1][col.1]) := by
  let ca : ContractArgs := ⟨n, r.1, x0.1, ws, k⟩
  have hf_pos : 0 < s₀.frontier := by have := r.pos; dsimp only [wsSize] at hf; nlinarith
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hfit_c' : ∀ u col : Fin n,
      Fits w (Signed.encode
        (contractReducedCostTable a c f inCycle bEntry bExit x0)[u.1][col.1]) := by
    intro u col
    have habs := contractReducedCostTable_natAbs_le a c f inCycle bEntry bExit x0 hB u col
    unfold Signed.encode
    exact hfit_diff.of_le (by split_ifs <;> linarith only [habs])
  have hloop := iterate_spec contractOuterStep ContractOuterStepSafe w ca (16 * n + 1) n
    (fun m idx s =>
      idx = m ∧ s.frontier = s₀.frontier ∧
        (∀ u col : Fin n,
          s.mem (curAdjBase ws n + u.1 * n + col.1) = if a[u.1][col.1] then 1 else 0) ∧
        (∀ u col : Fin n,
          s.mem (curCostBase ws n + u.1 * n + col.1) = Signed.encode c[u.1][col.1]) ∧
        (∀ y : Fin n, s.mem (frameMaskBase ws n k + y.1) = if inCycle[y.1] then 1 else 0) ∧
        (∀ x : Fin n, s.mem (frameParentBase ws n k + x.1) = (f[x.1]).1) ∧
        (∀ u : Fin n, s.mem (frameBEntryBase ws n k + u.1) = optFinIdx bEntry[u.1]) ∧
        (∀ col : Fin n, s.mem (frameBExitBase ws n k + col.1) = optFinIdx bExit[col.1]) ∧
        (∀ u col : Fin n, u.1 < m →
          s.mem (nextAdjBase ws n + u.1 * n + col.1) =
            (if (contractAdjTable a inCycle bEntry bExit x0 r)[u.1][col.1] then 1 else 0) ∧
          s.mem (nextCostBase ws n + u.1 * n + col.1) =
            Signed.encode
              (contractReducedCostTable a c f inCycle bEntry bExit x0)[u.1][col.1]))
    (fun addr => nextAdjBase ws n ≤ addr ∧ addr < nextCostBase ws n + n * n)
    (fun m hm idx s ⟨hidx, hfr, ha_s, hc_s, hm_s, hfp_s, hbe_s, hbx_s, hdone_o⟩ => by
      subst idx
      set uFin : Fin n := ⟨m, hm⟩
      let ra : ContractRowArgs := ⟨n, r.1, x0.1, m, ws, k⟩
      have hrow := fillContractRowProg_spec r x0 uFin a c f inCycle bEntry bExit s
        hk hws (by rw [hfr]; exact hf) hfit_diff ha_s hc_s hm_s hfp_s hbe_s hbx_s hB
      have hdisj_row : ∀ addr, addr < nextAdjBase ws n + m * n ∨
          nextAdjBase ws n + m * n + n ≤ addr ∧ addr < nextCostBase ws n + m * n ∨
          nextCostBase ws n + m * n + n ≤ addr →
          ((Memory.spec 0).clientState s (fillContractRowProg ra)).mem addr = s.mem addr :=
        fun addr h => hrow.2.2.2.2.1 addr
          (by dsimp only [uFin, nextAdjBase, nextCostBase] at h ⊢; omega)
      have hm_mul : m * n + n ≤ n * n := by
        simpa [Nat.succ_mul] using Nat.mul_le_mul_right n hm
      refine ⟨by dsimp only [ContractOuterStepSafe, ca]; exact ⟨hws.of_le
          (by dsimp only [wsSize]; omega), hrow.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold contractOuterStep
        dsimp only [ca]
        exact validHistory_read_bind (by omega)
          (validHistory_bind_step hrow.2.1 (validHistory_pure w _ _))
      · unfold contractOuterStep
        dsimp only [ca]
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
        have hc_r : memoryCost (fillContractRowProg ra) s ≤ 16 * n := hrow.2.2.1
        dsimp only [ra] at hc_r ⊢
        simp only [client_simps]
        omega
      · unfold contractOuterStep
        dsimp only [ca]
        have hrow_fr := hrow.2.2.2.1
        dsimp only [uFin] at hrow_fr
        simp [client_simps, hrow_fr, hfr]
      · intro addr haddr
        unfold contractOuterStep
        dsimp only [ca]
        simp only [client_simps]
        exact hrow.2.2.2.2.1 addr
          (by dsimp only [uFin, nextAdjBase, nextCostBase] at haddr ⊢; omega)
      · unfold contractOuterStep
        dsimp only [ca]
        have hrow_fr := hrow.2.2.2.1
        dsimp only [uFin] at hrow_fr
        simp only [client_simps]
        refine ⟨trivial, hrow_fr.trans hfr, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro u0 c0
          have := List.mul_add_lt_sq u0.isLt c0.isLt
          rw [hdisj_row _ (Or.inl (by dsimp only [curAdjBase, nextAdjBase]; omega))]
          exact ha_s u0 c0
        · intro u0 c0
          have := List.mul_add_lt_sq u0.isLt c0.isLt
          rw [hdisj_row _ (Or.inl (by dsimp only [curCostBase, nextAdjBase]; omega))]
          exact hc_s u0 c0
        · intro y
          have := y.isLt
          rw [hdisj_row _ (Or.inr (Or.inr
            (by dsimp only [frameMaskBase, frameBase, nextCostBase]; omega)))]
          exact hm_s y
        · intro x
          have := x.isLt
          rw [hdisj_row _ (Or.inr (Or.inr
            (by dsimp only [frameParentBase, frameBase, nextCostBase]; omega)))]
          exact hfp_s x
        · intro u0
          have := u0.isLt
          rw [hdisj_row _ (Or.inr (Or.inr
            (by dsimp only [frameBEntryBase, frameBase, nextCostBase]; omega)))]
          exact hbe_s u0
        · intro c0
          have := c0.isLt
          rw [hdisj_row _ (Or.inr (Or.inr
            (by dsimp only [frameBExitBase, frameBase, nextCostBase]; omega)))]
          exact hbx_s c0
        · intro u0 c0 hu0
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hu0) with hlt | heq
          · have hlt_mul : u0.1 * n + c0.1 < m * n := by
              have hc_lt := c0.isLt
              have hu_le : (u0.1 + 1) * n ≤ m * n := Nat.mul_le_mul_right n hlt
              linarith [Nat.succ_mul u0.1 n]
            rw [hdisj_row _ (Or.inl (by dsimp only [nextAdjBase]; omega)),
              hdisj_row _ (Or.inr (Or.inl (by dsimp only [nextAdjBase, nextCostBase]; omega)))]
            exact hdone_o u0 c0 hlt
          · have hu_eq : u0 = uFin := Fin.ext heq
            subst hu_eq
            exact hrow.2.2.2.2.2 c0)
    0 s₀ ⟨rfl, rfl, ha, hc, hm, hfp, hbe, hbx, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe_l, hvh_l, hmc_l, hs1_fr, hmod_l, _, _, _, _, _, _, _, _, hs1_cells⟩ := hloop
  set s1 := (Memory.spec 0).clientState s₀ (contractLoopProg ca)
  have hs1_fr' : s1.frontier = s₀.frontier := hs1_fr
  let cp : CopyArgs := ⟨nextAdjBase ws n, curAdjBase ws n, 2 * (n * n)⟩
  have hcopy := copyWordsProg_spec cp s1
    (by dsimp only [cp, wsSize, nextAdjBase] at hf ⊢; rw [hs1_fr']; omega)
    (by dsimp only [cp, wsSize, curAdjBase] at hf ⊢; rw [hs1_fr']; omega)
    (Or.inr (by dsimp only [cp, curAdjBase, nextAdjBase]; omega))
    (hws.of_le (by dsimp only [cp, wsSize, nextAdjBase]; omega))
    (hws.of_le (by dsimp only [cp, wsSize, curAdjBase]; omega))
    (hws.of_le (by dsimp only [cp, wsSize]; omega))
    (fun i hi => by
      dsimp only [cp] at hi ⊢
      by_cases hlt : i < n * n
      · set u0 : Fin n := ⟨i / n, Nat.div_lt_of_lt_mul hlt⟩
        set c0 : Fin n := ⟨i % n, Nat.mod_lt i r.pos⟩
        rw [show nextAdjBase ws n + i = nextAdjBase ws n + u0.1 * n + c0.1 by
          have := Nat.div_add_mod' i n; dsimp only [u0, c0]; omega]
        dsimp only [s1, contractLoopProg]
        rw [(hs1_cells u0 c0 u0.isLt).1]
        split_ifs <;> first | exact h1 | exact fits_zero w
      · set j := i - n * n
        have hj : j < n * n := by omega
        set u0 : Fin n := ⟨j / n, Nat.div_lt_of_lt_mul hj⟩
        set c0 : Fin n := ⟨j % n, Nat.mod_lt j r.pos⟩
        rw [show nextAdjBase ws n + i = nextCostBase ws n + u0.1 * n + c0.1 by
          have hdm : (j / n) * n + j % n = j := Nat.div_add_mod' j n
          dsimp only [u0, c0, nextAdjBase, nextCostBase]
          omega]
        dsimp only [s1, contractLoopProg]
        rw [(hs1_cells u0 c0 u0.isLt).2]
        exact hfit_c' u0 c0)
  unfold contractTablesProg
  refine ⟨⟨hsafe_l, hcopy.1⟩, validHistory_bind_step hvh_l hcopy.2.1,
    by
      rw [memoryCost_bind']
      have hl_c : memoryCost (contractLoopProg ca) s₀ ≤ (16 * n + 1) * n := hmc_l
      have hcp_c := hcopy.2.2.1
      dsimp only [ca, cp] at hl_c hcp_c ⊢
      nlinarith only [hl_c, hcp_c],
    by
      rw [StateTransitionSpec.clientState_bind]
      exact hcopy.2.2.2.1.trans hs1_fr',
    fun addr haddr => by
      rw [StateTransitionSpec.clientState_bind]
      rw [hcopy.2.2.2.2.1 addr (by dsimp only [cp, curAdjBase]; omega)]
      exact hmod_l addr (by dsimp only [nextAdjBase, nextCostBase]; omega),
    fun u col => by
      rw [StateTransitionSpec.clientState_bind]
      have hidx_lt : u.1 * n + col.1 < 2 * (n * n) := by
        have := List.mul_add_lt_sq u.isLt col.isLt; omega
      rw [show curAdjBase ws n + u.1 * n + col.1 = cp.dst + (u.1 * n + col.1) by
          dsimp only [cp, curAdjBase]; omega,
        hcopy.2.2.2.2.2 _ hidx_lt,
        show cp.src + (u.1 * n + col.1) = nextAdjBase ws n + u.1 * n + col.1 by
          dsimp only [cp, nextAdjBase]; omega]
      exact (hs1_cells u col u.isLt).1,
    fun u col => by
      rw [StateTransitionSpec.clientState_bind]
      have hidx_lt : n * n + (u.1 * n + col.1) < 2 * (n * n) := by
        have := List.mul_add_lt_sq u.isLt col.isLt; omega
      rw [show curCostBase ws n + u.1 * n + col.1 = cp.dst + (n * n + (u.1 * n + col.1)) by
          dsimp only [cp, curAdjBase, curCostBase]; omega,
        hcopy.2.2.2.2.2 _ hidx_lt,
        show cp.src + (n * n + (u.1 * n + col.1)) = nextCostBase ws n + u.1 * n + col.1 by
          dsimp only [cp, nextAdjBase, nextCostBase]; omega]
      exact (hs1_cells u col u.isLt).2⟩

end Cslib.Algorithms.WordRAM.Arborescence.Internal
