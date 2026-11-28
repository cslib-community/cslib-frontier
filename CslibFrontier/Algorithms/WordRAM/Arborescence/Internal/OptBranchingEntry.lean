/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.CoreSpec
import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.FinEnumBridges
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize

/-!
# Super-root reduction and `optimumBranchingProg` entry (internal)

Implements `superRootProg` (adding a super-root with zero-cost incoming arcs and reversing/negating
original arcs), `extractBranchingProg`, and `optimumBranchingProg`, together with
`Realizes .exact`, `inputFits_branching_encode`, and `optimumBranchingProg_spec`.
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

@[local client_simps] private theorem local_fst_snd_signedNegProg (w : ℕ)
    (s : Memory.State) (u : ℕ) :
    ((Memory.spec w).runClient s (signedNegProg u)).2.1 = s :=
  clientState_signedNegProg s u

private theorem init_mem_encode_branching_adj (I : BranchingInput) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (2 + (u.val * I.n + v.val)) = if I.adj u v then 1 else 0 := by
  rw [show 2 + (u.val * I.n + v.val) = ((u.val * I.n + v.val) + 1) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem (((u.val * I.n + v.val) + 1) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [BranchingInput.encode]
  rw [List.getD_cons_succ]
  have hlt : u.val * I.n + v.val < (flattenBoolMatrix I.n I.adj).length := by
    rw [length_flattenBoolMatrix]; exact List.mul_add_lt_sq u.isLt v.isLt
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt, ← List.getD_eq_getElem?_getD]
  exact getD_flattenBoolMatrix I.n I.adj u v

private theorem init_mem_encode_branching_wt (I : BranchingInput) (u v : Fin I.n) :
    (Memory.State.init I.encode).mem (2 + I.n * I.n + (u.val * I.n + v.val)) =
      Signed.encode (I.weight u v) := by
  rw [show 2 + I.n * I.n + (u.val * I.n + v.val) =
    ((I.n * I.n + (u.val * I.n + v.val)) + 1) + 1 by omega]
  change (Data.init (r := 0) I.encode).mem (((I.n * I.n + (u.val * I.n + v.val)) + 1) + 1) = _
  rw [Data.init_mem_succ]
  dsimp only [BranchingInput.encode]
  rw [List.getD_cons_succ]
  have hlen1 : (flattenBoolMatrix I.n I.adj).length = I.n * I.n :=
    length_flattenBoolMatrix I.n I.adj
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hlen1]; omega)]
  simp only [hlen1, Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact getD_flattenSignedMatrix I.n I.weight u v

public theorem inputFits_branching_encode {w M₀ : ℕ} (I : BranchingInput)
    (hM : ∀ u v, (I.weight u v).natAbs ≤ M₀) (hwb : Fits w (wordBound (I.n + 1) M₀)) :
    Fits w (I.encode.length + 1) ∧ InputFits w I.encode := by
  have hsq := sq_le_wordBound (I.n + 1) M₀
  have hlen : I.encode.length = 1 + 2 * (I.n * I.n) := by
    simp [BranchingInput.encode, length_flattenBoolMatrix, length_flattenSignedMatrix]
    omega
  have hfit_len1 : Fits w (I.encode.length + 1) :=
    hwb.of_le (by rw [hlen]; nlinarith only [hsq])
  refine ⟨hfit_len1, hfit_len1.of_le (by omega), fun x hx => ?_⟩
  simp only [BranchingInput.encode, List.mem_cons] at hx
  rcases hx with rfl | hrest
  · exact hwb.of_le (by nlinarith only [hsq])
  · exact fits_mem_flatten_adj_signed I.adj I.weight hM hwb hrest

private structure SuperRootRowArgs where
  n : ℕ
  x : ℕ
  ws : ℕ

private word_enc_structure encSuperRootRowArgs : SuperRootRowArgs where
  n : wordWords, x : wordWords, ws : wordWords

private instance : WordEncoding SuperRootRowArgs := ⟨3, encSuperRootRowArgs⟩

private def superRootRowStep (q : SuperRootRowArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let y := Prod.snd q
  let _ ← Memory.read 0
  let m := env.n + 1
  if env.x < env.n then
    if y < env.n then
      let a ← Memory.read (2 + y * env.n + env.x)
      let wtVal ← Memory.read (2 + env.n * env.n + y * env.n + env.x)
      let nw ← signedNegProg wtVal
      Memory.write (curAdjBase env.ws m + env.x * m + y) a
      Memory.write (curCostBase env.ws m + env.x * m + y) nw
      pure (y + 1)
    else
      Memory.write (curAdjBase env.ws m + env.x * m + y) 1
      Memory.write (curCostBase env.ws m + env.x * m + y) 0
      pure (y + 1)
  else
    Memory.write (curAdjBase env.ws m + env.x * m + y) 0
    Memory.write (curCostBase env.ws m + env.x * m + y) 0
    pure (y + 1)

private abbrev SuperRootRowStepSafe (w : ℕ) (q : SuperRootRowArgs × ℕ)
    (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let y := Prod.snd q
  let m := env.n + 1
  env.x < m ∧ y < m ∧ WsFits w env.ws m ∧ Fits w (2 + 2 * (env.n * env.n)) ∧
    (env.x < env.n → y < env.n →
      Fits w (s.mem (2 + env.n * env.n + y * env.n + env.x) + 1))

private theorem superRootRowStep_realizes :
    Realizes .exact superRootRowStep (appendWords encSuperRootRowArgs wordWords) wordWords
      SuperRootRowStepSafe (fun _ _ => 0) := by
  unfold superRootRowStep
  realize [signedNegProg_realizes]
  all_goals
    obtain ⟨hx_m, hy_m, hws, hin, hwt_fit⟩ := h
    first
    | exact hwt_fit ‹_› ‹_›
    | exact hin.of_le (by
        have : d.2 < d.1.n := ‹_›
        have : d.1.x < d.1.n := ‹_›
        nlinarith)
    | exact hws.of_le (by dsimp only [wsSize, curAdjBase, curCostBase]; nlinarith)

private def fillSuperRootRowProg (a : SuperRootRowArgs) : Memory.Prog ℕ :=
  iterate superRootRowStep a (a.n + 1) 0

private theorem fillSuperRootRowProg_realizes :
    Realizes .exact fillSuperRootRowProg encSuperRootRowArgs wordWords
      (fun w a s => iterationSafe superRootRowStep SuperRootRowStepSafe w a (a.n + 1) 0 s)
      (fun _ _ => 0) := by
  unfold fillSuperRootRowProg
  realize [superRootRowStep_realizes]
  all_goals first | exact h | exact h.1.2.2.1.of_le (by dsimp only [wsSize]; nlinarith)

private def superRootOuterStep (q : (ℕ × ℕ) × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let x := Prod.snd q
  let _ ← Memory.read 0
  let _ ← fillSuperRootRowProg ⟨Prod.fst env, x, Prod.snd env⟩
  pure (x + 1)

private abbrev SuperRootOuterStepSafe (w : ℕ) (q : (ℕ × ℕ) × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst q
  let x := Prod.snd q
  Fits w (x + 1) ∧
    iterationSafe superRootRowStep SuperRootRowStepSafe w ⟨Prod.fst env, x, Prod.snd env⟩
      (Prod.fst env + 1) 0 s

private theorem superRootOuterStep_realizes :
    Realizes .exact superRootOuterStep (appendWords pairWords wordWords) wordWords
      SuperRootOuterStepSafe (fun _ _ => 0) := by
  unfold superRootOuterStep
  realize [fillSuperRootRowProg_realizes]
  all_goals first | exact h.1 | exact h.2

private def superRootProg (d : ℕ × ℕ) : Memory.Prog ℕ :=
  iterate superRootOuterStep d (Prod.fst d + 1) 0

private theorem superRootProg_realizes :
    Realizes .exact superRootProg pairWords wordWords
      (fun w d s =>
        Fits w (Prod.fst d + 1) ∧
          iterationSafe superRootOuterStep SuperRootOuterStepSafe w d (Prod.fst d + 1) 0 s)
      (fun _ _ => 0) := by
  unfold superRootProg
  realize [superRootOuterStep_realizes]
  all_goals first | exact h.1 | exact h.2

private theorem fillSuperRootRowProg_spec {w n ws : ℕ} (xFin : Fin (n + 1))
    (G : Digraph (Fin n)) [DecidableRel G.Adj] (wt : Fin n → Fin n → ℤ) (s : Memory.State)
    (hws : WsFits w ws (n + 1)) (hin_fit : Fits w (2 + 2 * (n * n)))
    (hws_lo : 2 + 2 * (n * n) ≤ ws) (hf : ws + wsSize (n + 1) ≤ s.frontier)
    (hadj_in : ∀ u v : Fin n, s.mem (2 + (u.val * n + v.val)) = if decide (G.Adj u v) then 1 else 0)
    (hwt_in : ∀ u v : Fin n, s.mem (2 + n * n + (u.val * n + v.val)) = Signed.encode (wt u v))
    (hfit_wt1 : ∀ u v : Fin n, Fits w (Signed.encode (wt u v) + 1)) :
    let m := n + 1
    let ra : SuperRootRowArgs := ⟨n, xFin.val, ws⟩
    let sr' := (Memory.spec 0).clientState s (fillSuperRootRowProg ra)
    iterationSafe superRootRowStep SuperRootRowStepSafe w ra m 0 s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillSuperRootRowProg ra)) ∧
      memoryCost (fillSuperRootRowProg ra) s ≤ 5 * m ∧
      sr'.frontier = s.frontier ∧
      (∀ addr, ¬(curAdjBase ws m + xFin.val * m ≤ addr ∧ addr < curAdjBase ws m + xFin.val * m + m ∨
        curCostBase ws m + xFin.val * m ≤ addr ∧ addr < curCostBase ws m + xFin.val * m + m) →
        sr'.mem addr = s.mem addr) ∧
      (∀ y : Fin m,
        sr'.mem (curAdjBase ws m + xFin.val * m + y.val) =
          (if (superRootAdjFin G)[xFin.val][y.val] then 1 else 0) ∧
        sr'.mem (curCostBase ws m + xFin.val * m + y.val) =
          Signed.encode (superRootCostFin wt)[xFin.val][y.val]) := by
  let m := n + 1
  let ra : SuperRootRowArgs := ⟨n, xFin.val, ws⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hx_lt := xFin.isLt
  have hrow := iterate_spec superRootRowStep SuperRootRowStepSafe w ra 5 m
    (fun y idxR sr =>
      idxR = y ∧ sr.frontier = s.frontier ∧
        (∀ u v : Fin n, sr.mem (2 + (u.val * n + v.val)) = if decide (G.Adj u v) then 1 else 0) ∧
        (∀ u v : Fin n, sr.mem (2 + n * n + (u.val * n + v.val)) = Signed.encode (wt u v)) ∧
        (∀ y0 : Fin m, y0.val < y →
          sr.mem (curAdjBase ws m + xFin.val * m + y0.val) =
            (if (superRootAdjFin G)[xFin.val][y0.val] then 1 else 0) ∧
          sr.mem (curCostBase ws m + xFin.val * m + y0.val) =
            Signed.encode (superRootCostFin wt)[xFin.val][y0.val]))
    (fun addr => curAdjBase ws m + xFin.val * m ≤ addr ∧ addr < curAdjBase ws m + xFin.val * m + m ∨
      curCostBase ws m + xFin.val * m ≤ addr ∧ addr < curCostBase ws m + xFin.val * m + m)
    (fun y hy idxR sr ⟨hidxR, hfr_r, ha_r, hwt_r, hdone_r⟩ => by
      subst idxR
      have hcell_xy := List.mul_add_lt_sq hx_lt hy
      have ha_yx (hy_n : y < n) (hx_n : xFin.val < n) : sr.mem (2 + y * n + xFin.val) =
          if decide (G.Adj ⟨y, hy_n⟩ ⟨xFin.val, hx_n⟩) then 1 else 0 := by
        simpa [Nat.add_assoc] using ha_r ⟨y, hy_n⟩ ⟨xFin.val, hx_n⟩
      have hw_yx (hy_n : y < n) (hx_n : xFin.val < n) : sr.mem (2 + n * n + y * n + xFin.val) =
          Signed.encode (wt ⟨y, hy_n⟩ ⟨xFin.val, hx_n⟩) := by
        simpa [Nat.add_assoc] using hwt_r ⟨y, hy_n⟩ ⟨xFin.val, hx_n⟩
      -- The step writes the two cells `(x, y)` of the super-root tables and nothing else.
      have hstep : (Memory.spec 0).clientResult sr (superRootRowStep (ra, y)) = y + 1 ∧
          (Memory.spec 0).clientState sr (superRootRowStep (ra, y)) =
            ⟨Function.update (Function.update sr.mem (curAdjBase ws m + xFin.val * m + y)
                (if (superRootAdjFin G)[xFin.val][y] then 1 else 0))
              (curCostBase ws m + xFin.val * m + y)
              (Signed.encode (superRootCostFin wt)[xFin.val][y]),
              sr.frontier⟩ := by
        unfold superRootRowStep
        dsimp only [ra, m]
        by_cases hx_n : xFin.val < n
        · by_cases hy_n : y < n
          · simp only [hx_n, hy_n, ↓reduceIte, client_simps, hw_yx hy_n hx_n, ha_yx hy_n hx_n,
              clientResult_signedNegProg]
            simp [superRootAdjFin, superRootCostFin, initAdjTable, initCostTable, hx_n, hy_n]
          · simp [hx_n, hy_n, client_simps, superRootAdjFin, superRootCostFin, initAdjTable,
              initCostTable, Signed.encode]
        · simp [hx_n, client_simps, superRootAdjFin, superRootCostFin, initAdjTable,
            initCostTable, Signed.encode]
      have hfr_step : ((Memory.spec 0).clientState sr (superRootRowStep (ra, y))).frontier =
          sr.frontier := by rw [hstep.2]
      have hout : ∀ addr, ¬(curAdjBase ws m + xFin.val * m ≤ addr ∧
          addr < curAdjBase ws m + xFin.val * m + m ∨ curCostBase ws m + xFin.val * m ≤ addr ∧
          addr < curCostBase ws m + xFin.val * m + m) →
          ((Memory.spec 0).clientState sr (superRootRowStep (ra, y))).mem addr = sr.mem addr :=
        fun addr h => by
          rw [hstep.2]
          dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have hwr (a c : ℕ) (ha : Fits w a) (hc : Fits w c) :
          (Memory.spec w).ValidHistory sr ((Memory.spec w).clientHistory sr
            (do Memory.write (curAdjBase ws m + xFin.val * m + y) a
                Memory.write (curCostBase ws m + xFin.val * m + y) c
                pure (y + 1))) :=
        validHistory_write_bind
          (by dsimp only [wsSize, curAdjBase, m] at hf hfr_r hcell_xy ⊢; omega) ha
          (validHistory_write_bind
            (by dsimp only [wsSize, curCostBase, m] at hf hfr_r hcell_xy ⊢; omega) hc
            (validHistory_pure w _ _))
      refine ⟨by
          dsimp only [SuperRootRowStepSafe, ra]
          refine ⟨hx_lt, hy, hws, hin_fit, fun hx_n hy_n => ?_⟩
          rw [hw_yx hy_n hx_n]
          exact hfit_wt1 ⟨y, hy_n⟩ ⟨xFin.val, hx_n⟩,
        ?_, ?_, hfr_step, hout, hstep.1, hfr_step.trans hfr_r,
        fun u v => ?_, fun u v => ?_, fun y0 hy0 => ?_⟩
      · unfold superRootRowStep
        dsimp only [ra]
        refine validHistory_read_bind (by dsimp only [wsSize, m] at hf hfr_r ⊢; omega) ?_
        by_cases hx_n : xFin.val < n
        · simp only [hx_n, ↓reduceIte]
          by_cases hy_n : y < n
          · simp only [hy_n, ↓reduceIte]
            have hcell_in := List.mul_add_lt_sq hy_n hx_n
            refine validHistory_read_bind
              (by dsimp only [wsSize, m] at hf hfr_r hws_lo hcell_in ⊢; omega)
              (validHistory_read_bind
                (by dsimp only [wsSize, m] at hf hfr_r hws_lo hcell_in ⊢; omega) ?_)
            refine validHistory_bind_step (validHistory_signedNegProg w _ _) ?_
            rw [clientState_signedNegProg, hw_yx hy_n hx_n, clientResult_signedNegProg]
            refine hwr _ _
              (by rw [ha_yx hy_n hx_n]; split_ifs <;> first | exact h1 | exact fits_zero w) ?_
            have hfit1 := hfit_wt1 ⟨y, hy_n⟩ ⟨xFin.val, hx_n⟩
            unfold Signed.encode at hfit1 ⊢
            rw [Int.natAbs_neg]
            exact hfit1.of_le (by split_ifs <;> omega)
          · simp only [hy_n, ↓reduceIte]
            exact hwr _ _ h1 (fits_zero w)
        · simp only [hx_n, ↓reduceIte]
          exact hwr _ _ (fits_zero w) (fits_zero w)
      · unfold superRootRowStep
        dsimp only [ra]
        by_cases hx_n : xFin.val < n <;> by_cases hy_n : y < n <;>
          simp only [hx_n, hy_n, ↓reduceIte, client_simps] <;> omega
      · have := List.mul_add_lt_sq u.isLt v.isLt
        exact (hout _ (by dsimp only [curAdjBase, curCostBase, m]; omega)).trans (ha_r u v)
      · have := List.mul_add_lt_sq u.isLt v.isLt
        exact (hout _ (by dsimp only [curAdjBase, curCostBase, m]; omega)).trans (hwt_r u v)
      · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hy0) with hlt | rfl
        · rw [hstep.2]
          dsimp only
          rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
            Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
            Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
            Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega)]
          exact hdone_r y0 hlt
        · rw [hstep.2]
          refine ⟨?_, Function.update_self ..⟩
          dsimp only
          rw [Function.update_of_ne (by dsimp only [curAdjBase, curCostBase, m]; omega),
            Function.update_self])
    0 s ⟨rfl, rfl, hadj_in, hwt_in, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, hmod_end, _, _, _, _, hdone_end⟩ := hrow
  unfold fillSuperRootRowProg
  exact ⟨hsafe, hvh, hmc, hfr_end, hmod_end, fun y => hdone_end y y.isLt⟩

private theorem superRootProg_spec {w n ws : ℕ}
    (G : Digraph (Fin n)) [DecidableRel G.Adj] (wt : Fin n → Fin n → ℤ) (s₀ : Memory.State)
    (hws : WsFits w ws (n + 1)) (hin_fit : Fits w (2 + 2 * (n * n)))
    (hws_lo : 2 + 2 * (n * n) ≤ ws) (hf : ws + wsSize (n + 1) ≤ s₀.frontier)
    (hadj_in : ∀ u v : Fin n,
      s₀.mem (2 + (u.val * n + v.val)) = if decide (G.Adj u v) then 1 else 0)
    (hwt_in : ∀ u v : Fin n, s₀.mem (2 + n * n + (u.val * n + v.val)) = Signed.encode (wt u v))
    (hfit_wt1 : ∀ u v : Fin n, Fits w (Signed.encode (wt u v) + 1)) :
    let m := n + 1
    let s' := (Memory.spec 0).clientState s₀ (superRootProg (n, ws))
    (Fits w m ∧ iterationSafe superRootOuterStep SuperRootOuterStepSafe w (n, ws) m 0 s₀) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (superRootProg (n, ws))) ∧
      memoryCost (superRootProg (n, ws)) s₀ ≤ (5 * m + 1) * m ∧
      s'.frontier = s₀.frontier ∧
      (∀ x y : Fin m,
        s'.mem (curAdjBase ws m + x.val * m + y.val) =
          if (superRootAdjFin G)[x.val][y.val] then 1 else 0) ∧
      (∀ x y : Fin m,
        s'.mem (curCostBase ws m + x.val * m + y.val) =
          Signed.encode (superRootCostFin wt)[x.val][y.val]) := by
  let m := n + 1
  have hfit_m : Fits w m := hws.of_le (by dsimp only [wsSize, m]; nlinarith)
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec superRootOuterStep SuperRootOuterStepSafe w (n, ws) (5 * m + 1) m
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ u v : Fin n, s.mem (2 + (u.val * n + v.val)) = if decide (G.Adj u v) then 1 else 0) ∧
        (∀ u v : Fin n, s.mem (2 + n * n + (u.val * n + v.val)) = Signed.encode (wt u v)) ∧
        (∀ x y : Fin m, x.val < k →
          s.mem (curAdjBase ws m + x.val * m + y.val) =
            (if (superRootAdjFin G)[x.val][y.val] then 1 else 0) ∧
          s.mem (curCostBase ws m + x.val * m + y.val) =
            Signed.encode (superRootCostFin wt)[x.val][y.val]))
    (fun addr => curAdjBase ws m ≤ addr ∧ addr < curCostBase ws m + m * m)
    (fun k hk idx s ⟨hidx, hfr, ha_s, hwt_s, hdone_o⟩ => by
      subst idx
      let xFin : Fin m := ⟨k, hk⟩
      have hrow := fillSuperRootRowProg_spec xFin G wt s hws hin_fit hws_lo
        (by rw [hfr]; exact hf) ha_s hwt_s hfit_wt1
      have hdisj : ∀ addr, addr < curAdjBase ws m + k * m ∨
          curAdjBase ws m + k * m + m ≤ addr ∧ addr < curCostBase ws m + k * m ∨
          curCostBase ws m + k * m + m ≤ addr →
          ((Memory.spec 0).clientState s (fillSuperRootRowProg ⟨n, k, ws⟩)).mem addr =
            s.mem addr :=
        fun addr h => hrow.2.2.2.2.1 addr
          (by dsimp only [xFin, curAdjBase, curCostBase, m] at h ⊢; omega)
      refine ⟨by dsimp only [SuperRootOuterStepSafe]; exact ⟨hws.of_le
          (by dsimp only [wsSize, m] at hk ⊢; nlinarith), hrow.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold superRootOuterStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_bind_step hrow.2.1 (validHistory_pure w _ _))
      · unfold superRootOuterStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind']
        have hc_r : memoryCost (fillSuperRootRowProg ⟨n, k, ws⟩) s ≤ 5 * m := hrow.2.2.1
        simp only [client_simps]
        omega
      · unfold superRootOuterStep
        dsimp only
        have hrow_fr := hrow.2.2.2.1
        dsimp only [xFin] at hrow_fr
        simp [client_simps, hrow_fr, hfr]
      · intro addr haddr
        unfold superRootOuterStep
        dsimp only
        simp only [client_simps]
        exact hrow.2.2.2.2.1 addr
          (by have hmul_le := Nat.mul_le_mul_right m (Nat.succ_le_of_lt hk)
              rw [Nat.succ_mul] at hmul_le
              dsimp only [xFin, curAdjBase, curCostBase, m] at hmul_le haddr ⊢
              omega)
      · unfold superRootOuterStep
        dsimp only
        have hrow_fr := hrow.2.2.2.1
        dsimp only [xFin] at hrow_fr
        simp only [client_simps]
        refine ⟨trivial, hrow_fr.trans hfr, ?_, ?_, ?_⟩
        · intro u v
          have := List.mul_add_lt_sq u.isLt v.isLt
          rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega))]
          exact ha_s u v
        · intro u v
          have := List.mul_add_lt_sq u.isLt v.isLt
          rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega))]
          exact hwt_s u v
        · intro x0 y0 hx0
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hx0) with hlt | heq
          · have hlt_mul : x0.val * m + y0.val < k * m := by
              have := y0.isLt
              have := Nat.mul_le_mul_right m hlt
              linarith [Nat.succ_mul x0.val m]
            have hk_mul : k * m + m ≤ m * m := by
              simpa [Nat.succ_mul] using Nat.mul_le_mul_right m hk
            rw [hdisj _ (Or.inl (by dsimp only [curAdjBase]; omega)),
              hdisj _ (Or.inr (Or.inl (by dsimp only [curAdjBase, curCostBase]; omega)))]
            exact hdone_o x0 y0 hlt
          · have hx_eq : x0 = xFin := Fin.ext heq
            subst hx_eq
            exact hrow.2.2.2.2.2 y0)
    0 s₀ ⟨rfl, rfl, hadj_in, hwt_in, fun _ _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_end, _, _, _, _, _, hdone_end⟩ := h
  unfold superRootProg
  exact ⟨⟨hfit_m, hsafe⟩, hvh, hmc, hfr_end,
    fun x y => (hdone_end x y x.isLt).1,
    fun x y => (hdone_end x y x.isLt).2⟩

private structure ExtractArgs where
  n : ℕ
  src : ℕ
  dst : ℕ

private word_enc_structure encExtractArgs : ExtractArgs where
  n : wordWords, src : wordWords, dst : wordWords

private instance : WordEncoding ExtractArgs := ⟨3, encExtractArgs⟩

private def extractBranchingStep (q : ExtractArgs × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst q
  let v := Prod.snd q
  let pv ← Memory.read (env.src + v)
  let outVal := if pv < env.n then pv else v
  Memory.write (env.dst + v) outVal
  pure (v + 1)

private abbrev ExtractStepSafe (w : ℕ) (q : ExtractArgs × ℕ) (_ : Memory.State) : Prop :=
  let env := Prod.fst q
  let v := Prod.snd q
  Fits w (env.src + v) ∧ Fits w (env.dst + v) ∧ Fits w (v + 1)

private theorem extractBranchingStep_realizes :
    Realizes .exact extractBranchingStep (appendWords encExtractArgs wordWords) wordWords
      ExtractStepSafe (fun _ _ => 0) := by
  unfold extractBranchingStep
  realize
  all_goals first | exact h.1 | exact h.2.1 | exact h.2.2

private def extractBranchingProg (a : ExtractArgs) : Memory.Prog ℕ :=
  iterate extractBranchingStep a a.n 0

private theorem extractBranchingProg_realizes :
    Realizes .exact extractBranchingProg encExtractArgs wordWords
      (fun w a s => iterationSafe extractBranchingStep ExtractStepSafe w a a.n 0 s)
      (fun _ _ => 0) := by
  unfold extractBranchingProg
  realize [extractBranchingStep_realizes]
  exact h

private theorem extractBranchingProg_spec {w : ℕ} (a : ExtractArgs) (s₀ : Memory.State)
    (hsrc_f : a.src + a.n ≤ s₀.frontier) (hdst_f : a.dst + a.n ≤ s₀.frontier)
    (hdisj : a.src + a.n ≤ a.dst)
    (hfit_src : Fits w (a.src + a.n)) (hfit_dst : Fits w (a.dst + a.n))
    (hfit_n : Fits w a.n) :
    let s' := (Memory.spec 0).clientState s₀ (extractBranchingProg a)
    iterationSafe extractBranchingStep ExtractStepSafe w a a.n 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (extractBranchingProg a)) ∧
      memoryCost (extractBranchingProg a) s₀ ≤ 2 * a.n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(a.dst ≤ addr ∧ addr < a.dst + a.n) → s'.mem addr = s₀.mem addr) ∧
      (∀ i < a.n, s'.mem (a.dst + i) =
        if s₀.mem (a.src + i) < a.n then s₀.mem (a.src + i) else i) := by
  have h := iterate_spec extractBranchingStep ExtractStepSafe w a 2 a.n
    (fun k idx s =>
      idx = k ∧ s.frontier = s₀.frontier ∧
        (∀ j < a.n, s.mem (a.src + j) = s₀.mem (a.src + j)) ∧
        (∀ j < k, s.mem (a.dst + j) =
          if s₀.mem (a.src + j) < a.n then s₀.mem (a.src + j) else j))
    (fun addr => a.dst ≤ addr ∧ addr < a.dst + a.n)
    (fun k hk idx s ⟨hidx, hfr, hsrc_eq, hdone⟩ => by
      subst idx
      have hk_val := hsrc_eq k hk
      refine ⟨by dsimp only [ExtractStepSafe]; exact ⟨hfit_src.of_le (by omega),
          hfit_dst.of_le (by omega), hfit_n.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold extractBranchingStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_write_bind (by omega)
            (by split_ifs <;> exact hfit_n.of_le (by omega))
            (validHistory_pure w _ _))
      · unfold extractBranchingStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [extractBranchingStep, client_simps, hfr]
      · intro addr haddr
        simp only [extractBranchingStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · unfold extractBranchingStep
        dsimp only
        simp only [client_simps, hk_val]
        refine ⟨trivial, hfr, ?_, ?_⟩
        · intro j hj
          rw [Function.update_of_ne (by omega)]
          exact hsrc_eq j hj
        · intro j hj
          by_cases heq : j = k
          · subst heq; simp
          · rw [Function.update_of_ne (by omega)]
            exact hdone j (by omega))
    0 s₀ ⟨rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe, hvh, hmc, hfr_e, hmod_e, _, _, _, hdone_e⟩ := h
  unfold extractBranchingProg
  exact ⟨hsafe, hvh, hmc, hfr_e, hmod_e, hdone_e⟩

/-- Word-RAM entry program solving maximum-weight branching on `n` vertices via the `(n + 1)`-node
super-root reduction to `edmondsCoreProg`. -/
public def optimumBranchingProg (n : ℕ) : Memory.Prog ℕ := do
  let m := n + 1
  let ws ← Memory.allocDirty (wsSize m)
  let outAddr ← Memory.allocDirty (n + 1)
  let _ ← superRootProg (n, ws)
  let _ ← edmondsCoreProg ⟨m, n, ws⟩
  Memory.write outAddr n
  let _ ← extractBranchingProg ⟨n, curParentBase ws m, outAddr + 1⟩
  pure outAddr

/-- Safety precondition for `optimumBranchingProg`. -/
public def OptimumBranchingProgSafe (w n : ℕ) (s₀ : Memory.State) : Prop :=
  let m := n + 1
  let ws := s₀.frontier
  let outAddr := ws + wsSize m
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  let s3 := (Memory.spec 0).clientState s1 (superRootProg (n, ws))
  let ca : CoreArgs := ⟨m, n, ws⟩
  let res := (Memory.spec 0).clientResult s3 (forwardProg ca)
  let sf := (Memory.spec 0).clientState s3 (forwardProg ca)
  let s4 := (Memory.spec 0).clientState s3 (edmondsCoreProg ca)
  let s4w : Memory.State := ⟨Function.update s4.mem outAddr n, s4.frontier⟩
  Fits w (outAddr + (n + 1) + 8) ∧
    iterationSafe superRootOuterStep SuperRootOuterStepSafe w (n, ws) m 0 s1 ∧
    iterationSafe forwardStep ForwardStepSafe w ca m ⟨0, 0, 0⟩ s3 ∧
    (res.status = 1 →
      iterationSafe backwardStep BackwardStepSafe w ⟨m, ws, res.depth⟩ res.depth 0 sf) ∧
    iterationSafe extractBranchingStep ExtractStepSafe w
      ⟨n, curParentBase ws m, outAddr + 1⟩ n 0 s4w

public theorem optimumBranchingProg_realizes :
    Realizes .exact optimumBranchingProg wordWords wordWords
      OptimumBranchingProgSafe (fun _ _ => 0) := by
  unfold optimumBranchingProg
  realize [superRootProg_realizes, edmondsCoreProg_realizes, extractBranchingProg_realizes]
  all_goals
    obtain ⟨hfit, hsr, hfwd, hbwd, hext⟩ := h
    first
    | exact hsr
    | exact hfwd
    | exact hbwd
    | exact hext
    | exact hfit.of_le (by dsimp only [wsSize, curParentBase, frameBase]; nlinarith)

public theorem optimumBranchingProg_spec {w M₀ : ℕ} (I : BranchingInput)
    (hM : ∀ u v, (I.weight u v).natAbs ≤ M₀) (hwb : Fits w (wordBound (I.n + 1) M₀)) :
    let s₀ := Memory.State.init I.encode
    let n := I.n
    let outAddr := (Memory.spec 0).clientResult s₀ (optimumBranchingProg n)
    let s' := (Memory.spec 0).clientState s₀ (optimumBranchingProg n)
    OptimumBranchingProgSafe w n s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (optimumBranchingProg n)) ∧
      memoryCost (optimumBranchingProg n) s₀ ≤
        43 * (I.n + 1) ^ 3 + 23 * (I.n + 1) ^ 2 + 9 * (I.n + 1) + 3 ∧
      outputList s'.mem outAddr = I.expectedParentList ∧
      Fits w (outAddr + I.expectedParentList.length) := by
  rcases I with ⟨n, adj, weight⟩
  let I : BranchingInput := ⟨n, adj, weight⟩
  let m := n + 1
  set s₀ := Memory.State.init I.encode
  let ws := s₀.frontier
  let outAddr := ws + wsSize m
  have hws_eq : ws = 2 + 2 * (n * n) := by
    change I.encode.length + 1 = _
    simp [I, BranchingInput.encode, length_flattenBoolMatrix, length_flattenSignedMatrix]
    omega
  have hfit_top : Fits w (outAddr + (n + 1) + 8) :=
    hwb.of_le (by
      have hsq := sq_le_wordBound (n + 1) M₀
      dsimp only [outAddr, ws, m, wsSize] at hws_eq ⊢
      rw [hws_eq]
      nlinarith only [hsq])
  have hws_fit : WsFits w ws m := hfit_top.of_le (by dsimp only [outAddr, ws]; omega)
  let s1 : Memory.State := ⟨s₀.mem, outAddr + (n + 1)⟩
  have hfit_wt1 : ∀ u v : Fin n, Fits w (Signed.encode (weight u v) + 1) :=
    fun u v => fits_signedEncode_add_one_of_wordBound (hM u v) hwb
  let G : Digraph (Fin n) := BranchingInput.digraph ⟨n, adj, weight⟩
  have hsr := superRootProg_spec G weight s1 hws_fit
    (hfit_top.of_le (by dsimp only [outAddr, ws, m, wsSize] at hws_eq ⊢; rw [hws_eq]; nlinarith))
    (by rw [hws_eq])
    (by dsimp only [s1, outAddr, ws, m]; omega)
    (fun u v => by
      change (Memory.State.init I.encode).mem (2 + (u.val * I.n + v.val)) = _
      rw [init_mem_encode_branching_adj I u v]
      simp [I, G, BranchingInput.digraph])
    (fun u v => init_mem_encode_branching_wt I u v)
    hfit_wt1
  let s3 := (Memory.spec 0).clientState s1 (superRootProg (n, ws))
  have hs3_fr : s3.frontier = outAddr + (n + 1) := hsr.2.2.2.1
  let a₀ := superRootAdjFin G
  let c₀ := superRootCostFin weight
  have hB₀ : ∀ x y : Fin m, (c₀[x.val][y.val]).natAbs ≤ M₀ := by
    intro x y
    simp only [c₀, superRootCostFin, initCostTable, Vector.getElem_ofFn]
    split_ifs with hx hy
    · rw [Int.natAbs_neg]
      exact hM ⟨y.val, hy⟩ ⟨x.val, hx⟩
    · simp
    · simp
  have hcore := edmondsCoreProg_spec (Fin.last n) a₀ c₀ s3 hws_fit
    (by rw [hs3_fr]; dsimp only [outAddr, ws, m]; omega) hwb
    hsr.2.2.2.2.1 hsr.2.2.2.2.2 hB₀
  let ca : CoreArgs := ⟨m, n, ws⟩
  let s4 := (Memory.spec 0).clientState s3 (edmondsCoreProg ca)
  have hs4_fr : s4.frontier = outAddr + (n + 1) := hcore.2.2.2.1.trans hs3_fr
  obtain ⟨pTab, haux, hp_val⟩ := optimumBranchingParent_fin_eq G weight
  have hcore_res : (Memory.spec 0).clientResult s3 (edmondsCoreProg ca) = 1 ∧
       ∀ v : Fin m, s4.mem (curParentBase ws m + v.val) = (pTab[v.val]).val := by
    have h := hcore.2.2.2.2.2
    rwa [show edmondsTableAux (Fin.last n) m a₀ c₀ = some pTab from haux] at h
  let s4w : Memory.State := ⟨Function.update s4.mem outAddr n, s4.frontier⟩
  let extA : ExtractArgs := ⟨n, curParentBase ws m, outAddr + 1⟩
  have hext := extractBranchingProg_spec extA s4w
    (by dsimp only [extA, s4w]; rw [hs4_fr]; dsimp only [outAddr, ws, m, wsSize, curParentBase];
        nlinarith)
    (by dsimp only [extA, s4w]; rw [hs4_fr]; dsimp only [outAddr, ws]; omega)
    (by dsimp only [extA, outAddr, ws, m, wsSize, curParentBase]; nlinarith)
    (hfit_top.of_le (by dsimp only [extA, outAddr, ws, m, wsSize, curParentBase]; nlinarith))
    (hfit_top.of_le (by dsimp only [extA, outAddr, ws]; omega))
    (hfit_top.of_le (by dsimp only [extA, outAddr, ws]; omega))
  have hsafe : OptimumBranchingProgSafe w n s₀ :=
    ⟨hfit_top, hsr.1.2, hcore.1.2.1, hcore.1.2.2, hext.1⟩
  unfold optimumBranchingProg
  dsimp only [I]
  refine ⟨hsafe, ?_, ?_, ?_, ?_⟩
  · refine validHistory_allocDirty_bind
      (hfit_top.of_le (by dsimp only [outAddr, ws, m]; omega))
      (validHistory_allocDirty_bind
        (hfit_top.of_le (by dsimp only [outAddr, ws, m]; omega)) ?_)
    refine validHistory_bind_step hsr.2.1 (validHistory_bind_step hcore.2.1 ?_)
    exact validHistory_write_bind (by rw [hs4_fr]; dsimp only [outAddr, ws, m]; omega)
      (hfit_top.of_le (by dsimp only [outAddr, ws, m]; omega))
      (validHistory_bind_step hext.2.1 (validHistory_pure w _ _))
  · rw [memoryCost_bind', memoryCost_allocDirty]
    simp only [memoryCost_write, client_simps]
    have cSr := hsr.2.2.1
    have cCore := hcore.2.2.1
    have cExt := hext.2.2.1
    dsimp only [s4w, s4, s3, s1, ca, extA, outAddr, ws, m, I] at cSr cCore cExt ⊢
    have hid : 1 + (1 + ((5 * (n + 1) + 1) * (n + 1) +
        ((43 * (n + 1) ^ 3 + 18 * (n + 1) ^ 2 + 6 * (n + 1)) + (1 + (2 * n + 0))))) + 2 =
        43 * (n + 1) ^ 3 + 23 * (n + 1) ^ 2 + 9 * (n + 1) + 3 := by ring
    linarith only [cSr, cCore, cExt, hid]
  · have hext_m := hext.2.2.2.2.1
    have hext_v := hext.2.2.2.2.2
    have hcore_m := hcore_res.2
    unfold BranchingInput.expectedParentList
    dsimp only [s4w, s4, s3, s1, ca, extA, outAddr, ws, m, I, G] at hext_m hext_v hcore_m hp_val ⊢
    simp only [client_simps]
    rw [outputList_eq_iff]
    refine ⟨?_, fun i => ?_⟩
    · simp only [List.length_map, List.length_finRange]
      rw [hext_m (s₀.frontier + wsSize (n + 1)) (by omega)]
      exact Function.update_self _ _ _
    · have hi : i.val < n := by simpa using i.isLt
      change ((Memory.spec 0).clientState _ _).mem (s₀.frontier + wsSize (n + 1) + 1 + i.val) =
        ((List.finRange n).map fun v =>
          (optimumBranchingParent (BranchingInput.digraph ⟨n, adj, weight⟩) weight v).val)[i.val]
      simp only [List.getElem_map, List.getElem_finRange]
      rw [hext_v i.val hi, hp_val]
      have hval_i :
          (Function.update
            ((Memory.spec 0).clientState
              ((Memory.spec 0).clientState
                { mem := s₀.mem, frontier := s₀.frontier + wsSize (n + 1) + (n + 1) }
                (superRootProg (n, s₀.frontier)))
              (edmondsCoreProg { n := n + 1, r := n, ws := s₀.frontier })).mem
            (s₀.frontier + wsSize (n + 1)) n)
            (curParentBase s₀.frontier (n + 1) + i.val) =
          (pTab[i.val]).val := by
        rw [Function.update_of_ne (by dsimp only [wsSize, curParentBase]; omega)]
        exact hcore_m ⟨i.val, by omega⟩
      simp [hval_i]
  · simp only [client_simps, BranchingInput.expectedParentList, List.length_map,
      List.length_finRange]
    exact hfit_top.of_le (by dsimp only [outAddr, ws, m]; omega)

end Cslib.Algorithms.WordRAM.Arborescence.Internal
