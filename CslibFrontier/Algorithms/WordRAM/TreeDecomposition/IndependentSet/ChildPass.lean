/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.InstDP
public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.IndepScan
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.MaskOps
import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet.WeightScan
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize

/-!
# Child-to-parent DP table projection pass (`childPassProg`)

This module certifies the child pass `childPassProg`, which iterates over all `2 ^ |LB|` child masks
`curC`, checks pairwise independence (`indepBagProg`), transfers `curC` to its parent-bag mask
(`keyMaskProg`), computes the forgotten-vertex weight (`forgetWeightProg`), and updates the scratch
array `best` at `bestPtr + key` with the maximum of its previous value and `fw + tblB[curC]`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.childPassList`: `List ℕ` mirror of `childPassInst`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.ChildPassArgs`: register arguments for
  `childPassProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.childPassProg`: Word-RAM child-to-parent projection
  loop.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.getD_childPassList_eq`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.mem_childPassList_le`: agreement with `childPassInst`
  and entry upper bound.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.childPassProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.childPassProg_realizes`: functional correctness,
  framing below `bestPtr`, quadratic-per-mask cost bound, and exact-basis realization certificate.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### List mirror of `childPassInst` -/

/-- `List ℕ` counterpart of `childPassInst` matching contiguous `HoldsIn` blocks in memory. -/
def childPassList (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ) (LB LP tblB init : List ℕ) :
    ℕ → List ℕ
  | 0 => init
  | c + 1 =>
    let best := childPassList adj wt LB LP tblB init c
    if indepInst adj LB c then
      let key := keyMask LB LP c
      best.set key (max (best.getD key 0) (forgetWeight wt LP LB c + tblB.getD c 0))
    else
      best

/-- `childPassList` preserves the length of `init`. -/
theorem length_childPassList (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ)
    (LB LP tblB init : List ℕ) (c : ℕ) :
    (childPassList adj wt LB LP tblB init c).length = init.length := by
  induction c with
  | zero => rfl
  | succ c ih =>
    dsimp only [childPassList]
    split_ifs
    · rw [List.length_set, ih]
    · exact ih

/-- `childPassList` agrees entrywise with `childPassInst` on `0 .. 2 ^ |LP| - 1`. -/
theorem getD_childPassList_eq (adj : ℕ → ℕ → Bool) (wt : ℕ → ℕ)
    (LB LP tblB : List ℕ) (f : Array ℕ) (c : ℕ)
    (htbl : ∀ t < c, tblB.getD t 0 = f.getD t 0) :
    ∀ k < 2 ^ LP.length,
      (childPassList adj wt LB LP tblB (List.replicate (2 ^ LP.length) 0) c).getD k 0 =
        (childPassInst adj wt LB LP f (Array.replicate (2 ^ LP.length) 0) c).getD k 0 := by
  induction c with
  | zero =>
    intro k hk
    simp only [childPassList, childPassInst, List.getD_eq_getElem?_getD,
      List.getElem?_replicate, Array.getD_eq_getD_getElem?, Array.getElem?_replicate,
      hk, ↓reduceIte, Option.getD_some]
  | succ c ih =>
    intro k hk
    have hih := ih fun t ht => htbl t (Nat.lt_succ_of_lt ht)
    dsimp only [childPassList, childPassInst]
    split_ifs with hind
    · have hkey_lt : keyMask LB LP c < 2 ^ LP.length := keyMask_lt_two_pow LB LP c
      rw [List.getD_eq_getElem?_getD, List.getElem?_set, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds]
      rcases eq_or_ne (keyMask LB LP c) k with rfl | hne
      · simp only [↓reduceIte, length_childPassList, List.length_replicate,
          size_childPassInst, Array.size_replicate, hkey_lt, Option.getD_some,
          hih _ hkey_lt, htbl c (Nat.lt_succ_self c)]
      · simp only [hne, ↓reduceIte, ← List.getD_eq_getElem?_getD,
          ← Array.getD_eq_getD_getElem?, hih k hk]
    · exact hih k hk

/-- Every entry of `childPassList` is bounded by `cap` when `init` and all candidate sums are. -/
theorem mem_childPassList_le {adj : ℕ → ℕ → Bool} {wt : ℕ → ℕ}
    {LB LP tblB init : List ℕ} {cap c : ℕ}
    (hinit : ∀ x ∈ init, x ≤ cap)
    (hstep : ∀ t < c, forgetWeight wt LP LB t + tblB.getD t 0 ≤ cap) :
    ∀ x ∈ childPassList adj wt LB LP tblB init c, x ≤ cap := by
  induction c with
  | zero => exact hinit
  | succ c ih =>
    have hih := ih (fun t ht => hstep t (Nat.lt_succ_of_lt ht))
    dsimp only [childPassList]
    split_ifs with hind
    · intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hmem | rfl
      · exact hih x hmem
      · refine max_le ?_ (hstep c (Nat.lt_succ_self c))
        rw [List.getD_eq_getElem?_getD]
        cases hget :
            (childPassList adj wt LB LP tblB init c)[keyMask LB LP c]? with
        | none => exact Nat.zero_le _
        | some v => exact hih v (List.mem_of_getElem? hget)
    · exact hih

/-! ### Word-RAM child pass (`childPassProg`) -/

/-- Register arguments for `childPassProg`. -/
structure ChildPassArgs where
  /-- Number of graph vertices `m`. -/
  numVerts : ℕ
  /-- Base memory address of the `m × m` adjacency matrix. -/
  adjPtr : ℕ
  /-- Base memory address of the `m`-word weight array. -/
  wtPtr : ℕ
  /-- Base memory address of child bag `LB`. -/
  bagBPtr : ℕ
  /-- Length of child bag `LB`. -/
  bagBLen : ℕ
  /-- Base memory address of child DP table `tblB`. -/
  tblBPtr : ℕ
  /-- Length `2 ^ |LB|` of child DP table `tblB`. -/
  tblBLen : ℕ
  /-- Base memory address of parent bag `LP`. -/
  bagPPtr : ℕ
  /-- Length of parent bag `LP`. -/
  bagPLen : ℕ
  /-- Base memory address of the scratch `best` array of length `2 ^ |LP|`. -/
  bestPtr : ℕ

/-- Tuple equivalence encoding `ChildPassArgs` into Word-RAM registers. -/
@[expose] def ChildPassArgs.equiv :
    ChildPassArgs ≃
      ((((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a :=
    (((((((((a.numVerts, a.adjPtr), a.wtPtr), a.bagBPtr), a.bagBLen),
      a.tblBPtr), a.tblBLen), a.bagPPtr), a.bagPLen), a.bestPtr)
  invFun := fun (((((((((nv, ap), wp), bbp), bbl), tbp), tbl), bpp), bpl), bp) =>
    ⟨nv, ap, wp, bbp, bbl, tbp, tbl, bpp, bpl, bp⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding ChildPassArgs := .ofEquiv ChildPassArgs.equiv

private def childPassStep (p : ChildPassArgs × ℕ) : Memory.Prog ℕ := do
  let a := p.1
  let curC := p.2
  let fc ← Memory.read (a.tblBPtr + curC)
  let ind ← indepBagProg ⟨a.numVerts, a.adjPtr, a.bagBPtr, a.bagBLen, curC⟩
  let key ← keyMaskProg ⟨a.bagBPtr, a.bagBLen, a.bagPPtr, a.bagPLen, curC⟩
  let fw ← forgetWeightProg ⟨a.wtPtr, a.bagPPtr, a.bagPLen, a.bagBPtr, a.bagBLen, curC⟩
  let oldBest ← Memory.read (a.bestPtr + key)
  let cand := fw + fc
  let upd := if oldBest < cand then cand else oldBest
  let nextVal := if ind = 1 then upd else oldBest
  Memory.write (a.bestPtr + key) nextVal
  pure (curC + 1)

/-- Populate the scratch `best` array at `args.bestPtr` across all `args.tblBLen` child masks. -/
def childPassProg (args : ChildPassArgs) : Memory.Prog Unit := do
  let _ ← iterate childPassStep args args.tblBLen 0
  pure ()

private theorem childPassStep_eval (a : ChildPassArgs) (curC : ℕ) (t : Memory.State) :
    let fc := t.mem (a.tblBPtr + curC)
    let ind := (Memory.spec 0).clientResult t
      (indepBagProg ⟨a.numVerts, a.adjPtr, a.bagBPtr, a.bagBLen, curC⟩)
    let key := (Memory.spec 0).clientResult t
      (keyMaskProg ⟨a.bagBPtr, a.bagBLen, a.bagPPtr, a.bagPLen, curC⟩)
    let fw := (Memory.spec 0).clientResult t
      (forgetWeightProg ⟨a.wtPtr, a.bagPPtr, a.bagPLen, a.bagBPtr, a.bagBLen, curC⟩)
    let oldBest := t.mem (a.bestPtr + key)
    let cand := fw + fc
    let nextVal := if ind = 1 then (if oldBest < cand then cand else oldBest) else oldBest
    (Memory.spec 0).clientState t (childPassStep (a, curC)) =
      ⟨Function.update t.mem (a.bestPtr + key) nextVal, t.frontier⟩ ∧
    (Memory.spec 0).clientResult t (childPassStep (a, curC)) = curC + 1 := by
  have hr_st (x : ℕ) : (Memory.spec 0).clientState t (Memory.read x) = t := rfl
  have hr_res (x : ℕ) : (Memory.spec 0).clientResult t (Memory.read x) = t.mem x := rfl
  unfold childPassStep
  dsimp only
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hr_st, hr_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    indepBagProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    keyMaskProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    forgetWeightProg_state,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hr_st, hr_res]
  exact ⟨rfl, rfl⟩

/-- Functional correctness, framing below `bestPtr`, and memory-cost bound for `childPassProg`. -/
theorem childPassProg_spec {w : ℕ} (args : ChildPassArgs) {inst : MWISInstance}
    {LB LP tblB initL : List ℕ} {cap : ℕ} {s : Memory.State}
    (hadj : HoldsIn args.adjPtr inst.adjMatrix s)
    (hadj_end : args.adjPtr + inst.adjMatrix.length ≤ args.bestPtr)
    (hwt : HoldsIn args.wtPtr inst.weights s)
    (hwt_end : args.wtPtr + inst.weights.length ≤ args.bestPtr)
    (hnv : args.numVerts = inst.numVerts)
    (hLB : HoldsIn args.bagBPtr LB s) (hlenB : LB.length = args.bagBLen)
    (hLB_end : args.bagBPtr + args.bagBLen ≤ args.bestPtr)
    (hLB_lt : ∀ u ∈ LB, u < inst.numVerts)
    (htblB : HoldsIn args.tblBPtr tblB s) (htblB_len : tblB.length = args.tblBLen)
    (htblB_end : args.tblBPtr + args.tblBLen ≤ args.bestPtr)
    (hLP : HoldsIn args.bagPPtr LP s) (hlenP : LP.length = args.bagPLen)
    (hLP_end : args.bagPPtr + args.bagPLen ≤ args.bestPtr)
    (hinit : HoldsIn args.bestPtr initL s) (hinit_len : initL.length = 2 ^ LP.length)
    (hinit_le : ∀ x ∈ initL, x ≤ cap)
    (hcand_le : ∀ t < args.tblBLen, forgetWeight inst.wt LP LB t + tblB.getD t 0 ≤ cap)
    (hfit_cap : Fits w cap) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (childPassProg args)) ∧
    ((Memory.spec 0).clientState s (childPassProg args)).frontier = s.frontier ∧
    PreservesBelow args.bestPtr s ((Memory.spec 0).clientState s (childPassProg args)) ∧
    HoldsIn args.bestPtr (childPassList inst.adj inst.wt LB LP tblB initL args.tblBLen)
      ((Memory.spec 0).clientState s (childPassProg args)) ∧
    memoryCost (childPassProg args) s ≤
      args.tblBLen *
        (args.bagBLen * (2 * args.bagBLen + 1) +
          args.bagPLen * (args.bagBLen + 1) +
          args.bagBLen * (args.bagPLen + 2) + 3) := by
  let stepCost :=
    args.bagBLen * (2 * args.bagBLen + 1) +
      args.bagPLen * (args.bagBLen + 1) +
      args.bagBLen * (args.bagPLen + 2) + 3
  suffices ∀ rem curC st,
      curC + rem = args.tblBLen →
      st.frontier = s.frontier →
      PreservesBelow args.bestPtr s st →
      HoldsIn args.bestPtr (childPassList inst.adj inst.wt LB LP tblB initL curC) st →
      (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (iterate childPassStep args rem curC)) ∧
      ((Memory.spec 0).clientState st (iterate childPassStep args rem curC)).frontier =
        s.frontier ∧
      PreservesBelow args.bestPtr s
        ((Memory.spec 0).clientState st (iterate childPassStep args rem curC)) ∧
      HoldsIn args.bestPtr (childPassList inst.adj inst.wt LB LP tblB initL (curC + rem))
        ((Memory.spec 0).clientState st (iterate childPassStep args rem curC)) ∧
      memoryCost (iterate childPassStep args rem curC) st ≤ rem * stepCost by
    have hbest_le : args.bestPtr ≤ s.frontier := by have := hinit.1; omega
    obtain ⟨hv_run, hfr_run, hpres_run, hbest_run, hc_run⟩ :=
      this args.tblBLen 0 s (Nat.zero_add _) rfl (PreservesBelow.refl hbest_le) hinit
    rw [Nat.zero_add] at hbest_run
    unfold childPassProg
    refine ⟨validHistory_bind_step hv_run (validHistory_pure w _ ()), ?_⟩
    rw [StateTransitionSpec.clientState_bind, memoryCost_bind', memoryCost_pure, Nat.add_zero]
    exact ⟨hfr_run, hpres_run, hbest_run, hc_run⟩
  intro rem
  induction rem with
  | zero =>
    intro curC st _ hfr hpres hbest_st
    rw [show iterate childPassStep args 0 curC = pure curC from rfl, Nat.add_zero]
    exact ⟨validHistory_pure w st curC, hfr, hpres, hbest_st, by simp [memoryCost_pure]⟩
  | succ rem ih =>
    intro curC st hsum hfr hpres hbest_st
    have hcur_lt : curC < args.tblBLen := by omega
    have hadj_st : HoldsIn args.adjPtr inst.adjMatrix st := hadj.mono hadj_end hpres
    have hwt_st : HoldsIn args.wtPtr inst.weights st := hwt.mono hwt_end hpres
    have hLB_st : HoldsIn args.bagBPtr LB st := hLB.mono (by omega) hpres
    have htblB_st : HoldsIn args.tblBPtr tblB st := htblB.mono (by omega) hpres
    have hLP_st : HoldsIn args.bagPPtr LP st := hLP.mono (by omega) hpres
    have hLB_lt_wt : ∀ u ∈ LB, u < inst.weights.length := inst.weights_len ▸ hLB_lt
    obtain ⟨hv_ind, hst_ind, hr_ind, hc_ind⟩ :=
      indepBagProg_spec (w := w) ⟨args.numVerts, args.adjPtr, args.bagBPtr, args.bagBLen, curC⟩
        hadj_st inst.adjMatrix_len hnv hLB_st hlenB hLB_lt
    obtain ⟨hv_key, hst_key, hr_key, hc_key⟩ :=
      keyMaskProg_spec (w := w) ⟨args.bagBPtr, args.bagBLen, args.bagPPtr, args.bagPLen, curC⟩
        hLB_st hlenB hLP_st hlenP
    obtain ⟨hv_fw, hst_fw, hr_fw, hc_fw⟩ :=
      forgetWeightProg_spec (w := w)
        ⟨args.wtPtr, args.bagPPtr, args.bagPLen, args.bagBPtr, args.bagBLen, curC⟩
        hwt_st hLP_st hlenP hLB_st hlenB hLB_lt_wt
    dsimp only at hr_ind hc_ind hr_key hc_key hr_fw hc_fw
    let bestCur := childPassList inst.adj inst.wt LB LP tblB initL curC
    let key := keyMask LB LP curC
    have hkey_lt : key < bestCur.length := by
      rw [length_childPassList, hinit_len]
      exact keyMask_lt_two_pow LB LP curC
    have hcur_tbl_lt : curC < tblB.length := by omega
    have hfc_addr_lt : args.tblBPtr + curC < st.frontier := by have := htblB_st.1; omega
    have hbest_addr_lt : args.bestPtr + key < st.frontier := by
      have h1 : args.bestPtr + bestCur.length ≤ st.frontier := hbest_st.1
      omega
    have hfc_eq : st.mem (args.tblBPtr + curC) = tblB.getD curC 0 := by
      rw [htblB_st.get curC hcur_tbl_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hcur_tbl_lt, Option.getD_some]
    have holdBest_eq : st.mem (args.bestPtr + key) = bestCur.getD key 0 := by
      rw [hbest_st.get key hkey_lt, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hkey_lt, Option.getD_some]
    let fw := forgetWeight inst.wt LP LB curC
    let fc := st.mem (args.tblBPtr + curC)
    let oldBest := st.mem (args.bestPtr + key)
    let cand := fw + fc
    let nextVal :=
      if (if indepInst inst.adj LB curC then 1 else 0) = 1 then
        if oldBest < cand then cand else oldBest
      else oldBest
    have holdBest_le : oldBest ≤ cap := by
      dsimp only [oldBest]
      rw [hbest_st.get key hkey_lt]
      exact mem_childPassList_le (adj := inst.adj) hinit_le
        (fun t ht => hcand_le t (lt_trans ht hcur_lt)) _ (List.getElem_mem hkey_lt)
    have hcand_val_le : cand ≤ cap := by
      dsimp only [cand, fw, fc]
      rw [hfc_eq]
      exact hcand_le curC hcur_lt
    have hnext_fit : Fits w nextVal := hfit_cap.of_le (by dsimp only [nextVal]; split_ifs <;> omega)
    let st₁ : Memory.State := ⟨Function.update st.mem (args.bestPtr + key) nextVal, st.frontier⟩
    obtain ⟨hst_step, hres_step⟩ := childPassStep_eval args curC st
    rw [hr_ind, hr_key, hr_fw] at hst_step
    have hv_step : (Memory.spec w).ValidHistory st
        ((Memory.spec w).clientHistory st (childPassStep (args, curC))) := by
      unfold childPassStep
      dsimp only
      refine validHistory_read_bind hfc_addr_lt (validHistory_bind_step hv_ind ?_)
      rw [hst_ind, hr_ind]
      refine validHistory_bind_step hv_key ?_
      rw [hst_key, hr_key]
      refine validHistory_bind_step hv_fw ?_
      rw [hst_fw, hr_fw]
      exact validHistory_read_bind hbest_addr_lt
        (validHistory_write_bind hbest_addr_lt hnext_fit (validHistory_pure w st₁ _))
    have hbest_next : HoldsIn args.bestPtr
        (childPassList inst.adj inst.wt LB LP tblB initL (curC + 1)) st₁ := by
      have hlist_eq : bestCur.set key nextVal =
          childPassList inst.adj inst.wt LB LP tblB initL (curC + 1) := by
        simp only [nextVal, cand, fw, fc, oldBest, hfc_eq, holdBest_eq]
        dsimp only [bestCur, key, childPassList]
        by_cases hind : indepInst inst.adj LB curC = true
        · simp only [hind, ↓reduceIte]
          congr 1
          split_ifs with hlt
          · exact (Nat.max_eq_right hlt.le).symm
          · exact (Nat.max_eq_left (Nat.not_lt.1 hlt)).symm
        · have hlt' : keyMask LB LP curC <
              (childPassList inst.adj inst.wt LB LP tblB initL curC).length := hkey_lt
          simp only [Bool.eq_false_iff.2 hind, Bool.false_eq_true, ↓reduceIte]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt', Option.getD_some]
          exact List.set_getElem_self hlt'
      exact hlist_eq ▸ holdsIn_set hbest_st
    have hc_step : memoryCost (childPassStep (args, curC)) st ≤ stepCost := by
      have hr_s (x : ℕ) : (Memory.spec 0).clientState st (Memory.read x) = st := rfl
      have hr_r (x : ℕ) : (Memory.spec 0).clientResult st (Memory.read x) = st.mem x := rfl
      unfold childPassStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, hr_s, hr_r,
        memoryCost_bind', hst_ind, hr_ind,
        memoryCost_bind', hst_key, hr_key,
        memoryCost_bind', hst_fw, hr_fw,
        memoryCost_bind', memoryCost_read, hr_s, hr_r,
        memoryCost_bind', memoryCost_write, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hfr_rem, hp_rem, hbest_rem, hc_rem⟩ :=
      ih (curC + 1) st₁ (by omega) hfr
        (hpres.trans (preservesBelow_write (Nat.le_add_right _ _) hbest_addr_lt)) hbest_next
    rw [show iterate childPassStep args (rem + 1) curC =
      (childPassStep (args, curC) >>= iterate childPassStep args rem) from rfl]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step]), ?_⟩
    rw [StateTransitionSpec.clientState_bind, memoryCost_bind', hst_step, hres_step,
      show curC + (rem + 1) = curC + 1 + rem by omega]
    exact ⟨hfr_rem, hp_rem, hbest_rem,
      (Nat.add_le_add hc_step hc_rem).trans_eq (by rw [Nat.succ_mul, Nat.add_comm])⟩

/-- Exact-basis Word-RAM realization certificate for `childPassProg`. -/
theorem childPassProg_realizes :
    Realizes .exact childPassProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 2 ∧
        ∃ m adjL wtL LB LP tblB initL cap,
          adjL.length = m * m ∧ wtL.length = m ∧ args.numVerts = m ∧
          HoldsIn args.adjPtr adjL s ∧ args.adjPtr + adjL.length ≤ args.bestPtr ∧
          HoldsIn args.wtPtr wtL s ∧ args.wtPtr + wtL.length ≤ args.bestPtr ∧
          HoldsIn args.bagBPtr LB s ∧ LB.length = args.bagBLen ∧
          args.bagBPtr + args.bagBLen ≤ args.bestPtr ∧ (∀ u ∈ LB, u < m) ∧
          HoldsIn args.tblBPtr tblB s ∧ tblB.length = args.tblBLen ∧
          args.tblBPtr + args.tblBLen ≤ args.bestPtr ∧
          HoldsIn args.bagPPtr LP s ∧ LP.length = args.bagPLen ∧
          args.bagPPtr + args.bagPLen ≤ args.bestPtr ∧
          HoldsIn args.bestPtr initL s ∧ initL.length = 2 ^ args.bagPLen ∧
          args.bagBLen * wtL.foldl max 0 + tblB.foldl max 0 ≤ cap ∧
          Fits w (args.adjPtr + m * m) ∧ Fits w (args.wtPtr + m) ∧
          Fits w (args.bagBPtr + args.bagBLen) ∧ Fits w (args.tblBPtr + args.tblBLen) ∧
          Fits w (args.bagPPtr + args.bagPLen) ∧ Fits w (2 ^ args.bagPLen) ∧
          Fits w (args.bestPtr + 2 ^ args.bagPLen) ∧ Fits w cap)
      (fun _ _ => 0) := by
  unfold childPassProg
  realize [indepBagProg_realizes, keyMaskProg_realizes, forgetWeightProg_realizes]
  obtain ⟨h2, m, adjL, wtL, LB, LP, tblB, initL, cap,
    hadjL_len, hwtL_len, hnv, hadj_h, hadj_end, hwt_h, hwt_end,
    hLB_h, hLB_len, hLB_end, hLB_lt, htblB_h, htblB_len, htblB_end,
    hLP_h, hLP_len, hLP_end, hinit_h, hinit_len, hcap_bound,
    hfit_adj, hfit_wt, hfit_bagB, hfit_tblB, hfit_bagP, hfit_powP, hfit_best, hfit_cap⟩ := h
  have h1 : Fits w 1 := h2.of_le (by decide)
  have hbest_le_fr : d.bestPtr ≤ s.frontier := by have := hinit_h.1; omega
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (curC : ℕ) (t : Memory.State) =>
      j ≤ d.tblBLen ∧ curC + j = d.tblBLen ∧
      t.frontier = s.frontier ∧
      PreservesBelow d.bestPtr s t ∧
      ∃ bestL, bestL.length = 2 ^ d.bagPLen ∧ HoldsIn d.bestPtr bestL t)
    (fun j curC t ⟨hj_le, hcur, hfr, hpres, bestL, hbest_len, hbest_t⟩ => ?_)
    ⟨le_rfl, Nat.zero_add _, rfl, PreservesBelow.refl hbest_le_fr, initL, hinit_len, hinit_h⟩
  have hadj_t : HoldsIn d.adjPtr adjL t := hadj_h.mono hadj_end hpres
  have hwt_t : HoldsIn d.wtPtr wtL t := hwt_h.mono hwt_end hpres
  have hLB_t : HoldsIn d.bagBPtr LB t := hLB_h.mono (by omega) hpres
  have htblB_t : HoldsIn d.tblBPtr tblB t := htblB_h.mono (by omega) hpres
  have hLP_t : HoldsIn d.bagPPtr LP t := hLP_h.mono (by omega) hpres
  have hLB_lt_wt : ∀ u ∈ LB, u < wtL.length := hwtL_len ▸ hLB_lt
  have hfit_wtL : Fits w (d.wtPtr + wtL.length) := hwtL_len ▸ hfit_wt
  have hfit_sumW : Fits w (d.bagBLen * wtL.foldl max 0) := hfit_cap.of_le (by omega)
  obtain ⟨_, _, hr_key, _⟩ :=
    keyMaskProg_spec (w := w) ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curC⟩
      hLB_t hLB_len hLP_t hLP_len
  dsimp only at hr_key
  have hkey_lt_pow : (Memory.spec 0).clientResult t
      (keyMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curC⟩) < 2 ^ d.bagPLen := by
    rw [hr_key, ← hLP_len]
    exact keyMask_lt_two_pow LB LP curC
  have hfw_le := forgetWeightProg_result_le
    ⟨d.wtPtr, d.bagPPtr, d.bagPLen, d.bagBPtr, d.bagBLen, curC⟩
    hwt_t hLP_t hLP_len hLB_t hLB_len hLB_lt_wt
  dsimp only at hfw_le
  have hcur_tbl : curC < tblB.length := by omega
  have hfc_le : t.mem (d.tblBPtr + curC) ≤ tblB.foldl max 0 :=
    htblB_t.get curC hcur_tbl ▸ List.mem_le_foldl_max (List.getElem_mem hcur_tbl)
  have hfit_tbl_addr : Fits w (d.tblBPtr + curC) := hfit_tblB.of_le (by omega)
  have hfit_best_addr : Fits w (d.bestPtr +
      (Memory.spec 0).clientResult t
        (keyMaskProg ⟨d.bagBPtr, d.bagBLen, d.bagPPtr, d.bagPLen, curC⟩)) :=
    hfit_best.of_le (by omega)
  have hfit_cand : Fits w ((Memory.spec 0).clientResult t
      (forgetWeightProg ⟨d.wtPtr, d.bagPPtr, d.bagPLen, d.bagBPtr, d.bagBLen, curC⟩) +
      t.mem (d.tblBPtr + curC)) :=
    hfit_cap.of_le (by omega)
  have hfit_cur1 : Fits w (curC + 1) := hfit_tblB.of_le (by omega)
  obtain ⟨hst_ev, hres_ev⟩ := childPassStep_eval d curC t
  refine ⟨?_, Nat.le_of_succ_le hj_le, by rw [hres_ev]; omega, ?_⟩
  · dsimp only [childPassStep]
    rw [indepBagProg_state, keyMaskProg_state, forgetWeightProg_state]
    repeat (
      first
      | split
      | exact ⟨h2, m, adjL, LB, hadjL_len, hnv, hadj_t, hLB_t, hLB_len, hLB_lt, hfit_adj, hfit_bagB⟩
      | exact ⟨h2, hfit_bagB, hfit_bagP, hfit_powP⟩
      | exact ⟨h2, wtL, LB, hwt_t, hLB_t, hLB_len, hLB_lt_wt, hfit_wtL, hfit_bagP, hfit_bagB,
          hfit_sumW⟩
      | exact trivial
      | assumption
      | refine And.intro ?_ ?_)
  · rw [hst_ev]
    exact ⟨hfr, hpres.trans (preservesBelow_write (Nat.le_add_right _ _)
        (by have := hbest_t.1; omega)),
      bestL.set _ _, by rw [List.length_set, hbest_len], holdsIn_set hbest_t⟩

end Cslib.Algorithms.WordRAM.TreeDecomposition
