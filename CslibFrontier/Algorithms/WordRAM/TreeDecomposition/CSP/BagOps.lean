/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.TreeDecomposition.Scan
import CslibFrontier.Tactic.Realize

/-!
# Word-RAM bag inclusion and erasure routines

This module certifies two materialized-bag subroutines used by the CSP dynamic program:

* `subsetBagProg`: tests whether a constraint scope slice is a subset of a bag slice via repeated
  `bagMemProg` calls.
* `eraseBagProg`: allocates `|xs.erase v|` words and copies the bag list omitting the first
  occurrence of `v`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.SubsetBagArgs`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.SubScanState`: loop input and accumulator states.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.subsetBagProg`: scope-inclusion check.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.eraseBagProg`: single-element bag erasure copy.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.subsetBagProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.subsetBagProg_realizes`: correctness and
  realization of `subsetBagProg`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.eraseBagProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.eraseBagProg_realizes`: correctness and realization
  of `eraseBagProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Scope subset test (`subsetBagProg`) and bag erasure (`eraseBagProg`) -/

/-- Register arguments for the linear scope-inclusion test `subsetBagProg`. -/
structure SubsetBagArgs where
  /-- Base memory address of the constraint scope list. -/
  scopePtr : ℕ
  /-- Length of the constraint scope list. -/
  scopeLen : ℕ
  /-- Base memory address of the bag list. -/
  bagPtr : ℕ
  /-- Length of the bag list. -/
  bagLen : ℕ

/-- Tuple equivalence encoding `SubsetBagArgs` into Word-RAM registers. -/
@[expose] def SubsetBagArgs.equiv : SubsetBagArgs ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun a := (((a.scopePtr, a.scopeLen), a.bagPtr), a.bagLen)
  invFun := fun (((sp, sl), bp), bl) => ⟨sp, sl, bp, bl⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SubsetBagArgs := .ofEquiv SubsetBagArgs.equiv

/-- Loop cursor and accumulator flag used by `subsetBagProg` and constraint scans. -/
structure SubScanState where
  /-- Current memory pointer in the scanned slice. -/
  cur : ℕ
  /-- Boolean-in-`ℕ` accumulator flag (`1` while all entries pass, `0` once falsified). -/
  found : ℕ

/-- Tuple equivalence encoding `SubScanState` into Word-RAM registers. -/
@[expose] def SubScanState.equiv : SubScanState ≃ ℕ × ℕ where
  toFun s := (s.cur, s.found)
  invFun := fun (cur, found) => ⟨cur, found⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SubScanState := .ofEquiv SubScanState.equiv

private def subsetBagStep (p : (ℕ × ℕ) × SubScanState) : Memory.Prog SubScanState := do
  let bagPtr := p.1.1
  let bagLen := p.1.2
  let st := p.2
  let u ← Memory.read st.cur
  let mem ← bagMemProg ⟨u, bagPtr, bagLen⟩
  pure ⟨st.cur + 1, if mem = 1 then st.found else 0⟩

/-- Decide whether every element of the scope slice appears in the bag slice (`1` iff true). -/
def subsetBagProg (args : SubsetBagArgs) : Memory.Prog ℕ := do
  let res ← iterate subsetBagStep (args.bagPtr, args.bagLen) args.scopeLen ⟨args.scopePtr, 1⟩
  pure res.found

private theorem subsetBagStep_eval (bp bl : ℕ) (st : SubScanState) (t : Memory.State) :
    let u := t.mem st.cur
    let mem := (Memory.spec 0).clientResult t (bagMemProg ⟨u, bp, bl⟩)
    (Memory.spec 0).clientState t (subsetBagStep ((bp, bl), st)) = t ∧
    (Memory.spec 0).clientResult t (subsetBagStep ((bp, bl), st)) =
      ⟨st.cur + 1, if mem = 1 then st.found else 0⟩ := by
  unfold subsetBagStep
  dsimp only
  rw [clientState_bind_read, clientResult_bind_read, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientResult_bind, bagMemProg_state]
  exact ⟨rfl, rfl⟩

/-- `subsetBagProg` is read-only and leaves memory unchanged. -/
theorem subsetBagProg_state (args : SubsetBagArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (subsetBagProg args) = s := by
  unfold subsetBagProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of subsetBagStep (args.bagPtr, args.bagLen)
    (fun st m => (subsetBagStep_eval args.bagPtr args.bagLen st m).1)
    args.scopeLen ⟨args.scopePtr, 1⟩ s

/-- Memory validity, functional correctness, and cost bound for `subsetBagProg`. -/
theorem subsetBagProg_spec {w : ℕ} (args : SubsetBagArgs)
    {scopeL bagL : List ℕ} {s : Memory.State}
    (hscope : HoldsIn args.scopePtr scopeL s) (hscope_len : scopeL.length = args.scopeLen)
    (hbag : HoldsIn args.bagPtr bagL s) (hbag_len : bagL.length = args.bagLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (subsetBagProg args)) ∧
    (Memory.spec 0).clientState s (subsetBagProg args) = s ∧
    (Memory.spec 0).clientResult s (subsetBagProg args) =
      (if decide (scopeL.toFinset ⊆ bagL.toFinset) then 1 else 0) ∧
    memoryCost (subsetBagProg args) s ≤ args.scopeLen * (args.bagLen + 1) := by
  let stepCost := args.bagLen + 1
  suffices ∀ ys cur ok,
      HoldsIn cur ys s →
      (ok = 0 ∨ ok = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate subsetBagStep (args.bagPtr, args.bagLen) ys.length ⟨cur, ok⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate subsetBagStep (args.bagPtr, args.bagLen) ys.length ⟨cur, ok⟩)).found =
        (if ok = 1 ∧ ∀ u ∈ ys, u ∈ bagL then 1 else 0) ∧
      memoryCost (iterate subsetBagStep (args.bagPtr, args.bagLen) ys.length ⟨cur, ok⟩) s ≤
        ys.length * stepCost by
    have hrun := this scopeL args.scopePtr 1 hscope (.inr rfl)
    rw [hscope_len] at hrun
    unfold subsetBagProg
    refine ⟨validHistory_bind_step hrun.1 (validHistory_pure w _ _), subsetBagProg_state args s,
      ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hrun.2.1]
      exact if_congr (by simp [Finset.subset_iff]) rfl rfl
    · rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
      exact hrun.2.2
  intro ys
  induction ys with
  | nil =>
    intro cur ok _ hok
    refine ⟨validHistory_pure w s _, ?_, by simp [iterate, memoryCost_pure]⟩
    rcases hok with rfl | rfl <;> rfl
  | cons u rest ih =>
    intro cur ok hcur hok
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hlt : cur < s.frontier := by omega
    obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ :=
      bagMemProg_spec (w := w) ⟨u, args.bagPtr, args.bagLen⟩ hbag hbag_len
    dsimp only at hr_bm hc_bm
    let ok' := if (if memBag u bagL then 1 else 0) = 1 then ok else 0
    have hok' : ok' = 0 ∨ ok' = 1 := by dsimp only [ok']; split_ifs <;> omega
    obtain ⟨hst_step, hres_step⟩ := subsetBagStep_eval args.bagPtr args.bagLen ⟨cur, ok⟩ s
    have hres_step' :
        (Memory.spec 0).clientResult s
          (subsetBagStep ((args.bagPtr, args.bagLen), ⟨cur, ok⟩)) = ⟨cur + 1, ok'⟩ := by
      rw [hres_step]
      simp only [hmem_u, hr_bm, ok']
    have hv_step : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (subsetBagStep ((args.bagPtr, args.bagLen), ⟨cur, ok⟩))) := by
      unfold subsetBagStep
      dsimp only
      refine validHistory_read_bind hlt ?_
      rw [hmem_u]
      exact validHistory_bind_step hv_bm (validHistory_pure w _ _)
    have hc_step :
        memoryCost (subsetBagStep ((args.bagPtr, args.bagLen), ⟨cur, ok⟩)) s ≤ stepCost := by
      unfold subsetBagStep
      dsimp only
      rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, hmem_u,
        memoryCost_bind', hst_bm, memoryCost_pure]
      dsimp only [stepCost]
      omega
    obtain ⟨hv_rem, hr_rem, hc_rem⟩ := ih (cur + 1) ok' hrest hok'
    simp only [List.length_cons]
    have hiter_eq :
        iterate subsetBagStep (args.bagPtr, args.bagLen) (rest.length + 1) ⟨cur, ok⟩ =
          (subsetBagStep ((args.bagPtr, args.bagLen), ⟨cur, ok⟩) >>=
            iterate subsetBagStep (args.bagPtr, args.bagLen) rest.length) := rfl
    rw [hiter_eq]
    refine ⟨validHistory_bind_step hv_step (by rwa [hst_step, hres_step']), ?_, ?_⟩
    · rw [StateTransitionSpec.clientResult_bind, hst_step, hres_step', hr_rem]
      refine if_congr ?_ rfl rfl
      dsimp only [ok']
      rw [memBag_eq_decide]
      rcases hok with rfl | rfl
      · simp
      · by_cases hu : u ∈ bagL <;> simp [hu]
    · rw [memoryCost_bind', hst_step, hres_step', Nat.succ_mul, Nat.add_comm _ stepCost]
      exact Nat.add_le_add hc_step hc_rem

/-- Exact-basis Word-RAM realization certificate for `subsetBagProg`. -/
theorem subsetBagProg_realizes :
    Realizes .exact subsetBagProg WordEncoding.encode WordEncoding.encode
      (fun w args _ =>
        Fits w 1 ∧ Fits w (args.scopePtr + args.scopeLen) ∧ Fits w (args.bagPtr + args.bagLen))
      (fun _ _ => 0) := by
  unfold subsetBagProg
  realize [bagMemProg_realizes]
  · exact h.1
  · obtain ⟨h1, hfit_sc, hfit_bg⟩ := h
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : SubScanState) (_ : Memory.State) =>
        st.cur + j = d.scopePtr + d.scopeLen ∧ st.found ≤ 1)
      (fun j st m ⟨hcur, hfd⟩ => ?_)
      ⟨rfl, le_rfl⟩
    have hbm_safe : Fits w 1 ∧ Fits w (d.bagPtr + d.bagLen) := ⟨h1, hfit_bg⟩
    have hfit_cur1 : Fits w (st.cur + 1) := hfit_sc.of_le (by omega)
    have hfit_fd : Fits w st.found := h1.of_le hfd
    obtain ⟨_, hres_ev⟩ := subsetBagStep_eval d.bagPtr d.bagLen st m
    refine ⟨?_, ?_, ?_⟩
    · dsimp only [subsetBagStep]
      repeat (
        first
        | split
        | exact hbm_safe
        | assumption
        | refine And.intro ?_ ?_)
    · rw [hres_ev]; dsimp only; omega
    · rw [hres_ev]; dsimp only; split_ifs <;> omega

/-! ### Materialized bag erasure (`eraseBagProg`) -/

private structure EraseState where
  srcCur : ℕ
  dstCur : ℕ
  skipped : ℕ

private def EraseState.equiv : EraseState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.srcCur, s.dstCur), s.skipped)
  invFun := fun ((sc, dc), sk) => ⟨sc, dc, sk⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding EraseState := .ofEquiv EraseState.equiv

private def eraseCopyStep (env : ℕ × EraseState) : Memory.Prog EraseState := do
  let target := env.1
  let st := env.2
  let x ← Memory.read st.srcCur
  if st.skipped = 0 ∧ x = target then
    pure ⟨st.srcCur + 1, st.dstCur, 1⟩
  else do
    Memory.write st.dstCur x
    pure ⟨st.srcCur + 1, st.dstCur + 1, st.skipped⟩

private theorem eraseCopyStep_eval (target : ℕ) (st : EraseState) (t : Memory.State) :
    let x := t.mem st.srcCur
    (Memory.spec 0).clientState t (eraseCopyStep (target, st)) =
      (if st.skipped = 0 ∧ x = target then t
       else ⟨Function.update t.mem st.dstCur x, t.frontier⟩) ∧
    (Memory.spec 0).clientResult t (eraseCopyStep (target, st)) =
      (if st.skipped = 0 ∧ x = target then ⟨st.srcCur + 1, st.dstCur, 1⟩
       else ⟨st.srcCur + 1, st.dstCur + 1, st.skipped⟩) ∧
    memoryCost (eraseCopyStep (target, st)) t ≤ 2 := by
  unfold eraseCopyStep
  dsimp only
  rw [clientState_bind_read, clientResult_bind_read, memoryCost_bind', memoryCost_read,
    clientState_read, clientResult_read]
  split_ifs
  · exact ⟨rfl, rfl, by rw [memoryCost_pure]; omega⟩
  · rw [memoryCost_bind', memoryCost_write, memoryCost_pure]
    exact ⟨rfl, rfl, le_rfl⟩

private theorem eraseCopyStep_valid {w target : ℕ} {st : EraseState} {t : Memory.State}
    (hsrc : st.srcCur < t.frontier) (hfit : Fits w (t.mem st.srcCur))
    (hdst : ¬(st.skipped = 0 ∧ t.mem st.srcCur = target) → st.dstCur < t.frontier) :
    (Memory.spec w).ValidHistory t
      ((Memory.spec w).clientHistory t (eraseCopyStep (target, st))) := by
  unfold eraseCopyStep
  dsimp only
  refine validHistory_read_bind hsrc ?_
  split_ifs with hc
  · exact validHistory_pure w t _
  · exact validHistory_write_bind (hdst hc) hfit (validHistory_pure w _ _)

private theorem sub_memBag_eq_length_erase {xs : List ℕ} {n target : ℕ} (hlen : xs.length = n) :
    n - (if memBag target xs then 1 else 0) = (xs.erase target).length := by
  subst hlen
  rw [memBag_eq_decide, List.length_erase]
  by_cases hm : target ∈ xs <;> simp [hm]

/-- Allocate and copy a materialized bag with the first occurrence of `args.target` erased. -/
def eraseBagProg (args : BagScanArgs) : Memory.Prog (ℕ × ℕ) := do
  let hasV ← bagMemProg args
  let bagLen := args.len - hasV
  let bagPtr ← Memory.allocDirty bagLen
  let _ ← iterate eraseCopyStep args.target args.len ⟨args.base, bagPtr, 0⟩
  pure (bagPtr, bagLen)

/-- Memory validity, framing, functional correctness, and cost bound for `eraseBagProg`. -/
theorem eraseBagProg_spec {w : ℕ} (args : BagScanArgs)
    {xs : List ℕ} {s : Memory.State}
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len)
    (hfit_elems : ∀ u ∈ xs, Fits w u)
    (hfit_fr : Fits w (s.frontier + (xs.erase args.target).length)) :
    let bagLen := (xs.erase args.target).length
    let s₁ := (Memory.spec 0).clientState s (eraseBagProg args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (eraseBagProg args)) ∧
    (Memory.spec 0).clientResult s (eraseBagProg args) = (s.frontier, bagLen) ∧
    s₁.frontier = s.frontier + bagLen ∧
    PreservesBelow s.frontier s s₁ ∧
    HoldsIn s.frontier (xs.erase args.target) s₁ ∧
    memoryCost (eraseBagProg args) s ≤ 3 * args.len + 1 := by
  obtain ⟨hv_bm, hst_bm, hr_bm, hc_bm⟩ := bagMemProg_spec (w := w) args hxs hlen
  have hlen_er := sub_memBag_eq_length_erase (target := args.target) hlen
  let bagLen := (xs.erase args.target).length
  let bagPtr := s.frontier
  let s_a := (Memory.spec 0).clientState s (Memory.allocDirty bagLen)
  have hp_a : PreservesBelow bagPtr s s_a := preservesBelow_allocDirty s bagLen
  have hv_a : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty bagLen)) :=
    validHistory_allocDirty hfit_fr
  suffices ∀ ys srcCur written skipped t,
      (∀ u ∈ ys, Fits w u) →
      srcCur + ys.length ≤ bagPtr →
      t.frontier = bagPtr + bagLen →
      PreservesBelow bagPtr s t →
      HoldsIn srcCur ys t →
      HoldsIn bagPtr written t →
      (skipped = 0 ∨ skipped = 1) →
      written ++ (if skipped = 1 then ys else ys.erase args.target) = xs.erase args.target →
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t
          (iterate eraseCopyStep args.target ys.length
            ⟨srcCur, bagPtr + written.length, skipped⟩)) ∧
      (let tEnd := (Memory.spec 0).clientState t
         (iterate eraseCopyStep args.target ys.length
           ⟨srcCur, bagPtr + written.length, skipped⟩)
       tEnd.frontier = bagPtr + bagLen ∧
       PreservesBelow bagPtr s tEnd ∧
       HoldsIn bagPtr (xs.erase args.target) tEnd) ∧
      memoryCost
        (iterate eraseCopyStep args.target ys.length
          ⟨srcCur, bagPtr + written.length, skipped⟩) t ≤ 2 * ys.length by
    have hrun := this xs args.base [] 0 s_a hfit_elems hxs.1 rfl hp_a
      (hxs.mono_frontier hp_a) (HoldsIn.nil (Nat.le_add_right _ _)) (.inl rfl)
      (by simp)
    simp only [List.length_nil, Nat.add_zero, hlen] at hrun
    obtain ⟨hv_loop, ⟨hfr_end, hp_end, hbag_end⟩, hc_loop⟩ := hrun
    have ha_st : (Memory.spec 0).clientState s (Memory.allocDirty bagLen) = s_a := rfl
    have ha_res : (Memory.spec 0).clientResult s (Memory.allocDirty bagLen) = bagPtr := rfl
    have hstate : (Memory.spec 0).clientState s (eraseBagProg args) =
        (Memory.spec 0).clientState s_a
          (iterate eraseCopyStep args.target args.len ⟨args.base, bagPtr, 0⟩) := by
      simp only [eraseBagProg]
      rw [StateTransitionSpec.clientState_bind, hst_bm, hr_bm, hlen_er,
        StateTransitionSpec.clientState_bind, ha_st, ha_res, StateTransitionSpec.clientState_bind]
      rfl
    dsimp only
    rw [hstate]
    simp only [eraseBagProg]
    refine ⟨validHistory_bind_step hv_bm ?_, ?_, hfr_end, hp_end, hbag_end, ?_⟩
    · rw [hst_bm, hr_bm, hlen_er]
      exact validHistory_bind_step hv_a (validHistory_bind_step hv_loop (validHistory_pure w _ _))
    · rw [StateTransitionSpec.clientResult_bind, hst_bm, hr_bm, hlen_er,
        StateTransitionSpec.clientResult_bind, ha_st, ha_res,
        StateTransitionSpec.clientResult_bind]
      rfl
    · rw [memoryCost_bind', hst_bm, hr_bm, hlen_er,
        memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res,
        memoryCost_bind', memoryCost_pure, Nat.add_zero]
      omega
  intro ys
  induction ys with
  | nil =>
    intro srcCur written skipped t _ _ hfr hpres _ hwr hsk hconcat
    have h0 : iterate eraseCopyStep args.target 0
        ⟨srcCur, bagPtr + written.length, skipped⟩ =
        pure ⟨srcCur, bagPtr + written.length, skipped⟩ := rfl
    rw [List.length_nil, h0]
    have hwr_eq : written = xs.erase args.target := by
      rcases hsk with rfl | rfl <;> simpa using hconcat
    rw [hwr_eq] at hwr
    exact ⟨validHistory_pure w t _, ⟨hfr, hpres, hwr⟩, by simp [memoryCost_pure]⟩
  | cons x rest ih =>
    intro srcCur written skipped t hfit_ys hsrc_end hfr hpres hys hwr hsk hconcat
    rw [HoldsIn.cons_iff] at hys
    obtain ⟨_, hmem_x, hrest⟩ := hys
    have hsrc_lt : srcCur < t.frontier := by simp only [List.length_cons] at hsrc_end; omega
    have hx_fit : Fits w (t.mem srcCur) := hmem_x ▸ hfit_ys x List.mem_cons_self
    have hfit_rest : ∀ u ∈ rest, Fits w u := fun u hu => hfit_ys u (List.mem_cons_of_mem _ hu)
    simp only [List.length_cons] at hsrc_end ⊢
    have hiter_eq : iterate eraseCopyStep args.target (rest.length + 1)
        ⟨srcCur, bagPtr + written.length, skipped⟩ =
      (eraseCopyStep (args.target, ⟨srcCur, bagPtr + written.length, skipped⟩) >>=
        iterate eraseCopyStep args.target rest.length) := rfl
    obtain ⟨hst_ev, hres_ev, hc_step⟩ :=
      eraseCopyStep_eval args.target ⟨srcCur, bagPtr + written.length, skipped⟩ t
    dsimp only at hst_ev hres_ev
    rw [hmem_x] at hst_ev hres_ev
    by_cases hskip_cond : skipped = 0 ∧ x = args.target
    · rw [ite_eq_left hskip_cond] at hst_ev hres_ev
      obtain ⟨rfl, rfl⟩ := hskip_cond
      have hv_step := eraseCopyStep_valid (target := args.target)
        (st := ⟨srcCur, bagPtr + written.length, 0⟩) hsrc_lt hx_fit fun h => (h ⟨rfl, hmem_x⟩).elim
      have hconcat' : written ++ (if (1 : ℕ) = 1 then rest else rest.erase args.target) =
          xs.erase args.target := by
        simpa [List.erase_cons] using hconcat
      obtain ⟨hv_rem, hprops_rem, hc_rem⟩ :=
        ih (srcCur + 1) written 1 t hfit_rest (by omega) hfr hpres hrest hwr (.inr rfl) hconcat'
      rw [hiter_eq]
      refine ⟨validHistory_bind_step hv_step (by rwa [hst_ev, hres_ev]), ?_, ?_⟩
      · rw [StateTransitionSpec.clientState_bind, hst_ev, hres_ev]
        exact hprops_rem
      · rw [memoryCost_bind', hst_ev, hres_ev]
        omega
    · rw [ite_eq_right hskip_cond] at hst_ev hres_ev
      have htail_eq :
          (if skipped = 1 then x :: rest else (x :: rest).erase args.target) =
            x :: (if skipped = 1 then rest else rest.erase args.target) := by
        rcases hsk with rfl | rfl
        · have hne : x ≠ args.target := fun hx => hskip_cond ⟨rfl, hx⟩
          simp [beq_eq_false_iff_ne.2 hne]
        · simp
      have hlen_sum : written.length + 1 +
          (if skipped = 1 then rest else rest.erase args.target).length = bagLen := by
        have hc_len := congrArg List.length hconcat
        rw [htail_eq, List.length_append, List.length_cons] at hc_len
        dsimp only [bagLen]
        omega
      have hdst_lt : bagPtr + written.length < t.frontier := by omega
      let t₁ : Memory.State := ⟨Function.update t.mem (bagPtr + written.length) x, t.frontier⟩
      have hres_ev' :
          (Memory.spec 0).clientResult t
            (eraseCopyStep (args.target, ⟨srcCur, bagPtr + written.length, skipped⟩)) =
            ⟨srcCur + 1, bagPtr + (written ++ [x]).length, skipped⟩ := by
        rw [hres_ev]
        simp [Nat.add_assoc]
      have hv_step := eraseCopyStep_valid (target := args.target)
        (st := ⟨srcCur, bagPtr + written.length, skipped⟩) hsrc_lt hx_fit fun _ => hdst_lt
      have hp₁ : PreservesBelow bagPtr t t₁ :=
        preservesBelow_write (Nat.le_add_right _ _) hdst_lt
      have hrest₁ : HoldsIn (srcCur + 1) rest t₁ :=
        hrest.mono (F := bagPtr) (by omega) hp₁
      have hwr₁ : HoldsIn bagPtr (written ++ [x]) t₁ :=
        holdsIn_append_one hwr (by omega)
      have hconcat₁ :
          (written ++ [x]) ++ (if skipped = 1 then rest else rest.erase args.target) =
            xs.erase args.target := by
        rw [List.append_assoc, List.singleton_append, ← htail_eq]
        exact hconcat
      obtain ⟨hv_rem, hprops_rem, hc_rem⟩ :=
        ih (srcCur + 1) (written ++ [x]) skipped t₁ hfit_rest (by omega) hfr
          (hpres.trans hp₁) hrest₁ hwr₁ hsk hconcat₁
      rw [hiter_eq]
      refine ⟨validHistory_bind_step hv_step (by rwa [hst_ev, hres_ev']), ?_, ?_⟩
      · rw [StateTransitionSpec.clientState_bind, hst_ev, hres_ev']
        exact hprops_rem
      · rw [memoryCost_bind', hst_ev, hres_ev']
        dsimp only [t₁] at hc_rem
        omega

/-- Exact-basis Word-RAM realization certificate for `eraseBagProg`. -/
theorem eraseBagProg_realizes :
    Realizes .exact eraseBagProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧
        ∃ xs,
          HoldsIn args.base xs s ∧
          xs.length = args.len ∧
          args.base + args.len ≤ s.frontier ∧
          (∀ u ∈ xs, Fits w u) ∧
          Fits w (s.frontier + args.len))
      (fun _ _ => 0) := by
  unfold eraseBagProg
  realize [bagMemProg_realizes]
  · exact h.1
  · obtain ⟨_, _, _, _, hbase_le, _, hfit_fr⟩ := h
    exact hfit_fr.of_le (by omega)
  · obtain ⟨_, xs, hxs, hlen, _, _, _⟩ := h
    obtain ⟨_, _, hr_bm, _⟩ := bagMemProg_spec (w := w) d hxs hlen
    rw [hr_bm, memBag_eq_decide]
    by_cases hm : d.target ∈ xs
    · simp only [hm, decide_true, ↓reduceIte, ← hlen]
      exact List.length_pos_of_mem hm
    · simp [hm]
  · obtain ⟨h1, xs, hxs, hlen, hbase_le, hfit_elems, hfit_fr⟩ := h
    obtain ⟨_, hst_bm, hr_bm, _⟩ := bagMemProg_spec (w := w) d hxs hlen
    rw [hst_bm, hr_bm, sub_memBag_eq_length_erase hlen]
    let bagLen := (xs.erase d.target).length
    have hbagLen_le : bagLen ≤ d.len := by
      dsimp only [bagLen]; rw [← hlen]; exact List.length_erase_le
    let s_a : Memory.State := { mem := s.mem, frontier := s.frontier + bagLen }
    have hp_a : PreservesBelow s.frontier s s_a := ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : EraseState) (t : Memory.State) =>
        j ≤ d.len ∧
        st.srcCur + j = d.base + d.len ∧
        s.frontier ≤ st.dstCur ∧
        st.dstCur ≤ s.frontier + (d.len - j) ∧
        st.skipped ≤ 1 ∧
        HoldsIn st.srcCur (xs.drop (d.len - j)) t)
      (fun j st t ⟨hj_le, hsrc_eq, hdst_lo, hdst_hi, hsk_le, hdrop_t⟩ => ?_)
      ⟨le_rfl, by simp, le_rfl, by simp, Nat.zero_le _,
        by dsimp only; rw [Nat.sub_self, List.drop_zero]; exact hxs.mono_frontier hp_a⟩
    have hidx_lt : d.len - (j + 1) < xs.length := by omega
    have hdrop_cons : xs.drop (d.len - (j + 1)) =
        xs[d.len - (j + 1)] :: xs.drop (d.len - j) := by
      have heq : d.len - (j + 1) + 1 = d.len - j := by omega
      rw [← heq]
      exact List.drop_eq_getElem_cons hidx_lt
    rw [hdrop_cons, HoldsIn.cons_iff] at hdrop_t
    obtain ⟨_, hmem_cur, hrest_t⟩ := hdrop_t
    have hx_fit : Fits w (t.mem st.srcCur) := by
      rw [hmem_cur]
      exact hfit_elems _ (List.getElem_mem hidx_lt)
    have hfit_src1 : Fits w (st.srcCur + 1) := hfit_fr.of_le (by omega)
    have hfit_dst : Fits w st.dstCur := hfit_fr.of_le (by omega)
    have hfit_dst1 : Fits w (st.dstCur + 1) := hfit_fr.of_le (by omega)
    have hfit_sk : Fits w st.skipped := h1.of_le hsk_le
    obtain ⟨hst_ev, hres_ev, _⟩ := eraseCopyStep_eval d.target st t
    dsimp only at hst_ev hres_ev
    refine ⟨?_, Nat.le_of_succ_le hj_le, ?_⟩
    · dsimp only [eraseCopyStep]
      repeat (
        first
        | split
        | assumption
        | refine And.intro ?_ ?_)
    · rw [hst_ev, hres_ev]
      by_cases hc : st.skipped = 0 ∧ t.mem st.srcCur = d.target
      · rw [ite_eq_left hc, ite_eq_left hc]
        exact ⟨by dsimp only; omega, hdst_lo,
          hdst_hi.trans (Nat.add_le_add_left (by omega) _), le_rfl, hrest_t⟩
      · rw [ite_eq_right hc, ite_eq_right hc]
        dsimp only
        refine ⟨by omega, by omega, by omega, hsk_le, hrest_t.1,
          hrest_t.2.frame fun a _ ha => ?_⟩
        have hdl : (xs.drop (d.len - j)).length = j := by simp [hlen]; omega
        exact Function.update_of_ne (by omega) _ t.mem

end Cslib.Algorithms.WordRAM.TreeDecomposition
