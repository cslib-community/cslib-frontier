/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.SumDomain
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Output Entry Table Materialization (`buildOutEntries`)

Iterates `sumDomainValues` over all `dom ^ outScopeLen` mixed-radix assignments to materialize the
dense output `FactorTable` entry array on the append-only Word-RAM heap.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.buildOutEntries`: output-entry table builder.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-- Arguments for materializing the output entry table of an eliminated bucket. -/
structure BuildOutArgs where
  /-- Field `dom` of `BuildOutArgs`. -/
  dom : ℕ
  /-- Field `x` of `BuildOutArgs`. -/
  x : ℕ
  /-- Field `outPtr` of `BuildOutArgs`. -/
  outPtr : ℕ
  /-- Field `outLen` of `BuildOutArgs`. -/
  outLen : ℕ
  /-- Field `bucketPtr` of `BuildOutArgs`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `BuildOutArgs`. -/
  bucketLen : ℕ

/-- Product equivalence encoding `BuildOutArgs` as words. -/
@[expose] def BuildOutArgs.equiv : BuildOutArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((s.dom, s.x), s.outPtr), s.outLen), s.bucketPtr), s.bucketLen)
  invFun := fun (((((dom, x), outPtr), outLen), bucketPtr), bucketLen) =>
    ⟨dom, x, outPtr, outLen, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding BuildOutArgs := .ofEquiv BuildOutArgs.equiv

private structure BuildEntryEnv where
  dom : ℕ
  x : ℕ
  outPtr : ℕ
  outLen : ℕ
  bucketPtr : ℕ
  bucketLen : ℕ
  entriesPtr : ℕ

private def BuildEntryEnv.equiv :
    BuildEntryEnv ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((((s.dom, s.x), s.outPtr), s.outLen), s.bucketPtr), s.bucketLen), s.entriesPtr)
  invFun := fun ((((((dom, x), outPtr), outLen), bucketPtr), bucketLen), entriesPtr) =>
    ⟨dom, x, outPtr, outLen, bucketPtr, bucketLen, entriesPtr⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BuildEntryEnv := .ofEquiv BuildEntryEnv.equiv

private def buildEntryStep (p : BuildEntryEnv × ℕ) : Memory.Prog ℕ :=
  Memory.read 0 >>= fun _ =>
  sumDomainValues ⟨p.1.dom, p.1.x, p.1.outPtr, p.1.outLen, p.2, p.1.bucketPtr, p.1.bucketLen⟩
    >>= fun val =>
  Memory.write (p.1.entriesPtr + p.2) val >>= fun _ =>
  pure (p.2 + 1)

/-- Materialize the `dom ^ outScopeLen`-entry array for an eliminated bucket. -/
def buildOutEntries (args : BuildOutArgs) : Memory.Prog (ℕ × ℕ) :=
  if args.dom = 0 then
    if args.outLen = 0 then
      Memory.alloc 1 >>= fun ptr => pure (ptr, 1)
    else
      Memory.alloc 0 >>= fun ptr => pure (ptr, 0)
  else
    powProg ⟨args.dom, args.outLen⟩ >>= fun numEntries =>
    Memory.allocDirty numEntries >>= fun entriesPtr =>
    iterate buildEntryStep
      ⟨args.dom, args.x, args.outPtr, args.outLen, args.bucketPtr, args.bucketLen, entriesPtr⟩
      numEntries 0 >>= fun _ =>
    pure (entriesPtr, numEntries)

private theorem buildEntryStep_state (env : BuildEntryEnv) (curIdx : ℕ) (t : Memory.State) :
    (Memory.spec 0).clientState t (buildEntryStep (env, curIdx)) =
      ⟨Function.update t.mem (env.entriesPtr + curIdx)
        ((Memory.spec 0).clientResult t (sumDomainValues
          ⟨env.dom, env.x, env.outPtr, env.outLen, curIdx, env.bucketPtr, env.bucketLen⟩)),
        t.frontier⟩ := by
  unfold buildEntryStep
  rw [clientState_bind_read, StateTransitionSpec.clientState_bind, sumDomainValues_state,
    StateTransitionSpec.clientState_bind]
  rfl

private theorem buildEntryStep_result (env : BuildEntryEnv) (curIdx : ℕ) (t : Memory.State) :
    (Memory.spec 0).clientResult t (buildEntryStep (env, curIdx)) = curIdx + 1 := by
  unfold buildEntryStep
  rw [clientResult_bind_read, StateTransitionSpec.clientResult_bind, sumDomainValues_state,
    StateTransitionSpec.clientResult_bind]
  rfl

theorem buildOutEntries_spec {w : ℕ} {args : BuildOutArgs} {outScope : List ℕ}
    {bucket : List (FactorTable ℕ ℕ)} {B maxScope : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hs0 : 0 < s.frontier)
    (hout : HoldsIn args.outPtr outScope s)
    (hout_eq : outScope = bucketOutScope args.x bucket)
    (hout_len : outScope.length = args.outLen)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope)
    (hfit_fr : Fits w (s.frontier + (max 1 args.dom) ^ args.outLen))
    (hcapB : (max 1 args.dom) * (bucket.map capFactor).prod ≤ B) (hB : Fits w B) :
    let res := (Memory.spec 0).clientResult s (buildOutEntries args)
    let s' := (Memory.spec 0).clientState s (buildOutEntries args)
    let newTab := elimBucketTable args.dom args.x bucket
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (buildOutEntries args)) ∧
      PreservesBelow s.frontier s s' ∧
      s'.frontier ≤ s.frontier + (max 1 args.dom) ^ args.outLen ∧
      s.frontier ≤ res.1 ∧
      res.2 = newTab.entries.size ∧
      HoldsIn res.1 newTab.entries.toList s' ∧
      memoryCost (buildOutEntries args) s ≤
        3 + args.outLen + (max 1 args.dom) ^ args.outLen *
          (3 + args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1)))) := by
  dsimp only
  unfold buildOutEntries
  by_cases hd0 : args.dom = 0
  · rw [ite_eq_left hd0]
    by_cases ho0 : args.outLen = 0
    · rw [ite_eq_left ho0]
      have hfit1 : Fits w (s.frontier + 1) := by simpa [hd0, ho0] using hfit_fr
      have htab_len : (bucketOutScope args.x bucket).length = 0 := by
        rw [← hout_eq, hout_len, ho0]
      have htab_sz : (elimBucketTable args.dom args.x bucket).entries.size = 1 := by
        simp [elimBucketTable, hd0, htab_len]
      have htab_list : (elimBucketTable args.dom args.x bucket).entries.toList = [0] := by
        simp [elimBucketTable, hd0, htab_len]
      refine ⟨validHistory_bind_step (validHistory_alloc hfit1) (validHistory_pure w _ _), ?_, ?_,
        le_rfl, ?_, ?_, ?_⟩
      · refine ⟨le_rfl, by change s.frontier ≤ s.frontier + 1; omega, fun a ha => ?_⟩
        change clear s.mem s.frontier 1 a = s.mem a
        exact clear_of_not_owns (by simp [Block.Owns]; omega)
      · change s.frontier + 1 ≤ s.frontier + (max 1 args.dom) ^ args.outLen
        simp [hd0, ho0]
      · exact htab_sz.symm
      · rw [htab_list]
        refine ⟨by change s.frontier + 1 ≤ s.frontier + 1; omega, ?_⟩
        refine Block.holdsList_cons_iff.mpr ⟨?_, Block.holdsList_nil _ _⟩
        change clear s.mem s.frontier 1 s.frontier = 0
        simp [clear]
      · rw [memoryCost_bind', memoryCost_alloc, memoryCost_pure]
        omega
    · rw [ite_eq_right ho0]
      have hfit0 : Fits w (s.frontier + 0) := by simpa using hwf.frontier_fits
      have htab_len : (bucketOutScope args.x bucket).length ≠ 0 := by
        rw [← hout_eq, hout_len]; exact ho0
      have htab_sz : (elimBucketTable args.dom args.x bucket).entries.size = 0 := by
        simp [elimBucketTable, hd0, Nat.zero_pow (Nat.pos_of_ne_zero htab_len)]
      have htab_list : (elimBucketTable args.dom args.x bucket).entries.toList = [] :=
        Array.toList_eq_nil_iff.mpr (Array.size_eq_zero_iff.mp htab_sz)
      refine ⟨validHistory_bind_step (validHistory_alloc hfit0) (validHistory_pure w _ _), ?_, ?_,
        le_rfl, ?_, ?_, ?_⟩
      · refine ⟨le_rfl, by change s.frontier ≤ s.frontier + 0; omega, fun a ha => ?_⟩
        change clear s.mem s.frontier 0 a = s.mem a
        exact clear_of_not_owns (by simp [Block.Owns])
      · change s.frontier + 0 ≤ s.frontier + (max 1 args.dom) ^ args.outLen
        omega
      · exact htab_sz.symm
      · rw [htab_list]
        exact ⟨by change s.frontier + 0 ≤ s.frontier + 0; omega, Block.holdsList_nil _ _⟩
      · rw [memoryCost_bind', memoryCost_alloc, memoryCost_pure]
        omega
  · rw [ite_eq_right hd0]
    have hdom : 0 < args.dom := Nat.pos_of_ne_zero hd0
    have hmax_dom : max 1 args.dom = args.dom := max_eq_right hdom
    let numEntries := args.dom ^ args.outLen
    have hfit_fr' : Fits w (s.frontier + numEntries) := by
      simpa [numEntries, hmax_dom] using hfit_fr
    have hcapB' : args.dom * (bucket.map capFactor).prod ≤ B := by
      simpa [hmax_dom] using hcapB
    have hpow_res : (Memory.spec 0).clientResult s (powProg ⟨args.dom, args.outLen⟩) =
        numEntries := powProg_result _ s
    have hpow_st : (Memory.spec 0).clientState s (powProg ⟨args.dom, args.outLen⟩) = s :=
      powProg_state _ s
    let s₀ : Memory.State := ⟨s.mem, s.frontier + numEntries⟩
    have hwf₀ : Memory.WellFormed w s₀ := hwf.step (o := .allocDirty numEntries) hfit_fr'
    let env : BuildEntryEnv :=
      ⟨args.dom, args.x, args.outPtr, args.outLen, args.bucketPtr, args.bucketLen, s.frontier⟩
    let entryFn : ℕ → ℕ := fun idx =>
      ∑ a : Fin args.dom,
        (bucket.map fun f => f.evalAt args.dom fun v =>
          if v = args.x then a.val
          else assignScope outScope (lsbDecode args.dom outScope.length idx) v).prod
    have hloop : ∀ (rem curIdx : ℕ) (t : Memory.State),
        curIdx + rem = numEntries →
        Memory.WellFormed w t →
        t.frontier = s.frontier + numEntries →
        PreservesBelow s.frontier s t →
        Block.HoldsList s.frontier ((List.range curIdx).map entryFn) t.mem →
        let p := iterate buildEntryStep env rem curIdx
        let t' := (Memory.spec 0).clientState t p
        (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
          t'.frontier = s.frontier + numEntries ∧
          PreservesBelow s.frontier s t' ∧
          Block.HoldsList s.frontier ((List.range numEntries).map entryFn) t'.mem ∧
          memoryCost p t ≤
            rem * (3 + args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1)))) := by
      intro rem
      induction rem with
      | zero =>
        intro curIdx t hsum _ hfr hpres hlist
        have hc : curIdx = numEntries := by omega
        subst hc
        exact ⟨validHistory_pure w t _, hfr, hpres, hlist, by simp [iterate]⟩
      | succ rem ih =>
        intro curIdx t hsum hwf_t hfr hpres hlist
        have hout_t : HoldsIn args.outPtr outScope t := hout.mono_frontier hpres
        have hb_t : HoldsFactorList args.bucketPtr bucket t := hb.mono_frontier hpres
        have hs0_t : 0 < t.frontier := by omega
        let sdArgs : SumDomainArgs :=
          ⟨args.dom, args.x, args.outPtr, args.outLen, curIdx, args.bucketPtr, args.bucketLen⟩
        have hsd_val := sumDomainValues_valid (w := w) (args := sdArgs) hs0_t
          (by dsimp only [sdArgs]; rw [← hout_len]; exact hout_t.1) hb_t hlen
        have hsd_res : (Memory.spec 0).clientResult t (sumDomainValues sdArgs) =
            entryFn curIdx := sumDomainValues_result hout_t.2 hout_len hb_t hlen
        have hsd_le : entryFn curIdx ≤ B := by
          rw [← hsd_res]
          exact (sumDomainValues_le_cap hb_t hlen).trans hcapB'
        have hval_fit : Fits w (entryFn curIdx) := hB.of_le hsd_le
        have haddr_lt : s.frontier + curIdx < t.frontier := by omega
        have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (buildEntryStep (env, curIdx))) := by
          unfold buildEntryStep
          dsimp only [env]
          refine validHistory_read_bind hs0_t <| validHistory_bind_step hsd_val ?_
          rw [sumDomainValues_state, hsd_res]
          exact validHistory_write_bind haddr_lt hval_fit (validHistory_pure w _ _)
        let t₁ : Memory.State :=
          ⟨Function.update t.mem (s.frontier + curIdx) (entryFn curIdx), t.frontier⟩
        have hstep_st : (Memory.spec 0).clientState t (buildEntryStep (env, curIdx)) = t₁ := by
          rw [buildEntryStep_state]
          dsimp only [env]
          rw [hsd_res]
        have hwf₁ : Memory.WellFormed w t₁ :=
          hwf_t.step (o := .write (s.frontier + curIdx) (entryFn curIdx)) ⟨haddr_lt, hval_fit⟩
        have hfr₁ : t₁.frontier = s.frontier + numEntries := hfr
        have hpres₁ : PreservesBelow s.frontier s t₁ := ⟨le_rfl, by omega,
          fun a ha => (Function.update_of_ne (by omega) _ _).trans (hpres.2.2 a ha)⟩
        have hlist₁ :
            Block.HoldsList s.frontier ((List.range (curIdx + 1)).map entryFn) t₁.mem := by
          rw [List.range_succ, List.map_append, List.map_singleton]
          have hlen_r : ((List.range curIdx).map entryFn).length = curIdx := by simp
          simpa [t₁, hlen_r] using hlist.append_one (entryFn curIdx)
        have hstep_cost : memoryCost (buildEntryStep (env, curIdx)) t ≤
            3 + args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1))) := by
          unfold buildEntryStep
          dsimp only [env]
          rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind',
            sumDomainValues_state, memoryCost_bind', memoryCost_write, memoryCost_pure]
          have hscost := sumDomainValues_cost (args := sdArgs) hb_t hlen hmax
          dsimp only [sdArgs] at hscost
          omega
        obtain ⟨hv_r, hfr_r, hpres_r, hlist_r, hcost_r⟩ :=
          ih (curIdx + 1) t₁ (by omega) hwf₁ hfr₁ hpres₁ hlist₁
        dsimp only
        have hiter_eq : iterate buildEntryStep env (rem + 1) curIdx =
            (buildEntryStep (env, curIdx) >>= iterate buildEntryStep env rem) := rfl
        rw [hiter_eq, StateTransitionSpec.clientState_bind, hstep_st, buildEntryStep_result]
        refine ⟨validHistory_bind_step hstep_val
          (by simpa [hstep_st, buildEntryStep_result] using hv_r), hfr_r, hpres_r, hlist_r, ?_⟩
        rw [memoryCost_bind', hstep_st, buildEntryStep_result, Nat.succ_mul]
        omega
    have hpres₀ : PreservesBelow s.frontier s s₀ := ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
    obtain ⟨hv_l, hfr_l, hpres_l, hlist_l, hcost_l⟩ :=
      hloop numEntries 0 s₀ (by simp) hwf₀ rfl hpres₀ (Block.holdsList_nil _ _)
    have hpure_st {α : Type} (x : α) (t : Memory.State) :
        (Memory.spec 0).clientState t (pure x) = t := rfl
    have hpure_res {α : Type} (x : α) (t : Memory.State) :
        (Memory.spec 0).clientResult t (pure x) = x := rfl
    have ha_st : (Memory.spec 0).clientState s (Memory.allocDirty numEntries) = s₀ := rfl
    have ha_res : (Memory.spec 0).clientResult s (Memory.allocDirty numEntries) = s.frontier := rfl
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
      hpow_st, hpow_res,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
      ha_st, ha_res,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
      hpure_res, hpure_st]
    have htab_len : (bucketOutScope args.x bucket).length = args.outLen := by
      rw [← hout_eq, hout_len]
    have htab_sz : (elimBucketTable args.dom args.x bucket).entries.size = numEntries := by
      simp [elimBucketTable, htab_len, numEntries]
    have htab_list : (elimBucketTable args.dom args.x bucket).entries.toList =
        (List.range numEntries).map entryFn := by
      apply List.ext_getElem
      · simp [htab_sz]
      · intro i hi1 hi2
        simp only [List.getElem_map, List.getElem_range]
        rw [Array.getElem_toList]
        simp only [elimBucketTable, Array.getElem_ofFn, entryFn]
        subst hout_eq
        rfl
    refine ⟨validHistory_bind_step (powProg_valid _ hs0) ?_, hpres_l, ?_, le_rfl, htab_sz.symm,
      ?_, ?_⟩
    · rw [hpow_st, hpow_res]
      refine validHistory_bind_step (validHistory_allocDirty hfit_fr') ?_
      rw [ha_st, ha_res]
      exact validHistory_bind_step hv_l (validHistory_pure w _ _)
    · rw [hfr_l, hmax_dom]
    · rw [htab_list]
      refine ⟨?_, hlist_l⟩
      rw [hfr_l]
      simp
    · rw [memoryCost_bind', hpow_st, hpow_res, memoryCost_bind', memoryCost_allocDirty,
        ha_st, ha_res, memoryCost_bind', memoryCost_pure, Nat.add_zero]
      have hpc := powProg_cost ⟨args.dom, args.outLen⟩ s
      dsimp only at hpc
      rw [hmax_dom]
      change memoryCost (powProg ⟨args.dom, args.outLen⟩) s +
        (1 + memoryCost (iterate buildEntryStep env numEntries 0) s₀) ≤
        3 + args.outLen + numEntries *
          (3 + args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1))))
      omega

theorem buildOutEntries_realizes :
    Realizes .exact buildOutEntries WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧
        args.outPtr + args.outLen ≤ s.frontier ∧
        Fits w (s.frontier + (max 1 args.dom) ^ args.outLen) ∧
        ∃ bucket B maxScope,
          bucket.length = args.bucketLen ∧
          HoldsFactorList args.bucketPtr bucket s ∧
          (∀ f ∈ bucket, f.scope.length ≤ maxScope) ∧
          Fits w ((max 1 args.dom) ^ maxScope) ∧
          (max 1 args.dom) * (bucket.map capFactor).prod ≤ B ∧
          Fits w B)
      (fun _ _ => 0) := by
  unfold buildOutEntries
  realize [powProg_realizes, sumDomainValues_realizes]
  · exact h.1
  · exact h.1
  · exact h.2.2.1.of_le (Nat.le_add_left _ _)
  · obtain ⟨h1, hout, hfit_fr, bucket, B, maxScope, hblen, hbf, hmax, hdomPow, hcapB, hB⟩ := h
    have hdom : 0 < d.dom := Nat.pos_of_ne_zero ‹_›
    have hmax_dom : max 1 d.dom = d.dom := max_eq_right hdom
    rw [powProg_state, powProg_result]
    dsimp only
    have hfit_fr' : Fits w (s.frontier + d.dom ^ d.outLen) := by simpa [hmax_dom] using hfit_fr
    refine iterationSafe_of_stepInv _ _ w _
      (fun j curIdx t => curIdx + j = d.dom ^ d.outLen ∧
        t.frontier = s.frontier + d.dom ^ d.outLen ∧
        PreservesBelow s.frontier s t)
      (fun j curIdx t ⟨hcur, hfr, hpres⟩ => ?_)
      ⟨by simp, rfl, ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩⟩
    dsimp only
    have hbf_t : HoldsFactorList d.bucketPtr bucket t := hbf.mono_frontier hpres
    have hout_t : d.outPtr + d.outLen ≤ t.frontier := hout.trans hpres.2.1
    have hdomPow' : Fits w (d.dom ^ maxScope) := by simpa [hmax_dom] using hdomPow
    have hcapB' : d.dom * (bucket.map capFactor).prod ≤ B := by simpa [hmax_dom] using hcapB
    refine ⟨?_, ?_⟩
    · exact ⟨⟨hdom, h1, hout_t, bucket, B, maxScope, hblen, hbf_t, hmax, hdomPow', hcapB', hB⟩,
        hfit_fr'.of_le (by omega), hfit_fr'.of_le (by omega)⟩
    · rw [buildEntryStep_state, buildEntryStep_result]
      refine ⟨by omega, hfr, ?_⟩
      refine ⟨le_rfl, by dsimp only; omega, fun a ha => ?_⟩
      dsimp only
      rw [Function.update_of_ne (by omega)]
      exact hpres.2.2 a ha

end Cslib.Algorithms.WordRAM.VariableElimination
