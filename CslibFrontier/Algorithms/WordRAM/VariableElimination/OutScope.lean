/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.FlattenScope
import CslibFrontier.Tactic.Realize

/-!
# Deduplicated Output Scope Materialization (`buildOutScope`)

Deduplicates a flattened bucket-scope buffer backwards (`dedupFilterBack`) skipping the eliminated
variable `x`, producing `bucketOutScope x bucket` in exact canonical order.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.buildOutScope`: output-scope builder `Memory.Prog`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

private structure DedupArgs where
  x : ℕ
  flatPtr : ℕ
  flatLen : ℕ

private def DedupArgs.equiv : DedupArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.x, s.flatPtr), s.flatLen)
  invFun := fun ((x, flatPtr), flatLen) => ⟨x, flatPtr, flatLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding DedupArgs := .ofEquiv DedupArgs.equiv

private structure DedupState where
  remPos : ℕ
  outStart : ℕ
  outLen : ℕ

private def DedupState.equiv : DedupState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.remPos, s.outStart), s.outLen)
  invFun := fun ((remPos, outStart), outLen) => ⟨remPos, outStart, outLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding DedupState := .ofEquiv DedupState.equiv

private def dedupBackStep (p : (ℕ × ℕ) × DedupState) : Memory.Prog DedupState :=
  let pos := p.2.remPos - 1
  Memory.read (p.1.2 + pos) >>= fun v =>
  memScan ⟨v, p.2.outStart, p.2.outLen⟩ >>= fun inAcc =>
  if v = p.1.1 ∨ inAcc = 1 then
    pure ⟨pos, p.2.outStart, p.2.outLen⟩
  else
    Memory.write (p.2.outStart - 1) v >>= fun _ =>
      pure ⟨pos, p.2.outStart - 1, p.2.outLen + 1⟩

private def dedupFilterBack (args : DedupArgs) : Memory.Prog (ℕ × ℕ) :=
  Memory.allocDirty args.flatLen >>= fun outBuf =>
  iterate dedupBackStep (args.x, args.flatPtr) args.flatLen
    ⟨args.flatLen, outBuf + args.flatLen, 0⟩ >>= fun res =>
  pure (res.outStart, res.outLen)

private theorem dedupFilterBack_spec {w : ℕ} {args : DedupArgs} {flat : List ℕ} {W_out : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hflat : HoldsIn args.flatPtr flat s) (hlen : flat.length = args.flatLen)
    (hW : (flat.foldr (dedupStepPure args.x) []).length ≤ W_out)
    (hfit : Fits w (s.frontier + args.flatLen)) :
    let res := (Memory.spec 0).clientResult s (dedupFilterBack args)
    let s' := (Memory.spec 0).clientState s (dedupFilterBack args)
    let outScope := flat.foldr (dedupStepPure args.x) []
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (dedupFilterBack args)) ∧
      s'.frontier = s.frontier + args.flatLen ∧
      PreservesBelow s.frontier s s' ∧
      s.frontier ≤ res.1 ∧
      res.2 = outScope.length ∧
      HoldsIn res.1 outScope s' ∧
      memoryCost (dedupFilterBack args) s ≤ 1 + args.flatLen * (2 + W_out) := by
  obtain ⟨x, flatPtr, flatLen⟩ := args
  dsimp only at hflat hlen hW hfit
  subst hlen
  unfold dedupFilterBack
  dsimp only
  have hloop : ∀ (ys acc : List ℕ) (t : Memory.State), Memory.WellFormed w t →
      t.frontier = s.frontier + flat.length → PreservesBelow s.frontier s t →
      flatPtr + ys.length ≤ s.frontier → Block.HoldsList flatPtr ys s.mem →
      ys.length + acc.length ≤ flat.length → (ys.foldr (dedupStepPure x) acc).length ≤ W_out →
      Block.HoldsList (s.frontier + flat.length - acc.length) acc t.mem →
      let p := iterate dedupBackStep (x, flatPtr) ys.length
        ⟨ys.length, s.frontier + flat.length - acc.length, acc.length⟩
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let out := ys.foldr (dedupStepPure x) acc
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = s.frontier + flat.length ∧ PreservesBelow s.frontier s t' ∧
        r.outStart = s.frontier + flat.length - out.length ∧ r.outLen = out.length ∧
        out.length ≤ flat.length ∧ Block.HoldsList r.outStart out t'.mem ∧
        memoryCost p t ≤ ys.length * (2 + W_out) := by
    intro ys
    induction ys using List.reverseRecOn with
    | nil =>
      intro acc t _ hfr hpres _ _ hroom _ hacc
      simp only [List.length_nil, Nat.zero_add, List.foldr_nil, Nat.zero_mul] at hroom ⊢
      exact ⟨validHistory_pure w t _, hfr, hpres, rfl, rfl, hroom, hacc, by simp [iterate]⟩
    | append_singleton ys v ih =>
      intro acc t hwf_t hfr hpres hys_b hys_h hroom hW_cur hacc
      have hacc_W : acc.length ≤ W_out :=
        (length_le_foldr_dedupStepPure x (ys ++ [v]) acc).trans hW_cur
      simp only [List.length_append, List.length_singleton, List.foldr_append, List.foldr_cons,
        List.foldr_nil] at hys_b hroom hW_cur ⊢
      obtain ⟨hys_h, hv_h⟩ := Block.holdsList_append_iff.mp hys_h
      have hv_mem : t.mem (flatPtr + ys.length) = v :=
        (hpres.2.2 _ (by omega)).trans (Block.holdsList_cons_iff.mp hv_h).1
      have hms_res : (Memory.spec 0).clientResult t
          (memScan ⟨v, s.frontier + flat.length - acc.length, acc.length⟩) =
          if v ∈ acc then 1 else 0 := memScan_result hacc rfl
      have hms_val := memScan_valid (w := w) ⟨v, s.frontier + flat.length - acc.length, acc.length⟩
        (s := t) (by dsimp only; omega)
      have hms_cost : memoryCost (memScan ⟨v, s.frontier + flat.length - acc.length, acc.length⟩) t
          ≤ acc.length := memScan_cost _ t
      let step := dedupBackStep ((x, flatPtr),
        ⟨ys.length + 1, s.frontier + flat.length - acc.length, acc.length⟩)
      let out₁ := dedupStepPure x v acc
      -- One step reads `v`, scans the output so far for it, and prepends it unless it is `x` or
      -- already present.
      obtain ⟨t₁, hst, hres, hval, hcost, hwf₁, hfr₁, hpres₁, hacc₁, hout₁⟩ : ∃ t₁ : Memory.State,
          (Memory.spec 0).clientState t step = t₁ ∧
          (Memory.spec 0).clientResult t step =
            ⟨ys.length, s.frontier + flat.length - out₁.length, out₁.length⟩ ∧
          (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t step) ∧
          memoryCost step t ≤ 2 + W_out ∧ Memory.WellFormed w t₁ ∧ t₁.frontier = t.frontier ∧
          PreservesBelow s.frontier s t₁ ∧
          Block.HoldsList (s.frontier + flat.length - out₁.length) out₁ t₁.mem ∧
          out₁.length ≤ acc.length + 1 := by
        simp only [step, out₁, dedupBackStep, dedupStepPure, Nat.add_sub_cancel]
        rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
          memoryCost_bind', memoryCost_read, clientState_read, clientResult_read, hv_mem,
          StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
          memoryCost_bind', memScan_state, hms_res]
        by_cases hcond : v = x ∨ v ∈ acc
        · have hg : v = x ∨ (if v ∈ acc then 1 else 0) = 1 := hcond.imp_right (ite_eq_left ·)
          rw [ite_eq_left hg, ite_eq_left hcond, memoryCost_pure]
          refine ⟨t, rfl, rfl, validHistory_read_bind (by omega) ?_, by omega, hwf_t, rfl, hpres,
            hacc, by omega⟩
          rw [hv_mem]
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, hms_res, ite_eq_left hg]
          exact validHistory_pure w t _
        · have hg : ¬(v = x ∨ (if v ∈ acc then 1 else 0) = 1) := by
            simp only [not_or] at hcond; simp [hcond.1, hcond.2]
          have hout_lt : s.frontier + flat.length - acc.length - 1 < t.frontier := by omega
          have hv_fit : Fits w v := hv_mem ▸ hwf_t.mem_fits _
          rw [ite_eq_right hg, ite_eq_right hcond, memoryCost_bind', memoryCost_write,
            memoryCost_pure]
          simp only [List.length_cons, ← Nat.sub_sub]
          refine ⟨⟨Function.update t.mem (s.frontier + flat.length - acc.length - 1) v, t.frontier⟩,
            rfl, rfl, validHistory_read_bind (by omega) ?_, by omega,
            hwf_t.step (o := .write _ v) ⟨hout_lt, hv_fit⟩, rfl,
            ⟨hpres.1, hpres.2.1, fun a ha => (Function.update_of_ne (by omega) _ _).trans
              (hpres.2.2 a ha)⟩,
            Block.holdsList_cons_iff.mpr ⟨Function.update_self _ v t.mem, ?_⟩, le_rfl⟩
          · rw [hv_mem]
            refine validHistory_bind_step hms_val ?_
            rw [memScan_state, hms_res, ite_eq_right hg]
            exact validHistory_write_bind hout_lt hv_fit (validHistory_pure w _ _)
          · rw [Nat.sub_add_cancel (by omega)]
            exact hacc.frame fun a hlo _ => Function.update_of_ne (by omega) v t.mem
      obtain ⟨hv_i, hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, hcost_i⟩ :=
        ih out₁ t₁ hwf₁ (hfr₁.trans hfr) hpres₁ (by omega) hys_h (by omega) hW_cur hacc₁
      have hiter : iterate dedupBackStep (x, flatPtr) (ys.length + 1)
          ⟨ys.length + 1, s.frontier + flat.length - acc.length, acc.length⟩ =
          step >>= iterate dedupBackStep (x, flatPtr) ys.length := rfl
      rw [hiter, validHistory_bind', StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientState_bind, memoryCost_bind', hst, hres]
      exact ⟨⟨hval, hv_i⟩, hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, by linarith⟩
  obtain ⟨hv_l, hfr_l, hpres_l, hst_l, hlen_l, hle_l, hholds_l, hcost_l⟩ :=
    hloop flat [] ⟨s.mem, s.frontier + flat.length⟩
      (hwf.step (o := .allocDirty flat.length) hfit) rfl
      ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩ hflat.1 hflat.2 (by simp) hW
      (Block.holdsList_nil _ _)
  simp only [List.length_nil, Nat.sub_zero] at hv_l hfr_l hpres_l hst_l hlen_l hholds_l hcost_l
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    memoryCost_bind', clientState_allocDirty, clientResult_allocDirty, memoryCost_allocDirty,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    memoryCost_bind', StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure,
    memoryCost_pure]
  exact ⟨validHistory_allocDirty_bind hfit (validHistory_bind_step hv_l (validHistory_pure w _ _)),
    hfr_l, hpres_l, by omega, hlen_l, ⟨by omega, hholds_l⟩, by omega⟩

private theorem bool_rec_reflects {p : Prop} {b : Bool} (hr : b.Reflects p)
    {f : false.Reflects p → Prop} {t : true.Reflects p → Prop}
    (hf : ∀ h, f h) (ht : ∀ h, t h) :
    Bool.rec (motive := fun x => x.Reflects p → Prop) f t b hr := by
  cases b
  · exact hf hr
  · exact ht hr

private theorem dedupFilterBack_realizes :
    Realizes .exact dedupFilterBack WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧ args.flatPtr + args.flatLen ≤ s.frontier ∧
        Fits w (s.frontier + args.flatLen))
      (fun _ _ => 0) := by
  unfold dedupFilterBack
  realize [memScan_realizes]
  · exact h.2.2
  · obtain ⟨h1, hflat_b, hfit⟩ := h
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : DedupState) (_ : Memory.State) =>
        st.remPos = j ∧
        st.outStart + st.outLen = s.frontier + d.flatLen ∧
        s.frontier + j ≤ st.outStart)
      (fun j st t ⟨hrem, hsum, hlo⟩ => ?_)
      ⟨rfl, Nat.add_zero _, le_rfl⟩
    dsimp only
    have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
    have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
    refine ⟨?_, ?_⟩
    · refine ⟨⟨by omega, hfit.of_le (by omega)⟩, ⟨h1, hfit.of_le (by omega)⟩, ?_⟩
      refine bool_rec_reflects _ (fun _ => ⟨h1, ?_⟩) (fun _ => by omega)
      split_ifs
      · omega
      · exact ⟨by omega, ⟨by omega, by omega⟩, hfit.of_le (by omega)⟩
    · unfold dedupBackStep
      dsimp only
      rw [StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientResult_bind, memScan_state]
      have hpure_res {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientResult u (pure x) = x := rfl
      split_ifs
      · rw [hpure_res]; dsimp only; exact ⟨by omega, hsum, by omega⟩
      · rw [StateTransitionSpec.clientResult_bind, hpure_res]
        dsimp only
        exact ⟨by omega, by omega, by omega⟩

/-- Arguments `(x, bucketPtr, bucketLen)` for `buildOutScope`. -/
structure BuildOutScopeArgs where
  /-- Field `x` of `BuildOutScopeArgs`. -/
  x : ℕ
  /-- Field `bucketPtr` of `BuildOutScopeArgs`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `BuildOutScopeArgs`. -/
  bucketLen : ℕ

/-- Product equivalence encoding `BuildOutScopeArgs` as words. -/
@[expose] def BuildOutScopeArgs.equiv : BuildOutScopeArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.x, s.bucketPtr), s.bucketLen)
  invFun := fun ((x, bucketPtr), bucketLen) => ⟨x, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding BuildOutScopeArgs := .ofEquiv BuildOutScopeArgs.equiv

/-- Materialize the deduplicated output scope `bucketOutScope x bucket`. -/
def buildOutScope (args : BuildOutScopeArgs) : Memory.Prog (ℕ × ℕ) :=
  sumScopeLen ⟨args.bucketPtr, args.bucketLen⟩ >>= fun flatLen =>
  flattenScopes ⟨args.bucketPtr, args.bucketLen, flatLen⟩ >>= fun flatPtr =>
  dedupFilterBack ⟨args.x, flatPtr, flatLen⟩

theorem buildOutScope_spec {w : ℕ} {args : BuildOutScopeArgs}
    {bucket : List (FactorTable ℕ ℕ)} {maxScope W_out : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope)
    (hW : (bucketOutScope args.x bucket).length ≤ W_out)
    (hfit : Fits w (s.frontier + 2 * (args.bucketLen * maxScope))) :
    let res := (Memory.spec 0).clientResult s (buildOutScope args)
    let s' := (Memory.spec 0).clientState s (buildOutScope args)
    let outScope := bucketOutScope args.x bucket
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (buildOutScope args)) ∧
      s'.frontier ≤ s.frontier + 2 * (args.bucketLen * maxScope) ∧
      PreservesBelow s.frontier s s' ∧
      s.frontier ≤ res.1 ∧
      res.2 = outScope.length ∧
      HoldsIn res.1 outScope s' ∧
      memoryCost (buildOutScope args) s ≤
        2 + args.bucketLen * (3 + 2 * maxScope + maxScope * (2 + W_out)) := by
  dsimp only
  unfold buildOutScope
  have hK_le : (bucket.flatMap FactorTable.scope).length ≤ args.bucketLen * maxScope := by
    rw [← hlen, List.length_flatMap]
    simpa using
      List.sum_le_length_nsmul (bucket.map (·.scope.length)) maxScope (by simpa using hmax)
  have hss_cost := sumScopeLen_cost ⟨args.bucketPtr, args.bucketLen⟩ s
  obtain ⟨hfl_val, hfl_fr, hfl_pres, hfl_res, hfl_holds, hfl_cost⟩ :=
    flattenScopes_spec (w := w) (args := ⟨args.bucketPtr, args.bucketLen, _⟩) hwf hb hlen rfl hmax
      (hfit.of_le (by dsimp only; omega))
  have hwf₁ := wellFormed_clientState hwf hfl_val
  rw [validHistory_bind', StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, memoryCost_bind', sumScopeLen_state,
    sumScopeLen_result hb hlen, validHistory_bind', StateTransitionSpec.clientResult_bind,
    StateTransitionSpec.clientState_bind, memoryCost_bind', hfl_res, bucketOutScope_eq_foldr]
  rw [hfl_res] at hfl_holds
  generalize (Memory.spec 0).clientState s (flattenScopes ⟨args.bucketPtr, args.bucketLen,
    (bucket.flatMap FactorTable.scope).length⟩) = s₁ at hwf₁ hfl_fr hfl_pres hfl_holds ⊢
  obtain ⟨hdd_val, hdd_fr, hdd_pres, hdd_lo, hdd_len, hdd_holds, hdd_cost⟩ :=
    dedupFilterBack_spec (w := w) (args := ⟨args.x, s.frontier, _⟩) hwf₁ hfl_holds rfl
      (bucketOutScope_eq_foldr args.x bucket ▸ hW) (hfit.of_le (by dsimp only at hfl_fr ⊢; omega))
  dsimp only at hss_cost hfl_cost hdd_cost hfl_fr hdd_fr
  refine ⟨⟨sumScopeLen_valid hb hlen, hfl_val, hdd_val⟩, by omega,
    hfl_pres.trans (hdd_pres.mono_bound hfl_pres.2.1), hfl_pres.2.1.trans hdd_lo, hdd_len,
    hdd_holds, ?_⟩
  have hK_cost := Nat.mul_le_mul_right (2 + W_out) hK_le
  calc _ ≤ args.bucketLen + ((1 + args.bucketLen * (2 + 2 * maxScope)) +
        (1 + args.bucketLen * maxScope * (2 + W_out))) :=
      Nat.add_le_add hss_cost (Nat.add_le_add hfl_cost (by omega))
    _ = 2 + args.bucketLen * (3 + 2 * maxScope + maxScope * (2 + W_out)) := by ring

theorem buildOutScope_realizes :
    Realizes .exact buildOutScope WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧
        ∃ bucket, bucket.length = args.bucketLen ∧ HoldsFactorList args.bucketPtr bucket s ∧
          Fits w (s.frontier + 2 * (bucket.flatMap FactorTable.scope).length))
      (fun _ _ => 0) := by
  unfold buildOutScope
  realize [sumScopeLen_realizes, flattenScopes_realizes, dedupFilterBack_realizes]
  · obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    exact ⟨bucket, hlen, hb, hfit.of_le (by omega)⟩
  · obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    exact hfit.of_le (by omega)
  · obtain ⟨_, bucket, hlen, hb, _⟩ := h
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    exact ⟨bucket, hlen, hb, rfl⟩
  · exact h.1
  all_goals
    obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    have hscK : ∀ f ∈ bucket, f.scope.length ≤ (bucket.flatMap FactorTable.scope).length :=
      fun f hf => by rw [List.length_flatMap]; exact List.le_sum_of_mem (List.mem_map_of_mem hf)
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    obtain ⟨_, hfl_fr, _, hfl_res, _, _⟩ :=
      flattenScopes_spec (w := w) (args := ⟨d.bucketPtr, d.bucketLen, _⟩) hmem hb hlen rfl hscK
        (hfit.of_le (by dsimp only; omega))
  · rw [hfl_res, hfl_fr]
  · rw [hfl_fr]
    exact hfit.of_le (by dsimp only; omega)

end Cslib.Algorithms.WordRAM.VariableElimination
