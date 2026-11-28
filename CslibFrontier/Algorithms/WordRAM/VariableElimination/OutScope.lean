/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.FlattenScope
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Foundations.Data.List.Counting
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
  dsimp only at hflat hlen hW hfit ⊢
  subst hlen
  let out (k : ℕ) := (flat.drop (flat.length - k)).foldr (dedupStepPure x) []
  have hout_le (k) : (out k).length ≤ W_out := by
    refine le_trans ?_ hW
    conv_rhs => rw [← List.take_append_drop (flat.length - k) flat, List.foldr_append]
    exact length_le_foldr_dedupStepPure x _ _
  have hfl := hflat.1
  obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w) (body := dedupBackStep)
    (safe := fun _ _ _ => True) (d := (x, flatPtr)) (n := flat.length) (c := 2 + W_out)
    (s := ⟨s.mem, s.frontier + flat.length⟩) (a₀ := ⟨flat.length, s.frontier + flat.length, 0⟩)
    (S := Set.Ici s.frontier)
    (fun k st t => t.frontier = s.frontier + flat.length ∧ st.remPos = flat.length - k ∧
      st.outLen = (out k).length ∧ st.outStart = s.frontier + flat.length - (out k).length ∧
      (out k).length ≤ k ∧ Block.HoldsList st.outStart (out k) t.mem)
    ⟨rfl, by simp, by simp [out], by simp [out], by simp [out],
      by simpa [out] using Block.holdsList_nil _ _⟩
    (fun k hk ⟨rem, ost, olen⟩ t ⟨hfr, hrem, holen, host, hle, hacc⟩ hmod => by
      dsimp only at hrem holen host hacc ⊢
      subst hrem holen host
      have hi : flat.length - k - 1 < flat.length := by omega
      have hv : t.mem (flatPtr + (flat.length - k - 1)) = flat[flat.length - k - 1] :=
        (hmod.2 _ (by dsimp only; omega) (by simp; omega)).trans (hflat.get _ hi)
      have hvfit : Fits w (t.mem (flatPtr + (flat.length - k - 1))) :=
        hv ▸ hflat.get _ hi ▸ hwf.mem_fits _
      have hout : out (k + 1) = dedupStepPure x flat[flat.length - k - 1] (out k) := by
        simp only [out, show flat.length - (k + 1) = flat.length - k - 1 by omega,
          List.drop_eq_getElem_cons hi, List.foldr_cons,
          show flat.length - k - 1 + 1 = flat.length - k by omega]
      have hms := memScan_framed (w := w) ⟨t.mem (flatPtr + (flat.length - k - 1)),
        s.frontier + flat.length - (out k).length, (out k).length⟩ hacc rfl (by dsimp only; omega)
      have hW_k := hout_le k
      refine ⟨trivial, ?_⟩
      unfold dedupBackStep
      framed_triple
      · rename_i hc
        rw [hv] at hc
        dsimp only; rw [hout, dedupStepPure, ite_eq_left (by simpa using hc)]
        exact ⟨hfr, by omega, rfl, rfl, by omega, hacc⟩
      · rename_i hc
        rw [hv] at hc
        dsimp only; rw [hout, dedupStepPure, ite_eq_right (by simpa using hc), List.length_cons]
        refine ⟨hfr, by omega, rfl, by omega, by omega, Block.holdsList_cons_iff.mpr
          ⟨by rw [hv]; exact Function.update_self .., ?_⟩⟩
        rw [Nat.sub_add_cancel (by omega)]
        exact hacc.frame fun a hlo _ => Function.update_of_ne (by omega) _ _)
    fun st t h _ => h
  have hft : Memory.FramedTriple w s (dedupFilterBack ⟨x, flatPtr, flat.length⟩)
      (1 + flat.length * (2 + W_out)) (Set.Ici s.frontier) fun r t =>
        t.frontier = s.frontier + flat.length ∧ s.frontier ≤ r.1 ∧ r.2 = (out flat.length).length ∧
        HoldsIn r.1 (out flat.length) t := by
    unfold dedupFilterBack
    exact Memory.FramedTriple.mono (c := (2 + W_out) * flat.length + 0 + 1)
      (Memory.FramedTriple.allocDirty_bind hfit (Memory.FramedTriple.call hloop subset_rfl
        fun _ t ⟨hfr, _, hl, hs, hle, hh⟩ _ => Memory.FramedTriple.pure
          ⟨hfr, by omega, hl, by omega, hh⟩)) (by rw [Nat.mul_comm]; omega) fun _ _ => id
  obtain ⟨hv, hc, hm, hfr, hlo, hlen, hh⟩ := framedTriple_iff_realization.mp hft
  simp only [out, Nat.sub_self, List.drop_zero] at hlen hh
  exact ⟨hv, hfr, preservesBelow_of_modifies hm (.refl le_rfl), hlo, hlen, hh, hc⟩

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
  have hK_le : (bucket.flatMap FactorTable.scope).length ≤ args.bucketLen * maxScope :=
    hlen ▸ List.length_flatMap_le hmax
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
    hfl_pres.trans_frontier hdd_pres, hfl_pres.2.1.trans hdd_lo, hdd_len,
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
