/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.CopyFilter
import CslibFrontier.Tactic.Realize

/-!
# Pure Scope Deduplication, `sumScopeLen`, and `flattenScopes`

Computes total concatenated bucket-scope length (`sumScopeLen`) and copies all bucket scopes into a
contiguous flat array (`flattenScopes`), paired with the `foldr` characterization of
`bucketOutScope`.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.dedupStepPure`: pure scope deduplication step.
* `Cslib.Algorithms.WordRAM.VariableElimination.sumScopeLen`: total bucket-scope length reader.
* `Cslib.Algorithms.WordRAM.VariableElimination.flattenScopes`: bucket-scope concatenator.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Output scope materialization (`buildOutScope`) -/

/-- Pure deduplicating insertion step avoiding the eliminated variable `x`. -/
@[expose] def dedupStepPure (x v : ℕ) (acc : List ℕ) : List ℕ :=
  if v = x ∨ v ∈ acc then acc else v :: acc

theorem length_le_foldr_dedupStepPure (x : ℕ) :
    ∀ (ys acc : List ℕ), acc.length ≤ (ys.foldr (dedupStepPure x) acc).length
  | [], acc => le_rfl
  | v :: rest, acc => by
    simp only [List.foldr_cons, dedupStepPure]
    split_ifs <;> exact (length_le_foldr_dedupStepPure x rest acc).trans (by simp)

private theorem filter_dedup_eq_foldr (x : ℕ) :
    ∀ (xs : List ℕ), (xs.dedup.filter fun v => decide (v ≠ x)) = xs.foldr (dedupStepPure x) []
  | [] => rfl
  | v :: rest => by
    rw [List.dedup_cons, List.foldr_cons, ← filter_dedup_eq_foldr x rest]
    unfold dedupStepPure
    obtain rfl | hvx := eq_or_ne v x <;> by_cases hmem : v ∈ rest <;> simp [*]

theorem bucketOutScope_eq_foldr (x : ℕ) (bucket : List (FactorTable ℕ ℕ)) :
    bucketOutScope x bucket = (bucket.flatMap FactorTable.scope).foldr (dedupStepPure x) [] :=
  filter_dedup_eq_foldr x _

/-- Arguments `(bucketPtr, bucketLen)` for `sumScopeLen`. -/
structure SumScopeArgs where
  /-- Field `bucketPtr` of `SumScopeArgs`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `SumScopeArgs`. -/
  bucketLen : ℕ

/-- Product equivalence encoding `SumScopeArgs` as words. -/
@[expose] def SumScopeArgs.equiv : SumScopeArgs ≃ ℕ × ℕ where
  toFun s := (s.bucketPtr, s.bucketLen)
  invFun := fun (bucketPtr, bucketLen) => ⟨bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding SumScopeArgs := .ofEquiv SumScopeArgs.equiv

private def sumScopeStep (p : Unit × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  Memory.read (p.2.1 + 1) >>= fun scLen => pure (p.2.1 + 4, p.2.2 + scLen)

/-- Compute the total length of all scopes inside a bucket descriptor array. -/
def sumScopeLen (args : SumScopeArgs) : Memory.Prog ℕ :=
  iterate sumScopeStep () args.bucketLen (args.bucketPtr, 0) >>= fun r => pure r.2

theorem sumScopeLen_state (args : SumScopeArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (sumScopeLen args) = s := by
  unfold sumScopeLen
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of sumScopeStep () (fun _ _ => rfl) args.bucketLen _ s

theorem sumScopeLen_cost (args : SumScopeArgs) (s : Memory.State) :
    memoryCost (sumScopeLen args) s ≤ args.bucketLen := by
  unfold sumScopeLen
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  simpa using memoryCost_iterate_le_of sumScopeStep 1 () (fun _ _ => le_rfl)
    args.bucketLen (args.bucketPtr, 0) s

theorem sumScopeLen_valid {w : ℕ} {args : SumScopeArgs} {bucket : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (hb : HoldsFactorList args.bucketPtr bucket s)
    (hlen : bucket.length = args.bucketLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (sumScopeLen args)) := by
  rw [sumScopeLen, ← hlen]
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur acc : ℕ), HoldsFactorList cur fs s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate sumScopeStep () fs.length (cur, acc))) from
    this bucket args.bucketPtr 0 hb
  intro fs
  induction fs with
  | nil => exact fun _ _ _ => validHistory_pure w s _
  | cons f rest ih =>
    exact fun cur acc ⟨hf, hrest⟩ => validHistory_bind_step
      (validHistory_read_bind (Nat.lt_of_lt_of_le (by omega : cur + 1 < cur + 4) hf.1)
        (validHistory_pure w s _))
      (ih (cur + 4) (acc + s.mem (cur + 1)) hrest)

theorem sumScopeLen_result {args : SumScopeArgs} {bucket : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (hb : HoldsFactorList args.bucketPtr bucket s)
    (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (sumScopeLen args) =
      (bucket.flatMap FactorTable.scope).length := by
  unfold sumScopeLen
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure, ← hlen]
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur acc : ℕ), HoldsFactorList cur fs s →
      ((Memory.spec 0).clientResult s (iterate sumScopeStep () fs.length (cur, acc))).2 =
      acc + (fs.flatMap FactorTable.scope).length by
    simpa using this bucket args.bucketPtr 0 hb
  intro fs
  induction fs with
  | nil => exact fun cur acc _ => (Nat.add_zero acc).symm
  | cons f rest ih =>
    rintro cur acc ⟨hf, hrest⟩
    erw [StateTransitionSpec.clientResult_bind, ih (cur + 4) (acc + s.mem (cur + 1)) hrest]
    rw [hf.2.1, List.flatMap_cons, List.length_append, Nat.add_assoc]

theorem sumScopeLen_realizes :
    Realizes .exact sumScopeLen WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        ∃ bucket, bucket.length = args.bucketLen ∧ HoldsFactorList args.bucketPtr bucket s ∧
          Fits w ((bucket.flatMap FactorTable.scope).length))
      (fun _ _ => 0) := by
  unfold sumScopeLen
  realize
  obtain ⟨bucket, hlen, hb, hfit_K⟩ := h
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st t => t = s ∧ ∃ rem, rem.length = j ∧ HoldsFactorList st.1 rem s ∧
      st.2 + (rem.flatMap FactorTable.scope).length = (bucket.flatMap FactorTable.scope).length)
    (fun j st _ ⟨rfl, rem, hrem_l, hrem_h, hsum⟩ => ?_)
    ⟨rfl, bucket, hlen, hb, Nat.zero_add _⟩
  dsimp only
  rcases rem with _ | ⟨f, rest⟩
  · simp at hrem_l
  simp only [List.length_cons, Nat.add_right_cancel_iff, List.flatMap_cons, List.length_append]
    at hrem_l hsum
  obtain ⟨hf, hrest⟩ := hrem_h
  exact ⟨⟨hmem.frontier_fits.of_le (by have := hf.1; omega), hmem.frontier_fits.of_le hf.1,
    hfit_K.of_le (by rw [hf.2.1]; omega)⟩, rfl, rest, hrem_l, hrest,
    Nat.add_assoc .. ▸ hf.2.1 ▸ hsum⟩

/-- Arguments for concatenating all bucket scopes into a scratch buffer. -/
structure FlattenArgs where
  /-- Field `bucketPtr` of `FlattenArgs`. -/
  bucketPtr : ℕ
  /-- Field `bucketLen` of `FlattenArgs`. -/
  bucketLen : ℕ
  /-- Field `flatLen` of `FlattenArgs`. -/
  flatLen : ℕ

/-- Product equivalence encoding `FlattenArgs` as words. -/
@[expose] def FlattenArgs.equiv : FlattenArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.bucketPtr, s.bucketLen), s.flatLen)
  invFun := fun ((bucketPtr, bucketLen), flatLen) => ⟨bucketPtr, bucketLen, flatLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding FlattenArgs := .ofEquiv FlattenArgs.equiv

private def flattenStep (p : Unit × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  Memory.read p.2.1 >>= fun scPtr =>
  Memory.read (p.2.1 + 1) >>= fun scLen =>
  copyWords ⟨scPtr, p.2.2, scLen⟩ >>= fun _ =>
  pure (p.2.1 + 4, p.2.2 + scLen)

/-- Concatenate every factor scope in a bucket into one flat word buffer. -/
def flattenScopes (args : FlattenArgs) : Memory.Prog ℕ :=
  Memory.allocDirty args.flatLen >>= fun flatPtr =>
  iterate flattenStep () args.bucketLen (args.bucketPtr, flatPtr) >>= fun _ =>
  pure flatPtr

theorem flattenScopes_spec {w : ℕ} {args : FlattenArgs} {bucket : List (FactorTable ℕ ℕ)}
    {maxScope : ℕ} {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen)
    (hflat : (bucket.flatMap FactorTable.scope).length = args.flatLen)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope)
    (hfit : Fits w (s.frontier + args.flatLen)) :
    let res := (Memory.spec 0).clientResult s (flattenScopes args)
    let s' := (Memory.spec 0).clientState s (flattenScopes args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (flattenScopes args)) ∧
      s'.frontier = s.frontier + args.flatLen ∧
      PreservesBelow s.frontier s s' ∧
      res = s.frontier ∧
      HoldsIn res (bucket.flatMap FactorTable.scope) s' ∧
      memoryCost (flattenScopes args) s ≤ 1 + args.bucketLen * (2 + 2 * maxScope) := by
  unfold flattenScopes
  have hloop : ∀ (rem : List (FactorTable ℕ ℕ)) (cur : ℕ) (acc : List ℕ) (t : Memory.State),
      Memory.WellFormed w t → t.frontier = s.frontier + args.flatLen →
      PreservesBelow s.frontier s t → HoldsFactorList cur rem s →
      (∀ f ∈ rem, f.scope.length ≤ maxScope) →
      acc.length + (rem.flatMap FactorTable.scope).length = args.flatLen →
      Block.HoldsList s.frontier acc t.mem →
      let p := iterate flattenStep () rem.length (cur, s.frontier + acc.length)
      let t' := (Memory.spec 0).clientState t p
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = s.frontier + args.flatLen ∧ PreservesBelow s.frontier s t' ∧
        Block.HoldsList s.frontier (acc ++ rem.flatMap FactorTable.scope) t'.mem ∧
        memoryCost p t ≤ rem.length * (2 + 2 * maxScope) := by
    intro rem cur acc t hwf_t hfr hpres hfl hmax_r hlen_eq hacc
    induction rem generalizing cur acc t with
    | nil =>
      simp only [List.length_nil, List.flatMap_nil, List.append_nil, Nat.zero_mul]
      exact ⟨validHistory_pure w t _, hfr, hpres, hacc, by simp [iterate]⟩
    | cons f rest ih =>
      obtain ⟨⟨hd, hsl, hel, hsc, _⟩, hrest⟩ := hfl
      simp only [List.flatMap_cons, List.length_append] at hlen_eq
      have hm0 : t.mem cur = s.mem cur := hpres.2.2 _ (by omega)
      have hm1 : t.mem (cur + 1) = f.scope.length := (hpres.2.2 _ (by omega)).trans hsl
      obtain ⟨hcw_val, hcw_fr, hcw_pres, hcw_holds⟩ :=
        copyWords_spec (w := w) ⟨t.mem cur, s.frontier + acc.length, t.mem (cur + 1)⟩ hwf_t
          (by rw [hm0]; exact (hsc.mono_frontier hpres).2) hm1.symm (F := s.frontier + acc.length)
          (by dsimp only; rw [hm0, hm1]; have := hsc.1; omega) le_rfl
          (by dsimp only; rw [hm1]; omega)
      have hcc := copyWords_cost ⟨t.mem cur, s.frontier + acc.length, t.mem (cur + 1)⟩ t
      have hfm := hmax_r f (List.mem_cons_self ..)
      obtain ⟨hv_i, hfr_i, hpres_i, hholds_i, hcost_i⟩ :=
        ih (cur + 4) (acc ++ f.scope) _ (wellFormed_clientState hwf_t hcw_val) (hcw_fr.trans hfr)
          (hpres.trans (hcw_pres.mono_bound (Nat.le_add_right _ _))) hrest
          (fun g hg => hmax_r g (List.mem_cons_of_mem f hg)) (by rw [List.length_append]; omega)
          (Block.holdsList_append_iff.mpr
            ⟨hacc.frame fun a _ hhi => hcw_pres.2.2 a hhi, hcw_holds⟩)
      -- One step reads the scope descriptor and copies the scope to the end of the buffer.
      have hnext : s.frontier + acc.length + t.mem (cur + 1) =
          s.frontier + (acc ++ f.scope).length := by
        rw [List.length_append, hm1, Nat.add_assoc]
      dsimp only [List.length_cons, iterate]
      rw [validHistory_bind', StateTransitionSpec.clientState_bind, memoryCost_bind']
      dsimp only [flattenStep]
      rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read,
        memoryCost_bind', memoryCost_read, clientState_read, clientResult_read,
        memoryCost_bind', memoryCost_pure, clientState_bind_read, clientState_bind_read,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure,
        clientResult_bind_read, clientResult_bind_read, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_pure, hnext, Nat.add_one_mul]
      simp only [List.flatMap_cons, ← List.append_assoc]
      exact ⟨⟨validHistory_read_bind (by omega) (validHistory_read_bind (by omega)
        (validHistory_bind_step hcw_val (validHistory_pure w _ _))), hv_i⟩,
        hfr_i, hpres_i, hholds_i, by dsimp only at hcc; omega⟩
  obtain ⟨hv_l, hfr_l, hpres_l, hholds_l, hcost_l⟩ :=
    hloop bucket args.bucketPtr [] ⟨s.mem, s.frontier + args.flatLen⟩
      (hwf.step (o := .allocDirty args.flatLen) hfit) rfl
      ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩ hb hmax (by simpa using hflat)
      (Block.holdsList_nil _ _)
  simp only [List.length_nil, Nat.add_zero, List.nil_append] at hv_l hfr_l hpres_l hholds_l hcost_l
  rw [← hlen, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    memoryCost_bind', clientState_allocDirty, clientResult_allocDirty, memoryCost_allocDirty,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    memoryCost_bind', StateTransitionSpec.clientResult_pure, StateTransitionSpec.clientState_pure,
    memoryCost_pure]
  exact ⟨validHistory_allocDirty_bind hfit (validHistory_bind_step hv_l (validHistory_pure w _ _)),
    hfr_l, hpres_l, rfl, ⟨by omega, hholds_l⟩, by omega⟩

theorem flattenScopes_realizes :
    Realizes .exact flattenScopes WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w (s.frontier + args.flatLen) ∧
        ∃ bucket, bucket.length = args.bucketLen ∧ HoldsFactorList args.bucketPtr bucket s ∧
          (bucket.flatMap FactorTable.scope).length = args.flatLen)
      (fun _ _ => 0) := by
  unfold flattenScopes
  realize [copyWords_realizes]
  obtain ⟨hfit, bucket, hlen, hb, hflat⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun j st t =>
      t.frontier = s.frontier + d.flatLen ∧
      PreservesBelow s.frontier s t ∧
      s.frontier ≤ st.2 ∧
      ∃ rem, rem.length = j ∧ HoldsFactorList st.1 rem s ∧
        st.2 + (rem.flatMap FactorTable.scope).length = s.frontier + d.flatLen)
    (fun j st t ⟨hfr, hpres, hdst_lo, rem, hrem_l, hrem_h, hsum⟩ => ?_)
    ⟨rfl, ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩, le_rfl, bucket, hlen, hb, hflat ▸ rfl⟩
  dsimp only
  rcases rem with _ | ⟨f, rest⟩
  · simp at hrem_l
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
  simp only [List.flatMap_cons, List.length_append] at hsum
  obtain ⟨⟨hd, hsl, hel, hsc, _⟩, hrest⟩ := hrem_h
  have hm0 : t.mem st.1 = s.mem st.1 := hpres.2.2 _ (by omega)
  have hm1 : t.mem (st.1 + 1) = f.scope.length := (hpres.2.2 _ (by omega)).trans hsl
  have hfit1 : Fits w (st.2 + t.mem (st.1 + 1)) := hm1 ▸ hfit.of_le (by omega)
  refine ⟨⟨hfit.of_le (by omega),
    ⟨hm0 ▸ hm1 ▸ hfit.of_le (hsc.1.trans (Nat.le_add_right _ _)), hfit1⟩,
    hfit.of_le (by omega), hfit1⟩, ?_⟩
  dsimp only [flattenStep]
  rw [clientState_bind_read, clientState_bind_read, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientState_pure, clientResult_bind_read, clientResult_bind_read,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
  obtain ⟨hcw_fr, hcw_mem⟩ := copyWords_frame ⟨t.mem st.1, st.2, t.mem (st.1 + 1)⟩ t
  exact ⟨hcw_fr.trans hfr, ⟨le_rfl, hcw_fr.symm ▸ hpres.2.1, fun a ha =>
    (hcw_mem a (lt_of_lt_of_le ha hdst_lo)).trans (hpres.2.2 a ha)⟩, by dsimp only; omega, rest,
    hrem_l, hrest, Nat.add_assoc .. ▸ hm1.symm ▸ hsum⟩

end Cslib.Algorithms.WordRAM.VariableElimination
