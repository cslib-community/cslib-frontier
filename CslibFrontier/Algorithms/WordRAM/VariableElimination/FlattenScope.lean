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
    simp only [List.foldr_cons]
    refine (length_le_foldr_dedupStepPure x rest acc).trans ?_
    unfold dedupStepPure
    split_ifs <;> simp

private theorem filter_dedup_eq_foldr (x : ℕ) :
    ∀ (xs : List ℕ), (xs.dedup.filter fun v => decide (v ≠ x)) = xs.foldr (dedupStepPure x) []
  | [] => rfl
  | v :: rest => by
    rw [List.dedup_cons, List.foldr_cons, ← filter_dedup_eq_foldr x rest]
    unfold dedupStepPure
    by_cases hmem : v ∈ rest
    · rw [ite_eq_left hmem]
      by_cases hvx : v = x
      · exact (ite_eq_left (Or.inl hvx)).symm
      · have hmem_f : v ∈ rest.dedup.filter (fun u => decide (u ≠ x)) :=
          List.mem_filter.mpr ⟨List.mem_dedup.mpr hmem, decide_eq_true hvx⟩
        exact (ite_eq_left (Or.inr hmem_f)).symm
    · rw [ite_eq_right hmem, List.filter_cons]
      by_cases hvx : v = x
      · subst hvx
        simp
      · have hnot_f : ¬ (v = x ∨ v ∈ rest.dedup.filter (fun u => decide (u ≠ x))) := by
          rintro (rfl | hf)
          · exact hvx rfl
          · exact hmem (List.mem_dedup.mp (List.mem_filter.mp hf).1)
        rw [decide_eq_true hvx, ite_eq_left rfl, ite_eq_right hnot_f]

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
  unfold sumScopeLen
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  rw [← hlen]
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur acc : ℕ), HoldsFactorList cur fs s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate sumScopeStep () fs.length (cur, acc))) from
    this bucket args.bucketPtr 0 hb
  intro fs
  induction fs with
  | nil => intro _ _ _; exact validHistory_pure w s _
  | cons f rest ih =>
    intro cur acc ⟨hf, hrest⟩
    have hlt : cur + 1 < s.frontier := by have := hf.1; omega
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (sumScopeStep ((), (cur, acc)) >>= iterate sumScopeStep () rest.length))
    refine validHistory_bind_step
      (validHistory_read_bind hlt (validHistory_pure w s _)) ?_
    exact ih (cur + 4) (acc + s.mem (cur + 1)) hrest

theorem sumScopeLen_result {args : SumScopeArgs} {bucket : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (hb : HoldsFactorList args.bucketPtr bucket s)
    (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (sumScopeLen args) =
      (bucket.flatMap FactorTable.scope).length := by
  unfold sumScopeLen
  rw [StateTransitionSpec.clientResult_bind, ← hlen]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur acc : ℕ), HoldsFactorList cur fs s →
      ((Memory.spec 0).clientResult s (iterate sumScopeStep () fs.length (cur, acc))).2 =
      acc + (fs.flatMap FactorTable.scope).length by
    simpa using this bucket args.bucketPtr 0 hb
  intro fs
  induction fs with
  | nil => intro cur acc _; change acc = acc + 0; simp
  | cons f rest ih =>
    intro cur acc ⟨hf, hrest⟩
    change ((Memory.spec 0).clientResult s
      (sumScopeStep ((), (cur, acc)) >>= iterate sumScopeStep () rest.length)).2 = _
    rw [StateTransitionSpec.clientResult_bind]
    have hst : (Memory.spec 0).clientState s (sumScopeStep ((), (cur, acc))) = s := rfl
    have hres : (Memory.spec 0).clientResult s (sumScopeStep ((), (cur, acc))) =
        (cur + 4, acc + f.scope.length) := by
      change (cur + 4, acc + s.mem (cur + 1)) = _
      rw [hf.2.1]
    rw [hst, hres, ih (cur + 4) _ hrest, List.flatMap_cons, List.length_append, Nat.add_assoc]

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
    (fun j st t ⟨ht, rem, hrem_l, hrem_h, hsum⟩ => ?_)
    ⟨rfl, bucket, hlen, hb, Nat.zero_add _⟩
  subst t
  dsimp only
  rcases rem with _ | ⟨f, rest⟩
  · simp at hrem_l
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
  obtain ⟨hf, hrest⟩ := hrem_h
  simp only [List.flatMap_cons, List.length_append] at hsum
  refine ⟨?_, rfl, rest, hrem_l, hrest, ?_⟩
  · exact ⟨hmem.frontier_fits.of_le (by have := hf.1; omega),
      hmem.frontier_fits.of_le hf.1,
      hfit_K.of_le (by rw [hf.2.1]; omega)⟩
  · change (st.2 + s.mem (st.1 + 1)) + (rest.flatMap FactorTable.scope).length = _
    rw [hf.2.1]
    omega

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
  dsimp only
  unfold flattenScopes
  have hv_a : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty args.flatLen)) :=
    validHistory_allocDirty hfit
  let s₀ : Memory.State := ⟨s.mem, s.frontier + args.flatLen⟩
  have hwf₀ : Memory.WellFormed w s₀ := hwf.step (o := .allocDirty args.flatLen) hfit
  have hloop : ∀ (rem : List (FactorTable ℕ ℕ)) (cur : ℕ) (acc : List ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      t.frontier = s.frontier + args.flatLen →
      PreservesBelow s.frontier s t →
      HoldsFactorList cur rem s →
      (∀ f ∈ rem, f.scope.length ≤ maxScope) →
      acc.length + (rem.flatMap FactorTable.scope).length = args.flatLen →
      Block.HoldsList s.frontier acc t.mem →
      let p := iterate flattenStep () rem.length (cur, s.frontier + acc.length)
      let t' := (Memory.spec 0).clientState t p
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = s.frontier + args.flatLen ∧
        PreservesBelow s.frontier s t' ∧
        Block.HoldsList s.frontier (acc ++ rem.flatMap FactorTable.scope) t'.mem ∧
        memoryCost p t ≤ rem.length * (2 + 2 * maxScope) := by
    intro rem
    induction rem with
    | nil =>
      intro cur acc t _ hfr hpres _ _ _ hacc
      simp only [List.length_nil, List.flatMap_nil, List.append_nil, Nat.zero_mul]
      exact ⟨validHistory_pure w t _, hfr, hpres, hacc, by simp [iterate]⟩
    | cons f rest ih =>
      intro cur acc t hwf_t hfr hpres ⟨hf, hrest⟩ hmax_r hlen_eq hacc
      simp only [List.flatMap_cons, List.length_append] at hlen_eq
      obtain ⟨hd, hsl, hel, hsc, _⟩ := hf
      have hm0 : t.mem cur = s.mem cur := hpres.2.2 _ (by omega)
      have hm1 : t.mem (cur + 1) = s.mem (cur + 1) := hpres.2.2 _ (by omega)
      have hsc_t : Block.HoldsList (t.mem cur) f.scope t.mem := by
        rw [hm0]; exact (hsc.mono_frontier hpres).2
      have hsc_len : f.scope.length = t.mem (cur + 1) := by rw [hm1, hsl]
      let cwArgs : CopyArgs := ⟨t.mem cur, s.frontier + acc.length, t.mem (cur + 1)⟩
      obtain ⟨hcw_val, hcw_fr, hcw_pres, hcw_holds⟩ :=
        copyWords_spec (w := w) cwArgs hwf_t hsc_t hsc_len
          (F := s.frontier + acc.length)
          (by dsimp only [cwArgs]; rw [hm0, hm1, hsl]; have := hsc.1; omega)
          le_rfl (by dsimp only [cwArgs]; rw [hm1, hsl]; omega)
      let t₁ := (Memory.spec 0).clientState t (copyWords cwArgs)
      have hwf₁ : Memory.WellFormed w t₁ :=
        wellFormed_clientState hwf_t hcw_val
      have hpres₁ : PreservesBelow s.frontier s t₁ :=
        hpres.trans (hcw_pres.mono_bound (Nat.le_add_right _ _))
      have hacc₁ : Block.HoldsList s.frontier (acc ++ f.scope) t₁.mem :=
        Block.holdsList_append_iff.mpr
          ⟨hacc.frame (fun a hlo hhi => hcw_pres.2.2 a hhi), hcw_holds⟩
      have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hstep_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (flattenStep ((), (cur, s.frontier + acc.length)))) := by
        unfold flattenStep
        dsimp only
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_read_bind (by omega) ?_
        exact validHistory_bind_step hcw_val (validHistory_pure w _ _)
      have hstep_st : (Memory.spec 0).clientState t
          (flattenStep ((), (cur, s.frontier + acc.length))) = t₁ := by
        unfold flattenStep
        dsimp only
        rw [StateTransitionSpec.clientState_bind, hr_t, hres_t,
          StateTransitionSpec.clientState_bind, hr_t, hres_t,
          StateTransitionSpec.clientState_bind]
        rfl
      have hstep_res : (Memory.spec 0).clientResult t
          (flattenStep ((), (cur, s.frontier + acc.length))) =
          (cur + 4, s.frontier + (acc ++ f.scope).length) := by
        unfold flattenStep
        dsimp only
        rw [StateTransitionSpec.clientResult_bind, hr_t, hres_t,
          StateTransitionSpec.clientResult_bind, hr_t, hres_t,
          StateTransitionSpec.clientResult_bind]
        change (cur + 4, s.frontier + acc.length + t.mem (cur + 1)) = _
        rw [← hsc_len, List.length_append, Nat.add_assoc]
      have hstep_cost : memoryCost (flattenStep ((), (cur, s.frontier + acc.length))) t ≤
          2 + 2 * maxScope := by
        unfold flattenStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, hr_t, hres_t,
          memoryCost_bind', memoryCost_read, hr_t, hres_t,
          memoryCost_bind', memoryCost_pure, Nat.add_zero]
        have hcc := copyWords_cost cwArgs t
        dsimp only [cwArgs] at hcc
        rw [← hsc_len] at hcc ⊢
        have hfm : 2 * f.scope.length ≤ 2 * maxScope :=
          Nat.mul_le_mul_left 2 (hmax_r f (List.mem_cons_self ..))
        omega
      obtain ⟨hv_i, hfr_i, hpres_i, hholds_i, hcost_i⟩ :=
        ih (cur + 4) (acc ++ f.scope) t₁ hwf₁ (hcw_fr.trans hfr) hpres₁ hrest
          (fun g hg => hmax_r g (List.mem_cons_of_mem f hg))
          (by rw [List.length_append]; omega) hacc₁
      dsimp only
      have hiter_eq : iterate flattenStep () (f :: rest).length (cur, s.frontier + acc.length) =
          (flattenStep ((), (cur, s.frontier + acc.length)) >>=
            iterate flattenStep () rest.length) := rfl
      rw [hiter_eq, StateTransitionSpec.clientState_bind, hstep_st, hstep_res,
        memoryCost_bind', hstep_st, hstep_res]
      simp only [List.flatMap_cons, ← List.append_assoc]
      refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hv_i),
        hfr_i, hpres_i, hholds_i, ?_⟩
      calc memoryCost (flattenStep ((), (cur, s.frontier + acc.length))) t + _
          ≤ (2 + 2 * maxScope) + rest.length * (2 + 2 * maxScope) :=
            Nat.add_le_add hstep_cost hcost_i
        _ = (f :: rest).length * (2 + 2 * maxScope) := by simp only [List.length_cons]; ring
  obtain ⟨hv_l, hfr_l, hpres_l, hholds_l, hcost_l⟩ :=
    hloop bucket args.bucketPtr [] s₀ hwf₀ rfl ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
      hb hmax (by simpa using hflat) (Block.holdsList_nil _ _)
  simp only [List.length_nil, Nat.add_zero, List.nil_append] at hv_l hfr_l hpres_l hholds_l hcost_l
  have ha_st : (Memory.spec 0).clientState s (Memory.allocDirty args.flatLen) = s₀ := rfl
  have ha_res : (Memory.spec 0).clientResult s (Memory.allocDirty args.flatLen) = s.frontier := rfl
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  rw [← hlen]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
  rw [hlen, ha_st, ha_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hpure_res, hpure_st]
  rw [← hlen]
  refine ⟨validHistory_bind_step hv_a ?_,
    by rw [hlen] at hfr_l ⊢; exact hfr_l, hpres_l, rfl, ?_, ?_⟩
  · rw [hlen, ha_st, ha_res, ← hlen]
    exact validHistory_bind_step hv_l (validHistory_pure w _ _)
  · refine ⟨?_, hholds_l⟩
    rw [hfr_l]
    omega
  · rw [hlen, memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res, memoryCost_bind',
      memoryCost_pure, Nat.add_zero, ← hlen]
    omega

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
    ⟨rfl, ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩, le_rfl, bucket, hlen, hb,
      by rw [hflat]⟩
  dsimp only
  rcases rem with _ | ⟨f, rest⟩
  · simp at hrem_l
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
  simp only [List.flatMap_cons, List.length_append] at hsum
  obtain ⟨hf, hrest⟩ := hrem_h
  obtain ⟨hd, hsl, hel, hsc, _⟩ := hf
  have hm0 : t.mem st.1 = s.mem st.1 := hpres.2.2 _ (by omega)
  have hm1 : t.mem (st.1 + 1) = s.mem (st.1 + 1) := hpres.2.2 _ (by omega)
  have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
  have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨hfit.of_le (by omega),
      ⟨hfit.of_le (by rw [hm0, hm1, hsl]; have := hsc.1; omega),
       hfit.of_le (by rw [hm1, hsl]; omega)⟩,
      hfit.of_le (by omega), hfit.of_le (by rw [hm1, hsl]; omega)⟩
  · unfold flattenStep
    dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
    have hpure_st {α : Type} (x : α) (u : Memory.State) :
        (Memory.spec 0).clientState u (pure x) = u := rfl
    have hpure_res {α : Type} (x : α) (u : Memory.State) :
        (Memory.spec 0).clientResult u (pure x) = x := rfl
    rw [hpure_st, hpure_res]
    obtain ⟨hcw_fr, hcw_mem⟩ := copyWords_frame ⟨t.mem st.1, st.2, t.mem (st.1 + 1)⟩ t
    refine ⟨hcw_fr.trans hfr, ?_, by dsimp only; omega, rest, hrem_l, hrest, ?_⟩
    · exact ⟨le_rfl, by rw [hcw_fr]; exact hpres.2.1, fun a ha =>
        (hcw_mem a (lt_of_lt_of_le ha hdst_lo)).trans (hpres.2.2 a ha)⟩
    · dsimp only
      rw [hm1, hsl]
      omega

end Cslib.Algorithms.WordRAM.VariableElimination
