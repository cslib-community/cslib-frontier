/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.VariableElimination.CopyFilter
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
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

/-- `copyWords` as a framed triple, from its older specification. -/
private theorem copyWords_framed {w : ℕ} (args : CopyArgs) {xs : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hxs : Block.HoldsList args.src xs s.mem)
    (hlen : xs.length = args.len) (hsd : args.src + args.len ≤ args.dst)
    (hdst : args.dst + args.len ≤ s.frontier) :
    Memory.FramedTriple w s (copyWords args) (2 * args.len) (Set.Ici args.dst) fun _ t =>
      t.frontier = s.frontier ∧ Block.HoldsList args.dst xs t.mem ∧ Memory.WellFormed w t := by
  obtain ⟨hv, hfr, hpres, hh⟩ := copyWords_spec args hwf hxs hlen hsd le_rfl hdst
  exact framedTriple_iff_realization.mpr ⟨hv, copyWords_cost args s,
    ⟨hfr.ge, fun a _ ha => hpres.2.2 a (by simpa using ha)⟩, hfr, hh,
    wellFormed_clientState hwf hv⟩

/-- Invariant of the loop of `flattenScopes` after `k` descriptors, for the input state `s`: the
scopes of the first `k` factors are concatenated at `s.frontier`. -/
private abbrev FlatInv (w L : ℕ) (bucket : List (FactorTable ℕ ℕ)) (s : Memory.State) (k : ℕ)
    (st : ℕ × ℕ) (t : Memory.State) : Prop :=
  Memory.WellFormed w t ∧ t.frontier = s.frontier + L ∧
    st.2 = s.frontier + ((bucket.take k).flatMap FactorTable.scope).length ∧
    HoldsFactorList st.1 (bucket.drop k) s ∧
    Block.HoldsList s.frontier ((bucket.take k).flatMap FactorTable.scope) t.mem

/-- The scopes of the first `k + 1` factors are those of the first `k` and the scope of factor
`k`, and fit in the concatenation of all scopes. -/
private theorem flatMap_take_succ {bucket : List (FactorTable ℕ ℕ)} {k : ℕ}
    (hk : k < bucket.length) :
    (bucket.take (k + 1)).flatMap FactorTable.scope =
        (bucket.take k).flatMap FactorTable.scope ++ bucket[k].scope ∧
      ((bucket.take k).flatMap FactorTable.scope).length + bucket[k].scope.length ≤
        (bucket.flatMap FactorTable.scope).length := by
  have h : (bucket.take (k + 1)).flatMap FactorTable.scope =
      (bucket.take k).flatMap FactorTable.scope ++ bucket[k].scope := by
    rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.flatMap_append,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hle := ((List.take_sublist (k + 1) bucket).flatMap FactorTable.scope).length_le
  rw [h, List.length_append] at hle
  exact ⟨h, hle⟩

/-- One step of the loop of `flattenScopes` appends the scope of factor `k`. -/
private theorem flattenStep_framed {w L maxScope k : ℕ} {bucket : List (FactorTable ℕ ℕ)}
    {s t : Memory.State} {st : ℕ × ℕ} (hk : k < bucket.length)
    (hflat : (bucket.flatMap FactorTable.scope).length = L)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope) (hpres : PreservesBelow s.frontier s t)
    (hinv : FlatInv w L bucket s k st t) :
    Memory.FramedTriple w t (flattenStep ((), st)) (2 + 2 * maxScope) (Set.Ici s.frontier)
      (FlatInv w L bucket s (k + 1)) := by
  obtain ⟨cur, dst⟩ := st
  obtain ⟨hwf_t, hfr_t, hdst, hrem, hacc⟩ := hinv
  dsimp only at hdst hrem; subst hdst
  rw [List.drop_eq_getElem_cons hk] at hrem
  obtain ⟨⟨hd, hsl, -, hsc, -⟩, hrest⟩ := hrem
  obtain ⟨htk, hfl⟩ := flatMap_take_succ hk
  have hsc1 := hsc.1
  have hm0 := hpres.2.2 cur (by omega)
  have hm1 := (hpres.2.2 (cur + 1) (by omega)).trans hsl
  have hcw := copyWords_framed (w := w) ⟨t.mem cur,
    s.frontier + ((bucket.take k).flatMap FactorTable.scope).length, t.mem (cur + 1)⟩ hwf_t
    (xs := bucket[k].scope) (hm0 ▸ hsc.2.frame fun a _ ha => hpres.2.2 a (by omega)) hm1.symm
    (by dsimp only; omega) (by dsimp only; omega)
  obtain ⟨-, -, hmod', hfr', hh', hwf'⟩ := framedTriple_iff_realization.mp hcw
  have hfm := hmax _ (List.getElem_mem hk)
  dsimp only [flattenStep]
  framed_triple
  · refine ⟨hwf', hfr'.trans hfr_t, by rw [htk, List.length_append, hm1, Nat.add_assoc], hrest,
      htk ▸ Block.holdsList_append_iff.mpr
        ⟨hacc.frame fun a _ ha => hmod'.2 a (by omega) (not_le.mpr ha), hh'⟩⟩

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
  have hft : Memory.FramedTriple w s (flattenScopes args) (1 + args.bucketLen * (2 + 2 * maxScope))
      (Set.Ici s.frontier) fun r t => t.frontier = s.frontier + args.flatLen ∧ r = s.frontier ∧
        HoldsIn r (bucket.flatMap FactorTable.scope) t := by
    obtain ⟨-, hloop⟩ := Memory.FramedTriple.iterate (w := w) (body := flattenStep)
      (safe := fun _ _ _ => True) (d := ()) (n := args.bucketLen) (c := 2 + 2 * maxScope)
      (s := ⟨s.mem, s.frontier + args.flatLen⟩) (a₀ := (args.bucketPtr, s.frontier))
      (S := Set.Ici s.frontier) (FlatInv w args.flatLen bucket s)
      ⟨hwf.step (o := .allocDirty args.flatLen) hfit, rfl, rfl, hb, Block.holdsList_nil _ _⟩
      (fun k hk _ t hinv hmod => ⟨trivial, flattenStep_framed (by omega) hflat hmax
        (preservesBelow_of_modifies hmod ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩) hinv⟩)
      fun _ _ h _ => h
    unfold flattenScopes
    exact Memory.FramedTriple.mono (c := (2 + 2 * maxScope) * args.bucketLen + 0 + 1)
      (Memory.FramedTriple.allocDirty_bind hfit (Memory.FramedTriple.call hloop subset_rfl
        fun _ t ⟨_, hfr, _, _, hh⟩ _ => Memory.FramedTriple.pure ⟨hfr, rfl, by
          rw [← hlen, List.take_length] at hh
          rw [HoldsIn, hfr, hflat]; exact ⟨le_rfl, hh⟩⟩)) (by rw [Nat.mul_comm]; omega)
      fun _ _ => id
  obtain ⟨hv, hc, hm, hfr, hres, hholds⟩ := framedTriple_iff_realization.mp hft
  exact ⟨hv, hfr, preservesBelow_of_modifies hm (.refl le_rfl), hres, hres ▸ hholds,
    hc⟩

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
  have hscK (f) (hf : f ∈ bucket) : f.scope.length ≤ d.flatLen := hflat ▸ by
    rw [List.length_flatMap]; exact List.le_sum_of_mem (List.mem_map_of_mem hf)
  refine (Memory.FramedTriple.iterate (w := w) (s := ⟨s.mem, s.frontier + d.flatLen⟩)
    (c := 2 + 2 * d.flatLen) (S := Set.Ici s.frontier) (Q := fun _ _ => True)
    (FlatInv w d.flatLen bucket s)
    ⟨hmem.step (o := .allocDirty d.flatLen) hfit, rfl, rfl, hb, Block.holdsList_nil _ _⟩
    (fun k hk st t hinv hmod => ?_) fun _ _ _ _ => trivial).1
  have hpres : PreservesBelow s.frontier s t :=
    preservesBelow_of_modifies hmod ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
  refine ⟨?_, flattenStep_framed (by omega) hflat hscK hpres hinv⟩
  obtain ⟨-, hfr, hdst, hrem, -⟩ := hinv
  rw [List.drop_eq_getElem_cons (by omega)] at hrem
  obtain ⟨⟨hd, hsl, -, hsc, -⟩, -⟩ := hrem
  have hfl := (flatMap_take_succ (by omega : k < bucket.length)).2
  have hm0 : t.mem st.1 = s.mem st.1 := hpres.2.2 _ (by omega)
  have hm1 := (hpres.2.2 (st.1 + 1) (by omega)).trans hsl
  have hfit1 : Fits w (st.2 + t.mem (st.1 + 1)) := hm1 ▸ hfit.of_le (by omega)
  dsimp only
  exact ⟨hfit.of_le (by omega),
    ⟨hm0 ▸ hm1 ▸ hfit.of_le (hsc.1.trans (Nat.le_add_right _ _)), hfit1⟩,
    hfit.of_le (by omega), hfit1⟩

end Cslib.Algorithms.WordRAM.VariableElimination
