/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CSP.VariableElimination
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.ListArray
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Foundations.Data.List.FoldMax
import CslibFrontier.Tactic.Realize
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring

/-!
# Bucket (variable) elimination on the Word-RAM

This module implements bucket (variable) elimination (`Cslib.Algorithms.Lean.CSP.eliminateOrder`)
over materialized radix-indexed factor tables (`FactorTable ℕ ℕ`) on the exact-basis Word-RAM
(`Cslib.WordRAM.Basis.exact`). `Basis.exact` supplies unit-cost multiplication, division, and
remainder for mixed-radix indexing and exact `ℕ` weight products while certifying non-underflowing
subtraction and non-zero divisors in the machine semantics.

Every operation of the algorithm is genuinely executed and charged on word-addressed memory:
- parsing serialized factor records into 4-word descriptors (`initFactors`),
- scanning and filtering active variable lists (`memScan`, `filterNe`),
- partitioning live factors into the active variable's bucket and unaffected factors
  (`partitionLive`),
- flattening, deduplicating, and filtering bucket scopes to form `bucketOutScope`
  (`buildOutScope`),
- decoding output table indices, looking up variable assignments across factor scopes, computing
  radix offsets, multiplying bucket factor entries, summing over all `d` domain values, and
  materializing the new `d ^ |outScope|` factor table (`evalScopeIdx`, `evalBucketProd`,
  `sumDomainValues`, `buildOutEntries`), and
- multiplying the final scalar accumulator across remaining zero-arity factor tables
  (`finalResultProd`).

Using the amortized bucket-count invariant `Cslib.Algorithms.Lean.CSP.sum_bucketFactors_le`, the
total Word-RAM instruction count along an arbitrary elimination order `order` is bounded
exponentially only in the actual intermediate joint bucket width
`W = maxJointScopeLen domain order initState`, with at most `|factors| + |order|` total factor
evaluations across the entire run.

## Main definitions

* `Cslib.Algorithms.WordRAM.VariableElimination.encodeFactor`: word-list serialization of a
  `FactorTable ℕ ℕ`.
* `Cslib.Algorithms.WordRAM.VariableElimination.ElimInstance`: input bundle (`domain`, `declared`,
  `order`, `factors`) with `ElimInstance.encode`, `ElimInstance.wordBound`,
  `ElimInstance.stepBound`, `ElimInstance.result`, and `ElimInstance.ofCSP`.

## Main results

* `Cslib.Algorithms.WordRAM.VariableElimination.exists_program_variableElimination`: one fixed
  exact-basis Word-RAM program computes `ElimInstance.result` in `O(stepBound + 1)` instructions
  for every word size `w` satisfying `Fits w inst.wordBound` and `InputFits w inst.encode`.
* `Cslib.Algorithms.WordRAM.VariableElimination.uniformComputableInTime_variableElimination`:
  `UniformComputableInTime .exact` certificate for `ElimInstance.result`.
* `Cslib.Algorithms.WordRAM.VariableElimination.exists_program_csp_partitionFunctionOn`: Word-RAM
  computation of `CSP.partitionFunctionOn` via `FactorTable.ofCSP`.
-/

public section

namespace Cslib.Algorithms.WordRAM.VariableElimination

open Cslib.Logic.PL Cslib.Logic.PL.CSP
open Cslib.Algorithms.Lean.CSP
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Monotone append-only memory preservation and descriptors -/

private def PreservesBelow (F : ℕ) (s₀ s₁ : Memory.State) : Prop :=
  F ≤ s₀.frontier ∧ s₀.frontier ≤ s₁.frontier ∧ ∀ a < F, s₁.mem a = s₀.mem a

private theorem PreservesBelow.refl {F : ℕ} {s : Memory.State} (hF : F ≤ s.frontier) :
    PreservesBelow F s s :=
  ⟨hF, le_rfl, fun _ _ => rfl⟩

private theorem PreservesBelow.mono_bound {F₁ F₂ : ℕ} {s₀ s₁ : Memory.State}
    (h : PreservesBelow F₂ s₀ s₁) (hle : F₁ ≤ F₂) : PreservesBelow F₁ s₀ s₁ :=
  ⟨hle.trans h.1, h.2.1, fun a ha => h.2.2 a (lt_of_lt_of_le ha hle)⟩

private theorem PreservesBelow.trans {F : ℕ} {s₀ s₁ s₂ : Memory.State}
    (h₁ : PreservesBelow F s₀ s₁) (h₂ : PreservesBelow F s₁ s₂) :
    PreservesBelow F s₀ s₂ :=
  ⟨h₁.1, h₁.2.1.trans h₂.2.1, fun a ha => (h₂.2.2 a ha).trans (h₁.2.2 a ha)⟩

private def HoldsIn (base : ℕ) (xs : List ℕ) (s : Memory.State) : Prop :=
  base + xs.length ≤ s.frontier ∧ Block.HoldsList base xs s.mem

private theorem HoldsIn.mono {base : ℕ} {xs : List ℕ} {F : ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀) (hF : base + xs.length ≤ F) (hp : PreservesBelow F s₀ s₁) :
    HoldsIn base xs s₁ :=
  ⟨h.1.trans hp.2.1, h.2.frame fun a _ hhi => hp.2.2 a (lt_of_lt_of_le hhi hF)⟩

private theorem HoldsIn.mono_frontier {base : ℕ} {xs : List ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀) (hp : PreservesBelow s₀.frontier s₀ s₁) :
    HoldsIn base xs s₁ :=
  h.mono h.1 hp

private def HoldsFactor (descAddr : ℕ) (f : FactorTable ℕ ℕ) (s : Memory.State) : Prop :=
  descAddr + 4 ≤ s.frontier ∧
  s.mem (descAddr + 1) = f.scope.length ∧
  s.mem (descAddr + 3) = f.entries.size ∧
  HoldsIn (s.mem descAddr) f.scope s ∧
  HoldsIn (s.mem (descAddr + 2)) f.entries.toList s

private theorem HoldsFactor.mono {descAddr : ℕ} {f : FactorTable ℕ ℕ} {F : ℕ}
    {s₀ s₁ : Memory.State} (h : HoldsFactor descAddr f s₀)
    (hF : descAddr + 4 ≤ F)
    (hsF : s₀.mem descAddr + f.scope.length ≤ F)
    (heF : s₀.mem (descAddr + 2) + f.entries.size ≤ F)
    (hp : PreservesBelow F s₀ s₁) : HoldsFactor descAddr f s₁ := by
  obtain ⟨hd, hsl, hel, hsc, hent⟩ := h
  unfold HoldsFactor
  rw [hp.2.2 descAddr (by omega), hp.2.2 (descAddr + 1) (by omega),
    hp.2.2 (descAddr + 2) (by omega), hp.2.2 (descAddr + 3) (by omega)]
  exact ⟨hd.trans hp.2.1, hsl, hel, hsc.mono hsF hp,
    hent.mono (by simpa [Array.length_toList] using heF) hp⟩

private theorem HoldsFactor.mono_frontier {descAddr : ℕ} {f : FactorTable ℕ ℕ}
    {s₀ s₁ : Memory.State} (h : HoldsFactor descAddr f s₀)
    (hp : PreservesBelow s₀.frontier s₀ s₁) : HoldsFactor descAddr f s₁ :=
  h.mono h.1 h.2.2.2.1.1 (by simpa [Array.length_toList] using h.2.2.2.2.1) hp

private def HoldsFactorList : ℕ → List (FactorTable ℕ ℕ) → Memory.State → Prop
  | base, [], s => base ≤ s.frontier
  | base, f :: fs, s => HoldsFactor base f s ∧ HoldsFactorList (base + 4) fs s

private theorem HoldsFactorList.bound {base : ℕ} {fs : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (h : HoldsFactorList base fs s) : base + 4 * fs.length ≤ s.frontier := by
  induction fs generalizing base with
  | nil => simpa [HoldsFactorList] using h
  | cons f rest ih =>
    have hb := ih h.2
    simp only [List.length_cons]
    omega

private theorem HoldsFactorList.mono_frontier {base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s₀ s₁ : Memory.State} (h : HoldsFactorList base fs s₀)
    (hp : PreservesBelow s₀.frontier s₀ s₁) : HoldsFactorList base fs s₁ := by
  induction fs generalizing base with
  | nil => exact h.trans hp.2.1
  | cons f rest ih => exact ⟨h.1.mono_frontier hp, ih h.2⟩

/-! ### Primitive 1: Linear membership scan (`memScan`) -/

private structure ScanState where
  cur : ℕ
  found : ℕ

private def ScanState.equiv : ScanState ≃ ℕ × ℕ where
  toFun s := (s.cur, s.found)
  invFun := fun (cur, found) => ⟨cur, found⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ScanState := .ofEquiv ScanState.equiv

private structure MemScanArgs where
  target : ℕ
  base : ℕ
  len : ℕ

private def MemScanArgs.equiv : MemScanArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.target, a.base), a.len)
  invFun := fun ((target, base), len) => ⟨target, base, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding MemScanArgs := .ofEquiv MemScanArgs.equiv

private def memScanStep (env : ℕ × ScanState) : Memory.Prog ScanState := do
  let v ← Memory.read env.2.cur
  pure ⟨env.2.cur + 1, if v = env.1 then 1 else env.2.found⟩

private def memScan (args : MemScanArgs) : Memory.Prog ℕ := do
  let res ← iterate memScanStep args.target args.len ⟨args.base, 0⟩
  pure res.found

private theorem memScan_state (args : MemScanArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (memScan args) = s := by
  unfold memScan
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of memScanStep args.target (fun _ _ => rfl) args.len ⟨args.base, 0⟩ s

private theorem memScan_cost (args : MemScanArgs) (s : Memory.State) :
    memoryCost (memScan args) s ≤ args.len := by
  unfold memScan
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  simpa using memoryCost_iterate_le_of memScanStep 1 args.target (fun _ _ => le_rfl)
    args.len ⟨args.base, 0⟩ s

private theorem memScan_valid {w : ℕ} (args : MemScanArgs) {s : Memory.State}
    (hb : args.base + args.len ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (memScan args)) := by
  unfold memScan
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  suffices ∀ len cur, cur + len ≤ s.frontier → ∀ found,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate memScanStep args.target len ⟨cur, found⟩)) from
    this args.len args.base hb 0
  intro len
  induction len with
  | zero => intro _ _ _; exact validHistory_pure w s _
  | succ len ih =>
    intro cur hcur found
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (memScanStep (args.target, ⟨cur, found⟩) >>= iterate memScanStep args.target len))
    have hlt : cur < s.frontier := by omega
    refine validHistory_bind_step (validHistory_read_bind hlt (validHistory_pure w s _)) ?_
    exact ih (cur + 1) (by omega) _

private theorem memScan_result {args : MemScanArgs} {xs : List ℕ} {s : Memory.State}
    (hxs : Block.HoldsList args.base xs s.mem) (hlen : xs.length = args.len) :
    (Memory.spec 0).clientResult s (memScan args) = if args.target ∈ xs then 1 else 0 := by
  unfold memScan
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ (ys : List ℕ) (cur found : ℕ), Block.HoldsList cur ys s.mem →
      ((Memory.spec 0).clientResult s
        (iterate memScanStep args.target ys.length ⟨cur, found⟩)).found =
      if args.target ∈ ys then 1 else found by
    rw [← hlen]
    exact this xs args.base 0 hxs
  intro ys
  induction ys with
  | nil => intro cur found _; rfl
  | cons u rest ih =>
    intro cur found hcur
    obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hcur
    change ((Memory.spec 0).clientResult s
      (memScanStep (args.target, ⟨cur, found⟩) >>=
        iterate memScanStep args.target rest.length)).found = _
    rw [StateTransitionSpec.clientResult_bind]
    have hstep_st : (Memory.spec 0).clientState s (memScanStep (args.target, ⟨cur, found⟩)) = s :=
      rfl
    have hstep_res : (Memory.spec 0).clientResult s (memScanStep (args.target, ⟨cur, found⟩)) =
        ⟨cur + 1, if u = args.target then 1 else found⟩ := by
      rw [← hhead]; rfl
    rw [hstep_st, hstep_res, ih (cur + 1) _ htail]
    by_cases hmem : args.target ∈ rest <;> by_cases heq : args.target = u
    · simp [List.mem_cons, heq]
    · simp [List.mem_cons, hmem]
    · subst heq; simp [List.mem_cons]
    · have hne : u ≠ args.target := Ne.symm heq
      simp [List.mem_cons, hmem, heq, hne]

private theorem memScan_realizes :
    Realizes .exact memScan WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w (args.base + args.len)) (fun _ _ => 0) := by
  unfold memScan
  realize
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st _ => st.cur + j = d.base + d.len) (fun j st t hinv => ?_)
    (show (⟨d.base, 0⟩ : ScanState).cur + d.len = d.base + d.len from rfl)
  dsimp only
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact ⟨h.2.of_le (by omega), h.1⟩
    · exact h.2.of_le (by omega)
  · change (st.cur + 1) + j = d.base + d.len
    omega

/-! ### Primitive 2: Block copy (`copyWords`) and inequality filter (`filterNe`) -/

private structure CopyArgs where
  src : ℕ
  dst : ℕ
  len : ℕ

private def CopyArgs.equiv : CopyArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.src, a.dst), a.len)
  invFun := fun ((src, dst), len) => ⟨src, dst, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding CopyArgs := .ofEquiv CopyArgs.equiv

private structure CopyState where
  src : ℕ
  dst : ℕ

private def CopyState.equiv : CopyState ≃ ℕ × ℕ where
  toFun s := (s.src, s.dst)
  invFun := fun (src, dst) => ⟨src, dst⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding CopyState := .ofEquiv CopyState.equiv

private def copyWordsStep (env : Unit × CopyState) : Memory.Prog CopyState := do
  let v ← Memory.read env.2.src
  Memory.write env.2.dst v
  pure ⟨env.2.src + 1, env.2.dst + 1⟩

private def copyWords (args : CopyArgs) : Memory.Prog Unit := do
  let _ ← iterate copyWordsStep () args.len ⟨args.src, args.dst⟩
  pure ()

private theorem copyWords_cost (args : CopyArgs) (s : Memory.State) :
    memoryCost (copyWords args) s ≤ 2 * args.len := by
  unfold copyWords
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  exact memoryCost_iterate_le_of copyWordsStep 2 () (fun _ _ => le_rfl) args.len
    ⟨args.src, args.dst⟩ s

private theorem copyWords_spec {w : ℕ} (args : CopyArgs) {xs : List ℕ} {F : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hxs : Block.HoldsList args.src xs s.mem) (hlen : xs.length = args.len)
    (hsrcF : args.src + args.len ≤ F) (hFdst : F ≤ args.dst)
    (hdst : args.dst + args.len ≤ s.frontier) :
    let s' := (Memory.spec 0).clientState s (copyWords args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (copyWords args)) ∧
      s'.frontier = s.frontier ∧
      PreservesBelow F s s' ∧
      Block.HoldsList args.dst xs s'.mem := by
  dsimp only
  unfold copyWords
  rw [StateTransitionSpec.clientState_bind]
  have haux : ∀ (ys : List ℕ) (src dst G : ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      Block.HoldsList src ys t.mem →
      src + ys.length ≤ G → G ≤ dst → dst + ys.length ≤ t.frontier →
      let t' := (Memory.spec 0).clientState t (iterate copyWordsStep () ys.length ⟨src, dst⟩)
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (iterate copyWordsStep () ys.length ⟨src, dst⟩)) ∧
      t'.frontier = t.frontier ∧
      PreservesBelow G t t' ∧
      Block.HoldsList dst ys t'.mem := by
    intro ys
    induction ys with
    | nil =>
      intro src dst G t _ _ _ hGdst hdstF
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega),
        Block.holdsList_nil dst t.mem⟩
    | cons v rest ih =>
      intro src dst G t hwf_t hys hsrcG hGdst hdstF
      simp only [List.length_cons] at hsrcG hdstF
      obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hys
      have hsrc_lt : src < t.frontier := by omega
      have hdst_lt : dst < t.frontier := by omega
      have hv_fit : Fits w v := hhead ▸ hwf_t.mem_fits src
      let t₁ : Memory.State := ⟨Function.update t.mem dst v, t.frontier⟩
      have hwf₁ : Memory.WellFormed w t₁ := hwf_t.step (o := .write dst v) ⟨hdst_lt, hv_fit⟩
      have htail₁ : Block.HoldsList (src + 1) rest t₁.mem :=
        htail.frame fun a _ hhi => Function.update_of_ne (by omega) v t.mem
      obtain ⟨hval_rest, hfr_rest, hpres_rest, hholds_rest⟩ :=
        ih (src + 1) (dst + 1) (dst + 1) t₁ hwf₁ htail₁ (by omega) le_rfl
          (by dsimp only [t₁]; omega)
      have hiter_eq : iterate copyWordsStep () (v :: rest).length ⟨src, dst⟩ =
          (copyWordsStep ((), ⟨src, dst⟩) >>= iterate copyWordsStep () rest.length) := rfl
      dsimp only
      rw [hiter_eq, StateTransitionSpec.clientState_bind]
      have hstep_st : (Memory.spec 0).clientState t (copyWordsStep ((), ⟨src, dst⟩)) = t₁ := by
        change (⟨Function.update t.mem dst (t.mem src), t.frontier⟩ : Memory.State) = t₁
        rw [hhead]
      have hstep_res : (Memory.spec 0).clientResult t (copyWordsStep ((), ⟨src, dst⟩)) =
          ⟨src + 1, dst + 1⟩ := rfl
      have hstep_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (copyWordsStep ((), ⟨src, dst⟩))) :=
        validHistory_read_bind hsrc_lt
          (validHistory_write_bind hdst_lt (hwf_t.mem_fits src) (validHistory_pure w _ _))
      rw [hstep_st, hstep_res]
      refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hval_rest),
        hfr_rest, ?_, ?_⟩
      · refine ⟨by omega, le_of_eq hfr_rest.symm, fun a ha => ?_⟩
        have ha_lt : a < dst + 1 := by omega
        have hne : a ≠ dst := by omega
        rw [hpres_rest.2.2 a ha_lt]
        exact Function.update_of_ne hne v t.mem
      · refine Block.holdsList_cons_iff.mpr ⟨?_, hholds_rest⟩
        have hdst_lt1 : dst < dst + 1 := by omega
        rw [hpres_rest.2.2 dst hdst_lt1]
        exact Function.update_self dst v t.mem
  rw [← hlen] at hsrcF hdst ⊢
  obtain ⟨hv, hfr, hpres, hholds⟩ := haux xs args.src args.dst F s hwf hxs hsrcF hFdst hdst
  exact ⟨validHistory_bind_step hv (validHistory_pure w _ _), hfr, hpres, hholds⟩

private theorem copyWords_realizes :
    Realizes .exact copyWords WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w (args.src + args.len) ∧ Fits w (args.dst + args.len))
      (fun _ _ => 0) := by
  unfold copyWords
  realize
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st _ => st.src + j = d.src + d.len ∧ st.dst + j = d.dst + d.len)
    (fun j st t hinv => ?_) ⟨rfl, rfl⟩
  dsimp only
  refine ⟨⟨h.1.of_le (by omega), h.2.of_le (by omega)⟩, ?_⟩
  change (st.src + 1) + j = d.src + d.len ∧ (st.dst + 1) + j = d.dst + d.len
  omega

private structure FilterState where
  src : ℕ
  dst : ℕ
  count : ℕ

private def FilterState.equiv : FilterState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.src, s.dst), s.count)
  invFun := fun ((src, dst), count) => ⟨src, dst, count⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding FilterState := .ofEquiv FilterState.equiv

private def filterNeStep (env : ℕ × FilterState) : Memory.Prog FilterState := do
  let v ← Memory.read env.2.src
  if v = env.1 then
    pure ⟨env.2.src + 1, env.2.dst, env.2.count⟩
  else
    Memory.write env.2.dst v >>= fun _ =>
      pure ⟨env.2.src + 1, env.2.dst + 1, env.2.count + 1⟩

private def filterNe (args : MemScanArgs) : Memory.Prog (ℕ × ℕ) := do
  let dst ← Memory.allocDirty args.len
  let res ← iterate filterNeStep args.target args.len ⟨args.base, dst, 0⟩
  pure (dst, res.count)

private theorem filterNe_cost (args : MemScanArgs) (s : Memory.State) :
    memoryCost (filterNe args) s ≤ 1 + 2 * args.len := by
  unfold filterNe
  rw [memoryCost_bind', memoryCost_allocDirty, memoryCost_bind', memoryCost_pure, Nat.add_zero]
  have hstep : ∀ a t, memoryCost (filterNeStep (args.target, a)) t ≤ 2 := by
    intro a t
    unfold filterNeStep
    rw [memoryCost_bind', memoryCost_read]
    dsimp only
    rw [memoryCost_ite]
    split_ifs
    · simp
    · rw [memoryCost_bind', memoryCost_write, memoryCost_pure]
  have hiter := memoryCost_iterate_le_of filterNeStep 2 args.target hstep args.len
    ⟨args.base, s.frontier, 0⟩ ⟨s.mem, s.frontier + args.len⟩
  exact Nat.add_le_add_left hiter 1

private theorem filterNe_spec {w : ℕ} (args : MemScanArgs) {xs : List ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len)
    (hfit : Fits w (s.frontier + args.len)) :
    let res := (Memory.spec 0).clientResult s (filterNe args)
    let s' := (Memory.spec 0).clientState s (filterNe args)
    let out := xs.filter fun v => decide (v ≠ args.target)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (filterNe args)) ∧
      s'.frontier = s.frontier + args.len ∧
      PreservesBelow s.frontier s s' ∧
      res.1 = s.frontier ∧
      res.2 = out.length ∧
      HoldsIn res.1 out s' := by
  dsimp only
  unfold filterNe
  have halloc_val : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty args.len)) :=
    validHistory_allocDirty hfit
  let s₀ : Memory.State := ⟨s.mem, s.frontier + args.len⟩
  have hwf₀ : Memory.WellFormed w s₀ := hwf.step (o := .allocDirty args.len) hfit
  have haux : ∀ (ys : List ℕ) (src dst cnt G : ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      Block.HoldsList src ys t.mem →
      src + ys.length ≤ G → G ≤ dst → dst + ys.length ≤ t.frontier →
      let p := iterate filterNeStep args.target ys.length ⟨src, dst, cnt⟩
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let out := ys.filter fun v => decide (v ≠ args.target)
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
      t'.frontier = t.frontier ∧
      PreservesBelow G t t' ∧
      r.count = cnt + out.length ∧
      Block.HoldsList dst out t'.mem := by
    intro ys
    induction ys with
    | nil =>
      intro src dst cnt G t _ _ _ hGdst hdstF
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega), rfl,
        Block.holdsList_nil dst t.mem⟩
    | cons v rest ih =>
      intro src dst cnt G t hwf_t hys hsrcG hGdst hdstF
      simp only [List.length_cons] at hsrcG hdstF
      obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hys
      have hsrc_lt : src < t.frontier := by omega
      have hiter_eq : iterate filterNeStep args.target (v :: rest).length ⟨src, dst, cnt⟩ =
          (filterNeStep (args.target, ⟨src, dst, cnt⟩) >>=
            iterate filterNeStep args.target rest.length) := rfl
      dsimp only
      rw [hiter_eq, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
      by_cases hvx : v = args.target
      · have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (filterNeStep (args.target, ⟨src, dst, cnt⟩))) := by
          refine validHistory_read_bind hsrc_lt ?_
          rw [hhead, ite_eq_left hvx]
          exact validHistory_pure w t _
        have hstep_st : (Memory.spec 0).clientState t
            (filterNeStep (args.target, ⟨src, dst, cnt⟩)) = t := by
          unfold filterNeStep
          change (Memory.spec 0).clientState t (if t.mem src = args.target then _ else _) = t
          rw [hhead, ite_eq_left hvx]; rfl
        have hstep_res : (Memory.spec 0).clientResult t
            (filterNeStep (args.target, ⟨src, dst, cnt⟩)) = ⟨src + 1, dst, cnt⟩ := by
          unfold filterNeStep
          change (Memory.spec 0).clientResult t (if t.mem src = args.target then _ else _) = _
          rw [hhead, ite_eq_left hvx]; rfl
        rw [hstep_st, hstep_res]
        obtain ⟨hval_r, hfr_r, hpres_r, hcnt_r, hholds_r⟩ :=
          ih (src + 1) dst cnt G t hwf_t htail (by omega) hGdst (by omega)
        simp only [List.filter_cons, hvx, ne_eq, not_true_eq_false, decide_false,
          Bool.false_eq_true, ↓reduceIte]
        exact ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hval_r),
          hfr_r, hpres_r, hcnt_r, hholds_r⟩
      · have hdst_lt : dst < t.frontier := by omega
        let t₁ : Memory.State := ⟨Function.update t.mem dst v, t.frontier⟩
        have hv_fit : Fits w v := hhead ▸ hwf_t.mem_fits src
        have hwf₁ : Memory.WellFormed w t₁ := hwf_t.step (o := .write dst v) ⟨hdst_lt, hv_fit⟩
        have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (filterNeStep (args.target, ⟨src, dst, cnt⟩))) := by
          refine validHistory_read_bind hsrc_lt ?_
          rw [hhead, ite_eq_right hvx]
          exact validHistory_write_bind hdst_lt hv_fit (validHistory_pure w _ _)
        have hstep_st : (Memory.spec 0).clientState t
            (filterNeStep (args.target, ⟨src, dst, cnt⟩)) = t₁ := by
          unfold filterNeStep
          change (Memory.spec 0).clientState t (if t.mem src = args.target then _ else _) = t₁
          rw [hhead, ite_eq_right hvx]; rfl
        have hstep_res : (Memory.spec 0).clientResult t
            (filterNeStep (args.target, ⟨src, dst, cnt⟩)) = ⟨src + 1, dst + 1, cnt + 1⟩ := by
          unfold filterNeStep
          change (Memory.spec 0).clientResult t (if t.mem src = args.target then _ else _) = _
          rw [hhead, ite_eq_right hvx]; rfl
        have htail₁ : Block.HoldsList (src + 1) rest t₁.mem :=
          htail.frame fun a _ hhi => Function.update_of_ne (by omega) v t.mem
        rw [hstep_st, hstep_res]
        have ht₁_fr : t₁.frontier = t.frontier := rfl
        obtain ⟨hval_r, hfr_r, hpres_r, hcnt_r, hholds_r⟩ :=
          ih (src + 1) (dst + 1) (cnt + 1) (dst + 1) t₁ hwf₁ htail₁
            (by omega) le_rfl (by omega)
        simp only [List.filter_cons, decide_eq_true hvx, ↓reduceIte, List.length_cons]
        refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hval_r),
          hfr_r, ?_, by omega, ?_⟩
        · refine ⟨by omega, le_of_eq hfr_r.symm, fun a ha => ?_⟩
          have ha_lt : a < dst + 1 := by omega
          have hne : a ≠ dst := by omega
          rw [hpres_r.2.2 a ha_lt]
          exact Function.update_of_ne hne v t.mem
        · refine Block.holdsList_cons_iff.mpr ⟨?_, hholds_r⟩
          have hdst_lt1 : dst < dst + 1 := by omega
          rw [hpres_r.2.2 dst hdst_lt1]
          exact Function.update_self dst v t.mem
  have hbase_le : args.base + xs.length ≤ s.frontier := hxs.1
  have halloc_val' : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty xs.length)) := by
    rw [hlen]; exact halloc_val
  have hwf₀' : Memory.WellFormed w ⟨s.mem, s.frontier + xs.length⟩ := by
    rw [hlen]; exact hwf₀
  obtain ⟨hv, hfr, hpres, hcnt, hholds⟩ :=
    haux xs args.base s.frontier 0 s.frontier ⟨s.mem, s.frontier + xs.length⟩ hwf₀' hxs.2 hbase_le
      le_rfl (by simp)
  rw [← hlen]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
  have ha_res : (Memory.spec 0).clientResult s (Memory.allocDirty xs.length) = s.frontier := rfl
  have ha_st : (Memory.spec 0).clientState s (Memory.allocDirty xs.length) =
      ⟨s.mem, s.frontier + xs.length⟩ := rfl
  rw [ha_res, ha_st]
  have hpure_st {α : Type} (x : α) (t : Memory.State) :
      (Memory.spec 0).clientState t (pure x) = t := rfl
  have hpure_res {α : Type} (x : α) (t : Memory.State) :
      (Memory.spec 0).clientResult t (pure x) = x := rfl
  rw [hpure_st, hpure_res]
  have hout_le : (xs.filter fun v => decide (v ≠ args.target)).length ≤ xs.length :=
    List.length_filter_le _ _
  refine ⟨validHistory_bind_step halloc_val'
    (validHistory_bind_step hv (validHistory_pure w _ _)), hfr, ?_, rfl, by omega, ?_⟩
  · exact ⟨le_rfl, (Nat.le_add_right _ _).trans (le_of_eq hfr.symm), hpres.2.2⟩
  · refine ⟨?_, hholds⟩
    rw [hfr]
    dsimp only
    omega

private theorem filterNeStep_result (target : ℕ) (st : FilterState) (t : Memory.State) :
    (Memory.spec 0).clientResult t (filterNeStep (target, st)) =
      if t.mem st.src = target then ⟨st.src + 1, st.dst, st.count⟩
      else ⟨st.src + 1, st.dst + 1, st.count + 1⟩ := by
  unfold filterNeStep
  change (Memory.spec 0).clientResult t
    (if t.mem st.src = target then
      (pure ⟨st.src + 1, st.dst, st.count⟩ : Memory.Prog FilterState)
     else
      Memory.write st.dst (t.mem st.src) >>= fun _ =>
        pure ⟨st.src + 1, st.dst + 1, st.count + 1⟩) = _
  split_ifs <;> rfl

private theorem filterNe_realizes :
    Realizes .exact filterNe WordEncoding.encode WordEncoding.encode
      (fun w args s => Fits w (args.base + args.len) ∧ Fits w (s.frontier + args.len))
      (fun _ _ => 0) := by
  unfold filterNe
  realize
  refine iterationSafe_of_stepInv _ _ w _
    (fun j st _ => st.src + j = d.base + d.len ∧ st.dst + j ≤ s.frontier + d.len ∧
      st.count + j ≤ d.len)
    (fun j st t ⟨hsrc, hdst, hcnt⟩ => ?_)
    ⟨rfl, le_rfl, by simp⟩
  dsimp only
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact h.1.of_le (by omega)
    · exact ⟨h.1.of_le (by omega), h.2.of_le (by omega), h.1.of_le (by omega)⟩
  · rw [filterNeStep_result]
    split_ifs <;> (dsimp only; omega)

/-! ### Primitive 3: Power `d ^ n`, radix assignment lookup, and scope evaluation -/

private structure PowArgs where
  base : ℕ
  exp : ℕ

private def PowArgs.equiv : PowArgs ≃ ℕ × ℕ where
  toFun a := (a.base, a.exp)
  invFun := fun (base, exp) => ⟨base, exp⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding PowArgs := .ofEquiv PowArgs.equiv

private def powStep (env : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  pure (env.2 * env.1)

private def powProg (args : PowArgs) : Memory.Prog ℕ :=
  iterate powStep args.base args.exp 1

private theorem powProg_state (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (powProg args) = s :=
  clientState_iterate_eq_of powStep args.base (fun _ _ => rfl) args.exp 1 s

private theorem powProg_cost (args : PowArgs) (s : Memory.State) :
    memoryCost (powProg args) s ≤ args.exp := by
  unfold powProg
  simpa using memoryCost_iterate_le_of powStep 1 args.base (fun _ _ => le_rfl) args.exp 1 s

private theorem powProg_valid {w : ℕ} (args : PowArgs) {s : Memory.State} (hs : 0 < s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (powProg args)) :=
  validHistory_iterate_inv (fun t => 0 < t.frontier) powStep args.base
    (fun _ t ht => validHistory_read_bind ht (validHistory_pure w t _)) args.exp 1 hs

private theorem powProg_result (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientResult s (powProg args) = args.base ^ args.exp := by
  unfold powProg
  suffices ∀ n acc, (Memory.spec 0).clientResult s (iterate powStep args.base n acc) =
      acc * args.base ^ n by
    simpa using this args.exp 1
  intro n
  induction n with
  | zero =>
    intro acc
    change acc = acc * args.base ^ 0
    simp
  | succ n ih =>
    intro acc
    change (Memory.spec 0).clientResult s
      (powStep (args.base, acc) >>= iterate powStep args.base n) = _
    rw [StateTransitionSpec.clientResult_bind]
    have hst : (Memory.spec 0).clientState s (powStep (args.base, acc)) = s := rfl
    have hres : (Memory.spec 0).clientResult s (powStep (args.base, acc)) = acc * args.base := rfl
    rw [hst, hres, ih (acc * args.base), pow_succ', Nat.mul_assoc]

private theorem powProg_realizes :
    Realizes .exact powProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w ((max 1 args.base) ^ args.exp)) (fun _ _ => 0) := by
  unfold powProg
  realize
  · exact h.1
  · refine iterationSafe_of_stepInv _ _ w d
      (fun j acc _ => acc * (max 1 d.base) ^ j ≤ (max 1 d.base) ^ d.exp)
      (fun j acc t hinv => ?_) (Nat.one_mul _).le
    have hm : acc * d.base ≤ acc * max 1 d.base := Nat.mul_le_mul_left acc (le_max_right 1 d.base)
    have h1 : 1 ≤ (max 1 d.base) ^ j := Nat.one_le_pow j _ (le_max_left 1 d.base)
    have hle : acc * d.base ≤ (max 1 d.base) ^ d.exp := by
      calc acc * d.base ≤ acc * max 1 d.base := hm
        _ ≤ (acc * max 1 d.base) * (max 1 d.base) ^ j := Nat.le_mul_of_pos_right _ h1
        _ = acc * (max 1 d.base) ^ (j + 1) := by rw [pow_succ', Nat.mul_assoc]
        _ ≤ (max 1 d.base) ^ d.exp := hinv
    refine ⟨h.2.of_le hle, ?_⟩
    change (acc * d.base) * (max 1 d.base) ^ j ≤ (max 1 d.base) ^ d.exp
    calc (acc * d.base) * (max 1 d.base) ^ j
        ≤ (acc * max 1 d.base) * (max 1 d.base) ^ j := Nat.mul_le_mul_right _ hm
      _ = acc * (max 1 d.base) ^ (j + 1) := by rw [pow_succ', Nat.mul_assoc]
      _ ≤ (max 1 d.base) ^ d.exp := hinv

private structure LookupArgs where
  dom : ℕ
  target : ℕ
  outPtr : ℕ
  outLen : ℕ
  idx : ℕ

private def LookupArgs.equiv : LookupArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun a := ((((a.dom, a.target), a.outPtr), a.outLen), a.idx)
  invFun := fun ((((dom, target), outPtr), outLen), idx) => ⟨dom, target, outPtr, outLen, idx⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupArgs := .ofEquiv LookupArgs.equiv

private structure LookupEnv where
  dom : ℕ
  target : ℕ

private def LookupEnv.equiv : LookupEnv ≃ ℕ × ℕ where
  toFun e := (e.dom, e.target)
  invFun := fun (dom, target) => ⟨dom, target⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupEnv := .ofEquiv LookupEnv.equiv

private structure LookupState where
  cur : ℕ
  remIdx : ℕ
  found : ℕ
  ans : ℕ

private def LookupState.equiv : LookupState ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.cur, s.remIdx), s.found), s.ans)
  invFun := fun (((cur, remIdx), found), ans) => ⟨cur, remIdx, found, ans⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding LookupState := .ofEquiv LookupState.equiv

private def lookupStep (p : LookupEnv × LookupState) : Memory.Prog LookupState := do
  let u ← Memory.read p.2.cur
  let dig := p.2.remIdx % p.1.dom
  let nextIdx := p.2.remIdx / p.1.dom
  if p.2.found = 0 ∧ u = p.1.target then
    pure ⟨p.2.cur + 1, nextIdx, 1, dig⟩
  else
    pure ⟨p.2.cur + 1, nextIdx, p.2.found, p.2.ans⟩

private def lookupAssign (args : LookupArgs) : Memory.Prog ℕ := do
  let res ← iterate lookupStep ⟨args.dom, args.target⟩ args.outLen ⟨args.outPtr, args.idx, 0, 0⟩
  pure res.ans

private theorem lookupAssign_state (args : LookupArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (lookupAssign args) = s := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of lookupStep ⟨args.dom, args.target⟩
    (fun a t => by
      unfold lookupStep
      change (Memory.spec 0).clientState t
        (if a.found = 0 ∧ t.mem a.cur = args.target then _ else _) = t
      split_ifs <;> rfl)
    args.outLen ⟨args.outPtr, args.idx, 0, 0⟩ s

private theorem lookupAssign_cost (args : LookupArgs) (s : Memory.State) :
    memoryCost (lookupAssign args) s ≤ args.outLen := by
  unfold lookupAssign
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  simpa using memoryCost_iterate_le_of lookupStep 1 ⟨args.dom, args.target⟩
    (fun a t => by
      unfold lookupStep
      rw [memoryCost_bind', memoryCost_read]
      dsimp only
      rw [memoryCost_ite]
      split_ifs <;> simp)
    args.outLen ⟨args.outPtr, args.idx, 0, 0⟩ s

private theorem lookupAssign_valid {w : ℕ} (args : LookupArgs) {s : Memory.State}
    (hb : args.outPtr + args.outLen ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (lookupAssign args)) := by
  unfold lookupAssign
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  suffices ∀ len cur, cur + len ≤ s.frontier → ∀ remIdx found ans,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate lookupStep ⟨args.dom, args.target⟩ len ⟨cur, remIdx, found, ans⟩)) from
    this args.outLen args.outPtr hb args.idx 0 0
  intro len
  induction len with
  | zero => intro _ _ _ _ _; exact validHistory_pure w s _
  | succ len ih =>
    intro cur hcur remIdx found ans
    have hlt : cur < s.frontier := by omega
    have hstep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩))) := by
      refine validHistory_read_bind hlt ?_
      split_ifs <;> exact validHistory_pure w s _
    have hst : (Memory.spec 0).clientState s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩)) = s := by
      unfold lookupStep
      change (Memory.spec 0).clientState s
        (if found = 0 ∧ s.mem cur = args.target then _ else _) = s
      split_ifs <;> rfl
    have hcur_next : ((Memory.spec 0).clientResult s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩))).cur = cur + 1 := by
      unfold lookupStep
      have : ((Memory.spec 0).clientResult s
          (if found = 0 ∧ s.mem cur = args.target then
            (pure ⟨cur + 1, remIdx / args.dom, 1, remIdx % args.dom⟩ : Memory.Prog LookupState)
           else
            pure ⟨cur + 1, remIdx / args.dom, found, ans⟩)).cur = cur + 1 := by
        split_ifs <;> rfl
      exact this
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩) >>=
          iterate lookupStep ⟨args.dom, args.target⟩ len))
    refine validHistory_bind_step hstep ?_
    rw [hst]
    let r := (Memory.spec 0).clientResult s
      (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩))
    exact ih r.cur (by rw [hcur_next]; omega) r.remIdx r.found r.ans

private theorem lookupAssign_result {args : LookupArgs} {us : List ℕ} {s : Memory.State}
    (hus : Block.HoldsList args.outPtr us s.mem) (hlen : us.length = args.outLen) :
    (Memory.spec 0).clientResult s (lookupAssign args) =
      assignScope us (lsbDecode args.dom us.length args.idx) args.target := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientResult_bind, ← hlen]
  have hfound1 : ∀ (n cur remIdx ans : ℕ),
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ n ⟨cur, remIdx, 1, ans⟩)).ans = ans := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro cur remIdx ans
      change ((Memory.spec 0).clientResult s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 1, ans⟩) >>=
          iterate lookupStep ⟨args.dom, args.target⟩ n)).ans = ans
      rw [StateTransitionSpec.clientResult_bind]
      have hst : (Memory.spec 0).clientState s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 1, ans⟩)) = s := rfl
      have hres : (Memory.spec 0).clientResult s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 1, ans⟩)) =
          ⟨cur + 1, remIdx / args.dom, 1, ans⟩ := rfl
      rw [hst, hres]
      exact ih _ _ _
  suffices ∀ (zs : List ℕ) (cur remIdx : ℕ), Block.HoldsList cur zs s.mem →
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ zs.length ⟨cur, remIdx, 0, 0⟩)).ans =
      assignScope zs (lsbDecode args.dom zs.length remIdx) args.target from
    this us args.outPtr args.idx hus
  intro zs
  induction zs with
  | nil => intro cur remIdx _; rfl
  | cons u rest ih =>
    intro cur remIdx hcur
    obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hcur
    change ((Memory.spec 0).clientResult s
      (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩) >>=
        iterate lookupStep ⟨args.dom, args.target⟩ rest.length)).ans = _
    rw [StateTransitionSpec.clientResult_bind]
    by_cases htu : args.target = u
    · have hst : (Memory.spec 0).clientState s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩)) = s := by
        unfold lookupStep
        change (Memory.spec 0).clientState s
          (if 0 = 0 ∧ s.mem cur = args.target then _ else _) = s
        rw [hhead, ite_eq_left ⟨rfl, htu.symm⟩]; rfl
      have hres : (Memory.spec 0).clientResult s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩)) =
          ⟨cur + 1, remIdx / args.dom, 1, remIdx % args.dom⟩ := by
        unfold lookupStep
        change (Memory.spec 0).clientResult s
          (if 0 = 0 ∧ s.mem cur = args.target then _ else _) = _
        rw [hhead, ite_eq_left ⟨rfl, htu.symm⟩]; rfl
      rw [hst, hres, hfound1]
      simp [lsbDecode, assignScope, htu]
    · have hne : u ≠ args.target := Ne.symm htu
      have hst : (Memory.spec 0).clientState s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩)) = s := by
        unfold lookupStep
        change (Memory.spec 0).clientState s
          (if 0 = 0 ∧ s.mem cur = args.target then _ else _) = s
        rw [hhead, ite_eq_right (fun h => hne h.2)]; rfl
      have hres : (Memory.spec 0).clientResult s
          (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, 0, 0⟩)) =
          ⟨cur + 1, remIdx / args.dom, 0, 0⟩ := by
        unfold lookupStep
        change (Memory.spec 0).clientResult s
          (if 0 = 0 ∧ s.mem cur = args.target then _ else _) = _
        rw [hhead, ite_eq_right (fun h => hne h.2)]; rfl
      rw [hst, hres, ih (cur + 1) (remIdx / args.dom) htail]
      simp [lsbDecode, assignScope, htu]

private theorem lookupAssign_realizes :
    Realizes .exact lookupAssign WordEncoding.encode WordEncoding.encode
      (fun w args _ => 0 < args.dom ∧ Fits w 1 ∧ Fits w (args.outPtr + args.outLen))
      (fun _ _ => 0) := by
  unfold lookupAssign
  realize
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st _ => st.cur + j = d.outPtr + d.outLen)
    (fun j st t hinv => ?_)
    (show (⟨d.outPtr, d.idx, 0, 0⟩ : LookupState).cur + d.outLen = d.outPtr + d.outLen from rfl)
  dsimp only
  refine ⟨?_, ?_⟩
  · split_ifs
    · exact ⟨Nat.ne_of_gt h.1, h.2.2.of_le (by omega), h.2.1⟩
    · exact ⟨Nat.ne_of_gt h.1, h.2.2.of_le (by omega)⟩
    · exact ⟨Nat.ne_of_gt h.1, h.2.2.of_le (by omega)⟩
  · unfold lookupStep
    have : ((Memory.spec 0).clientResult t
        (if st.found = 0 ∧ t.mem st.cur = d.target then
          (pure ⟨st.cur + 1, st.remIdx / d.dom, 1, st.remIdx % d.dom⟩ : Memory.Prog LookupState)
         else
          pure ⟨st.cur + 1, st.remIdx / d.dom, st.found, st.ans⟩)).cur + j =
        d.outPtr + d.outLen := by
      split_ifs
      · change (st.cur + 1) + j = d.outPtr + d.outLen; omega
      · change (st.cur + 1) + j = d.outPtr + d.outLen; omega
    exact this

private theorem lookupAssign_lt {args : LookupArgs} (hd : 0 < args.dom) (s : Memory.State) :
    (Memory.spec 0).clientResult s (lookupAssign args) < args.dom := by
  unfold lookupAssign
  rw [StateTransitionSpec.clientResult_bind]
  suffices ∀ (n cur remIdx found ans : ℕ), ans < args.dom →
      ((Memory.spec 0).clientResult s
        (iterate lookupStep ⟨args.dom, args.target⟩ n ⟨cur, remIdx, found, ans⟩)).ans <
      args.dom from
    this args.outLen args.outPtr args.idx 0 0 hd
  intro n
  induction n with
  | zero => intro _ _ _ _ hans; exact hans
  | succ n ih =>
    intro cur remIdx found ans hans
    change ((Memory.spec 0).clientResult s
      (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩) >>=
        iterate lookupStep ⟨args.dom, args.target⟩ n)).ans < args.dom
    rw [StateTransitionSpec.clientResult_bind]
    have hst : (Memory.spec 0).clientState s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩)) = s := by
      unfold lookupStep
      change (Memory.spec 0).clientState s
        (if found = 0 ∧ s.mem cur = args.target then _ else _) = s
      split_ifs <;> rfl
    have hnext : ((Memory.spec 0).clientResult s
        (lookupStep (⟨args.dom, args.target⟩, ⟨cur, remIdx, found, ans⟩))).ans < args.dom := by
      unfold lookupStep
      have : ((Memory.spec 0).clientResult s
          (if found = 0 ∧ s.mem cur = args.target then
            (pure ⟨cur + 1, remIdx / args.dom, 1, remIdx % args.dom⟩ : Memory.Prog LookupState)
           else
            pure ⟨cur + 1, remIdx / args.dom, found, ans⟩)).ans < args.dom := by
        split_ifs
        · exact Nat.mod_lt _ hd
        · exact hans
      exact this
    rw [hst]
    exact ih _ _ _ _ hnext

/-! ### Multiplicative factor capacity and Horner scope evaluation -/

private def capFactor (f : FactorTable ℕ ℕ) : ℕ :=
  max 1 (f.entries.toList.foldl max 0)

private theorem one_le_capFactor (f : FactorTable ℕ ℕ) : 1 ≤ capFactor f :=
  le_max_left 1 _

private theorem mem_entries_le_capFactor {f : FactorTable ℕ ℕ} {v : ℕ}
    (hv : v ∈ f.entries.toList) : v ≤ capFactor f :=
  (List.mem_le_foldl_max hv).trans (le_max_right 1 _)

private theorem evalAt_le_capFactor (d : ℕ) (f : FactorTable ℕ ℕ) (σ : ℕ → ℕ) :
    f.evalAt d σ ≤ capFactor f := by
  rw [FactorTable.evalAt, Array.getD]
  split_ifs with hlt
  · exact mem_entries_le_capFactor (Array.getElem_mem_toList hlt)
  · exact Nat.zero_le _

private theorem holdsFactor_read_entry_le {descAddr : ℕ} {f : FactorTable ℕ ℕ} {s : Memory.State}
    (hf : HoldsFactor descAddr f s) (fIdx : ℕ) :
    (if fIdx < s.mem (descAddr + 3) then s.mem (s.mem (descAddr + 2) + fIdx) else 0) ≤
      capFactor f := by
  obtain ⟨_, _, hel, _, hent⟩ := hf
  rw [hel]
  split_ifs with hlt
  · have hlt' : fIdx < f.entries.toList.length := by simpa using hlt
    rw [hent.2.get fIdx hlt']
    exact mem_entries_le_capFactor (List.getElem_mem hlt')
  · exact Nat.zero_le _

private theorem horner_step_bounds {dom scopeLen j acc pow valV : ℕ}
    (hdom : 0 < dom) (hval : valV < dom) (hacc : acc < pow)
    (hpow : pow * dom ^ (j + 1) = dom ^ scopeLen) :
    acc + valV * pow < pow * dom ∧
    (pow * dom) * dom ^ j = dom ^ scopeLen ∧
    pow * dom ≤ dom ^ scopeLen := by
  have hp1 : (1 + valV) * pow ≤ dom * pow := Nat.mul_le_mul_right pow (by omega)
  have hlt : acc + valV * pow < pow * dom := by
    calc acc + valV * pow < pow + valV * pow := Nat.add_lt_add_right hacc _
      _ = (1 + valV) * pow := by ring
      _ ≤ dom * pow := hp1
      _ = pow * dom := Nat.mul_comm dom pow
  have heq : (pow * dom) * dom ^ j = dom ^ scopeLen := by
    calc (pow * dom) * dom ^ j = pow * (dom * dom ^ j) := Nat.mul_assoc pow dom _
      _ = pow * dom ^ (j + 1) := by rw [pow_succ']
      _ = dom ^ scopeLen := hpow
  have hle : pow * dom ≤ dom ^ scopeLen := by
    have h1 : 1 ≤ dom ^ j := Nat.one_le_pow j dom hdom
    calc pow * dom ≤ (pow * dom) * dom ^ j := Nat.le_mul_of_pos_right _ h1
      _ = dom ^ scopeLen := heq
  exact ⟨hlt, heq, hle⟩

private structure EvalScopeArgs where
  dom : ℕ
  x : ℕ
  a : ℕ
  outPtr : ℕ
  outLen : ℕ
  idx : ℕ
  scopePtr : ℕ
  scopeLen : ℕ

private def EvalScopeArgs.equiv :
    EvalScopeArgs ≃ ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((((s.dom, s.x), s.a), s.outPtr), s.outLen), s.idx), s.scopePtr), s.scopeLen)
  invFun := fun (((((((dom, x), a), outPtr), outLen), idx), scopePtr), scopeLen) =>
    ⟨dom, x, a, outPtr, outLen, idx, scopePtr, scopeLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding EvalScopeArgs := .ofEquiv EvalScopeArgs.equiv

private structure EvalScopeEnv where
  dom : ℕ
  x : ℕ
  a : ℕ
  outPtr : ℕ
  outLen : ℕ
  idx : ℕ

private def EvalScopeEnv.equiv : EvalScopeEnv ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun e := (((((e.dom, e.x), e.a), e.outPtr), e.outLen), e.idx)
  invFun := fun (((((dom, x), a), outPtr), outLen), idx) => ⟨dom, x, a, outPtr, outLen, idx⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding EvalScopeEnv := .ofEquiv EvalScopeEnv.equiv

private structure EvalScopeState where
  cur : ℕ
  acc : ℕ
  pow : ℕ

private def EvalScopeState.equiv : EvalScopeState ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.cur, s.acc), s.pow)
  invFun := fun ((cur, acc), pow) => ⟨cur, acc, pow⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding EvalScopeState := .ofEquiv EvalScopeState.equiv

private def evalScopeStep (p : EvalScopeEnv × EvalScopeState) : Memory.Prog EvalScopeState :=
  Memory.read p.2.cur >>= fun v =>
    (if v = p.1.x then pure p.1.a
      else lookupAssign ⟨p.1.dom, v, p.1.outPtr, p.1.outLen, p.1.idx⟩) >>= fun valV =>
      pure ⟨p.2.cur + 1, p.2.acc + valV * p.2.pow, p.2.pow * p.1.dom⟩

private def evalScopeIdx (args : EvalScopeArgs) : Memory.Prog ℕ := do
  let res ← iterate evalScopeStep
    ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
    args.scopeLen ⟨args.scopePtr, 0, 1⟩
  pure res.acc

private theorem evalScopeStep_state (env : EvalScopeEnv) (st : EvalScopeState) (s : Memory.State) :
    (Memory.spec 0).clientState s (evalScopeStep (env, st)) = s := by
  unfold evalScopeStep
  rw [StateTransitionSpec.clientState_bind]
  have h1 : (Memory.spec 0).clientState s (Memory.read st.cur) = s := rfl
  have h2 : (Memory.spec 0).clientResult s (Memory.read st.cur) = s.mem st.cur := rfl
  rw [h1, h2, StateTransitionSpec.clientState_bind]
  split_ifs
  · rfl
  · rw [lookupAssign_state]; rfl

private theorem evalScopeIdx_state (args : EvalScopeArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (evalScopeIdx args) = s := by
  unfold evalScopeIdx
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of evalScopeStep _ (evalScopeStep_state _) args.scopeLen _ s

private theorem evalScopeIdx_cost (args : EvalScopeArgs) (s : Memory.State) :
    memoryCost (evalScopeIdx args) s ≤ args.scopeLen * (args.outLen + 1) := by
  unfold evalScopeIdx
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero, Nat.mul_comm]
  refine memoryCost_iterate_le_of evalScopeStep (args.outLen + 1) _ (fun st t => ?_)
    args.scopeLen ⟨args.scopePtr, 0, 1⟩ s
  unfold evalScopeStep
  dsimp only
  have hr : (Memory.spec 0).clientState t (Memory.read st.cur) = t := rfl
  have hres : (Memory.spec 0).clientResult t (Memory.read st.cur) = t.mem st.cur := rfl
  rw [memoryCost_bind', memoryCost_read, hr, hres, memoryCost_bind']
  split_ifs
  · rw [memoryCost_pure, memoryCost_pure]; omega
  · rw [lookupAssign_state, memoryCost_pure]
    have hlk := lookupAssign_cost ⟨args.dom, t.mem st.cur, args.outPtr, args.outLen, args.idx⟩ t
    dsimp only at hlk
    omega

private theorem evalScopeIdx_valid {w : ℕ} (args : EvalScopeArgs) {s : Memory.State}
    (hout : args.outPtr + args.outLen ≤ s.frontier)
    (hsc : args.scopePtr + args.scopeLen ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (evalScopeIdx args)) := by
  unfold evalScopeIdx
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  suffices ∀ len cur, cur + len ≤ s.frontier → ∀ acc pow,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate evalScopeStep env len ⟨cur, acc, pow⟩)) from
    this args.scopeLen args.scopePtr hsc 0 1
  intro len
  induction len with
  | zero => intro _ _ _ _; exact validHistory_pure w s _
  | succ len ih =>
    intro cur hcur acc pow
    have hlt : cur < s.frontier := by omega
    have hstep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (evalScopeStep (env, ⟨cur, acc, pow⟩))) := by
      unfold evalScopeStep
      refine validHistory_read_bind hlt ?_
      refine validHistory_bind_step ?_ (validHistory_pure w _ _)
      split_ifs
      · exact validHistory_pure w s _
      · exact lookupAssign_valid _ hout
    have hcur_next : ((Memory.spec 0).clientResult s
        (evalScopeStep (env, ⟨cur, acc, pow⟩))).cur = cur + 1 := by
      unfold evalScopeStep
      rw [StateTransitionSpec.clientResult_bind]
      have h1 : (Memory.spec 0).clientState s (Memory.read cur) = s := rfl
      have h2 : (Memory.spec 0).clientResult s (Memory.read cur) = s.mem cur := rfl
      rw [h1, h2, StateTransitionSpec.clientResult_bind]
      split_ifs <;> rfl
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (evalScopeStep (env, ⟨cur, acc, pow⟩) >>= iterate evalScopeStep env len))
    refine validHistory_bind_step hstep ?_
    rw [evalScopeStep_state]
    let r := (Memory.spec 0).clientResult s (evalScopeStep (env, ⟨cur, acc, pow⟩))
    exact ih r.cur (by rw [hcur_next]; omega) r.acc r.pow

private theorem evalScopeIdx_result {args : EvalScopeArgs} {outScope fScope : List ℕ}
    {s : Memory.State}
    (hout : Block.HoldsList args.outPtr outScope s.mem) (hout_len : outScope.length = args.outLen)
    (hsc : Block.HoldsList args.scopePtr fScope s.mem) (hsc_len : fScope.length = args.scopeLen) :
    (Memory.spec 0).clientResult s (evalScopeIdx args) =
      Nat.ofDigits args.dom (fScope.map fun v =>
        if v = args.x then args.a
        else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v) := by
  unfold evalScopeIdx
  rw [StateTransitionSpec.clientResult_bind, ← hsc_len]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  let σ : ℕ → ℕ := fun v =>
    if v = args.x then args.a
    else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v
  suffices ∀ (ys : List ℕ) (cur acc pow : ℕ), Block.HoldsList cur ys s.mem →
      ((Memory.spec 0).clientResult s (iterate evalScopeStep env ys.length ⟨cur, acc, pow⟩)).acc =
      acc + pow * Nat.ofDigits args.dom (ys.map σ) by
    simpa [env, σ] using this fScope args.scopePtr 0 1 hsc
  intro ys
  induction ys with
  | nil => intro cur acc pow _; change acc = acc + pow * 0; simp
  | cons v rest ih =>
    intro cur acc pow hcur
    obtain ⟨hhead, htail⟩ := Block.holdsList_cons_iff.mp hcur
    change ((Memory.spec 0).clientResult s
      (evalScopeStep (env, ⟨cur, acc, pow⟩) >>= iterate evalScopeStep env rest.length)).acc = _
    rw [StateTransitionSpec.clientResult_bind, evalScopeStep_state]
    have hstep_res : (Memory.spec 0).clientResult s (evalScopeStep (env, ⟨cur, acc, pow⟩)) =
        ⟨cur + 1, acc + σ v * pow, pow * args.dom⟩ := by
      unfold evalScopeStep
      rw [StateTransitionSpec.clientResult_bind]
      have h1 : (Memory.spec 0).clientState s (Memory.read cur) = s := rfl
      have h2 : (Memory.spec 0).clientResult s (Memory.read cur) = v := hhead
      rw [h1, h2, StateTransitionSpec.clientResult_bind]
      by_cases hvx : v = args.x
      · simp [env, σ, hvx]; rfl
      · simp only [env, σ, hvx, ↓reduceIte]
        rw [lookupAssign_state, lookupAssign_result hout hout_len]
        rfl
    rw [hstep_res, ih (cur + 1) _ _ htail, List.map_cons, Nat.ofDigits_cons]
    ring

private theorem evalScopeIdx_realizes :
    Realizes .exact evalScopeIdx WordEncoding.encode WordEncoding.encode
      (fun w args _ => 0 < args.dom ∧ args.a < args.dom ∧ Fits w 1 ∧
        Fits w (args.outPtr + args.outLen) ∧ Fits w (args.scopePtr + args.scopeLen) ∧
        Fits w (args.dom ^ args.scopeLen))
      (fun _ _ => 0) := by
  unfold evalScopeIdx
  realize [lookupAssign_realizes]
  · exact h.2.2.1
  · refine iterationSafe_of_stepInv _ _ w d
      (fun j st _ => st.cur + j = d.scopePtr + d.scopeLen ∧ st.acc < st.pow ∧
        st.pow * d.dom ^ j = d.dom ^ d.scopeLen)
      (fun j st t ⟨hcur, hacc, hpow⟩ => ?_)
      ⟨rfl, Nat.zero_lt_one, Nat.one_mul _⟩
    dsimp only
    obtain ⟨hdom, ha, h1, hout, hsc, hpow_fit⟩ := h
    let lkArgs : LookupArgs := ⟨d.dom, t.mem st.cur, d.outPtr, d.outLen, d.idx⟩
    have hlk_lt : (Memory.spec 0).clientResult t (lookupAssign lkArgs) < d.dom :=
      lookupAssign_lt hdom t
    have hb_a := horner_step_bounds hdom ha hacc hpow
    have hb_lk := horner_step_bounds hdom hlk_lt hacc hpow
    refine ⟨?_, ?_⟩
    · split_ifs
      · exact ⟨trivial, hsc.of_le (by omega), hpow_fit.of_le (hb_a.1.le.trans hb_a.2.2),
          hpow_fit.of_le hb_a.2.2⟩
      · exact ⟨⟨hdom, h1, hout⟩, hsc.of_le (by omega),
          hpow_fit.of_le (hb_lk.1.le.trans hb_lk.2.2), hpow_fit.of_le hb_lk.2.2⟩
    · unfold evalScopeStep
      rw [StateTransitionSpec.clientResult_bind]
      have hr1 : (Memory.spec 0).clientState t (Memory.read st.cur) = t := rfl
      have hr2 : (Memory.spec 0).clientResult t (Memory.read st.cur) = t.mem st.cur := rfl
      rw [hr1, hr2, StateTransitionSpec.clientResult_bind]
      split_ifs
      · change (st.cur + 1) + j = d.scopePtr + d.scopeLen ∧ st.acc + d.a * st.pow < st.pow * d.dom ∧
          (st.pow * d.dom) * d.dom ^ j = d.dom ^ d.scopeLen
        exact ⟨by omega, hb_a.1, hb_a.2.1⟩
      · rw [lookupAssign_state]
        change (st.cur + 1) + j = d.scopePtr + d.scopeLen ∧
          st.acc + (Memory.spec 0).clientResult t (lookupAssign lkArgs) * st.pow < st.pow * d.dom ∧
          (st.pow * d.dom) * d.dom ^ j = d.dom ^ d.scopeLen
        exact ⟨by omega, hb_lk.1, hb_lk.2.1⟩

/-! ### Bucket product evaluation (`evalBucketProd`) -/

private structure BucketProdArgs where
  dom : ℕ
  x : ℕ
  a : ℕ
  outPtr : ℕ
  outLen : ℕ
  idx : ℕ
  bucketPtr : ℕ
  bucketLen : ℕ

private def BucketProdArgs.equiv :
    BucketProdArgs ≃ ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((((s.dom, s.x), s.a), s.outPtr), s.outLen), s.idx), s.bucketPtr), s.bucketLen)
  invFun := fun (((((((dom, x), a), outPtr), outLen), idx), bucketPtr), bucketLen) =>
    ⟨dom, x, a, outPtr, outLen, idx, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BucketProdArgs := .ofEquiv BucketProdArgs.equiv

private structure BucketProdState where
  curDesc : ℕ
  prod : ℕ

private def BucketProdState.equiv : BucketProdState ≃ ℕ × ℕ where
  toFun s := (s.curDesc, s.prod)
  invFun := fun (curDesc, prod) => ⟨curDesc, prod⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BucketProdState := .ofEquiv BucketProdState.equiv

private def bucketProdStep (p : EvalScopeEnv × BucketProdState) : Memory.Prog BucketProdState :=
  Memory.read p.2.curDesc >>= fun scopePtr =>
  Memory.read (p.2.curDesc + 1) >>= fun scopeLen =>
  Memory.read (p.2.curDesc + 2) >>= fun entriesPtr =>
  Memory.read (p.2.curDesc + 3) >>= fun entriesLen =>
  evalScopeIdx ⟨p.1.dom, p.1.x, p.1.a, p.1.outPtr, p.1.outLen, p.1.idx, scopePtr, scopeLen⟩ >>=
    fun fIdx =>
    (if fIdx < entriesLen then Memory.read (entriesPtr + fIdx) else pure 0) >>= fun entry =>
      pure ⟨p.2.curDesc + 4, p.2.prod * entry⟩

private def evalBucketProd (args : BucketProdArgs) : Memory.Prog ℕ := do
  let res ← iterate bucketProdStep
    ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
    args.bucketLen ⟨args.bucketPtr, 1⟩
  pure res.prod

private theorem bucketProdStep_state (env : EvalScopeEnv) (st : BucketProdState)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (bucketProdStep (env, st)) = s := by
  unfold bucketProdStep
  have hr (addr : ℕ) : (Memory.spec 0).clientState s (Memory.read addr) = s := rfl
  have hres (addr : ℕ) : (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl
  rw [StateTransitionSpec.clientState_bind, hr, hres,
    StateTransitionSpec.clientState_bind, hr, hres,
    StateTransitionSpec.clientState_bind, hr, hres,
    StateTransitionSpec.clientState_bind, hr, hres,
    StateTransitionSpec.clientState_bind, evalScopeIdx_state,
    StateTransitionSpec.clientState_bind]
  split_ifs <;> rfl

private theorem evalBucketProd_state (args : BucketProdArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (evalBucketProd args) = s := by
  unfold evalBucketProd
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of bucketProdStep _ (bucketProdStep_state _) args.bucketLen _ s

private theorem bucketProdStep_result (env : EvalScopeEnv) (st : BucketProdState)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (bucketProdStep (env, st)) =
      let fIdx := (Memory.spec 0).clientResult s (evalScopeIdx
        ⟨env.dom, env.x, env.a, env.outPtr, env.outLen, env.idx,
          s.mem st.curDesc, s.mem (st.curDesc + 1)⟩)
      let entry := if fIdx < s.mem (st.curDesc + 3) then s.mem (s.mem (st.curDesc + 2) + fIdx)
        else 0
      ⟨st.curDesc + 4, st.prod * entry⟩ := by
  unfold bucketProdStep
  dsimp only
  have hr (addr : ℕ) : (Memory.spec 0).clientState s (Memory.read addr) = s := rfl
  have hres (addr : ℕ) : (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl
  rw [StateTransitionSpec.clientResult_bind, hr, hres,
    StateTransitionSpec.clientResult_bind, hr, hres,
    StateTransitionSpec.clientResult_bind, hr, hres,
    StateTransitionSpec.clientResult_bind, hr, hres,
    StateTransitionSpec.clientResult_bind, evalScopeIdx_state,
    StateTransitionSpec.clientResult_bind]
  split_ifs <;> rfl

private theorem evalBucketProd_cost {args : BucketProdArgs} {bucket : List (FactorTable ℕ ℕ)}
    {maxScope : ℕ} {s : Memory.State}
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope) :
    memoryCost (evalBucketProd args) s ≤ args.bucketLen * (5 + maxScope * (args.outLen + 1)) := by
  unfold evalBucketProd
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero, ← hlen]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur prod : ℕ),
      HoldsFactorList cur fs s → (∀ f ∈ fs, f.scope.length ≤ maxScope) →
      memoryCost (iterate bucketProdStep env fs.length ⟨cur, prod⟩) s ≤
        fs.length * (5 + maxScope * (args.outLen + 1)) from
    this bucket args.bucketPtr 1 hb hmax
  intro fs
  induction fs with
  | nil => intro _ _ _ _; simp [iterate]
  | cons f rest ih =>
    intro cur prod hfs hmax_fs
    obtain ⟨hf, hrest⟩ := hfs
    have hstep_cost : memoryCost (bucketProdStep (env, ⟨cur, prod⟩)) s ≤
        5 + maxScope * (args.outLen + 1) := by
      unfold bucketProdStep
      dsimp only [env]
      have hr (addr : ℕ) : (Memory.spec 0).clientState s (Memory.read addr) = s := rfl
      have hres (addr : ℕ) : (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl
      rw [memoryCost_bind', memoryCost_read, hr, hres,
        memoryCost_bind', memoryCost_read, hr, hres,
        memoryCost_bind', memoryCost_read, hr, hres,
        memoryCost_bind', memoryCost_read, hr, hres,
        memoryCost_bind', evalScopeIdx_state, memoryCost_bind']
      have hev := evalScopeIdx_cost ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx,
        s.mem cur, s.mem (cur + 1)⟩ s
      dsimp only at hev
      have hsc_le : s.mem (cur + 1) * (args.outLen + 1) ≤ maxScope * (args.outLen + 1) := by
        rw [hf.2.1]
        exact Nat.mul_le_mul_right _ (hmax_fs f (List.mem_cons_self ..))
      split_ifs
      · rw [memoryCost_read, hr, memoryCost_pure]; omega
      · rw [memoryCost_pure, memoryCost_pure]; omega
    change memoryCost (bucketProdStep (env, ⟨cur, prod⟩) >>= iterate bucketProdStep env rest.length)
      s ≤ _
    rw [memoryCost_bind', bucketProdStep_state, bucketProdStep_result]
    dsimp only
    calc memoryCost (bucketProdStep (env, ⟨cur, prod⟩)) s + _
        ≤ (5 + maxScope * (args.outLen + 1)) + rest.length * (5 + maxScope * (args.outLen + 1)) :=
          Nat.add_le_add hstep_cost
            (ih (cur + 4) _ hrest (fun g hg => hmax_fs g (List.mem_cons_of_mem f hg)))
      _ = (rest.length + 1) * (5 + maxScope * (args.outLen + 1)) := by ring

private theorem evalBucketProd_valid {w : ℕ} {args : BucketProdArgs}
    {bucket : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hout : args.outPtr + args.outLen ≤ s.frontier)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (evalBucketProd args)) := by
  unfold evalBucketProd
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  rw [← hlen]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur prod : ℕ), HoldsFactorList cur fs s →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate bucketProdStep env fs.length ⟨cur, prod⟩)) from
    this bucket args.bucketPtr 1 hb
  intro fs
  induction fs with
  | nil => intro _ _ _; exact validHistory_pure w s _
  | cons f rest ih =>
    intro cur prod ⟨hf, hrest⟩
    obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
    have hstep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (bucketProdStep (env, ⟨cur, prod⟩))) := by
      unfold bucketProdStep
      dsimp only [env]
      refine validHistory_read_bind (by omega) ?_
      refine validHistory_read_bind (by omega) ?_
      refine validHistory_read_bind (by omega) ?_
      refine validHistory_read_bind (by omega) ?_
      refine validHistory_bind_step
        (evalScopeIdx_valid _ hout (by dsimp only; rw [hsl]; exact hsc.1)) ?_
      rw [evalScopeIdx_state]
      refine validHistory_bind_step ?_ (validHistory_pure w _ _)
      split_ifs with hlt
      · rw [hel] at hlt
        have hent_le : s.mem (cur + 2) + f.entries.size ≤ s.frontier := by
          simpa [Array.length_toList] using hent.1
        exact validHistory_read (by omega)
      · exact validHistory_pure w s _
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (bucketProdStep (env, ⟨cur, prod⟩) >>= iterate bucketProdStep env rest.length))
    refine validHistory_bind_step hstep ?_
    rw [bucketProdStep_state, bucketProdStep_result]
    exact ih (cur + 4) _ hrest

private theorem evalBucketProd_result {args : BucketProdArgs} {outScope : List ℕ}
    {bucket : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hout : Block.HoldsList args.outPtr outScope s.mem) (hout_len : outScope.length = args.outLen)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (evalBucketProd args) =
      (bucket.map fun f => f.evalAt args.dom fun v =>
        if v = args.x then args.a
        else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v).prod := by
  unfold evalBucketProd
  rw [StateTransitionSpec.clientResult_bind, ← hlen]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  let σ : ℕ → ℕ := fun v =>
    if v = args.x then args.a
    else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur prod : ℕ), HoldsFactorList cur fs s →
      ((Memory.spec 0).clientResult s (iterate bucketProdStep env fs.length ⟨cur, prod⟩)).prod =
      prod * (fs.map fun f => f.evalAt args.dom σ).prod by
    simpa [env, σ] using this bucket args.bucketPtr 1 hb
  intro fs
  induction fs with
  | nil => intro cur prod _; change prod = prod * 1; simp
  | cons f rest ih =>
    intro cur prod ⟨hf, hrest⟩
    obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
    change ((Memory.spec 0).clientResult s
      (bucketProdStep (env, ⟨cur, prod⟩) >>= iterate bucketProdStep env rest.length)).prod = _
    rw [StateTransitionSpec.clientResult_bind, bucketProdStep_state, bucketProdStep_result]
    have hfIdx : (Memory.spec 0).clientResult s (evalScopeIdx
        ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx,
          s.mem cur, s.mem (cur + 1)⟩) = Nat.ofDigits args.dom (f.scope.map σ) :=
      evalScopeIdx_result hout hout_len hsc.2 hsl.symm
    have hentry : (if Nat.ofDigits args.dom (f.scope.map σ) < s.mem (cur + 3) then
        s.mem (s.mem (cur + 2) + Nat.ofDigits args.dom (f.scope.map σ)) else 0) =
        f.evalAt args.dom σ := by
      rw [hel, FactorTable.evalAt, Array.getD]
      split_ifs with hlt
      · have hlt' : Nat.ofDigits args.dom (f.scope.map σ) < f.entries.toList.length := by
          simpa using hlt
        rw [hent.2.get _ hlt', Array.getElem_toList]
        rfl
      · rfl
    dsimp only [env]
    rw [hfIdx, hentry, ih (cur + 4) _ hrest, List.map_cons, List.prod_cons, Nat.mul_assoc]

private theorem evalBucketProd_realizes :
    Realizes .exact evalBucketProd WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        0 < args.dom ∧ args.a < args.dom ∧ Fits w 1 ∧
        args.outPtr + args.outLen ≤ s.frontier ∧
        ∃ bucket B maxScope,
          bucket.length = args.bucketLen ∧
          HoldsFactorList args.bucketPtr bucket s ∧
          (∀ f ∈ bucket, f.scope.length ≤ maxScope) ∧
          Fits w (args.dom ^ maxScope) ∧
          (bucket.map capFactor).prod ≤ B ∧
          Fits w B)
      (fun _ _ => 0) := by
  unfold evalBucketProd
  realize [evalScopeIdx_realizes]
  · exact h.2.2.1
  · obtain ⟨hdom, ha, h1, hout, bucket, B, maxScope, hblen, hbf, hmax, hdomPow, hcapB, hB⟩ := h
    refine iterationSafe_of_stepInv _ _ w d
      (fun j st t => t = s ∧ ∃ rem, rem.length = j ∧ HoldsFactorList st.curDesc rem s ∧
        (∀ f ∈ rem, f.scope.length ≤ maxScope) ∧ st.prod * (rem.map capFactor).prod ≤ B)
      (fun j st t ⟨ht, rem, hrem_len, hrem_holds, hrem_max, hprod_le⟩ => ?_)
      ⟨rfl, bucket, hblen, hbf, hmax, by simpa using hcapB⟩
    subst t
    dsimp only
    rcases rem with _ | ⟨f, rem'⟩
    · simp at hrem_len
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_len
    obtain ⟨hf, hrem'_holds⟩ := hrem_holds
    have hf_max : f.scope.length ≤ maxScope := hrem_max f (List.mem_cons_self ..)
    have hrem'_max : ∀ g ∈ rem', g.scope.length ≤ maxScope :=
      fun g hg => hrem_max g (List.mem_cons_of_mem f hg)
    have hent_le : ∀ fIdx,
        (if fIdx < s.mem (st.curDesc + 3) then s.mem (s.mem (st.curDesc + 2) + fIdx) else 0) ≤
          capFactor f := holdsFactor_read_entry_le hf
    have hprod_cap : st.prod * capFactor f * (rem'.map capFactor).prod ≤ B := by
      simpa [List.map_cons, List.prod_cons, Nat.mul_assoc] using hprod_le
    have hprod_f : st.prod * capFactor f ≤ B := by
      have h1' : 1 ≤ (rem'.map capFactor).prod :=
        List.one_le_prod_of_one_le (by simp [one_le_capFactor])
      exact (Nat.le_mul_of_pos_right _ h1').trans hprod_cap
    obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
    have hpow_f : Fits w (d.dom ^ s.mem (st.curDesc + 1)) := by
      rw [hsl]
      exact hdomPow.of_le (Nat.pow_le_pow_right hdom hf_max)
    refine ⟨?_, ?_⟩
    · refine ⟨hmem.frontier_fits.of_le (by omega), hmem.frontier_fits.of_le (by omega),
        hmem.frontier_fits.of_le (by omega),
        ⟨hdom, ha, h1, hmem.frontier_fits.of_le hout, hmem.frontier_fits.of_le (by
          rw [hsl]; exact hsc.1), hpow_f⟩, ?_⟩
      split_ifs with hlt
      · have hent_sz : s.mem (st.curDesc + 2) + f.entries.size ≤ s.frontier := by
          simpa [Array.length_toList] using hent.1
        have hlt_sz : (Memory.spec 0).clientResult s (evalScopeIdx
            ⟨d.dom, d.x, d.a, d.outPtr, d.outLen, d.idx,
              s.mem st.curDesc, s.mem (st.curDesc + 1)⟩) < f.entries.size := by
          simpa [hel] using hlt
        have hm_le : st.prod * s.mem (s.mem (st.curDesc + 2) +
            (Memory.spec 0).clientResult s (evalScopeIdx
              ⟨d.dom, d.x, d.a, d.outPtr, d.outLen, d.idx,
                s.mem st.curDesc, s.mem (st.curDesc + 1)⟩)) ≤ B := by
          have he := hent_le ((Memory.spec 0).clientResult s (evalScopeIdx
            ⟨d.dom, d.x, d.a, d.outPtr, d.outLen, d.idx,
              s.mem st.curDesc, s.mem (st.curDesc + 1)⟩))
          rw [ite_eq_left hlt] at he
          exact (Nat.mul_le_mul_left st.prod he).trans hprod_f
        rw [evalScopeIdx_state]
        refine ⟨hmem.frontier_fits.of_le (by omega), hmem.frontier_fits.of_le hd, ?_⟩
        exact hB.of_le hm_le
      · rw [evalScopeIdx_state]
        refine ⟨trivial, hmem.frontier_fits.of_le hd, ?_⟩
        change Fits w (st.prod * 0)
        simp
    · rw [bucketProdStep_state, bucketProdStep_result]
      dsimp only
      refine ⟨rfl, rem', hrem_len, hrem'_holds, hrem'_max, ?_⟩
      have he := hent_le ((Memory.spec 0).clientResult s (evalScopeIdx
        ⟨d.dom, d.x, d.a, d.outPtr, d.outLen, d.idx, s.mem st.curDesc, s.mem (st.curDesc + 1)⟩))
      exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left st.prod he)).trans hprod_cap

private theorem evalBucketProd_le_cap {args : BucketProdArgs} {bucket : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (hb : HoldsFactorList args.bucketPtr bucket s)
    (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (evalBucketProd args) ≤ (bucket.map capFactor).prod := by
  unfold evalBucketProd
  rw [StateTransitionSpec.clientResult_bind, ← hlen]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  let env : EvalScopeEnv := ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx⟩
  suffices ∀ (fs : List (FactorTable ℕ ℕ)) (cur prod : ℕ), HoldsFactorList cur fs s →
      ((Memory.spec 0).clientResult s (iterate bucketProdStep env fs.length ⟨cur, prod⟩)).prod ≤
      prod * (fs.map capFactor).prod by
    simpa [env] using this bucket args.bucketPtr 1 hb
  intro fs
  induction fs with
  | nil => intro cur prod _; change prod ≤ prod * 1; simp
  | cons f rest ih =>
    intro cur prod ⟨hf, hrest⟩
    change ((Memory.spec 0).clientResult s
      (bucketProdStep (env, ⟨cur, prod⟩) >>= iterate bucketProdStep env rest.length)).prod ≤ _
    rw [StateTransitionSpec.clientResult_bind, bucketProdStep_state, bucketProdStep_result]
    dsimp only [env]
    have he := holdsFactor_read_entry_le hf ((Memory.spec 0).clientResult s (evalScopeIdx
      ⟨args.dom, args.x, args.a, args.outPtr, args.outLen, args.idx,
        s.mem cur, s.mem (cur + 1)⟩))
    calc ((Memory.spec 0).clientResult s (iterate bucketProdStep env rest.length _)).prod
        ≤ (prod * _) * (rest.map capFactor).prod := ih (cur + 4) _ hrest
      _ ≤ (prod * capFactor f) * (rest.map capFactor).prod :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left prod he)
      _ = prod * ((f :: rest).map capFactor).prod := by
          simp [List.map_cons, List.prod_cons, Nat.mul_assoc]

/-! ### Domain summation (`sumDomainValues`) and table materialization (`buildOutEntries`) -/

private structure SumDomainArgs where
  dom : ℕ
  x : ℕ
  outPtr : ℕ
  outLen : ℕ
  idx : ℕ
  bucketPtr : ℕ
  bucketLen : ℕ

private def SumDomainArgs.equiv :
    SumDomainArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((((s.dom, s.x), s.outPtr), s.outLen), s.idx), s.bucketPtr), s.bucketLen)
  invFun := fun ((((((dom, x), outPtr), outLen), idx), bucketPtr), bucketLen) =>
    ⟨dom, x, outPtr, outLen, idx, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SumDomainArgs := .ofEquiv SumDomainArgs.equiv

private structure SumDomainState where
  curA : ℕ
  sumAcc : ℕ

private def SumDomainState.equiv : SumDomainState ≃ ℕ × ℕ where
  toFun s := (s.curA, s.sumAcc)
  invFun := fun (curA, sumAcc) => ⟨curA, sumAcc⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SumDomainState := .ofEquiv SumDomainState.equiv

private def sumDomainStep (p : SumDomainArgs × SumDomainState) : Memory.Prog SumDomainState :=
  Memory.read 0 >>= fun _ =>
  evalBucketProd
    ⟨p.1.dom, p.1.x, p.2.curA, p.1.outPtr, p.1.outLen, p.1.idx, p.1.bucketPtr, p.1.bucketLen⟩
    >>= fun prod =>
  pure ⟨p.2.curA + 1, p.2.sumAcc + prod⟩

private def sumDomainValues (args : SumDomainArgs) : Memory.Prog ℕ :=
  iterate sumDomainStep args args.dom ⟨0, 0⟩ >>= fun res => pure res.sumAcc

private theorem sumDomainStep_state (args : SumDomainArgs) (st : SumDomainState)
    (s : Memory.State) :
    (Memory.spec 0).clientState s (sumDomainStep (args, st)) = s := by
  unfold sumDomainStep
  have hr : (Memory.spec 0).clientState s (Memory.read 0) = s := rfl
  rw [StateTransitionSpec.clientState_bind, hr, StateTransitionSpec.clientState_bind,
    evalBucketProd_state]
  rfl

private theorem sumDomainStep_result (args : SumDomainArgs) (st : SumDomainState)
    (s : Memory.State) :
    (Memory.spec 0).clientResult s (sumDomainStep (args, st)) =
      ⟨st.curA + 1, st.sumAcc + (Memory.spec 0).clientResult s (evalBucketProd
        ⟨args.dom, args.x, st.curA, args.outPtr, args.outLen, args.idx,
          args.bucketPtr, args.bucketLen⟩)⟩ := by
  unfold sumDomainStep
  have hr : (Memory.spec 0).clientState s (Memory.read 0) = s := rfl
  rw [StateTransitionSpec.clientResult_bind, hr, StateTransitionSpec.clientResult_bind,
    evalBucketProd_state]
  rfl

private theorem sumDomainValues_state (args : SumDomainArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (sumDomainValues args) = s := by
  unfold sumDomainValues
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of sumDomainStep args (sumDomainStep_state args) args.dom ⟨0, 0⟩ s

private theorem memoryCost_iterate_le_of_state_eq {α δ : Type} (step : δ × α → Memory.Prog α)
    (c : ℕ) (env : δ) (s : Memory.State)
    (hst : ∀ a, (Memory.spec 0).clientState s (step (env, a)) = s)
    (hcost : ∀ a, memoryCost (step (env, a)) s ≤ c) :
    ∀ n a, memoryCost (iterate step env n a) s ≤ n * c
  | 0, _ => by simp [iterate]
  | n + 1, a => by
    change memoryCost (step (env, a) >>= iterate step env n) s ≤ (n + 1) * c
    rw [memoryCost_bind', hst a]
    calc memoryCost (step (env, a)) s + _
        ≤ c + n * c := Nat.add_le_add (hcost a)
          (memoryCost_iterate_le_of_state_eq step c env s hst hcost n _)
      _ = (n + 1) * c := by ring

private theorem sumDomainValues_cost {args : SumDomainArgs} {bucket : List (FactorTable ℕ ℕ)}
    {maxScope : ℕ} {s : Memory.State}
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen)
    (hmax : ∀ f ∈ bucket, f.scope.length ≤ maxScope) :
    memoryCost (sumDomainValues args) s ≤
      args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1))) := by
  unfold sumDomainValues
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  refine memoryCost_iterate_le_of_state_eq sumDomainStep
    (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1))) args s
    (fun st => sumDomainStep_state args st s) (fun st => ?_) args.dom ⟨0, 0⟩
  unfold sumDomainStep
  have hr : (Memory.spec 0).clientState s (Memory.read 0) = s := rfl
  rw [memoryCost_bind', memoryCost_read, hr, memoryCost_bind', evalBucketProd_state,
    memoryCost_pure, Nat.add_zero]
  exact Nat.add_le_add_left (evalBucketProd_cost hb hlen hmax) 1

private theorem sumDomainValues_valid {w : ℕ} {args : SumDomainArgs}
    {bucket : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hs0 : 0 < s.frontier) (hout : args.outPtr + args.outLen ≤ s.frontier)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (sumDomainValues args)) := by
  unfold sumDomainValues
  refine validHistory_bind_step ?_ (validHistory_pure w _ _)
  suffices ∀ n st, (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (iterate sumDomainStep args n st)) from
    this args.dom ⟨0, 0⟩
  intro n
  induction n with
  | zero => intro _; exact validHistory_pure w s _
  | succ n ih =>
    intro st
    have hstep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (sumDomainStep (args, st))) := by
      unfold sumDomainStep
      refine validHistory_read_bind hs0 ?_
      refine validHistory_bind_step (evalBucketProd_valid hout hb hlen) ?_
      exact validHistory_pure w _ _
    change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s
        (sumDomainStep (args, st) >>= iterate sumDomainStep args n))
    refine validHistory_bind_step hstep ?_
    rw [sumDomainStep_state]
    exact ih _

private theorem sumDomainValues_le_cap {args : SumDomainArgs} {bucket : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (hb : HoldsFactorList args.bucketPtr bucket s)
    (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (sumDomainValues args) ≤
      args.dom * (bucket.map capFactor).prod := by
  unfold sumDomainValues
  rw [StateTransitionSpec.clientResult_bind]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  suffices ∀ (k curA acc : ℕ),
      ((Memory.spec 0).clientResult s (iterate sumDomainStep args k ⟨curA, acc⟩)).sumAcc ≤
      acc + k * (bucket.map capFactor).prod by
    simpa using this args.dom 0 0
  intro k
  induction k with
  | zero => intro curA acc; change acc ≤ acc + 0 * _; simp
  | succ k ih =>
    intro curA acc
    change ((Memory.spec 0).clientResult s
      (sumDomainStep (args, ⟨curA, acc⟩) >>= iterate sumDomainStep args k)).sumAcc ≤ _
    rw [StateTransitionSpec.clientResult_bind, sumDomainStep_state, sumDomainStep_result]
    have hp := evalBucketProd_le_cap
      (args := ⟨args.dom, args.x, curA, args.outPtr, args.outLen, args.idx,
        args.bucketPtr, args.bucketLen⟩) hb hlen
    calc ((Memory.spec 0).clientResult s (iterate sumDomainStep args k _)).sumAcc
        ≤ (acc + _) + k * (bucket.map capFactor).prod := ih (curA + 1) _
      _ ≤ (acc + (bucket.map capFactor).prod) + k * (bucket.map capFactor).prod :=
          Nat.add_le_add_right (Nat.add_le_add_left hp acc) _
      _ = acc + (k + 1) * (bucket.map capFactor).prod := by ring

private theorem sumDomainValues_result {args : SumDomainArgs} {outScope : List ℕ}
    {bucket : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hout : Block.HoldsList args.outPtr outScope s.mem) (hout_len : outScope.length = args.outLen)
    (hb : HoldsFactorList args.bucketPtr bucket s) (hlen : bucket.length = args.bucketLen) :
    (Memory.spec 0).clientResult s (sumDomainValues args) =
      ∑ a : Fin args.dom,
        (bucket.map fun f => f.evalAt args.dom fun v =>
          if v = args.x then a.1
          else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v).prod := by
  unfold sumDomainValues
  rw [StateTransitionSpec.clientResult_bind,
    Fin.sum_univ_eq_sum_range (fun a =>
      (bucket.map fun f => f.evalAt args.dom fun v =>
        if v = args.x then a
        else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v).prod)]
  have hpure (t : Memory.State) (v : ℕ) : (Memory.spec 0).clientResult t (pure v) = v := rfl
  rw [hpure]
  let term : ℕ → ℕ := fun a =>
    (bucket.map fun f => f.evalAt args.dom fun v =>
      if v = args.x then a
      else assignScope outScope (lsbDecode args.dom outScope.length args.idx) v).prod
  suffices ∀ (k startA acc : ℕ),
      ((Memory.spec 0).clientResult s (iterate sumDomainStep args k ⟨startA, acc⟩)).sumAcc =
      acc + ∑ i ∈ Finset.range k, term (startA + i) by
    simpa [term] using this args.dom 0 0
  intro k
  induction k with
  | zero => intro startA acc; change acc = acc + 0; simp
  | succ k ih =>
    intro startA acc
    change ((Memory.spec 0).clientResult s
      (sumDomainStep (args, ⟨startA, acc⟩) >>= iterate sumDomainStep args k)).sumAcc = _
    rw [StateTransitionSpec.clientResult_bind, sumDomainStep_state, sumDomainStep_result]
    have hev : (Memory.spec 0).clientResult s (evalBucketProd
        ⟨args.dom, args.x, startA, args.outPtr, args.outLen, args.idx,
          args.bucketPtr, args.bucketLen⟩) = term startA :=
      evalBucketProd_result hout hout_len hb hlen
    rw [hev, ih (startA + 1) _, Finset.sum_range_succ']
    have hshift : (∑ i ∈ Finset.range k, term (startA + 1 + i)) =
        ∑ i ∈ Finset.range k, term (startA + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => congrArg term (by omega)
    rw [hshift, Nat.add_zero]
    ring

private theorem sumDomainValues_realizes :
    Realizes .exact sumDomainValues WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        0 < args.dom ∧ Fits w 1 ∧
        args.outPtr + args.outLen ≤ s.frontier ∧
        ∃ bucket B maxScope,
          bucket.length = args.bucketLen ∧
          HoldsFactorList args.bucketPtr bucket s ∧
          (∀ f ∈ bucket, f.scope.length ≤ maxScope) ∧
          Fits w (args.dom ^ maxScope) ∧
          args.dom * (bucket.map capFactor).prod ≤ B ∧
          Fits w B)
      (fun _ _ => 0) := by
  unfold sumDomainValues
  realize [evalBucketProd_realizes]
  obtain ⟨hdom, h1, hout, bucket, B, maxScope, hblen, hbf, hmax, hdomPow, hcapB, hB⟩ := h
  refine iterationSafe_of_stepInv _ _ w d
    (fun j st t => t = s ∧ st.curA + j = d.dom ∧ st.sumAcc ≤ st.curA * (bucket.map capFactor).prod)
    (fun j st t ⟨ht, hcurA, hsum⟩ => ?_)
    ⟨rfl, by simp, by simp⟩
  subst t
  dsimp only
  have h1_prod : 1 ≤ (bucket.map capFactor).prod :=
    List.one_le_prod_of_one_le (by simp [one_le_capFactor])
  have hprod_le_B : (bucket.map capFactor).prod ≤ B :=
    (Nat.le_mul_of_pos_left _ hdom).trans hcapB
  have hcurA_fit : Fits w (st.curA + 1) := by
    have hle : st.curA + 1 ≤ B := by
      calc st.curA + 1 ≤ d.dom := by omega
        _ ≤ d.dom * (bucket.map capFactor).prod := Nat.le_mul_of_pos_right _ h1_prod
        _ ≤ B := hcapB
    exact hB.of_le hle
  have hp := evalBucketProd_le_cap
    (args := ⟨d.dom, d.x, st.curA, d.outPtr, d.outLen, d.idx, d.bucketPtr, d.bucketLen⟩) hbf hblen
  have hsum_next : st.sumAcc + (Memory.spec 0).clientResult s (evalBucketProd
      ⟨d.dom, d.x, st.curA, d.outPtr, d.outLen, d.idx, d.bucketPtr, d.bucketLen⟩) ≤
      (st.curA + 1) * (bucket.map capFactor).prod := by
    calc st.sumAcc + _ ≤ st.curA * (bucket.map capFactor).prod + (bucket.map capFactor).prod :=
          Nat.add_le_add hsum hp
      _ = (st.curA + 1) * (bucket.map capFactor).prod := by ring
  have hsum_B : (st.curA + 1) * (bucket.map capFactor).prod ≤ B :=
    (Nat.mul_le_mul_right _ (by omega : st.curA + 1 ≤ d.dom)).trans hcapB
  refine ⟨?_, ?_⟩
  · exact ⟨⟨hdom, by omega, h1, hout, bucket, B, maxScope, hblen, hbf, hmax, hdomPow,
      hprod_le_B, hB⟩, hcurA_fit, hB.of_le (hsum_next.trans hsum_B)⟩
  · rw [sumDomainStep_state, sumDomainStep_result]
    exact ⟨rfl, by dsimp only; omega, hsum_next⟩

private structure BuildOutArgs where
  dom : ℕ
  x : ℕ
  outPtr : ℕ
  outLen : ℕ
  bucketPtr : ℕ
  bucketLen : ℕ

private def BuildOutArgs.equiv : BuildOutArgs ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((s.dom, s.x), s.outPtr), s.outLen), s.bucketPtr), s.bucketLen)
  invFun := fun (((((dom, x), outPtr), outLen), bucketPtr), bucketLen) =>
    ⟨dom, x, outPtr, outLen, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BuildOutArgs := .ofEquiv BuildOutArgs.equiv

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

private def buildOutEntries (args : BuildOutArgs) : Memory.Prog (ℕ × ℕ) :=
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
  have hr : (Memory.spec 0).clientState t (Memory.read 0) = t := rfl
  rw [StateTransitionSpec.clientState_bind, hr, StateTransitionSpec.clientState_bind,
    sumDomainValues_state, StateTransitionSpec.clientState_bind]
  rfl

private theorem buildEntryStep_result (env : BuildEntryEnv) (curIdx : ℕ) (t : Memory.State) :
    (Memory.spec 0).clientResult t (buildEntryStep (env, curIdx)) = curIdx + 1 := by
  unfold buildEntryStep
  have hr : (Memory.spec 0).clientState t (Memory.read 0) = t := rfl
  rw [StateTransitionSpec.clientResult_bind, hr, StateTransitionSpec.clientResult_bind,
    sumDomainValues_state, StateTransitionSpec.clientResult_bind]
  rfl

private theorem buildOutEntries_spec {w : ℕ} {args : BuildOutArgs} {outScope : List ℕ}
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
      have halloc_val : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (Memory.alloc 1)) := validHistory_alloc hfit1
      have htab_len : (bucketOutScope args.x bucket).length = 0 := by
        rw [← hout_eq, hout_len, ho0]
      have htab_sz : (elimBucketTable args.dom args.x bucket).entries.size = 1 := by
        simp [elimBucketTable, hd0, htab_len]
      have htab_list : (elimBucketTable args.dom args.x bucket).entries.toList = [0] := by
        apply List.ext_getElem
        · simp [htab_sz]
        · intro i hi1 hi2
          have hi0 : i = 0 := by simp at hi2; omega
          subst hi0
          simp [elimBucketTable, hd0]
      refine ⟨validHistory_bind_step halloc_val (validHistory_pure w _ _), ?_, ?_, le_rfl, ?_, ?_,
        ?_⟩
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
      have halloc_val : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (Memory.alloc 0)) := validHistory_alloc hfit0
      have htab_len : (bucketOutScope args.x bucket).length ≠ 0 := by
        rw [← hout_eq, hout_len]; exact ho0
      have htab_sz : (elimBucketTable args.dom args.x bucket).entries.size = 0 := by
        simp [elimBucketTable, hd0, Nat.zero_pow (Nat.pos_of_ne_zero htab_len)]
      have htab_list : (elimBucketTable args.dom args.x bucket).entries.toList = [] :=
        Array.toList_eq_nil_iff.mpr (Array.size_eq_zero_iff.mp htab_sz)
      refine ⟨validHistory_bind_step halloc_val (validHistory_pure w _ _), ?_, ?_, le_rfl, ?_, ?_,
        ?_⟩
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
    have hpow_val : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (powProg ⟨args.dom, args.outLen⟩)) :=
      powProg_valid _ hs0
    have hpow_res : (Memory.spec 0).clientResult s (powProg ⟨args.dom, args.outLen⟩) =
        numEntries := powProg_result _ s
    have hpow_st : (Memory.spec 0).clientState s (powProg ⟨args.dom, args.outLen⟩) = s :=
      powProg_state _ s
    let s₀ : Memory.State := ⟨s.mem, s.frontier + numEntries⟩
    have hwf₀ : Memory.WellFormed w s₀ := hwf.step (o := .allocDirty numEntries) hfit_fr'
    have halloc_val : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (Memory.allocDirty numEntries)) :=
      validHistory_allocDirty hfit_fr'
    let env : BuildEntryEnv :=
      ⟨args.dom, args.x, args.outPtr, args.outLen, args.bucketPtr, args.bucketLen, s.frontier⟩
    let entryFn : ℕ → ℕ := fun idx =>
      ∑ a : Fin args.dom,
        (bucket.map fun f => f.evalAt args.dom fun v =>
          if v = args.x then a.1
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
          refine validHistory_read_bind hs0_t ?_
          refine validHistory_bind_step hsd_val ?_
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
        have hpres₁ : PreservesBelow s.frontier s t₁ := by
          refine ⟨le_rfl, by omega, fun a ha => ?_⟩
          have hne : a ≠ s.frontier + curIdx := by omega
          change Function.update t.mem (s.frontier + curIdx) (entryFn curIdx) a = s.mem a
          rw [Function.update_of_ne hne]
          exact hpres.2.2 a ha
        have hlist₁ :
            Block.HoldsList s.frontier ((List.range (curIdx + 1)).map entryFn) t₁.mem := by
          rw [List.range_succ, List.map_append, List.map_singleton]
          have hlen_r : ((List.range curIdx).map entryFn).length = curIdx := by simp
          simpa [t₁, hlen_r] using hlist.append_one (entryFn curIdx)
        have hstep_cost : memoryCost (buildEntryStep (env, curIdx)) t ≤
            3 + args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1))) := by
          unfold buildEntryStep
          dsimp only [env]
          have hr : (Memory.spec 0).clientState t (Memory.read 0) = t := rfl
          rw [memoryCost_bind', memoryCost_read, hr, memoryCost_bind', sumDomainValues_state,
            memoryCost_bind', memoryCost_write, memoryCost_pure]
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
        rw [memoryCost_bind', hstep_st, buildEntryStep_result]
        calc memoryCost (buildEntryStep (env, curIdx)) t + _
            ≤ (3 + args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1)))) +
                rem * (3 + args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1)))) :=
              Nat.add_le_add hstep_cost hcost_r
          _ = (rem + 1) *
                (3 + args.dom * (1 + args.bucketLen * (5 + maxScope * (args.outLen + 1)))) := by
              ring
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
    refine ⟨validHistory_bind_step hpow_val ?_, hpres_l, ?_, le_rfl, htab_sz.symm, ?_, ?_⟩
    · rw [hpow_st, hpow_res]
      refine validHistory_bind_step halloc_val ?_
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

private theorem buildOutEntries_realizes :
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

/-! ### Descriptor writer (`writeDesc`), live partitioning (`partitionLive`), and `buildOutScope` -/

private theorem HoldsFactor.frame_outside {descAddr : ℕ} {f : FactorTable ℕ ℕ} {F : ℕ}
    {s₀ s₁ : Memory.State} (hf : HoldsFactor descAddr f s₀)
    (hsF : s₀.mem descAddr + f.scope.length ≤ F)
    (heF : s₀.mem (descAddr + 2) + f.entries.size ≤ F)
    (hpres : PreservesBelow F s₀ s₁)
    (hdesc : ∀ a, descAddr ≤ a → a < descAddr + 4 → s₁.mem a = s₀.mem a) :
    HoldsFactor descAddr f s₁ := by
  obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
  unfold HoldsFactor
  rw [hdesc descAddr le_rfl (by omega), hdesc (descAddr + 1) (by omega) (by omega),
    hdesc (descAddr + 2) (by omega) (by omega), hdesc (descAddr + 3) (by omega) (by omega)]
  exact ⟨hd.trans hpres.2.1, hsl, hel, hsc.mono hsF hpres,
    hent.mono (by simpa [Array.length_toList] using heF) hpres⟩

private def AllDataBelow (F : ℕ) : ℕ → List (FactorTable ℕ ℕ) → Memory.State → Prop
  | _, [], _ => True
  | base, f :: fs, s =>
    s.mem base + f.scope.length ≤ F ∧
    s.mem (base + 2) + f.entries.size ≤ F ∧
    AllDataBelow F (base + 4) fs s

private theorem AllDataBelow.of_holdsFactorList {base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (h : HoldsFactorList base fs s) :
    AllDataBelow s.frontier base fs s := by
  induction fs generalizing base with
  | nil => trivial
  | cons f rest ih =>
    exact ⟨h.1.2.2.2.1.1, by simpa [Array.length_toList] using h.1.2.2.2.2.1, ih h.2⟩

private theorem AllDataBelow.mono_bound {F₁ F₂ base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} (h : AllDataBelow F₁ base fs s) (hle : F₁ ≤ F₂) :
    AllDataBelow F₂ base fs s := by
  induction fs generalizing base with
  | nil => trivial
  | cons f rest ih => exact ⟨h.1.trans hle, h.2.1.trans hle, ih h.2.2⟩

private theorem AllDataBelow.frame {F base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s₀ s₁ : Memory.State} (h : AllDataBelow F base fs s₀)
    (hdesc : ∀ a, base ≤ a → a < base + 4 * fs.length → s₁.mem a = s₀.mem a) :
    AllDataBelow F base fs s₁ := by
  induction fs generalizing base with
  | nil => trivial
  | cons f rest ih =>
    simp only [List.length_cons] at hdesc
    refine ⟨?_, ?_, ih h.2.2 fun a hlo hhi => hdesc a (by omega) (by omega)⟩
    · rw [hdesc base le_rfl (by omega)]; exact h.1
    · rw [hdesc (base + 2) (by omega) (by omega)]; exact h.2.1

private theorem HoldsFactorList.frame_outside {F base : ℕ} {fs : List (FactorTable ℕ ℕ)}
    {s₀ s₁ : Memory.State} (h : HoldsFactorList base fs s₀)
    (hdata : AllDataBelow F base fs s₀) (hpres : PreservesBelow F s₀ s₁)
    (hdesc : ∀ a, base ≤ a → a < base + 4 * fs.length → s₁.mem a = s₀.mem a) :
    HoldsFactorList base fs s₁ := by
  induction fs generalizing base with
  | nil => exact h.trans hpres.2.1
  | cons f rest ih =>
    simp only [List.length_cons] at hdesc
    exact ⟨h.1.frame_outside hdata.1 hdata.2.1 hpres
        (fun a hlo hhi => hdesc a hlo (by omega)),
      ih h.2 hdata.2.2 fun a hlo hhi => hdesc a (by omega) (by omega)⟩

private theorem holdsFactorList_append {base : ℕ} {fs gs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} :
    HoldsFactorList base (fs ++ gs) s ↔
      HoldsFactorList base fs s ∧ HoldsFactorList (base + 4 * fs.length) gs s := by
  induction fs generalizing base with
  | nil =>
    simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨fun h => ⟨(Nat.le_add_right _ _).trans h.bound, h⟩, fun h => h.2⟩
  | cons f rest ih =>
    simp only [List.cons_append, HoldsFactorList, List.length_cons]
    have heq : base + 4 + 4 * rest.length = base + 4 * (rest.length + 1) := by ring
    rw [ih, heq]
    exact and_assoc.symm

private theorem allDataBelow_append {F base : ℕ} {fs gs : List (FactorTable ℕ ℕ)}
    {s : Memory.State} :
    AllDataBelow F base (fs ++ gs) s ↔
      AllDataBelow F base fs s ∧ AllDataBelow F (base + 4 * fs.length) gs s := by
  induction fs generalizing base with
  | nil => simp [AllDataBelow]
  | cons f rest ih =>
    simp only [List.cons_append, AllDataBelow, List.length_cons]
    have heq : base + 4 + 4 * rest.length = base + 4 * (rest.length + 1) := by ring
    rw [ih, heq]
    tauto

private structure WriteDescArgs where
  dst : ℕ
  scPtr : ℕ
  scLen : ℕ
  enPtr : ℕ
  enLen : ℕ

private def WriteDescArgs.equiv : WriteDescArgs ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((s.dst, s.scPtr), s.scLen), s.enPtr), s.enLen)
  invFun := fun ((((dst, scPtr), scLen), enPtr), enLen) => ⟨dst, scPtr, scLen, enPtr, enLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding WriteDescArgs := .ofEquiv WriteDescArgs.equiv

private def writeDesc (args : WriteDescArgs) : Memory.Prog Unit :=
  Memory.write args.dst args.scPtr >>= fun _ =>
  Memory.write (args.dst + 1) args.scLen >>= fun _ =>
  Memory.write (args.dst + 2) args.enPtr >>= fun _ =>
  Memory.write (args.dst + 3) args.enLen

private theorem writeDesc_cost (args : WriteDescArgs) (s : Memory.State) :
    memoryCost (writeDesc args) s = 4 := rfl

private theorem writeDesc_valid {w : ℕ} (args : WriteDescArgs) {s : Memory.State}
    (hdst : args.dst + 4 ≤ s.frontier)
    (hf0 : Fits w args.scPtr) (hf1 : Fits w args.scLen)
    (hf2 : Fits w args.enPtr) (hf3 : Fits w args.enLen) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeDesc args)) := by
  unfold writeDesc
  refine validHistory_write_bind (by omega) hf0 ?_
  refine validHistory_write_bind (by dsimp only; omega) hf1 ?_
  refine validHistory_write_bind (by dsimp only; omega) hf2 ?_
  exact validHistory_write (by dsimp only; omega) hf3

private theorem writeDesc_spec {w : ℕ} (args : WriteDescArgs) {f : FactorTable ℕ ℕ} {F : ℕ}
    {s : Memory.State} (hwf : Memory.WellFormed w s)
    (hFdst : F ≤ args.dst) (hdst : args.dst + 4 ≤ s.frontier)
    (hscF : args.scPtr + f.scope.length ≤ F)
    (henF : args.enPtr + f.entries.size ≤ F)
    (hsc_len : args.scLen = f.scope.length) (hen_len : args.enLen = f.entries.size)
    (hsc : HoldsIn args.scPtr f.scope s) (hen : HoldsIn args.enPtr f.entries.toList s) :
    let s' := (Memory.spec 0).clientState s (writeDesc args)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (writeDesc args)) ∧
      s'.frontier = s.frontier ∧
      Memory.WellFormed w s' ∧
      PreservesBelow F s s' ∧
      (∀ a, a < args.dst ∨ args.dst + 4 ≤ a → s'.mem a = s.mem a) ∧
      HoldsFactor args.dst f s' ∧
      s'.mem args.dst = args.scPtr ∧
      s'.mem (args.dst + 2) = args.enPtr := by
  dsimp only
  have hv := writeDesc_valid args hdst
    (hwf.frontier_fits.of_le (by omega))
    (hwf.frontier_fits.of_le (by omega))
    (hwf.frontier_fits.of_le (by omega))
    (hwf.frontier_fits.of_le (by omega))
  have hwf' : Memory.WellFormed w ((Memory.spec 0).clientState s (writeDesc args)) :=
    wellFormed_clientState hwf hv
  have hst : (Memory.spec 0).clientState s (writeDesc args) =
      ⟨Function.update (Function.update (Function.update (Function.update s.mem
        args.dst args.scPtr) (args.dst + 1) args.scLen) (args.dst + 2) args.enPtr)
        (args.dst + 3) args.enLen, s.frontier⟩ := rfl
  have hout : ∀ a, a < args.dst ∨ args.dst + 4 ≤ a →
      ((Memory.spec 0).clientState s (writeDesc args)).mem a = s.mem a := by
    intro a ha
    rw [hst]
    dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hpres : PreservesBelow F s ((Memory.spec 0).clientState s (writeDesc args)) :=
    ⟨by omega, by rw [hst], fun a ha => hout a (Or.inl (lt_of_lt_of_le ha hFdst))⟩
  have hm0 : ((Memory.spec 0).clientState s (writeDesc args)).mem args.dst = args.scPtr := by
    rw [hst]; dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_self]
  have hm1 : ((Memory.spec 0).clientState s (writeDesc args)).mem (args.dst + 1) = args.scLen := by
    rw [hst]; dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
  have hm2 : ((Memory.spec 0).clientState s (writeDesc args)).mem (args.dst + 2) = args.enPtr := by
    rw [hst]; dsimp only
    rw [Function.update_of_ne (by omega), Function.update_self]
  have hm3 : ((Memory.spec 0).clientState s (writeDesc args)).mem (args.dst + 3) = args.enLen := by
    rw [hst]; dsimp only
    rw [Function.update_self]
  refine ⟨hv, by rw [hst], hwf', hpres, hout, ?_, hm0, hm2⟩
  unfold HoldsFactor
  rw [hm0, hm1, hm2, hm3]
  exact ⟨by rw [hst]; exact hdst, hsc_len, hen_len, hsc.mono hscF hpres,
    hen.mono (by simpa [Array.length_toList] using henF) hpres⟩

private theorem writeDesc_realizes :
    Realizes .exact writeDesc WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w (args.dst + 3)) (fun _ _ => 0) := by
  unfold writeDesc
  realize
  · exact h.of_le (by omega)
  · exact h.of_le (by omega)
  · exact h

private structure PartitionArgs where
  x : ℕ
  livePtr : ℕ
  liveLen : ℕ

private def PartitionArgs.equiv : PartitionArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.x, s.livePtr), s.liveLen)
  invFun := fun ((x, livePtr), liveLen) => ⟨x, livePtr, liveLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding PartitionArgs := .ofEquiv PartitionArgs.equiv

private structure PartitionState where
  curDesc : ℕ
  bDst : ℕ
  bCnt : ℕ
  rDst : ℕ
  rCnt : ℕ

private def PartitionState.equiv : PartitionState ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((s.curDesc, s.bDst), s.bCnt), s.rDst), s.rCnt)
  invFun := fun ((((curDesc, bDst), bCnt), rDst), rCnt) => ⟨curDesc, bDst, bCnt, rDst, rCnt⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding PartitionState := .ofEquiv PartitionState.equiv

private structure PartitionRes where
  bucketPtr : ℕ
  bucketLen : ℕ
  newLiveBuf : ℕ
  restLen : ℕ

private def PartitionRes.equiv : PartitionRes ≃ ((ℕ × ℕ) × ℕ) × ℕ where
  toFun s := (((s.bucketPtr, s.bucketLen), s.newLiveBuf), s.restLen)
  invFun := fun (((bucketPtr, bucketLen), newLiveBuf), restLen) =>
    ⟨bucketPtr, bucketLen, newLiveBuf, restLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding PartitionRes := .ofEquiv PartitionRes.equiv

private def partitionStep (p : ℕ × PartitionState) : Memory.Prog PartitionState :=
  Memory.read p.2.curDesc >>= fun scPtr =>
  Memory.read (p.2.curDesc + 1) >>= fun scLen =>
  Memory.read (p.2.curDesc + 2) >>= fun enPtr =>
  Memory.read (p.2.curDesc + 3) >>= fun enLen =>
  memScan ⟨p.1, scPtr, scLen⟩ >>= fun flag =>
  if flag = 1 then
    writeDesc ⟨p.2.bDst, scPtr, scLen, enPtr, enLen⟩ >>= fun _ =>
      pure ⟨p.2.curDesc + 4, p.2.bDst + 4, p.2.bCnt + 1, p.2.rDst, p.2.rCnt⟩
  else
    writeDesc ⟨p.2.rDst, scPtr, scLen, enPtr, enLen⟩ >>= fun _ =>
      pure ⟨p.2.curDesc + 4, p.2.bDst, p.2.bCnt, p.2.rDst + 4, p.2.rCnt + 1⟩

private def partitionLive (args : PartitionArgs) : Memory.Prog PartitionRes :=
  Memory.allocDirty (4 * args.liveLen) >>= fun bucketPtr =>
  Memory.allocDirty (4 + 4 * args.liveLen) >>= fun newLiveBuf =>
  iterate partitionStep args.x args.liveLen
    ⟨args.livePtr, bucketPtr, 0, newLiveBuf + 4, 0⟩ >>= fun res =>
  pure ⟨bucketPtr, res.bCnt, newLiveBuf, res.rCnt⟩

private theorem partitionLive_spec {w : ℕ} {args : PartitionArgs}
    {live : List (FactorTable ℕ ℕ)} {maxScope : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hlive : HoldsFactorList args.livePtr live s) (hlen : live.length = args.liveLen)
    (hmax : ∀ f ∈ live, f.scope.length ≤ maxScope)
    (hfit : Fits w (s.frontier + 4 + 8 * args.liveLen)) :
    let res := (Memory.spec 0).clientResult s (partitionLive args)
    let s' := (Memory.spec 0).clientState s (partitionLive args)
    let bucket := live.filter fun f => decide (args.x ∈ f.scope)
    let rest := live.filter fun f => decide (args.x ∉ f.scope)
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (partitionLive args)) ∧
      s'.frontier = s.frontier + 4 + 8 * args.liveLen ∧
      PreservesBelow s.frontier s s' ∧
      res.bucketPtr = s.frontier ∧
      res.newLiveBuf = s.frontier + 4 * args.liveLen ∧
      res.bucketLen = bucket.length ∧
      res.restLen = rest.length ∧
      HoldsFactorList res.bucketPtr bucket s' ∧
      AllDataBelow s.frontier res.bucketPtr bucket s' ∧
      HoldsFactorList (res.newLiveBuf + 4) rest s' ∧
      AllDataBelow s.frontier (res.newLiveBuf + 4) rest s' ∧
      memoryCost (partitionLive args) s ≤ 2 + args.liveLen * (8 + maxScope) := by
  dsimp only
  unfold partitionLive
  let bBase := s.frontier
  let rBuf := s.frontier + 4 * args.liveLen
  have hfit1 : Fits w (s.frontier + 4 * args.liveLen) := hfit.of_le (by omega)
  have hfit2 : Fits w ((s.frontier + 4 * args.liveLen) + (4 + 4 * args.liveLen)) :=
    hfit.of_le (by omega)
  have hv_a1 : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty (4 * args.liveLen))) :=
    validHistory_allocDirty hfit1
  let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * args.liveLen⟩
  have hwf₁ : Memory.WellFormed w s₁ := hwf.step (o := .allocDirty _) hfit1
  have hv_a2 : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (Memory.allocDirty (4 + 4 * args.liveLen))) :=
    validHistory_allocDirty hfit2
  let s₂ : Memory.State := ⟨s.mem, (s.frontier + 4 * args.liveLen) + (4 + 4 * args.liveLen)⟩
  have hwf₂ : Memory.WellFormed w s₂ := hwf₁.step (o := .allocDirty _) hfit2
  have hpres₂ : PreservesBelow s.frontier s s₂ :=
    ⟨le_rfl, by dsimp only [s₂]; omega, fun _ _ => rfl⟩
  have hlive_data : AllDataBelow s.frontier args.livePtr live s₂ :=
    (AllDataBelow.of_holdsFactorList hlive).frame fun _ _ _ => rfl
  have hlive₂ : HoldsFactorList args.livePtr live s₂ := hlive.mono_frontier hpres₂
  have hloop : ∀ (rem : List (FactorTable ℕ ℕ)) (cur : ℕ)
      (bAcc rAcc : List (FactorTable ℕ ℕ)) (t : Memory.State),
      Memory.WellFormed w t →
      t.frontier = s.frontier + 4 + 8 * args.liveLen →
      PreservesBelow s.frontier s t →
      cur + 4 * rem.length ≤ bBase →
      HoldsFactorList cur rem t →
      AllDataBelow s.frontier cur rem t →
      (∀ f ∈ rem, f.scope.length ≤ maxScope) →
      bAcc.length + rem.length ≤ args.liveLen →
      rAcc.length + rem.length ≤ args.liveLen →
      HoldsFactorList bBase bAcc t →
      AllDataBelow s.frontier bBase bAcc t →
      HoldsFactorList (rBuf + 4) rAcc t →
      AllDataBelow s.frontier (rBuf + 4) rAcc t →
      let st₀ : PartitionState :=
        ⟨cur, bBase + 4 * bAcc.length, bAcc.length, rBuf + 4 + 4 * rAcc.length, rAcc.length⟩
      let p := iterate partitionStep args.x rem.length st₀
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let bOut := bAcc ++ rem.filter fun f => decide (args.x ∈ f.scope)
      let rOut := rAcc ++ rem.filter fun f => decide (args.x ∉ f.scope)
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = s.frontier + 4 + 8 * args.liveLen ∧
        PreservesBelow s.frontier s t' ∧
        r.bCnt = bOut.length ∧
        r.rCnt = rOut.length ∧
        HoldsFactorList bBase bOut t' ∧
        AllDataBelow s.frontier bBase bOut t' ∧
        HoldsFactorList (rBuf + 4) rOut t' ∧
        AllDataBelow s.frontier (rBuf + 4) rOut t' ∧
        memoryCost p t ≤ rem.length * (8 + maxScope) := by
    intro rem
    induction rem with
    | nil =>
      intro cur bAcc rAcc t _ hfr hpres _ _ _ _ _ _ hbAcc hbData hrAcc hrData
      simp only [List.length_nil, List.filter_nil, List.append_nil, Nat.zero_mul]
      exact ⟨validHistory_pure w t _, hfr, hpres, rfl, rfl, hbAcc, hbData, hrAcc, hrData,
        by simp [iterate]⟩
    | cons f rest ih =>
      intro cur bAcc rAcc t hwf_t hfr hpres hcur_b ⟨hf, hrest⟩ ⟨hf_scF, hf_enF, hrest_data⟩
        hmax_rem hb_room hr_room hbAcc hbData hrAcc hrData
      simp only [List.length_cons] at hcur_b hb_room hr_room
      obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
      have hf_max : f.scope.length ≤ maxScope := hmax_rem f (List.mem_cons_self ..)
      have hrest_max : ∀ g ∈ rest, g.scope.length ≤ maxScope :=
        fun g hg => hmax_rem g (List.mem_cons_of_mem f hg)
      let st₀ : PartitionState :=
        ⟨cur, bBase + 4 * bAcc.length, bAcc.length, rBuf + 4 + 4 * rAcc.length, rAcc.length⟩
      let msArgs : MemScanArgs := ⟨args.x, t.mem cur, t.mem (cur + 1)⟩
      have hms_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (memScan msArgs)) :=
        memScan_valid msArgs (by dsimp only [msArgs]; rw [hsl]; exact hsc.1)
      have hms_res : (Memory.spec 0).clientResult t (memScan msArgs) =
          if args.x ∈ f.scope then 1 else 0 := memScan_result hsc.2 hsl.symm
      have hms_cost : memoryCost (memScan msArgs) t ≤ maxScope := by
        refine (memScan_cost msArgs t).trans ?_
        dsimp only [msArgs]
        rw [hsl]
        exact hf_max
      have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hiter_eq : iterate partitionStep args.x (f :: rest).length st₀ =
          (partitionStep (args.x, st₀) >>= iterate partitionStep args.x rest.length) := rfl
      dsimp only
      rw [hiter_eq]
      by_cases hxf : args.x ∈ f.scope
      · have hflag1 : ((Memory.spec 0).clientResult t (memScan msArgs) = 1) := by
          rw [hms_res, ite_eq_left hxf]
        let wdArgs : WriteDescArgs :=
          ⟨bBase + 4 * bAcc.length, t.mem cur, t.mem (cur + 1), t.mem (cur + 2), t.mem (cur + 3)⟩
        obtain ⟨hwd_val, hwd_fr, hwf₁, hwd_pres, hwd_out, hf_new, hm0, hm2⟩ :=
          writeDesc_spec (w := w) wdArgs hwf_t
            (F := s.frontier) (by dsimp only [wdArgs, bBase]; omega)
            (by dsimp only [wdArgs, bBase]; omega)
            hf_scF hf_enF hsl hel hsc hent
        let t₁ := (Memory.spec 0).clientState t (writeDesc wdArgs)
        have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (partitionStep (args.x, st₀))) := by
          unfold partitionStep
          dsimp only [st₀]
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, ite_eq_left hflag1]
          exact validHistory_bind_step hwd_val (validHistory_pure w _ _)
        have hstep_st : (Memory.spec 0).clientState t (partitionStep (args.x, st₀)) = t₁ := by
          unfold partitionStep
          dsimp only [st₀]
          rw [StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, memScan_state, ite_eq_left hflag1,
            StateTransitionSpec.clientState_bind]
          rfl
        have hstep_res : (Memory.spec 0).clientResult t (partitionStep (args.x, st₀)) =
            ⟨cur + 4, bBase + 4 * (bAcc.length + 1), bAcc.length + 1,
              rBuf + 4 + 4 * rAcc.length, rAcc.length⟩ := by
          unfold partitionStep
          dsimp only [st₀]
          rw [StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, memScan_state, ite_eq_left hflag1,
            StateTransitionSpec.clientResult_bind]
          change (⟨cur + 4, bBase + 4 * bAcc.length + 4, bAcc.length + 1,
            rBuf + 4 + 4 * rAcc.length, rAcc.length⟩ : PartitionState) = _
          have heq : bBase + 4 * bAcc.length + 4 = bBase + 4 * (bAcc.length + 1) := by ring
          rw [heq]
        have hstep_cost : memoryCost (partitionStep (args.x, st₀)) t ≤ 8 + maxScope := by
          unfold partitionStep
          dsimp only [st₀]
          rw [memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memScan_state, ite_eq_left hflag1,
            memoryCost_bind', writeDesc_cost, memoryCost_pure]
          change 1 + (1 + (1 + (1 + (memoryCost (memScan msArgs) t + (4 + 0))))) ≤ 8 + maxScope
          omega
        have hpres₁ : PreservesBelow s.frontier s t₁ := hpres.trans hwd_pres
        have hrest₁ : HoldsFactorList (cur + 4) rest t₁ :=
          hrest.frame_outside hrest_data hwd_pres fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase]; omega))
        have hrest_data₁ : AllDataBelow s.frontier (cur + 4) rest t₁ :=
          hrest_data.frame fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase]; omega))
        have hbAcc₁ : HoldsFactorList bBase (bAcc ++ [f]) t₁ := by
          refine holdsFactorList_append.mpr ⟨?_, hf_new, ?_⟩
          · exact hbAcc.frame_outside hbData hwd_pres fun a hlo hhi =>
              hwd_out a (Or.inl (by dsimp only [wdArgs]; omega))
          · unfold HoldsFactorList
            have ht₁_fr : t₁.frontier = t.frontier := hwd_fr
            rw [ht₁_fr, hfr]
            dsimp only [bBase]
            omega
        have hbData₁ : AllDataBelow s.frontier bBase (bAcc ++ [f]) t₁ := by
          refine allDataBelow_append.mpr ⟨?_, ?_⟩
          · exact hbData.frame fun a hlo hhi => hwd_out a (Or.inl (by dsimp only [wdArgs]; omega))
          · refine ⟨?_, ?_, trivial⟩
            · change t₁.mem wdArgs.dst + f.scope.length ≤ s.frontier
              rw [hm0]; exact hf_scF
            · change t₁.mem (wdArgs.dst + 2) + f.entries.size ≤ s.frontier
              rw [hm2]; exact hf_enF
        have hrAcc₁ : HoldsFactorList (rBuf + 4) rAcc t₁ :=
          hrAcc.frame_outside hrData hwd_pres fun a hlo hhi =>
            hwd_out a (Or.inr (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hrData₁ : AllDataBelow s.frontier (rBuf + 4) rAcc t₁ :=
          hrData.frame fun a hlo hhi =>
            hwd_out a (Or.inr (by dsimp only [wdArgs, bBase, rBuf]; omega))
        obtain ⟨hv_i, hfr_i, hpres_i, hbCnt_i, hrCnt_i, hbH_i, hbD_i, hrH_i, hrD_i, hcost_i⟩ :=
          ih (cur + 4) (bAcc ++ [f]) rAcc t₁ hwf₁ (hwd_fr.trans hfr) hpres₁ (by omega)
            hrest₁ hrest_data₁ hrest_max (by simp; omega) (by omega)
            hbAcc₁ hbData₁ hrAcc₁ hrData₁
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_res, memoryCost_bind', hstep_st, hstep_res]
        have hbOut_eq : bAcc ++ (f :: rest).filter (fun g => decide (args.x ∈ g.scope)) =
            (bAcc ++ [f]) ++ rest.filter (fun g => decide (args.x ∈ g.scope)) := by
          simp [decide_eq_true hxf, List.append_assoc]
        have hrOut_eq : rAcc ++ (f :: rest).filter (fun g => decide (args.x ∉ g.scope)) =
            rAcc ++ rest.filter (fun g => decide (args.x ∉ g.scope)) := by
          simp [hxf]
        rw [hbOut_eq, hrOut_eq]
        refine ⟨validHistory_bind_step hstep_val
          (by simpa [hstep_st, hstep_res, List.length_append] using hv_i),
          by simpa [List.length_append] using hfr_i,
          by simpa [List.length_append] using hpres_i,
          by simpa [List.length_append] using hbCnt_i,
          by simpa [List.length_append] using hrCnt_i,
          by simpa [List.length_append] using hbH_i,
          by simpa [List.length_append] using hbD_i,
          by simpa [List.length_append] using hrH_i,
          by simpa [List.length_append] using hrD_i, ?_⟩
        have hcost_i' : memoryCost (iterate partitionStep args.x rest.length
            ⟨cur + 4, bBase + 4 * (bAcc.length + 1), bAcc.length + 1,
              rBuf + 4 + 4 * rAcc.length, rAcc.length⟩) t₁ ≤ rest.length * (8 + maxScope) := by
          simpa [List.length_append] using hcost_i
        calc memoryCost (partitionStep (args.x, st₀)) t + _
            ≤ (8 + maxScope) + rest.length * (8 + maxScope) := Nat.add_le_add hstep_cost hcost_i'
          _ = (f :: rest).length * (8 + maxScope) := by simp only [List.length_cons]; ring
      · have hflag0 : ¬ ((Memory.spec 0).clientResult t (memScan msArgs) = 1) := by
          rw [hms_res, ite_eq_right hxf]; decide
        let wdArgs : WriteDescArgs :=
          ⟨rBuf + 4 + 4 * rAcc.length, t.mem cur, t.mem (cur + 1), t.mem (cur + 2),
            t.mem (cur + 3)⟩
        obtain ⟨hwd_val, hwd_fr, hwf₁, hwd_pres, hwd_out, hf_new, hm0, hm2⟩ :=
          writeDesc_spec (w := w) wdArgs hwf_t
            (F := s.frontier) (by dsimp only [wdArgs, rBuf]; omega)
            (by dsimp only [wdArgs, rBuf]; omega)
            hf_scF hf_enF hsl hel hsc hent
        let t₁ := (Memory.spec 0).clientState t (writeDesc wdArgs)
        have hstep_val : (Memory.spec w).ValidHistory t
            ((Memory.spec w).clientHistory t (partitionStep (args.x, st₀))) := by
          unfold partitionStep
          dsimp only [st₀]
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_read_bind (by omega) ?_
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, ite_eq_right hflag0]
          exact validHistory_bind_step hwd_val (validHistory_pure w _ _)
        have hstep_st : (Memory.spec 0).clientState t (partitionStep (args.x, st₀)) = t₁ := by
          unfold partitionStep
          dsimp only [st₀]
          rw [StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, hr_t, hres_t,
            StateTransitionSpec.clientState_bind, memScan_state, ite_eq_right hflag0,
            StateTransitionSpec.clientState_bind]
          rfl
        have hstep_res : (Memory.spec 0).clientResult t (partitionStep (args.x, st₀)) =
            ⟨cur + 4, bBase + 4 * bAcc.length, bAcc.length,
              rBuf + 4 + 4 * (rAcc.length + 1), rAcc.length + 1⟩ := by
          unfold partitionStep
          dsimp only [st₀]
          rw [StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, hr_t, hres_t,
            StateTransitionSpec.clientResult_bind, memScan_state, ite_eq_right hflag0,
            StateTransitionSpec.clientResult_bind]
          change (⟨cur + 4, bBase + 4 * bAcc.length, bAcc.length,
            rBuf + 4 + 4 * rAcc.length + 4, rAcc.length + 1⟩ : PartitionState) = _
          have heq : rBuf + 4 + 4 * rAcc.length + 4 = rBuf + 4 + 4 * (rAcc.length + 1) := by ring
          rw [heq]
        have hstep_cost : memoryCost (partitionStep (args.x, st₀)) t ≤ 8 + maxScope := by
          unfold partitionStep
          dsimp only [st₀]
          rw [memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memoryCost_read, hr_t, hres_t,
            memoryCost_bind', memScan_state, ite_eq_right hflag0,
            memoryCost_bind', writeDesc_cost, memoryCost_pure]
          change 1 + (1 + (1 + (1 + (memoryCost (memScan msArgs) t + (4 + 0))))) ≤ 8 + maxScope
          omega
        have hpres₁ : PreservesBelow s.frontier s t₁ := hpres.trans hwd_pres
        have hrest₁ : HoldsFactorList (cur + 4) rest t₁ :=
          hrest.frame_outside hrest_data hwd_pres fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hrest_data₁ : AllDataBelow s.frontier (cur + 4) rest t₁ :=
          hrest_data.frame fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hbAcc₁ : HoldsFactorList bBase bAcc t₁ :=
          hbAcc.frame_outside hbData hwd_pres fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hbData₁ : AllDataBelow s.frontier bBase bAcc t₁ :=
          hbData.frame fun a hlo hhi =>
            hwd_out a (Or.inl (by dsimp only [wdArgs, bBase, rBuf]; omega))
        have hrAcc₁ : HoldsFactorList (rBuf + 4) (rAcc ++ [f]) t₁ := by
          refine holdsFactorList_append.mpr ⟨?_, hf_new, ?_⟩
          · exact hrAcc.frame_outside hrData hwd_pres fun a hlo hhi =>
              hwd_out a (Or.inl (by dsimp only [wdArgs]; omega))
          · unfold HoldsFactorList
            have ht₁_fr : t₁.frontier = t.frontier := hwd_fr
            rw [ht₁_fr, hfr]
            dsimp only [rBuf]
            omega
        have hrData₁ : AllDataBelow s.frontier (rBuf + 4) (rAcc ++ [f]) t₁ := by
          refine allDataBelow_append.mpr ⟨?_, ?_⟩
          · exact hrData.frame fun a hlo hhi => hwd_out a (Or.inl (by dsimp only [wdArgs]; omega))
          · refine ⟨?_, ?_, trivial⟩
            · change t₁.mem wdArgs.dst + f.scope.length ≤ s.frontier
              rw [hm0]; exact hf_scF
            · change t₁.mem (wdArgs.dst + 2) + f.entries.size ≤ s.frontier
              rw [hm2]; exact hf_enF
        obtain ⟨hv_i, hfr_i, hpres_i, hbCnt_i, hrCnt_i, hbH_i, hbD_i, hrH_i, hrD_i, hcost_i⟩ :=
          ih (cur + 4) bAcc (rAcc ++ [f]) t₁ hwf₁ (hwd_fr.trans hfr) hpres₁ (by omega)
            hrest₁ hrest_data₁ hrest_max (by omega) (by simp; omega)
            hbAcc₁ hbData₁ hrAcc₁ hrData₁
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_res, memoryCost_bind', hstep_st, hstep_res]
        have hbOut_eq : bAcc ++ (f :: rest).filter (fun g => decide (args.x ∈ g.scope)) =
            bAcc ++ rest.filter (fun g => decide (args.x ∈ g.scope)) := by
          simp [hxf]
        have hrOut_eq : rAcc ++ (f :: rest).filter (fun g => decide (args.x ∉ g.scope)) =
            (rAcc ++ [f]) ++ rest.filter (fun g => decide (args.x ∉ g.scope)) := by
          simp [hxf, List.append_assoc]
        rw [hbOut_eq, hrOut_eq]
        refine ⟨validHistory_bind_step hstep_val
          (by simpa [hstep_st, hstep_res, List.length_append] using hv_i),
          by simpa [List.length_append] using hfr_i,
          by simpa [List.length_append] using hpres_i,
          by simpa [List.length_append] using hbCnt_i,
          by simpa [List.length_append] using hrCnt_i,
          by simpa [List.length_append] using hbH_i,
          by simpa [List.length_append] using hbD_i,
          by simpa [List.length_append] using hrH_i,
          by simpa [List.length_append] using hrD_i, ?_⟩
        have hcost_i' : memoryCost (iterate partitionStep args.x rest.length
            ⟨cur + 4, bBase + 4 * bAcc.length, bAcc.length,
              rBuf + 4 + 4 * (rAcc.length + 1), rAcc.length + 1⟩) t₁ ≤
            rest.length * (8 + maxScope) := by
          simpa [List.length_append] using hcost_i
        calc memoryCost (partitionStep (args.x, st₀)) t + _
            ≤ (8 + maxScope) + rest.length * (8 + maxScope) := Nat.add_le_add hstep_cost hcost_i'
          _ = (f :: rest).length * (8 + maxScope) := by simp only [List.length_cons]; ring
  obtain ⟨hv_l, hfr_l, hpres_l, hbCnt_l, hrCnt_l, hbH_l, hbD_l, hrH_l, hrD_l, hcost_l⟩ :=
    hloop live args.livePtr [] [] s₂ hwf₂ (by dsimp only [s₂]; omega) hpres₂
      hlive.bound hlive₂ hlive_data hmax (by simp [hlen]) (by simp [hlen])
      (by dsimp only [HoldsFactorList, s₂, bBase]; omega) trivial
      (by dsimp only [HoldsFactorList, s₂, rBuf]; omega) trivial
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hv_l hfr_l hpres_l hcost_l
  simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero] at hbCnt_l hrCnt_l
  simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero] at hbH_l hbD_l
  simp only [List.nil_append, List.length_nil, Nat.mul_zero, Nat.add_zero] at hrH_l hrD_l
  have ha1_st : (Memory.spec 0).clientState s (Memory.allocDirty (4 * args.liveLen)) = s₁ := rfl
  have ha1_res : (Memory.spec 0).clientResult s (Memory.allocDirty (4 * args.liveLen)) =
      bBase := rfl
  have ha2_st : (Memory.spec 0).clientState s₁ (Memory.allocDirty (4 + 4 * args.liveLen)) =
      s₂ := rfl
  have ha2_res : (Memory.spec 0).clientResult s₁ (Memory.allocDirty (4 + 4 * args.liveLen)) =
      rBuf := rfl
  have hpure_st {α : Type} (x : α) (t : Memory.State) :
      (Memory.spec 0).clientState t (pure x) = t := rfl
  have hpure_res {α : Type} (x : α) (t : Memory.State) :
      (Memory.spec 0).clientResult t (pure x) = x := rfl
  rw [← hlen]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
  rw [hlen]
  rw [ha1_st, ha1_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    ha2_st, ha2_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hpure_res, hpure_st]
  rw [← hlen]
  refine ⟨validHistory_bind_step (by rw [hlen]; exact hv_a1) ?_,
    by rw [hlen] at hfr_l ⊢; exact hfr_l, hpres_l, rfl, by rw [hlen],
    hbCnt_l, hrCnt_l, hbH_l, hbD_l, ?_, ?_, ?_⟩
  · rw [hlen, ha1_st, ha1_res]
    refine validHistory_bind_step hv_a2 ?_
    rw [ha2_st, ha2_res, ← hlen]
    exact validHistory_bind_step hv_l (validHistory_pure w _ _)
  · dsimp only; exact hrH_l
  · dsimp only; exact hrD_l
  · rw [memoryCost_bind', memoryCost_allocDirty]
    rw [hlen, ha1_st, ha1_res, memoryCost_bind', memoryCost_allocDirty, ha2_st, ha2_res,
      memoryCost_bind', memoryCost_pure, Nat.add_zero, ← hlen]
    omega

private theorem writeDesc_frame (args : WriteDescArgs) (t : Memory.State) :
    ((Memory.spec 0).clientState t (writeDesc args)).frontier = t.frontier ∧
    ∀ a, a < args.dst ∨ args.dst + 4 ≤ a →
      ((Memory.spec 0).clientState t (writeDesc args)).mem a = t.mem a := by
  have hst : (Memory.spec 0).clientState t (writeDesc args) =
      ⟨Function.update (Function.update (Function.update (Function.update t.mem
        args.dst args.scPtr) (args.dst + 1) args.scLen) (args.dst + 2) args.enPtr)
        (args.dst + 3) args.enLen, t.frontier⟩ := rfl
  refine ⟨by rw [hst], fun a ha => ?_⟩
  rw [hst]
  dsimp only
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private theorem partitionLive_realizes :
    Realizes .exact partitionLive WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧ Fits w (s.frontier + 4 + 8 * args.liveLen) ∧
        ∃ live, live.length = args.liveLen ∧ HoldsFactorList args.livePtr live s)
      (fun _ _ => 0) := by
  unfold partitionLive
  realize [memScan_realizes, writeDesc_realizes]
  · exact h.2.1.of_le (by omega)
  · exact h.2.1.of_le (by omega)
  · exact h.2.1.of_le (by omega)
  · exact h.2.1.of_le (by omega)
  · obtain ⟨h1, hfit, live, hlen, hlive⟩ := h
    let bBase := s.frontier
    let rBuf := s.frontier + 4 * d.liveLen
    have hlive_b : d.livePtr + 4 * d.liveLen ≤ s.frontier := by rw [← hlen]; exact hlive.bound
    let stInit : PartitionState :=
      ⟨d.livePtr, s.frontier, 0, s.frontier + 4 * d.liveLen + 4, 0⟩
    let sInit : Memory.State := ⟨s.mem, s.frontier + 4 * d.liveLen + (4 + 4 * d.liveLen)⟩
    have hinit : sInit.frontier = s.frontier + 4 * d.liveLen + (4 + 4 * d.liveLen) ∧
        PreservesBelow s.frontier s sInit ∧
        bBase ≤ stInit.bDst ∧ rBuf + 4 ≤ stInit.rDst ∧
        stInit.curDesc + 4 * d.liveLen ≤ s.frontier ∧
        stInit.bDst + 4 * d.liveLen ≤ rBuf ∧
        stInit.bCnt + d.liveLen ≤ d.liveLen ∧
        stInit.rDst + 4 * d.liveLen ≤ s.frontier + 4 + 8 * d.liveLen ∧
        stInit.rCnt + d.liveLen ≤ d.liveLen ∧
        ∃ rem, rem.length = d.liveLen ∧ HoldsFactorList stInit.curDesc rem s :=
      ⟨rfl, ⟨le_rfl, by dsimp only [sInit]; omega, fun _ _ => rfl⟩,
        le_rfl, le_rfl, hlive_b, le_rfl, Nat.zero_add _ |>.le,
        by dsimp only [stInit, rBuf]; omega, Nat.zero_add _ |>.le, live, hlen, hlive⟩
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : PartitionState) (t : Memory.State) =>
        t.frontier = s.frontier + 4 * d.liveLen + (4 + 4 * d.liveLen) ∧
        PreservesBelow s.frontier s t ∧
        bBase ≤ st.bDst ∧
        rBuf + 4 ≤ st.rDst ∧
        st.curDesc + 4 * j ≤ s.frontier ∧
        st.bDst + 4 * j ≤ rBuf ∧
        st.bCnt + j ≤ d.liveLen ∧
        st.rDst + 4 * j ≤ s.frontier + 4 + 8 * d.liveLen ∧
        st.rCnt + j ≤ d.liveLen ∧
        ∃ rem, rem.length = j ∧ HoldsFactorList st.curDesc rem s)
      (fun j st t ⟨hfr, hpres, hb_lo, hr_lo, hcur_b, hb_b, hb_c, hr_b, hr_c, rem, hrem_l,
        hrem_h⟩ => ?_)
      hinit
    dsimp only
    rcases rem with _ | ⟨f, rest⟩
    · cases hrem_l
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
    obtain ⟨hf, hrest⟩ := hrem_h
    obtain ⟨hd, hsl, hel, hsc, hent⟩ := hf
    have hm0 : t.mem st.curDesc = s.mem st.curDesc := hpres.2.2 _ (by omega)
    have hm1 : t.mem (st.curDesc + 1) = s.mem (st.curDesc + 1) := hpres.2.2 _ (by omega)
    have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
    have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
    refine ⟨?_, ?_⟩
    · refine ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
        ⟨h1, hfit.of_le (by rw [hm0, hm1, hsl]; have := hsc.1; omega)⟩, h1, ?_⟩
      split_ifs
      · exact ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
          hfit.of_le (by omega)⟩
      · exact ⟨hfit.of_le (by omega), hfit.of_le (by omega), hfit.of_le (by omega),
          hfit.of_le (by omega)⟩
    · unfold partitionStep
      dsimp only
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, hr_t, hres_t,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind, memScan_state]
      split_ifs
      · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
        obtain ⟨hwf_fr, hwf_mem⟩ := writeDesc_frame
          ⟨st.bDst, t.mem st.curDesc, t.mem (st.curDesc + 1), t.mem (st.curDesc + 2),
            t.mem (st.curDesc + 3)⟩ t
        have hpure_st {α : Type} (x : α) (u : Memory.State) :
            (Memory.spec 0).clientState u (pure x) = u := rfl
        have hpure_res {α : Type} (x : α) (u : Memory.State) :
            (Memory.spec 0).clientResult u (pure x) = x := rfl
        rw [hpure_st, hpure_res]
        dsimp only
        refine ⟨hwf_fr.trans hfr, ?_, by omega, hr_lo, by omega, by omega, by omega, by omega,
          by omega, rest, hrem_l, hrest⟩
        exact ⟨le_rfl, by rw [hwf_fr]; exact hpres.2.1, fun a ha =>
          (hwf_mem a (Or.inl (by dsimp only; omega))).trans (hpres.2.2 a ha)⟩
      · rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind]
        obtain ⟨hwf_fr, hwf_mem⟩ := writeDesc_frame
          ⟨st.rDst, t.mem st.curDesc, t.mem (st.curDesc + 1), t.mem (st.curDesc + 2),
            t.mem (st.curDesc + 3)⟩ t
        have hpure_st {α : Type} (x : α) (u : Memory.State) :
            (Memory.spec 0).clientState u (pure x) = u := rfl
        have hpure_res {α : Type} (x : α) (u : Memory.State) :
            (Memory.spec 0).clientResult u (pure x) = x := rfl
        rw [hpure_st, hpure_res]
        dsimp only
        refine ⟨hwf_fr.trans hfr, ?_, hb_lo, by omega, by omega, by omega, by omega, by omega,
          by omega, rest, hrem_l, hrest⟩
        exact ⟨le_rfl, by rw [hwf_fr]; exact hpres.2.1, fun a ha =>
          (hwf_mem a (Or.inl (by dsimp only; omega))).trans (hpres.2.2 a ha)⟩

/-! ### Output scope materialization (`buildOutScope`) -/

private def dedupStepPure (x v : ℕ) (acc : List ℕ) : List ℕ :=
  if v = x ∨ v ∈ acc then acc else v :: acc

private theorem length_le_foldr_dedupStepPure (x : ℕ) :
    ∀ (ys acc : List ℕ), acc.length ≤ (ys.foldr (dedupStepPure x) acc).length
  | [], acc => le_rfl
  | v :: rest, acc => by
    simp only [List.foldr_cons]
    refine (length_le_foldr_dedupStepPure x rest acc).trans ?_
    unfold dedupStepPure
    split_ifs <;> simp

private theorem mem_foldr_dedupStepPure (x : ℕ) :
    ∀ (ys : List ℕ) (u : ℕ), u ∈ ys.foldr (dedupStepPure x) [] ↔ u ≠ x ∧ u ∈ ys
  | [], u => by simp
  | v :: rest, u => by
    simp only [List.foldr_cons, dedupStepPure]
    have ih := mem_foldr_dedupStepPure x rest u
    have ihv := mem_foldr_dedupStepPure x rest v
    split_ifs with hcond
    · rcases hcond with rfl | hmem
      · simp only [ih, List.mem_cons]
        exact ⟨fun ⟨hne, hr⟩ => ⟨hne, Or.inr hr⟩,
          fun ⟨hne, h⟩ => ⟨hne, h.resolve_left hne⟩⟩
      · have hv_in : v ≠ x ∧ v ∈ rest := ihv.mp hmem
        simp only [ih, List.mem_cons]
        exact ⟨fun ⟨hne, hr⟩ => ⟨hne, Or.inr hr⟩,
          fun ⟨hne, h⟩ => ⟨hne, by rcases h with rfl | hr; exacts [hv_in.2, hr]⟩⟩
    · simp only [not_or] at hcond
      simp only [List.mem_cons, ih]
      exact ⟨fun h => by rcases h with rfl | ⟨hne, hr⟩; exacts [⟨hcond.1, Or.inl rfl⟩,
        ⟨hne, Or.inr hr⟩],
        fun ⟨hne, h⟩ => by rcases h with rfl | hr; exacts [Or.inl rfl, Or.inr ⟨hne, hr⟩]⟩

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

private theorem bucketOutScope_eq_foldr (x : ℕ) (bucket : List (FactorTable ℕ ℕ)) :
    bucketOutScope x bucket = (bucket.flatMap FactorTable.scope).foldr (dedupStepPure x) [] :=
  filter_dedup_eq_foldr x _

private structure SumScopeArgs where
  bucketPtr : ℕ
  bucketLen : ℕ

private def SumScopeArgs.equiv : SumScopeArgs ≃ ℕ × ℕ where
  toFun s := (s.bucketPtr, s.bucketLen)
  invFun := fun (bucketPtr, bucketLen) => ⟨bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding SumScopeArgs := .ofEquiv SumScopeArgs.equiv

private def sumScopeStep (p : Unit × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  Memory.read (p.2.1 + 1) >>= fun scLen => pure (p.2.1 + 4, p.2.2 + scLen)

private def sumScopeLen (args : SumScopeArgs) : Memory.Prog ℕ :=
  iterate sumScopeStep () args.bucketLen (args.bucketPtr, 0) >>= fun r => pure r.2

private theorem sumScopeLen_state (args : SumScopeArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (sumScopeLen args) = s := by
  unfold sumScopeLen
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of sumScopeStep () (fun _ _ => rfl) args.bucketLen _ s

private theorem sumScopeLen_cost (args : SumScopeArgs) (s : Memory.State) :
    memoryCost (sumScopeLen args) s ≤ args.bucketLen := by
  unfold sumScopeLen
  rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
  simpa using memoryCost_iterate_le_of sumScopeStep 1 () (fun _ _ => le_rfl)
    args.bucketLen (args.bucketPtr, 0) s

private theorem sumScopeLen_valid {w : ℕ} {args : SumScopeArgs} {bucket : List (FactorTable ℕ ℕ)}
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

private theorem sumScopeLen_result {args : SumScopeArgs} {bucket : List (FactorTable ℕ ℕ)}
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

private theorem sumScopeLen_realizes :
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

private structure FlattenArgs where
  bucketPtr : ℕ
  bucketLen : ℕ
  flatLen : ℕ

private def FlattenArgs.equiv : FlattenArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.bucketPtr, s.bucketLen), s.flatLen)
  invFun := fun ((bucketPtr, bucketLen), flatLen) => ⟨bucketPtr, bucketLen, flatLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding FlattenArgs := .ofEquiv FlattenArgs.equiv

private def flattenStep (p : Unit × (ℕ × ℕ)) : Memory.Prog (ℕ × ℕ) :=
  Memory.read p.2.1 >>= fun scPtr =>
  Memory.read (p.2.1 + 1) >>= fun scLen =>
  copyWords ⟨scPtr, p.2.2, scLen⟩ >>= fun _ =>
  pure (p.2.1 + 4, p.2.2 + scLen)

private def flattenScopes (args : FlattenArgs) : Memory.Prog ℕ :=
  Memory.allocDirty args.flatLen >>= fun flatPtr =>
  iterate flattenStep () args.bucketLen (args.bucketPtr, flatPtr) >>= fun _ =>
  pure flatPtr

private theorem flattenScopes_spec {w : ℕ} {args : FlattenArgs} {bucket : List (FactorTable ℕ ℕ)}
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

private theorem copyWords_frame (args : CopyArgs) (t : Memory.State) :
    ((Memory.spec 0).clientState t (copyWords args)).frontier = t.frontier ∧
    ∀ a, a < args.dst → ((Memory.spec 0).clientState t (copyWords args)).mem a = t.mem a := by
  unfold copyWords
  rw [StateTransitionSpec.clientState_bind]
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  rw [hpure_st]
  suffices ∀ (n src dst : ℕ) (u : Memory.State),
      ((Memory.spec 0).clientState u (iterate copyWordsStep () n ⟨src, dst⟩)).frontier =
        u.frontier ∧
      ∀ a, a < dst →
        ((Memory.spec 0).clientState u (iterate copyWordsStep () n ⟨src, dst⟩)).mem a = u.mem a by
    exact this args.len args.src args.dst t
  intro n
  induction n with
  | zero => intro src dst u; exact ⟨rfl, fun _ _ => rfl⟩
  | succ n ih =>
    intro src dst u
    change ((Memory.spec 0).clientState u
      (copyWordsStep ((), ⟨src, dst⟩) >>= iterate copyWordsStep () n)).frontier = u.frontier ∧
      ∀ a < dst, ((Memory.spec 0).clientState u
        (copyWordsStep ((), ⟨src, dst⟩) >>= iterate copyWordsStep () n)).mem a = u.mem a
    rw [StateTransitionSpec.clientState_bind]
    have hstep_st : (Memory.spec 0).clientState u (copyWordsStep ((), ⟨src, dst⟩)) =
        ⟨Function.update u.mem dst (u.mem src), u.frontier⟩ := rfl
    have hstep_res : (Memory.spec 0).clientResult u (copyWordsStep ((), ⟨src, dst⟩)) =
        ⟨src + 1, dst + 1⟩ := rfl
    rw [hstep_st, hstep_res]
    obtain ⟨hfr_i, hmem_i⟩ := ih (src + 1) (dst + 1)
      ⟨Function.update u.mem dst (u.mem src), u.frontier⟩
    refine ⟨hfr_i, fun a ha => ?_⟩
    rw [hmem_i a (by omega)]
    exact Function.update_of_ne (by omega) _ u.mem

private theorem flattenScopes_realizes :
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
  dsimp only
  unfold dedupFilterBack
  let outBuf := s.frontier
  have hv_a : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty args.flatLen)) :=
    validHistory_allocDirty hfit
  let s₀ : Memory.State := ⟨s.mem, outBuf + args.flatLen⟩
  have hwf₀ : Memory.WellFormed w s₀ := hwf.step (o := .allocDirty args.flatLen) hfit
  have hloop : ∀ (ys : List ℕ) (acc : List ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      t.frontier = outBuf + args.flatLen →
      PreservesBelow outBuf s t →
      args.flatPtr + ys.length ≤ outBuf →
      Block.HoldsList args.flatPtr ys s.mem →
      ys.length + acc.length ≤ args.flatLen →
      (ys.foldr (dedupStepPure args.x) acc).length ≤ W_out →
      Block.HoldsList (outBuf + args.flatLen - acc.length) acc t.mem →
      let st₀ : DedupState := ⟨ys.length, outBuf + args.flatLen - acc.length, acc.length⟩
      let p := iterate dedupBackStep (args.x, args.flatPtr) ys.length st₀
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let out := ys.foldr (dedupStepPure args.x) acc
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = outBuf + args.flatLen ∧
        PreservesBelow outBuf s t' ∧
        r.outStart = outBuf + args.flatLen - out.length ∧
        r.outLen = out.length ∧
        out.length ≤ args.flatLen ∧
        Block.HoldsList r.outStart out t'.mem ∧
        memoryCost p t ≤ ys.length * (2 + W_out) := by
    intro ys
    induction ys using List.reverseRecOn with
    | nil =>
      intro acc t _ hfr hpres _ _ hroom _ hacc
      simp only [List.length_nil, Nat.zero_add, List.foldr_nil, Nat.zero_mul] at hroom ⊢
      exact ⟨validHistory_pure w t _, hfr, hpres, rfl, rfl, hroom, hacc, by simp [iterate]⟩
    | append_singleton ys' v ih =>
      intro acc t hwf_t hfr hpres hys_b hys_h hroom hW_cur hacc
      rw [List.length_append, List.length_singleton] at hys_b hroom
      obtain ⟨hys'_h, hv_h⟩ := Block.holdsList_append_iff.mp hys_h
      have hv_mem_s : s.mem (args.flatPtr + ys'.length) = v :=
        (Block.holdsList_cons_iff.mp hv_h).1
      have hv_mem_t : t.mem (args.flatPtr + ys'.length) = v :=
        (hpres.2.2 _ (by omega)).trans hv_mem_s
      have hacc_W : acc.length ≤ W_out :=
        (length_le_foldr_dedupStepPure args.x (ys' ++ [v]) acc).trans hW_cur
      let outStart := outBuf + args.flatLen - acc.length
      let st₀ : DedupState := ⟨(ys' ++ [v]).length, outStart, acc.length⟩
      have hpos_eq : st₀.remPos - 1 = ys'.length := by
        dsimp only [st₀]; rw [List.length_append, List.length_singleton]; omega
      let msArgs : MemScanArgs := ⟨v, outStart, acc.length⟩
      have hms_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (memScan msArgs)) :=
        memScan_valid msArgs (by dsimp only [msArgs, outStart]; omega)
      have hms_res : (Memory.spec 0).clientResult t (memScan msArgs) =
          if v ∈ acc then 1 else 0 := memScan_result hacc rfl
      have hms_cost : memoryCost (memScan msArgs) t ≤ W_out :=
        (memScan_cost msArgs t).trans hacc_W
      have hr_t (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hres_t (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hlen_ys : (ys' ++ [v]).length = ys'.length + 1 := by simp
      dsimp only
      rw [hlen_ys]
      have hiter_eq : iterate dedupBackStep (args.x, args.flatPtr) (ys'.length + 1)
          ⟨ys'.length + 1, outStart, acc.length⟩ =
          (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩) >>=
            iterate dedupBackStep (args.x, args.flatPtr) ys'.length) := rfl
      rw [hiter_eq]
      have hfoldr_eq : (ys' ++ [v]).foldr (dedupStepPure args.x) acc =
          ys'.foldr (dedupStepPure args.x) (dedupStepPure args.x v acc) := by
        rw [List.foldr_append, List.foldr_cons, List.foldr_nil]
      rw [hfoldr_eq] at hW_cur ⊢
      by_cases hcond : v = args.x ∨ v ∈ acc
      · have hguard : v = args.x ∨ (Memory.spec 0).clientResult t (memScan msArgs) = 1 := by
          rcases hcond with h1 | h2
          · exact Or.inl h1
          · exact Or.inr (by rw [hms_res, ite_eq_left h2])
        have hstep_val : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩))) := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel]
          refine validHistory_read_bind (by omega) ?_
          rw [hv_mem_t]
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, ite_eq_left hguard]
          exact validHistory_pure w t _
        have hstep_st : (Memory.spec 0).clientState t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) =
            t := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, StateTransitionSpec.clientState_bind, hr_t, hres_t, hv_mem_t,
            StateTransitionSpec.clientState_bind, memScan_state, ite_eq_left hguard]
          rfl
        have hstep_res : (Memory.spec 0).clientResult t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) =
            ⟨ys'.length, outStart, acc.length⟩ := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, StateTransitionSpec.clientResult_bind, hr_t, hres_t, hv_mem_t,
            StateTransitionSpec.clientResult_bind, memScan_state, ite_eq_left hguard]
          rfl
        have hstep_cost : memoryCost
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) t ≤
            2 + W_out := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, memoryCost_bind', memoryCost_read, hr_t, hres_t, hv_mem_t,
            memoryCost_bind', memScan_state, ite_eq_left hguard, memoryCost_pure]
          dsimp only [msArgs] at hms_cost
          omega
        have hdedup_eq : dedupStepPure args.x v acc = acc := by
          unfold dedupStepPure; exact ite_eq_left hcond
        rw [hdedup_eq] at hW_cur ⊢
        obtain ⟨hv_i, hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, hcost_i⟩ :=
          ih acc t hwf_t hfr hpres (by omega) hys'_h (by omega) hW_cur hacc
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_res, memoryCost_bind', hstep_st, hstep_res]
        refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hv_i),
          hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, ?_⟩
        calc memoryCost _ t + _
            ≤ (2 + W_out) + ys'.length * (2 + W_out) := Nat.add_le_add hstep_cost hcost_i
          _ = (ys'.length + 1) * (2 + W_out) := by ring
      · have hnot_guard : ¬ (v = args.x ∨ (Memory.spec 0).clientResult t (memScan msArgs) = 1) := by
          rintro (h1 | h2)
          · exact hcond (Or.inl h1)
          · have hnot_in : v ∉ acc := fun hm => hcond (Or.inr hm)
            rw [hms_res, ite_eq_right hnot_in] at h2
            cases h2
        have hv_fit : Fits w v := hv_mem_t ▸ hwf_t.mem_fits (args.flatPtr + ys'.length)
        have hout_lt : outStart - 1 < t.frontier := by dsimp only [outStart]; omega
        let t₁ : Memory.State := ⟨Function.update t.mem (outStart - 1) v, t.frontier⟩
        have hwf₁ : Memory.WellFormed w t₁ :=
          hwf_t.step (o := .write (outStart - 1) v) ⟨hout_lt, hv_fit⟩
        have hstep_val : (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩))) := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel]
          refine validHistory_read_bind (by omega) ?_
          rw [hv_mem_t]
          refine validHistory_bind_step hms_val ?_
          rw [memScan_state, ite_eq_right hnot_guard]
          exact validHistory_write_bind hout_lt hv_fit (validHistory_pure w _ _)
        have hstep_st : (Memory.spec 0).clientState t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) =
            t₁ := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, StateTransitionSpec.clientState_bind, hr_t, hres_t, hv_mem_t,
            StateTransitionSpec.clientState_bind, memScan_state, ite_eq_right hnot_guard,
            StateTransitionSpec.clientState_bind]
          rfl
        have hout_sub : outStart - 1 = outBuf + args.flatLen - (v :: acc).length := by
          dsimp only [outStart]; simp only [List.length_cons]; omega
        have hstep_res : (Memory.spec 0).clientResult t
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) =
            ⟨ys'.length, outBuf + args.flatLen - (v :: acc).length, (v :: acc).length⟩ := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, StateTransitionSpec.clientResult_bind, hr_t, hres_t, hv_mem_t,
            StateTransitionSpec.clientResult_bind, memScan_state, ite_eq_right hnot_guard,
            StateTransitionSpec.clientResult_bind]
          change (⟨ys'.length, outStart - 1, acc.length + 1⟩ : DedupState) = _
          rw [hout_sub]
          rfl
        have hstep_cost : memoryCost
            (dedupBackStep ((args.x, args.flatPtr), ⟨ys'.length + 1, outStart, acc.length⟩)) t ≤
            2 + W_out := by
          unfold dedupBackStep
          dsimp only
          rw [Nat.add_sub_cancel, memoryCost_bind', memoryCost_read, hr_t, hres_t, hv_mem_t,
            memoryCost_bind', memScan_state, ite_eq_right hnot_guard,
            memoryCost_bind', memoryCost_write, memoryCost_pure]
          dsimp only [msArgs] at hms_cost
          omega
        have hpres₁ : PreservesBelow outBuf s t₁ := by
          refine ⟨le_rfl, by dsimp only [t₁]; omega, fun a ha => ?_⟩
          have hne : a ≠ outStart - 1 := by dsimp only [outStart]; omega
          change Function.update t.mem (outStart - 1) v a = s.mem a
          rw [Function.update_of_ne hne]
          exact hpres.2.2 a ha
        have hacc₁ : Block.HoldsList (outBuf + args.flatLen - (v :: acc).length) (v :: acc)
            t₁.mem := by
          rw [← hout_sub]
          refine Block.holdsList_cons_iff.mpr ⟨Function.update_self _ v t.mem, ?_⟩
          have hpos1 : outStart - 1 + 1 = outStart := by dsimp only [outStart]; omega
          rw [hpos1]
          exact hacc.frame fun a hlo hhi =>
            Function.update_of_ne (by dsimp only [outStart] at hlo ⊢; omega) v t.mem
        have hdedup_eq : dedupStepPure args.x v acc = v :: acc := by
          unfold dedupStepPure; exact ite_eq_right hcond
        rw [hdedup_eq] at hW_cur ⊢
        obtain ⟨hv_i, hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, hcost_i⟩ :=
          ih (v :: acc) t₁ hwf₁ hfr hpres₁ (by omega) hys'_h (by simp; omega) hW_cur hacc₁
        rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
          hstep_st, hstep_res, memoryCost_bind', hstep_st, hstep_res]
        refine ⟨validHistory_bind_step hstep_val (by simpa [hstep_st, hstep_res] using hv_i),
          hfr_i, hpres_i, hst_i, hlen_i, hle_i, hholds_i, ?_⟩
        calc memoryCost _ t + _
            ≤ (2 + W_out) + ys'.length * (2 + W_out) := Nat.add_le_add hstep_cost hcost_i
          _ = (ys'.length + 1) * (2 + W_out) := by ring
  obtain ⟨hv_l, hfr_l, hpres_l, hst_l, hlen_l, hle_l, hholds_l, hcost_l⟩ :=
    hloop flat [] s₀ hwf₀ rfl ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩
      hflat.1 hflat.2 (by simp [hlen]) hW (Block.holdsList_nil _ _)
  simp only [List.length_nil, Nat.sub_zero] at hv_l hfr_l hpres_l hst_l hlen_l hholds_l hcost_l
  have ha_st : (Memory.spec 0).clientState s (Memory.allocDirty args.flatLen) = s₀ := rfl
  have ha_res : (Memory.spec 0).clientResult s (Memory.allocDirty args.flatLen) = outBuf := rfl
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  rw [← hlen]
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind]
  rw [hlen, ha_st, ha_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hpure_res, hpure_st, ← hlen]
  refine ⟨validHistory_bind_step (by rw [hlen]; exact hv_a) ?_,
    by simpa [hlen] using hfr_l,
    by simpa [outBuf, hlen] using hpres_l,
    ?_,
    by simpa [hlen] using hlen_l, ?_, ?_⟩
  · rw [hlen, ha_st, ha_res]
    exact validHistory_bind_step (by simpa [hlen] using hv_l) (validHistory_pure w _ _)
  · have hst' : ((Memory.spec 0).clientResult s₀
        (iterate dedupBackStep (args.x, args.flatPtr) flat.length
          ⟨flat.length, outBuf + flat.length, 0⟩)).outStart =
        outBuf + flat.length - (flat.foldr (dedupStepPure args.x) []).length := by
      simpa [hlen] using hst_l
    have hle' : (flat.foldr (dedupStepPure args.x) []).length ≤ flat.length := by
      simpa [hlen] using hle_l
    dsimp only [outBuf] at hst' ⊢
    rw [hst']
    omega
  · refine ⟨?_, by simpa [hlen] using hholds_l⟩
    have hfr' : ((Memory.spec 0).clientState s₀
        (iterate dedupBackStep (args.x, args.flatPtr) flat.length
          ⟨flat.length, outBuf + flat.length, 0⟩)).frontier = outBuf + flat.length := by
      simpa [hlen] using hfr_l
    have hst' : ((Memory.spec 0).clientResult s₀
        (iterate dedupBackStep (args.x, args.flatPtr) flat.length
          ⟨flat.length, outBuf + flat.length, 0⟩)).outStart =
        outBuf + flat.length - (flat.foldr (dedupStepPure args.x) []).length := by
      simpa [hlen] using hst_l
    rw [hfr', hst']
    omega
  · rw [hlen, memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res,
      memoryCost_bind', memoryCost_pure, Nat.add_zero]
    have hc' : memoryCost (iterate dedupBackStep (args.x, args.flatPtr) args.flatLen
        ⟨args.flatLen, outBuf + args.flatLen, 0⟩) s₀ ≤ args.flatLen * (2 + W_out) := by
      simpa [hlen] using hcost_l
    rw [← hlen] at hc' ⊢
    omega

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

private structure BuildOutScopeArgs where
  x : ℕ
  bucketPtr : ℕ
  bucketLen : ℕ

private def BuildOutScopeArgs.equiv : BuildOutScopeArgs ≃ (ℕ × ℕ) × ℕ where
  toFun s := ((s.x, s.bucketPtr), s.bucketLen)
  invFun := fun ((x, bucketPtr), bucketLen) => ⟨x, bucketPtr, bucketLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BuildOutScopeArgs := .ofEquiv BuildOutScopeArgs.equiv

private def buildOutScope (args : BuildOutScopeArgs) : Memory.Prog (ℕ × ℕ) :=
  sumScopeLen ⟨args.bucketPtr, args.bucketLen⟩ >>= fun flatLen =>
  flattenScopes ⟨args.bucketPtr, args.bucketLen, flatLen⟩ >>= fun flatPtr =>
  dedupFilterBack ⟨args.x, flatPtr, flatLen⟩

private theorem buildOutScope_spec {w : ℕ} {args : BuildOutScopeArgs}
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
  let flat := bucket.flatMap FactorTable.scope
  let K := flat.length
  have hK_le : K ≤ args.bucketLen * maxScope := by
    rw [← hlen]
    dsimp only [K, flat]
    rw [List.length_flatMap]
    have hsum := List.sum_le_length_nsmul (bucket.map fun a => a.scope.length) maxScope
      fun _ hn => by
        rcases List.mem_map.mp hn with ⟨f, hf, rfl⟩
        exact hmax f hf
    simpa [smul_eq_mul] using hsum
  have hss_val := sumScopeLen_valid (w := w) (args := ⟨args.bucketPtr, args.bucketLen⟩) hb hlen
  have hss_st := sumScopeLen_state ⟨args.bucketPtr, args.bucketLen⟩ s
  have hss_res : (Memory.spec 0).clientResult s (sumScopeLen ⟨args.bucketPtr, args.bucketLen⟩) =
      K := sumScopeLen_result hb hlen
  have hss_cost := sumScopeLen_cost ⟨args.bucketPtr, args.bucketLen⟩ s
  obtain ⟨hfl_val, hfl_fr, hfl_pres, hfl_res, hfl_holds, hfl_cost⟩ :=
    flattenScopes_spec (w := w) (args := ⟨args.bucketPtr, args.bucketLen, K⟩) hwf hb hlen rfl hmax
      (hfit.of_le (by dsimp only; omega))
  let s₁ := (Memory.spec 0).clientState s (flattenScopes ⟨args.bucketPtr, args.bucketLen, K⟩)
  have hwf₁ : Memory.WellFormed w s₁ := wellFormed_clientState hwf hfl_val
  have hW_foldr : (flat.foldr (dedupStepPure args.x) []).length ≤ W_out := by
    rw [← bucketOutScope_eq_foldr]; exact hW
  obtain ⟨hdd_val, hdd_fr, hdd_pres, hdd_lo, hdd_len, hdd_holds, hdd_cost⟩ :=
    dedupFilterBack_spec (w := w) (args := ⟨args.x, s.frontier, K⟩) hwf₁
      (by simpa [hfl_res] using hfl_holds) rfl hW_foldr
      (hfit.of_le (by
        change s₁.frontier + K ≤ s.frontier + 2 * (args.bucketLen * maxScope)
        have h1 : s₁.frontier = s.frontier + K := hfl_fr
        rw [h1]; omega))
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hss_st, hss_res,
    StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
    hfl_res, bucketOutScope_eq_foldr]
  refine ⟨validHistory_bind_step hss_val ?_, ?_, hfl_pres.trans (hdd_pres.mono_bound hfl_pres.2.1),
    hfl_pres.2.1.trans hdd_lo, hdd_len, hdd_holds, ?_⟩
  · rw [hss_st, hss_res]
    refine validHistory_bind_step hfl_val ?_
    rw [hfl_res]
    exact hdd_val
  · change ((Memory.spec 0).clientState s₁ (dedupFilterBack ⟨args.x, s.frontier, K⟩)).frontier ≤
        s.frontier + 2 * (args.bucketLen * maxScope)
    have h1 : s₁.frontier = s.frontier + K := hfl_fr
    have h2 : ((Memory.spec 0).clientState s₁
        (dedupFilterBack ⟨args.x, s.frontier, K⟩)).frontier = s₁.frontier + K := hdd_fr
    rw [h2, h1]
    omega
  · rw [memoryCost_bind', hss_st, hss_res, memoryCost_bind', hfl_res]
    dsimp only at hss_cost hfl_cost hdd_cost
    have hdd_le : K * (2 + W_out) ≤ args.bucketLen * maxScope * (2 + W_out) :=
      Nat.mul_le_mul_right _ hK_le
    calc memoryCost (sumScopeLen ⟨args.bucketPtr, args.bucketLen⟩) s +
          (memoryCost (flattenScopes ⟨args.bucketPtr, args.bucketLen, K⟩) s +
            memoryCost (dedupFilterBack ⟨args.x, s.frontier, K⟩) s₁)
        ≤ args.bucketLen + ((1 + args.bucketLen * (2 + 2 * maxScope)) +
            (1 + args.bucketLen * maxScope * (2 + W_out))) :=
          Nat.add_le_add hss_cost (Nat.add_le_add hfl_cost (by omega))
      _ = 2 + args.bucketLen * (3 + 2 * maxScope + maxScope * (2 + W_out)) := by ring

private theorem buildOutScope_realizes :
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
  · obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    let K := (bucket.flatMap FactorTable.scope).length
    have hscK : ∀ f ∈ bucket, f.scope.length ≤ K := fun f hf => by
      dsimp only [K]
      rw [List.length_flatMap]
      exact List.le_sum_of_mem
        (List.mem_map_of_mem (f := fun g : FactorTable ℕ ℕ => g.scope.length) hf)
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    obtain ⟨_, hfl_fr, _, hfl_res, _, _⟩ :=
      flattenScopes_spec (w := w) (args := ⟨d.bucketPtr, d.bucketLen, K⟩) hmem hb hlen rfl
        hscK (hfit.of_le (by dsimp only [K]; omega))
    rw [hfl_res, hfl_fr]
  · obtain ⟨_, bucket, hlen, hb, hfit⟩ := h
    let K := (bucket.flatMap FactorTable.scope).length
    have hscK : ∀ f ∈ bucket, f.scope.length ≤ K := fun f hf => by
      dsimp only [K]
      rw [List.length_flatMap]
      exact List.le_sum_of_mem
        (List.mem_map_of_mem (f := fun g : FactorTable ℕ ℕ => g.scope.length) hf)
    rw [sumScopeLen_state, sumScopeLen_result hb hlen]
    obtain ⟨_, hfl_fr, _, _, _, _⟩ :=
      flattenScopes_spec (w := w) (args := ⟨d.bucketPtr, d.bucketLen, K⟩) hmem hb hlen rfl
        hscK (hfit.of_le (by dsimp only [K]; omega))
    rw [hfl_fr]
    exact hfit.of_le (by dsimp only [K]; omega)

/-! ### Multiplicative state-capacity budget (`stateCap`), `elimVarProg`, and `elimOrderLoop` -/

private theorem capFactor_elimBucketTable (d x : ℕ) (bucket : List (FactorTable ℕ ℕ)) :
    capFactor (elimBucketTable d x bucket) ≤ max 1 d * (bucket.map capFactor).prod := by
  rw [capFactor]
  refine max_le (Nat.mul_le_mul (le_max_left 1 d)
    (List.one_le_prod_of_one_le (by simp [one_le_capFactor]))) ?_
  refine List.foldl_max_le (Nat.zero_le _) fun v hv => ?_
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  rw [Array.getElem_toList]
  simp only [elimBucketTable, Array.getElem_ofFn]
  have hsum : (∑ a : Fin d,
      (bucket.map fun f => f.evalAt d fun u =>
        if u = x then a.1
        else assignScope (bucketOutScope x bucket)
          (lsbDecode d (bucketOutScope x bucket).length i) u).prod) ≤
      ∑ _ : Fin d, (bucket.map capFactor).prod := by
    refine Finset.sum_le_sum fun a _ => ?_
    exact List.prod_map_le_prod_map₀ _ _ (fun _ _ => Nat.zero_le _)
      fun f _ => evalAt_le_capFactor d f _
  calc _ ≤ ∑ _ : Fin d, (bucket.map capFactor).prod := hsum
    _ = d * (bucket.map capFactor).prod := by simp
    _ ≤ max 1 d * (bucket.map capFactor).prod := Nat.mul_le_mul_right _ (le_max_right 1 d)

private def stateCap (s : ElimState ℕ ℕ) : ℕ :=
  max 1 s.scalar * (s.live.map capFactor).prod

private theorem one_le_stateCap (s : ElimState ℕ ℕ) : 1 ≤ stateCap s :=
  Nat.mul_le_mul (le_max_left 1 _) (List.one_le_prod_of_one_le (by simp [one_le_capFactor]))

private theorem max_one_mul_le (a d : ℕ) : max 1 (a * d) ≤ max 1 d * max 1 a := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · rw [max_eq_right (Nat.mul_pos ha hd), max_eq_right hd, max_eq_right ha, Nat.mul_comm]

private theorem bucket_prod_le_stateCap (x : ℕ) (s : ElimState ℕ ℕ) :
    (((s.live.filter fun f => decide (x ∈ f.scope)).map capFactor).prod) ≤ stateCap s := by
  have hsplit :=
    ((List.filter_append_perm (fun f => decide (x ∈ f.scope)) s.live).map capFactor).prod_eq
  rw [List.map_append, List.prod_append] at hsplit
  have h1 : 1 ≤ ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod :=
    List.one_le_prod_of_one_le fun _ hn => by
      rcases List.mem_map.mp hn with ⟨f, _, rfl⟩
      exact one_le_capFactor f
  have hle_live : ((s.live.filter fun f => decide (x ∈ f.scope)).map capFactor).prod ≤
      (s.live.map capFactor).prod := by
    calc _ ≤ _ * ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod :=
          Nat.le_mul_of_pos_right _ h1
      _ = (s.live.map capFactor).prod := hsplit
  exact hle_live.trans (Nat.le_mul_of_pos_left _ (le_max_left 1 s.scalar))

private theorem stateCap_elimVar_le (d x : ℕ) (s : ElimState ℕ ℕ) :
    stateCap (elimVar d x s) ≤ max 1 d * stateCap s := by
  by_cases hx : x ∈ s.remaining
  · simp only [elimVar, hx, ↓reduceIte]
    split_ifs with hb
    · unfold stateCap
      dsimp only
      calc max 1 (s.scalar * d) * (s.live.map capFactor).prod
          ≤ (max 1 d * max 1 s.scalar) * (s.live.map capFactor).prod :=
            Nat.mul_le_mul_right _ (max_one_mul_le s.scalar d)
        _ = max 1 d * (max 1 s.scalar * (s.live.map capFactor).prod) := Nat.mul_assoc _ _ _
    · unfold stateCap
      dsimp only
      simp only [List.map_cons, List.prod_cons]
      have hcap := capFactor_elimBucketTable d x (s.live.filter fun f => decide (x ∈ f.scope))
      have hrest_eq : (s.live.filter fun f => decide (x ∉ f.scope)) =
          (s.live.filter fun f => !decide (x ∈ f.scope)) := by
        refine List.filter_congr fun f _ => ?_
        simp
      rw [hrest_eq]
      have hsplit :=
        ((List.filter_append_perm (fun f => decide (x ∈ f.scope)) s.live).map capFactor).prod_eq
      rw [List.map_append, List.prod_append] at hsplit
      calc max 1 s.scalar *
            (capFactor (elimBucketTable d x (s.live.filter fun f => decide (x ∈ f.scope))) *
              ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod)
          ≤ max 1 s.scalar *
              ((max 1 d * ((s.live.filter fun f => decide (x ∈ f.scope)).map capFactor).prod) *
                ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcap)
        _ = max 1 d * (max 1 s.scalar *
              (((s.live.filter fun f => decide (x ∈ f.scope)).map capFactor).prod *
                ((s.live.filter fun f => !decide (x ∈ f.scope)).map capFactor).prod)) := by ring
        _ = max 1 d * (max 1 s.scalar * (s.live.map capFactor).prod) := by rw [hsplit]
  · simp only [elimVar, hx, ↓reduceIte]
    exact Nat.le_mul_of_pos_left _ (le_max_left 1 d)

private structure ElimStepState where
  scalar : ℕ
  livePtr : ℕ
  liveLen : ℕ
  remPtr : ℕ
  remLen : ℕ

private def ElimStepState.equiv : ElimStepState ≃ (((ℕ × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((s.scalar, s.livePtr), s.liveLen), s.remPtr), s.remLen)
  invFun := fun ((((scalar, livePtr), liveLen), remPtr), remLen) =>
    ⟨scalar, livePtr, liveLen, remPtr, remLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ElimStepState := .ofEquiv ElimStepState.equiv

private structure ElimVarArgs where
  dom : ℕ
  x : ℕ
  scalar : ℕ
  livePtr : ℕ
  liveLen : ℕ
  remPtr : ℕ
  remLen : ℕ

private def ElimVarArgs.equiv :
    ElimVarArgs ≃ (((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := ((((((s.dom, s.x), s.scalar), s.livePtr), s.liveLen), s.remPtr), s.remLen)
  invFun := fun ((((((dom, x), scalar), livePtr), liveLen), remPtr), remLen) =>
    ⟨dom, x, scalar, livePtr, liveLen, remPtr, remLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ElimVarArgs := .ofEquiv ElimVarArgs.equiv

private def HoldsElimState (st : ElimStepState) (es : ElimState ℕ ℕ) (s : Memory.State) : Prop :=
  0 < s.frontier ∧
  st.scalar = es.scalar ∧
  st.liveLen = es.live.length ∧
  st.remLen = es.remaining.length ∧
  HoldsFactorList st.livePtr es.live s ∧
  HoldsIn st.remPtr es.remaining s

private def elimVarProg (args : ElimVarArgs) : Memory.Prog ElimStepState :=
  memScan ⟨args.x, args.remPtr, args.remLen⟩ >>= fun inRem =>
  if inRem = 0 then
    pure ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩
  else
    filterNe ⟨args.x, args.remPtr, args.remLen⟩ >>= fun remPair =>
    partitionLive ⟨args.x, args.livePtr, args.liveLen⟩ >>= fun part =>
    if part.bucketLen = 0 then
      pure ⟨args.scalar * args.dom, args.livePtr, args.liveLen, remPair.1, remPair.2⟩
    else
      buildOutScope ⟨args.x, part.bucketPtr, part.bucketLen⟩ >>= fun outPair =>
      buildOutEntries
        ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩ >>=
        fun entPair =>
      writeDesc ⟨part.newLiveBuf, outPair.1, outPair.2, entPair.1, entPair.2⟩ >>= fun _ =>
      pure ⟨args.scalar, part.newLiveBuf, 1 + part.restLen, remPair.1, remPair.2⟩

private abbrev stepMemDelta (R M SW d W : ℕ) : ℕ :=
  R + 4 + 8 * M + 2 * (M * SW) + (max 1 d) ^ W

private abbrev stepFixedCost (R M SW d W : ℕ) : ℕ :=
  12 + 3 * R + M * (8 + SW) + W + 4 * (max 1 d) ^ W

private abbrev stepBucketUnitCost (SW d W : ℕ) : ℕ :=
  3 + SW * (4 + W) + (max 1 d) ^ W * (5 + SW * W)

private theorem elimVarProg_spec {w : ℕ} {args : ElimVarArgs} {es : ElimState ℕ ℕ}
    {R M SW W B : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hes : HoldsElimState ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s)
    (hM : es.live.length ≤ M) (hR : es.remaining.length ≤ R)
    (hSW : ∀ f ∈ es.live, f.scope.length ≤ SW)
    (hW : (stepStats args.dom args.x es).jointScopeVars ≤ W) (_hW_SW : W ≤ SW)
    (hcapB : max 1 args.dom * stateCap es ≤ B) (hB : Fits w B)
    (_h1 : Fits w 1) (_hpowSW : Fits w ((max 1 args.dom) ^ SW))
    (hfit_fr : Fits w (s.frontier + stepMemDelta R M SW args.dom W)) :
    let res := (Memory.spec 0).clientResult s (elimVarProg args)
    let s' := (Memory.spec 0).clientState s (elimVarProg args)
    let es' := elimVar args.dom args.x es
    let bk := (stepStats args.dom args.x es).bucketFactors
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (elimVarProg args)) ∧
      PreservesBelow s.frontier s s' ∧
      s'.frontier ≤ s.frontier + stepMemDelta R M SW args.dom W ∧
      HoldsElimState res es' s' ∧
      memoryCost (elimVarProg args) s ≤
        stepFixedCost R M SW args.dom W + bk * stepBucketUnitCost SW args.dom W := by
  dsimp only
  unfold elimVarProg
  obtain ⟨hs0, hsc_eq, hlive_len, hrem_len, hlive_h, hrem_h⟩ := hes
  dsimp only at hsc_eq hlive_len hrem_len hlive_h hrem_h
  let msArgs : MemScanArgs := ⟨args.x, args.remPtr, args.remLen⟩
  have hms_val :
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (memScan msArgs)) :=
    memScan_valid msArgs (by dsimp only [msArgs]; rw [hrem_len]; exact hrem_h.1)
  have hms_st : (Memory.spec 0).clientState s (memScan msArgs) = s := memScan_state msArgs s
  have hms_res : (Memory.spec 0).clientResult s (memScan msArgs) =
      if args.x ∈ es.remaining then 1 else 0 := memScan_result hrem_h.2 hrem_len.symm
  have hms_cost : memoryCost (memScan msArgs) s ≤ R :=
    (memScan_cost msArgs s).trans (by dsimp only [msArgs]; rw [hrem_len]; exact hR)
  dsimp only [msArgs] at hms_cost
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  by_cases hx : args.x ∈ es.remaining
  · have hin1 : ¬ ((Memory.spec 0).clientResult s (memScan msArgs) = 0) := by
      rw [hms_res, ite_eq_left hx]; decide
    let fnArgs : MemScanArgs := ⟨args.x, args.remPtr, args.remLen⟩
    have hfn_spec := filterNe_spec (w := w) fnArgs hwf hrem_h hrem_len.symm
      (hfit_fr.of_le (by dsimp only [fnArgs, stepMemDelta]; omega))
    have hfn_cost := filterNe_cost fnArgs s
    dsimp only at hfn_spec
    generalize hs₁ : (Memory.spec 0).clientState s (filterNe fnArgs) = s₁ at hfn_spec
    generalize hremPair : (Memory.spec 0).clientResult s (filterNe fnArgs) = remPair at hfn_spec
    obtain ⟨hfn_val, hfn_fr, hfn_pres, hfn_ptr, hfn_len, hfn_holds⟩ := hfn_spec
    dsimp only [fnArgs] at hfn_fr hfn_len hfn_holds hfn_cost
    have hwf₁ : Memory.WellFormed w s₁ := by rw [← hs₁]; exact wellFormed_clientState hwf hfn_val
    have hlive_s₁ : HoldsFactorList args.livePtr es.live s₁ := hlive_h.mono_frontier hfn_pres
    let plArgs : PartitionArgs := ⟨args.x, args.livePtr, args.liveLen⟩
    have hpl_spec := partitionLive_spec (w := w) (args := plArgs) hwf₁ hlive_s₁ hlive_len.symm hSW
      (hfit_fr.of_le (by rw [hfn_fr]; dsimp only [plArgs, stepMemDelta]; omega))
    dsimp only at hpl_spec
    generalize hs₂ : (Memory.spec 0).clientState s₁ (partitionLive plArgs) = s₂ at hpl_spec
    generalize hpart : (Memory.spec 0).clientResult s₁ (partitionLive plArgs) = part at hpl_spec
    obtain ⟨hpl_val, hpl_fr, hpl_pres, hpl_bPtr, hpl_rBuf, hpl_bLen, hpl_rLen,
        hpl_bH, _, hpl_rH, hpl_rD, hpl_cost⟩ := hpl_spec
    dsimp only [plArgs] at hpl_fr hpl_rBuf hpl_bLen hpl_rLen hpl_bH hpl_rH hpl_rD hpl_cost
    have hwf₂ : Memory.WellFormed w s₂ :=
      by rw [← hs₂]; exact wellFormed_clientState hwf₁ hpl_val
    let bucket := es.live.filter fun f => decide (args.x ∈ f.scope)
    let rest := es.live.filter fun f => decide (args.x ∉ f.scope)
    let rem' := es.remaining.filter fun v => decide (v ≠ args.x)
    change part.bucketLen = bucket.length at hpl_bLen
    change part.restLen = rest.length at hpl_rLen
    change HoldsFactorList part.bucketPtr bucket s₂ at hpl_bH
    change HoldsFactorList (part.newLiveBuf + 4) rest s₂ at hpl_rH
    change AllDataBelow s₁.frontier (part.newLiveBuf + 4) rest s₂ at hpl_rD
    have hs2_fr : s₂.frontier = s.frontier + args.remLen + 4 + 8 * args.liveLen := by
      rw [hpl_fr, hfn_fr]
    by_cases hbk0 : bucket.isEmpty = true
    · have hb_nil : bucket = [] := List.isEmpty_iff.mp hbk0
      have hp_bLen0 : part.bucketLen = 0 := by rw [hpl_bLen, hb_nil]; rfl
      have hes'_eq : elimVar args.dom args.x es =
          { scalar := es.scalar * args.dom, live := es.live, remaining := rem' } := by
        unfold elimVar
        rw [ite_eq_left hx]
        dsimp only
        change (if bucket.isEmpty then _ else _) = _
        rw [ite_eq_left hbk0]
        simp only [Nat.cast_id]
        rfl
      have hbk_eq : (stepStats args.dom args.x es).bucketFactors = 0 := by
        unfold stepStats
        rw [ite_eq_left hx]
        dsimp only
        change ElimStepStats.bucketFactors (if bucket.isEmpty then _ else _) = 0
        rw [ite_eq_left hbk0]
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hms_st, ite_eq_right hin1,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hs₁, hremPair,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hs₂, hpart,
        ite_eq_left hp_bLen0, hpure_st, hpure_res, hes'_eq, hbk_eq]
      have hpres_all : PreservesBelow s.frontier s s₂ :=
        hfn_pres.trans (hpl_pres.mono_bound hfn_pres.2.1)
      refine ⟨validHistory_bind_step hms_val ?_, hpres_all,
        by rw [hs2_fr]; dsimp only [stepMemDelta]; omega, ?_, ?_⟩
      · rw [hms_st, ite_eq_right hin1]
        refine validHistory_bind_step hfn_val ?_
        rw [hs₁, hremPair]
        refine validHistory_bind_step hpl_val ?_
        rw [hs₂, hpart, ite_eq_left hp_bLen0]
        exact validHistory_pure w s₂ _
      · refine ⟨by rw [hs2_fr]; omega, by dsimp only; rw [hsc_eq], hlive_len, hfn_len,
          hlive_h.mono_frontier hpres_all, hfn_holds.mono_frontier hpl_pres⟩
      · rw [memoryCost_bind', hms_st, ite_eq_right hin1, memoryCost_bind',
          hs₁, hremPair, memoryCost_bind', hs₂, hpart, ite_eq_left hp_bLen0,
          memoryCost_pure, Nat.add_zero]
        have hM_mul : args.liveLen * (8 + SW) ≤ M * (8 + SW) :=
          Nat.mul_le_mul_right _ (by omega)
        dsimp only [stepFixedCost]
        omega
    · have hb_ne : bucket ≠ [] := fun h => hbk0 (List.isEmpty_iff.mpr h)
      have hp_bLen_ne : ¬ (part.bucketLen = 0) := by
        rw [hpl_bLen]; exact (List.length_pos_iff.mpr hb_ne).ne'
      have hes'_eq : elimVar args.dom args.x es =
          { scalar := es.scalar, live := elimBucketTable args.dom args.x bucket :: rest,
            remaining := rem' } := by
        simp [elimVar, hx, hbk0, bucket, rest, rem']
      have hbk_eq : (stepStats args.dom args.x es).bucketFactors = bucket.length := by
        simp [stepStats, hx, hbk0, bucket]
      have hj_le : (bucketJointScope bucket).length ≤ W := by
        simpa [stepStats, hx, hbk0, bucket] using hW
      have hout_le_W : (bucketOutScope args.x bucket).length ≤ W :=
        (List.length_filter_le _ _).trans hj_le
      have hb_SW : ∀ f ∈ bucket, f.scope.length ≤ SW :=
        fun f hf => hSW f (List.mem_filter.mp hf).1
      have hb_le_M : part.bucketLen ≤ M := by
        rw [hpl_bLen]; exact (List.length_filter_le _ _).trans hM
      let bosArgs : BuildOutScopeArgs := ⟨args.x, part.bucketPtr, part.bucketLen⟩
      have hbmul_le : part.bucketLen * SW ≤ M * SW := Nat.mul_le_mul_right SW hb_le_M
      have hbos_spec :=
        buildOutScope_spec (w := w) (args := bosArgs) hwf₂ hpl_bH hpl_bLen.symm hb_SW hout_le_W
          (hfit_fr.of_le (by dsimp only [bosArgs, stepMemDelta]; rw [hs2_fr]; omega))
      dsimp only at hbos_spec
      generalize hs₃ : (Memory.spec 0).clientState s₂ (buildOutScope bosArgs) = s₃ at hbos_spec
      generalize houtPair :
        (Memory.spec 0).clientResult s₂ (buildOutScope bosArgs) = outPair at hbos_spec
      obtain ⟨hbos_val, hbos_fr, hbos_pres, hbos_lo, hbos_len, hbos_holds, hbos_cost⟩ := hbos_spec
      dsimp only [bosArgs] at hbos_fr hbos_len hbos_holds hbos_cost
      have hwf₃ : Memory.WellFormed w s₃ :=
        by rw [← hs₃]; exact wellFormed_clientState hwf₂ hbos_val
      have hjoint_eq : (bucketOutScope args.x bucket).length + 1 =
          (bucketJointScope bucket).length :=
        length_bucketOutScope_add_one hb_ne fun f hf => by
          simpa using (List.mem_filter.mp hf).2
      have hout_succ_le_W : outPair.2 + 1 ≤ W := by
        rw [hbos_len, hjoint_eq]; exact hj_le
      have hout_le_W' : outPair.2 ≤ W := Nat.le_of_succ_le hout_succ_le_W
      have hpow_out_le : (max 1 args.dom) ^ outPair.2 ≤ (max 1 args.dom) ^ W :=
        Nat.pow_le_pow_right (le_max_left 1 args.dom) hout_le_W'
      have hpow_joint_le : (max 1 args.dom) ^ outPair.2 * args.dom ≤ (max 1 args.dom) ^ W := by
        calc (max 1 args.dom) ^ outPair.2 * args.dom
            ≤ (max 1 args.dom) ^ outPair.2 * max 1 args.dom :=
              Nat.mul_le_mul_left _ (le_max_right 1 args.dom)
          _ = (max 1 args.dom) ^ (outPair.2 + 1) := (Nat.pow_succ _ _).symm
          _ ≤ (max 1 args.dom) ^ W :=
              Nat.pow_le_pow_right (le_max_left 1 args.dom) hout_succ_le_W
      have hb_capB : max 1 args.dom * (bucket.map capFactor).prod ≤ B :=
        (Nat.mul_le_mul_left _ (bucket_prod_le_stateCap args.x es)).trans hcapB
      let boeArgs : BuildOutArgs :=
        ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩
      have hs3_pos : 0 < s₃.frontier := lt_of_lt_of_le hs0
        (hfn_pres.2.1.trans (hpl_pres.2.1.trans hbos_pres.2.1))
      have hboe_spec :=
        buildOutEntries_spec (w := w) (args := boeArgs) hwf₃ hs3_pos
          hbos_holds rfl hbos_len.symm (hpl_bH.mono_frontier hbos_pres) hpl_bLen.symm hb_SW
          (hfit_fr.of_le (by dsimp only [boeArgs, stepMemDelta]; rw [hs2_fr] at hbos_fr; omega))
          hb_capB hB
      dsimp only at hboe_spec
      generalize hs₄ : (Memory.spec 0).clientState s₃ (buildOutEntries boeArgs) = s₄ at hboe_spec
      generalize hentPair :
        (Memory.spec 0).clientResult s₃ (buildOutEntries boeArgs) = entPair at hboe_spec
      obtain ⟨hboe_val, hboe_pres, hboe_fr, hboe_lo, hboe_len, hboe_holds, hboe_cost⟩ := hboe_spec
      dsimp only [boeArgs] at hboe_fr hboe_len hboe_holds hboe_cost
      have hwf₄ : Memory.WellFormed w s₄ :=
        by rw [← hs₄]; exact wellFormed_clientState hwf₃ hboe_val
      let newTab := elimBucketTable args.dom args.x bucket
      change entPair.2 = newTab.entries.size at hboe_len
      change HoldsIn entPair.1 newTab.entries.toList s₄ at hboe_holds
      let wdFinal : WriteDescArgs := ⟨part.newLiveBuf, outPair.1, outPair.2, entPair.1, entPair.2⟩
      have hrBuf_le_s2 : part.newLiveBuf + 4 ≤ s₂.frontier := by omega
      have hs2_le_s3 : s₂.frontier ≤ s₃.frontier := hbos_pres.2.1
      have hs3_le_s4 : s₃.frontier ≤ s₄.frontier := hboe_pres.2.1
      have hwd_dst_lt : part.newLiveBuf + 4 ≤ s₄.frontier :=
        hrBuf_le_s2.trans (hs2_le_s3.trans hs3_le_s4)
      have hout_s4 : HoldsIn outPair.1 newTab.scope s₄ :=
        hbos_holds.mono_frontier hboe_pres
      have hsc_eq_new : newTab.scope = bucketOutScope args.x bucket := rfl
      have hfit_o1 : Fits w outPair.1 := hwf₄.frontier_fits.of_le (by have := hout_s4.1; omega)
      have hfit_o2 : Fits w outPair.2 := hwf₄.frontier_fits.of_le (by
        have hbd := hout_s4.1; rw [hsc_eq_new, ← hbos_len] at hbd; omega)
      have hfit_e1 : Fits w entPair.1 := hwf₄.frontier_fits.of_le (by have := hboe_holds.1; omega)
      have hfit_e2 : Fits w entPair.2 := hwf₄.frontier_fits.of_le (by
        have hbd := hboe_holds.1; rw [Array.length_toList, ← hboe_len] at hbd; omega)
      have hwd_val := writeDesc_valid wdFinal hwd_dst_lt hfit_o1 hfit_o2 hfit_e1 hfit_e2
      have hwd_fr_pair := writeDesc_frame wdFinal s₄
      have hst5_def : (Memory.spec 0).clientState s₄ (writeDesc wdFinal) =
          ⟨Function.update (Function.update (Function.update
            (Function.update s₄.mem part.newLiveBuf outPair.1) (part.newLiveBuf + 1) outPair.2)
            (part.newLiveBuf + 2) entPair.1) (part.newLiveBuf + 3) entPair.2, s₄.frontier⟩ := rfl
      generalize hs₅ : (Memory.spec 0).clientState s₄ (writeDesc wdFinal) = s₅
        at hwd_fr_pair hst5_def
      obtain ⟨hs5_fr, hwd_out⟩ := hwd_fr_pair
      dsimp only [wdFinal] at hwd_out
      have hs1_le_dst : s₁.frontier ≤ part.newLiveBuf := by omega
      have hpres_15 : PreservesBelow s₁.frontier s₁ s₅ := by
        refine ⟨le_rfl, ?_, fun a ha => ?_⟩
        · rw [hs5_fr]
          exact hpl_pres.2.1.trans (hs2_le_s3.trans hs3_le_s4)
        · rw [hwd_out a (Or.inl (lt_of_lt_of_le ha hs1_le_dst))]
          rw [hboe_pres.2.2 a (lt_of_lt_of_le ha (hpl_pres.2.1.trans hs2_le_s3))]
          rw [hbos_pres.2.2 a (lt_of_lt_of_le ha hpl_pres.2.1)]
          exact hpl_pres.2.2 a ha
      have hpres_all : PreservesBelow s.frontier s s₅ :=
        hfn_pres.trans (hpres_15.mono_bound hfn_pres.2.1)
      have hnew_f : HoldsFactor part.newLiveBuf newTab s₅ := by
        have hm0 : s₅.mem part.newLiveBuf = outPair.1 := by
          rw [hst5_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        have hm1 : s₅.mem (part.newLiveBuf + 1) = outPair.2 := by
          rw [hst5_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        have hm2 : s₅.mem (part.newLiveBuf + 2) = entPair.1 := by
          rw [hst5_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]
        have hm3 : s₅.mem (part.newLiveBuf + 3) = entPair.2 := by
          rw [hst5_def]; dsimp only; rw [Function.update_self]
        unfold HoldsFactor
        rw [hm0, hm1, hm2, hm3]
        refine ⟨by rw [hs5_fr]; exact hwd_dst_lt, hbos_len, hboe_len, ?_, ?_⟩
        · refine ⟨by rw [hs5_fr]; exact hout_s4.1, hout_s4.2.frame fun a hlo _ => ?_⟩
          exact hwd_out a (Or.inr (hrBuf_le_s2.trans (hbos_lo.trans hlo)))
        · refine ⟨by rw [hs5_fr]; exact hboe_holds.1, hboe_holds.2.frame fun a hlo _ => ?_⟩
          exact hwd_out a (Or.inr (hrBuf_le_s2.trans (hs2_le_s3.trans (hboe_lo.trans hlo))))
      have hrest_s5 : HoldsFactorList (part.newLiveBuf + 4) rest s₅ := by
        have hpres_25 : PreservesBelow s₁.frontier s₂ s₅ := by
          refine ⟨hpl_pres.2.1, ?_, fun a ha => ?_⟩
          · rw [hs5_fr]; exact hs2_le_s3.trans hs3_le_s4
          · rw [hwd_out a (Or.inl (lt_of_lt_of_le ha hs1_le_dst))]
            rw [hboe_pres.2.2 a (lt_of_lt_of_le ha (hpl_pres.2.1.trans hs2_le_s3))]
            exact hbos_pres.2.2 a (lt_of_lt_of_le ha hpl_pres.2.1)
        exact hpl_rH.frame_outside hpl_rD hpres_25 fun a hlo hhi => by
          rw [hwd_out a (Or.inr hlo)]
          have hr_le : rest.length ≤ args.liveLen :=
            (List.length_filter_le _ _).trans (le_of_eq hlive_len.symm)
          have ha2 : a < s₂.frontier := by omega
          rw [hboe_pres.2.2 a (lt_of_lt_of_le ha2 hs2_le_s3)]
          exact hbos_pres.2.2 a ha2
      rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hms_st, ite_eq_right hin1,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hs₁, hremPair,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hs₂, hpart, ite_eq_right hp_bLen_ne,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hs₃, houtPair,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hs₄, hentPair,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hs₅, hpure_res, hpure_st, hes'_eq, hbk_eq]
      refine ⟨validHistory_bind_step hms_val ?_, hpres_all, ?_, ?_, ?_⟩
      · rw [hms_st, ite_eq_right hin1]
        refine validHistory_bind_step hfn_val ?_
        rw [hs₁, hremPair]
        refine validHistory_bind_step hpl_val ?_
        rw [hs₂, hpart, ite_eq_right hp_bLen_ne]
        refine validHistory_bind_step hbos_val ?_
        rw [hs₃, houtPair]
        refine validHistory_bind_step hboe_val ?_
        rw [hs₄, hentPair]
        refine validHistory_bind_step hwd_val ?_
        rw [hs₅]
        exact validHistory_pure w s₅ _
      · rw [hs5_fr]
        dsimp only [stepMemDelta]
        omega
      · refine ⟨lt_of_lt_of_le hs0 hpres_all.2.1, hsc_eq, ?_, hfn_len, ⟨hnew_f, hrest_s5⟩,
          hfn_holds.mono_frontier hpres_15⟩
        dsimp only
        rw [hpl_rLen, List.length_cons, Nat.add_comm]
      · rw [memoryCost_bind', hms_st, ite_eq_right hin1, memoryCost_bind',
          hs₁, hremPair, memoryCost_bind', hs₂, hpart, ite_eq_right hp_bLen_ne,
          memoryCost_bind', hs₃, houtPair, memoryCost_bind', hs₄, hentPair,
          memoryCost_bind', hs₅, writeDesc_cost, memoryCost_pure, Nat.add_zero]
        have hM_mul : args.liveLen * (8 + SW) ≤ M * (8 + SW) :=
          Nat.mul_le_mul_right _ (by omega)
        have hbos_c' :
            memoryCost (buildOutScope ⟨args.x, part.bucketPtr, part.bucketLen⟩) s₂ ≤
              2 + bucket.length * (3 + SW * (4 + W)) :=
          calc memoryCost (buildOutScope ⟨args.x, part.bucketPtr, part.bucketLen⟩) s₂
              ≤ 2 + part.bucketLen * (3 + 2 * SW + SW * (2 + W)) := hbos_cost
            _ = 2 + bucket.length * (3 + SW * (4 + W)) := by rw [hpl_bLen]; ring
        have hboe_c' :
            memoryCost (buildOutEntries
              ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩) s₃ ≤
              3 + W + 4 * (max 1 args.dom) ^ W +
                bucket.length * ((max 1 args.dom) ^ W * (5 + SW * W)) := by
          have h2_le : 5 + SW * (outPair.2 + 1) ≤ 5 + SW * W :=
            Nat.add_le_add_left (Nat.mul_le_mul_left SW hout_succ_le_W) 5
          calc memoryCost (buildOutEntries
                ⟨args.dom, args.x, outPair.1, outPair.2, part.bucketPtr, part.bucketLen⟩) s₃
              ≤ 3 + outPair.2 + (max 1 args.dom) ^ outPair.2 *
                  (3 + args.dom * (1 + part.bucketLen * (5 + SW * (outPair.2 + 1)))) := hboe_cost
            _ = 3 + outPair.2 + (max 1 args.dom) ^ outPair.2 * 3 +
                  ((max 1 args.dom) ^ outPair.2 * args.dom) * 1 +
                  bucket.length * (((max 1 args.dom) ^ outPair.2 * args.dom) *
                    (5 + SW * (outPair.2 + 1))) := by
                rw [hpl_bLen]; ring
            _ ≤ 3 + W + (max 1 args.dom) ^ W * 3 +
                  (max 1 args.dom) ^ W * 1 +
                  bucket.length * ((max 1 args.dom) ^ W * (5 + SW * W)) :=
                Nat.add_le_add
                  (Nat.add_le_add
                    (Nat.add_le_add (Nat.add_le_add_left hout_le_W' 3)
                      (Nat.mul_le_mul_right 3 hpow_out_le))
                    (Nat.mul_le_mul_right 1 hpow_joint_le))
                  (Nat.mul_le_mul_left _ (Nat.mul_le_mul hpow_joint_le h2_le))
            _ = 3 + W + 4 * (max 1 args.dom) ^ W +
                  bucket.length * ((max 1 args.dom) ^ W * (5 + SW * W)) := by ring
        have hunit_split : bucket.length * (3 + SW * (4 + W)) +
            bucket.length * ((max 1 args.dom) ^ W * (5 + SW * W)) =
            bucket.length * stepBucketUnitCost SW args.dom W := by
          dsimp only [stepBucketUnitCost]; ring
        dsimp only [stepFixedCost]
        omega
  · have hin0 : (Memory.spec 0).clientResult s (memScan msArgs) = 0 := by
      rw [hms_res, ite_eq_right hx]
    have hes'_eq : elimVar args.dom args.x es = es := by simp [elimVar, hx]
    have hbk_eq : (stepStats args.dom args.x es).bucketFactors = 0 := by simp [stepStats, hx]
    rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
      hms_st, ite_eq_left hin0, hpure_res, hpure_st, hes'_eq, hbk_eq]
    refine ⟨validHistory_bind_step hms_val ?_, PreservesBelow.refl le_rfl,
      Nat.le_add_right _ _, ⟨hs0, hsc_eq, hlive_len, hrem_len, hlive_h, hrem_h⟩, ?_⟩
    · rw [hms_st, ite_eq_left hin0]
      exact validHistory_pure w s _
    · rw [memoryCost_bind', hms_st, ite_eq_left hin0, memoryCost_pure, Nat.add_zero]
      dsimp only [stepFixedCost]
      omega

private theorem elimVarProg_realizes :
    Realizes .exact elimVarProg WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        Fits w 1 ∧
        ∃ es R M SW W B,
          HoldsElimState
            ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s ∧
          es.live.length ≤ M ∧
          es.remaining.length ≤ R ∧
          (∀ f ∈ es.live, f.scope.length ≤ SW) ∧
          (stepStats args.dom args.x es).jointScopeVars ≤ W ∧
          W ≤ SW ∧
          max 1 args.dom * stateCap es ≤ B ∧
          Fits w B ∧
          Fits w ((max 1 args.dom) ^ SW) ∧
          Fits w (s.frontier + stepMemDelta R M SW args.dom W))
      (fun _ _ => 0) := by
  unfold elimVarProg
  realize [memScan_realizes, filterNe_realizes, partitionLive_realizes,
    buildOutScope_realizes, buildOutEntries_realizes, writeDesc_realizes]
  all_goals
    obtain ⟨h1, es, R, M, SW, W, B, hes, hM, hR, hSW, hW, _hW_SW, hcapB, hB, hpowSW, hfit_fr⟩ := h
    obtain ⟨_hs0, hsc_eq, hlive_len, hrem_len, hlive_h, hrem_h⟩ := hes
    dsimp only at hsc_eq hlive_len hrem_len hlive_h hrem_h
    obtain ⟨hfn_val, hfn_fr, hfn_pres, _, _, _⟩ :=
      filterNe_spec (w := w) ⟨d.x, d.remPtr, d.remLen⟩ hmem hrem_h hrem_len.symm
        (hfit_fr.of_le (by dsimp only [stepMemDelta]; omega))
    dsimp only at hfn_fr
    have hwf₁ := wellFormed_clientState hmem hfn_val
    obtain ⟨hpl_val, hpl_fr, _, _, hpl_rBuf, hpl_bLen, hpl_rLen, hpl_bH, _, _, _, _⟩ :=
      partitionLive_spec (w := w) (args := ⟨d.x, d.livePtr, d.liveLen⟩) hwf₁
        (hlive_h.mono_frontier hfn_pres) hlive_len.symm hSW
        (hfit_fr.of_le (by rw [hfn_fr]; dsimp only [stepMemDelta]; omega))
    dsimp only at hpl_fr hpl_rBuf hpl_bLen hpl_rLen hpl_bH
    have hwf₂ := wellFormed_clientState hwf₁ hpl_val
    let s₁ := (Memory.spec 0).clientState s (filterNe ⟨d.x, d.remPtr, d.remLen⟩)
    let part := (Memory.spec 0).clientResult s₁ (partitionLive ⟨d.x, d.livePtr, d.liveLen⟩)
    let bucket := es.live.filter fun f => decide (d.x ∈ f.scope)
    have hb_SW : ∀ f ∈ bucket, f.scope.length ≤ SW :=
      fun f hf => hSW f (List.mem_filter.mp hf).1
    have hb_le_M : part.bucketLen ≤ M := by
      rw [hpl_bLen]; exact (List.length_filter_le _ _).trans hM
    obtain ⟨_, hbos_fr, hbos_pres, _, hbos_len, hbos_holds, _⟩ :=
      buildOutScope_spec (w := w) (args := ⟨d.x, part.bucketPtr, part.bucketLen⟩)
        hwf₂ hpl_bH hpl_bLen.symm hb_SW le_rfl
        (hfit_fr.of_le (by
          dsimp only [stepMemDelta]
          rw [hpl_fr, hfn_fr]
          have := Nat.mul_le_mul_right SW hb_le_M; omega))
    dsimp only [part, s₁] at hbos_fr hbos_len hbos_holds hb_le_M
  · exact h1
  · exact hfit_fr.of_le (by have := hrem_h.1; rw [← hrem_len] at this; omega)
  · exact hfit_fr.of_le (by have := hrem_h.1; rw [← hrem_len] at this; omega)
  · rw [memScan_state]
    exact hfit_fr.of_le (by dsimp only [stepMemDelta]; omega)
  · exact h1
  · rw [memScan_state, hfn_fr]
    exact hfit_fr.of_le (by dsimp only [stepMemDelta]; omega)
  · rw [memScan_state]
    exact ⟨es.live, hlive_len.symm, hlive_h.mono_frontier hfn_pres⟩
  · have hsc_le : d.scalar * d.dom ≤ B := by
      have h1_live : 1 ≤ (es.live.map capFactor).prod :=
        List.one_le_prod_of_one_le (by simp [one_le_capFactor])
      have hsc_m : d.scalar * d.dom ≤ max 1 d.dom * max 1 es.scalar := by
        rw [hsc_eq, Nat.mul_comm]
        exact Nat.mul_le_mul (le_max_right 1 d.dom) (le_max_right 1 es.scalar)
      calc d.scalar * d.dom ≤ max 1 d.dom * max 1 es.scalar := hsc_m
        _ ≤ (max 1 d.dom * max 1 es.scalar) * (es.live.map capFactor).prod :=
            Nat.le_mul_of_pos_right _ h1_live
        _ = max 1 d.dom * stateCap es := by unfold stateCap; ring
        _ ≤ B := hcapB
    exact hB.of_le hsc_le
  · exact h1
  · rw [memScan_state]
    have hK_le : (bucket.flatMap FactorTable.scope).length ≤ M * SW := by
      have hfl : (bucket.flatMap FactorTable.scope).length ≤ bucket.length * SW := by
        rw [List.length_flatMap]
        have hsum := List.sum_le_length_nsmul (bucket.map fun a => a.scope.length) SW
          fun _ hn => by
            rcases List.mem_map.mp hn with ⟨f, hf, rfl⟩
            exact hb_SW f hf
        simpa [smul_eq_mul] using hsum
      exact hfl.trans (Nat.mul_le_mul_right SW ((List.length_filter_le _ _).trans hM))
    refine ⟨bucket, hpl_bLen.symm, hpl_bH, hfit_fr.of_le ?_⟩
    rw [hpl_fr, hfn_fr]
    dsimp only [stepMemDelta]
    omega
  · rw [memScan_state]
    have hbd := hbos_holds.1
    rw [← hbos_len] at hbd
    exact hbd
  · rw [memScan_state] at hc ⊢
    have hms_res : (Memory.spec 0).clientResult s (memScan ⟨d.x, d.remPtr, d.remLen⟩) =
        if d.x ∈ es.remaining then 1 else 0 := memScan_result hrem_h.2 hrem_len.symm
    have hx : d.x ∈ es.remaining := by
      by_contra hnx
      have : (Memory.spec 0).clientResult s (memScan ⟨d.x, d.remPtr, d.remLen⟩) = 0 := by
        rw [hms_res, ite_eq_right hnx]
      exact absurd this ‹_›
    have hbk_ne : bucket.isEmpty = false := by
      cases hb_emp : bucket.isEmpty
      · rfl
      · exfalso
        have hb0 : bucket = [] := List.isEmpty_iff.mp hb_emp
        have hb0_len : bucket.length = 0 := by rw [hb0]; rfl
        have hbz : part.bucketLen = 0 := hpl_bLen.trans hb0_len
        exact absurd hbz hc
    have hj_le : (bucketJointScope bucket).length ≤ W := by
      simpa [stepStats, hx, hbk_ne, bucket] using hW
    have hout_le_W : (bucketOutScope d.x bucket).length ≤ W :=
      (List.length_filter_le _ _).trans hj_le
    have hpow_le : (max 1 d.dom) ^ ((Memory.spec 0).clientResult
        ((Memory.spec 0).clientState s₁ (partitionLive ⟨d.x, d.livePtr, d.liveLen⟩))
        (buildOutScope ⟨d.x, part.bucketPtr, part.bucketLen⟩)).2 ≤ (max 1 d.dom) ^ W := by
      dsimp only [part, s₁]
      rw [hbos_len]
      exact Nat.pow_le_pow_right (le_max_left 1 d.dom) hout_le_W
    dsimp only [part, s₁] at hpow_le
    refine hfit_fr.of_le ?_
    have hbmul := Nat.mul_le_mul_right SW hb_le_M
    rw [hpl_fr, hfn_fr] at hbos_fr
    dsimp only [stepMemDelta]
    omega
  · rw [memScan_state]
    exact ⟨bucket, B, SW, hpl_bLen.symm, hpl_bH.mono_frontier hbos_pres, hb_SW, hpowSW,
      (Nat.mul_le_mul_left _ (bucket_prod_le_stateCap d.x es)).trans hcapB, hB⟩
  · rw [memScan_state, hpl_rBuf, hfn_fr]
    exact hfit_fr.of_le (by dsimp only [stepMemDelta]; omega)
  · rw [memScan_state, hpl_rLen]
    have hr_le : (es.live.filter fun f => decide (d.x ∉ f.scope)).length ≤ M :=
      (List.length_filter_le _ _).trans hM
    exact hfit_fr.of_le (by dsimp only [stepMemDelta]; omega)

/-! ### Sequential elimination loop (`elimOrderLoop`) -/

private theorem scope_elimVar_le_of_le (d x : ℕ) (s : ElimState ℕ ℕ) {SW W : ℕ}
    (hs : ∀ f ∈ s.live, f.scope.length ≤ SW)
    (hstep : (stepStats d x s).jointScopeVars ≤ W) (hW_SW : W ≤ SW) :
    ∀ f ∈ (elimVar d x s).live, f.scope.length ≤ SW := by
  have h := scope_length_elimVar_le d x s (S := SW) (W := W)
    (fun f hf => (hs f hf).trans (le_max_left SW W)) hstep
  simpa [max_eq_left hW_SW] using h

private structure ElimLoopEnv where
  dom : ℕ
  orderPtr : ℕ

private def ElimLoopEnv.equiv : ElimLoopEnv ≃ ℕ × ℕ where
  toFun e := (e.dom, e.orderPtr)
  invFun := fun (dom, orderPtr) => ⟨dom, orderPtr⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ElimLoopEnv := .ofEquiv ElimLoopEnv.equiv

private structure ElimLoopState where
  idx : ℕ
  scalar : ℕ
  livePtr : ℕ
  liveLen : ℕ
  remPtr : ℕ
  remLen : ℕ

private def ElimLoopState.equiv :
    ElimLoopState ≃ ((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((s.idx, s.scalar), s.livePtr), s.liveLen), s.remPtr), s.remLen)
  invFun := fun (((((idx, scalar), livePtr), liveLen), remPtr), remLen) =>
    ⟨idx, scalar, livePtr, liveLen, remPtr, remLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ElimLoopState := .ofEquiv ElimLoopState.equiv

private structure ElimOrderArgs where
  dom : ℕ
  orderPtr : ℕ
  orderLen : ℕ
  scalar : ℕ
  livePtr : ℕ
  liveLen : ℕ
  remPtr : ℕ
  remLen : ℕ

private def ElimOrderArgs.equiv :
    ElimOrderArgs ≃ ((((((ℕ × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ where
  toFun s := (((((((s.dom, s.orderPtr), s.orderLen), s.scalar), s.livePtr), s.liveLen), s.remPtr),
    s.remLen)
  invFun := fun (((((((dom, orderPtr), orderLen), scalar), livePtr), liveLen), remPtr), remLen) =>
    ⟨dom, orderPtr, orderLen, scalar, livePtr, liveLen, remPtr, remLen⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding ElimOrderArgs := .ofEquiv ElimOrderArgs.equiv

private def elimOrderStep : ElimLoopEnv × ElimLoopState → Memory.Prog ElimLoopState :=
  fun ⟨env, st⟩ =>
    Memory.read (env.orderPtr + st.idx) >>= fun x =>
    elimVarProg ⟨env.dom, x, st.scalar, st.livePtr, st.liveLen, st.remPtr, st.remLen⟩ >>=
      fun st' =>
    pure ⟨st.idx + 1, st'.scalar, st'.livePtr, st'.liveLen, st'.remPtr, st'.remLen⟩

private def elimOrderLoop (args : ElimOrderArgs) : Memory.Prog ElimLoopState :=
  iterate elimOrderStep ⟨args.dom, args.orderPtr⟩ args.orderLen
    ⟨0, args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩

private theorem holdsIn_cons_shift {base : ℕ} {x : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base (x :: xs) s) :
    base < s.frontier ∧ s.mem base = x ∧ HoldsIn (base + 1) xs s := by
  obtain ⟨hb, hl⟩ := h
  simp only [List.length_cons] at hb
  obtain ⟨hx, hxs⟩ := Block.holdsList_cons_iff.mp hl
  exact ⟨by omega, hx, by omega, hxs⟩

private theorem elimOrderLoop_aux {w : ℕ} (env : ElimLoopEnv)
    {R M SW W B : ℕ} (hW_SW : W ≤ SW) (hB : Fits w B) (h1 : Fits w 1)
    (hpowSW : Fits w ((max 1 env.dom) ^ SW)) :
    ∀ (ord : List ℕ) (idx : ℕ) (st0 : ElimStepState) (es : ElimState ℕ ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      HoldsIn (env.orderPtr + idx) ord t →
      HoldsElimState st0 es t →
      es.live.length ≤ M →
      es.remaining.length ≤ R →
      (∀ f ∈ es.live, f.scope.length ≤ SW) →
      (∀ s_st ∈ traceOrder env.dom ord es, s_st.jointScopeVars ≤ W) →
      (max 1 env.dom) ^ ord.length * stateCap es ≤ B →
      Fits w (t.frontier + ord.length * stepMemDelta R M SW env.dom W) →
      let st_in : ElimLoopState :=
        ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩
      let p := iterate elimOrderStep env ord.length st_in
      let r := (Memory.spec 0).clientResult t p
      let t' := (Memory.spec 0).clientState t p
      let es' := eliminateOrder env.dom ord es
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        PreservesBelow t.frontier t t' ∧
        t'.frontier ≤ t.frontier + ord.length * stepMemDelta R M SW env.dom W ∧
        HoldsElimState ⟨r.scalar, r.livePtr, r.liveLen, r.remPtr, r.remLen⟩ es' t' ∧
        memoryCost p t ≤
          ord.length * (1 + stepFixedCost R M SW env.dom W) +
            ((traceOrder env.dom ord es).map ElimStepStats.bucketFactors).sum *
              stepBucketUnitCost SW env.dom W
  | [], idx, st0, es, t, _, _, hes, _, _, _, _, _, _ => by
      dsimp only
      have h0 : iterate elimOrderStep env 0
          ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩ =
          pure ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩ := rfl
      simp only [List.length_nil]
      rw [h0]
      exact ⟨validHistory_pure w t _, PreservesBelow.refl le_rfl, Nat.le_add_right _ _, hes,
        by simp [memoryCost_pure, traceOrder]⟩
  | x :: xs, idx, st0, es, t, hwf, hord, hes, hM, hR, hSW, hW_all, hcap, hfit_fr => by
      dsimp only
      obtain ⟨hrd_lt, hm_x, hord_tail⟩ := holdsIn_cons_shift hord
      have hW_head : (stepStats env.dom x es).jointScopeVars ≤ W :=
        hW_all _ (by simp [traceOrder])
      have hW_tail : ∀ s_st ∈ traceOrder env.dom xs (elimVar env.dom x es),
          s_st.jointScopeVars ≤ W :=
        fun s_st hs => hW_all s_st (by simp [traceOrder, hs])
      simp only [List.length_cons] at hcap hfit_fr ⊢
      have hpow_pos : 1 ≤ (max 1 env.dom) ^ xs.length :=
        Nat.one_le_pow _ _ (le_max_left 1 env.dom)
      have hcap_step : max 1 env.dom * stateCap es ≤ B := by
        have hmul : 1 * (max 1 env.dom * stateCap es) ≤
            (max 1 env.dom) ^ xs.length * (max 1 env.dom * stateCap es) :=
          Nat.mul_le_mul_right _ hpow_pos
        have heq : (max 1 env.dom) ^ xs.length * (max 1 env.dom * stateCap es) =
            (max 1 env.dom) ^ (xs.length + 1) * stateCap es := by rw [Nat.pow_succ]; ring
        omega
      have hdelta_one : t.frontier + stepMemDelta R M SW env.dom W ≤
          t.frontier + (xs.length + 1) * stepMemDelta R M SW env.dom W := by
        rw [Nat.succ_mul]; omega
      let vpArgs : ElimVarArgs :=
        ⟨env.dom, x, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩
      have hvp := elimVarProg_spec (w := w) (args := vpArgs) hwf hes hM hR hSW hW_head hW_SW
        hcap_step hB h1 hpowSW (hfit_fr.of_le hdelta_one)
      dsimp only at hvp
      generalize ht₁ : (Memory.spec 0).clientState t (elimVarProg vpArgs) = t₁ at hvp
      generalize hst₁ : (Memory.spec 0).clientResult t (elimVarProg vpArgs) = st₁ at hvp
      obtain ⟨hvp_val, hvp_pres, hvp_fr, hvp_es, hvp_cost⟩ := hvp
      dsimp only [vpArgs] at hvp_fr hvp_es hvp_cost
      have hwf₁ : Memory.WellFormed w t₁ :=
        by rw [← ht₁]; exact wellFormed_clientState hwf hvp_val
      have hord_t₁ : HoldsIn (env.orderPtr + (idx + 1)) xs t₁ := by
        rw [show env.orderPtr + (idx + 1) = env.orderPtr + idx + 1 by omega]
        exact hord_tail.mono_frontier hvp_pres
      have hM₁ : (elimVar env.dom x es).live.length ≤ M :=
        (length_elimVar_live_le env.dom x es).trans hM
      have hR₁ : (elimVar env.dom x es).remaining.length ≤ R :=
        (length_elimVar_remaining_le env.dom x es).trans hR
      have hSW₁ : ∀ f ∈ (elimVar env.dom x es).live, f.scope.length ≤ SW :=
        scope_elimVar_le_of_le env.dom x es hSW hW_head hW_SW
      have hcap₁ : (max 1 env.dom) ^ xs.length * stateCap (elimVar env.dom x es) ≤ B := by
        calc (max 1 env.dom) ^ xs.length * stateCap (elimVar env.dom x es)
            ≤ (max 1 env.dom) ^ xs.length * (max 1 env.dom * stateCap es) :=
              Nat.mul_le_mul_left _ (stateCap_elimVar_le env.dom x es)
          _ = (max 1 env.dom) ^ (xs.length + 1) * stateCap es := by rw [Nat.pow_succ]; ring
          _ ≤ B := hcap
      have hfit₁ : Fits w (t₁.frontier + xs.length * stepMemDelta R M SW env.dom W) := by
        refine hfit_fr.of_le ?_
        rw [Nat.succ_mul]
        omega
      have hih := elimOrderLoop_aux env hW_SW hB h1 hpowSW xs (idx + 1) st₁
        (elimVar env.dom x es) t₁ hwf₁ hord_t₁ hvp_es hM₁ hR₁ hSW₁ hW_tail hcap₁ hfit₁
      dsimp only at hih
      obtain ⟨hih_val, hih_pres, hih_fr, hih_es, hih_cost⟩ := hih
      have hr_st (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hr_res (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hpure_st {α : Type} (y : α) (u : Memory.State) :
          (Memory.spec 0).clientState u (pure y) = u := rfl
      have hpure_res {α : Type} (y : α) (u : Memory.State) :
          (Memory.spec 0).clientResult u (pure y) = y := rfl
      have hstep_st : (Memory.spec 0).clientState t
          (elimOrderStep (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr,
            st0.remLen⟩)) = t₁ := by
        unfold elimOrderStep
        dsimp only
        rw [StateTransitionSpec.clientState_bind, hr_st, hr_res, hm_x,
          StateTransitionSpec.clientState_bind, ht₁, hst₁, hpure_st]
      have hstep_res : (Memory.spec 0).clientResult t
          (elimOrderStep (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr,
            st0.remLen⟩)) =
          ⟨idx + 1, st₁.scalar, st₁.livePtr, st₁.liveLen, st₁.remPtr, st₁.remLen⟩ := by
        unfold elimOrderStep
        dsimp only
        rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm_x,
          StateTransitionSpec.clientResult_bind, ht₁, hst₁, hpure_res]
      have hstep_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (elimOrderStep
            (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩))) := by
        unfold elimOrderStep
        dsimp only
        refine validHistory_read_bind hrd_lt ?_
        rw [hm_x]
        refine validHistory_bind_step hvp_val ?_
        rw [ht₁, hst₁]
        exact validHistory_pure w t₁ _
      have hstep_cost : memoryCost (elimOrderStep
          (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩)) t ≤
          1 + stepFixedCost R M SW env.dom W +
            (stepStats env.dom x es).bucketFactors * stepBucketUnitCost SW env.dom W := by
        unfold elimOrderStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, hm_x,
          memoryCost_bind', ht₁, hst₁, memoryCost_pure, Nat.add_zero]
        omega
      have hiter_eq : iterate elimOrderStep env (xs.length + 1)
          ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩ =
          (elimOrderStep
            (env, ⟨idx, st0.scalar, st0.livePtr, st0.liveLen, st0.remPtr, st0.remLen⟩) >>=
            iterate elimOrderStep env xs.length) := rfl
      rw [hiter_eq, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind,
        hstep_st, hstep_res]
      refine ⟨validHistory_bind_step hstep_val ?_,
        hvp_pres.trans (hih_pres.mono_bound hvp_pres.2.1),
        by rw [Nat.succ_mul]; omega,
        hih_es, ?_⟩
      · rw [hstep_st, hstep_res]
        exact hih_val
      · rw [memoryCost_bind', hstep_st, hstep_res]
        simp only [traceOrder, List.map_cons, List.sum_cons]
        calc memoryCost _ t + _
            ≤ (1 + stepFixedCost R M SW env.dom W +
                (stepStats env.dom x es).bucketFactors * stepBucketUnitCost SW env.dom W) +
              (xs.length * (1 + stepFixedCost R M SW env.dom W) +
                ((traceOrder env.dom xs (elimVar env.dom x es)).map
                  ElimStepStats.bucketFactors).sum * stepBucketUnitCost SW env.dom W) :=
              Nat.add_le_add hstep_cost hih_cost
          _ = (xs.length + 1) * (1 + stepFixedCost R M SW env.dom W) +
                ((stepStats env.dom x es).bucketFactors +
                  ((traceOrder env.dom xs (elimVar env.dom x es)).map
                    ElimStepStats.bucketFactors).sum) * stepBucketUnitCost SW env.dom W := by ring

private theorem elimOrderLoop_spec {w : ℕ} {args : ElimOrderArgs}
    {ord : List ℕ} {es : ElimState ℕ ℕ} {R M SW W B : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hord : HoldsIn args.orderPtr ord s) (hord_len : ord.length = args.orderLen)
    (hes : HoldsElimState ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s)
    (hM : es.live.length ≤ M) (hR : es.remaining.length ≤ R)
    (hSW : ∀ f ∈ es.live, f.scope.length ≤ SW)
    (hW : ∀ st ∈ traceOrder args.dom ord es, st.jointScopeVars ≤ W) (hW_SW : W ≤ SW)
    (hcap : (max 1 args.dom) ^ args.orderLen * stateCap es ≤ B)
    (hB : Fits w B) (h1 : Fits w 1) (hpowSW : Fits w ((max 1 args.dom) ^ SW))
    (hfit_fr : Fits w (s.frontier + args.orderLen * stepMemDelta R M SW args.dom W)) :
    let r := (Memory.spec 0).clientResult s (elimOrderLoop args)
    let s' := (Memory.spec 0).clientState s (elimOrderLoop args)
    let es' := eliminateOrder args.dom ord es
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (elimOrderLoop args)) ∧
      PreservesBelow s.frontier s s' ∧
      s'.frontier ≤ s.frontier + args.orderLen * stepMemDelta R M SW args.dom W ∧
      HoldsElimState ⟨r.scalar, r.livePtr, r.liveLen, r.remPtr, r.remLen⟩ es' s' ∧
      memoryCost (elimOrderLoop args) s ≤
        args.orderLen * (1 + stepFixedCost R M SW args.dom W) +
          (M + args.orderLen) * stepBucketUnitCost SW args.dom W := by
  dsimp only
  unfold elimOrderLoop
  rw [← hord_len] at hcap hfit_fr ⊢
  have hord0 : HoldsIn (args.orderPtr + 0) ord s := by simpa using hord
  obtain ⟨hval, hpres, hfr, hes', hcost⟩ :=
    elimOrderLoop_aux (w := w) ⟨args.dom, args.orderPtr⟩ hW_SW hB h1 hpowSW ord 0
      ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s
      hwf hord0 hes hM hR hSW hW hcap hfit_fr
  refine ⟨hval, hpres, hfr, hes', ?_⟩
  have hbk_sum : ((traceOrder args.dom ord es).map ElimStepStats.bucketFactors).sum ≤
      M + ord.length := by
    have hsb := sum_bucketFactors_le args.dom ord es
    omega
  exact hcost.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hbk_sum) _)

private theorem elimOrderLoop_realizes :
    Realizes .exact elimOrderLoop WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        ∃ ord es R M SW W B,
          Fits w 1 ∧
          ord.length = args.orderLen ∧
          HoldsIn args.orderPtr ord s ∧
          HoldsElimState
            ⟨args.scalar, args.livePtr, args.liveLen, args.remPtr, args.remLen⟩ es s ∧
          es.live.length ≤ M ∧
          es.remaining.length ≤ R ∧
          (∀ f ∈ es.live, f.scope.length ≤ SW) ∧
          (∀ st ∈ traceOrder args.dom ord es, st.jointScopeVars ≤ W) ∧
          W ≤ SW ∧
          (max 1 args.dom) ^ args.orderLen * stateCap es ≤ B ∧
          Fits w B ∧
          Fits w ((max 1 args.dom) ^ SW) ∧
          Fits w (s.frontier + args.orderLen * stepMemDelta R M SW args.dom W))
      (fun _ _ => 0) := by
  unfold elimOrderLoop
  realize [elimVarProg_realizes]
  obtain ⟨ord₀, es₀, R, M, SW, W, B, h1, hord_len, hord₀, hes₀, hM₀, hR₀, hSW₀,
    hW₀, hW_SW, hcap₀, hB, hpowSW, hfit_fr⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : ElimLoopState) (t : Memory.State) =>
      Memory.WellFormed w t ∧
      st.idx + j = d.orderLen ∧
      ∃ ord es,
        ord.length = j ∧
        HoldsIn (d.orderPtr + st.idx) ord t ∧
        HoldsElimState ⟨st.scalar, st.livePtr, st.liveLen, st.remPtr, st.remLen⟩ es t ∧
        es.live.length ≤ M ∧
        es.remaining.length ≤ R ∧
        (∀ f ∈ es.live, f.scope.length ≤ SW) ∧
        (∀ s_st ∈ traceOrder d.dom ord es, s_st.jointScopeVars ≤ W) ∧
        (max 1 d.dom) ^ j * stateCap es ≤ B ∧
        Fits w (t.frontier + j * stepMemDelta R M SW d.dom W))
    (fun j st t ⟨hwf_t, hidx_sum, ord, es, hlen_j, hord_t, hes_t, hM_t, hR_t, hSW_t,
      hW_t, hcap_t, hfit_t⟩ => ?_)
    ⟨hmem, Nat.zero_add _, ord₀, es₀, hord_len, by simpa using hord₀, hes₀, hM₀, hR₀, hSW₀,
      hW₀, hcap₀, hfit_fr⟩
  dsimp only
  rcases ord with _ | ⟨x, xs⟩
  · cases hlen_j
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen_j
  subst hlen_j
  obtain ⟨hrd_lt, hm_x, hord_tail⟩ := holdsIn_cons_shift hord_t
  have hW_head : (stepStats d.dom x es).jointScopeVars ≤ W := hW_t _ (by simp [traceOrder])
  have hW_tail : ∀ s_st ∈ traceOrder d.dom xs (elimVar d.dom x es), s_st.jointScopeVars ≤ W :=
    fun s_st hs => hW_t s_st (by simp [traceOrder, hs])
  have hpow_pos : 1 ≤ (max 1 d.dom) ^ xs.length := Nat.one_le_pow _ _ (le_max_left 1 d.dom)
  have hcap_step : max 1 d.dom * stateCap es ≤ B := by
    have hmul : 1 * (max 1 d.dom * stateCap es) ≤
        (max 1 d.dom) ^ xs.length * (max 1 d.dom * stateCap es) :=
      Nat.mul_le_mul_right _ hpow_pos
    have heq : (max 1 d.dom) ^ xs.length * (max 1 d.dom * stateCap es) =
        (max 1 d.dom) ^ (xs.length + 1) * stateCap es := by rw [Nat.pow_succ]; ring
    omega
  have hfit_one : Fits w (t.frontier + stepMemDelta R M SW d.dom W) :=
    hfit_t.of_le (by rw [Nat.succ_mul]; omega)
  have hr_st (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
  have hr_res (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
  have hpure_st {α : Type} (y : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure y) = u := rfl
  have hpure_res {α : Type} (y : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure y) = y := rfl
  refine ⟨?_, ?_⟩
  · refine ⟨hwf_t.frontier_fits.of_le hrd_lt.le, ?_, ?_⟩
    · simp only [hm_x]
      exact ⟨h1, es, R, M, SW, W, B, hes_t, hM_t, hR_t, hSW_t, hW_head, hW_SW,
        hcap_step, hB, hpowSW, hfit_one⟩
    · have hidx_lt : st.idx + 1 ≤ t.frontier := by
        have hbd := hord_t.1
        simp only [List.length_cons] at hbd
        omega
      exact hwf_t.frontier_fits.of_le hidx_lt
  · let vpArgs : ElimVarArgs :=
      ⟨d.dom, x, st.scalar, st.livePtr, st.liveLen, st.remPtr, st.remLen⟩
    have hvp := elimVarProg_spec (w := w) (args := vpArgs) hwf_t hes_t hM_t hR_t hSW_t
      hW_head hW_SW hcap_step hB h1 hpowSW hfit_one
    dsimp only at hvp
    generalize ht₁ : (Memory.spec 0).clientState t (elimVarProg vpArgs) = t₁ at hvp
    generalize hst₁ : (Memory.spec 0).clientResult t (elimVarProg vpArgs) = st₁ at hvp
    obtain ⟨hvp_val, hvp_pres, hvp_fr, hvp_es, _⟩ := hvp
    dsimp only [vpArgs] at hvp_fr hvp_es
    have hwf₁ : Memory.WellFormed w t₁ :=
      by rw [← ht₁]; exact wellFormed_clientState hwf_t hvp_val
    unfold elimOrderStep
    dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      hr_st, hr_res, hm_x,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      ht₁, hst₁, hpure_st, hpure_res]
    refine ⟨hwf₁, by dsimp only; omega, xs, elimVar d.dom x es, rfl, ?_, hvp_es,
      (length_elimVar_live_le d.dom x es).trans hM_t,
      (length_elimVar_remaining_le d.dom x es).trans hR_t,
      scope_elimVar_le_of_le d.dom x es hSW_t hW_head hW_SW,
      hW_tail, ?_, ?_⟩
    · dsimp only
      rw [show d.orderPtr + (st.idx + 1) = d.orderPtr + st.idx + 1 by omega]
      exact hord_tail.mono_frontier hvp_pres
    · calc (max 1 d.dom) ^ xs.length * stateCap (elimVar d.dom x es)
          ≤ (max 1 d.dom) ^ xs.length * (max 1 d.dom * stateCap es) :=
            Nat.mul_le_mul_left _ (stateCap_elimVar_le d.dom x es)
        _ = (max 1 d.dom) ^ (xs.length + 1) * stateCap es := by rw [Nat.pow_succ]; ring
        _ ≤ B := hcap_t
    · refine hfit_t.of_le ?_
      rw [Nat.succ_mul]
      omega

/-! ### Final scalar-table product (`finalResultProd`) and factor parsing (`initFactors`) -/

private theorem getD_zero_le_capFactor (f : FactorTable ℕ ℕ) :
    f.entries.getD 0 0 ≤ capFactor f := by
  unfold Array.getD capFactor
  split_ifs with h0
  · refine le_trans ?_ (le_max_right 1 _)
    have hmem : f.entries[0] ∈ f.entries.toList := by
      rw [← Array.getElem_toList (xs := f.entries) (i := 0) (by simpa using h0)]
      exact List.getElem_mem _
    exact List.mem_le_foldl_max hmem
  · omega

private structure FinalProdArgs where
  livePtr : ℕ
  liveLen : ℕ
  scalar : ℕ

private def FinalProdArgs.equiv : FinalProdArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.livePtr, a.liveLen), a.scalar)
  invFun := fun ((livePtr, liveLen), scalar) => ⟨livePtr, liveLen, scalar⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding FinalProdArgs := .ofEquiv FinalProdArgs.equiv

private def finalProdStep : Unit × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ) :=
  fun ⟨_, (curDesc, acc)⟩ =>
    Memory.read (curDesc + 2) >>= fun enPtr =>
    Memory.read (curDesc + 3) >>= fun enLen =>
    (if enLen = 0 then pure 0 else Memory.read enPtr) >>= fun e0 =>
    pure (curDesc + 4, acc * e0)

private def finalResultProd (args : FinalProdArgs) : Memory.Prog ℕ :=
  iterate finalProdStep () args.liveLen (args.livePtr, args.scalar) >>= fun res =>
  pure res.2

private theorem finalResultProd_aux {w B : ℕ} (hB : Fits w B) {s : Memory.State} :
    ∀ (rem : List (FactorTable ℕ ℕ)) (cur acc : ℕ),
      HoldsFactorList cur rem s →
      acc * (rem.map capFactor).prod ≤ B →
      let p := iterate finalProdStep () rem.length (cur, acc)
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s p) ∧
        (Memory.spec 0).clientState s p = s ∧
        ((Memory.spec 0).clientResult s p).2 =
          acc * (rem.map fun f => f.entries.getD 0 0).prod ∧
        memoryCost p s ≤ 3 * rem.length
  | [], cur, acc, _, _ => by
      dsimp only
      have h0 : iterate finalProdStep () 0 (cur, acc) = pure (cur, acc) := rfl
      simp only [List.length_nil]
      rw [h0]
      exact ⟨validHistory_pure w s _, rfl,
        by simp only [List.map_nil, List.prod_nil, Nat.mul_one]; rfl,
        by simp [memoryCost_pure]⟩
  | f :: rest, cur, acc, ⟨hf, hrest⟩, hcap => by
      dsimp only
      obtain ⟨hd, _, hel, _, hent⟩ := hf
      simp only [List.map_cons, List.prod_cons] at hcap ⊢
      have he0_le : f.entries.getD 0 0 ≤ capFactor f := getD_zero_le_capFactor f
      have hcap' : (acc * f.entries.getD 0 0) * (rest.map capFactor).prod ≤ B := by
        calc (acc * f.entries.getD 0 0) * (rest.map capFactor).prod
            ≤ (acc * capFactor f) * (rest.map capFactor).prod :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he0_le)
          _ = acc * (capFactor f * (rest.map capFactor).prod) := Nat.mul_assoc _ _ _
          _ ≤ B := hcap
      obtain ⟨hih_val, hih_st, hih_res, hih_cost⟩ :=
        finalResultProd_aux hB rest (cur + 4) (acc * f.entries.getD 0 0) hrest hcap'
      have hr_st (addr : ℕ) : (Memory.spec 0).clientState s (Memory.read addr) = s := rfl
      have hr_res (addr : ℕ) : (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl
      have hpure_st {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientState u (pure x) = u := rfl
      have hpure_res {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientResult u (pure x) = x := rfl
      have hbr_spec :
          let br : Memory.Prog ℕ :=
            if s.mem (cur + 3) = 0 then pure 0 else Memory.read (s.mem (cur + 2))
          (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s br) ∧
            (Memory.spec 0).clientState s br = s ∧
            (Memory.spec 0).clientResult s br = f.entries.getD 0 0 ∧
            memoryCost br s ≤ 1 := by
        dsimp only
        by_cases hz : s.mem (cur + 3) = 0
        · rw [ite_eq_left hz]
          have hsz0 : ¬ (0 < f.entries.size) := by omega
          have hget0 : f.entries.getD 0 0 = 0 := by simp [Array.getD, hsz0]
          exact ⟨validHistory_pure w s 0, rfl, hget0.symm, by rw [memoryCost_pure]; omega⟩
        · rw [ite_eq_right hz]
          have hsz_pos : 0 < f.entries.size := by omega
          have hlt_fr : s.mem (cur + 2) < s.frontier := by
            have hbd := hent.1
            rw [Array.length_toList] at hbd
            omega
          have hmem0 : s.mem (s.mem (cur + 2)) = f.entries.getD 0 0 := by
            have h0 := hent.2.get 0 (by rw [Array.length_toList]; exact hsz_pos)
            simp only [Nat.add_zero, Array.getElem_toList] at h0
            simp only [Array.getD, hsz_pos, ↓reduceDIte]
            exact h0
          exact ⟨validHistory_read hlt_fr, rfl, hmem0, by rw [memoryCost_read]⟩
      obtain ⟨hbr_val, hbr_st, hbr_res, hbr_cost⟩ := hbr_spec
      have hstep_val : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (finalProdStep ((), (cur, acc)))) := by
        unfold finalProdStep
        dsimp only
        refine validHistory_read_bind (by omega) ?_
        refine validHistory_read_bind (by omega) ?_
        exact validHistory_bind_step hbr_val (validHistory_pure w _ _)
      have hstep_st : (Memory.spec 0).clientState s (finalProdStep ((), (cur, acc))) = s := by
        unfold finalProdStep
        dsimp only
        rw [StateTransitionSpec.clientState_bind, hr_st, hr_res,
          StateTransitionSpec.clientState_bind, hr_st, hr_res,
          StateTransitionSpec.clientState_bind, hbr_st, hbr_res, hpure_st]
      have hstep_res : (Memory.spec 0).clientResult s (finalProdStep ((), (cur, acc))) =
          (cur + 4, acc * f.entries.getD 0 0) := by
        unfold finalProdStep
        dsimp only
        rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res,
          StateTransitionSpec.clientResult_bind, hr_st, hr_res,
          StateTransitionSpec.clientResult_bind, hbr_st, hbr_res, hpure_res]
      have hstep_cost : memoryCost (finalProdStep ((), (cur, acc))) s ≤ 3 := by
        unfold finalProdStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, hr_st, hr_res,
          memoryCost_bind', memoryCost_read, hr_st, hr_res,
          memoryCost_bind', hbr_st, hbr_res, memoryCost_pure, Nat.add_zero]
        omega
      simp only [List.length_cons]
      have hiter_eq : iterate finalProdStep () (rest.length + 1) (cur, acc) =
          (finalProdStep ((), (cur, acc)) >>= iterate finalProdStep () rest.length) := rfl
      rw [hiter_eq, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        hstep_st, hstep_res, hih_st, hih_res, Nat.mul_assoc]
      refine ⟨validHistory_bind_step hstep_val ?_, rfl, rfl, ?_⟩
      · rw [hstep_st, hstep_res]; exact hih_val
      · rw [memoryCost_bind', hstep_st, hstep_res]; omega

private theorem finalResultProd_spec {w B : ℕ} {args : FinalProdArgs}
    {es : ElimState ℕ ℕ} {s : Memory.State}
    (hB : Fits w B) (hcap : stateCap es ≤ B)
    (hsc : args.scalar = es.scalar) (hlen : args.liveLen = es.live.length)
    (hlive : HoldsFactorList args.livePtr es.live s) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (finalResultProd args)) ∧
      (Memory.spec 0).clientState s (finalResultProd args) = s ∧
      (Memory.spec 0).clientResult s (finalResultProd args) = es.result ∧
      memoryCost (finalResultProd args) s ≤ 3 * args.liveLen := by
  unfold finalResultProd
  rw [hlen, hsc]
  have hcap0 : es.scalar * (es.live.map capFactor).prod ≤ B :=
    (Nat.mul_le_mul_right _ (le_max_right 1 es.scalar)).trans hcap
  obtain ⟨hval, hst, hres, hcost⟩ := finalResultProd_aux hB es.live args.livePtr es.scalar
    hlive hcap0
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hst, hpure_st, hpure_res, hres]
  refine ⟨validHistory_bind_step hval (by rw [hst]; exact validHistory_pure w s _),
    rfl, rfl, ?_⟩
  rw [memoryCost_bind', hst, memoryCost_pure, Nat.add_zero]
  exact hcost

private theorem finalResultProd_realizes :
    Realizes .exact finalResultProd WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        ∃ live B,
          Fits w 4 ∧
          live.length = args.liveLen ∧
          HoldsFactorList args.livePtr live s ∧
          args.scalar * (live.map capFactor).prod ≤ B ∧
          Fits w B)
      (fun _ _ => 0) := by
  unfold finalResultProd
  realize
  obtain ⟨live₀, B, h4, hlen₀, hlive₀, hcap₀, hB⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : ℕ × ℕ) (t : Memory.State) =>
      t = s ∧
      ∃ rem,
        rem.length = j ∧
        HoldsFactorList st.1 rem s ∧
        st.2 * (rem.map capFactor).prod ≤ B)
    (fun j st t ⟨ht_eq, rem, hrem_l, hrem_h, hcap_t⟩ => ?_)
    ⟨rfl, live₀, hlen₀, hlive₀, hcap₀⟩
  dsimp only
  rcases ht_eq.symm with rfl
  rcases rem with _ | ⟨f, rest⟩
  · cases hrem_l
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
  subst hrem_l
  obtain ⟨hf, hrest⟩ := hrem_h
  obtain ⟨hd, _, hel, _, hent⟩ := hf
  simp only [List.map_cons, List.prod_cons] at hcap_t
  have hr_st (addr : ℕ) : (Memory.spec 0).clientState s (Memory.read addr) = s := rfl
  have hr_res (addr : ℕ) : (Memory.spec 0).clientResult s (Memory.read addr) = s.mem addr := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  have hbr_eq :
      let br : Memory.Prog ℕ :=
        if s.mem (st.1 + 3) = 0 then pure 0 else Memory.read (s.mem (st.1 + 2))
      (Memory.spec 0).clientState s br = s ∧
        (Memory.spec 0).clientResult s br = f.entries.getD 0 0 := by
    dsimp only
    by_cases hz : s.mem (st.1 + 3) = 0
    · rw [ite_eq_left hz]
      have hsz0 : ¬ (0 < f.entries.size) := by omega
      have hget0 : f.entries.getD 0 0 = 0 := by simp [Array.getD, hsz0]
      exact ⟨rfl, hget0.symm⟩
    · rw [ite_eq_right hz]
      have hsz_pos : 0 < f.entries.size := by omega
      have h0 := hent.2.get 0 (by rw [Array.length_toList]; exact hsz_pos)
      simp only [Nat.add_zero, Array.getElem_toList] at h0
      simp only [Array.getD, hsz_pos, ↓reduceDIte]
      exact ⟨rfl, h0⟩
  obtain ⟨hbr_st, hbr_res⟩ := hbr_eq
  have he0_le : f.entries.getD 0 0 ≤ capFactor f := getD_zero_le_capFactor f
  have hcap' : (st.2 * f.entries.getD 0 0) * (rest.map capFactor).prod ≤ B := by
    calc (st.2 * f.entries.getD 0 0) * (rest.map capFactor).prod
        ≤ (st.2 * capFactor f) * (rest.map capFactor).prod :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ he0_le)
      _ = st.2 * (capFactor f * (rest.map capFactor).prod) := Nat.mul_assoc _ _ _
      _ ≤ B := hcap_t
  have hprod_le : st.2 * f.entries.getD 0 0 ≤ B := by
    have h1_rest : 1 ≤ (rest.map capFactor).prod :=
      List.one_le_prod_of_one_le (by simp [one_le_capFactor])
    exact (Nat.le_mul_of_pos_right _ h1_rest).trans hcap'
  refine ⟨?_, ?_⟩
  · refine ⟨hmem.frontier_fits.of_le (by omega), hmem.frontier_fits.of_le (by omega), ?_, ?_⟩
    · split_ifs
    · rw [hbr_res]
      exact ⟨hmem.frontier_fits.of_le (by omega), hB.of_le hprod_le⟩
  · unfold finalProdStep
    dsimp only
    rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      hr_st, hr_res,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      hr_st, hr_res,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
      hbr_st, hbr_res, hpure_res]
    exact ⟨rfl, rest, rfl, hrest, hcap'⟩

/-- Word-array serialization of a factor table: `[f.scope.length, f.entries.size] ++ f.scope ++
f.entries.toList`. -/
@[expose] def encodeFactor (f : FactorTable ℕ ℕ) : List ℕ :=
  [f.scope.length, f.entries.size] ++ f.scope ++ f.entries.toList

private theorem holdsIn_append_split {base : ℕ} {xs ys : List ℕ} {s : Memory.State}
    (h : HoldsIn base (xs ++ ys) s) :
    HoldsIn base xs s ∧ HoldsIn (base + xs.length) ys s := by
  obtain ⟨hb, hl⟩ := h
  simp only [List.length_append] at hb
  obtain ⟨hx, hy⟩ := Block.holdsList_append_iff.mp hl
  exact ⟨⟨by omega, hx⟩, ⟨by omega, hy⟩⟩

private theorem holdsIn_encodeFactor_cons {curRaw : ℕ} {f : FactorTable ℕ ℕ}
    {rest : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hraw : HoldsIn curRaw ((f :: rest).flatMap encodeFactor) s) :
    curRaw < s.frontier ∧
      curRaw + 1 < s.frontier ∧
      s.mem curRaw = f.scope.length ∧
      s.mem (curRaw + 1) = f.entries.size ∧
      HoldsIn (curRaw + 2) f.scope s ∧
      HoldsIn (curRaw + 2 + f.scope.length) f.entries.toList s ∧
      HoldsIn (curRaw + 2 + f.scope.length + f.entries.size)
        (rest.flatMap encodeFactor) s := by
  simp only [List.flatMap_cons, encodeFactor, List.cons_append, List.nil_append,
    List.append_assoc] at hraw
  obtain ⟨h1, hm_sc, hr1⟩ := holdsIn_cons_shift hraw
  obtain ⟨h2, hm_en, hr2⟩ := holdsIn_cons_shift hr1
  rw [show curRaw + 1 + 1 = curRaw + 2 by omega] at hr2
  obtain ⟨hsc, hr3⟩ := holdsIn_append_split hr2
  obtain ⟨hen, hrest⟩ := holdsIn_append_split hr3
  exact ⟨h1, h2, hm_sc, hm_en, hsc, hen, by simpa [Array.length_toList] using hrest⟩

private def initFactorStep : Unit × (ℕ × ℕ) → Memory.Prog (ℕ × ℕ) :=
  fun ⟨_, (curRaw, curDesc)⟩ =>
    Memory.read curRaw >>= fun scLen =>
    Memory.read (curRaw + 1) >>= fun enLen =>
    writeDesc ⟨curDesc, curRaw + 2, scLen, curRaw + 2 + scLen, enLen⟩ >>= fun _ =>
    pure (curRaw + 2 + scLen + enLen, curDesc + 4)

private def initFactors (args : ℕ × ℕ) : Memory.Prog ℕ :=
  Memory.allocDirty (4 * args.2) >>= fun descBase =>
  iterate initFactorStep () args.2 (args.1, descBase) >>= fun _ =>
  pure descBase

private theorem initFactors_loop {w : ℕ} {s₀ : Memory.State} :
    ∀ (rem : List (FactorTable ℕ ℕ)) (curRaw curDesc : ℕ) (t : Memory.State),
      Memory.WellFormed w t →
      s₀.frontier ≤ curDesc →
      curDesc + 4 * rem.length ≤ t.frontier →
      PreservesBelow s₀.frontier s₀ t →
      HoldsIn curRaw (rem.flatMap encodeFactor) s₀ →
      let p := iterate initFactorStep () rem.length (curRaw, curDesc)
      let t' := (Memory.spec 0).clientState t p
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t p) ∧
        t'.frontier = t.frontier ∧
        PreservesBelow curDesc t t' ∧
        PreservesBelow s₀.frontier s₀ t' ∧
        HoldsFactorList curDesc rem t' ∧
        memoryCost p t ≤ 6 * rem.length
  | [], curRaw, curDesc, t, _, _, hbd, hpres, _ => by
      dsimp only
      have h0 : iterate initFactorStep () 0 (curRaw, curDesc) = pure (curRaw, curDesc) := rfl
      simp only [List.length_nil] at hbd ⊢
      rw [h0]
      exact ⟨validHistory_pure w t _, rfl, PreservesBelow.refl (by omega), hpres,
        by change curDesc ≤ t.frontier; omega,
        by simp [memoryCost_pure]⟩
  | f :: rest, curRaw, curDesc, t, hwf, hF_le, hbd, hpres, hraw => by
      dsimp only
      obtain ⟨h1, h2, hm_scLen, hm_enLen, hsc_s0, hen_s0, hrest_raw⟩ :=
        holdsIn_encodeFactor_cons hraw
      have ht_scLen : t.mem curRaw = f.scope.length := by
        rw [hpres.2.2 curRaw h1, hm_scLen]
      have ht_enLen : t.mem (curRaw + 1) = f.entries.size := by
        rw [hpres.2.2 (curRaw + 1) h2, hm_enLen]
      let wdArgs : WriteDescArgs :=
        ⟨curDesc, curRaw + 2, f.scope.length, curRaw + 2 + f.scope.length, f.entries.size⟩
      have hsc_t : HoldsIn (curRaw + 2) f.scope t := hsc_s0.mono hsc_s0.1 hpres
      have hen_t : HoldsIn (curRaw + 2 + f.scope.length) f.entries.toList t :=
        hen_s0.mono hen_s0.1 hpres
      simp only [List.length_cons] at hbd
      have hdst_lt : curDesc + 4 ≤ t.frontier := by omega
      have hfit_scPtr : Fits w (curRaw + 2) :=
        hwf.frontier_fits.of_le (by have := hsc_t.1; omega)
      have hfit_scLen : Fits w f.scope.length :=
        hwf.frontier_fits.of_le (by have := hsc_t.1; omega)
      have hfit_enPtr : Fits w (curRaw + 2 + f.scope.length) :=
        hwf.frontier_fits.of_le (by have := hen_t.1; omega)
      have hfit_enLen : Fits w f.entries.size :=
        hwf.frontier_fits.of_le (by have := hen_t.1; rw [Array.length_toList] at this; omega)
      have hwd_val := writeDesc_valid wdArgs hdst_lt hfit_scPtr hfit_scLen hfit_enPtr hfit_enLen
      have hwd_fr_p := writeDesc_frame wdArgs t
      have hst1_def : (Memory.spec 0).clientState t (writeDesc wdArgs) =
          ⟨Function.update (Function.update (Function.update
            (Function.update t.mem curDesc (curRaw + 2))
            (curDesc + 1) f.scope.length)
            (curDesc + 2) (curRaw + 2 + f.scope.length))
            (curDesc + 3) f.entries.size, t.frontier⟩ := rfl
      generalize ht₁ : (Memory.spec 0).clientState t (writeDesc wdArgs) = t₁ at hwd_fr_p hst1_def
      obtain ⟨ht1_fr, hwd_out⟩ := hwd_fr_p
      dsimp only [wdArgs] at hwd_out
      have hwf₁ : Memory.WellFormed w t₁ :=
        by rw [← ht₁]; exact wellFormed_clientState hwf hwd_val
      have hpres_cd : PreservesBelow curDesc t t₁ :=
        ⟨by omega, by rw [ht1_fr], fun a ha => hwd_out a (Or.inl ha)⟩
      have hpres₁ : PreservesBelow s₀.frontier s₀ t₁ := by
        refine ⟨hpres.1, by rw [ht1_fr]; exact hpres.2.1, fun a ha => ?_⟩
        rw [hwd_out a (Or.inl (lt_of_lt_of_le ha hF_le))]
        exact hpres.2.2 a ha
      have hih := initFactors_loop rest
        (curRaw + 2 + f.scope.length + f.entries.size) (curDesc + 4) t₁ hwf₁
        (by omega) (by rw [ht1_fr]; omega) hpres₁ hrest_raw
      dsimp only at hih
      obtain ⟨hih_val, hih_fr, hih_pres_cd, hih_pres_F, hih_holds, hih_cost⟩ := hih
      have hr_st (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
      have hr_res (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
      have hpure_st {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientState u (pure x) = u := rfl
      have hpure_res {α : Type} (x : α) (u : Memory.State) :
          (Memory.spec 0).clientResult u (pure x) = x := rfl
      have hstep_val : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (initFactorStep ((), (curRaw, curDesc)))) := by
        unfold initFactorStep
        dsimp only
        refine validHistory_read_bind (lt_of_lt_of_le h1 hpres.2.1) ?_
        rw [ht_scLen]
        refine validHistory_read_bind (lt_of_lt_of_le h2 hpres.2.1) ?_
        rw [ht_enLen]
        refine validHistory_bind_step hwd_val ?_
        rw [ht₁]
        exact validHistory_pure w t₁ _
      have hstep_st : (Memory.spec 0).clientState t (initFactorStep ((), (curRaw, curDesc))) =
          t₁ := by
        unfold initFactorStep
        dsimp only
        rw [StateTransitionSpec.clientState_bind, hr_st, hr_res, ht_scLen,
          StateTransitionSpec.clientState_bind, hr_st, hr_res, ht_enLen,
          StateTransitionSpec.clientState_bind, ht₁, hpure_st]
      have hstep_res : (Memory.spec 0).clientResult t (initFactorStep ((), (curRaw, curDesc))) =
          (curRaw + 2 + f.scope.length + f.entries.size, curDesc + 4) := by
        unfold initFactorStep
        dsimp only
        rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, ht_scLen,
          StateTransitionSpec.clientResult_bind, hr_st, hr_res, ht_enLen,
          StateTransitionSpec.clientResult_bind, ht₁, hpure_res]
      have hstep_cost : memoryCost (initFactorStep ((), (curRaw, curDesc))) t ≤ 6 := by
        unfold initFactorStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, ht_scLen,
          memoryCost_bind', memoryCost_read, hr_st, hr_res, ht_enLen,
          memoryCost_bind', ht₁, writeDesc_cost, memoryCost_pure, Nat.add_zero]
      have hf_final : HoldsFactor curDesc f
          ((Memory.spec 0).clientState t₁
            (iterate initFactorStep () rest.length
              (curRaw + 2 + f.scope.length + f.entries.size, curDesc + 4))) := by
        have hm0 : t₁.mem curDesc = curRaw + 2 := by
          rw [hst1_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_of_ne (by omega), Function.update_self]
        have hm1 : t₁.mem (curDesc + 1) = f.scope.length := by
          rw [hst1_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self]
        have hm2 : t₁.mem (curDesc + 2) = curRaw + 2 + f.scope.length := by
          rw [hst1_def]; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_self]
        have hm3 : t₁.mem (curDesc + 3) = f.entries.size := by
          rw [hst1_def]; dsimp only; rw [Function.update_self]
        unfold HoldsFactor
        rw [hih_pres_cd.2.2 curDesc (by omega),
          hih_pres_cd.2.2 (curDesc + 1) (by omega),
          hih_pres_cd.2.2 (curDesc + 2) (by omega),
          hih_pres_cd.2.2 (curDesc + 3) (by omega),
          hm0, hm1, hm2, hm3]
        exact ⟨by rw [hih_fr, ht1_fr]; exact hdst_lt, rfl, rfl,
          hsc_s0.mono hsc_s0.1 hih_pres_F,
          hen_s0.mono hen_s0.1 hih_pres_F⟩
      simp only [List.length_cons]
      have hiter_eq : iterate initFactorStep () (rest.length + 1) (curRaw, curDesc) =
          (initFactorStep ((), (curRaw, curDesc)) >>= iterate initFactorStep () rest.length) := rfl
      rw [hiter_eq, StateTransitionSpec.clientState_bind, hstep_st, hstep_res]
      refine ⟨validHistory_bind_step hstep_val ?_,
        by rw [hih_fr, ht1_fr],
        hpres_cd.trans (hih_pres_cd.mono_bound (by omega)),
        hih_pres_F,
        ⟨hf_final, hih_holds⟩, ?_⟩
      · rw [hstep_st, hstep_res]; exact hih_val
      · rw [memoryCost_bind', hstep_st, hstep_res]; omega

private theorem initFactors_spec {w : ℕ} {rawPtr facLen : ℕ}
    {factors : List (FactorTable ℕ ℕ)} {s : Memory.State}
    (hwf : Memory.WellFormed w s)
    (hlen : factors.length = facLen)
    (hraw : HoldsIn rawPtr (factors.flatMap encodeFactor) s)
    (hfit : Fits w (s.frontier + 4 * facLen)) :
    let res := (Memory.spec 0).clientResult s (initFactors (rawPtr, facLen))
    let s' := (Memory.spec 0).clientState s (initFactors (rawPtr, facLen))
    (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (initFactors (rawPtr, facLen))) ∧
      s'.frontier = s.frontier + 4 * facLen ∧
      PreservesBelow s.frontier s s' ∧
      res = s.frontier ∧
      HoldsFactorList res factors s' ∧
      memoryCost (initFactors (rawPtr, facLen)) s ≤ 1 + 6 * facLen := by
  subst hlen
  dsimp only
  unfold initFactors
  dsimp only
  have hv_alloc : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (Memory.allocDirty (4 * factors.length))) :=
    validHistory_allocDirty hfit
  let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * factors.length⟩
  have ha_st :
      (Memory.spec 0).clientState s (Memory.allocDirty (4 * factors.length)) = s₁ := rfl
  have ha_res :
      (Memory.spec 0).clientResult s (Memory.allocDirty (4 * factors.length)) = s.frontier := rfl
  have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit, hwf.mem_fits⟩
  have hpres₁ : PreservesBelow s.frontier s s₁ :=
    ⟨le_rfl, by dsimp only [s₁]; omega, fun _ _ => rfl⟩
  obtain ⟨hl_val, hl_fr, _, hl_pres, hl_holds, hl_cost⟩ :=
    initFactors_loop factors rawPtr s.frontier s₁ hwf₁ le_rfl
      (by dsimp only [s₁]; omega) hpres₁ hraw
  have hpure_st {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientState u (pure x) = u := rfl
  have hpure_res {α : Type} (x : α) (u : Memory.State) :
      (Memory.spec 0).clientResult u (pure x) = x := rfl
  rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    ha_st, ha_res,
    StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
    hpure_st, hpure_res]
  refine ⟨validHistory_bind_step hv_alloc ?_,
    by rw [hl_fr],
    hl_pres, rfl, hl_holds, ?_⟩
  · rw [ha_st, ha_res]
    exact validHistory_bind_step hl_val (validHistory_pure w _ _)
  · rw [memoryCost_bind', memoryCost_allocDirty, ha_st, ha_res,
      memoryCost_bind', memoryCost_pure, Nat.add_zero]
    omega

private theorem initFactors_realizes :
    Realizes .exact initFactors WordEncoding.encode WordEncoding.encode
      (fun w args s =>
        ∃ (factors : List (FactorTable ℕ ℕ)),
          Fits w 4 ∧
          Fits w (s.frontier + 4 * args.2) ∧
          factors.length = args.2 ∧
          HoldsIn args.1 (factors.flatMap encodeFactor) s)
      (fun _ _ => 0) := by
  unfold initFactors
  realize [writeDesc_realizes]
  · obtain ⟨_, _, hfit, _, _⟩ := h; exact hfit.of_le (by omega)
  · obtain ⟨_, h4, _, _, _⟩ := h; exact h4
  · obtain ⟨factors₀, _, hfit, hlen₀, hraw₀⟩ := h
    let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * d.2⟩
    have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit, hmem.mem_fits⟩
    have hpres₁ : PreservesBelow s.frontier s s₁ :=
      ⟨le_rfl, by dsimp only [s₁]; omega, fun _ _ => rfl⟩
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (st : ℕ × ℕ) (t : Memory.State) =>
        Memory.WellFormed w t ∧
        t.frontier = s.frontier + 4 * d.2 ∧
        s.frontier ≤ st.2 ∧
        st.2 + 4 * j ≤ t.frontier ∧
        PreservesBelow s.frontier s t ∧
        ∃ rem,
          rem.length = j ∧
          HoldsIn st.1 (rem.flatMap encodeFactor) s)
      (fun j st t ⟨hwf_t, hfr_t, hlo_t, hbd_t, hpres_t, rem, hrem_l, hraw_t⟩ => ?_)
      ⟨hwf₁, rfl, le_rfl, by dsimp only [s₁]; omega, hpres₁, factors₀, hlen₀, hraw₀⟩
    dsimp only
    rcases rem with _ | ⟨f, rest⟩
    · cases hrem_l
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hrem_l
    subst hrem_l
    obtain ⟨h1, h2, hm_scLen, hm_enLen, hsc_s0, hen_s0, hrest_raw⟩ :=
      holdsIn_encodeFactor_cons hraw_t
    have ht_scLen : t.mem st.1 = f.scope.length := by
      rw [hpres_t.2.2 st.1 h1, hm_scLen]
    have ht_enLen : t.mem (st.1 + 1) = f.entries.size := by
      rw [hpres_t.2.2 (st.1 + 1) h2, hm_enLen]
    have hr_st (addr : ℕ) : (Memory.spec 0).clientState t (Memory.read addr) = t := rfl
    have hr_res (addr : ℕ) : (Memory.spec 0).clientResult t (Memory.read addr) = t.mem addr := rfl
    have hpure_st {α : Type} (x : α) (u : Memory.State) :
        (Memory.spec 0).clientState u (pure x) = u := rfl
    have hpure_res {α : Type} (x : α) (u : Memory.State) :
        (Memory.spec 0).clientResult u (pure x) = x := rfl
    have hraw_end : st.1 + 2 + f.scope.length + f.entries.size ≤ s.frontier := by
      have hbd := hen_s0.1
      rw [Array.length_toList] at hbd
      omega
    have ht_le : s.frontier ≤ t.frontier := hpres_t.2.1
    refine ⟨?_, ?_⟩
    · refine ⟨hwf_t.frontier_fits.of_le (by omega), ?_⟩
      simp only [ht_scLen, ht_enLen]
      repeat (any_goals refine ⟨?_, ?_⟩)
      all_goals exact hwf_t.frontier_fits.of_le (by omega)
    · let wdArgs : WriteDescArgs :=
        ⟨st.2, st.1 + 2, f.scope.length, st.1 + 2 + f.scope.length, f.entries.size⟩
      have hwd_val := writeDesc_valid (w := w) (s := t) wdArgs (by dsimp only [wdArgs]; omega)
        (hwf_t.frontier_fits.of_le (by dsimp only [wdArgs]; omega))
        (hwf_t.frontier_fits.of_le (by dsimp only [wdArgs]; omega))
        (hwf_t.frontier_fits.of_le (by dsimp only [wdArgs]; omega))
        (hwf_t.frontier_fits.of_le (by dsimp only [wdArgs]; omega))
      have hwd_fr_p := writeDesc_frame wdArgs t
      generalize ht₁ : (Memory.spec 0).clientState t (writeDesc wdArgs) = t₁ at hwd_fr_p
      obtain ⟨ht1_fr, hwd_out⟩ := hwd_fr_p
      dsimp only [wdArgs] at hwd_out
      have hwf₁ : Memory.WellFormed w t₁ :=
        by rw [← ht₁]; exact wellFormed_clientState hwf_t hwd_val
      have hpres_next : PreservesBelow s.frontier s t₁ := by
        refine ⟨hpres_t.1, by rw [ht1_fr]; exact hpres_t.2.1, fun a ha => ?_⟩
        rw [hwd_out a (Or.inl (lt_of_lt_of_le ha hlo_t))]
        exact hpres_t.2.2 a ha
      unfold initFactorStep
      dsimp only
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        hr_st, hr_res, ht_scLen,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        hr_st, hr_res, ht_enLen,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientResult_bind,
        ht₁, hpure_st, hpure_res]
      exact ⟨hwf₁, by rw [ht1_fr]; exact hfr_t, by dsimp only; omega,
        by dsimp only; rw [ht1_fr]; omega, hpres_next, rest, rfl, hrest_raw⟩

/-! ### Public `ElimInstance` bundle and top-level Word-RAM program (`runProg`) -/

/-- Word-RAM input bundle for bucket (variable) elimination over explicit `ℕ`-valued radix-indexed
factor tables at finite domain size `domain`. -/
structure ElimInstance where
  /-- Domain size `d` (variables range over `0, ..., domain - 1`). -/
  domain : ℕ
  /-- Declared variables to contract over (`ElimState.remaining` initially). -/
  declared : List ℕ
  /-- Supplied variable elimination order. -/
  order : List ℕ
  /-- Initial explicit radix-indexed factor tables. -/
  factors : List (FactorTable ℕ ℕ)

namespace ElimInstance

/-- Initial pure elimination state `ElimState.ofFactors inst.factors inst.declared`. -/
@[expose] def initState (inst : ElimInstance) : ElimState ℕ ℕ :=
  ElimState.ofFactors inst.factors inst.declared

/-- Pure contracted scalar result
`(eliminateOrder inst.domain inst.order inst.initState).result`. -/
@[expose] def result (inst : ElimInstance) : ℕ :=
  (eliminateOrder inst.domain inst.order inst.initState).result

/-- Maximum entry across all initial factor tables (`0` if all tables are empty). -/
@[expose] def maxEntry (inst : ElimInstance) : ℕ :=
  (inst.factors.map fun f => f.entries.toList.foldl max 0).foldl max 0

/-- Word-array serialization of `inst`:
`[inst.domain, inst.declared.length, inst.order.length, inst.factors.length] ++ inst.declared ++
inst.order ++ inst.factors.flatMap encodeFactor`. -/
@[expose] def encode (inst : ElimInstance) : List ℕ :=
  [inst.domain, inst.declared.length, inst.order.length, inst.factors.length] ++
    inst.declared ++ inst.order ++ inst.factors.flatMap encodeFactor

/-- Word-value upper bound covering literal constants, peak memory frontier across the entire
elimination run, radix powers `(max 1 domain) ^ max S W`, and intermediate/final weighted sums
`(max 1 domain) ^ order.length * (max 1 maxEntry) ^ factors.length`. -/
@[expose] def wordBound (inst : ElimInstance) : ℕ :=
  let d := inst.domain
  let R := inst.declared.length
  let T := inst.order.length
  let M := inst.factors.length
  let W := maxJointScopeLen d inst.order inst.initState
  let SW := max (maxScopeLen inst.factors) W
  5 + (inst.encode.length + 1 + 4 * M +
      T * (R + 4 + 8 * M + 2 * (M * SW) + (max 1 d) ^ W)) +
    (max 1 d) ^ SW +
    (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M

/-- Upper bound on the oracle memory cost (`memoryCost`) of bucket elimination along `inst.order`,
exponential only in `W = maxJointScopeLen` (`(max 1 domain) ^ W`) with amortized `M + T` bucket
factor evaluations. -/
@[expose] def stepBound (inst : ElimInstance) : ℕ :=
  let d := inst.domain
  let R := inst.declared.length
  let T := inst.order.length
  let M := inst.factors.length
  let W := maxJointScopeLen d inst.order inst.initState
  let SW := max (maxScopeLen inst.factors) W
  5 + 9 * M +
    T * (1 + (12 + 3 * R + M * (8 + SW) + W + 4 * (max 1 d) ^ W)) +
    (M + T) * (3 + SW * (4 + W) + (max 1 d) ^ W * (5 + SW * W))

/-- Compile a `ℕ`-weighted `CSP Rel ℕ` over finite domain `D ≃ Fin d` with declared variable list
`declared` and elimination order `order` into an `ElimInstance`. -/
@[expose] def ofCSP {Rel D : Type*} [Inhabited D]
    (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → ℕ) (F : CSP Rel ℕ)
    (declared order : List ℕ) : ElimInstance :=
  { domain := d
    declared := declared
    order := order
    factors := FactorTable.ofCSP d e wt F }

/-- `ElimInstance.ofCSP` evaluates to `F.partitionFunctionOn wt declared.toFinset` whenever
`declared` contains all occurring variables of `F` and `order` covers `declared`. -/
theorem result_ofCSP {Rel D : Type*} [Fintype D] [Inhabited D]
    (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → ℕ) {F : CSP Rel ℕ}
    {declared order : List ℕ}
    (hvars : F.vars.toFinset ⊆ declared.toFinset)
    (hcover : declared.toFinset ⊆ order.toFinset) :
    (ofCSP d e wt F declared order).result = F.partitionFunctionOn wt declared.toFinset :=
  result_eliminateOrder_ofCSP d e wt hvars hcover

end ElimInstance

private theorem holdsIn_stateInit (words : List ℕ) :
    HoldsIn 1 words (Memory.State.init words) := by
  refine ⟨by simp [Memory.State.init]; omega, fun i => ?_⟩
  have h := Data.init_realizes_append (r := 0) [] words [] i
  simpa [Memory.State.init] using h

private theorem capFactor_le_maxEntry {inst : ElimInstance} {f : FactorTable ℕ ℕ}
    (hf : f ∈ inst.factors) :
    capFactor f ≤ max 1 inst.maxEntry := by
  unfold capFactor ElimInstance.maxEntry
  refine max_le (le_max_left 1 _) (le_trans ?_ (le_max_right 1 _))
  exact List.mem_le_foldl_max (List.mem_map.mpr ⟨f, hf, rfl⟩)

private theorem initState_stateCap_le (inst : ElimInstance) :
    stateCap inst.initState ≤ (max 1 inst.maxEntry) ^ inst.factors.length := by
  unfold stateCap ElimInstance.initState ElimState.ofFactors
  dsimp only
  simp only [max_self, Nat.one_mul]
  simpa [List.length_map] using
    List.prod_le_pow_length (inst.factors.map capFactor) (max 1 inst.maxEntry) fun _ hn => by
      rcases List.mem_map.mp hn with ⟨f, hf, rfl⟩
      exact capFactor_le_maxEntry hf

private theorem stateCap_eliminateOrder_le (d : ℕ) :
    ∀ (ord : List ℕ) (es : ElimState ℕ ℕ),
      stateCap (eliminateOrder d ord es) ≤ (max 1 d) ^ ord.length * stateCap es
  | [], es => by simp [eliminateOrder]
  | x :: xs, es => by
      simp only [eliminateOrder, List.length_cons, Nat.pow_succ]
      calc stateCap (eliminateOrder d xs (elimVar d x es))
          ≤ (max 1 d) ^ xs.length * stateCap (elimVar d x es) :=
            stateCap_eliminateOrder_le d xs (elimVar d x es)
        _ ≤ (max 1 d) ^ xs.length * (max 1 d * stateCap es) :=
            Nat.mul_le_mul_left _ (stateCap_elimVar_le d x es)
        _ = (max 1 d) ^ xs.length * max 1 d * stateCap es := by ring

private def runProg (_ : Unit) : Memory.Prog ℕ :=
  Memory.read 1 >>= fun dom =>
  Memory.read 2 >>= fun declLen =>
  Memory.read 3 >>= fun ordLen =>
  Memory.read 4 >>= fun facLen =>
  initFactors (5 + declLen + ordLen, facLen) >>= fun livePtr =>
  elimOrderLoop ⟨dom, 5 + declLen, ordLen, 1, livePtr, facLen, 5, declLen⟩ >>= fun finalSt =>
  finalResultProd ⟨finalSt.livePtr, finalSt.liveLen, finalSt.scalar⟩

private theorem decode_init_layout (inst : ElimInstance) :
    let s₀ := Memory.State.init inst.encode
    5 ≤ s₀.frontier ∧
      s₀.mem 1 = inst.domain ∧
      s₀.mem 2 = inst.declared.length ∧
      s₀.mem 3 = inst.order.length ∧
      s₀.mem 4 = inst.factors.length ∧
      HoldsIn 5 inst.declared s₀ ∧
      HoldsIn (5 + inst.declared.length) inst.order s₀ ∧
      HoldsIn (5 + inst.declared.length + inst.order.length)
        (inst.factors.flatMap encodeFactor) s₀ := by
  dsimp only
  have hall : HoldsIn 1 inst.encode (Memory.State.init inst.encode) :=
    holdsIn_stateInit inst.encode
  have henc : inst.encode = inst.domain :: inst.declared.length :: inst.order.length ::
      inst.factors.length ::
      (inst.declared ++ (inst.order ++ inst.factors.flatMap encodeFactor)) := by
    simp [ElimInstance.encode, List.append_assoc]
  nth_rw 1 [henc] at hall
  obtain ⟨_, hm1, hr1⟩ := holdsIn_cons_shift hall
  obtain ⟨_, hm2, hr2⟩ := holdsIn_cons_shift hr1
  obtain ⟨_, hm3, hr3⟩ := holdsIn_cons_shift hr2
  obtain ⟨h4_lt, hm4, hr4⟩ := holdsIn_cons_shift hr3
  have h5 : 1 + 1 + 1 + 1 + 1 = 5 := rfl
  rw [h5] at hr4
  obtain ⟨hdecl, hr5⟩ := holdsIn_append_split hr4
  obtain ⟨hord, hfac⟩ := holdsIn_append_split hr5
  exact ⟨by omega, hm1, hm2, hm3, hm4, hdecl, hord, hfac⟩

private theorem runProg_spec {w : ℕ} (inst : ElimInstance)
    (hin : InputFits w inst.encode) (hw : Fits w inst.wordBound) :
    let s₀ := Memory.State.init inst.encode
    (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (runProg ())) ∧
      (Memory.spec 0).clientResult s₀ (runProg ()) = inst.result ∧
      memoryCost (runProg ()) s₀ ≤ inst.stepBound := by
  dsimp only
  let s₀ := Memory.State.init inst.encode
  have hf_init : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  have hwf₀ : Memory.WellFormed w s₀ := Memory.wellFormed_init hin hf_init
  obtain ⟨hs0_5, hm1, hm2, hm3, hm4, hdecl₀, hord₀, hfac₀⟩ := decode_init_layout inst
  change 5 ≤ s₀.frontier at hs0_5
  let d := inst.domain
  let R := inst.declared.length
  let T := inst.order.length
  let M := inst.factors.length
  let W := maxJointScopeLen d inst.order inst.initState
  let SW := max (maxScopeLen inst.factors) W
  let B := (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M
  have h1 : Fits w 1 := hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  have hB : Fits w B := hw.of_le (by unfold ElimInstance.wordBound; dsimp only [B, d, T, M]; omega)
  have hpowSW : Fits w ((max 1 d) ^ SW) :=
    hw.of_le (by unfold ElimInstance.wordBound; dsimp only [d, W, SW]; omega)
  have hs0_fr : s₀.frontier = inst.encode.length + 1 := rfl
  have hfit_initF : Fits w (s₀.frontier + 4 * M) := hw.of_le (by
    rw [hs0_fr]; unfold ElimInstance.wordBound; dsimp only [M]; omega)
  have hif_spec := initFactors_spec (w := w) (rawPtr := 5 + R + T) (facLen := M)
    hwf₀ rfl hfac₀ hfit_initF
  dsimp only at hif_spec
  generalize hs₁ : (Memory.spec 0).clientState s₀ (initFactors (5 + R + T, M)) = s₁ at hif_spec
  generalize hlivePtr :
    (Memory.spec 0).clientResult s₀ (initFactors (5 + R + T, M)) = livePtr at hif_spec
  obtain ⟨hif_val, hif_fr, hif_pres, _, hif_holds, hif_cost⟩ := hif_spec
  have hwf₁ : Memory.WellFormed w s₁ :=
    by rw [← hs₁]; exact wellFormed_clientState hwf₀ hif_val
  have hdecl₁ : HoldsIn 5 inst.declared s₁ := hdecl₀.mono_frontier hif_pres
  have hord₁ : HoldsIn (5 + R) inst.order s₁ := hord₀.mono_frontier hif_pres
  have hes₁ : HoldsElimState ⟨1, livePtr, M, 5, R⟩ inst.initState s₁ :=
    ⟨by rw [hif_fr, hs0_fr]; omega, rfl, rfl, rfl, hif_holds, hdecl₁⟩
  have hSW₀ : ∀ f ∈ inst.initState.live, f.scope.length ≤ SW :=
    fun f hf => (each_mem_le_maxScopeLen f hf).trans (le_max_left _ _)
  have hW₀ : ∀ st ∈ traceOrder d inst.order inst.initState, st.jointScopeVars ≤ W :=
    fun _ hst => mem_traceOrder_joint_le d inst.order inst.initState hst
  have hcap₀ : (max 1 d) ^ T * stateCap inst.initState ≤ B :=
    Nat.mul_le_mul_left _ (initState_stateCap_le inst)
  have hfit_loop : Fits w (s₁.frontier + T * stepMemDelta R M SW d W) := hw.of_le (by
    rw [hif_fr, hs0_fr]
    unfold ElimInstance.wordBound
    dsimp only [d, R, T, M, W, SW, stepMemDelta]
    omega)
  let eoArgs : ElimOrderArgs := ⟨d, 5 + R, T, 1, livePtr, M, 5, R⟩
  have heo_spec := elimOrderLoop_spec (w := w) (args := eoArgs) (R := R) (M := M)
    hwf₁ hord₁ rfl hes₁ le_rfl le_rfl hSW₀ hW₀ (le_max_right _ _) hcap₀ hB h1 hpowSW hfit_loop
  dsimp only at heo_spec
  generalize hs₂ : (Memory.spec 0).clientState s₁ (elimOrderLoop eoArgs) = s₂ at heo_spec
  generalize hfinalSt :
    (Memory.spec 0).clientResult s₁ (elimOrderLoop eoArgs) = finalSt at heo_spec
  obtain ⟨heo_val, _, _, heo_es, heo_cost⟩ := heo_spec
  dsimp only [eoArgs] at heo_es heo_cost
  let esFinal := eliminateOrder d inst.order inst.initState
  have hcap_final : stateCap esFinal ≤ B :=
    (stateCap_eliminateOrder_le d inst.order inst.initState).trans hcap₀
  obtain ⟨_, hsc_f, hliveLen_f, _, hlive_f, _⟩ := heo_es
  dsimp only at hsc_f hliveLen_f hlive_f
  let fpArgs : FinalProdArgs := ⟨finalSt.livePtr, finalSt.liveLen, finalSt.scalar⟩
  obtain ⟨hfp_val, _, hfp_res, hfp_cost⟩ :=
    finalResultProd_spec (w := w) (args := fpArgs) hB hcap_final hsc_f hliveLen_f hlive_f
  dsimp only [fpArgs] at hfp_cost
  have hliveLen_le_M : finalSt.liveLen ≤ M := by
    rw [hliveLen_f]
    exact liveLength_eliminateOrder_le d inst.order inst.initState
  have hr_st (addr : ℕ) : (Memory.spec 0).clientState s₀ (Memory.read addr) = s₀ := rfl
  have hr_res (addr : ℕ) : (Memory.spec 0).clientResult s₀ (Memory.read addr) = s₀.mem addr := rfl
  unfold runProg
  rw [StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm1,
    StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm2,
    StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm3,
    StateTransitionSpec.clientResult_bind, hr_st, hr_res, hm4]
  change (Memory.spec w).ValidHistory s₀ _ ∧
    (Memory.spec 0).clientResult s₀
      (initFactors (5 + R + T, M) >>= fun lp =>
        elimOrderLoop ⟨d, 5 + R, T, 1, lp, M, 5, R⟩ >>= fun fs =>
          finalResultProd ⟨fs.livePtr, fs.liveLen, fs.scalar⟩) = inst.result ∧ _
  rw [StateTransitionSpec.clientResult_bind, hs₁, hlivePtr,
    StateTransitionSpec.clientResult_bind, hs₂, hfinalSt, hfp_res]
  refine ⟨?_, rfl, ?_⟩
  · refine validHistory_read_bind (by omega) ?_
    rw [hm1]
    refine validHistory_read_bind (by omega) ?_
    rw [hm2]
    refine validHistory_read_bind (by omega) ?_
    rw [hm3]
    refine validHistory_read_bind (by omega) ?_
    rw [hm4]
    refine validHistory_bind_step hif_val ?_
    rw [hs₁, hlivePtr]
    refine validHistory_bind_step heo_val ?_
    rw [hs₂, hfinalSt]
    exact hfp_val
  · rw [memoryCost_bind', memoryCost_read, hr_st, hr_res, hm1,
      memoryCost_bind', memoryCost_read, hr_st, hr_res, hm2,
      memoryCost_bind', memoryCost_read, hr_st, hr_res, hm3,
      memoryCost_bind', memoryCost_read, hr_st, hr_res, hm4,
      memoryCost_bind', hs₁, hlivePtr,
      memoryCost_bind', hs₂, hfinalSt]
    unfold ElimInstance.stepBound
    dsimp only [d, R, T, M, W, SW, stepFixedCost, stepBucketUnitCost]
      at hif_cost heo_cost hfp_cost hliveLen_le_M ⊢
    omega

private theorem runProg_realizes :
    Realizes .exact runProg WordEncoding.encode WordEncoding.encode
      (fun w _ s =>
        ∃ inst : ElimInstance,
          s = Memory.State.init inst.encode ∧
          InputFits w inst.encode ∧
          Fits w inst.wordBound)
      (fun _ _ => 0) := by
  unfold runProg
  realize [initFactors_realizes, elimOrderLoop_realizes, finalResultProd_realizes]
  all_goals
    obtain ⟨inst, hs_eq, hin, hw⟩ := h
    subst hs_eq
    obtain ⟨hs0_5, hm1, hm2, hm3, hm4, hdecl₀, hord₀, hfac₀⟩ := decode_init_layout inst
    have hord_le : 5 + inst.declared.length + inst.order.length ≤ inst.encode.length + 1 :=
      hord₀.1
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · simp only [hm2, hm3, hm4]
    refine ⟨inst.factors,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega), ?_, rfl, hfac₀⟩
    exact hw.of_le (by
      change inst.encode.length + 1 + 4 * inst.factors.length ≤ inst.wordBound
      unfold ElimInstance.wordBound; dsimp only; omega)
  · rw [hm2]
    exact hmem.frontier_fits.of_le (by have := hdecl₀.1; omega)
  · exact hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  · simp only [hm1, hm2, hm3, hm4]
    let s₀ := Memory.State.init inst.encode
    let d := inst.domain
    let R := inst.declared.length
    let T := inst.order.length
    let M := inst.factors.length
    let W := maxJointScopeLen d inst.order inst.initState
    let SW := max (maxScopeLen inst.factors) W
    let B := (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M
    have hfit_initF : Fits w (s₀.frontier + 4 * M) := hw.of_le (by
      change inst.encode.length + 1 + 4 * M ≤ inst.wordBound
      unfold ElimInstance.wordBound; dsimp only [M]; omega)
    have hif_spec := initFactors_spec (w := w) (rawPtr := 5 + R + T) (facLen := M)
      hmem rfl hfac₀ hfit_initF
    dsimp only at hif_spec
    obtain ⟨_, hif_fr, hif_pres, _, hif_holds, _⟩ := hif_spec
    exact ⟨inst.order, inst.initState, R, M, SW, W, B,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega),
      rfl,
      hord₀.mono_frontier hif_pres,
      ⟨by rw [hif_fr]; change 0 < inst.encode.length + 1 + 4 * M; omega,
        rfl, rfl, rfl, hif_holds, hdecl₀.mono_frontier hif_pres⟩,
      le_rfl, le_rfl,
      fun f hf => (each_mem_le_maxScopeLen f hf).trans (le_max_left _ _),
      fun _ hst => mem_traceOrder_joint_le d inst.order inst.initState hst,
      le_max_right _ _,
      Nat.mul_le_mul_left _ (initState_stateCap_le inst),
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only [B, d, T, M]; omega),
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only [d, W, SW]; omega),
      hw.of_le (by
        rw [hif_fr]
        change inst.encode.length + 1 + 4 * M + T * stepMemDelta R M SW d W ≤ inst.wordBound
        unfold ElimInstance.wordBound
        dsimp only [d, R, T, M, W, SW, stepMemDelta]
        omega)⟩
  · simp only [hm1, hm2, hm3, hm4]
    let s₀ := Memory.State.init inst.encode
    let d := inst.domain
    let R := inst.declared.length
    let T := inst.order.length
    let M := inst.factors.length
    let W := maxJointScopeLen d inst.order inst.initState
    let SW := max (maxScopeLen inst.factors) W
    let B := (max 1 d) ^ T * (max 1 inst.maxEntry) ^ M
    have hfit_initF : Fits w (s₀.frontier + 4 * M) := hw.of_le (by
      change inst.encode.length + 1 + 4 * M ≤ inst.wordBound
      unfold ElimInstance.wordBound; dsimp only [M]; omega)
    have hif_spec := initFactors_spec (w := w) (rawPtr := 5 + R + T) (facLen := M)
      hmem rfl hfac₀ hfit_initF
    dsimp only at hif_spec
    generalize hs₁ : (Memory.spec 0).clientState s₀ (initFactors (5 + R + T, M)) = s₁ at hif_spec
    generalize hlivePtr :
      (Memory.spec 0).clientResult s₀ (initFactors (5 + R + T, M)) = livePtr at hif_spec
    obtain ⟨hif_val, hif_fr, hif_pres, _, hif_holds, _⟩ := hif_spec
    have hwf₁ : Memory.WellFormed w s₁ :=
      by rw [← hs₁]; exact wellFormed_clientState hmem hif_val
    have hes₁ : HoldsElimState ⟨1, livePtr, M, 5, R⟩ inst.initState s₁ :=
      ⟨by rw [hif_fr]; change 0 < inst.encode.length + 1 + 4 * M; omega,
        rfl, rfl, rfl, hif_holds, hdecl₀.mono_frontier hif_pres⟩
    have hcap₀ : (max 1 d) ^ T * stateCap inst.initState ≤ B :=
      Nat.mul_le_mul_left _ (initState_stateCap_le inst)
    let eoArgs : ElimOrderArgs := ⟨d, 5 + R, T, 1, livePtr, M, 5, R⟩
    have heo_spec := elimOrderLoop_spec (w := w) (args := eoArgs) (R := R) (M := M) (SW := SW)
      hwf₁ (hord₀.mono_frontier hif_pres) rfl hes₁ le_rfl le_rfl
      (fun f hf => (each_mem_le_maxScopeLen f hf).trans (le_max_left _ _))
      (fun _ hst => mem_traceOrder_joint_le d inst.order inst.initState hst)
      (le_max_right _ _) hcap₀
      (hw.of_le (by unfold ElimInstance.wordBound; dsimp only [B, d, T, M]; omega))
      (hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega))
      (hw.of_le (by unfold ElimInstance.wordBound; dsimp only [eoArgs, d, W, SW]; omega))
      (hw.of_le (by
        rw [hif_fr]
        change inst.encode.length + 1 + 4 * M + T * stepMemDelta R M SW d W ≤ inst.wordBound
        unfold ElimInstance.wordBound
        dsimp only [d, R, T, M, W, SW, stepMemDelta]
        omega))
    dsimp only at heo_spec
    obtain ⟨_, _, _, heo_es, _⟩ := heo_spec
    obtain ⟨_, hsc_f, hliveLen_f, _, hlive_f, _⟩ := heo_es
    dsimp only [eoArgs] at hsc_f hliveLen_f hlive_f
    let esFinal := eliminateOrder d inst.order inst.initState
    have hcap_final : esFinal.scalar * (esFinal.live.map capFactor).prod ≤ B :=
      (Nat.mul_le_mul_right _ (le_max_right 1 esFinal.scalar)).trans
        ((stateCap_eliminateOrder_le d inst.order inst.initState).trans hcap₀)
    exact ⟨esFinal.live, B,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega),
      hliveLen_f.symm, hlive_f,
      by rw [hsc_f]; exact hcap_final,
      hw.of_le (by unfold ElimInstance.wordBound; dsimp only [B, d, T, M]; omega)⟩

/-- One fixed exact-basis Word-RAM program computes bucket (variable) elimination
`ElimInstance.result` in `≤ C * (inst.stepBound + 1) + 1` instructions for every word width `w`
satisfying `Fits w inst.wordBound` and `InputFits w inst.encode`. -/
theorem exists_program_variableElimination :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      prog.ComputesInTime
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound)
        ElimInstance.result := by
  obtain ⟨r, C, pc, prog, _, _, hexec⟩ :=
    runProg_realizes.exists_standard_init_program_state_from_words (0 : Fin 1)
  refine ⟨r, C, prog, fun inst w hw hin => ?_⟩
  have hf_len : Fits w (inst.encode.length + 1) :=
    hw.of_le (by unfold ElimInstance.wordBound; dsimp only; omega)
  obtain ⟨hval, hres, hcost⟩ := runProg_spec inst hin hw
  obtain ⟨y, n, hruns, hhalt, _, _, hn_le⟩ :=
    hexec w () inst.encode (fun i => Fin.elim0 i) (Nat.zero_le _) hf_len hin
      ⟨inst, rfl, hin, hw⟩ hval
  rw [clientResult_width, hres] at hhalt
  refine ⟨n + 1, ⟨⟨pc, y⟩, n, hruns, hhalt, rfl⟩, ?_⟩
  have hwork : (fun (_ : Unit) (_ : Memory.State) => (0 : ℕ)) () (Memory.State.init inst.encode) =
      0 := rfl
  have hmul : C * (memoryCost (runProg ()) (Memory.State.init inst.encode) + 0 + 1) + 1 ≤
      C * (inst.stepBound + 1) + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul_left C (by omega)) 1
  exact hn_le.trans hmul

/-- Uniform exact-basis Word-RAM computability certificate for `ElimInstance.result`. -/
theorem uniformComputableInTime_variableElimination :
    ∃ C : ℕ,
      UniformComputableInTime .exact
        ElimInstance.result
        (fun _ inst => inst.encode)
        (fun inst _ => C * (inst.stepBound + 1) + 1)
        (fun inst w => Fits w inst.wordBound) := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_variableElimination
  refine ⟨C, r, prog, hcomp, fun inst => ?_⟩
  obtain ⟨w, hw_le, hin⟩ := InputFits.exists_width inst.encode inst.wordBound
  exact ⟨w, (fits_self inst.wordBound).mono hw_le, hin⟩

/-- One fixed exact-basis Word-RAM program computes the weighted CSP partition function
`F.partitionFunctionOn wt declared.toFinset` by variable elimination along any supplied order
`order` covering `declared` (whenever `F.vars.toFinset ⊆ declared.toFinset`), within
`C * ((ElimInstance.ofCSP d e wt F declared order).stepBound + 1) + 1` instructions. -/
theorem exists_program_csp_partitionFunctionOn :
    ∃ r C : ℕ, ∃ prog : Program .exact r,
      ∀ {Rel D : Type*} [Fintype D] [Inhabited D]
        (d : ℕ) (e : D ≃ Fin d) (wt : Rel → List D → ℕ) (F : CSP Rel ℕ)
        (declared order : List ℕ),
        F.vars.toFinset ⊆ declared.toFinset →
        declared.toFinset ⊆ order.toFinset →
        ∀ w : ℕ,
          let inst := ElimInstance.ofCSP d e wt F declared order
          Fits w inst.wordBound →
          InputFits w inst.encode →
          ∃ n,
            Executes w prog (.init inst.encode) (F.partitionFunctionOn wt declared.toFinset) n ∧
            n ≤ C * (inst.stepBound + 1) + 1 := by
  obtain ⟨r, C, prog, hcomp⟩ := exists_program_variableElimination
  refine ⟨r, C, prog, fun d e wt F declared order hvars hcover w hw hin => ?_⟩
  rw [← ElimInstance.result_ofCSP d e wt hvars hcover]
  exact hcomp (ElimInstance.ofCSP d e wt F declared order) w hw hin

end Cslib.Algorithms.WordRAM.VariableElimination
