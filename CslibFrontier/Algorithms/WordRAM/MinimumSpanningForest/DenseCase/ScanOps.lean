/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.Layout
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Foundations.Data.List.Subperm
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bounded-Heap DJP Scan Operations, Threshold Computation, and Extraction Primitives

Implements the pure-register heap-threshold routine `computeThreshProg`, the CSR adjacency scan
subroutine `ftScanVertex`, and the cut/invariant building blocks used by `DenseCase/Scan` for a
single bounded-heap contraction phase of `[FredmanTarjan1987]` (§3) / `[PettieRamachandran2002]`
(§3.4 `DenseCase`) toward `#8624`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.computeThreshProg`,
  `computeThreshProgSafe`: pure-register bounded doubling for `min n (2 ^ ((2 * mRef) / n))`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.FTScanArgs`, `ftScanVertex`,
  `ftScanVertexSafe`: word-encoded CSR adjacency scan and Fibonacci-heap relaxation routine.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.scanMod`, `growMod`, `FTGrowInv`:
  modification footprints and inner tree-growth invariant.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.realizes_computeThreshProg`,
  `computeThreshProg_spec`: exact zero-traffic realization and threshold bounds.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.realizes_ftScanVertex`,
  `ftScanVertex_spec`: correctness and amortized potential bound for scanning a vertex's CSR edges.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.extractRawProg_spec_n`,
  `ftExtract_cutStep`, `ftExtract_grow_cutInv`: heap-extraction cut and invariant lemmas.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.FibonacciHeap
open Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.MinimumSpanningForest
open Cslib.Query.MinimumSpanningForest

/-! ## Pure-Register Heap-Size Threshold Computation (`computeThreshProg`) -/

private def threshStep (d : ℕ × ℕ) : Memory.Prog ℕ :=
  if d.1 < 2 * d.2 then pure d.1 else pure (2 * d.2)

private def threshStepSafe (w : ℕ) (d : ℕ × ℕ) (_ : Memory.State) : Prop :=
  Fits w (2 * d.1) ∧ d.2 ≤ d.1 ∧ 1 ≤ d.1

private theorem realizes_threshStep : Realizes .exact
    threshStep (appendWords wordWords wordWords) wordWords threshStepSafe (fun _ _ => 0) := by
  unfold threshStep
  realize
  all_goals
    rcases h with ⟨h2n, ha, hn1⟩
    have h2 : Fits w 2 := h2n.of_le (by omega)
    have h1 : Fits w (2 * d.2) := h2n.of_le (by omega)
    fits

/-- Computes `min n (2 ^ ((2 * mRef) / n))` purely in registers (`memoryCost = 0`, `s' = s`)
using at most `min n ((2 * mRef) / n)` doubling steps. -/
def computeThreshProg (n mRef : ℕ) : Memory.Prog ℕ :=
  let sh := (2 * mRef) / n
  if n < sh then iterate threshStep n n 1
  else iterate threshStep n sh 1

/-- Native safety domain for `computeThreshProg`. -/
def computeThreshProgSafe (w : ℕ) (d : ℕ × ℕ) (_ : Memory.State) : Prop :=
  Fits w (2 * d.2 + 1) ∧ Fits w (2 * d.1) ∧ 1 ≤ d.1

private theorem computeThresh_realize_iterSafe {w : ℕ} {d : ℕ × ℕ} {steps : ℕ} {s : Memory.State}
    (h : computeThreshProgSafe w d s) :
    iterationSafe (fun x : ((ℕ × ℕ) × ℕ) × ℕ => threshStep (x.1.1.1, x.2))
      (fun w x s => threshStepSafe w (x.1.1.1, x.2) s) w (d, steps)
      (if d.1 < steps then d.1 else steps) 1 s := by
  refine iterationSafe_of_stepInv _ _ w (d, steps)
    (fun _ k t => k ≤ d.1 ∧ t = s) ?_ ⟨h.2.2, rfl⟩
  intro _ k t ⟨hk, ht⟩
  refine ⟨⟨h.2.1, hk, h.2.2⟩, ?_⟩
  dsimp only [threshStep]
  rw [prog_clientResult_ite, prog_clientState_ite]
  split_ifs <;> simp only [StateTransitionSpec.clientResult_pure]
  · exact ⟨le_rfl, ht⟩
  · exact ⟨by omega, ht⟩

/-- Uniform exact-basis realization of `computeThreshProg` with `work ≤ (2 * mRef) / n + 2`. -/
theorem realizes_computeThreshProg : Realizes .exact
    (fun d : ℕ × ℕ => computeThreshProg d.1 d.2)
    WordEncoding.encode WordEncoding.encode computeThreshProgSafe
    (fun d _ => (2 * d.2) / d.1 + 2) := by
  unfold computeThreshProg
  realize [realizes_threshStep]
  · have := h.2.2; omega
  · exact h.1.of_le (by omega)
  · have := h.2.2; exact h.2.1.of_le (by omega)
  · have hdiv := Nat.div_le_self (2 * d.2) d.1; exact h.1.of_le (by omega)
  · have hct := computeThresh_realize_iterSafe (steps := (2 * d.2) / d.1) h
    rw [ite_eq_left ‹_›] at hct; exact hct
  · have := h.2.2; exact h.2.1.of_le (by omega)
  · have := h.2.2; omega
  · exact h.1.of_le (by omega)
  · have := h.2.2; exact h.2.1.of_le (by omega)
  · have hct := computeThresh_realize_iterSafe (steps := (2 * d.2) / d.1) h
    rw [ite_eq_right ‹_›] at hct; exact hct
  · rw [iterationWork_zero threshStep d.1 d.1 1 s,
        iterationWork_zero threshStep d.1 ((2 * d.2) / d.1) 1 s]
    split_ifs <;> omega

/-- Specification of `computeThreshProg`: returns `min n (2 ^ ((2 * mRef) / n))` with zero memory
reads/writes (`s' = s`, `memoryCost = 0`). -/
theorem computeThreshProg_spec {w n mRef : ℕ} {s : Memory.State}
    (hmRef : Fits w (2 * mRef + 1)) (h2n : Fits w (2 * n)) (hn1 : 1 ≤ n) :
    let prog := computeThreshProg n mRef
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    computeThreshProgSafe w (n, mRef) s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s' = s ∧
    res = min n (2 ^ ((2 * mRef) / n)) ∧
    1 ≤ res ∧ res ≤ n ∧
    memoryCost prog s = 0 := by
  let sh := (2 * mRef) / n
  let steps := if n < sh then n else sh
  have hsafe : computeThreshProgSafe w (n, mRef) s := ⟨hmRef, h2n, hn1⟩
  have hsteps_eq : steps = min n sh := by dsimp only [steps]; split_ifs <;> omega
  let inv (k a : ℕ) (t : Memory.State) : Prop := t = s ∧ a = min n (2 ^ k)
  have hiter := iterate_potential_spec threshStep threshStepSafe w n 0 steps inv
    (fun _ _ _ => 0) ∅ (fun k _ a t ⟨ht, ha⟩ => by
      have hs : threshStepSafe w (n, a) t := ⟨h2n, by rw [ha]; exact min_le_left _ _, hn1⟩
      have hv : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (threshStep (n, a))) := by
        dsimp only [threshStep]; split_ifs <;> exact validHistory_pure w _ _
      have hc : memoryCost (threshStep (n, a)) t ≤ 0 := by
        dsimp only [threshStep]; split_ifs <;> simp only [memoryCost_pure, le_rfl]
      have hst : (Memory.spec 0).clientState t (threshStep (n, a)) = t := by
        dsimp only [threshStep]; rw [prog_clientState_ite]; split_ifs <;> rfl
      have hres : (Memory.spec 0).clientResult t (threshStep (n, a)) = min n (2 ^ (k + 1)) := by
        dsimp only [threshStep]
        rw [prog_clientResult_ite, StateTransitionSpec.clientResult_pure,
          StateTransitionSpec.clientResult_pure, ha, Nat.pow_succ']
        by_cases hk : 2 ^ k ≤ n
        · rw [min_eq_right hk]; split_ifs <;> omega
        · have : n ≤ 2 ^ k := by omega
          rw [min_eq_left this]; split_ifs <;> omega
      refine ⟨hs, hv, by omega, by rw [hst]; exact Memory.Modifies.refl _ _,
        by rw [hst, hres]; exact ⟨ht, rfl⟩⟩)
    1 s ⟨rfl, by simp [min_eq_right hn1]⟩
  rcases hiter with ⟨_, hv, hc, _, hst_eq, hres_eq⟩
  have hprog_eq : computeThreshProg n mRef = iterate threshStep n steps 1 := by
    dsimp only [computeThreshProg, steps, sh]; split_ifs <;> rfl
  have hmin_eq : min n (2 ^ steps) = min n (2 ^ sh) := by
    rw [hsteps_eq]
    by_cases hns : n ≤ sh
    · rw [min_eq_left hns]
      have h1 : n ≤ 2 ^ n := Nat.lt_two_pow_self.le
      rw [min_eq_left h1, min_eq_left (h1.trans (Nat.pow_le_pow_right Nat.two_pos hns))]
    · rw [min_eq_right (by omega : sh ≤ n)]
  have hres_final :
      (Memory.spec 0).clientResult s (computeThreshProg n mRef) = min n (2 ^ sh) := by
    rw [hprog_eq, hres_eq, hmin_eq]
  refine ⟨hsafe, ?_, ?_, hres_final, ?_, ?_, ?_⟩
  · rw [hprog_eq]; exact hv
  · rw [hprog_eq]; exact hst_eq
  · rw [hres_final]; exact le_min hn1 Nat.one_le_two_pow
  · rw [hres_final]; exact min_le_left _ _
  · rw [hprog_eq]; omega


/-! ## Private Inner Sub-Programs and Word-Encoded Arguments -/

private structure FTRelaxUpdateArgs where
  ctx : FTCtx
  y : ℕ
  eIdx : ℕ
  ew : ℕ
  touchedLen : ℕ

private word_enc_structure encFTRelaxUpdateArgs : FTRelaxUpdateArgs where
  ctx : encFTCtx,
  y : wordWords,
  eIdx : wordWords,
  ew : wordWords,
  touchedLen : wordWords

private instance : WordEncoding FTRelaxUpdateArgs := ⟨13, encFTRelaxUpdateArgs⟩

private structure FTRelaxEnv where
  ctx : FTCtx
  treeId : ℕ
  pStart : ℕ

private word_enc_structure encFTRelaxEnv : FTRelaxEnv where
  ctx : encFTCtx,
  treeId : wordWords,
  pStart : wordWords

private instance : WordEncoding FTRelaxEnv := ⟨11, encFTRelaxEnv⟩

/-- Input bundle for `ftScanVertex`. -/
structure FTScanArgs where
  /-- Phase context. -/
  ctx : FTCtx
  /-- Root vertex id `t` of the active DJP tree. -/
  treeId : ℕ
  /-- Current vertex `x` whose CSR adjacency list is scanned. -/
  x : ℕ
  /-- Number of touched vertices currently recorded on the reset stack. -/
  touchedLen : ℕ

/-- Faithful twelve-word encoding of `FTScanArgs`. -/
word_enc_structure encFTScanArgs : FTScanArgs where
  ctx : encFTCtx,
  treeId : wordWords,
  x : wordWords,
  touchedLen : wordWords

instance : WordEncoding FTScanArgs := ⟨12, encFTScanArgs⟩


private def ftRelaxUpdate (d : FTRelaxUpdateArgs) : Memory.Prog ℕ := do
  let cur ← getKeyProg d.ctx.n d.ctx.fhBase d.y
  match cur with
  | none =>
    Memory.write (d.ctx.auxBase + d.ctx.n + d.y) d.eIdx
    Memory.write (d.ctx.auxBase + 4 * d.ctx.n + d.touchedLen) d.y
    insertProg d.ctx.n d.ctx.fhBase d.y d.ew
    pure (d.touchedLen + 1)
  | some oldW =>
    if d.ew < oldW then
      Memory.write (d.ctx.auxBase + d.ctx.n + d.y) d.eIdx
      decreaseKeyProg d.ctx.n d.ctx.fhBase d.y d.ew
      pure d.touchedLen
    else
      pure d.touchedLen

private def ftRelaxUpdateSafe (w : ℕ) (d : FTRelaxUpdateArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.ctx.fhBase + (9 * d.ctx.n + 5)) ∧ Fits w d.ctx.m ∧
    Fits w (d.ctx.auxBase + 5 * d.ctx.n) ∧ Fits w d.ew ∧
    d.y < d.ctx.n ∧ d.eIdx < d.ctx.m ∧ d.touchedLen < d.ctx.n ∧
    d.ctx.auxBase + 5 * d.ctx.n ≤ s.frontier ∧
    (d.ctx.auxBase + 5 * d.ctx.n ≤ d.ctx.fhBase ∨
      d.ctx.fhBase + 9 * d.ctx.n + 5 ≤ d.ctx.auxBase) ∧
    (let cur := (Memory.spec 0).clientResult s (getKeyProg d.ctx.n d.ctx.fhBase d.y)
     let s₁ := (Memory.spec 0).clientState s (getKeyProg d.ctx.n d.ctx.fhBase d.y)
     ∀ oldW, cur = some oldW → d.ew < oldW →
       decreaseValid w ![d.ctx.n, d.ctx.fhBase, d.y, d.ew]
         ⟨Function.update s₁.mem (d.ctx.auxBase + d.ctx.n + d.y) d.eIdx, s₁.frontier⟩)

private theorem realizes_ftRelaxUpdate : Realizes .exact
    ftRelaxUpdate WordEncoding.encode WordEncoding.encode ftRelaxUpdateSafe (fun _ _ => 0) := by
  unfold ftRelaxUpdate
  realize [realizes_getKeyProg, realizes_insertProg, realizes_decreaseKeyProg]
  all_goals
    rcases h with ⟨h16, hfh, hm, haux, hew, hy, he, htl, hfr, hdisj, hdec⟩
    have hfront := hmem.frontier_fits
    have hfr_gk := Memory.frontier_le_clientState (w := 0) s
      (getKeyProg d.ctx.n d.ctx.fhBase d.y)
    have hfr_w : ∀ t a v,
        ((Memory.spec 0).clientState t (Memory.write a v)).frontier = t.frontier :=
      fun _ _ _ => rfl
    simp only [hfr_w] at *
    first
    | exact hy
    | fits
    | omega
    | (cases hcur : (Memory.spec 0).clientResult s (getKeyProg d.ctx.n d.ctx.fhBase d.y) with
       | none =>
         have h0 : optionWords (none : Option ℕ) 0 = 0 := rfl
         simp only [hcur, h0] at *
         contradiction
       | some oldW =>
         have h0 : optionWords (some oldW : Option ℕ) 0 = 1 := rfl
         have h1 : optionWords (some oldW : Option ℕ) 1 = oldW := by simp [optionWords]
         simp only [hcur, h0, h1] at *
         exact hdec oldW rfl (by assumption))

private def ftRelaxOne (d : FTRelaxEnv × ℕ × ℕ) : Memory.Prog (ℕ × ℕ) := do
  let y ← Memory.read (d.1.ctx.adjBase + 2 * (d.1.pStart + d.2.1))
  let eIdx ← Memory.read (d.1.ctx.adjBase + 2 * (d.1.pStart + d.2.1) + 1)
  let trY ← Memory.read (d.1.ctx.auxBase + y)
  if trY = d.1.treeId then pure (d.2.1 + 1, d.2.2)
  else do
    let ew ← Memory.read (d.1.ctx.edgeBase + 4 * eIdx + 2)
    let tl' ← ftRelaxUpdate ⟨d.1.ctx, y, eIdx, ew, d.2.2⟩
    pure (d.2.1 + 1, tl')

private def ftRelaxOneSafe (w : ℕ) (d : FTRelaxEnv × ℕ × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.1.ctx.adjBase + 4 * d.1.ctx.m) ∧
    Fits w (d.1.ctx.edgeBase + 4 * d.1.ctx.m) ∧ Fits w (d.1.pStart + d.2.1 + 1) ∧
    d.1.pStart + d.2.1 < 2 * d.1.ctx.m ∧
    d.1.ctx.adjBase + 4 * d.1.ctx.m ≤ s.frontier ∧
    d.1.ctx.edgeBase + 4 * d.1.ctx.m ≤ s.frontier ∧
    d.1.ctx.auxBase + d.1.ctx.n ≤ s.frontier ∧
    (let y := s.mem (d.1.ctx.adjBase + 2 * (d.1.pStart + d.2.1))
     let eIdx := s.mem (d.1.ctx.adjBase + 2 * (d.1.pStart + d.2.1) + 1)
     y < d.1.ctx.n ∧ eIdx < d.1.ctx.m ∧
     (s.mem (d.1.ctx.auxBase + y) ≠ d.1.treeId →
       ftRelaxUpdateSafe w ⟨d.1.ctx, y, eIdx, s.mem (d.1.ctx.edgeBase + 4 * eIdx + 2), d.2.2⟩ s))

private theorem realizes_ftRelaxOne : Realizes .exact
    ftRelaxOne (appendWords encFTRelaxEnv WordEncoding.encode) WordEncoding.encode
    ftRelaxOneSafe (fun _ _ => 0) := by
  unfold ftRelaxOne
  realize [realizes_ftRelaxUpdate]
  all_goals
    rcases h with ⟨h16, hadj, hedge, hstep, h2m, hadj_fr, hedge_fr, haux_fr, hy, he, hupd⟩
    have hfront := hmem.frontier_fits
    first
    | exact hupd (by assumption)
    | fits

/-- Scan the undirected CSR adjacency list of `d.x` and relax outgoing edges into the heap. -/
def ftScanVertex (d : FTScanArgs) : Memory.Prog ℕ := do
  let pStart ← Memory.read (d.ctx.offBase + d.x)
  let pEnd ← Memory.read (d.ctx.offBase + d.x + 1)
  let res ← iterate ftRelaxOne ⟨d.ctx, d.treeId, pStart⟩ (pEnd - pStart) (0, d.touchedLen)
  pure res.2

/-- Word-width safety predicate for `ftScanVertex`. -/
def ftScanVertexSafe (w : ℕ) (d : FTScanArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.ctx.offBase + d.ctx.n + 1) ∧ Fits w (2 * d.ctx.m + 1) ∧
    d.x < d.ctx.n ∧ d.ctx.offBase + d.ctx.n + 1 ≤ s.frontier ∧
    let pStart := s.mem (d.ctx.offBase + d.x)
    let pEnd := s.mem (d.ctx.offBase + d.x + 1)
    pStart ≤ pEnd ∧ pEnd ≤ 2 * d.ctx.m ∧
    iterationSafe ftRelaxOne ftRelaxOneSafe w ⟨d.ctx, d.treeId, pStart⟩
      (pEnd - pStart) (0, d.touchedLen) s

/-- `ftScanVertex` is exact-realizable with zero auxiliary register work. -/
theorem realizes_ftScanVertex : Realizes .exact
    ftScanVertex WordEncoding.encode WordEncoding.encode ftScanVertexSafe (fun _ _ => 0) := by
  unfold ftScanVertex
  realize [realizes_ftRelaxOne]
  all_goals
    rcases h with ⟨h16, hoff, h2m, hx, hoff_fr, hp1, hp2, hiter⟩
    have hfront := hmem.frontier_fits
    first
    | exact iterationSafe_imp hiter (fun _ => rfl) (fun _ _ hs => hs)
    | fits
    | omega

/-- Every call to `ftScanVertex` issues at least one memory read (`offBase[x]`). -/
theorem one_le_memoryCost_ftScanVertex (d : FTScanArgs) (s : Memory.State) :
    1 ≤ memoryCost (ftScanVertex d) s := by
  rw [ftScanVertex, memoryCost_bind', memoryCost_read]
  omega


private theorem edgePartition_mem_iff_of_closed {n : ℕ} (L : List (WeightedEdge n ℕ))
    (A : Finset (Fin n)) (hclosed : ∀ f ∈ L, f.u ∈ A ↔ f.v ∈ A)
    {x y : Fin n} (hrel : (edgePartition L).rel x y = true) : x ∈ A ↔ y ∈ A := by
  rw [rel_edgePartition_iff_eqvGen] at hrel
  induction hrel with
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  | rel _ _ hxy => obtain ⟨f, hf, rfl, rfl⟩ := hxy; exact hclosed f hf


/-- Congruence for `framed.inv` across an equality `n₁ = n₂` of capacity parameters. -/
theorem framed_inv_congr {w n₁ n₂ K base : ℕ} (heq : n₁ = n₂)
    (hn₁ : Fits w n₁) (hn₂ : Fits w n₂) (hK : Fits w K) {s : Memory.State}
    (h : (framed hn₁ hK base).inv s) : (framed hn₂ hK base).inv s := by
  subst heq; exact h

/-- Congruence for `framed.abs` across an equality `n₁ = n₂` of capacity parameters. -/
theorem framed_abs_congr {w n₁ n₂ K base : ℕ} (heq : n₁ = n₂)
    (hn₁ : Fits w n₁) (hn₂ : Fits w n₂) (hK : Fits w K) (s : Memory.State)
    (v : Fin n₁) : (framed hn₁ hK base).abs s v =
      (framed hn₂ hK base).abs s ⟨v.val, heq ▸ v.isLt⟩ := by
  subst heq; rfl

/-- Congruence for Fibonacci heap potential across an equality `n₁ = n₂` of capacities. -/
theorem potential_congr {n₁ n₂ base : ℕ} (heq : n₁ = n₂) (s : Memory.State) :
    potential n₁ ((layout n₁ base).abs s) = potential n₂ ((layout n₂ base).abs s) := by
  subst heq; rfl

private theorem framed_abs_update_congr {w n₁ n₂ K base y : ℕ} (heq : n₁ = n₂)
    (hn₁ : Fits w n₁) (hn₂ : Fits w n₂) (hK : Fits w K) (s s' : Memory.State)
    (hy₁ : y < n₁) (hy₂ : y < n₂) (v : Option ℕ)
    (hu : (framed hn₁ hK base).abs s' =
      Function.update ((framed hn₁ hK base).abs s) ⟨y, hy₁⟩ v) :
    (framed hn₂ hK base).abs s' =
      Function.update ((framed hn₂ hK base).abs s) ⟨y, hy₂⟩ v := by
  subst heq; exact hu

private theorem ftRelaxUpdate_frame_best {w n K fhBase addr val : ℕ}
    {hn : Fits w n} {hK : Fits w K} {s s₁ : Memory.State}
    (hwf : Memory.WellFormed w s) (hfit : Fits w val)
    (hinv : (framed hn hK fhBase).inv s) (hs1 : s₁ = s)
    (hnot_fp : addr ∉ footprint n fhBase) :
    let s₂ : Memory.State := ⟨Function.update s₁.mem addr val, s₁.frontier⟩
    Memory.WellFormed w s₂ ∧ (framed hn hK fhBase).inv s₂ ∧
      (framed hn hK fhBase).abs s₂ = (framed hn hK fhBase).abs s ∧
      potential n ((layout n fhBase).abs s₂) = potential n ((layout n fhBase).abs s) := by
  intro s₂
  have hwf₂ : Memory.WellFormed w s₂ := by
    simpa only [s₂, hs1] using wellFormed_update hwf hfit
  have hs2_eq : ∀ a ∈ footprint n fhBase, s₂.mem a = s.mem a := fun a ha => by
    dsimp only [s₂]; rw [Function.update_of_ne (fun h => hnot_fp (by rw [← h]; exact ha)), hs1]
  obtain ⟨hinv₂, habs₂, hpot₂⟩ := framed_preserved hinv hs2_eq
    (by dsimp only [s₂]; rw [hs1]) (by dsimp only [s₂]; rw [hs1]; exact hwf.frontier_fits)
  exact ⟨hwf₂, hinv₂, habs₂, hpot₂⟩

private theorem ftRelaxUpdate_spec {w K : ℕ} {ctx : FTCtx} {y eIdx ew touchedLen : ℕ}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn : Fits w ctx.n) (hK : Fits w K) (hm : Fits w ctx.m)
    (hfit_fh : Fits w (ctx.fhBase + (9 * ctx.n + 5)))
    (hfit_aux : Fits w (ctx.auxBase + 5 * ctx.n))
    (hinv : (framed hn hK ctx.fhBase).inv s)
    (hy : y < ctx.n) (heIdx : eIdx < ctx.m) (hew : ew ≤ K)
    (htl : touchedLen < ctx.n) (haux_fr : ctx.auxBase + 5 * ctx.n ≤ s.frontier)
    (hdisj : ctx.auxBase + 5 * ctx.n ≤ ctx.fhBase ∨
      ctx.fhBase + 9 * ctx.n + 5 ≤ ctx.auxBase) :
    let prog := ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftRelaxUpdateSafe w ⟨ctx, y, eIdx, ew, touchedLen⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (framed hn hK ctx.fhBase).inv s' ∧
    (∀ a, a ∉ footprint ctx.n ctx.fhBase →
      a ≠ ctx.auxBase + ctx.n + y → a ≠ ctx.auxBase + 4 * ctx.n + touchedLen →
      s'.mem a = s.mem a) ∧
    (∀ z : Fin ctx.n, z.val ≠ y →
      s'.mem (ctx.auxBase + ctx.n + z.val) = s.mem (ctx.auxBase + ctx.n + z.val)) ∧
    (∀ i < touchedLen, s'.mem (ctx.auxBase + 4 * ctx.n + i) =
      s.mem (ctx.auxBase + 4 * ctx.n + i)) ∧
    (((framed hn hK ctx.fhBase).abs s ⟨y, hy⟩ = none ∧
      res = touchedLen + 1 ∧
      s'.mem (ctx.auxBase + ctx.n + y) = eIdx ∧
      s'.mem (ctx.auxBase + 4 * ctx.n + touchedLen) = y ∧
      (framed hn hK ctx.fhBase).abs s' =
        Function.update ((framed hn hK ctx.fhBase).abs s) ⟨y, hy⟩ (some ew) ∧
      memoryCost prog s + potential ctx.n ((layout ctx.n ctx.fhBase).abs s') ≤
        47 + potential ctx.n ((layout ctx.n ctx.fhBase).abs s)) ∨
     (∃ oldW, (framed hn hK ctx.fhBase).abs s ⟨y, hy⟩ = some oldW ∧
      res = touchedLen ∧
      (ew < oldW →
        s'.mem (ctx.auxBase + ctx.n + y) = eIdx ∧
        (framed hn hK ctx.fhBase).abs s' =
          Function.update ((framed hn hK ctx.fhBase).abs s) ⟨y, hy⟩ (some ew) ∧
        memoryCost prog s + potential ctx.n ((layout ctx.n ctx.fhBase).abs s') ≤
          107 + potential ctx.n ((layout ctx.n ctx.fhBase).abs s)) ∧
      (¬(ew < oldW) →
        s' = s ∧
        memoryCost prog s + potential ctx.n ((layout ctx.n ctx.fhBase).abs s') ≤
          2 + potential ctx.n ((layout ctx.n ctx.fhBase).abs s)))) := by
  have hgk := getKeyProg_spec hwf hn hK hinv hy
  dsimp only at hgk
  generalize h_cur : (Memory.spec 0).clientResult s (getKeyProg ctx.n ctx.fhBase y) = cur at hgk
  generalize h_s1 : (Memory.spec 0).clientState s (getKeyProg ctx.n ctx.fhBase y) = s₁ at hgk
  rcases hgk with ⟨hv_gk, hinv₁, hs1_eq, hcur_eq, hc_gk⟩
  have hew_fit : Fits w ew := hK.of_le hew
  have heIdx_fit : Fits w eIdx := hm.of_le heIdx.le
  have hy_fit : Fits w y := hn.of_le hy.le
  have hnot_fp_best : ctx.auxBase + ctx.n + y ∉ footprint ctx.n ctx.fhBase := by
    simp only [footprint, Finset.mem_Ico]; rcases hdisj with hd | hd <;> omega
  have hnot_fp_tch : ctx.auxBase + 4 * ctx.n + touchedLen ∉ footprint ctx.n ctx.fhBase := by
    simp only [footprint, Finset.mem_Ico]; rcases hdisj with hd | hd <;> omega
  have hsafe_dec : ∀ oldW, cur = some oldW → ew < oldW →
      decreaseValid w ![ctx.n, ctx.fhBase, y, ew]
        ⟨Function.update s₁.mem (ctx.auxBase + ctx.n + y) eIdx, s₁.frontier⟩ := by
    intro oldW hsome hlt
    obtain ⟨_, hinv₂, habs₂, _⟩ :=
      ftRelaxUpdate_frame_best hwf heIdx_fit hinv hs1_eq hnot_fp_best
    refine ⟨hfit_fh, hinv₂.1, ⟨y, hy⟩, K, oldW, rfl, hK, hinv₂.2, ?_, by dsimp; omega, hew⟩
    change (framed hn hK ctx.fhBase).abs
      ⟨Function.update s₁.mem (ctx.auxBase + ctx.n + y) eIdx, s₁.frontier⟩ ⟨y, hy⟩ = some oldW
    rw [habs₂, ← hcur_eq, hsome]
  have hsafe : ftRelaxUpdateSafe w ⟨ctx, y, eIdx, ew, touchedLen⟩ s := by
    refine ⟨h16, hfit_fh, hm, hfit_aux, hew_fit, hy, heIdx, htl, haux_fr, hdisj, ?_⟩
    rw [h_cur, h_s1]; exact hsafe_dec
  have hprog_eq : ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩ =
      (getKeyProg ctx.n ctx.fhBase y >>= fun cur => match cur with
        | none => do
          Memory.write (ctx.auxBase + ctx.n + y) eIdx
          Memory.write (ctx.auxBase + 4 * ctx.n + touchedLen) y
          insertProg ctx.n ctx.fhBase y ew
          pure (touchedLen + 1)
        | some oldW =>
          if ew < oldW then do
            Memory.write (ctx.auxBase + ctx.n + y) eIdx
            decreaseKeyProg ctx.n ctx.fhBase y ew
            pure touchedLen
          else pure touchedLen) := rfl
  have hbest_other_of : ∀ (m : ℕ → ℕ),
      (∀ a, a ∉ footprint ctx.n ctx.fhBase →
        a ≠ ctx.auxBase + ctx.n + y → a ≠ ctx.auxBase + 4 * ctx.n + touchedLen →
        m a = s.mem a) →
      (∀ z : Fin ctx.n, z.val ≠ y →
        m (ctx.auxBase + ctx.n + z.val) = s.mem (ctx.auxBase + ctx.n + z.val)) := by
    intro m hm_eq z hz
    exact hm_eq _ (by simp only [footprint, Finset.mem_Ico]; rcases hdisj with hd | hd <;> omega)
      (by intro h; apply hz; omega) (by omega)
  have htch_other_of : ∀ (m : ℕ → ℕ),
      (∀ a, a ∉ footprint ctx.n ctx.fhBase →
        a ≠ ctx.auxBase + ctx.n + y → a ≠ ctx.auxBase + 4 * ctx.n + touchedLen →
        m a = s.mem a) →
      (∀ i < touchedLen,
        m (ctx.auxBase + 4 * ctx.n + i) = s.mem (ctx.auxBase + 4 * ctx.n + i)) := by
    intro m hm_eq i hi
    exact hm_eq _ (by simp only [footprint, Finset.mem_Ico]; rcases hdisj with hd | hd <;> omega)
      (by omega) (by omega)
  cases hcur_cases : cur with
  | none =>
    have habs_y : (framed hn hK ctx.fhBase).abs s ⟨y, hy⟩ = none := by rw [← hcur_eq, hcur_cases]
    let s₂ : Memory.State := ⟨Function.update s₁.mem (ctx.auxBase + ctx.n + y) eIdx, s₁.frontier⟩
    let s₃ : Memory.State := ⟨Function.update s₂.mem (ctx.auxBase + 4 * ctx.n + touchedLen) y,
      s₁.frontier⟩
    have hwf₃ : Memory.WellFormed w s₃ := by
      have hwf₂ : Memory.WellFormed w s₂ := by
        simpa only [s₂, hs1_eq] using wellFormed_update hwf heIdx_fit
      simpa only [s₃, s₂] using wellFormed_update hwf₂ hy_fit
    have hfp_s3 : ∀ a ∈ footprint ctx.n ctx.fhBase, s₃.mem a = s.mem a := fun a ha => by
      dsimp only [s₃, s₂]
      rw [Function.update_of_ne (fun h => hnot_fp_tch (by rw [← h]; exact ha)),
        Function.update_of_ne (fun h => hnot_fp_best (by rw [← h]; exact ha)), hs1_eq]
    obtain ⟨hinv₃, habs₃, hpot₃⟩ :=
      framed_preserved hinv hfp_s3 (by dsimp only [s₃]; rw [hs1_eq])
        (by dsimp only [s₃]; rw [hs1_eq]; exact hwf.frontier_fits)
    have hins := insertProg_spec hwf₃ hn hK hinv₃ hy hew (by rw [habs₃]; exact habs_y)
    dsimp only at hins
    generalize h_s4 :
        (Memory.spec 0).clientState s₃ (insertProg ctx.n ctx.fhBase y ew) = s₄ at hins
    rcases hins with ⟨hv_ins, hinv₄, hfr₄, hwf₄, hmod₄, habs₄, hc_ins⟩
    have hv_all : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩)) := by
      rw [hprog_eq]
      refine validHistory_bind_step hv_gk ?_
      rw [h_cur, h_s1, hcur_cases]
      refine validHistory_write_bind (by rw [hs1_eq]; omega) heIdx_fit ?_
      refine validHistory_write_bind (by dsimp only [s₂]; rw [hs1_eq]; omega) hy_fit ?_
      exact validHistory_bind_step hv_ins (validHistory_pure w _ _)
    have hst_all : (Memory.spec 0).clientState s
        (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) = s₄ := by
      rw [hprog_eq, StateTransitionSpec.clientState_bind, h_cur, h_s1, hcur_cases,
        StateTransitionSpec.clientState_bind, clientState_write,
        StateTransitionSpec.clientState_bind, clientState_write,
        StateTransitionSpec.clientState_bind, h_s4, StateTransitionSpec.clientState_pure]
    have hres_all : (Memory.spec 0).clientResult s
        (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) = touchedLen + 1 := by
      rw [hprog_eq, StateTransitionSpec.clientResult_bind, h_cur, h_s1, hcur_cases]
      simp only [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    have hcost_all : memoryCost (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) s ≤
        2 + 2 + memoryCost (insertProg ctx.n ctx.fhBase y ew) s₃ := by
      rw [hprog_eq, memoryCost_bind', h_cur, h_s1, hcur_cases]
      dsimp only
      rw [memoryCost_bind', memoryCost_write, clientState_write,
        memoryCost_bind', memoryCost_write, clientState_write,
        memoryCost_bind', memoryCost_pure]
      dsimp only [s₃, s₂]; omega
    have hfr_s4 : s₄.frontier = s.frontier := by rw [hfr₄]; dsimp only [s₃]; rw [hs1_eq]
    have hmem_s4 : ∀ a, a ∉ footprint ctx.n ctx.fhBase →
        a ≠ ctx.auxBase + ctx.n + y → a ≠ ctx.auxBase + 4 * ctx.n + touchedLen →
        s₄.mem a = s.mem a := by
      intro a hfp hne1 hne2
      rw [hmod₄ a hfp]
      dsimp only [s₃, s₂]; rw [Function.update_of_ne hne2, Function.update_of_ne hne1, hs1_eq]
    have hbest_eq : s₄.mem (ctx.auxBase + ctx.n + y) = eIdx := by
      rw [hmod₄ _ hnot_fp_best]; dsimp only [s₃, s₂]; update_simp
    have htch_eq : s₄.mem (ctx.auxBase + 4 * ctx.n + touchedLen) = y := by
      rw [hmod₄ _ hnot_fp_tch]; dsimp only [s₃]; update_simp
    refine ⟨hsafe, hv_all, hst_all ▸ hfr_s4, hst_all ▸ hwf₄, hst_all ▸ hinv₄,
      fun a hfp h1 h2 => hst_all ▸ hmem_s4 a hfp h1 h2,
      hbest_other_of _ fun a hfp h1 h2 => hst_all ▸ hmem_s4 a hfp h1 h2,
      htch_other_of _ fun a hfp h1 h2 => hst_all ▸ hmem_s4 a hfp h1 h2,
      Or.inl ⟨habs_y, hres_all, hst_all ▸ hbest_eq, hst_all ▸ htch_eq,
        by rw [hst_all, habs₄, habs₃], by rw [hst_all]; omega⟩⟩
  | some oldW =>
    have habs_y : (framed hn hK ctx.fhBase).abs s ⟨y, hy⟩ = some oldW := by
      rw [← hcur_eq, hcur_cases]
    by_cases hlt : ew < oldW
    · let s₂ : Memory.State := ⟨Function.update s₁.mem (ctx.auxBase + ctx.n + y) eIdx, s₁.frontier⟩
      obtain ⟨hwf₂, hinv₂, habs₂, hpot₂⟩ :=
        ftRelaxUpdate_frame_best hwf heIdx_fit hinv hs1_eq hnot_fp_best
      change Memory.WellFormed w s₂ at hwf₂
      change (framed hn hK ctx.fhBase).inv s₂ at hinv₂
      change (framed hn hK ctx.fhBase).abs s₂ = _ at habs₂
      change potential ctx.n ((layout ctx.n ctx.fhBase).abs s₂) = _ at hpot₂
      have hdec := decreaseKeyProg_spec hwf₂ hn hK hinv₂ hy
        (by rw [habs₂]; exact habs_y) (by omega) hew
      dsimp only at hdec
      generalize h_s3 : (Memory.spec 0).clientState s₂
        (decreaseKeyProg ctx.n ctx.fhBase y ew) = s₃ at hdec
      rcases hdec with ⟨hv_dec, hinv₃, hfr₃, hwf₃, hmod₃, habs₃, hc_dec⟩
      have hv_all : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩)) := by
        rw [hprog_eq]
        refine validHistory_bind_step hv_gk ?_
        rw [h_cur, h_s1, hcur_cases]; simp only [hlt, ↓reduceIte]
        refine validHistory_write_bind (by rw [hs1_eq]; omega) heIdx_fit ?_
        exact validHistory_bind_step hv_dec (validHistory_pure w _ _)
      have hst_all : (Memory.spec 0).clientState s
          (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) = s₃ := by
        rw [hprog_eq, StateTransitionSpec.clientState_bind, h_cur, h_s1, hcur_cases]
        dsimp only; rw [ite_eq_left hlt, StateTransitionSpec.clientState_bind, clientState_write,
          StateTransitionSpec.clientState_bind, h_s3, StateTransitionSpec.clientState_pure]
      have hres_all : (Memory.spec 0).clientResult s
          (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) = touchedLen := by
        rw [hprog_eq, StateTransitionSpec.clientResult_bind, h_cur, h_s1, hcur_cases]
        dsimp only; rw [ite_eq_left hlt]
        simp only [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
      have hcost_all : memoryCost (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) s ≤
          2 + 1 + memoryCost (decreaseKeyProg ctx.n ctx.fhBase y ew) s₂ := by
        rw [hprog_eq, memoryCost_bind', h_cur, h_s1, hcur_cases]
        dsimp only; rw [ite_eq_left hlt, memoryCost_bind', memoryCost_write, clientState_write,
          memoryCost_bind', memoryCost_pure]
        dsimp only [s₂]; omega
      have hfr_s3 : s₃.frontier = s.frontier := by rw [hfr₃]; dsimp only [s₂]; rw [hs1_eq]
      have hmem_s3 : ∀ a, a ∉ footprint ctx.n ctx.fhBase →
          a ≠ ctx.auxBase + ctx.n + y → a ≠ ctx.auxBase + 4 * ctx.n + touchedLen →
          s₃.mem a = s.mem a := by
        intro a hfp hne1 _
        rw [hmod₃ a hfp]
        dsimp only [s₂]; rw [Function.update_of_ne hne1, hs1_eq]
      have hbest_eq : s₃.mem (ctx.auxBase + ctx.n + y) = eIdx := by
        rw [hmod₃ _ hnot_fp_best]; dsimp only [s₂]; update_simp
      refine ⟨hsafe, hv_all, hst_all ▸ hfr_s3, hst_all ▸ hwf₃, hst_all ▸ hinv₃,
        fun a hfp h1 h2 => hst_all ▸ hmem_s3 a hfp h1 h2,
        hbest_other_of _ fun a hfp h1 h2 => hst_all ▸ hmem_s3 a hfp h1 h2,
        htch_other_of _ fun a hfp h1 h2 => hst_all ▸ hmem_s3 a hfp h1 h2,
        Or.inr ⟨oldW, habs_y, hres_all, fun _ =>
          ⟨hst_all ▸ hbest_eq, by rw [hst_all, habs₃, habs₂], by rw [hst_all]; omega⟩,
          fun hno => absurd hlt hno⟩⟩
    · have hv_all : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩)) := by
        rw [hprog_eq]; refine validHistory_bind_step hv_gk ?_
        rw [h_cur, h_s1, hcur_cases]; simp only [hlt, ↓reduceIte]; exact validHistory_pure w _ _
      have hst_all : (Memory.spec 0).clientState s
          (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) = s := by
        rw [hprog_eq, StateTransitionSpec.clientState_bind, h_cur, h_s1, hcur_cases]
        dsimp only; rw [ite_eq_right hlt, StateTransitionSpec.clientState_pure]; exact hs1_eq
      have hres_all : (Memory.spec 0).clientResult s
          (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) = touchedLen := by
        rw [hprog_eq, StateTransitionSpec.clientResult_bind, h_cur, h_s1, hcur_cases]
        dsimp only; rw [ite_eq_right hlt, StateTransitionSpec.clientResult_pure]
      have hcost_all : memoryCost (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩) s ≤ 2 := by
        rw [hprog_eq, memoryCost_bind', h_cur, h_s1, hcur_cases]
        simp only [hlt, ↓reduceIte, memoryCost_pure]; omega
      refine ⟨hsafe, hv_all, by rw [hst_all], by rw [hst_all]; exact hwf,
        by rw [hst_all]; exact hinv, fun _ _ _ _ => by rw [hst_all],
        fun _ _ => by rw [hst_all], fun _ _ => by rw [hst_all],
        Or.inr ⟨oldW, habs_y, hres_all, fun h => absurd h hlt,
          fun _ => ⟨hst_all, by rw [hst_all]; omega⟩⟩⟩


private theorem ftScanVertex_update_cutInv {w n K tl tl' : ℕ} {hn : Fits w n} {hK : Fits w K}
    {ctx : FTCtx} {es : List (IndexedEdge n)} {t u y : Fin n} {eIdx : Fin es.length}
    {scanned : Finset (Fin n)} {s s' : Memory.State}
    (hcut : FTCutInv hn hK ctx es t scanned tl s)
    (hinv' : (framed hn hK ctx.fhBase).inv s')
    (htr_eq : ∀ z : Fin n, s'.mem (ctx.auxBase + z.val) = s.mem (ctx.auxBase + z.val))
    (ht_tr : t ∈ trSet ctx.auxBase n t s.mem)
    (hbest_y : s'.mem (ctx.auxBase + n + y.val) = eIdx.val)
    (hbest_other : ∀ z : Fin n, z ≠ y →
      s'.mem (ctx.auxBase + n + z.val) = s.mem (ctx.auxBase + n + z.val))
    (habs' : (framed hn hK ctx.fhBase).abs s' =
      Function.update ((framed hn hK ctx.fhBase).abs s) y (some es[eIdx.val].weight))
    (hy_not_tr : y ∉ trSet ctx.auxBase n t s.mem)
    (hu_tr : u ∈ trSet ctx.auxBase n t s.mem)
    (hrel : (es[eIdx.val].u = u ∧ es[eIdx.val].v = y) ∨
      (es[eIdx.val].v = u ∧ es[eIdx.val].u = y))
    (hbr : (tl' = tl ∧
        (∃ prev, (framed hn hK ctx.fhBase).abs s y = some prev ∧ es[eIdx.val].weight < prev) ∧
        ∀ i < tl, s'.mem (ctx.auxBase + 4 * n + i) = s.mem (ctx.auxBase + 4 * n + i)) ∨
      (tl' = tl + 1 ∧ (framed hn hK ctx.fhBase).abs s y = none ∧
        s'.mem (ctx.auxBase + 4 * n + tl) = y.val ∧
        ∀ i < tl, s'.mem (ctx.auxBase + 4 * n + i) = s.mem (ctx.auxBase + 4 * n + i))) :
    FTCutInv hn hK ctx es t scanned tl' s' := by
  have htr_set_eq : trSet ctx.auxBase n t s'.mem = trSet ctx.auxBase n t s.mem := by
    ext z; simp only [mem_trSet, htr_eq z]
  have hy_ne_t : y ≠ t := fun h => hy_not_tr (h ▸ ht_tr)
  have htl_fields : tl' ≤ n ∧
      (∀ i < tl', s'.mem (ctx.auxBase + 4 * n + i) < n) ∧
      (touchedList ctx.auxBase n tl' s'.mem).Nodup ∧
      (∀ i < tl', s'.mem (ctx.auxBase + 4 * n + i) ≠ t.val) ∧
      (∀ i < tl', ∀ (hv : s'.mem (ctx.auxBase + 4 * n + i) < n),
        ((framed hn hK ctx.fhBase).abs s' ⟨_, hv⟩).isSome ∨
          (⟨_, hv⟩ : Fin n) ∈ trSet ctx.auxBase n t s'.mem) ∧
      (∀ v : Fin n, ((framed hn hK ctx.fhBase).abs s' v).isSome →
        ∃ i < tl', s'.mem (ctx.auxBase + 4 * n + i) = v.val) := by
    rcases hbr with ⟨htl_eq, ⟨prev, hprev, _⟩, htch_eq⟩ |
        ⟨htl_eq, hnone, hnew, htch_eq⟩
    · have hnd : (touchedList ctx.auxBase n tl s'.mem).Nodup := by
        rw [touchedList_congr htch_eq]; exact hcut.htouched_nd
      rw [htl_eq]
      refine ⟨hcut.htl_le, fun i hi => by rw [htch_eq i hi]; exact hcut.htouched_lt i hi, hnd,
        fun i hi => by rw [htch_eq i hi]; exact hcut.htouched_ne_t i hi, fun i hi hv => ?_,
        fun v hv => ?_⟩
      · have hv0 : s.mem (ctx.auxBase + 4 * n + i) < n := by rw [← htch_eq i hi]; exact hv
        by_cases hvy : (⟨_, hv⟩ : Fin n) = y
        · left; rw [hvy, habs', Function.update_self]; rfl
        · have hne' : (⟨_, hv0⟩ : Fin n) ≠ y := fun h =>
            hvy (Fin.ext ((htch_eq i hi).trans (congrArg Fin.val h)))
          have hmem_v : (⟨_, hv⟩ : Fin n) = ⟨_, hv0⟩ := Fin.ext (htch_eq i hi)
          rw [hmem_v, habs', Function.update_of_ne hne', htr_set_eq]
          exact hcut.htouched_in i hi hv0
      · by_cases hvy : v = y
        · subst hvy
          obtain ⟨i, hi, heq⟩ := hcut.htouched_cov v (by simp [hprev])
          exact ⟨i, hi, by rw [htch_eq i hi, heq]⟩
        · rw [habs', Function.update_of_ne hvy] at hv
          obtain ⟨i, hi, heq⟩ := hcut.htouched_cov v hv
          exact ⟨i, hi, by rw [htch_eq i hi, heq]⟩
    · have hy_fresh : ∀ i < tl, s.mem (ctx.auxBase + 4 * n + i) ≠ y.val := by
        intro i hi heq
        have hv_lt : s.mem (ctx.auxBase + 4 * n + i) < n := heq ▸ y.isLt
        rcases hcut.htouched_in i hi hv_lt with hsome | htr
        · have hfe : (⟨s.mem (ctx.auxBase + 4 * n + i), hv_lt⟩ : Fin n) = y := Fin.ext heq
          rw [hfe, hnone] at hsome; contradiction
        · have hfe : (⟨s.mem (ctx.auxBase + 4 * n + i), hv_lt⟩ : Fin n) = y := Fin.ext heq
          exact hy_not_tr (hfe ▸ htr)
      have hlt' : ∀ i < tl + 1, s'.mem (ctx.auxBase + 4 * n + i) < n := fun i hi => by
        by_cases hil : i < tl
        · rw [htch_eq i hil]; exact hcut.htouched_lt i hil
        · have : i = tl := by omega
          subst this; rw [hnew]; exact y.isLt
      have hlist_eq : touchedList ctx.auxBase n (tl + 1) s'.mem =
          touchedList ctx.auxBase n tl s.mem ++ [y.val] := by
        simp only [touchedList_eq, List.range_succ, List.map_append, List.map_singleton, hnew]
        congr 1
        exact List.map_congr_left fun i hi => htch_eq i (List.mem_range.mp hi)
      have hnd : (touchedList ctx.auxBase n (tl + 1) s'.mem).Nodup := by
        rw [hlist_eq, List.nodup_append]
        refine ⟨hcut.htouched_nd, List.nodup_singleton _, fun a ha b hb => ?_⟩
        rw [List.mem_singleton] at hb; subst hb
        simp only [touchedList_eq] at ha
        obtain ⟨i, hi, heq⟩ := List.mem_map.mp ha
        rw [List.mem_range] at hi
        intro heq2; exact hy_fresh i hi (heq.trans heq2)
      have htl_le' : tl + 1 ≤ n := by
        have hlen : (touchedList ctx.auxBase n (tl + 1) s'.mem).length = tl + 1 := by
          simp [touchedList_eq]
        have hcard : (touchedList ctx.auxBase n (tl + 1) s'.mem).toFinset.card = tl + 1 := by
          rw [List.toFinset_card_of_nodup hnd, hlen]
        have hsub : (touchedList ctx.auxBase n (tl + 1) s'.mem).toFinset ⊆ Finset.range n := by
          intro a ha
          rw [List.mem_toFinset, touchedList_eq] at ha
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
          rw [List.mem_range] at hi
          rw [Finset.mem_range]
          exact hlt' i hi
        have hle := Finset.card_le_card hsub
        rw [hcard, Finset.card_range] at hle
        exact hle
      rw [htl_eq]
      refine ⟨htl_le', hlt', hnd, fun i hi => ?_, fun i hi hv => ?_, fun v hv => ?_⟩
      · by_cases hil : i < tl
        · rw [htch_eq i hil]; exact hcut.htouched_ne_t i hil
        · have : i = tl := by omega
          subst this; rw [hnew]; exact Fin.val_ne_of_ne hy_ne_t
      · by_cases hil : i < tl
        · have hv0 : s.mem (ctx.auxBase + 4 * n + i) < n := by
            rw [← htch_eq i hil]; exact hv
          by_cases hvy : (⟨_, hv⟩ : Fin n) = y
          · left; rw [hvy, habs', Function.update_self]; rfl
          · have hne' : (⟨_, hv0⟩ : Fin n) ≠ y := fun h =>
              hvy (Fin.ext ((htch_eq i hil).trans (congrArg Fin.val h)))
            have hmem_v : (⟨_, hv⟩ : Fin n) = ⟨_, hv0⟩ := Fin.ext (htch_eq i hil)
            rw [hmem_v, habs', Function.update_of_ne hne', htr_set_eq]
            exact hcut.htouched_in i hil hv0
        · have : i = tl := by omega
          subst this
          have hvy : (⟨_, hv⟩ : Fin n) = y := Fin.ext hnew
          left; rw [hvy, habs', Function.update_self]; rfl
      · by_cases hvy : v = y
        · subst hvy; exact ⟨tl, Nat.lt_succ_self tl, hnew⟩
        · rw [habs', Function.update_of_ne hvy] at hv
          obtain ⟨i, hi, heq⟩ := hcut.htouched_cov v hv
          exact ⟨i, Nat.lt_succ_of_lt hi, by rw [htch_eq i hi, heq]⟩
  refine ⟨hinv', htl_fields.1, htl_fields.2.1, htl_fields.2.2.1, htl_fields.2.2.2.1,
    htl_fields.2.2.2.2.1, htl_fields.2.2.2.2.2, fun v kv hkv => ?_, fun u' hu' e he => ?_⟩
  · rw [habs'] at hkv
    by_cases hvy : v = y
    · rw [hvy] at hkv ⊢; rw [Function.update_self] at hkv
      have hwt : es[eIdx.val].weight = kv := Option.some.inj hkv
      refine ⟨fun h => hy_not_tr (mem_trSet.mpr (by rw [← htr_eq y, h])),
        ⟨eIdx, hbest_y, hwt, ?_⟩⟩
      rw [htr_set_eq]
      rcases hrel with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;> exact ⟨h1 ▸ hu_tr, h2⟩
    · rw [Function.update_of_ne hvy] at hkv
      obtain ⟨hne, e0, he0_best, he0_wt, he0_end⟩ := hcut.hheap_cut v kv hkv
      refine ⟨by rw [htr_eq v]; exact hne, ⟨e0, ?_, he0_wt, ?_⟩⟩
      · exact (hbest_other v hvy).trans he0_best
      · rw [htr_set_eq]; exact he0_end
  · rw [htr_set_eq]
    obtain ⟨hL, hR⟩ := hcut.hscanned_cov u' hu' e he
    have upd_cov : ∀ (z : Fin n),
        (∃ kz, (framed hn hK ctx.fhBase).abs s z = some kz ∧ kz ≤ e.weight) →
        ∃ kz, (framed hn hK ctx.fhBase).abs s' z = some kz ∧ kz ≤ e.weight := by
      intro z ⟨kz, hkz, hle⟩
      by_cases hzy : z = y
      · subst hzy
        refine ⟨es[eIdx.val].weight, by rw [habs', Function.update_self], ?_⟩
        rcases hbr with ⟨_, ⟨prev, hprev, hlt⟩, _⟩ | ⟨_, hnone, _⟩
        · rw [hkz] at hprev; have := Option.some.inj hprev; omega
        · rw [hkz] at hnone; contradiction
      · exact ⟨kz, by rw [habs', Function.update_of_ne hzy]; exact hkz, hle⟩
    exact ⟨fun h => upd_cov e.v (hL h), fun h => upd_cov e.u (hR h)⟩


/-- Memory addresses modified by `ftScanVertex`: heap footprint, `bestEdge`, and `touched`. -/
@[expose] def scanMod (ctx : FTCtx) (n : ℕ) (a : ℕ) : Prop :=
  a ∈ footprint n ctx.fhBase ∨
  (ctx.auxBase + n ≤ a ∧ a < ctx.auxBase + 2 * n) ∨
  (ctx.auxBase + 4 * n ≤ a ∧ a < ctx.auxBase + 5 * n)

private theorem ftScanVertex_relax_cov {w n K pStart pEnd k : ℕ} {hn : Fits w n} {hK : Fits w K}
    {ctx : FTCtx} {es : List (IndexedEdge n)} {t y : Fin n} {eIdx : Fin es.length}
    {s s' : Memory.State}
    (hk : k < pEnd - pStart) (hpEnd_le : pEnd ≤ 2 * es.length)
    (hy_val : s.mem (ctx.adjBase + 2 * (pStart + k)) = y.val)
    (heIdx_eq : eIdx.val = s.mem (ctx.adjBase + 2 * (pStart + k) + 1))
    (hk_cov : ∀ j < k, ∀ (hv : s.mem (ctx.adjBase + 2 * (pStart + j)) < n)
      (he : s.mem (ctx.adjBase + 2 * (pStart + j) + 1) < es.length),
      (⟨_, hv⟩ : Fin n) ∉ trSet ctx.auxBase n t s.mem →
      ∃ kz, (framed hn hK ctx.fhBase).abs s ⟨_, hv⟩ = some kz ∧
        kz ≤ es[s.mem (ctx.adjBase + 2 * (pStart + j) + 1)].weight)
    (htr_set_eq : trSet ctx.auxBase n t s'.mem = trSet ctx.auxBase n t s.mem)
    (hadj_ro : ∀ p < 2 * es.length,
      s'.mem (ctx.adjBase + 2 * p) = s.mem (ctx.adjBase + 2 * p) ∧
      s'.mem (ctx.adjBase + 2 * p + 1) = s.mem (ctx.adjBase + 2 * p + 1))
    (habs_y : ∃ kz, (framed hn hK ctx.fhBase).abs s' y = some kz ∧
      kz ≤ es[eIdx.val].weight ∧
      ∀ old, (framed hn hK ctx.fhBase).abs s y = some old → kz ≤ old)
    (habs_ne : ∀ z : Fin n, z ≠ y →
      (framed hn hK ctx.fhBase).abs s' z = (framed hn hK ctx.fhBase).abs s z) :
    ∀ j < k + 1, ∀ (hv' : s'.mem (ctx.adjBase + 2 * (pStart + j)) < n)
      (he' : s'.mem (ctx.adjBase + 2 * (pStart + j) + 1) < es.length),
      (⟨_, hv'⟩ : Fin n) ∉ trSet ctx.auxBase n t s'.mem →
      ∃ kz, (framed hn hK ctx.fhBase).abs s' ⟨_, hv'⟩ = some kz ∧
        kz ≤ es[s'.mem (ctx.adjBase + 2 * (pStart + j) + 1)].weight := by
  intro j hj hv' he' hnot
  have hlt_p : pStart + j < 2 * es.length := by omega
  obtain ⟨hj1, hj2⟩ := hadj_ro (pStart + j) hlt_p
  by_cases hjk : j < k
  · have hnot0 : (⟨s.mem (ctx.adjBase + 2 * (pStart + j)), by rw [← hj1]; exact hv'⟩ : Fin n) ∉
        trSet ctx.auxBase n t s.mem := by
      intro hmem; apply hnot; rw [htr_set_eq]
      simpa only [mem_trSet, hj1] using hmem
    obtain ⟨kz, hkz, hle⟩ := hk_cov j hjk (by rw [← hj1]; exact hv')
      (by rw [← hj2]; exact he') hnot0
    have hkz' : (framed hn hK ctx.fhBase).abs s
        ⟨s'.mem (ctx.adjBase + 2 * (pStart + j)), hv'⟩ = some kz := by
      simpa only [hj1] using hkz
    have hle' : kz ≤ es[s'.mem (ctx.adjBase + 2 * (pStart + j) + 1)].weight := by
      have hi_fin : (⟨s'.mem (ctx.adjBase + 2 * (pStart + j) + 1), he'⟩ : Fin es.length) =
          ⟨s.mem (ctx.adjBase + 2 * (pStart + j) + 1), by rw [← hj2]; exact he'⟩ :=
        Fin.ext hj2
      have hw := congrArg (fun q : Fin es.length => es[q.val].weight) hi_fin
      dsimp only at hw; omega
    by_cases hzy : (⟨_, hv'⟩ : Fin n) = y
    · obtain ⟨ky, hky, _, hky_le⟩ := habs_y
      rw [hzy] at hkz' ⊢
      exact ⟨ky, hky, le_trans (hky_le kz hkz') hle'⟩
    · exact ⟨kz, (habs_ne _ hzy).trans hkz', hle'⟩
  · have : j = k := by omega
    subst j
    have hi_fin : (⟨s'.mem (ctx.adjBase + 2 * (pStart + k) + 1), he'⟩ : Fin es.length) = eIdx :=
      Fin.ext (hj2.trans heIdx_eq.symm)
    have hw := congrArg (fun q : Fin es.length => es[q.val].weight) hi_fin
    dsimp only at hw
    obtain ⟨ky, hky, hky_wt, _⟩ := habs_y
    have hv_eq : (⟨s'.mem (ctx.adjBase + 2 * (pStart + k)), hv'⟩ : Fin n) = y :=
      Fin.ext (hj1.trans hy_val)
    exact ⟨ky, by rw [hv_eq]; exact hky, by omega⟩


private theorem ftRelaxUpdate_spec_n {w n m K : ℕ} {ctx : FTCtx} {y eIdx ew touchedLen : ℕ}
    {s : Memory.State} (hcn : ctx.n = n) (hcm : ctx.m = m)
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn : Fits w n) (hK : Fits w K) (hm : Fits w m)
    (hfit_fh : Fits w (ctx.fhBase + (9 * n + 5)))
    (hfit_aux : Fits w (ctx.auxBase + 5 * n))
    (hinv : (framed hn hK ctx.fhBase).inv s)
    (hy : y < n) (heIdx : eIdx < m) (hew : ew ≤ K)
    (htl : touchedLen < n) (haux_fr : ctx.auxBase + 5 * n ≤ s.frontier)
    (hdisj : ctx.auxBase + 5 * n ≤ ctx.fhBase ∨
      ctx.fhBase + 9 * n + 5 ≤ ctx.auxBase) :
    let prog := ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftRelaxUpdateSafe w ⟨ctx, y, eIdx, ew, touchedLen⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (framed hn hK ctx.fhBase).inv s' ∧
    (∀ a, a ∉ footprint n ctx.fhBase →
      a ≠ ctx.auxBase + n + y → a ≠ ctx.auxBase + 4 * n + touchedLen →
      s'.mem a = s.mem a) ∧
    (∀ z : Fin n, z.val ≠ y →
      s'.mem (ctx.auxBase + n + z.val) = s.mem (ctx.auxBase + n + z.val)) ∧
    (∀ i < touchedLen, s'.mem (ctx.auxBase + 4 * n + i) =
      s.mem (ctx.auxBase + 4 * n + i)) ∧
    (((framed hn hK ctx.fhBase).abs s ⟨y, hy⟩ = none ∧
      res = touchedLen + 1 ∧
      s'.mem (ctx.auxBase + n + y) = eIdx ∧
      s'.mem (ctx.auxBase + 4 * n + touchedLen) = y ∧
      (framed hn hK ctx.fhBase).abs s' =
        Function.update ((framed hn hK ctx.fhBase).abs s) ⟨y, hy⟩ (some ew) ∧
      memoryCost prog s + potential n ((layout n ctx.fhBase).abs s') ≤
        47 + potential n ((layout n ctx.fhBase).abs s)) ∨
     (∃ oldW, (framed hn hK ctx.fhBase).abs s ⟨y, hy⟩ = some oldW ∧
      res = touchedLen ∧
      (ew < oldW →
        s'.mem (ctx.auxBase + n + y) = eIdx ∧
        (framed hn hK ctx.fhBase).abs s' =
          Function.update ((framed hn hK ctx.fhBase).abs s) ⟨y, hy⟩ (some ew) ∧
        memoryCost prog s + potential n ((layout n ctx.fhBase).abs s') ≤
          107 + potential n ((layout n ctx.fhBase).abs s)) ∧
      (¬(ew < oldW) →
        s' = s ∧
        memoryCost prog s + potential n ((layout n ctx.fhBase).abs s') ≤
          2 + potential n ((layout n ctx.fhBase).abs s)))) := by
  have hn_c : Fits w ctx.n := by rw [hcn]; exact hn
  have hm_c : Fits w ctx.m := by rw [hcm]; exact hm
  have hinv_c : (framed hn_c hK ctx.fhBase).inv s :=
    framed_inv_congr hcn.symm hn hn_c hK hinv
  have hraw := ftRelaxUpdate_spec (K := K) h16 hwf hn_c hK hm_c
    (by rw [hcn]; exact hfit_fh) (by rw [hcn]; exact hfit_aux) hinv_c
    (y := y) (eIdx := eIdx) (ew := ew) (touchedLen := touchedLen)
    (by rw [hcn]; exact hy) (by rw [hcm]; exact heIdx) hew (by rw [hcn]; exact htl)
    (by rw [hcn]; exact haux_fr)
    (by rcases hdisj with hd | hd <;> [left; right] <;> rw [hcn] <;> exact hd)
  dsimp only at hraw
  rcases hraw with ⟨hs, hv, hfr, hwf', hinv', hmod, hbest_o, htch_o, hbr⟩
  have cast_abs : ∀ m z, (framed hn hK ctx.fhBase).abs m z =
      (framed hn_c hK ctx.fhBase).abs m ⟨z.val, hcn.symm ▸ z.isLt⟩ :=
    fun m z => framed_abs_congr hcn.symm hn hn_c hK m z
  have cast_upd : ∀ s₁ s₂ (hy_c : y < ctx.n),
      (framed hn_c hK ctx.fhBase).abs s₂ =
        Function.update ((framed hn_c hK ctx.fhBase).abs s₁) ⟨y, hy_c⟩ (some ew) →
      (framed hn hK ctx.fhBase).abs s₂ =
        Function.update ((framed hn hK ctx.fhBase).abs s₁) ⟨y, hy⟩ (some ew) :=
    fun s₁ s₂ hy_c hu => framed_abs_update_congr hcn hn_c hn hK s₁ s₂ hy_c hy (some ew) hu
  have hpot_s : potential n ((layout n ctx.fhBase).abs s) =
      potential ctx.n ((layout ctx.n ctx.fhBase).abs s) := potential_congr hcn.symm s
  have hpot_s' : potential n ((layout n ctx.fhBase).abs
        ((Memory.spec 0).clientState s (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩))) =
      potential ctx.n ((layout ctx.n ctx.fhBase).abs
        ((Memory.spec 0).clientState s (ftRelaxUpdate ⟨ctx, y, eIdx, ew, touchedLen⟩))) :=
    potential_congr hcn.symm _
  refine ⟨hs, hv, hfr, hwf', framed_inv_congr hcn hn_c hn hK hinv',
    fun a hfp h1 h2 => hmod a (by rw [hcn]; exact hfp) (by rw [hcn]; exact h1)
      (by rw [hcn]; exact h2),
    fun z hz => by simpa only [hcn] using hbest_o ⟨z.val, hcn.symm ▸ z.isLt⟩ hz,
    fun i hi => by simpa only [hcn] using htch_o i hi, ?_⟩
  rcases hbr with ⟨hnone, hres, hb, ht, hu, hc⟩ | ⟨oldW, hsome, hres, hlt, hge⟩
  · left
    refine ⟨by rw [cast_abs s ⟨y, hy⟩]; exact hnone, hres,
      by rw [show ctx.auxBase + n + y = ctx.auxBase + ctx.n + y by rw [hcn]]; exact hb,
      by rw [show ctx.auxBase + 4 * n + touchedLen =
          ctx.auxBase + 4 * ctx.n + touchedLen by rw [hcn]]; exact ht,
      cast_upd s _ _ hu, by rw [hpot_s, hpot_s']; exact hc⟩
  · right
    refine ⟨oldW, by rw [cast_abs s ⟨y, hy⟩]; exact hsome, hres, fun h => ?_, fun h => ?_⟩
    · obtain ⟨hb, hu, hc⟩ := hlt h
      exact ⟨by rw [show ctx.auxBase + n + y = ctx.auxBase + ctx.n + y by rw [hcn]]; exact hb,
        cast_upd s _ _ hu, by rw [hpot_s, hpot_s']; exact hc⟩
    · obtain ⟨heq, hc⟩ := hge h
      exact ⟨heq, by rw [hpot_s, hpot_s']; exact hc⟩


/-- Inductive adjacency-scan coverage invariant through index `k` of `[pStart, pEnd)`. -/
private def ScanStepCov {w n K : ℕ} (hn : Fits w n) (hK : Fits w K)
    (ctx : FTCtx) (es : List (IndexedEdge n)) (t : Fin n) (pStart k : ℕ)
    (s : Memory.State) : Prop :=
  ∀ j < k, ∀ (hv : s.mem (ctx.adjBase + 2 * (pStart + j)) < n)
    (he : s.mem (ctx.adjBase + 2 * (pStart + j) + 1) < es.length),
    (⟨_, hv⟩ : Fin n) ∉ trSet ctx.auxBase n t s.mem →
    ∃ kz, (framed hn hK ctx.fhBase).abs s ⟨_, hv⟩ = some kz ∧
      kz ≤ es[s.mem (ctx.adjBase + 2 * (pStart + j) + 1)].weight

private theorem ftScanVertex_step {w n K mRef selLen0 pStart pEnd k tl : ℕ}
    {hn : Fits w n} {hK : Fits w K} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {t x : Fin n} {scanned : Finset (Fin n)} {s : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s)
    (hwf : Memory.WellFormed w s)
    (ht_tr : t ∈ trSet ctx.auxBase n t s.mem)
    (hx_tr : x ∈ trSet ctx.auxBase n t s.mem)
    (hcut : FTCutInv hn hK ctx es t scanned tl s)
    (hpStart : pStart = s.mem (ctx.offBase + x.val))
    (hpEnd : pEnd = s.mem (ctx.offBase + x.val + 1))
    (hk : k < pEnd - pStart)
    (hk_cov : ∀ j < k, ∀ (hv : s.mem (ctx.adjBase + 2 * (pStart + j)) < n)
      (he : s.mem (ctx.adjBase + 2 * (pStart + j) + 1) < es.length),
      (⟨_, hv⟩ : Fin n) ∉ trSet ctx.auxBase n t s.mem →
      ∃ kz, (framed hn hK ctx.fhBase).abs s ⟨_, hv⟩ = some kz ∧
        kz ≤ es[s.mem (ctx.adjBase + 2 * (pStart + j) + 1)].weight) :
    let d : FTRelaxEnv × ℕ × ℕ := ⟨⟨ctx, t.val, pStart⟩, k, tl⟩
    let prog := ftRelaxOne d
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftRelaxOneSafe w d s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    memoryCost prog s + potential n ((layout n ctx.fhBase).abs s') + 2 * res.2 ≤
      potential n ((layout n ctx.fhBase).abs s) + 2 * tl + 117 ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, ¬scanMod ctx n a → s'.mem a = s.mem a) ∧
    res.1 = k + 1 ∧
    FTCutInv hn hK ctx es t scanned res.2 s' ∧
    res.2 ≤ tl + 1 ∧
    (∀ j < k + 1, ∀ (hv : s'.mem (ctx.adjBase + 2 * (pStart + j)) < n)
      (he : s'.mem (ctx.adjBase + 2 * (pStart + j) + 1) < es.length),
      (⟨_, hv⟩ : Fin n) ∉ trSet ctx.auxBase n t s'.mem →
      ∃ kz, (framed hn hK ctx.fhBase).abs s' ⟨_, hv⟩ = some kz ∧
        kz ≤ es[s'.mem (ctx.adjBase + 2 * (pStart + j) + 1)].weight) := by
  have hcn := hs.cn; have hcm := hs.cm
  have hmem_slice : (s.mem (ctx.adjBase + 2 * (pStart + k)),
      s.mem (ctx.adjBase + 2 * (pStart + k) + 1)) ∈
      (List.range (s.mem (ctx.offBase + x.val + 1) - s.mem (ctx.offBase + x.val))).map
        (fun j => let p := s.mem (ctx.offBase + x.val) + j
          (s.mem (ctx.adjBase + 2 * p), s.mem (ctx.adjBase + 2 * p + 1))) :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr (by rw [← hpStart, ← hpEnd]; exact hk), by
      rw [← hpStart]⟩
  obtain ⟨eIdx, heIdx_eq, heIdx_end⟩ :=
    (hs.hcsr.mem_slice_iff x _ _).mp hmem_slice
  obtain ⟨y, hy_val, hrel_e⟩ : ∃ y : Fin n,
      s.mem (ctx.adjBase + 2 * (pStart + k)) = y.val ∧
      ((es[eIdx.val].u = x ∧ es[eIdx.val].v = y) ∨
       (es[eIdx.val].v = x ∧ es[eIdx.val].u = y)) := by
    rcases heIdx_end with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨es[eIdx.val].v, h2.symm, Or.inl ⟨h1, rfl⟩⟩
    · exact ⟨es[eIdx.val].u, h2.symm, Or.inr ⟨h1, rfl⟩⟩
  have hpEnd_le : pEnd ≤ 2 * es.length := by
    rw [hpEnd]; exact hs.hcsr.offset_le_end (x.val + 1) x.isLt
  have hpstep_lt : pStart + k < 2 * ctx.m := by omega
  have hpstep_fit : Fits w (pStart + k + 1) := hs.fit2m.of_le (by omega)
  have hprog_eq : ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩ =
      (Memory.read (ctx.adjBase + 2 * (pStart + k)) >>= fun yv =>
       Memory.read (ctx.adjBase + 2 * (pStart + k) + 1) >>= fun eIv =>
       Memory.read (ctx.auxBase + yv) >>= fun trY =>
       if trY = t.val then pure (k + 1, tl)
       else
         Memory.read (ctx.edgeBase + 4 * eIv + 2) >>= fun ew =>
         ftRelaxUpdate ⟨ctx, yv, eIv, ew, tl⟩ >>= fun tl' => pure (k + 1, tl')) := rfl
  have hnot_scan : ∀ a, ¬scanMod ctx n a →
      (ctx.edgeBase ≤ a ∧ a < ctx.edgeBase + 4 * es.length) ∨
      (ctx.adjBase ≤ a ∧ a < ctx.adjBase + 4 * es.length) ∨
      (ctx.offBase ≤ a ∧ a < ctx.offBase + n + 1) → True := fun _ _ _ => trivial
  have haux_ctx : ctx.auxBase + ctx.n ≤ s.frontier := by
    have hfr := hs.auxFr; rw [hcn]
    exact Nat.le_trans (Nat.add_le_add_left (by omega : n ≤ 5 * n) _) hfr
  by_cases htrY : s.mem (ctx.auxBase + y.val) = t.val
  · have hsafe : ftRelaxOneSafe w ⟨⟨ctx, t.val, pStart⟩, k, tl⟩ s := by
      unfold ftRelaxOneSafe; dsimp only
      refine ⟨hs.fit16, by rw [hcm]; exact hs.fitAdj, by rw [hcm]; exact hs.fitEdge,
        hpstep_fit, hpstep_lt, by rw [hcm]; exact hs.adjFr, by rw [hcm]; exact hs.edgeFr,
        haux_ctx, ?_⟩
      refine ⟨by rw [hy_val, hcn]; exact y.isLt, by rw [← heIdx_eq, hcm]; exact eIdx.isLt,
        fun hbad => absurd (by rw [hy_val]; exact htrY) hbad⟩
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩)) := by
      rw [hprog_eq]
      refine validHistory_read_bind (by have := hs.adjFr; omega) ?_
      refine validHistory_read_bind (by have := hs.adjFr; omega) ?_
      refine validHistory_read_bind (by have := hs.auxFr; have := y.isLt; omega) ?_
      rw [ite_eq_left (by rw [hy_val]; exact htrY)]
      exact validHistory_pure w _ _
    have hst : (Memory.spec 0).clientState s
        (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩) = s := by
      rw [hprog_eq, StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        ite_eq_left (by rw [hy_val]; exact htrY), StateTransitionSpec.clientState_pure]
    have hres : (Memory.spec 0).clientResult s
        (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩) = (k + 1, tl) := by
      rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        ite_eq_left (by rw [hy_val]; exact htrY), StateTransitionSpec.clientResult_pure]
    have hcost : memoryCost (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩) s ≤ 3 := by
      rw [hprog_eq, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        ite_eq_left (by rw [hy_val]; exact htrY), memoryCost_pure]
    have hcov_fin : ScanStepCov hn hK ctx es t pStart (k + 1)
        ((Memory.spec 0).clientState s (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩)) := by
      rw [hst]
      intro j hj hv' he' hnot
      by_cases hjk : j < k
      · exact hk_cov j hjk hv' he' hnot
      · have : j = k := by omega
        subst j
        exfalso; apply hnot
        rw [mem_trSet]; dsimp only; rw [hy_val]; exact htrY
    refine ⟨hsafe, hv, by rw [hst, hres]; omega, by rw [hst], by rw [hst]; exact hwf,
      fun _ _ => by rw [hst], by rw [hres], by rw [hst, hres]; exact hcut,
      by rw [hres]; omega, hcov_fin⟩
  · have hy_not_tr : y ∉ trSet ctx.auxBase n t s.mem := by
      intro hy_mem; rw [mem_trSet] at hy_mem; exact htrY hy_mem
    have hew_eq : s.mem (ctx.edgeBase + 4 * eIdx.val + 2) = es[eIdx.val].weight :=
      (hs.hin eIdx.val eIdx.isLt).2.2.1
    have htl_lt : tl < ctx.n := by
      have hsub : (touchedList ctx.auxBase n tl s.mem).toFinset ⊆
          (Finset.range n).erase t.val := by
        intro a ha
        rw [List.mem_toFinset, touchedList_eq] at ha
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
        rw [List.mem_range] at hi
        exact Finset.mem_erase.mpr ⟨hcut.htouched_ne_t i hi,
          Finset.mem_range.mpr (hcut.htouched_lt i hi)⟩
      have hcard := Finset.card_le_card hsub
      have hlen : (touchedList ctx.auxBase n tl s.mem).length = tl := by simp [touchedList_eq]
      rw [List.toFinset_card_of_nodup hcut.htouched_nd, hlen,
        Finset.card_erase_of_mem (Finset.mem_range.mpr t.isLt), Finset.card_range] at hcard
      have := t.isLt; omega
    have hupd := ftRelaxUpdate_spec_n hcn hcm hs.fit16 hwf hn hK (hs.fit2m.of_le (by omega))
      hs.fitFh hs.fitAux hcut.hinv y.isLt eIdx.isLt (hs.hKes _ (List.getElem_mem eIdx.isLt))
      (by rw [← hcn]; exact htl_lt) hs.auxFr (Or.inr hs.fhLtAux)
    dsimp only at hupd
    generalize h_ru_r : (Memory.spec 0).clientResult s
      (ftRelaxUpdate ⟨ctx, y.val, eIdx.val, es[eIdx.val].weight, tl⟩) = tl' at hupd
    generalize h_ru_s : (Memory.spec 0).clientState s
      (ftRelaxUpdate ⟨ctx, y.val, eIdx.val, es[eIdx.val].weight, tl⟩) = s' at hupd
    rcases hupd with ⟨hsafe_u, hv_u, hfr_u, hwf_u, hinv_u, hmod_u, hbest_other, htch_other, hbr_u⟩
    have hy_eta : (⟨y.val, y.isLt⟩ : Fin n) = y := Fin.eta y y.isLt
    rw [hy_eta] at hbr_u
    have hsafe : ftRelaxOneSafe w ⟨⟨ctx, t.val, pStart⟩, k, tl⟩ s := by
      unfold ftRelaxOneSafe; dsimp only
      refine ⟨hs.fit16, by rw [hcm]; exact hs.fitAdj, by rw [hcm]; exact hs.fitEdge,
        hpstep_fit, hpstep_lt, by rw [hcm]; exact hs.adjFr, by rw [hcm]; exact hs.edgeFr,
        haux_ctx, ?_⟩
      refine ⟨by rw [hy_val, hcn]; exact y.isLt, by rw [← heIdx_eq, hcm]; exact eIdx.isLt,
        fun _ => ?_⟩
      rw [hy_val, ← heIdx_eq, hew_eq]
      exact hsafe_u
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩)) := by
      rw [hprog_eq]
      refine validHistory_read_bind (by have := hs.adjFr; omega) ?_
      refine validHistory_read_bind (by have := hs.adjFr; omega) ?_
      refine validHistory_read_bind (by have := hs.auxFr; have := y.isLt; omega) ?_
      rw [ite_eq_right (by rw [hy_val]; exact htrY)]
      refine validHistory_read_bind (by have := hs.edgeFr; omega) ?_
      rw [hy_val, ← heIdx_eq, hew_eq]
      exact validHistory_bind_step hv_u (validHistory_pure w _ _)
    have hst : (Memory.spec 0).clientState s
        (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩) = s' := by
      rw [hprog_eq, StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
        ite_eq_right (by rw [hy_val]; exact htrY),
        StateTransitionSpec.clientState_bind, clientState_read, clientResult_read]
      rw [hy_val, ← heIdx_eq, hew_eq, StateTransitionSpec.clientState_bind, h_ru_s,
        StateTransitionSpec.clientState_pure]
    have hres : (Memory.spec 0).clientResult s
        (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩) = (k + 1, tl') := by
      rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        ite_eq_right (by rw [hy_val]; exact htrY),
        StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read]
      rw [hy_val, ← heIdx_eq, hew_eq, StateTransitionSpec.clientResult_bind, h_ru_r,
        StateTransitionSpec.clientResult_pure]
    have hmod_s' : ∀ a, ¬scanMod ctx n a → s'.mem a = s.mem a := by
      intro a ha
      simp only [scanMod, not_or] at ha
      exact hmod_u a ha.1 (fun heq => ha.2.1 (by rw [heq]; omega))
        (fun heq => ha.2.2 (by rw [heq]; omega))
    have htr_eq : ∀ z : Fin n, s'.mem (ctx.auxBase + z.val) = s.mem (ctx.auxBase + z.val) :=
      fun z => hmod_s' _ (by
        simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
        have := hs.fhLtAux; have := z.isLt
        exact ⟨by omega, fun _ => by omega, fun _ => by omega⟩)
    have htr_set_eq : trSet ctx.auxBase n t s'.mem = trSet ctx.auxBase n t s.mem := by
      ext z; simp only [mem_trSet, htr_eq z]
    have hadj_ro : ∀ p < 2 * es.length,
        s'.mem (ctx.adjBase + 2 * p) = s.mem (ctx.adjBase + 2 * p) ∧
        s'.mem (ctx.adjBase + 2 * p + 1) = s.mem (ctx.adjBase + 2 * p + 1) := by
      intro p hp
      have h1 : ¬scanMod ctx n (ctx.adjBase + 2 * p) := by
        simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
        have := hs.adjLtFh; have := hs.fhLtAux; omega
      have h2 : ¬scanMod ctx n (ctx.adjBase + 2 * p + 1) := by
        simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
        have := hs.adjLtFh; have := hs.fhLtAux; omega
      exact ⟨hmod_s' _ h1, hmod_s' _ h2⟩
    have hcost_core : memoryCost (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩) s ≤
        4 + memoryCost (ftRelaxUpdate ⟨ctx, y.val, eIdx.val, es[eIdx.val].weight, tl⟩) s := by
      rw [hprog_eq, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        ite_eq_right (by rw [hy_val]; exact htrY),
        memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
      rw [hy_val, ← heIdx_eq, hew_eq, memoryCost_bind', h_ru_s, memoryCost_pure]
      omega
    have hpot : memoryCost (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩) s +
        potential n ((layout n ctx.fhBase).abs s') + 2 * tl' ≤
        potential n ((layout n ctx.fhBase).abs s) + 2 * tl + 117 := by
      rcases hbr_u with ⟨_, hres_u, _, _, _, hcu⟩ | ⟨oldW, _, hres_u, hlt_b, hge_b⟩
      · omega
      · by_cases hlt_w : es[eIdx.val].weight < oldW
        · have := (hlt_b hlt_w).2.2; omega
        · have := (hge_b hlt_w).2; omega
    have mk_cut : ∀ (hbest_n : s'.mem (ctx.auxBase + n + y.val) = eIdx.val)
        (habs_n : (framed hn hK ctx.fhBase).abs s' =
          Function.update ((framed hn hK ctx.fhBase).abs s) y (some es[eIdx.val].weight))
        (hbr_n : (tl' = tl ∧ (∃ prev, (framed hn hK ctx.fhBase).abs s y = some prev ∧
            es[eIdx.val].weight < prev) ∧
            ∀ i < tl, s'.mem (ctx.auxBase + 4 * n + i) = s.mem (ctx.auxBase + 4 * n + i)) ∨
          (tl' = tl + 1 ∧ (framed hn hK ctx.fhBase).abs s y = none ∧
            s'.mem (ctx.auxBase + 4 * n + tl) = y.val ∧
            ∀ i < tl, s'.mem (ctx.auxBase + 4 * n + i) = s.mem (ctx.auxBase + 4 * n + i))),
        FTCutInv hn hK ctx es t scanned tl' s' := fun hbest_n habs_n hbr_n =>
      ftScanVertex_update_cutInv hcut hinv_u htr_eq ht_tr hbest_n
        (fun z hz => hbest_other z (Fin.val_ne_of_ne hz)) habs_n hy_not_tr hx_tr hrel_e hbr_n
    have hcut_and_abs : FTCutInv hn hK ctx es t scanned tl' s' ∧ tl' ≤ tl + 1 ∧
        (∃ kz, (framed hn hK ctx.fhBase).abs s' y = some kz ∧ kz ≤ es[eIdx.val].weight ∧
          ∀ old, (framed hn hK ctx.fhBase).abs s y = some old → kz ≤ old) ∧
        (∀ z : Fin n, z ≠ y →
          (framed hn hK ctx.fhBase).abs s' z = (framed hn hK ctx.fhBase).abs s z) := by
      rcases hbr_u with ⟨hnone, hres_u, hbest_u, htch_u, habs_u, _⟩ |
          ⟨oldW, hsome, hres_u, hlt_b, hge_b⟩
      · have hcut' := mk_cut hbest_u habs_u
          (Or.inr ⟨hres_u, hnone, htch_u, htch_other⟩)
        refine ⟨hcut', by omega, ⟨es[eIdx.val].weight, by rw [habs_u, Function.update_self],
          le_rfl, fun old hold => by rw [hnone] at hold; exact absurd hold (by simp)⟩,
          fun z hz => by rw [habs_u, Function.update_of_ne hz]⟩
      · by_cases hlt_w : es[eIdx.val].weight < oldW
        · obtain ⟨hbest_u, habs_u, _⟩ := hlt_b hlt_w
          have hcut' := mk_cut hbest_u habs_u
            (Or.inl ⟨hres_u, ⟨oldW, hsome, hlt_w⟩, htch_other⟩)
          refine ⟨hcut', by omega, ⟨es[eIdx.val].weight, by rw [habs_u, Function.update_self],
            le_rfl, fun old hold => by
            rw [hsome] at hold; have : oldW = old := Option.some.inj hold; omega⟩,
            fun z hz => by rw [habs_u, Function.update_of_ne hz]⟩
        · obtain ⟨hs'_eq, _⟩ := hge_b hlt_w
          have hcut' : FTCutInv hn hK ctx es t scanned tl' s' := by
            rw [hs'_eq, hres_u]; exact hcut
          refine ⟨hcut', by omega, ⟨oldW, by rw [hs'_eq]; exact hsome, by omega,
            fun old hold => by
              rw [hsome] at hold; have : oldW = old := Option.some.inj hold; omega⟩,
            fun z _ => by rw [hs'_eq]⟩
    have hcov_fin := ftScanVertex_relax_cov hk hpEnd_le hy_val heIdx_eq hk_cov htr_set_eq
      hadj_ro hcut_and_abs.2.2.1 hcut_and_abs.2.2.2
    have hcov_end : ScanStepCov hn hK ctx es t pStart (k + 1)
        ((Memory.spec 0).clientState s (ftRelaxOne ⟨⟨ctx, t.val, pStart⟩, k, tl⟩)) := by
      rw [hst]; exact hcov_fin
    refine ⟨hsafe, hv, by rw [hst, hres]; exact hpot, by rw [hst]; exact hfr_u,
      by rw [hst]; exact hwf_u, fun a ha => by rw [hst]; exact hmod_s' a ha,
      by rw [hres], by rw [hst, hres]; exact hcut_and_abs.1,
      by rw [hres]; exact hcut_and_abs.2.1, hcov_end⟩


/-- Specification of `ftScanVertex`: scans CSR neighbors of `x`, updates `bestEdge`, relaxes
the Fibonacci heap, appends newly touched vertices, and preserves `FTCutInv` and amortized
heap + touched-stack potential. -/
theorem ftScanVertex_spec {w n K mRef selLen0 tl₀ : ℕ}
    {hn : Fits w n} {hK : Fits w K} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {t x : Fin n} {scanned : Finset (Fin n)} {s : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s)
    (hwf : Memory.WellFormed w s)
    (ht_tr : t ∈ trSet ctx.auxBase n t s.mem)
    (hx_tr : x ∈ trSet ctx.auxBase n t s.mem)
    (hcut : FTCutInv hn hK ctx es t scanned tl₀ s) :
    let prog := ftScanVertex ⟨ctx, t.val, x.val, tl₀⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftScanVertexSafe w ⟨ctx, t.val, x.val, tl₀⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, ¬scanMod ctx n a → s'.mem a = s.mem a) ∧
    FTCutInv hn hK ctx es t (insert x scanned) res s' ∧
    memoryCost prog s + potential n ((layout n ctx.fhBase).abs s') + 2 * res ≤
      potential n ((layout n ctx.fhBase).abs s) + 2 * tl₀ +
        117 * (s.mem (ctx.offBase + x.val + 1) - s.mem (ctx.offBase + x.val)) + 2 := by
  have hcn := hs.cn; have hcm := hs.cm
  let pStart := s.mem (ctx.offBase + x.val)
  let pEnd := s.mem (ctx.offBase + x.val + 1)
  have hp_le : pStart ≤ pEnd := hs.hcsr.off_mono x
  have hpEnd_le : pEnd ≤ 2 * es.length := hs.hcsr.offset_le_end (x.val + 1) x.isLt
  have hstatic_ro : ∀ (u : Memory.State), s.frontier ≤ u.frontier →
      (∀ a, ¬scanMod ctx n a → u.mem a = s.mem a) →
      FTStatic w n K mRef selLen0 ctx es u := fun u hfr hmod =>
    hs.of_step hfr fun a ha => hmod a (by
      simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
      have := hs.edgeLtFh; have := hs.offLtFh; have := hs.adjLtFh; have := hs.fhLtAux
      rcases ha with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> omega)
  let inv (k : ℕ) (acc : ℕ × ℕ) (u : Memory.State) : Prop :=
    acc.1 = k ∧ u.frontier = s.frontier ∧ Memory.WellFormed w u ∧
    (∀ a, ¬scanMod ctx n a → u.mem a = s.mem a) ∧
    t ∈ trSet ctx.auxBase n t u.mem ∧ x ∈ trSet ctx.auxBase n t u.mem ∧
    FTCutInv hn hK ctx es t scanned acc.2 u ∧
    (∀ j < k, ∀ (hv : u.mem (ctx.adjBase + 2 * (pStart + j)) < n)
      (he : u.mem (ctx.adjBase + 2 * (pStart + j) + 1) < es.length),
      (⟨_, hv⟩ : Fin n) ∉ trSet ctx.auxBase n t u.mem →
      ∃ kz, (framed hn hK ctx.fhBase).abs u ⟨_, hv⟩ = some kz ∧
        kz ≤ es[u.mem (ctx.adjBase + 2 * (pStart + j) + 1)].weight)
  let pot (_ : ℕ) (acc : ℕ × ℕ) (u : Memory.State) : ℕ :=
    potential n ((layout n ctx.fhBase).abs u) + 2 * acc.2
  have hiter := iterate_potential_spec ftRelaxOne ftRelaxOneSafe w
    ⟨ctx, t.val, pStart⟩ 117 (pEnd - pStart) inv pot {a | scanMod ctx n a}
    (fun k hk acc u ⟨hk_eq, hufr, huwf, humod, hut, hux, hucut, hucov⟩ => by
      have hpStart_u : pStart = u.mem (ctx.offBase + x.val) :=
        (humod _ (by
          simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
          have := hs.offLtFh; have := hs.fhLtAux; have := x.isLt; omega)).symm
      have hpEnd_u : pEnd = u.mem (ctx.offBase + x.val + 1) :=
        (humod _ (by
          simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
          have := hs.offLtFh; have := hs.fhLtAux; have := x.isLt; omega)).symm
      have hhs_u := hstatic_ro u (by rw [hufr]) humod
      have hst := ftScanVertex_step hhs_u huwf hut hux hucut hpStart_u hpEnd_u hk
        (by
          intro j hj hv he hnot
          have hp_lt : pStart + j < 2 * es.length := by omega
          exact hucov j hj hv he hnot)
      have hacc_eq : ((⟨ctx, t.val, pStart⟩ : FTRelaxEnv), acc) =
          (⟨ctx, t.val, pStart⟩, k, acc.2) := by
        ext <;> simp [hk_eq]
      rw [← hacc_eq] at hst
      rcases hst with ⟨hs_step, hv_step, hpot_step, hfr_step, hwf_step, hmod_step, hres1_step,
        hcut_step, _, hcov_step⟩
      let u' := (Memory.spec 0).clientState u (ftRelaxOne (⟨ctx, t.val, pStart⟩, acc))
      have hmod_step' : ∀ a, ¬scanMod ctx n a → u'.mem a = s.mem a := fun a ha =>
        (hmod_step a ha).trans (humod a ha)
      have htr_u' : ∀ z : Fin n, u'.mem (ctx.auxBase + z.val) = u.mem (ctx.auxBase + z.val) :=
        fun z => hmod_step _ (by
          simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
          have := hs.fhLtAux; have := z.isLt; omega)
      have hut' : t ∈ trSet ctx.auxBase n t u'.mem := by
        simpa only [mem_trSet, htr_u' t] using hut
      have hux' : x ∈ trSet ctx.auxBase n t u'.mem := by
        simpa only [mem_trSet, htr_u' x] using hux
      refine ⟨hs_step, hv_step, by dsimp only [pot]; omega,
        ⟨by rw [hfr_step, hufr], fun a _ ha => hmod_step a ha⟩,
        hres1_step, hfr_step.trans hufr, hwf_step, hmod_step', hut', hux', hcut_step, hcov_step⟩)
    (0, tl₀) s ⟨rfl, rfl, hwf, fun _ _ => rfl, ht_tr, hx_tr, hcut, fun _ h => absurd h (by omega)⟩
  dsimp only at hiter
  generalize h_res : (Memory.spec 0).clientResult s
    (iterate ftRelaxOne ⟨ctx, t.val, pStart⟩ (pEnd - pStart) (0, tl₀)) = res at hiter
  generalize h_s' : (Memory.spec 0).clientState s
    (iterate ftRelaxOne ⟨ctx, t.val, pStart⟩ (pEnd - pStart) (0, tl₀)) = s' at hiter
  rcases hiter with
    ⟨hsafe_it, hv_it, hpot_it, hmod_it, ⟨_, hfr', hwf', hmod', ht', hx', hcut', hcov'⟩⟩
  have hprog_eq : ftScanVertex ⟨ctx, t.val, x.val, tl₀⟩ =
      (Memory.read (ctx.offBase + x.val) >>= fun ps =>
       Memory.read (ctx.offBase + x.val + 1) >>= fun pe =>
       iterate ftRelaxOne ⟨ctx, t.val, ps⟩ (pe - ps) (0, tl₀) >>= fun r => pure r.2) := rfl
  have hsafe : ftScanVertexSafe w ⟨ctx, t.val, x.val, tl₀⟩ s :=
    ⟨hs.fit16, by rw [hcn]; exact hs.fitOff, by rw [hcm]; exact hs.fit2m,
      by rw [hcn]; exact x.isLt, by rw [hcn]; exact hs.offFr,
      hp_le, by rw [hcm]; exact hpEnd_le, hsafe_it⟩
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (ftScanVertex ⟨ctx, t.val, x.val, tl₀⟩)) := by
    rw [hprog_eq]
    refine validHistory_read_bind (by have := x.isLt; have := hs.offFr; omega) ?_
    refine validHistory_read_bind (by have := x.isLt; have := hs.offFr; omega) ?_
    exact validHistory_bind_step hv_it (validHistory_pure w _ _)
  have hst : (Memory.spec 0).clientState s (ftScanVertex ⟨ctx, t.val, x.val, tl₀⟩) = s' := by
    rw [hprog_eq, StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
      StateTransitionSpec.clientState_bind, clientState_read, clientResult_read,
      StateTransitionSpec.clientState_bind, h_s', StateTransitionSpec.clientState_pure]
  have hres : (Memory.spec 0).clientResult s (ftScanVertex ⟨ctx, t.val, x.val, tl₀⟩) = res.2 := by
    rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
      StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
      StateTransitionSpec.clientResult_bind, h_res, StateTransitionSpec.clientResult_pure]
  have hcost : memoryCost (ftScanVertex ⟨ctx, t.val, x.val, tl₀⟩) s ≤
      2 + memoryCost (iterate ftRelaxOne ⟨ctx, t.val, pStart⟩ (pEnd - pStart) (0, tl₀)) s := by
    rw [hprog_eq, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
      memoryCost_bind', h_s', memoryCost_pure]
    change 1 + (1 + (memoryCost (iterate ftRelaxOne ⟨ctx, t.val, pStart⟩
      (pEnd - pStart) (0, tl₀)) s + 0)) ≤ _
    omega
  have hhs' := hstatic_ro s' (by rw [hfr']) hmod'
  have hcut_fin : FTCutInv hn hK ctx es t (insert x scanned) res.2 s' := by
    refine ⟨hcut'.hinv, hcut'.htl_le, hcut'.htouched_lt, hcut'.htouched_nd, hcut'.htouched_ne_t,
      hcut'.htouched_in, hcut'.htouched_cov, hcut'.hheap_cut, fun u' hu' e he => ?_⟩
    rw [Finset.mem_insert] at hu'
    rcases hu' with rfl | hu_sc
    · have hp_ro : s'.mem (ctx.offBase + u'.val) = pStart ∧
          s'.mem (ctx.offBase + u'.val + 1) = pEnd := ⟨hmod' _ (by
        simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
        have := hs.offLtFh; have := hs.fhLtAux; have := u'.isLt; omega), hmod' _ (by
        simp only [scanMod, footprint, Finset.mem_Ico, not_or, not_and]
        have := hs.offLtFh; have := hs.fhLtAux; have := u'.isLt; omega)⟩
      have of_edge : ∀ z : Fin n,
          ((e.u = u' ∧ e.v = z) ∨ (e.v = u' ∧ e.u = z)) → z ∉ trSet ctx.auxBase n t s'.mem →
          ∃ kz, (framed hn hK ctx.fhBase).abs s' z = some kz ∧ kz ≤ e.weight := by
        intro z hrel hz_not
        obtain ⟨i, hi_mem⟩ : ∃ i : Fin es.length, es[i.val] = e := by
          obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp he
          exact ⟨⟨i, hi⟩, heq⟩
        have hmem_sl := (hhs'.hcsr.mem_slice_iff u' z.val i.val).mpr ⟨i, rfl, by
          rw [hi_mem]
          rcases hrel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> [left; right] <;> exact ⟨rfl, rfl⟩⟩
        rw [hp_ro.1, hp_ro.2] at hmem_sl
        obtain ⟨j, hj, hpair⟩ := List.mem_map.mp hmem_sl
        rw [List.mem_range] at hj
        have hpair' := Prod.ext_iff.mp hpair
        dsimp only at hpair'
        have hz_lt : s'.mem (ctx.adjBase + 2 * (pStart + j)) < n := by rw [hpair'.1]; exact z.isLt
        have hi_lt : s'.mem (ctx.adjBase + 2 * (pStart + j) + 1) < es.length := by
          rw [hpair'.2]; exact i.isLt
        obtain ⟨kz, hkz, hle⟩ := hcov' j hj hz_lt hi_lt (by
          have hz_eq : (⟨s'.mem (ctx.adjBase + 2 * (pStart + j)), hz_lt⟩ : Fin n) = z :=
            Fin.ext hpair'.1
          rwa [hz_eq])
        have hz_eq : (⟨s'.mem (ctx.adjBase + 2 * (pStart + j)), hz_lt⟩ : Fin n) = z :=
          Fin.ext hpair'.1
        rw [hz_eq] at hkz
        have hi_fin : (⟨s'.mem (ctx.adjBase + 2 * (pStart + j) + 1), hi_lt⟩ : Fin es.length) =
            i := Fin.ext hpair'.2
        have hw := congrArg (fun q : Fin es.length => es[q.val].weight) hi_fin
        rw [hw, hi_mem] at hle
        exact ⟨kz, hkz, hle⟩
      exact ⟨fun ⟨h1, h2⟩ => of_edge e.v (.inl ⟨h1, rfl⟩) h2,
        fun ⟨h1, h2⟩ => of_edge e.u (.inr ⟨h1, rfl⟩) h2⟩
    · exact hcut'.hscanned_cov u' hu_sc e he
  refine ⟨hsafe, hv, by rw [hst]; exact hfr', by rw [hst]; exact hwf',
    fun a ha => by rw [hst]; exact hmod' a ha, by rw [hst, hres]; exact hcut_fin, ?_⟩
  rw [hst, hres]
  dsimp only [pot] at hpot_it
  omega


/-- Memory addresses modified during DJP tree growth for root `t`. -/
@[expose] def growMod (ctx : FTCtx) (n selLen0 sel0Len : ℕ) (a : ℕ) : Prop :=
  a ∈ footprint n ctx.fhBase ∨
  (ctx.auxBase ≤ a ∧ a < ctx.auxBase + 2 * n) ∨
  (ctx.auxBase + 4 * n ≤ a ∧ a < ctx.auxBase + 5 * n) ∨
  (ctx.selBufBase + selLen0 + sel0Len ≤ a ∧ a < ctx.selBufBase + selLen0 + n)

/-- Every address modified by `ftScanVertex` lies in `growMod`. -/
theorem scanMod_imp_growMod {ctx : FTCtx} {n selLen0 sel0Len a : ℕ}
    (h : scanMod ctx n a) : growMod ctx n selLen0 sel0Len a := by
  rcases h with h1 | h2 | h3
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨by omega, h2.2⟩)
  · exact Or.inr (Or.inr (Or.inl h3))

/-- Inner DJP bounded-heap tree-growth invariant relating `FTGrowState` and `Memory.State`. -/
structure FTGrowInv {w n K : ℕ} (hn : Fits w n) (hK : Fits w K)
    (ctx : FTCtx) (es : List (IndexedEdge n)) (t : Fin n)
    (nComp selLen0 : ℕ) (selIdxs0 : List (Fin es.length)) (s₀ : Memory.State)
    (selTree : List (Fin es.length)) (scanned : Finset (Fin n))
    (st : FTGrowState) (s : Memory.State) : Prop where
  /-- Memory frontier is unchanged from tree start `s₀`. -/
  hfr : s.frontier = s₀.frontier
  /-- Memory state remains word-well-formed. -/
  hwf : Memory.WellFormed w s
  /-- Continuation flag is boolean (`0` or `1`). -/
  hgo_bin : st.go = 0 ∨ st.go = 1
  /-- Memory outside `growMod` agrees with `s₀`. -/
  hmod : ∀ a, ¬growMod ctx n selLen0 selIdxs0.length a → s.mem a = s₀.mem a
  /-- Root `t` belongs to the current tree set. -/
  ht_tr : t ∈ trSet ctx.auxBase n t s.mem
  /-- All `tr` entries are `< t`, `= t`, or `= n`. -/
  hbound : ∀ v : Fin n,
    s.mem (ctx.auxBase + v.val) < t.val ∨
    s.mem (ctx.auxBase + v.val) = t.val ∨
    s.mem (ctx.auxBase + v.val) = n
  /-- Every vertex currently in `trSet` was unvisited (`tr = n`) at tree start `s₀`. -/
  htr_new : ∀ v ∈ trSet ctx.auxBase n t s.mem, s₀.mem (ctx.auxBase + v.val) = n
  /-- Every `tr[v]` either equals `s₀` or newly entered tree `t` from `n`. -/
  htr_rel : ∀ v : Fin n, s.mem (ctx.auxBase + v.val) = s₀.mem (ctx.auxBase + v.val) ∨
    (s₀.mem (ctx.auxBase + v.val) = n ∧ s.mem (ctx.auxBase + v.val) = t.val)
  /-- Framed Fibonacci heap invariant holds. -/
  hinv : (framed hn hK ctx.fhBase).inv s
  /-- Touched-stack length fits in `n`. -/
  htl_le : st.touchedLen ≤ n
  /-- Every touched-stack entry is `< n`. -/
  htouched_lt : ∀ i < st.touchedLen, s.mem (ctx.auxBase + 4 * n + i) < n
  /-- Every vertex in the Fibonacci heap appears in the touched stack. -/
  htouched_cov : ∀ v : Fin n, ((framed hn hK ctx.fhBase).abs s v).isSome →
    ∃ i < st.touchedLen, s.mem (ctx.auxBase + 4 * n + i) = v.val
  /-- Recorded selection buffer length matches `selLen0 + (selIdxs0 ++ selTree).length`. -/
  hsel_len : st.selLen = selLen0 + (selIdxs0 ++ selTree).length
  /-- Selected edge + component count invariant across merged/unmerged termination. -/
  hsel_card : (selIdxs0 ++ selTree).length + nComp +
      (if st.go = 0 ∧ st.jn < t.val then 0 else 1) =
    (visitedSet ctx.auxBase n t.val s₀.mem).card + (trSet ctx.auxBase n t s.mem).card
  /-- Accumulated selected edge indices are duplicate-free. -/
  hsel_nd : (selIdxs0 ++ selTree).Nodup
  /-- Prior-tree selected edges lie inside `visitedSet`. -/
  hphase_verts : ∀ idx ∈ selIdxs0,
    es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∧
    es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem
  /-- All selected edges lie inside `visitedSet ∪ trSet`. -/
  hsel_verts : ∀ idx ∈ selIdxs0 ++ selTree,
    es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∪ trSet ctx.auxBase n t s.mem ∧
    es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem ∪ trSet ctx.auxBase n t s.mem
  /-- Selected edges form an acyclic forest. -/
  hacyclic : IsAcyclic (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
    IndexedEdge.toWeighted)
  /-- Selected edges extend to a minimum spanning forest of `es`. -/
  hext : ∃ F_ext : List (WeightedEdge n ℕ),
    IsMinSpanningForest (es.map IndexedEdge.toWeighted)
      ((((selIdxs0 ++ selTree).map fun i => es[i.val]).map
        IndexedEdge.toWeighted) ++ F_ext)
  /-- Newly selected edge ids appear consecutively in `selBuf`. -/
  hsel_buf : ∀ j (hj : j < selTree.length),
    s.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) = es[selTree[j].val].id
  /-- Branch invariant: continuing (`go = 1`) vs stopped (`go = 0`: closed/heavy or merged). -/
  hgo : if st.go = 1 then
      FTCutInv hn hK ctx es t scanned st.touchedLen s ∧
      ∃ x : Fin n, st.x = x.val ∧ x ∈ trSet ctx.auxBase n t s.mem ∧ x ∉ scanned ∧
        trSet ctx.auxBase n t s.mem = insert x scanned ∧
        (∀ idx ∈ selTree,
          es[idx.val].u ∈ trSet ctx.auxBase n t s.mem ∧
          es[idx.val].v ∈ trSet ctx.auxBase n t s.mem) ∧
        (∀ x' ∈ trSet ctx.auxBase n t s.mem, ∀ y' ∈ trSet ctx.auxBase n t s.mem,
          (edgePartition (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
            IndexedEdge.toWeighted)).rel x' y' = true)
    else
      scanned = trSet ctx.auxBase n t s.mem ∧
      ((st.jn = n ∧
        (∀ idx ∈ selTree,
          es[idx.val].u ∈ trSet ctx.auxBase n t s.mem ∧
          es[idx.val].v ∈ trSet ctx.auxBase n t s.mem) ∧
        (∀ x' ∈ trSet ctx.auxBase n t s.mem, ∀ y' ∈ trSet ctx.auxBase n t s.mem,
          (edgePartition (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
            IndexedEdge.toWeighted)).rel x' y' = true) ∧
        ((∀ e ∈ es, (e.u ∈ trSet ctx.auxBase n t s.mem ↔ e.v ∈ trSet ctx.auxBase n t s.mem)) ∨
          ∃ Z : Finset (Fin n), ctx.thresh + 1 ≤ Z.card ∧
            ∀ z ∈ Z, z ∉ trSet ctx.auxBase n t s.mem ∧
              ∃ e ∈ es,
                (e.u ∈ trSet ctx.auxBase n t s.mem ∧ e.v = z) ∨
                (e.v ∈ trSet ctx.auxBase n t s.mem ∧ e.u = z))) ∨
       (st.jn < t.val ∧ selTree ≠ [] ∧
        ∃ eIdx : Fin es.length, selTree.getLast? = some eIdx ∧
          (∀ idx ∈ selTree.dropLast,
            es[idx.val].u ∈ trSet ctx.auxBase n t s.mem ∧
            es[idx.val].v ∈ trSet ctx.auxBase n t s.mem) ∧
          (∀ x' ∈ trSet ctx.auxBase n t s.mem, ∀ y' ∈ trSet ctx.auxBase n t s.mem,
            (edgePartition (((selIdxs0 ++ selTree.dropLast).map fun i => es[i.val]).map
              IndexedEdge.toWeighted)).rel x' y' = true) ∧
          ∃ y : Fin n, ∃ u : Fin n, u ∈ trSet ctx.auxBase n t s.mem ∧
            s₀.mem (ctx.auxBase + y.val) = st.jn ∧
            ((es[eIdx.val].u = u ∧ es[eIdx.val].v = y) ∨
              (es[eIdx.val].v = u ∧ es[eIdx.val].u = y))))

/-- Vertex potential drop across scanning vertex `x` during tree growth. -/
theorem grow_vertexSum_step_le {n mRef : ℕ} {ctx : FTCtx} {t x : Fin n}
    {st st' : FTGrowState} {m m' : ℕ → ℕ}
    (hoff : ∀ v : Fin n,
      m' (ctx.offBase + v.val) = m (ctx.offBase + v.val) ∧
      m' (ctx.offBase + v.val + 1) = m (ctx.offBase + v.val + 1))
    (hx_before : m (ctx.auxBase + x.val) = t.val ∧ st.go = 1 ∧ x.val = st.x)
    (hx_after : m' (ctx.auxBase + x.val) = t.val ∧ ¬(st'.go = 1 ∧ x.val = st'.x))
    (hother : ∀ v : Fin n, v ≠ x → m (ctx.auxBase + v.val) = t.val →
      m' (ctx.auxBase + v.val) = t.val ∧ ¬(st'.go = 1 ∧ v.val = st'.x)) :
    (∑ v : Fin n,
      if m' (ctx.auxBase + v.val) = t.val ∧ ¬(st'.go = 1 ∧ v.val = st'.x) then 0
      else vertexPot ctx n mRef v m') + vertexPot ctx n mRef x m ≤
    ∑ v : Fin n,
      if m (ctx.auxBase + v.val) = t.val ∧ ¬(st.go = 1 ∧ v.val = st.x) then 0
      else vertexPot ctx n mRef v m := by
  let f' (v : Fin n) : ℕ :=
    if m' (ctx.auxBase + v.val) = t.val ∧ ¬(st'.go = 1 ∧ v.val = st'.x) then 0
    else vertexPot ctx n mRef v m'
  let f (v : Fin n) : ℕ :=
    if m (ctx.auxBase + v.val) = t.val ∧ ¬(st.go = 1 ∧ v.val = st.x) then 0
    else vertexPot ctx n mRef v m
  have hsum_x' : ∑ v : Fin n, f' v = f' x + ∑ v ∈ Finset.univ.erase x, f' v :=
    (Finset.add_sum_erase Finset.univ f' (Finset.mem_univ x)).symm
  have hsum_x : ∑ v : Fin n, f v = f x + ∑ v ∈ Finset.univ.erase x, f v :=
    (Finset.add_sum_erase Finset.univ f (Finset.mem_univ x)).symm
  have hfx' : f' x = 0 := ite_eq_left hx_after
  have hfx : f x = vertexPot ctx n mRef x m := by
    dsimp only [f]; rw [ite_eq_right]; intro h; exact h.2 ⟨hx_before.2.1, hx_before.2.2⟩
  have hrest : ∑ v ∈ Finset.univ.erase x, f' v ≤ ∑ v ∈ Finset.univ.erase x, f v := by
    refine Finset.sum_le_sum fun v hv => ?_
    have hne : v ≠ x := (Finset.mem_erase.mp hv).1
    have hvp : vertexPot ctx n mRef v m' = vertexPot ctx n mRef v m := by
      simp only [vertexPot_eq, (hoff v).1, (hoff v).2]
    dsimp only [f', f]
    split_ifs with h1 h2 h2
    · omega
    · omega
    · exact absurd (hother v hne h2.1) h1
    · rw [hvp]
  change ∑ v : Fin n, f' v + vertexPot ctx n mRef x m ≤ ∑ v : Fin n, f v
  rw [hsum_x', hsum_x, hfx', hfx, Nat.zero_add]
  omega


/-- Transport `extractRawProg_spec` across `ctx.n = n`. -/
theorem extractRawProg_spec_n {w n K : ℕ} {ctx : FTCtx} {s : Memory.State}
    (hcn : ctx.n = n) (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK ctx.fhBase).inv s) :
    let prog := extractRawProg ctx.n ctx.fhBase
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (framed hn hK ctx.fhBase).inv s' ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    Modifies (footprint n ctx.fhBase) s.mem s'.mem ∧
    (IndexedMinPQ.dom ((framed hn hK ctx.fhBase).abs s)).card = s.mem (ctx.fhBase + 9 * n + 4) ∧
    (res = none →
      (framed hn hK ctx.fhBase).abs s = IndexedMinPQ.empty n ∧
      (framed hn hK ctx.fhBase).abs s' = IndexedMinPQ.empty n) ∧
    (∀ y k, res = some (y, k) →
      ∃ hy : y < n, (framed hn hK ctx.fhBase).abs s ⟨y, hy⟩ = some k ∧
        (∀ z : Fin n, ∀ kz, (framed hn hK ctx.fhBase).abs s z = some kz →
          k < kz ∨ (k = kz ∧ y ≤ z.val)) ∧
        (framed hn hK ctx.fhBase).abs s' =
          Function.update ((framed hn hK ctx.fhBase).abs s) ⟨y, hy⟩ none) ∧
    memoryCost prog s + potential n ((layout n ctx.fhBase).abs s') ≤
      92 * (Nat.log 2 (s.mem (ctx.fhBase + 9 * n + 4)) + 1) +
        potential n ((layout n ctx.fhBase).abs s) := by
  have hn_c : Fits w ctx.n := by rw [hcn]; exact hn
  have hinv_c : (framed hn_c hK ctx.fhBase).inv s :=
    framed_inv_congr hcn.symm hn hn_c hK hinv
  have hraw := extractRawProg_spec hwf hn_c hK hinv_c
  dsimp only at hraw
  rcases hraw with ⟨hv, hinv', hfr', hwf', hmod, hcard, hnone, hsome, hcost⟩
  have hcast_abs : ∀ m z, (framed hn hK ctx.fhBase).abs m z =
      (framed hn_c hK ctx.fhBase).abs m ⟨z.val, hcn.symm ▸ z.isLt⟩ :=
    fun m z => framed_abs_congr hcn.symm hn hn_c hK m z
  have hdom_card : (IndexedMinPQ.dom ((framed hn hK ctx.fhBase).abs s)).card =
      (IndexedMinPQ.dom ((framed hn_c hK ctx.fhBase).abs s)).card :=
    Finset.card_bij (fun z _ => (⟨z.val, hcn.symm ▸ z.isLt⟩ : Fin ctx.n))
      (fun z hz => by
        simp only [IndexedMinPQ.dom, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [← hcast_abs s z]; exact hz)
      (fun _ _ _ _ h => Fin.ext (congrArg (Fin.val : Fin ctx.n → ℕ) h))
      (fun z hz => ⟨⟨z.val, hcn ▸ z.isLt⟩, by
        simp only [IndexedMinPQ.dom, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        rw [hcast_abs]; simpa only [Fin.eta] using hz, Fin.ext rfl⟩)
  have hpot_s : potential n ((layout n ctx.fhBase).abs s) =
      potential ctx.n ((layout ctx.n ctx.fhBase).abs s) := potential_congr hcn.symm s
  have hpot_s' : potential n ((layout n ctx.fhBase).abs
        ((Memory.spec 0).clientState s (extractRawProg ctx.n ctx.fhBase))) =
      potential ctx.n ((layout ctx.n ctx.fhBase).abs
        ((Memory.spec 0).clientState s (extractRawProg ctx.n ctx.fhBase))) :=
    potential_congr hcn.symm _
  refine ⟨hv, framed_inv_congr hcn hn_c hn hK hinv', hfr', hwf',
    fun a hfp => hmod a (by rw [hcn]; exact hfp),
    by rw [hdom_card, hcard, show ctx.fhBase + 9 * n + 4 = ctx.fhBase + 9 * ctx.n + 4 by
        rw [hcn]],
    fun hr => ?_, fun y k hr => ?_, ?_⟩
  · obtain ⟨hs0, hs1⟩ := hnone hr
    constructor <;> funext z <;> rw [hcast_abs _ z]
    · rw [hs0]; rfl
    · rw [hs1]; rfl
  · obtain ⟨hy_c, hk_s, hmin, hupd⟩ := hsome y k hr
    have hy : y < n := by rw [← hcn]; exact hy_c
    refine ⟨hy, by rw [hcast_abs s ⟨y, hy⟩]; exact hk_s, fun z kz hkz => ?_, ?_⟩
    · rw [hcast_abs s z] at hkz
      exact hmin ⟨z.val, hcn.symm ▸ z.isLt⟩ kz hkz
    · exact framed_abs_update_congr hcn hn_c hn hK s _ hy_c hy none hupd
  · rw [hpot_s, hpot_s', show ctx.fhBase + 9 * n + 4 = ctx.fhBase + 9 * ctx.n + 4 by rw [hcn]]
    exact hcost


/-- Cut-step extension of selected acyclic MSF edges when extracting min edge `eIdx`. -/
theorem ftExtract_cutStep {w n K : ℕ} {hn : Fits w n} {hK : Fits w K}
    {ctx : FTCtx} {es : List (IndexedEdge n)} {t yf : Fin n} {eIdx : Fin es.length}
    {selIdxs0 selTree : List (Fin es.length)} {s₀ s : Memory.State} {tl ky : ℕ}
    (ht_tr : t ∈ trSet ctx.auxBase n t s.mem)
    (hy_not_tr : yf ∉ trSet ctx.auxBase n t s.mem)
    (htr_new : ∀ v ∈ trSet ctx.auxBase n t s.mem, s₀.mem (ctx.auxBase + v.val) = n)
    (heIdx_wt : es[eIdx.val].weight = ky)
    (heIdx_end : (es[eIdx.val].u ∈ trSet ctx.auxBase n t s.mem ∧ es[eIdx.val].v = yf) ∨
      (es[eIdx.val].v ∈ trSet ctx.auxBase n t s.mem ∧ es[eIdx.val].u = yf))
    (hmin_ex : ∀ z : Fin n, ∀ kz, (framed hn hK ctx.fhBase).abs s z = some kz →
      ky < kz ∨ (ky = kz ∧ yf.val ≤ z.val))
    (hcut : FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s.mem) tl s)
    (hsel_nd : (selIdxs0 ++ selTree).Nodup)
    (hphase_verts : ∀ idx ∈ selIdxs0,
      es[idx.val].u ∈ visitedSet ctx.auxBase n t.val s₀.mem ∧
      es[idx.val].v ∈ visitedSet ctx.auxBase n t.val s₀.mem)
    (hsel_tree_verts : ∀ idx ∈ selTree,
      es[idx.val].u ∈ trSet ctx.auxBase n t s.mem ∧ es[idx.val].v ∈ trSet ctx.auxBase n t s.mem)
    (htr_conn : ∀ x' ∈ trSet ctx.auxBase n t s.mem, ∀ y' ∈ trSet ctx.auxBase n t s.mem,
      (edgePartition (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
        IndexedEdge.toWeighted)).rel x' y' = true)
    (hacyclic : IsAcyclic (((selIdxs0 ++ selTree).map fun i => es[i.val]).map
      IndexedEdge.toWeighted))
    (hext : ∃ F_ext : List (WeightedEdge n ℕ),
      IsMinSpanningForest (es.map IndexedEdge.toWeighted)
        ((((selIdxs0 ++ selTree).map fun i => es[i.val]).map
          IndexedEdge.toWeighted) ++ F_ext)) :
    (selIdxs0 ++ (selTree ++ [eIdx])).Nodup ∧
    IsAcyclic (((selIdxs0 ++ (selTree ++ [eIdx])).map fun i => es[i.val]).map
      IndexedEdge.toWeighted) ∧
    ∃ F_ext : List (WeightedEdge n ℕ),
      IsMinSpanningForest (es.map IndexedEdge.toWeighted)
        ((((selIdxs0 ++ (selTree ++ [eIdx])).map fun i => es[i.val]).map
          IndexedEdge.toWeighted) ++ F_ext) := by
  have hdisj_vt : Disjoint (visitedSet ctx.auxBase n t.val s₀.mem) (trSet ctx.auxBase n t s.mem) :=
    Finset.disjoint_left.mpr fun v hv1 hv2 => by
      rw [mem_visitedSet] at hv1
      have := htr_new v hv2
      omega
  let selW := ((selIdxs0 ++ selTree).map fun i => es[i.val]).map IndexedEdge.toWeighted
  have hsub_es : selW.Subperm (es.map IndexedEdge.toWeighted) :=
    List.subperm_map IndexedEdge.toWeighted (selIdxs_subperm_es hsel_nd)
  have hA_comp : ∀ x' ∈ trSet ctx.auxBase n t s.mem, ∀ z : Fin n,
      (edgePartition selW).rel x' z = true ↔ z ∈ trSet ctx.auxBase n t s.mem := by
    intro x' hx' z
    constructor
    · intro hrel
      have hcl : ∀ f ∈ selW, f.u ∈ trSet ctx.auxBase n t s.mem ↔
          f.v ∈ trSet ctx.auxBase n t s.mem := by
        intro f hf
        obtain ⟨e', he', rfl⟩ := List.mem_map.mp hf
        obtain ⟨idx, hidx, rfl⟩ := List.mem_map.mp he'
        rw [List.mem_append] at hidx
        rcases hidx with h0 | htr
        · have hu := Finset.disjoint_left.mp hdisj_vt (hphase_verts idx h0).1
          have hv := Finset.disjoint_left.mp hdisj_vt (hphase_verts idx h0).2
          exact iff_of_false hu hv
        · exact iff_of_true (hsel_tree_verts idx htr).1 (hsel_tree_verts idx htr).2
      exact (edgePartition_mem_iff_of_closed selW _ hcl hrel).mp hx'
    · intro hz; exact htr_conn x' hx' z hz
  have hcut_e : es[eIdx.val].toWeighted.u ∈ trSet ctx.auxBase n t s.mem ↔
      es[eIdx.val].toWeighted.v ∉ trSet ctx.auxBase n t s.mem := by
    rcases heIdx_end with ⟨hu, hev⟩ | ⟨hv, heu⟩
    · exact iff_of_true hu (by change es[eIdx.val].v ∉ _; rw [hev]; exact hy_not_tr)
    · exact iff_of_false (by change es[eIdx.val].u ∉ _; rw [heu]; exact hy_not_tr)
        (not_not.mpr hv)
  have hmin_e : ∀ f ∈ es.map IndexedEdge.toWeighted,
      (f.u ∈ trSet ctx.auxBase n t s.mem ↔ f.v ∉ trSet ctx.auxBase n t s.mem) →
      es[eIdx.val].toWeighted.weight ≤ f.weight := by
    intro f hf hcross
    obtain ⟨f₀, hf₀, rfl⟩ := List.mem_map.mp hf
    by_cases hfu : f₀.u ∈ trSet ctx.auxBase n t s.mem
    · have hfv : f₀.v ∉ trSet ctx.auxBase n t s.mem := hcross.mp hfu
      obtain ⟨kz, hkz, hle⟩ := (hcut.hscanned_cov f₀.u hfu f₀ hf₀).1 ⟨rfl, hfv⟩
      have hmin_le := hmin_ex f₀.v kz hkz
      change es[eIdx.val].weight ≤ f₀.weight
      rw [heIdx_wt]
      rcases hmin_le with hlt | ⟨heq, _⟩ <;> omega
    · have hfv : f₀.v ∈ trSet ctx.auxBase n t s.mem := by
        by_contra hc; exact hfu (hcross.mpr hc)
      obtain ⟨kz, hkz, hle⟩ := (hcut.hscanned_cov f₀.v hfv f₀ hf₀).2 ⟨rfl, hfu⟩
      have hmin_le := hmin_ex f₀.u kz hkz
      change es[eIdx.val].weight ≤ f₀.weight
      rw [heIdx_wt]
      rcases hmin_le with hlt | ⟨heq, _⟩ <;> omega
  have hcs := exists_extend_isMinSpanningForest_cutStep (es.map IndexedEdge.toWeighted) selW
    hsub_es hacyclic hext (trSet ctx.auxBase n t s.mem) ⟨t, ht_tr⟩ hA_comp
    es[eIdx.val].toWeighted (List.mem_map.mpr ⟨_, List.getElem_mem eIdx.isLt, rfl⟩)
    hcut_e hmin_e
  have heIdx_fresh : eIdx ∉ selIdxs0 ++ selTree := by
    intro hmem
    rw [List.mem_append] at hmem
    rcases hmem with h0 | htr
    · have h0u := (hphase_verts eIdx h0).1; have h0v := (hphase_verts eIdx h0).2
      rcases heIdx_end with ⟨hu, hev⟩ | ⟨hv, heu⟩
      · exact Finset.disjoint_left.mp hdisj_vt h0u hu
      · exact Finset.disjoint_left.mp hdisj_vt h0v hv
    · have htu := (hsel_tree_verts eIdx htr).1; have htv := (hsel_tree_verts eIdx htr).2
      rcases heIdx_end with ⟨_, hev⟩ | ⟨_, heu⟩
      · exact hy_not_tr (hev ▸ htv)
      · exact hy_not_tr (heu ▸ htu)
  have hnd' : (selIdxs0 ++ (selTree ++ [eIdx])).Nodup := by
    rw [← List.append_assoc, List.nodup_append]
    exact ⟨hsel_nd, List.nodup_singleton _, fun a ha b hb => by
      rw [List.mem_singleton] at hb; subst hb; intro h; subst h; exact heIdx_fresh ha⟩
  refine ⟨hnd', ?_, ?_⟩
  · simpa only [selW, ← List.append_assoc, List.map_append, List.map_singleton] using hcs.2.1
  · simpa only [selW, ← List.append_assoc, List.map_append, List.map_singleton] using hcs.2.2

/-- Preserve `selBuf` invariants when appending a newly selected edge id. -/
theorem ftExtract_sel_buf_eq {n : ℕ} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {selIdxs0 selTree : List (Fin es.length)} {eIdx : Fin es.length}
    {selLen0 selLen : ℕ} {s s' : Memory.State}
    (hsel_len : selLen = selLen0 + (selIdxs0 ++ selTree).length)
    (hsel_buf : ∀ j (hj : j < selTree.length),
      s.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) = es[selTree[j].val].id)
    (hnew : s'.mem (ctx.selBufBase + selLen) = es[eIdx.val].id)
    (hother : ∀ j < selTree.length,
      s'.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) =
        s.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j)) :
    ∀ j (hj : j < (selTree ++ [eIdx]).length),
      s'.mem (ctx.selBufBase + selLen0 + selIdxs0.length + j) =
        es[(selTree ++ [eIdx])[j].val].id := by
  intro j hj
  by_cases hjl : j < selTree.length
  · rw [hother j hjl, hsel_buf j hjl]
    simp only [List.getElem_append_left hjl]
  · have hj_eq : j = selTree.length := by simp at hj; omega
    subst hj_eq
    have heq_addr : ctx.selBufBase + selLen0 + selIdxs0.length + selTree.length =
        ctx.selBufBase + selLen := by rw [hsel_len, List.length_append]; omega
    rw [heq_addr, hnew]
    simp


/-- Preserve `FTCutInv` when extracting `yf` and inserting it into `trSet`. -/
theorem ftExtract_grow_cutInv {w n K tl : ℕ} {hn : Fits w n} {hK : Fits w K}
    {ctx : FTCtx} {es : List (IndexedEdge n)} {t yf : Fin n}
    {s s₃ : Memory.State}
    (hinv₃ : (framed hn hK ctx.fhBase).inv s₃)
    (habs₃ : (framed hn hK ctx.fhBase).abs s₃ =
      Function.update ((framed hn hK ctx.fhBase).abs s) yf none)
    (hcut : FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s.mem) tl s)
    (htr_s3_v : ∀ v : Fin n, v ≠ yf → s₃.mem (ctx.auxBase + v.val) = s.mem (ctx.auxBase + v.val))
    (htr_set_s3 : trSet ctx.auxBase n t s₃.mem = insert yf (trSet ctx.auxBase n t s.mem))
    (htch_s3 : ∀ i < tl, s₃.mem (ctx.auxBase + 4 * n + i) = s.mem (ctx.auxBase + 4 * n + i))
    (hbest_s3 : ∀ v : Fin n, v ≠ yf →
      s₃.mem (ctx.auxBase + n + v.val) = s.mem (ctx.auxBase + n + v.val)) :
    FTCutInv hn hK ctx es t (trSet ctx.auxBase n t s.mem) tl s₃ := by
  have hnd_t : (touchedList ctx.auxBase n tl s₃.mem).Nodup := by
    rw [touchedList_congr htch_s3]; exact hcut.htouched_nd
  refine ⟨hinv₃, hcut.htl_le,
    fun i hi => by rw [htch_s3 i hi]; exact hcut.htouched_lt i hi, hnd_t,
    fun i hi => by rw [htch_s3 i hi]; exact hcut.htouched_ne_t i hi, fun i hi hv => ?_,
    fun v hv => ?_, fun v kv hkv => ?_, fun u' hu' e he => ?_⟩
  · have hv0 : s.mem (ctx.auxBase + 4 * n + i) < n := by rw [← htch_s3 i hi]; exact hv
    have hmem_v : (⟨_, hv⟩ : Fin n) = ⟨_, hv0⟩ := Fin.ext (htch_s3 i hi)
    by_cases hvy : (⟨_, hv⟩ : Fin n) = yf
    · right; rw [hvy, htr_set_s3]; exact Finset.mem_insert_self _ _
    · have hne' : (⟨_, hv0⟩ : Fin n) ≠ yf := fun h => hvy (hmem_v.trans h)
      rw [hmem_v, habs₃, Function.update_of_ne hne', htr_set_s3]
      rcases hcut.htouched_in i hi hv0 with h1 | h2
      · exact Or.inl h1
      · exact Or.inr (Finset.mem_insert_of_mem h2)
  · rw [habs₃] at hv
    by_cases hvy : v = yf
    · rw [hvy, Function.update_self] at hv; exact absurd hv (by simp)
    · rw [Function.update_of_ne hvy] at hv
      obtain ⟨i, hi, heq⟩ := hcut.htouched_cov v hv
      exact ⟨i, hi, by rw [htch_s3 i hi, heq]⟩
  · rw [habs₃] at hkv
    by_cases hvy : v = yf
    · rw [hvy, Function.update_self] at hkv; exact absurd hkv (by simp)
    · rw [Function.update_of_ne hvy] at hkv
      obtain ⟨hne, e0, he0_b, he0_w, he0_e⟩ := hcut.hheap_cut v kv hkv
      refine ⟨by rw [htr_s3_v v hvy]; exact hne, ⟨e0, ?_, he0_w, ?_⟩⟩
      · rw [hbest_s3 v hvy]; exact he0_b
      · rw [htr_set_s3]
        rcases he0_e with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> [left; right] <;>
          exact ⟨Finset.mem_insert_of_mem h1, h2⟩
  · obtain ⟨hL, hR⟩ := hcut.hscanned_cov u' hu' e he
    constructor
    · intro ⟨h1, h2⟩
      rw [htr_set_s3, Finset.mem_insert, not_or] at h2
      obtain ⟨kz, hkz, hle⟩ := hL ⟨h1, h2.2⟩
      exact ⟨kz, by rw [habs₃, Function.update_of_ne h2.1]; exact hkz, hle⟩
    · intro ⟨h1, h2⟩
      rw [htr_set_s3, Finset.mem_insert, not_or] at h2
      obtain ⟨kz, hkz, hle⟩ := hR ⟨h1, h2.2⟩
      exact ⟨kz, by rw [habs₃, Function.update_of_ne h2.1]; exact hkz, hle⟩

private theorem edgePartition_append_bridge {n : ℕ} (selW : List (WeightedEdge n ℕ))
    (A : Finset (Fin n)) (e : WeightedEdge n ℕ) (y : Fin n)
    (hA_conn : ∀ x ∈ A, ∀ z ∈ A, (edgePartition selW).rel x z = true)
    (hend : (e.u ∈ A ∧ e.v = y) ∨ (e.v ∈ A ∧ e.u = y)) :
    (∀ a b, (edgePartition selW).rel a b = true →
      (edgePartition (selW ++ [e])).rel a b = true) ∧
    (∀ z ∈ A, (edgePartition (selW ++ [e])).rel z y = true) := by
  refine ⟨fun a b hab => (edgePartition_append_single_rel selW e a b).mpr (Or.inl hab),
    fun z hz => (edgePartition_append_single_rel selW e z y).mpr ?_⟩
  rcases hend with ⟨hu, hev⟩ | ⟨hv, heu⟩
  · exact Or.inr (Or.inl ⟨hA_conn z hz e.u hu, by rw [hev]; exact (edgePartition selW).refl y⟩)
  · exact Or.inr (Or.inr ⟨hA_conn z hz e.v hv, by rw [heu]; exact (edgePartition selW).refl y⟩)

/-- Connectivity preservation in `trSet ∪ {yf}` after appending bridging edge `eIdx`. -/
theorem ftExtract_grow_conn {n : ℕ} (F : List (WeightedEdge n ℕ))
    (A : Finset (Fin n)) (e : WeightedEdge n ℕ) (yf : Fin n)
    (hA_conn : ∀ x' ∈ A, ∀ y' ∈ A, (edgePartition F).rel x' y' = true)
    (hend : (e.u ∈ A ∧ e.v = yf) ∨ (e.v ∈ A ∧ e.u = yf)) :
    ∀ x' ∈ insert yf A, ∀ y' ∈ insert yf A,
      (edgePartition (F ++ [e])).rel x' y' = true := by
  obtain ⟨hsub_rel, he_conn⟩ := edgePartition_append_bridge F A e yf hA_conn hend
  intro x' hx' y' hy'
  rw [Finset.mem_insert] at hx' hy'
  rcases hx' with rfl | hx_old <;> rcases hy' with rfl | hy_old
  · exact (edgePartition (F ++ [e])).refl _
  · exact (edgePartition (F ++ [e])).symm (he_conn y' hy_old)
  · exact he_conn x' hx_old
  · exact hsub_rel x' y' (hA_conn x' hx_old y' hy_old)


/-- Left-projection of `edgePartition (F ++ G)` across disjoint vertex sets `V` and `A`. -/
theorem eqvGen_append_disjoint_left {n : ℕ} (F G : List (WeightedEdge n ℕ))
    (V A : Finset (Fin n)) (hdisj : Disjoint V A)
    (hF : ∀ e ∈ F, e.u ∈ V ∧ e.v ∈ V) (hG : ∀ e ∈ G, e.u ∈ A ∧ e.v ∈ A)
    {u : Fin n} (hu : u ∈ V) {v : Fin n}
    (hrel : (edgePartition (F ++ G)).rel u v = true) :
    v ∈ V ∧ (edgePartition F).rel u v = true := by
  rw [rel_edgePartition_iff_eqvGen] at hrel
  have hgen : ∀ a b, Relation.EqvGen (fun x y => ∃ e ∈ F ++ G, x = e.u ∧ y = e.v) a b →
      (a ∈ V → b ∈ V ∧ (edgePartition F).rel a b = true) ∧
      (b ∈ V → a ∈ V ∧ (edgePartition F).rel b a = true) := by
    intro a b hab
    induction hab with
    | refl x => exact ⟨fun hx => ⟨hx, (edgePartition F).refl x⟩,
        fun hx => ⟨hx, (edgePartition F).refl x⟩⟩
    | symm _ _ _ ih => exact ⟨ih.2, ih.1⟩
    | trans _ _ _ _ _ ih1 ih2 =>
      exact ⟨fun hx => let ⟨hy, h1⟩ := ih1.1 hx; let ⟨hz, h2⟩ := ih2.1 hy
        ⟨hz, (edgePartition F).trans h1 h2⟩,
        fun hz => let ⟨hy, h2⟩ := ih2.2 hz; let ⟨hx, h1⟩ := ih1.2 hy
        ⟨hx, (edgePartition F).trans h2 h1⟩⟩
    | rel _ _ hxy =>
      obtain ⟨e, he, rfl, rfl⟩ := hxy
      rw [List.mem_append] at he
      rcases he with heF | heG
      · have ⟨huV, hvV⟩ := hF e heF
        have hrelF : (edgePartition F).rel e.u e.v = true :=
          (rel_edgePartition_iff_eqvGen F e.u e.v).mpr (.rel e.u e.v ⟨e, heF, rfl, rfl⟩)
        exact ⟨fun _ => ⟨hvV, hrelF⟩, fun _ => ⟨huV, (edgePartition F).symm hrelF⟩⟩
      · have ⟨huA, _⟩ := hG e heG
        exact ⟨fun hx => absurd hx (Finset.disjoint_right.mp hdisj huA),
          fun hy => absurd hy (Finset.disjoint_right.mp hdisj (hG e heG).2)⟩
  exact (hgen u v hrel).1 hu


end Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase
