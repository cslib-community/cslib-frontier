/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.Phase
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Dedup
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Boruvka
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Computability.WordRAM.Realization.RecordOps
import CslibFrontier.Foundations.Data.List.Subperm
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.UpdateSimp
import CslibFrontier.Tactic.ValidProg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fredman–Tarjan Bounded-Heap MSF Driver (`denseCaseProg`)

Assembles the full multi-phase Fredman–Tarjan bounded-heap minimum spanning forest algorithm over
`GraphSlice` toward Theorem 5.8 of [PettieRamachandran2002] (Section 2.3, #8624) and
[FredmanTarjan1987] (Section 3, pp. 605–607):

1. Preprocessing (densePreprocessProg): retags stride-4 input edges with local ordinals
   `0 .. m - 1`, removes self-loops and parallel duplicate edges (`dedupSimpleEdgesProg`), and
   compacts isolated vertices (`compactVerticesProg`).
2. Contraction loop (densePhaseLoopProg): executes bounded-heap Fredman–Tarjan contraction phases
   (`buildUndirCSR`, `ftPhaseProg`, `boruvkaShrinkProg`) tracked by ftPhaseRank (mRef, nCur),
   shrinking active vertices to `0` in at most `Nat.iterClogBeta (2 * m / n) n` phases.
3. Emission (emitIndexedEdgesFromIdxs): materializes the original `IndexedEdge n` records for the
   accumulated edge indices into a fresh `GraphSlice`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.denseCaseProg`: Fredman–Tarjan
  bounded-heap MSF algorithm mapping `GraphSlice` to `GraphSlice`.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.realizes_denseCaseProg`: uniform
  `Realizes .exact` realization with `work = 0`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.denseCaseProg_spec`: framed
  `O(m * iterClogBeta (2 * m / n) n + n)` correctness and memory-cost specification.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.denseCaseProg_spec_of_dense`: framed
  linear-time `O(m + n)` specification when `n ≤ n₀` and
  `n * max 1 (Nat.iterLog 3 n₀) ≤ 2 * m`.

## References

* [FredmanTarjan1987]: Michael L. Fredman and Robert Endre Tarjan, "Fibonacci Heaps and Their Uses
  in Improved Network Optimization Algorithms", *JACM* 34(3), 1987, Section 3 ("Minimum Spanning
  Trees"), pp. 605–607.
* [PettieRamachandran2002]: Seth Pettie and Vijaya Ramachandran, "An Optimal Minimum Spanning
  Tree Algorithm", *JACM* 49(1), 2002, Section 2.3 and Section 3.4.
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.MinimumSpanningForest
open Cslib.Query.MinimumSpanningForest

/-! ## Private Combinatorial Helpers -/

private theorem empty_FinZero_isMinSpanningForest (es : List (WeightedEdge 0 ℕ)) :
    es = [] ∧ IsMinSpanningForest es ([] : List (WeightedEdge 0 ℕ)) := by
  have hes_nil : es = [] := by
    cases es with
    | nil => rfl
    | cons e _ => exact Fin.elim0 e.u
  subst hes_nil
  refine ⟨rfl, ⟨List.nil_subperm, ?_, rfl⟩, fun G' hG' => ?_⟩
  · simp [isAcyclic_iff, edgePartition]
  · simp [totalWeight]

private theorem empty_isMSF_of_numVertices_zero {n : ℕ} (hn : n = 0) (es : List (IndexedEdge n)) :
    es = [] ∧ IsMinSpanningForest (es.map IndexedEdge.toWeighted)
      (([] : List (IndexedEdge n)).map IndexedEdge.toWeighted) := by
  subst hn
  have hes_nil : es = [] := by
    cases es with
    | nil => rfl
    | cons e _ => exact Fin.elim0 e.u
  subst hes_nil
  exact ⟨rfl, (empty_FinZero_isMinSpanningForest []).2⟩

private theorem iterClogBeta_div_le_self {mRef n : ℕ} (hn1 : 1 ≤ n) :
    Nat.iterClogBeta ((2 * mRef) / n) n ≤ n := by
  rcases le_or_gt n 1 with hle1 | hgt1
  · have hn_eq : n = 1 := by omega
    subst hn_eq
    have h1 : Nat.iterClogBeta ((2 * mRef) / 1) 1 = 1 :=
      Nat.iterClogBeta_eq_one_iff.mpr (Nat.one_le_pow _ _ (by decide))
    omega
  · have hpow : n ≤ 2 ^ (n - 1) := by
      have := Nat.lt_two_pow_self (n := n - 1)
      omega
    have hclog : Nat.clog 2 n ≤ n - 1 := (Nat.clog_le_iff_le_pow (by decide)).mpr hpow
    have h1 := Nat.iterClogBeta_le_add_iterClog (k := 1) le_rfl ((2 * mRef) / n) n
    change Nat.iterClogBeta ((2 * mRef) / n) n ≤ 1 + Nat.clog 2 n at h1
    omega

/-! ## Private Word-Encoded Helper Records -/

private structure RetagEnv where
  srcBase : ℕ
  dstBase : ℕ

private word_enc_structure encRetagEnv : RetagEnv where
  srcBase : wordWords,
  dstBase : wordWords

private instance : WordEncoding RetagEnv := ⟨2, encRetagEnv⟩

private structure RetagArgs where
  edgeBase : ℕ
  count : ℕ

private word_enc_structure encRetagArgs : RetagArgs where
  edgeBase : wordWords,
  count : wordWords

private instance : WordEncoding RetagArgs := ⟨2, encRetagArgs⟩

private structure DensePhaseEnv where
  mRef : ℕ
  selBufBase : ℕ
  selEnd : ℕ

private word_enc_structure encDensePhaseEnv : DensePhaseEnv where
  mRef : wordWords,
  selBufBase : wordWords,
  selEnd : wordWords

private instance : WordEncoding DensePhaseEnv := ⟨3, encDensePhaseEnv⟩

private structure DenseLoopState where
  numVertices : ℕ
  numEdges : ℕ
  edgeBase : ℕ
  selLen : ℕ

private word_enc_structure encDenseLoopState : DenseLoopState where
  numVertices : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  selLen : wordWords

private instance : WordEncoding DenseLoopState := ⟨4, encDenseLoopState⟩

private structure DenseLoopInit where
  numVertices : ℕ
  numEdges : ℕ
  edgeBase : ℕ
  mRef : ℕ

private word_enc_structure encDenseLoopInit : DenseLoopInit where
  numVertices : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  mRef : wordWords

private instance : WordEncoding DenseLoopInit := ⟨4, encDenseLoopInit⟩

private structure DenseLoopOut where
  selBufBase : ℕ
  selLen : ℕ

private word_enc_structure encDenseLoopOut : DenseLoopOut where
  selBufBase : wordWords,
  selLen : wordWords

private instance : WordEncoding DenseLoopOut := ⟨2, encDenseLoopOut⟩

/-! ## Private Preprocessing: Retag Local Edge IDs, Deduplicate, Compact -/

private def retagEdgeStep (x : RetagEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let idx := Prod.snd x
  let u ← Memory.read (env.srcBase + 4 * idx)
  let v ← Memory.read (env.srcBase + 4 * idx + 1)
  let wt ← Memory.read (env.srcBase + 4 * idx + 2)
  Memory.write (env.dstBase + 4 * idx) u
  Memory.write (env.dstBase + 4 * idx + 1) v
  Memory.write (env.dstBase + 4 * idx + 2) wt
  Memory.write (env.dstBase + 4 * idx + 3) idx
  pure (idx + 1)

private def retagEdgeStepSafe (w : ℕ) (x : RetagEnv × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let idx := Prod.snd x
  Fits w 16 ∧ Fits w (idx + 1) ∧ Fits w (env.srcBase + 4 * idx + 3) ∧
    Fits w (env.dstBase + 4 * idx + 4) ∧
    env.srcBase + 4 * idx + 3 < s.frontier ∧ env.dstBase + 4 * idx + 4 ≤ s.frontier

private theorem realizes_retagEdgeStep_history : Realizes .exact
    retagEdgeStep (appendWords encRetagEnv wordWords) wordWords
    (fun w d s => retagEdgeStepSafe w d s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (retagEdgeStep d)))
    (fun _ _ => 0) := by
  unfold retagEdgeStep
  realize
  all_goals
    obtain ⟨⟨h16, hfit, hsrc, hdst, _, _⟩, hv⟩ := h
    have hfront := hmem.frontier_fits
    dsimp only [StateTransitionSpec.clientHistory] at hv
    simp_all only [StateTransitionSpec.runClient_lift_bind',
      StateTransitionSpec.validHistory_cons, StateTransitionSpec.stepFn, Memory.read,
      Memory.write, Memory.step_read, Memory.step_write, Memory.valid]
  all_goals fits

private theorem realizes_retagEdgeStep : Realizes .exact
    retagEdgeStep (appendWords encRetagEnv wordWords) wordWords
    retagEdgeStepSafe (fun _ _ => 0) :=
  realizes_retagEdgeStep_history.consequence_valid fun _ _ _ _ _ hv h => ⟨h, hv⟩

private def retagLocalEdgesProg (a : RetagArgs) : Memory.Prog ℕ := do
  let out ← Memory.allocBlockDirty (4 * a.count)
  let _ ← iterate retagEdgeStep ⟨a.edgeBase, out.base⟩ a.count 0
  pure out.base

private theorem memoryCost_retagEdgeStep (x : RetagEnv × ℕ) (t : Memory.State) :
    memoryCost (retagEdgeStep x) t = 7 := by
  dsimp only [retagEdgeStep]
  rw [memoryCost_bind', memoryCost_read, memoryCost_bind', memoryCost_read,
    memoryCost_bind', memoryCost_read, memoryCost_bind', memoryCost_write,
    memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write,
    memoryCost_bind', memoryCost_write, memoryCost_pure]

private theorem memoryCost_retagLocalEdgesProg (a : RetagArgs) (s : Memory.State) :
    memoryCost (retagLocalEdgesProg a) s = 7 * a.count + 1 := by
  have hiter : ∀ (env : RetagEnv) (k idx : ℕ) (t : Memory.State),
      memoryCost (iterate retagEdgeStep env k idx) t = 7 * k := by
    intro env k
    induction k with
    | zero => intro _ _; simp [iterate, memoryCost_pure]
    | succ k ih =>
      intro idx t
      have hit : iterate retagEdgeStep env (k + 1) idx =
          (retagEdgeStep (env, idx) >>= iterate retagEdgeStep env k) := rfl
      rw [hit, memoryCost_bind', memoryCost_retagEdgeStep, ih]
      omega
  dsimp only [retagLocalEdgesProg, Memory.allocBlockDirty]
  rw [bind_assoc, memoryCost_bind', memoryCost_allocDirty, clientResult_allocDirty,
    clientState_allocDirty, memoryCost_bind', memoryCost_pure, StateTransitionSpec.clientState_pure,
    StateTransitionSpec.clientResult_pure, memoryCost_bind', hiter, memoryCost_pure]
  omega

private theorem retagLocalEdgesProg_word_spec {w edgeBase count : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : edgeBase + 4 * count ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * count)) :
    iterationSafe retagEdgeStep retagEdgeStepSafe w
      ⟨edgeBase, s.frontier⟩ count 0 ⟨s.mem, s.frontier + 4 * count⟩ ∧
    Memory.FramedTriple w s (retagLocalEdgesProg ⟨edgeBase, count⟩) (7 * count + 1) ∅
      fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + 4 * count ∧
        Memory.WellFormed w s' ∧
        ∀ i < count,
          s'.mem (outBase + 4 * i) = s.mem (edgeBase + 4 * i) ∧
          s'.mem (outBase + 4 * i + 1) = s.mem (edgeBase + 4 * i + 1) ∧
          s'.mem (outBase + 4 * i + 2) = s.mem (edgeBase + 4 * i + 2) ∧
          s'.mem (outBase + 4 * i + 3) = i := by
  let S : Set ℕ := Set.Ico s.frontier (s.frontier + 4 * count)
  let inv (k a : ℕ) (t : Memory.State) : Prop :=
    a = k ∧ t.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w t ∧
    (∀ x, x ∉ S → t.mem x = s.mem x) ∧
    ∀ i < k,
      t.mem (s.frontier + 4 * i) = s.mem (edgeBase + 4 * i) ∧
      t.mem (s.frontier + 4 * i + 1) = s.mem (edgeBase + 4 * i + 1) ∧
      t.mem (s.frontier + 4 * i + 2) = s.mem (edgeBase + 4 * i + 2) ∧
      t.mem (s.frontier + 4 * i + 3) = i
  have hfit_m1 : Fits w (count + 1) := by
    rcases count with _ | m
    · exact h16.of_le (by omega)
    · exact hfit.of_le (by omega)
  have hstep : ∀ k < count, ∀ a t, inv k a t →
      retagEdgeStepSafe w (⟨edgeBase, s.frontier⟩, a) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (retagEdgeStep (⟨edgeBase, s.frontier⟩, a))) ∧
      let a' := (Memory.spec 0).clientResult t (retagEdgeStep (⟨edgeBase, s.frontier⟩, a))
      let t' := (Memory.spec 0).clientState t (retagEdgeStep (⟨edgeBase, s.frontier⟩, a))
      memoryCost (retagEdgeStep (⟨edgeBase, s.frontier⟩, a)) t + 0 ≤ 0 + 7 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) a' t' := by
    intro k hk a t ⟨ha, htfr, hwt, hframe, hpref⟩
    subst a
    have hin_eq : ∀ q < 3, t.mem (edgeBase + 4 * k + q) = s.mem (edgeBase + 4 * k + q) :=
      fun q hq => hframe _ (by simp only [S, Set.mem_Ico, not_and, not_lt]; omega)
    have hfit_k1 : Fits w (k + 1) := hfit_m1.of_le (by omega)
    have hfit_k : Fits w k := hfit_k1.of_le (by omega)
    have hmem_t : ∀ a, Fits w (t.mem a) := hwt.mem_fits
    have hvh : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (retagEdgeStep (⟨edgeBase, s.frontier⟩, k))) := by
      dsimp only [retagEdgeStep]
      valid_prog
      all_goals
        try dsimp only at *
        first
        | exact hmem_t _
        | omega
    have hcost : memoryCost (retagEdgeStep (⟨edgeBase, s.frontier⟩, k)) t ≤ 7 := by
      rw [memoryCost_retagEdgeStep]
    have hres : (Memory.spec 0).clientResult t (retagEdgeStep (⟨edgeBase, s.frontier⟩, k)) =
        k + 1 := by
      dsimp only [retagEdgeStep]
      simp only [clientResult_bind_read, clientResult_bind_write,
        StateTransitionSpec.clientResult_pure]
    have hst : (Memory.spec 0).clientState t (retagEdgeStep (⟨edgeBase, s.frontier⟩, k)) =
        ⟨Function.update (Function.update (Function.update (Function.update t.mem
          (s.frontier + 4 * k) (t.mem (edgeBase + 4 * k)))
          (s.frontier + 4 * k + 1) (t.mem (edgeBase + 4 * k + 1)))
          (s.frontier + 4 * k + 2) (t.mem (edgeBase + 4 * k + 2)))
          (s.frontier + 4 * k + 3) k, t.frontier⟩ := by
      dsimp only [retagEdgeStep]
      repeat rw [clientState_bind_read]
      rfl
    have hupd_out : ∀ x, x ∉ S →
        ((Memory.spec 0).clientState t (retagEdgeStep (⟨edgeBase, s.frontier⟩, k))).mem x =
          t.mem x := by
      intro x hx
      rw [hst]
      simp only [S, Set.mem_Ico, not_and_or, not_le, not_lt] at hx
      update_simp
    have hsafe_k : retagEdgeStepSafe w (⟨edgeBase, s.frontier⟩, k) t := by
      dsimp only [retagEdgeStepSafe]
      exact ⟨h16, hfit_k1, hfit.of_le (by omega), hfit.of_le (by omega), by omega, by omega⟩
    refine ⟨hsafe_k, hvh, by omega, ⟨by rw [hst], fun x _ hx => hupd_out x hx⟩,
      hres, by rw [hst]; exact htfr, wellFormed_clientState hwt hvh,
      fun x hx => (hupd_out x hx).trans (hframe x hx), fun i hi => ?_⟩
    rw [hst]; dsimp only
    by_cases hik : i = k
    · subst i
      have h0 := hin_eq 0 (by decide)
      have h1 := hin_eq 1 (by decide)
      have h2 := hin_eq 2 (by decide)
      simp only [Nat.add_zero] at h0
      refine ⟨?_, ?_, ?_, ?_⟩ <;> update_simp <;> simp [h0, h1, h2]
    · have hik' : i < k := by omega
      have hp := hpref i hik'
      refine ⟨?_, ?_, ?_, ?_⟩ <;> update_simp <;> simp [hp]
  obtain ⟨hsafe, hv_it, hm_it, hmod_it, _, hfr_it, hwf_it, _, hvals⟩ :=
    iterate_potential_spec retagEdgeStep retagEdgeStepSafe w ⟨edgeBase, s.frontier⟩
      7 count inv (fun _ _ _ => 0) S hstep 0 ⟨s.mem, s.frontier + 4 * count⟩
      ⟨rfl, rfl, ⟨hfit, hwf.mem_fits⟩, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  refine ⟨hsafe, ?_⟩
  have hprog : retagLocalEdgesProg ⟨edgeBase, count⟩ =
      (Memory.allocBlockDirty (4 * count) >>= fun out =>
        iterate retagEdgeStep ⟨edgeBase, out.base⟩ count 0 >>= fun _ => pure out.base) := rfl
  rw [hprog]
  have ft_iter : Memory.FramedTriple w ⟨s.mem, s.frontier + 4 * count⟩
      (iterate retagEdgeStep ⟨edgeBase, s.frontier⟩ count 0) (7 * count) S
      (fun _ s' => Memory.FramedTriple w s' (pure s.frontier) 0 S fun outBase s'' =>
        outBase = s.frontier ∧ s''.frontier = s.frontier + 4 * count ∧ Memory.WellFormed w s'' ∧
        ∀ i < count,
          s''.mem (outBase + 4 * i) = s.mem (edgeBase + 4 * i) ∧
          s''.mem (outBase + 4 * i + 1) = s.mem (edgeBase + 4 * i + 1) ∧
          s''.mem (outBase + 4 * i + 2) = s.mem (edgeBase + 4 * i + 2) ∧
          s''.mem (outBase + 4 * i + 3) = i) :=
    framedTriple_iff_realization.mpr ⟨hv_it, by simpa using hm_it, hmod_it,
      Memory.FramedTriple.pure ⟨rfl, hfr_it, hwf_it, hvals⟩⟩
  exact ((Memory.FramedTriple.allocBlockDirty_bind hfit
    (Memory.FramedTriple.bind_same ft_iter)).frame_empty_of_ge_frontier (S := S)
    fun _ ha => (Set.mem_Ico.mp ha).1).mono
    (by omega : 7 * count + 0 + 1 ≤ 7 * count + 1) fun _ _ h => h

private theorem realizes_retagLocalEdgesProg : Realizes .exact
    retagLocalEdgesProg WordEncoding.encode WordEncoding.encode
    (fun w a s => Fits w 16 ∧ a.edgeBase + 4 * a.count ≤ s.frontier ∧
      Fits w (s.frontier + 4 * a.count))
    (fun _ _ => 0) := by
  have hraw : Realizes .exact retagLocalEdgesProg WordEncoding.encode WordEncoding.encode
      (fun w a s => Fits w 16 ∧ Fits w (s.frontier + 4 * a.count) ∧
        iterationSafe (fun x : (RetagArgs × Block) × ℕ =>
          let args := Prod.fst (Prod.fst x)
          let blk := Prod.snd (Prod.fst x)
          retagEdgeStep (⟨args.edgeBase, blk.base⟩, Prod.snd x))
          (fun w x s =>
            let args := Prod.fst (Prod.fst x)
            let blk := Prod.snd (Prod.fst x)
            retagEdgeStepSafe w (⟨args.edgeBase, blk.base⟩, Prod.snd x) s)
          w (a, ⟨s.frontier, 4 * a.count⟩) a.count 0 ⟨s.mem, s.frontier + 4 * a.count⟩)
      (fun _ _ => 0) := by
    unfold retagLocalEdgesProg
    realize [realizes_allocBlockDirty, realizes_retagEdgeStep]
    · exact h.2.1.of_le (by omega)
    · exact h.1.of_le (by decide)
    · exact iterationSafe_imp h.2.2 (fun _ => rfl) (fun _ _ hs => hs)
  refine hraw.consequence (fun w a s _ hmem ⟨h16, hin_lt, hfit⟩ => ?_) (fun _ _ => le_rfl)
  exact ⟨h16, hfit, iterationSafe_imp (retagLocalEdgesProg_word_spec h16 hmem hin_lt hfit).1
    (fun _ => rfl) (fun _ _ hs => hs)⟩

private theorem retagLocalEdgesProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 4 * es.length)) :
    Memory.FramedTriple w s (retagLocalEdgesProg ⟨edgeBase, es.length⟩) (7 * es.length + 1) ∅
      fun outBase s' =>
        outBase = s.frontier ∧
        s'.frontier = s.frontier + 4 * es.length ∧
        Memory.WellFormed w s' ∧
        HoldsIndexedEdges outBase (es.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩) s'.mem := by
  refine (retagLocalEdgesProg_word_spec h16 hwf hin_lt hfit).2.mono le_rfl
    fun outBase s' ⟨hout, hfr, hwf', hvals⟩ => ⟨hout, hfr, hwf', fun i hi => ?_⟩
  have hi_len : i < es.length := by simpa using hi
  obtain ⟨hu, hv, hw, _⟩ := hin i hi_len
  obtain ⟨h0, h1, h2, h3⟩ := hvals i hi_len
  simp only [List.getElem_mapIdx]
  exact ⟨h0.trans hu, h1.trans hv, h2.trans hw, h3⟩

private def densePreprocessProg (g : GraphSlice) : Memory.Prog GraphSlice := do
  let locBase ← retagLocalEdgesProg ⟨g.edgeBase, g.numEdges⟩
  let ded ← dedupSimpleEdgesProg ⟨g.numVertices, g.numEdges, locBase⟩
  let comp ← compactVerticesProg ⟨g.numVertices, ded.numEdges, ded.edgeBase⟩
  pure ⟨comp.numVertices, ded.numEdges, comp.edgeBase⟩

private theorem densePreprocessProg_cost_lower (g : GraphSlice) (s : Memory.State) :
    7 * g.numEdges + 1 ≤ memoryCost (densePreprocessProg g) s := by
  dsimp only [densePreprocessProg]
  rw [memoryCost_bind', memoryCost_retagLocalEdgesProg]
  dsimp only
  omega

private theorem sq_add_three_le_nine_mul_pow (k : ℕ) :
    (k + 3) ^ 2 ≤ 9 * 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have hk : (k + 1 + 3) ^ 2 ≤ 2 * (k + 3) ^ 2 := by
      have hsq : 2 * (k + 3) ^ 2 = (k + 1 + 3) ^ 2 + (k * k + 4 * k + 2) := by ring
      omega
    have h2 : 9 * 2 ^ (k + 1) = 2 * (9 * 2 ^ k) := by ring
    omega

private theorem densePreprocessProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State} (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (21 * es.length + 3 * n + 3))) :
    Memory.FramedTriple w s (densePreprocessProg ⟨n, es.length, edgeBase⟩)
      (62 * es.length + 9 * n + 9) ∅ fun res s' =>
        s'.frontier ≤ s.frontier + (21 * es.length + 3 * n) ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        res.numVertices ≤ n ∧
        res.numEdges ≤ es.length ∧
        Memory.WellFormed w s' ∧
        ∃ esOut : List (IndexedEdge res.numVertices),
          esOut.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase esOut s'.mem ∧
          (∀ y : Fin res.numVertices, ∃ e ∈ esOut, e.u = y ∨ e.v = y) ∧
          ∀ L : List (IndexedEdge res.numVertices),
            L.Subperm esOut →
            IsMinSpanningForest (esOut.map IndexedEdge.toWeighted)
              (L.map IndexedEdge.toWeighted) →
            ∃ msfEs : List (IndexedEdge n),
              msfEs.Subperm es ∧
              msfEs.length = L.length ∧
              (∀ j (hj : j < L.length) (hj' : j < msfEs.length),
                ∃ hid : L[j].id < es.length, msfEs[j] = es[L[j].id]'hid) ∧
              IsMinSpanningForest (es.map IndexedEdge.toWeighted)
                (msfEs.map IndexedEdge.toWeighted) := by
  dsimp only [densePreprocessProg]
  let esLoc : List (IndexedEdge n) := es.mapIdx fun i e => ⟨e.u, e.v, e.weight, i⟩
  have hloc_len : esLoc.length = es.length := List.length_mapIdx
  refine (Memory.FramedTriple.bind_same (c₂ := (41 * es.length + 6 * n + 6) +
      (14 * es.length + 3 * n + 2))
    ((retagLocalEdgesProg_spec h16 hwf hin hin_lt (hfit.of_le (by omega))).mono le_rfl
      fun locBase s₁ ⟨hloc_eq, hfr₁, hwf₁, hholds₁⟩ => ?_)).mono
    (by omega) fun _ _ h => h
  have hded := dedupSimpleEdgesProg_spec h16 hwf₁ hholds₁ (by rw [hloc_len, hloc_eq, hfr₁])
    (by rw [hloc_len, hfr₁]; exact hfit.of_le (by omega))
  rw [show (⟨n, esLoc.length, locBase⟩ : GraphSlice) = ⟨n, es.length, locBase⟩ from by
    rw [hloc_len]] at hded
  refine (Memory.FramedTriple.bind_same (c₂ := 14 * es.length + 3 * n + 2)
    (hded.mono le_rfl fun dedup s₂ ⟨_, hded_bound, hfr₂_le, hwf₂, esDedup, hded_len, hded_sub,
      hded_holds, hded_eq, _, _⟩ => ?_)).mono (by rw [hloc_len]) fun _ _ h => h
  rw [hfr₁, hloc_len] at hfr₂_le
  have hded_le : dedup.numEdges ≤ es.length := hded_len ▸ hded_sub.length_le.trans hloc_len.le
  have hcmp := compactVerticesProg_spec h16 hwf₂ hded_holds (by rw [hded_len]; exact hded_bound)
    (by rw [hded_len]; exact hfit.of_le (by omega))
  rw [show (⟨n, esDedup.length, dedup.edgeBase⟩ : GraphSlice) =
    ⟨n, dedup.numEdges, dedup.edgeBase⟩ from by rw [hded_len]] at hcmp
  refine (Memory.FramedTriple.bind_same (c₂ := 0) (hcmp.mono le_rfl fun comp s₃
      ⟨_, hcomp_eb, hcomp_nv, hfr₃, hwf₃, lift, esOut, hlift_inj, hesOut_len, hesOut_holds, _,
        hnoniso, hesOut_map⟩ => ?_)).mono (by rw [hded_len]; omega) fun _ _ h => h
  refine Memory.FramedTriple.pure ⟨by rw [hfr₃, hded_len]; omega,
    by dsimp only; rw [hfr₃, hcomp_eb, hded_len], hcomp_nv, hded_le, hwf₃,
    esOut, hesOut_len.trans hded_len, hesOut_holds, hnoniso, fun L hL_sub hL_msf => ?_⟩
  let clift : IndexedEdge comp.numVertices → IndexedEdge n :=
    fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩
  let L_ded : List (IndexedEdge n) := L.map clift
  have hL_ded_sub_ded : L_ded.Subperm esDedup :=
    hesOut_map ▸ List.subperm_map clift hL_sub
  have hesLoc_eq : esLoc = (List.finRange es.length).map
      (fun i : Fin es.length => ⟨es[i.val].u, es[i.val].v, es[i.val].weight, i.val⟩) := by
    apply List.ext_getElem
    · simp [esLoc]
    · intro i hi1 hi2
      simp [esLoc, List.getElem_mapIdx]
  have hL_ded_sub_fin : L_ded.Subperm ((List.finRange es.length).map
      fun i : Fin es.length => ⟨es[i.val].u, es[i.val].v, es[i.val].weight, i.val⟩) := by
    simpa only [← hesLoc_eq] using hL_ded_sub_ded.trans hded_sub
  obtain ⟨idxs, hidxs_sub, hidxs_map⟩ := hL_ded_sub_fin.exists_map
  let msfEs := idxs.map (fun i : Fin es.length => es[i.val])
  have hmsf_sub : msfEs.Subperm es := by
    have hm := List.subperm_map (fun i : Fin es.length => es[i.val]) hidxs_sub
    rwa [List.map_getElem_finRange] at hm
  have hmsf_len : msfEs.length = L.length := by
    have hm1 := congrArg List.length hidxs_map
    simp only [List.length_map, L_ded] at hm1
    simpa only [msfEs, List.length_map] using hm1
  have hmsf_get : ∀ (j : ℕ) (hj : j < L.length) (hj' : j < msfEs.length),
      ∃ hid : L[j].id < es.length, msfEs[j] = es[L[j].id]'hid := by
    intro j hj hj'
    have hj_id : j < idxs.length := by simpa only [msfEs, List.length_map] using hj'
    have hget := congrArg (fun l => l[j]?) hidxs_map
    simp only [List.getElem?_map, L_ded, List.getElem?_eq_getElem hj_id,
      List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at hget
    have hid_eq : idxs[j].val = L[j].id := congrArg IndexedEdge.id hget
    refine ⟨hid_eq ▸ idxs[j].isLt, ?_⟩
    simp only [msfEs, List.getElem_map]
    congr 1
  have hL_ded_msf : IsMinSpanningForest (esDedup.map IndexedEdge.toWeighted)
      (L_ded.map IndexedEdge.toWeighted) := by
    have h1 := compactVertices_isMinSpanningForest hlift_inj hesOut_map hL_msf
    have h2 : contractEdgeList lift (L.map IndexedEdge.toWeighted) =
        L_ded.map IndexedEdge.toWeighted := by
      simp [L_ded, clift, contractEdgeList, List.map_map, Function.comp_def, contractEdge,
        IndexedEdge.toWeighted]
    rwa [← h2]
  have hL_loc_msf : IsMinSpanningForest (esLoc.map IndexedEdge.toWeighted)
      (L_ded.map IndexedEdge.toWeighted) :=
    isMinSpanningForest_of_dedupSimpleEdges _ _ (hded_eq ▸ hL_ded_msf)
  have hes_w : esLoc.map IndexedEdge.toWeighted = es.map IndexedEdge.toWeighted := by
    apply List.ext_getElem
    · simp [hloc_len]
    · intro i hi1 hi2
      simp [esLoc, List.getElem_mapIdx, IndexedEdge.toWeighted]
  have hmsf_w : msfEs.map IndexedEdge.toWeighted = L_ded.map IndexedEdge.toWeighted := by
    rw [← hidxs_map, List.map_map, List.map_map]
    rfl
  rw [hes_w, ← hmsf_w] at hL_loc_msf
  exact ⟨msfEs, hmsf_sub, hmsf_len, hmsf_get, hL_loc_msf⟩

private theorem densePreprocess_word_posts {w : ℕ} {g : GraphSlice} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : g.edgeBase + 4 * g.numEdges ≤ s.frontier)
    (hfit : Fits w (s.frontier + (21 * g.numEdges + 3 * g.numVertices + 3)))
    (hedges : ∀ j < g.numEdges,
      s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
      s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) :
    let locBase := (Memory.spec 0).clientResult s (retagLocalEdgesProg ⟨g.edgeBase, g.numEdges⟩)
    let s₁ := (Memory.spec 0).clientState s (retagLocalEdgesProg ⟨g.edgeBase, g.numEdges⟩)
    let g₁ : GraphSlice := ⟨g.numVertices, g.numEdges, locBase⟩
    let ded := (Memory.spec 0).clientResult s₁ (dedupSimpleEdgesProg g₁)
    let s₂ := (Memory.spec 0).clientState s₁ (dedupSimpleEdgesProg g₁)
    (locBase + 4 * g.numEdges ≤ s₁.frontier ∧
      Fits w (s₁.frontier + (13 * g.numEdges + 2 * g.numVertices)) ∧
      ∀ j < g.numEdges,
        s₁.mem (locBase + 4 * j) < g.numVertices ∧
        s₁.mem (locBase + 4 * j + 1) < g.numVertices) ∧
    (ded.edgeBase + 4 * ded.numEdges ≤ s₂.frontier ∧
      Fits w (s₂.frontier + (g.numVertices + 4 * ded.numEdges + 1)) ∧
      ∀ j < ded.numEdges,
        s₂.mem (ded.edgeBase + 4 * j) < g.numVertices ∧
        s₂.mem (ded.edgeBase + 4 * j + 1) < g.numVertices) := by
  rcases g with ⟨n, m, eb⟩; dsimp only at *
  obtain ⟨es, hlen, hin⟩ := exists_indexedEdges_of_mem_lt hedges
  have h1_ft := retagLocalEdgesProg_spec h16 hwf hin (by rw [hlen]; exact hin_lt)
    (by rw [hlen]; exact hfit.of_le (by omega))
  rw [hlen] at h1_ft
  obtain ⟨_, _, _, hloc, hfr₁, hwf₁, hholds₁⟩ := framedTriple_iff_realization.mp h1_ft
  let esLoc := es.mapIdx fun i e => (⟨e.u, e.v, e.weight, i⟩ : IndexedEdge n)
  have hloc_len : esLoc.length = m := by simp [esLoc, hlen]
  have h2_ft := dedupSimpleEdgesProg_spec h16 hwf₁ hholds₁ (by rw [hloc_len, hloc, hfr₁])
    (by rw [hloc_len, hfr₁]; exact hfit.of_le (by omega))
  rw [show (⟨n, esLoc.length, _⟩ : GraphSlice) = ⟨n, m, _⟩ from by rw [hloc_len]] at h2_ft
  obtain ⟨_, _, _, hded_nv, hded_bound, hfr₂_le, _, esDedup, hded_len, hded_sub, hded_holds, _⟩ :=
    framedTriple_iff_realization.mp h2_ft
  have hded_le : esDedup.length ≤ m := hded_len ▸ hded_sub.length_le.trans hloc_len.le
  refine ⟨⟨by rw [hloc, hfr₁], by rw [hfr₁]; exact hfit.of_le (by omega), fun j hj => by
      obtain ⟨hu, hv, _⟩ := hholds₁ j (hloc_len.symm ▸ hj)
      exact ⟨hu ▸ (esLoc[j]'(hloc_len.symm ▸ hj)).u.isLt,
        hv ▸ (esLoc[j]'(hloc_len.symm ▸ hj)).v.isLt⟩⟩,
    ⟨hded_bound, by
        dsimp only [esLoc] at hloc_len
        rw [hfr₁, hloc_len] at hfr₂_le
        rw [← hded_len]
        exact hfit.of_le (by omega),
      fun j hj => by
        obtain ⟨hu, hv, _⟩ := hded_holds j (hded_len.symm ▸ hj)
        exact ⟨hu ▸ (esDedup[j]'(hded_len.symm ▸ hj)).u.isLt,
          hv ▸ (esDedup[j]'(hded_len.symm ▸ hj)).v.isLt⟩⟩⟩

private theorem realizes_densePreprocessProg : Realizes .exact
    densePreprocessProg WordEncoding.encode WordEncoding.encode
    (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (21 * g.numEdges + 3 * g.numVertices + 3)) ∧
      ∀ j < g.numEdges,
        s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
    (fun _ _ => 0) := by
  unfold densePreprocessProg
  realize [realizes_retagLocalEdgesProg, realizes_dedupSimpleEdgesProg,
    realizes_compactVerticesProg]
  all_goals
    obtain ⟨h16, hin_lt, hfit, hedges⟩ := h
    first
    | exact h16 | exact hin_lt | exact hfit.of_le (by omega)
    | (obtain ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ :=
         densePreprocess_word_posts h16 hmem hin_lt hfit hedges
       first | exact a1 | exact a2 | exact a3 | exact b1 | exact b2 | exact b3)

/-! ## Private Phase Step and Contraction Loop -/

private def densePhaseStepProg (x : DensePhaseEnv × DenseLoopState) :
    Memory.Prog DenseLoopState := do
  let env := Prod.fst x
  let st := Prod.snd x
  let csr ← buildUndirCSR ⟨st.numVertices, st.numEdges, st.edgeBase⟩
  let ph ← ftPhaseProg ⟨st.numVertices, st.numEdges, env.mRef, st.edgeBase,
    csr.offBase, csr.adjBase, env.selBufBase, st.selLen⟩
  let sh ← boruvkaShrinkProg ⟨st.numVertices, ph.nComp, st.numEdges, st.edgeBase, ph.compBase⟩
  pure ⟨sh.numVertices, sh.numEdges, sh.edgeBase, ph.selLen⟩

private def densePhaseStepProgSafe (w : ℕ) (x : DensePhaseEnv × DenseLoopState)
    (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let st := Prod.snd x
  let csr := (Memory.spec 0).clientResult s
    (buildUndirCSR ⟨st.numVertices, st.numEdges, st.edgeBase⟩)
  let s₁ := (Memory.spec 0).clientState s
    (buildUndirCSR ⟨st.numVertices, st.numEdges, st.edgeBase⟩)
  let ph := (Memory.spec 0).clientResult s₁
    (ftPhaseProg ⟨st.numVertices, st.numEdges, env.mRef, st.edgeBase,
      csr.offBase, csr.adjBase, env.selBufBase, st.selLen⟩)
  let s₂ := (Memory.spec 0).clientState s₁
    (ftPhaseProg ⟨st.numVertices, st.numEdges, env.mRef, st.edgeBase,
      csr.offBase, csr.adjBase, env.selBufBase, st.selLen⟩)
  Fits w 16 ∧
  st.edgeBase + 4 * st.numEdges ≤ s.frontier ∧
  Fits w (s.frontier + (2 * st.numVertices + 4 * st.numEdges + 1)) ∧
  (∀ j < st.numEdges,
    s.mem (st.edgeBase + 4 * j) < st.numVertices ∧
    s.mem (st.edgeBase + 4 * j + 1) < st.numVertices) ∧
  ftPhaseProgSafe w ⟨st.numVertices, st.numEdges, env.mRef, st.edgeBase,
    csr.offBase, csr.adjBase, env.selBufBase, st.selLen⟩ s₁ ∧
  st.edgeBase + 4 * st.numEdges ≤ s₂.frontier ∧
  ph.compBase + st.numVertices ≤ s₂.frontier ∧
  Fits w (s₂.frontier + (21 * st.numEdges + 3 * ph.nComp + 3)) ∧
  (∀ j < st.numEdges,
    s₂.mem (st.edgeBase + 4 * j) < st.numVertices ∧
    s₂.mem (st.edgeBase + 4 * j + 1) < st.numVertices) ∧
  (∀ u < st.numVertices, s₂.mem (ph.compBase + u) < ph.nComp)

private theorem realizes_densePhaseStepProg : Realizes .exact
    densePhaseStepProg WordEncoding.encode WordEncoding.encode densePhaseStepProgSafe
    (fun x _ => (2 * (Prod.fst x).mRef) / (Prod.snd x).numVertices + 2) := by
  unfold densePhaseStepProg
  realize [realizes_buildUndirCSR, realizes_ftPhaseProg, realizes_boruvkaShrinkProg]
  all_goals
    rcases h with ⟨h16, h_csr_eb, h_csr_fit, h_csr_ed, h_ft, h_sh_eb, h_sh_cb, h_sh_fit,
      h_sh_ed, h_sh_cp⟩
    first
    | exact h16 | exact h_csr_eb | exact h_csr_fit | exact h_csr_ed | exact h_ft
    | exact h_sh_eb | exact h_sh_cb | exact h_sh_fit | exact h_sh_ed | exact h_sh_cp

private theorem densePhaseStepProg_spec {w n mRef edgeBase selBufBase selEnd selLen0 : ℕ}
    {es : List (IndexedEdge n)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn1 : 1 ≤ n) (hm_le : es.length ≤ mRef) (hfit_mRef : Fits w (2 * mRef + 1))
    (hsel_fr : selBufBase + selLen0 + n ≤ selEnd) (hsel_end : selEnd ≤ s.frontier)
    (hsel_disj_edge : selBufBase + selLen0 + n ≤ edgeBase ∨
      edgeBase + 4 * es.length ≤ selBufBase + selLen0)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (19 * n + 25 * es.length + 9))) :
    let env : DensePhaseEnv := ⟨mRef, selBufBase, selEnd⟩
    let st : DenseLoopState := ⟨n, es.length, edgeBase, selLen0⟩
    let prog := densePhaseStepProg (env, st)
    densePhaseStepProgSafe w (env, st) s ∧
    Memory.FramedTriple w s prog (316 * es.length + 172 * n + 184 * mRef + 36)
      (Set.Ico (selBufBase + selLen0) (selBufBase + selLen0 + n)) fun res s' =>
      s'.frontier ≤ s.frontier + (19 * n + 25 * es.length + 9) ∧
      selEnd ≤ res.edgeBase ∧
      res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
      res.numVertices ≤ n ∧ res.numEdges ≤ es.length ∧
      ftPhaseRank mRef res.numVertices < ftPhaseRank mRef n ∧
      (1 ≤ res.numVertices → 2 ^ ((2 * mRef) / n) < n) ∧
      Memory.WellFormed w s' ∧
      ∃ (selEs : List (IndexedEdge n)) (esOut : List (IndexedEdge res.numVertices)),
        res.selLen = selLen0 + selEs.length ∧
        selEs.length + res.numVertices ≤ n ∧
        esOut.length = res.numEdges ∧
        HoldsIndexedEdges res.edgeBase esOut s'.mem ∧
        (∀ j (hj : j < selEs.length), s'.mem (selBufBase + selLen0 + j) = selEs[j].id) ∧
        (∀ L_out : List (IndexedEdge res.numVertices),
          L_out.Subperm esOut →
          IsMinSpanningForest (esOut.map IndexedEdge.toWeighted)
            (L_out.map IndexedEdge.toWeighted) →
          ∃ L_orig : List (IndexedEdge n),
            (selEs ++ L_orig).Subperm es ∧
            L_orig.map IndexedEdge.id = L_out.map IndexedEdge.id ∧
            IsMinSpanningForest (es.map IndexedEdge.toWeighted)
              ((selEs ++ L_orig).map IndexedEdge.toWeighted)) := by
  let env : DensePhaseEnv := ⟨mRef, selBufBase, selEnd⟩
  let st : DenseLoopState := ⟨n, es.length, edgeBase, selLen0⟩
  have h1 := buildUndirCSR_spec (w := w) (n := n) (edgeBase := edgeBase) (es := es) (s := s)
    h16 hwf hin hin_lt (hfit.of_le (by omega))
  obtain ⟨hv₁, hc₁, hmod₁, hcsr1, hcsr2, hfr₁, hwf₁, hcsr_holds⟩ :=
    framedTriple_iff_realization.mp h1
  set csr := (Memory.spec 0).clientResult s (buildUndirCSR ⟨n, es.length, edgeBase⟩)
  set s₁ := (Memory.spec 0).clientState s (buildUndirCSR ⟨n, es.length, edgeBase⟩)
  have hin₁ : HoldsIndexedEdges edgeBase es s₁.mem :=
    hin.congr fun a _ ha => hmod₁.mem_eq_of_not_mem (by omega) (Set.notMem_empty _)
  have h2 := @ftPhaseProg_spec w n mRef es edgeBase csr.offBase csr.adjBase selBufBase selLen0 s₁
    h16 hwf₁ hn1 (hfit_mRef.of_le (by omega)) (by rw [hfr₁]; exact hfit.of_le (by omega))
    (by rw [hfr₁, hcsr1]; omega) (by rw [hfr₁, hcsr2]; omega) (by rw [hfr₁]; omega)
    (by rw [hfr₁]; omega) hsel_disj_edge (Or.inl (by rw [hcsr1]; omega))
    (Or.inl (by rw [hcsr2]; omega)) hin₁ hcsr_holds
  dsimp only at h2
  generalize h_ph : (Memory.spec 0).clientResult s₁
    (ftPhaseProg ⟨n, es.length, mRef, edgeBase, csr.offBase, csr.adjBase, selBufBase, selLen0⟩) =
    ph at h2
  generalize h_s2 : (Memory.spec 0).clientState s₁
    (ftPhaseProg ⟨n, es.length, mRef, edgeBase, csr.offBase, csr.adjBase, selBufBase, selLen0⟩) =
    s₂ at h2
  rcases h2 with ⟨hsafe₂, hv₂, hfr₂, hwf₂, hmod₂, hcomp_fr, hnc1, hnc_le,
    ⟨selEs, compFn, hsel_sub, hsel_len, hsel_card, hsel_buf, hac, hext, hsurj, hcomp_mem,
      hcomp_rel, hcomp_deg⟩, hc₂⟩
  have hmod₂_set : Memory.Modifies (Set.Ico (selBufBase + selLen0) (selBufBase + selLen0 + n))
      s₁ s₂ := by
    refine ⟨by rw [← h_s2]; exact Memory.frontier_le_clientState _ _, fun a ha hnot => ?_⟩
    rw [Set.mem_Ico, not_and_or, not_le, not_lt] at hnot
    exact hmod₂ a ha hnot
  have hin₂ : HoldsIndexedEdges edgeBase es s₂.mem :=
    hin₁.congr fun a _ ha => hmod₂ a (by rw [hfr₁]; omega) (by
      rcases hsel_disj_edge with hd | hd <;> [right; left] <;> omega)
  have h3 := @boruvkaShrinkProg_spec w n ph.nComp edgeBase ph.compBase es compFn s₂
    h16 hwf₂ hin₂ (by rw [hfr₂, hfr₁]; omega) hcomp_mem hcomp_fr
    (hfit.of_le (by rw [hfr₂, hfr₁]; omega))
  set sh := (Memory.spec 0).clientResult s₂
    (boruvkaShrinkProg ⟨n, ph.nComp, es.length, edgeBase, ph.compBase⟩)
  set s₃ := (Memory.spec 0).clientState s₂
    (boruvkaShrinkProg ⟨n, ph.nComp, es.length, edgeBase, ph.compBase⟩)
  obtain ⟨hv₃, hc₃, hmod₃, hfr₃_le, hsh_eb_ge, hsh_eb_fr, hsh_nv_le, hsh_ne_le, hwf₃,
    esCon, esDedup, lift, esOut, hes_con, hded_sub, hded_eq, hded_simp, hlift_inj,
    hesOut_len, hesOut_holds, hnoniso, hesOut_map⟩ := framedTriple_iff_realization.mp h3
  change Memory.Modifies ∅ s₂ s₃ at hmod₃
  change s₃.frontier ≤ s₂.frontier + (21 * es.length + 3 * ph.nComp + 3) at hfr₃_le
  change s₂.frontier ≤ sh.edgeBase at hsh_eb_ge
  change sh.edgeBase + 4 * sh.numEdges ≤ s₃.frontier at hsh_eb_fr
  change sh.numVertices ≤ ph.nComp at hsh_nv_le
  change sh.numEdges ≤ es.length at hsh_ne_le
  change Memory.WellFormed w s₃ at hwf₃
  have hded_noloop : ∀ e ∈ esDedup, e.u ≠ e.v := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
    have hno := ((isSimple_iff _).mp hded_simp).1 ⟨i, by simp [hi]⟩
    simpa [edgeEnds, IndexedEdge.toWeighted, Sym2.mk_isDiag_iff] using hno
  have hrank_lt := ftPhase_rank_lt_of_shrink hn1 hm_le hsh_nv_le hnc_le hcomp_deg
    hes_con hded_sub hded_noloop hlift_inj hesOut_map hnoniso
  have htwo_pow_lt : 1 ≤ sh.numVertices → 2 ^ ((2 * mRef) / n) < n := fun hn1_out => by
    have h1 : 1 ≤ ftPhaseRank mRef sh.numVertices := by
      dsimp only [ftPhaseRank]; rw [ite_eq_right (Nat.ne_of_gt hn1_out)]
      exact Nat.one_le_iterClogBeta _ _
    have h2 : Nat.iterClogBeta ((2 * mRef) / n) n ≠ 1 := by
      have hr : ftPhaseRank mRef n = Nat.iterClogBeta ((2 * mRef) / n) n := by
        dsimp only [ftPhaseRank]; exact ite_eq_right (Nat.ne_of_gt hn1)
      have := hrank_lt.2
      omega
    have hgt : 2 ^ max 1 ((2 * mRef) / n) < n :=
      Nat.lt_of_not_ge (fun hle => h2 (Nat.iterClogBeta_eq_one_iff.mpr hle))
    exact lt_of_le_of_lt (Nat.pow_le_pow_right (by decide : 0 < 2) (le_max_right 1 _)) hgt
  have hsel_buf₃ : ∀ j (hj : j < selEs.length), s₃.mem (selBufBase + selLen0 + j) = selEs[j].id :=
    fun j hj => (hmod₃.mem_eq_of_not_mem (by rw [hfr₂, hfr₁]; omega)
      (Set.notMem_empty _)).trans (hsel_buf j hj)
  have hsh_ge_end : selEnd ≤ sh.edgeBase := by
    have := hmod₁.1
    have := hmod₂_set.1
    omega
  have h1_ft : Memory.FramedTriple w s (buildUndirCSR ⟨n, es.length, edgeBase⟩)
      (16 * es.length + 5 * n + 6) ∅ fun r₁ t₁ => r₁ = csr ∧ t₁ = s₁ :=
    framedTriple_iff_realization.mpr ⟨hv₁, hc₁, hmod₁, rfl, rfl⟩
  have h2_ft : Memory.FramedTriple w s₁
      (ftPhaseProg ⟨n, es.length, mRef, edgeBase, csr.offBase, csr.adjBase, selBufBase, selLen0⟩)
      (234 * es.length + 156 * n + 184 * mRef + 7)
      (Set.Ico (selBufBase + selLen0) (selBufBase + selLen0 + n)) fun r₂ t₂ =>
        r₂ = ph ∧ t₂ = s₂ :=
    framedTriple_iff_realization.mpr ⟨hv₂, hc₂, h_s2.symm ▸ hmod₂_set, h_ph, h_s2⟩
  have h3_ft : Memory.FramedTriple w s₂
      (boruvkaShrinkProg ⟨n, ph.nComp, es.length, edgeBase, ph.compBase⟩)
      (66 * es.length + 11 * ph.nComp + 23) ∅ fun r₃ t₃ => r₃ = sh ∧ t₃ = s₃ :=
    framedTriple_iff_realization.mpr ⟨hv₃, hc₃, hmod₃, rfl, rfl⟩
  have hsafe : densePhaseStepProgSafe w (env, st) s := by
    dsimp only [densePhaseStepProgSafe, env, st]
    refine ⟨h16, hin_lt, hfit.of_le (by omega), fun j hj => ?_, hsafe₂,
      by rw [h_s2, hfr₂, hfr₁]; omega, by rw [h_ph, h_s2]; exact hcomp_fr,
      by rw [h_ph, h_s2, hfr₂, hfr₁]; exact hfit.of_le (by omega),
      fun j hj => ?_, fun u hu => ?_⟩
    · obtain ⟨hu, hv, _, _⟩ := hin j hj
      exact ⟨hu ▸ es[j].u.isLt, hv ▸ es[j].v.isLt⟩
    · rw [h_s2]
      obtain ⟨hu, hv, _, _⟩ := hin₂ j hj
      exact ⟨hu ▸ es[j].u.isLt, hv ▸ es[j].v.isLt⟩
    · rw [h_ph, h_s2]
      exact hcomp_mem ⟨u, hu⟩ ▸ (compFn ⟨u, hu⟩).isLt
  refine ⟨hsafe, ?_⟩
  have hprog : densePhaseStepProg (env, st) =
      (buildUndirCSR ⟨n, es.length, edgeBase⟩ >>= fun c =>
        ftPhaseProg ⟨n, es.length, mRef, edgeBase, c.offBase, c.adjBase, selBufBase, selLen0⟩ >>=
          fun p =>
        boruvkaShrinkProg ⟨n, p.nComp, es.length, edgeBase, p.compBase⟩ >>= fun q =>
        pure ⟨q.numVertices, q.numEdges, q.edgeBase, p.selLen⟩) := rfl
  let Q_step : DenseLoopState → Memory.State → Prop := fun res s' =>
    s'.frontier ≤ s.frontier + (19 * n + 25 * es.length + 9) ∧
    selEnd ≤ res.edgeBase ∧
    res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
    res.numVertices ≤ n ∧ res.numEdges ≤ es.length ∧
    ftPhaseRank mRef res.numVertices < ftPhaseRank mRef n ∧
    (1 ≤ res.numVertices → 2 ^ ((2 * mRef) / n) < n) ∧
    Memory.WellFormed w s' ∧
    ∃ (selEs : List (IndexedEdge n)) (esOut : List (IndexedEdge res.numVertices)),
      res.selLen = selLen0 + selEs.length ∧
      selEs.length + res.numVertices ≤ n ∧
      esOut.length = res.numEdges ∧
      HoldsIndexedEdges res.edgeBase esOut s'.mem ∧
      (∀ j (hj : j < selEs.length), s'.mem (selBufBase + selLen0 + j) = selEs[j].id) ∧
      (∀ L_out : List (IndexedEdge res.numVertices),
        L_out.Subperm esOut →
        IsMinSpanningForest (esOut.map IndexedEdge.toWeighted)
          (L_out.map IndexedEdge.toWeighted) →
        ∃ L_orig : List (IndexedEdge n),
          (selEs ++ L_orig).Subperm es ∧
          L_orig.map IndexedEdge.id = L_out.map IndexedEdge.id ∧
          IsMinSpanningForest (es.map IndexedEdge.toWeighted)
            ((selEs ++ L_orig).map IndexedEdge.toWeighted))
  rw [hprog]
  refine ((Memory.FramedTriple.bind (c₂ := (234 * es.length + 156 * n + 184 * mRef + 7) +
      (66 * es.length + 11 * ph.nComp + 23))
      (S₂ := Set.Ico (selBufBase + selLen0) (selBufBase + selLen0 + n)) (Q := Q_step)
      (Memory.FramedTriple.mono h1_ft le_rfl ?_)).frame_mono
    (Set.empty_union _).subset).mono (by omega) fun _ _ h => h
  rintro _ _ ⟨rfl, rfl⟩
  refine (Memory.FramedTriple.bind (c₂ := 66 * es.length + 11 * ph.nComp + 23)
      (S₂ := ∅) (Q := Q_step)
      (Memory.FramedTriple.mono h2_ft le_rfl ?_)).frame_mono
    (Set.union_empty _).subset
  rintro _ _ ⟨rfl, rfl⟩
  refine (Memory.FramedTriple.bind (c₂ := 0) (S₂ := ∅) (Q := Q_step)
      (Memory.FramedTriple.mono h3_ft le_rfl ?_)).frame_mono
    (Set.union_empty ∅).subset
  rintro _ _ ⟨rfl, rfl⟩
  dsimp only [Q_step]
  exact Memory.FramedTriple.pure (c := 0) ⟨by rw [hfr₂, hfr₁] at hfr₃_le; omega, hsh_ge_end,
    hsh_eb_fr, hsh_nv_le.trans hnc_le, hsh_ne_le, hrank_lt.2, htwo_pow_lt, hwf₃, selEs, esOut,
    hsel_len, by dsimp only; omega, hesOut_len, hesOut_holds, hsel_buf₃,
    fun L_out hL_sub hL_msf => boruvkaStepProg_lift_msf hsel_sub hext hsurj hcomp_rel hes_con
      hded_sub hded_eq hded_simp hlift_inj hesOut_map hL_sub hL_msf⟩

private def densePhaseLoopProg (d : DenseLoopInit) : Memory.Prog DenseLoopOut := do
  let sel ← Memory.allocBlockDirty d.numVertices
  let res ← boundedWhile (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
    densePhaseStepProg ⟨d.mRef, sel.base, sel.base + d.numVertices⟩ d.numVertices
    ⟨d.numVertices, d.numEdges, d.edgeBase, 0⟩
  pure ⟨sel.base, res.selLen⟩

private def denseLoopInv {w n₁ mRef selBase selEnd : ℕ} (es₁ : List (IndexedEdge n₁))
    (s₁ : Memory.State) (st : DenseLoopState) (t : Memory.State) : Prop :=
  s₁.frontier = selEnd ∧
  selBase + n₁ = selEnd ∧
  selEnd ≤ t.frontier ∧
  t.frontier + ftPhaseRank mRef st.numVertices * (76 * mRef) ≤
    s₁.frontier + ftPhaseRank mRef n₁ * (76 * mRef) ∧
  Memory.WellFormed w t ∧
  (∀ a < selBase, t.mem a = s₁.mem a) ∧
  (selEnd ≤ st.edgeBase ∨ st.edgeBase + 4 * st.numEdges ≤ selBase) ∧
  ∃ esCur : List (IndexedEdge st.numVertices),
    st.numVertices ≤ n₁ ∧
    esCur.length = st.numEdges ∧
    esCur.length ≤ mRef ∧
    HoldsIndexedEdges st.edgeBase esCur t.mem ∧
    st.edgeBase + 4 * st.numEdges ≤ t.frontier ∧
    st.selLen + st.numVertices ≤ n₁ ∧
    ∀ L_cur : List (IndexedEdge st.numVertices),
      L_cur.Subperm esCur →
      IsMinSpanningForest (esCur.map IndexedEdge.toWeighted) (L_cur.map IndexedEdge.toWeighted) →
      ∃ L₁ : List (IndexedEdge n₁),
        L₁.Subperm es₁ ∧
        L₁.length = st.selLen + L_cur.length ∧
        (∀ j (_hj : j < st.selLen) (hj' : j < L₁.length), L₁[j].id = t.mem (selBase + j)) ∧
        (∀ j (hj : j < L_cur.length) (hj' : st.selLen + j < L₁.length),
          L₁[st.selLen + j].id = L_cur[j].id) ∧
        IsMinSpanningForest (es₁.map IndexedEdge.toWeighted) (L₁.map IndexedEdge.toWeighted)

private theorem densePhaseLoop_step_lift {n₁ st_nv selBase st_sel : ℕ}
    {es₁ : List (IndexedEdge n₁)} {esCur selEs : List (IndexedEdge st_nv)}
    {res_nv res_sel : ℕ} {esOut : List (IndexedEdge res_nv)} {t t' : Memory.State}
    (hsel_len' : res_sel = st_sel + selEs.length)
    (hsel_buf' : ∀ j (hj : j < selEs.length), t'.mem (selBase + st_sel + j) = selEs[j].id)
    (hmod_s : Memory.Modifies (Set.Ico (selBase + st_sel) (selBase + st_sel + st_nv)) t t')
    (hst_fr_sel : selBase + st_sel + st_nv ≤ t.frontier)
    (hlift_s : ∀ L_out : List (IndexedEdge res_nv), L_out.Subperm esOut →
      IsMinSpanningForest (esOut.map IndexedEdge.toWeighted) (L_out.map IndexedEdge.toWeighted) →
      ∃ L_orig : List (IndexedEdge st_nv),
        (selEs ++ L_orig).Subperm esCur ∧
        L_orig.map IndexedEdge.id = L_out.map IndexedEdge.id ∧
        IsMinSpanningForest (esCur.map IndexedEdge.toWeighted)
          ((selEs ++ L_orig).map IndexedEdge.toWeighted))
    (hlift_cur : ∀ L_cur : List (IndexedEdge st_nv), L_cur.Subperm esCur →
      IsMinSpanningForest (esCur.map IndexedEdge.toWeighted) (L_cur.map IndexedEdge.toWeighted) →
      ∃ L₁ : List (IndexedEdge n₁),
        L₁.Subperm es₁ ∧
        L₁.length = st_sel + L_cur.length ∧
        (∀ j (_hj : j < st_sel) (hj' : j < L₁.length), L₁[j].id = t.mem (selBase + j)) ∧
        (∀ j (hj : j < L_cur.length) (hj' : st_sel + j < L₁.length),
          L₁[st_sel + j].id = L_cur[j].id) ∧
        IsMinSpanningForest (es₁.map IndexedEdge.toWeighted) (L₁.map IndexedEdge.toWeighted)) :
    ∀ L_cur : List (IndexedEdge res_nv), L_cur.Subperm esOut →
      IsMinSpanningForest (esOut.map IndexedEdge.toWeighted) (L_cur.map IndexedEdge.toWeighted) →
      ∃ L₁ : List (IndexedEdge n₁),
        L₁.Subperm es₁ ∧
        L₁.length = res_sel + L_cur.length ∧
        (∀ j (_hj : j < res_sel) (hj' : j < L₁.length), L₁[j].id = t'.mem (selBase + j)) ∧
        (∀ j (hj : j < L_cur.length) (hj' : res_sel + j < L₁.length),
          L₁[res_sel + j].id = L_cur[j].id) ∧
        IsMinSpanningForest (es₁.map IndexedEdge.toWeighted) (L₁.map IndexedEdge.toWeighted) := by
  intro L_cur hL_sub hL_msf
  obtain ⟨L_orig, hLor_sub, hLor_map, hLor_msf⟩ := hlift_s L_cur hL_sub hL_msf
  obtain ⟨L₁, hL1_sub, hL1_len, hL1_pre, hL1_suf, hL1_msf⟩ :=
    hlift_cur (selEs ++ L_orig) hLor_sub hLor_msf
  have hL_orig_len : L_orig.length = L_cur.length := by
    have := congrArg List.length hLor_map
    simpa only [List.length_map] using this
  refine ⟨L₁, hL1_sub, ?_, fun j hj hj' => ?_, fun j hj hj' => ?_, hL1_msf⟩
  · rw [hsel_len']; rw [List.length_append, hL_orig_len] at hL1_len; omega
  · rw [hsel_len'] at hj
    by_cases hj0 : j < st_sel
    · rw [hL1_pre j hj0 hj', hmod_s.mem_eq_of_not_mem (by omega)
        (by simp only [Set.mem_Ico, not_and, not_lt]; omega)]
    · have hjs : j - st_sel < selEs.length := by omega
      have hjs_add : st_sel + (j - st_sel) = j := by omega
      have h1 := hL1_suf (j - st_sel) (by rw [List.length_append]; omega) (by omega)
      simp only [hjs_add] at h1
      rw [List.getElem_append_left hjs] at h1
      rw [h1]
      conv_rhs => rw [← hjs_add, ← Nat.add_assoc]
      rw [hsel_buf' (j - st_sel) hjs]
  · have hj_or : st_sel + (selEs.length + j) = res_sel + j := by rw [hsel_len']; ring
    have hj_lt_app : selEs.length + j < (selEs ++ L_orig).length := by
      rw [List.length_append]; omega
    have h1 := hL1_suf (selEs.length + j) hj_lt_app (by omega)
    simp only [hj_or] at h1
    rw [List.getElem_append_right (Nat.le_add_right selEs.length j)] at h1
    have hsub_id : selEs.length + j - selEs.length = j := by omega
    simp only [hsub_id] at h1
    have hget_m := congrArg (fun l => l[j]?) hLor_map
    simp only [List.getElem?_map, List.getElem?_eq_getElem (by omega : j < L_orig.length),
      List.getElem?_eq_getElem hj, Option.map_some, Option.some.injEq] at hget_m
    exact h1.trans hget_m

private theorem densePhaseLoop_step_spec {w n₁ mRef selBase selEnd : ℕ}
    {es₁ : List (IndexedEdge n₁)} {s₁ : Memory.State}
    (h16 : Fits w 16) (hn1_le_2m : n₁ ≤ 2 * es₁.length) (hm₁_le : es₁.length ≤ mRef)
    (hfit : Fits w (selBase + (n₁ + 76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁)))
    (hfit_mRef : Fits w (2 * mRef + 1))
    {st : DenseLoopState} {t : Memory.State}
    (hinv : denseLoopInv (w := w) (mRef := mRef) (selBase := selBase) (selEnd := selEnd)
      es₁ s₁ st t)
    (hg : 0 < st.numVertices) :
    let env : DensePhaseEnv := ⟨mRef, selBase, selEnd⟩
    let prog := densePhaseStepProg (env, st)
    let st' := (Memory.spec 0).clientResult t prog
    let t' := (Memory.spec 0).clientState t prog
    densePhaseStepProgSafe w (env, st) t ∧
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t prog) ∧
    memoryCost prog t + ftPhaseRank mRef st'.numVertices * (889 * mRef) ≤
      ftPhaseRank mRef st.numVertices * (889 * mRef) ∧
    Memory.Modifies (Set.Ici selBase) t t' ∧
    denseLoopInv (w := w) (mRef := mRef) (selBase := selBase) (selEnd := selEnd) es₁ s₁ st' t' ∧
    ftPhaseRank mRef st'.numVertices < ftPhaseRank mRef st.numVertices ∧
    (1 ≤ st'.numVertices → 2 ^ ((2 * mRef) / st.numVertices) < st.numVertices) := by
  rcases hinv with ⟨hs1_end, hsel_end, hend_le_t, ht_fr, htwf, htmod, hdisj, esCur, hst_le,
    hesl, hesm, hholds, hed_fr, hsel_le, hlift_cur⟩
  have hmRef_pos : 1 ≤ mRef := by omega
  have hst_2m : st.numVertices ≤ 2 * mRef := by omega
  have hmul_comm : ftPhaseRank mRef n₁ * (76 * mRef) =
      76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁ := by
    dsimp only [ftPhaseRank]
    rw [ite_eq_right (by omega)]
    ring
  have hfit_step : Fits w (t.frontier + (19 * st.numVertices + 25 * esCur.length + 9)) := by
    have h1 : 19 * st.numVertices + 25 * esCur.length + 9 ≤ 76 * mRef := by omega
    have h2 : 1 ≤ ftPhaseRank mRef st.numVertices := by
      dsimp only [ftPhaseRank]; rw [ite_eq_right (by omega)]; exact Nat.one_le_iterClogBeta _ _
    have h3 : 19 * st.numVertices + 25 * esCur.length + 9 ≤
        ftPhaseRank mRef st.numVertices * (76 * mRef) :=
      h1.trans (Nat.le_mul_of_pos_left _ h2)
    exact hfit.of_le (by rw [hs1_end, ← hsel_end] at ht_fr; omega)
  have hsel_fr_end : selBase + st.selLen + st.numVertices ≤ selEnd := by omega
  have hdisj_edge : selBase + st.selLen + st.numVertices ≤ st.edgeBase ∨
      st.edgeBase + 4 * esCur.length ≤ selBase + st.selLen := by
    rw [hesl]
    rcases hdisj with hd | hd <;> [left; right] <;> omega
  obtain ⟨hsafe_s, hstep_ft⟩ := @densePhaseStepProg_spec w st.numVertices mRef st.edgeBase selBase
    selEnd st.selLen esCur t h16 htwf hg hesm (hfit_mRef.of_le (by omega)) hsel_fr_end hend_le_t
    hdisj_edge hholds (by rw [hesl]; exact hed_fr) hfit_step
  rw [show (⟨st.numVertices, esCur.length, st.edgeBase, st.selLen⟩ : DenseLoopState) = st from by
    cases st; simp only [hesl]] at hsafe_s hstep_ft
  set st' := (Memory.spec 0).clientResult t
    (densePhaseStepProg (⟨mRef, selBase, selEnd⟩, st))
  set t' := (Memory.spec 0).clientState t
    (densePhaseStepProg (⟨mRef, selBase, selEnd⟩, st))
  obtain ⟨hv_s, hc_s, hmod_s, ht'_fr, hend_out, hres_ed, hres1_le, hres2_le, hrank_lt, htwo_pow,
    hwf_s, selEs, esOut, hsel_len', hsel_sum, hesOut_len, hesOut_holds, hsel_buf', hlift_s⟩ :=
    framedTriple_iff_realization.mp hstep_ft
  have hdiff_rank : ftPhaseRank mRef st'.numVertices + 1 ≤ ftPhaseRank mRef st.numVertices :=
    hrank_lt
  have hpot_s : memoryCost (densePhaseStepProg (⟨mRef, selBase, selEnd⟩, st)) t +
      ftPhaseRank mRef st'.numVertices * (889 * mRef) ≤
      ftPhaseRank mRef st.numVertices * (889 * mRef) := by
    have hcost_bound :
        316 * esCur.length + 172 * st.numVertices + 184 * mRef + 36 ≤ 889 * mRef := by
      omega
    have hmul_le : (ftPhaseRank mRef st'.numVertices + 1) * (889 * mRef) ≤
        ftPhaseRank mRef st.numVertices * (889 * mRef) :=
      Nat.mul_le_mul_right _ hdiff_rank
    rw [Nat.add_mul, Nat.one_mul] at hmul_le
    omega
  have ht'_fr_bound : t'.frontier + ftPhaseRank mRef st'.numVertices * (76 * mRef) ≤
      s₁.frontier + ftPhaseRank mRef n₁ * (76 * mRef) := by
    have hfr_growth : t'.frontier ≤ t.frontier + 76 * mRef := by
      dsimp only [t']
      have : 19 * st.numVertices + 25 * esCur.length + 9 ≤ 76 * mRef := by omega
      omega
    have hmul_le : (ftPhaseRank mRef st'.numVertices + 1) * (76 * mRef) ≤
        ftPhaseRank mRef st.numVertices * (76 * mRef) :=
      Nat.mul_le_mul_right _ hdiff_rank
    rw [Nat.add_mul, Nat.one_mul] at hmul_le
    omega
  have hmod_ici : Memory.Modifies (Set.Ici selBase) t t' :=
    hmod_s.mono (fun a ha => by simp only [Set.mem_Ico] at ha; exact Set.mem_Ici.mpr (by omega))
  refine ⟨hsafe_s, hv_s, hpot_s, hmod_ici, ⟨hs1_end, hsel_end, hend_le_t.trans hmod_s.1,
    ht'_fr_bound, hwf_s, fun a ha => ?_, Or.inl hend_out,
    esOut, hres1_le.trans hst_le, hesOut_len, hesOut_len ▸ hres2_le.trans hesm, hesOut_holds,
    hres_ed,
    by rw [hsel_len']; omega, fun L_cur hL_sub hL_msf => ?_⟩, hrank_lt, htwo_pow⟩
  · rw [hmod_s.mem_eq_of_not_mem (by omega) (by simp only [Set.mem_Ico, not_and, not_lt]; omega),
      htmod a ha]
  · exact densePhaseLoop_step_lift hsel_len' hsel_buf' hmod_s (by omega) hlift_s hlift_cur
      L_cur hL_sub hL_msf

private def denseWorkPot (mRef : ℕ) (st : DenseLoopState) : ℕ :=
  if st.numVertices = 0 then 0
  else ftPhaseRank mRef st.numVertices * (Nat.log 2 (2 * mRef) + 3) + (2 * mRef + 3)

private theorem denseLoop_whileWork_le {w n₁ mRef selBase selEnd : ℕ}
    {es₁ : List (IndexedEdge n₁)} {s₁ : Memory.State}
    (h16 : Fits w 16) (hn1_le_2m : n₁ ≤ 2 * es₁.length) (hm₁_le : es₁.length ≤ mRef)
    (hfit : Fits w (selBase + (n₁ + 76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁)))
    (hfit_mRef : Fits w (2 * mRef + 1)) :
    ∀ (fuel : ℕ) (st : DenseLoopState) (t : Memory.State),
      denseLoopInv (w := w) (mRef := mRef) (selBase := selBase) (selEnd := selEnd) es₁ s₁ st t →
      whileWork (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
        densePhaseStepProg (fun x _ => (2 * (Prod.fst x).mRef) / (Prod.snd x).numVertices + 2)
        ⟨mRef, selBase, selEnd⟩ fuel st t ≤ denseWorkPot mRef st := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ _ _
    simp only [whileWork, Nat.zero_le]
  | succ fuel ih =>
    intro st t hinv
    by_cases hg : 0 < st.numVertices
    · have hst := densePhaseLoop_step_spec h16 hn1_le_2m hm₁_le hfit hfit_mRef hinv hg
      rcases hst with ⟨_, _, _, _, hinv', hrank_lt, htwo_pow⟩
      have hst_2m : st.numVertices ≤ 2 * mRef := by
        rcases hinv with ⟨_, _, _, _, _, _, _, _, hst_le, _, _, _, _, _, _⟩
        omega
      set env : DensePhaseEnv := ⟨mRef, selBase, selEnd⟩
      set st' := (Memory.spec 0).clientResult t (densePhaseStepProg (env, st))
      set t' := (Memory.spec 0).clientState t (densePhaseStepProg (env, st))
      have hih := ih st' t' hinv'
      have hstep_work :
          ((2 * mRef) / st.numVertices + 2) + 1 + denseWorkPot mRef st' ≤
            denseWorkPot mRef st := by
        have hnz : st.numVertices ≠ 0 := Nat.ne_of_gt hg
        dsimp only [denseWorkPot]
        rw [ite_eq_right hnz]
        by_cases hz' : st'.numVertices = 0
        · rw [ite_eq_left hz', Nat.add_zero]
          have hdiv : (2 * mRef) / st.numVertices ≤ 2 * mRef := Nat.div_le_self _ _
          omega
        · rw [ite_eq_right hz']
          have hpow := htwo_pow (Nat.pos_of_ne_zero hz')
          have hlog : (2 * mRef) / st.numVertices ≤ Nat.log 2 (2 * mRef) :=
            Nat.le_log_of_pow_le (by decide : 1 < 2) (by omega)
          have hmul : (ftPhaseRank mRef st'.numVertices + 1) * (Nat.log 2 (2 * mRef) + 3) ≤
              ftPhaseRank mRef st.numVertices * (Nat.log 2 (2 * mRef) + 3) :=
            Nat.mul_le_mul_right _ hrank_lt
          rw [Nat.add_mul, Nat.one_mul] at hmul
          omega
      simp only [whileWork, hg, ↓reduceIte]
      dsimp only [env, st', t'] at hih hstep_work ⊢
      omega
    · simp only [whileWork, hg, ↓reduceIte, Nat.zero_le]

private theorem densePhaseLoopProg_spec {w n₁ edge₁ mRef : ℕ}
    {es₁ : List (IndexedEdge n₁)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin₁ : HoldsIndexedEdges edge₁ es₁ s.mem)
    (hin₁_lt : edge₁ + 4 * es₁.length ≤ s.frontier)
    (hm₁_le : es₁.length ≤ mRef)
    (hnoniso₁ : ∀ y : Fin n₁, ∃ e ∈ es₁, e.u = y ∨ e.v = y)
    (hfit : Fits w (s.frontier + (n₁ + 76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁)))
    (hfit_mRef : Fits w (2 * mRef + 1)) :
    Memory.FramedTriple w s (densePhaseLoopProg ⟨n₁, es₁.length, edge₁, mRef⟩)
      (1 + 889 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁) ∅ fun res s' =>
        res.selBufBase = s.frontier ∧
        res.selLen ≤ n₁ ∧
        s'.frontier ≤ s.frontier + n₁ + 76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁ ∧
        res.selBufBase + res.selLen ≤ s'.frontier ∧
        Memory.WellFormed w s' ∧
        ∃ msf₁ : List (IndexedEdge n₁),
          msf₁.Subperm es₁ ∧
          msf₁.length = res.selLen ∧
          (∀ j (_hj : j < res.selLen) (hj' : j < msf₁.length),
            s'.mem (res.selBufBase + j) = msf₁[j].id) ∧
          IsMinSpanningForest (es₁.map IndexedEdge.toWeighted)
            (msf₁.map IndexedEdge.toWeighted) := by
  let selBase := s.frontier
  let selEnd := selBase + n₁
  let s₁ : Memory.State := ⟨s.mem, selEnd⟩
  have hfit_alloc : Fits w selEnd := hfit.of_le (by omega)
  have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit_alloc, hwf.mem_fits⟩
  have hin₁' : HoldsIndexedEdges edge₁ es₁ s₁.mem := hin₁
  have hn1_le_2m : n₁ ≤ 2 * es₁.length := card_le_two_mul_of_noIsolated hnoniso₁
  let guard : DensePhaseEnv → DenseLoopState → Prop := fun _ st => 0 < st.numVertices
  let env : DensePhaseEnv := ⟨mRef, selBase, selEnd⟩
  let st₀ : DenseLoopState := ⟨n₁, es₁.length, edge₁, 0⟩
  let rank (st : DenseLoopState) (_ : Memory.State) : ℕ := ftPhaseRank mRef st.numVertices
  let pot (st : DenseLoopState) (_ : Memory.State) : ℕ :=
    ftPhaseRank mRef st.numVertices * (889 * mRef)
  have hbw := boundedWhile_potential_spec guard densePhaseStepProg densePhaseStepProgSafe
    w env 0 (denseLoopInv (w := w) (mRef := mRef) (selBase := selBase) (selEnd := selEnd) es₁ s₁)
    rank pot (Set.Ici selBase)
    (fun st _ _ hrank0 => by
      dsimp only [rank, ftPhaseRank] at hrank0
      by_cases h0 : st.numVertices = 0
      · simp [guard, h0]
      · rw [ite_eq_right h0] at hrank0
        have := Nat.one_le_iterClogBeta ((2 * mRef) / st.numVertices) st.numVertices
        omega)
    (fun st t hinv hg => by
      obtain ⟨hs, hv, hpot, hmod, hinv', hrank, _⟩ :=
        densePhaseLoop_step_spec h16 hn1_le_2m hm₁_le hfit hfit_mRef hinv hg
      exact ⟨hs, hv, by omega, hmod, hinv', hrank⟩)
    n₁ st₀ s₁
    ⟨rfl, rfl, le_rfl, le_rfl, hwf₁, fun _ _ => rfl, Or.inr (by dsimp only [selBase]; omega),
      es₁, le_rfl, rfl, hm₁_le, hin₁', by dsimp only [st₀, s₁, selEnd, selBase]; omega,
      by dsimp only [st₀]; omega, fun L hsub hmsf => by
        dsimp only [st₀]
        exact ⟨L, hsub, (Nat.zero_add L.length).symm, fun _ hj _ => absurd hj (by omega),
          fun j _ _ => by simp, hmsf⟩⟩
    (by
      dsimp only [rank, st₀, ftPhaseRank]
      split_ifs with h0
      · exact Nat.zero_le _
      · exact iterClogBeta_div_le_self (Nat.pos_of_ne_zero h0))
  set resBW := (Memory.spec 0).clientResult s₁ (boundedWhile guard densePhaseStepProg env n₁ st₀)
  set s₂ := (Memory.spec 0).clientState s₁ (boundedWhile guard densePhaseStepProg env n₁ st₀)
  obtain ⟨_, hv_bw, hstop_bw, ⟨_, _, _, ht_fr₂, hwf₂, _, _, esCur, _, _, _, _, _,
    hsel_le₂, hlift₂⟩, hmod_bw, hc_bw⟩ := hbw
  change resBW.selLen + resBW.numVertices ≤ n₁ at hsel_le₂
  change s₂.frontier + ftPhaseRank mRef resBW.numVertices * (76 * mRef) ≤
    s₁.frontier + ftPhaseRank mRef n₁ * (76 * mRef) at ht_fr₂
  change Memory.Modifies (Set.Ici selBase) s₁ s₂ at hmod_bw
  change memoryCost (boundedWhile guard densePhaseStepProg env n₁ st₀) s₁ +
    pot resBW s₂ ≤ pot st₀ s₁ + 0 * rank st₀ s₁ at hc_bw
  have hres1_0 : resBW.numVertices = 0 := by
    have : ¬ 0 < resBW.numVertices := hstop_bw
    omega
  obtain ⟨hesCur_nil, hmsf0'⟩ := empty_isMSF_of_numVertices_zero hres1_0 esCur
  obtain ⟨msf₁, hmsf1_sub, hmsf1_len, hmsf1_ids, _, hmsf1_msf⟩ :=
    hlift₂ [] (hesCur_nil ▸ List.nil_subperm) hmsf0'
  simp only [List.length_nil, Nat.add_zero] at hmsf1_len
  have hr0 : ftPhaseRank mRef resBW.numVertices = 0 := by simp [ftPhaseRank, hres1_0]
  have hcost_bw_bound : memoryCost (boundedWhile guard densePhaseStepProg env n₁ st₀) s₁ ≤
      889 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁ := by
    dsimp only [pot, rank, st₀] at hc_bw ⊢
    rw [hr0, Nat.zero_mul, Nat.add_zero, Nat.zero_mul, Nat.add_zero] at hc_bw
    by_cases h0 : n₁ = 0
    · have hn0 : ftPhaseRank mRef n₁ = 0 := by simp [ftPhaseRank, h0]
      rw [hn0, Nat.zero_mul] at hc_bw
      omega
    · simp only [ftPhaseRank, h0, ↓reduceIte] at hc_bw
      have hcomm : Nat.iterClogBeta ((2 * mRef) / n₁) n₁ * (889 * mRef) =
          889 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁ := by ring
      omega
  have hfr_final :
      s₂.frontier ≤ s.frontier + n₁ + 76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁ := by
    rw [hr0, Nat.zero_mul, Nat.add_zero] at ht_fr₂
    by_cases h0 : n₁ = 0
    · simp only [ftPhaseRank, h0, ↓reduceIte, Nat.zero_mul, Nat.add_zero] at ht_fr₂
      dsimp only [s₁, selEnd, selBase] at ht_fr₂
      omega
    · simp only [ftPhaseRank, h0, ↓reduceIte] at ht_fr₂
      have hcomm : Nat.iterClogBeta ((2 * mRef) / n₁) n₁ * (76 * mRef) =
          76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁ := by ring
      dsimp only [s₁, selEnd, selBase] at ht_fr₂
      omega
  have hbw_ft : Memory.FramedTriple w s₁ (boundedWhile guard densePhaseStepProg env n₁ st₀)
      (889 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁) (Set.Ici selBase)
      fun res s' =>
        res.selLen ≤ n₁ ∧
        s'.frontier ≤ s.frontier + n₁ + 76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁ ∧
        selBase + res.selLen ≤ s'.frontier ∧
        Memory.WellFormed w s' ∧
        ∃ msf₁ : List (IndexedEdge n₁),
          msf₁.Subperm es₁ ∧
          msf₁.length = res.selLen ∧
          (∀ j (_hj : j < res.selLen) (hj' : j < msf₁.length), s'.mem (selBase + j) = msf₁[j].id) ∧
          IsMinSpanningForest (es₁.map IndexedEdge.toWeighted) (msf₁.map IndexedEdge.toWeighted) :=
    framedTriple_iff_realization.mpr ⟨hv_bw, hcost_bw_bound, hmod_bw,
      by dsimp only [resBW] at hsel_le₂; omega, hfr_final,
      by
        have := hmod_bw.1
        dsimp only [resBW, s₂, s₁, selEnd, selBase] at this hsel_le₂ ⊢
        omega,
      hwf₂, msf₁, hmsf1_sub, hmsf1_len, fun j hj hj' => (hmsf1_ids j hj hj').symm, hmsf1_msf⟩
  have hprog : densePhaseLoopProg ⟨n₁, es₁.length, edge₁, mRef⟩ =
      (Memory.allocBlockDirty n₁ >>= fun sel =>
        boundedWhile guard densePhaseStepProg ⟨mRef, sel.base, sel.base + n₁⟩ n₁
          ⟨n₁, es₁.length, edge₁, 0⟩ >>= fun res => pure ⟨sel.base, res.selLen⟩) := rfl
  rw [hprog]
  exact ((Memory.FramedTriple.allocBlockDirty_bind hfit_alloc
    (Memory.FramedTriple.bind_same (c₂ := 0) (hbw_ft.mono le_rfl fun res s' h =>
      Memory.FramedTriple.pure (c := 0) ⟨rfl, h⟩))).frame_empty_of_ge_frontier
    (S := Set.Ici selBase) (fun _ ha => Set.mem_Ici.mp ha)).mono (by omega) fun _ _ h => h

private theorem densePhaseLoop_safe_and_work {w n₁ edge₁ mRef : ℕ}
    {es₁ : List (IndexedEdge n₁)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin₁ : HoldsIndexedEdges edge₁ es₁ s.mem)
    (hin₁_lt : edge₁ + 4 * es₁.length ≤ s.frontier)
    (hm₁_le : es₁.length ≤ mRef)
    (hnoniso₁ : ∀ y : Fin n₁, ∃ e ∈ es₁, e.u = y ∨ e.v = y)
    (hfit : Fits w (s.frontier + (n₁ + 76 * mRef * Nat.iterClogBeta ((2 * mRef) / n₁) n₁)))
    (hfit_mRef : Fits w (2 * mRef + 1)) :
    let selBase := s.frontier
    let selEnd := selBase + n₁
    let s₁ : Memory.State := ⟨s.mem, selEnd⟩
    let env : DensePhaseEnv := ⟨mRef, selBase, selEnd⟩
    let st₀ : DenseLoopState := ⟨n₁, es₁.length, edge₁, 0⟩
    whileSafe (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
      densePhaseStepProg densePhaseStepProgSafe w env n₁ st₀ s₁ ∧
    whileWork (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
      densePhaseStepProg (fun x _ => (2 * (Prod.fst x).mRef) / (Prod.snd x).numVertices + 2)
      env n₁ st₀ s₁ ≤ 20 * mRef + 3 := by
  let selBase := s.frontier
  let selEnd := selBase + n₁
  let s₁ : Memory.State := ⟨s.mem, selEnd⟩
  have hfit_alloc : Fits w selEnd := hfit.of_le (by omega)
  have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit_alloc, hwf.mem_fits⟩
  have hn1_le_2m : n₁ ≤ 2 * es₁.length := card_le_two_mul_of_noIsolated hnoniso₁
  let env : DensePhaseEnv := ⟨mRef, selBase, selEnd⟩
  let st₀ : DenseLoopState := ⟨n₁, es₁.length, edge₁, 0⟩
  have hinv₀ : denseLoopInv (w := w) (mRef := mRef) (selBase := selBase) (selEnd := selEnd)
      es₁ s₁ st₀ s₁ :=
    ⟨rfl, rfl, le_rfl, le_rfl, hwf₁, fun _ _ => rfl, Or.inr (by dsimp only [selBase]; omega),
      es₁, le_rfl, rfl, hm₁_le, hin₁, by dsimp only [st₀, s₁, selEnd, selBase]; omega,
      by dsimp only [st₀]; omega, fun L hsub hmsf => by
        dsimp only [st₀]
        exact ⟨L, hsub, (Nat.zero_add L.length).symm, fun _ hj _ => absurd hj (by omega),
          fun j _ _ => by simp, hmsf⟩⟩
  let guard : DensePhaseEnv → DenseLoopState → Prop := fun _ st => 0 < st.numVertices
  let rank (st : DenseLoopState) (_ : Memory.State) : ℕ := ftPhaseRank mRef st.numVertices
  let pot (st : DenseLoopState) (_ : Memory.State) : ℕ :=
    ftPhaseRank mRef st.numVertices * (889 * mRef)
  have hbw := boundedWhile_potential_spec guard densePhaseStepProg densePhaseStepProgSafe
    w env 0 (denseLoopInv (w := w) (mRef := mRef) (selBase := selBase) (selEnd := selEnd) es₁ s₁)
    rank pot (Set.Ici selBase)
    (fun st _ _ hrank0 => by
      dsimp only [rank, ftPhaseRank] at hrank0
      by_cases h0 : st.numVertices = 0
      · simp [guard, h0]
      · rw [ite_eq_right h0] at hrank0
        have := Nat.one_le_iterClogBeta ((2 * mRef) / st.numVertices) st.numVertices
        omega)
    (fun st t hinv hg => by
      obtain ⟨hs, hv, hpot, hmod, hinv', hrank, _⟩ :=
        densePhaseLoop_step_spec h16 hn1_le_2m hm₁_le hfit hfit_mRef hinv hg
      exact ⟨hs, hv, by omega, hmod, hinv', hrank⟩)
    n₁ st₀ s₁ hinv₀
    (by
      dsimp only [rank, st₀, ftPhaseRank]
      split_ifs with h0
      · exact Nat.zero_le _
      · exact iterClogBeta_div_le_self (Nat.pos_of_ne_zero h0))
  have hwork_le := denseLoop_whileWork_le h16 hn1_le_2m hm₁_le hfit hfit_mRef n₁ st₀ s₁ hinv₀
  have hpot_le : denseWorkPot mRef st₀ ≤ 20 * mRef + 3 := by
    dsimp only [denseWorkPot, st₀]
    by_cases h0 : n₁ = 0
    · simp only [h0, ↓reduceIte, Nat.zero_le]
    · simp only [h0, ↓reduceIte]
      have h2m_pos : 2 * mRef ≠ 0 := by omega
      let k := Nat.log 2 (2 * mRef)
      have hpow_le : 2 ^ k ≤ 2 * mRef := Nat.pow_log_le_self 2 h2m_pos
      have hlt_pow : 2 * mRef < 2 ^ (k + 1) :=
        Nat.lt_pow_succ_log_self (by decide : 1 < 2) (2 * mRef)
      have hn1_pow : n₁ ≤ 2 ^ (k + 1) := by omega
      have hclog : Nat.clog 2 n₁ ≤ k + 1 := (Nat.clog_le_iff_le_pow (by decide)).mpr hn1_pow
      have hiter := Nat.iterClogBeta_le_add_iterClog (k := 1) le_rfl ((2 * mRef) / n₁) n₁
      change Nat.iterClogBeta ((2 * mRef) / n₁) n₁ ≤ 1 + Nat.clog 2 n₁ at hiter
      have hrank_le : ftPhaseRank mRef n₁ ≤ k + 2 := by
        dsimp only [ftPhaseRank]
        rw [ite_eq_right h0]
        omega
      have hmul1 : ftPhaseRank mRef n₁ * (k + 3) ≤ (k + 2) * (k + 3) :=
        Nat.mul_le_mul_right _ hrank_le
      have hsq : (k + 2) * (k + 3) ≤ 9 * 2 ^ k :=
        (by nlinarith : (k + 2) * (k + 3) ≤ (k + 3) ^ 2).trans (sq_add_three_le_nine_mul_pow k)
      change ftPhaseRank mRef n₁ * (k + 3) + (2 * mRef + 3) ≤ 20 * mRef + 3
      omega
  exact ⟨hbw.1, hwork_le.trans hpot_le⟩

private theorem whileWork_dense_eq (mRef sb se : ℕ) :
    ∀ (fuel : ℕ) (st : DenseLoopState) (t : Memory.State),
      whileWork (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
        densePhaseStepProg (fun x _ => (2 * mRef) / x.2.numVertices + 2)
        ⟨mRef, sb, se⟩ fuel st t =
      whileWork (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
        densePhaseStepProg (fun x _ => (2 * x.1.mRef) / x.2.numVertices + 2)
        ⟨mRef, sb, se⟩ fuel st t
  | 0, _, _ => rfl
  | fuel + 1, st, t => by
    simp only [whileWork]
    split_ifs
    · rw [whileWork_dense_eq mRef sb se fuel]
    · rfl

private theorem realizes_densePhaseLoopProg_work : Realizes .exact
    densePhaseLoopProg WordEncoding.encode WordEncoding.encode
    (fun w d s =>
      let selBase := s.frontier
      let s₁ : Memory.State := ⟨s.mem, selBase + d.numVertices⟩
      Fits w 16 ∧ Fits w (selBase + d.numVertices) ∧
      whileSafe (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
        densePhaseStepProg densePhaseStepProgSafe w ⟨d.mRef, selBase, selBase + d.numVertices⟩
        d.numVertices ⟨d.numVertices, d.numEdges, d.edgeBase, 0⟩ s₁)
    (fun d s =>
      let selBase := s.frontier
      let s₁ : Memory.State := ⟨s.mem, selBase + d.numVertices⟩
      whileWork (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
        densePhaseStepProg (fun x _ => (2 * (Prod.fst x).mRef) / (Prod.snd x).numVertices + 2)
        ⟨d.mRef, selBase, selBase + d.numVertices⟩ d.numVertices
        ⟨d.numVertices, d.numEdges, d.edgeBase, 0⟩ s₁) := by
  unfold densePhaseLoopProg
  realize [realizes_allocBlockDirty, realizes_densePhaseStepProg]
  · intro _
    exact whileSafe_imp _ _ (safe := densePhaseStepProgSafe)
      (safe' := fun w x s' =>
        Fits w (((Memory.spec 0).clientResult s (Memory.allocBlockDirty d.numVertices)).base +
          d.numVertices) ∧
        densePhaseStepProgSafe w
          (⟨d.mRef, ((Memory.spec 0).clientResult s (Memory.allocBlockDirty d.numVertices)).base,
            ((Memory.spec 0).clientResult s (Memory.allocBlockDirty d.numVertices)).base +
              d.numVertices⟩, x.2) s')
      (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ _ hs => ⟨h.2.1, hs⟩) h.2.2
  · exact (whileWork_dense_eq d.mRef s.frontier (s.frontier + d.numVertices) d.numVertices
      ⟨d.numVertices, d.numEdges, d.edgeBase, 0⟩
      ((Memory.spec 0).clientState s (Memory.allocBlockDirty d.numVertices))).le

/-! ## Top-Level Fredman–Tarjan MSF Driver (`denseCaseProg`) -/

/-- Fredman–Tarjan bounded-heap minimum spanning forest algorithm ([FredmanTarjan1987],
[PettieRamachandran2002] Section 2.3) over `GraphSlice`: preprocesses edges (local retag,
deduplication, isolated-vertex compaction), executes `O(iterClogBeta (2 * m / n) n)` bounded-heap
contraction phases, and emits the selected original `IndexedEdge` records as a `GraphSlice`. -/
def denseCaseProg (g : GraphSlice) : Memory.Prog GraphSlice := do
  let pre ← densePreprocessProg g
  let sel ← densePhaseLoopProg ⟨pre.numVertices, pre.numEdges, pre.edgeBase, g.numEdges⟩
  let outBase ← emitIndexedEdgesFromIdxs ⟨g.edgeBase, sel.selBufBase, sel.selLen⟩
  pure ⟨g.numVertices, sel.selLen, outBase⟩

private theorem denseCase_safe_and_work {w : ℕ} {g : GraphSlice} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin_lt : g.edgeBase + 4 * g.numEdges ≤ s.frontier)
    (hfit : Fits w (s.frontier + (21 * g.numEdges + 8 * g.numVertices +
      76 * g.numEdges * Nat.iterClogBeta ((2 * g.numEdges) / g.numVertices) g.numVertices + 3)))
    (hedges : ∀ j < g.numEdges,
      s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
      s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) :
    let pre := (Memory.spec 0).clientResult s (densePreprocessProg g)
    let s₁ := (Memory.spec 0).clientState s (densePreprocessProg g)
    let sel := (Memory.spec 0).clientResult s₁
      (densePhaseLoopProg ⟨pre.numVertices, pre.numEdges, pre.edgeBase, g.numEdges⟩)
    let s₂ := (Memory.spec 0).clientState s₁
      (densePhaseLoopProg ⟨pre.numVertices, pre.numEdges, pre.edgeBase, g.numEdges⟩)
    (Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (21 * g.numEdges + 3 * g.numVertices + 3)) ∧
      (∀ j < g.numEdges,
        s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) ∧
      Fits w (s₁.frontier + pre.numVertices) ∧
      whileSafe (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
        densePhaseStepProg densePhaseStepProgSafe w
        ⟨g.numEdges, s₁.frontier, s₁.frontier + pre.numVertices⟩
        pre.numVertices ⟨pre.numVertices, pre.numEdges, pre.edgeBase, 0⟩
        ⟨s₁.mem, s₁.frontier + pre.numVertices⟩ ∧
      sel.selBufBase + sel.selLen ≤ s₂.frontier ∧
      Fits w (s₂.frontier + 4 * sel.selLen) ∧
      ∀ j < sel.selLen, g.edgeBase + 4 * s₂.mem (sel.selBufBase + j) + 4 ≤ s₂.frontier) ∧
    whileWork (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
      densePhaseStepProg (fun x _ => (2 * (Prod.fst x).mRef) / (Prod.snd x).numVertices + 2)
      ⟨g.numEdges, s₁.frontier, s₁.frontier + pre.numVertices⟩
      pre.numVertices ⟨pre.numVertices, pre.numEdges, pre.edgeBase, 0⟩
      ⟨s₁.mem, s₁.frontier + pre.numVertices⟩ ≤ 20 * g.numEdges + 3 := by
  rcases g with ⟨n, m, eb⟩; dsimp only at *
  obtain ⟨es, hes_len, hin⟩ := exists_indexedEdges_of_mem_lt hedges
  have h1_ft := densePreprocessProg_spec h16 hwf hin (by rw [hes_len]; exact hin_lt)
    (by rw [hes_len]; exact hfit.of_le (by omega))
  rw [show (⟨n, es.length, eb⟩ : GraphSlice) = ⟨n, m, eb⟩ from by rw [hes_len]] at h1_ft
  set pre := (Memory.spec 0).clientResult s (densePreprocessProg ⟨n, m, eb⟩)
  set s₁ := (Memory.spec 0).clientState s (densePreprocessProg ⟨n, m, eb⟩)
  obtain ⟨_, _, hmod₁, hfr₁, hres_fr₁, hpre_nv, hpre_ne, hwf₁,
    esOut, hesOut_len, hesOut_holds, hnoniso₁, hlift₁⟩ :=
    framedTriple_iff_realization.mp h1_ft
  change s₁.frontier ≤ s.frontier + (21 * es.length + 3 * n) at hfr₁
  change pre.edgeBase + 4 * pre.numEdges ≤ s₁.frontier at hres_fr₁
  change pre.numVertices ≤ n at hpre_nv
  change pre.numEdges ≤ es.length at hpre_ne
  change Memory.WellFormed w s₁ at hwf₁
  have hpre_ne_m : pre.numEdges ≤ m := hpre_ne.trans_eq hes_len
  have hbeta_le : Nat.iterClogBeta ((2 * m) / pre.numVertices) pre.numVertices ≤
      Nat.iterClogBeta ((2 * m) / n) n :=
    Nat.iterClogBeta_div_mono_right (2 * m) hpre_nv
  have hmul_beta : 76 * m * Nat.iterClogBeta ((2 * m) / pre.numVertices) pre.numVertices ≤
      76 * m * Nat.iterClogBeta ((2 * m) / n) n :=
    Nat.mul_le_mul_left _ hbeta_le
  have hfit_loop : Fits w (s₁.frontier + (pre.numVertices +
      76 * m * Nat.iterClogBeta ((2 * m) / pre.numVertices) pre.numVertices)) :=
    hfit.of_le (by omega)
  have hfit_mRef : Fits w (2 * m + 1) := hfit.of_le (by omega)
  have hloop_sw := densePhaseLoop_safe_and_work (mRef := m) h16 hwf₁ hesOut_holds
    (by rw [hesOut_len]; exact hres_fr₁) (by rw [hesOut_len]; exact hpre_ne_m)
    hnoniso₁ hfit_loop hfit_mRef
  dsimp only at hloop_sw
  rw [hesOut_len] at hloop_sw
  have h2_ft := densePhaseLoopProg_spec (mRef := m) h16 hwf₁ hesOut_holds
    (by rw [hesOut_len]; exact hres_fr₁) (by rw [hesOut_len]; exact hpre_ne_m)
    hnoniso₁ hfit_loop hfit_mRef
  rw [show (⟨pre.numVertices, esOut.length, pre.edgeBase, m⟩ : DenseLoopInit) =
    ⟨pre.numVertices, pre.numEdges, pre.edgeBase, m⟩ from by rw [hesOut_len]] at h2_ft
  set sel := (Memory.spec 0).clientResult s₁
    (densePhaseLoopProg ⟨pre.numVertices, pre.numEdges, pre.edgeBase, m⟩)
  set s₂ := (Memory.spec 0).clientState s₁
    (densePhaseLoopProg ⟨pre.numVertices, pre.numEdges, pre.edgeBase, m⟩)
  obtain ⟨_, _, hmod₂, _, hsel_len_le, hfr₂, hsel_fr₂, _,
    msf₁, hmsf1_sub, hmsf1_len, hmsf1_buf, hmsf1_msf⟩ :=
    framedTriple_iff_realization.mp h2_ft
  change Memory.Modifies ∅ s₁ s₂ at hmod₂
  change sel.selLen ≤ pre.numVertices at hsel_len_le
  change s₂.frontier ≤ s₁.frontier + pre.numVertices +
    76 * m * Nat.iterClogBeta ((2 * m) / pre.numVertices) pre.numVertices at hfr₂
  change sel.selBufBase + sel.selLen ≤ s₂.frontier at hsel_fr₂
  obtain ⟨msfEs, _, hmsf_len, hmsf_get, _⟩ := hlift₁ msf₁ hmsf1_sub hmsf1_msf
  have hfit_emit : Fits w (s₂.frontier + 4 * sel.selLen) := by
    have : sel.selLen ≤ n := hsel_len_le.trans hpre_nv
    exact hfit.of_le (by omega)
  refine ⟨⟨h16, hin_lt, hfit.of_le (by omega), hedges, hfit_loop.of_le (by omega), hloop_sw.1,
    hsel_fr₂, hfit_emit, fun j hj => ?_⟩, hloop_sw.2⟩
  have hj1 : j < msf₁.length := hmsf1_len ▸ hj
  have hj2 : j < msfEs.length := hmsf_len ▸ hj1
  obtain ⟨hid_lt, _⟩ := hmsf_get j hj1 hj2
  rw [hmsf1_buf j hj hj1]
  have hfr_le : s.frontier ≤ s₂.frontier := (hmod₁.1).trans hmod₂.1
  omega

/-- Uniform `Realizes .exact` realization of `denseCaseProg` (`work = 0`), running in
`O(memoryCost + 1)` Word-RAM register instructions. -/
theorem realizes_denseCaseProg : Realizes .exact
    denseCaseProg WordEncoding.encode WordEncoding.encode
    (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
      Fits w (s.frontier + (21 * g.numEdges + 8 * g.numVertices +
        76 * g.numEdges * Nat.iterClogBeta ((2 * g.numEdges) / g.numVertices) g.numVertices + 3)) ∧
      ∀ j < g.numEdges,
        s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
        s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
    (fun _ _ => 0) := by
  have hraw : Realizes .exact denseCaseProg WordEncoding.encode WordEncoding.encode
      (fun w g s =>
        let pre := (Memory.spec 0).clientResult s (densePreprocessProg g)
        let s₁ := (Memory.spec 0).clientState s (densePreprocessProg g)
        let sel := (Memory.spec 0).clientResult s₁
          (densePhaseLoopProg ⟨pre.numVertices, pre.numEdges, pre.edgeBase, g.numEdges⟩)
        let s₂ := (Memory.spec 0).clientState s₁
          (densePhaseLoopProg ⟨pre.numVertices, pre.numEdges, pre.edgeBase, g.numEdges⟩)
        Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (21 * g.numEdges + 3 * g.numVertices + 3)) ∧
        (∀ j < g.numEdges,
          s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices) ∧
        Fits w (s₁.frontier + pre.numVertices) ∧
        whileSafe (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
          densePhaseStepProg densePhaseStepProgSafe w
          ⟨g.numEdges, s₁.frontier, s₁.frontier + pre.numVertices⟩
          pre.numVertices ⟨pre.numVertices, pre.numEdges, pre.edgeBase, 0⟩
          ⟨s₁.mem, s₁.frontier + pre.numVertices⟩ ∧
        sel.selBufBase + sel.selLen ≤ s₂.frontier ∧
        Fits w (s₂.frontier + 4 * sel.selLen) ∧
        ∀ j < sel.selLen, g.edgeBase + 4 * s₂.mem (sel.selBufBase + j) + 4 ≤ s₂.frontier)
      (fun g s =>
        let pre := (Memory.spec 0).clientResult s (densePreprocessProg g)
        let s₁ := (Memory.spec 0).clientState s (densePreprocessProg g)
        whileWork (fun (_ : DensePhaseEnv) (st : DenseLoopState) => 0 < st.numVertices)
          densePhaseStepProg (fun x _ => (2 * (Prod.fst x).mRef) / (Prod.snd x).numVertices + 2)
          ⟨g.numEdges, s₁.frontier, s₁.frontier + pre.numVertices⟩
          pre.numVertices ⟨pre.numVertices, pre.numEdges, pre.edgeBase, 0⟩
          ⟨s₁.mem, s₁.frontier + pre.numVertices⟩) := by
    unfold denseCaseProg
    realize [realizes_densePreprocessProg, realizes_densePhaseLoopProg_work,
      realizes_emitIndexedEdgesFromIdxs]
    · exact h.1
    · exact h.2.1
    · exact h.2.2.1
    · exact h.2.2.2.1
    · exact h.2.2.2.2.1
    · exact h.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.2.1
    · exact h.2.2.2.2.2.2.2.2
  have hcons : Realizes .exact denseCaseProg WordEncoding.encode WordEncoding.encode
      (fun w g s => Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
        Fits w (s.frontier + (21 * g.numEdges + 8 * g.numVertices +
          76 * g.numEdges * Nat.iterClogBeta ((2 * g.numEdges) / g.numVertices) g.numVertices +
            3)) ∧
        ∀ j < g.numEdges,
          s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
          s.mem (g.edgeBase + 4 * j + 1) < g.numVertices)
      (fun g s => 3 * memoryCost (denseCaseProg g) s) := by
    refine hraw.consequence_work
      (fun _ _ _ _ hmem _ ⟨h16, hin_lt, hfit, hedges⟩ =>
        (denseCase_safe_and_work h16 hmem hin_lt hfit hedges).1)
      (fun _ g s _ hmem _ ⟨h16, hin_lt, hfit, hedges⟩ => by
        have hwork_bw := (denseCase_safe_and_work h16 hmem hin_lt hfit hedges).2
        have hcost_pre := densePreprocessProg_cost_lower g s
        have hcost_le : memoryCost (densePreprocessProg g) s ≤
            memoryCost (denseCaseProg g) s := by
          have hprog_dc : denseCaseProg g =
              (densePreprocessProg g >>= fun p =>
                densePhaseLoopProg ⟨p.numVertices, p.numEdges, p.edgeBase, g.numEdges⟩ >>= fun sl =>
                emitIndexedEdgesFromIdxs ⟨g.edgeBase, sl.selBufBase, sl.selLen⟩ >>= fun ob =>
                pure ⟨g.numVertices, sl.selLen, ob⟩) := rfl
          rw [hprog_dc, memoryCost_bind']
          omega
        dsimp only
        omega)
  refine hcons.mono_mul 3 fun g s => by omega

/-- Framed specification for `denseCaseProg` over an arbitrary input multigraph `es`
(`HoldsIndexedEdges edgeBase es s.mem`): computes a minimum spanning forest `msfEs`
(`msfEs.Subperm es`) in `O(m * Nat.iterClogBeta (2 * m / n) n + n)` memory operations while leaving
cells below `s.frontier` untouched. -/
theorem denseCaseProg_spec {w n edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (21 * es.length + 8 * n +
      76 * es.length * Nat.iterClogBeta ((2 * es.length) / n) n + 3))) :
    Memory.FramedTriple w s (denseCaseProg ⟨n, es.length, edgeBase⟩)
      (62 * es.length + 18 * n + 889 * es.length * Nat.iterClogBeta ((2 * es.length) / n) n + 11)
      ∅ fun res s' =>
        res.numVertices = n ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (21 * es.length + 8 * n +
          76 * es.length * Nat.iterClogBeta ((2 * es.length) / n) n + 3) ∧
        Memory.WellFormed w s' ∧
        ∃ msfEs : List (IndexedEdge n),
          msfEs.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase msfEs s'.mem ∧
          msfEs.Subperm es ∧
          IsMinSpanningForest (es.map IndexedEdge.toWeighted)
            (msfEs.map IndexedEdge.toWeighted) := by
  dsimp only [denseCaseProg]
  refine (Memory.FramedTriple.bind_same
    (c₂ := (1 + 889 * es.length * Nat.iterClogBeta ((2 * es.length) / n) n) + (9 * n + 1))
    (Memory.FramedTriple.mono (Memory.Triple.mono (holdsIndexedEdges_frame_mem
      (densePreprocessProg_spec h16 hwf hin hin_lt (hfit.of_le (by omega)))
      hin (Set.empty_disjoint _) hin_lt) le_rfl fun _ _ h =>
        And.intro h.1 (And.intro h.1 h.2)) le_rfl
      fun pre s₁ ⟨hmod₁, ⟨hfr₁, hres_fr₁, hpre1_le, hpre2_le, hwf₁,
        esOut, hesOut_len, hesOut_holds, hnoniso₁, hlift₁⟩, hin₁⟩ => ?_)).mono
    (by omega) fun _ _ h => h
  have hbeta_le : Nat.iterClogBeta ((2 * es.length) / pre.numVertices) pre.numVertices ≤
      Nat.iterClogBeta ((2 * es.length) / n) n :=
    Nat.iterClogBeta_div_mono_right (2 * es.length) hpre1_le
  have hmul76 : 76 * es.length *
      Nat.iterClogBeta ((2 * es.length) / pre.numVertices) pre.numVertices ≤
      76 * es.length * Nat.iterClogBeta ((2 * es.length) / n) n :=
    Nat.mul_le_mul_left _ hbeta_le
  have hmul889 : 889 * es.length *
      Nat.iterClogBeta ((2 * es.length) / pre.numVertices) pre.numVertices ≤
      889 * es.length * Nat.iterClogBeta ((2 * es.length) / n) n :=
    Nat.mul_le_mul_left _ hbeta_le
  have hfit_loop : Fits w (s₁.frontier + (pre.numVertices + 76 * es.length *
      Nat.iterClogBeta ((2 * es.length) / pre.numVertices) pre.numVertices)) :=
    hfit.of_le (by omega)
  have hfit_mRef : Fits w (2 * es.length + 1) := hfit.of_le (by omega)
  have h2 := densePhaseLoopProg_spec (mRef := es.length) h16 hwf₁ hesOut_holds
    (by rw [hesOut_len]; exact hres_fr₁) (by rw [hesOut_len]; exact hpre2_le) hnoniso₁
    hfit_loop hfit_mRef
  rw [show (⟨pre.numVertices, esOut.length, pre.edgeBase, es.length⟩ : DenseLoopInit) =
    ⟨pre.numVertices, pre.numEdges, pre.edgeBase, es.length⟩ from by rw [hesOut_len]] at h2
  have hin₁_lt : edgeBase + 4 * es.length ≤ s₁.frontier := by have := hmod₁.1; omega
  refine (Memory.FramedTriple.bind_same (c₁ := 1 + 889 * es.length *
      Nat.iterClogBeta ((2 * es.length) / n) n) (c₂ := 9 * n + 1)
    (Memory.FramedTriple.mono (Memory.Triple.mono (holdsIndexedEdges_frame_mem h2 hin₁
      (Set.empty_disjoint _) hin₁_lt) le_rfl fun _ _ h => And.intro h.1 (And.intro h.1 h.2))
      (by omega) fun sel s₂ ⟨hmod₂, ⟨hsel1_eq, hsel2_le, hfr₂, hsel_fr₂, hwf₂,
        msf₁, hmsf1_sub, hmsf1_len, hmsf1_buf, hmsf1_msf⟩, hin₂⟩ => ?_)).mono
    (by omega) fun _ _ h => h
  obtain ⟨msfEs, hmsf_sub, hmsf_len, hmsf_get, hmsf_msf⟩ := hlift₁ msf₁ hmsf1_sub hmsf1_msf
  let idxs : List (Fin es.length) := (List.finRange sel.selLen).map fun j =>
    ⟨(msf₁[j.val]'(by omega)).id, (hmsf_get j.val (by omega) (by omega)).choose⟩
  have hidxs_len : idxs.length = sel.selLen := by simp [idxs]
  have hsel_idxs : ∀ j (hj : j < idxs.length), s₂.mem (sel.selBufBase + j) = idxs[j].val := by
    intro j hj
    have hj2 : j < sel.selLen := hidxs_len ▸ hj
    dsimp only [idxs]
    rw [List.getElem_map, List.getElem_finRange]
    exact hmsf1_buf j hj2 (by omega)
  have hin₂_lt : edgeBase + 4 * es.length ≤ s₂.frontier := by have := hmod₂.1; omega
  have hsel_le_n : sel.selLen ≤ n := hsel2_le.trans hpre1_le
  have hfit_emit : Fits w (s₂.frontier + 4 * sel.selLen) := hfit.of_le (by omega)
  have h3 := emitIndexedEdgesFromIdxs_spec (d := ⟨edgeBase, sel.selBufBase, sel.selLen⟩)
    (es := es) (idxs := idxs) (s := s₂) h16 hwf₂ hin₂ hin₂_lt hsel_idxs hsel_fr₂ hidxs_len.symm
    hfit_emit
  have hmsf_eq_map : idxs.map (fun i => es[i.val]) = msfEs := by
    apply List.ext_getElem
    · simp only [List.length_map, hidxs_len, hmsf_len, hmsf1_len]
    · intro j hj1 hj2
      have hjL : j < msf₁.length := by simpa [hmsf_len] using hj2
      have hj_id : j < idxs.length := by simpa only [List.length_map] using hj1
      have hid_eq : idxs[j].val = msf₁[j].id := by simp [idxs]
      simp only [List.getElem_map]
      simpa only [hid_eq] using (hmsf_get j hjL hj2).choose_spec.symm
  rw [hmsf_eq_map] at h3
  have hs_le_s2 : s.frontier ≤ s₂.frontier := hmod₁.1.trans hmod₂.1
  refine (Memory.FramedTriple.bind_same (c₁ := 9 * n + 1) (c₂ := 0)
    (h3.mono (by dsimp only; omega) fun outBase s₃ ⟨hout_eq, hfr₃, hwf₃, hholds₃⟩ => by
      dsimp only at hout_eq hfr₃
      exact Memory.FramedTriple.pure (c := 0) ⟨rfl, hout_eq ▸ hs_le_s2,
        by dsimp only; rw [hfr₃]; omega, by rw [hfr₃]; omega, hwf₃, msfEs,
        by rw [hmsf_len, hmsf1_len], hholds₃, hmsf_sub, hmsf_msf⟩)).mono
    (by omega) fun _ _ h => h

/-- Linear-time [PettieRamachandran2002] Section 2.3 dense-case specification for
`denseCaseProg`: when `n ≤ n₀` and `n * max 1 (Nat.iterLog 3 n₀) ≤ 2 * es.length`, `denseCaseProg`
computes a minimum spanning forest in `O(m + n)` memory operations (`≤ 39178 * m + 18 * n + 11`). -/
theorem denseCaseProg_spec_of_dense {w n n₀ edgeBase : ℕ} {es : List (IndexedEdge n)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn_le : n ≤ n₀)
    (hdense : n * max 1 (Nat.iterLog 3 n₀) ≤ 2 * es.length)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hin_lt : edgeBase + 4 * es.length ≤ s.frontier)
    (hfit : Fits w (s.frontier + (3365 * es.length + 8 * n + 3))) :
    Memory.FramedTriple w s (denseCaseProg ⟨n, es.length, edgeBase⟩)
      (39178 * es.length + 18 * n + 11) ∅ fun res s' =>
        res.numVertices = n ∧
        s.frontier ≤ res.edgeBase ∧
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (3365 * es.length + 8 * n + 3) ∧
        Memory.WellFormed w s' ∧
        ∃ msfEs : List (IndexedEdge n),
          msfEs.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase msfEs s'.mem ∧
          msfEs.Subperm es ∧
          IsMinSpanningForest (es.map IndexedEdge.toWeighted)
            (msfEs.map IndexedEdge.toWeighted) := by
  have hiter_mono : Nat.iterLog 3 n ≤ Nat.iterLog 3 n₀ := Nat.iterLog_mono 3 hn_le
  have hmax_le : max 1 (Nat.iterLog 3 n) ≤ max 1 (Nat.iterLog 3 n₀) :=
    max_le_max le_rfl hiter_mono
  have hmul_iter : n * max 1 (Nat.iterLog 3 n) ≤ 2 * es.length :=
    (Nat.mul_le_mul_left n hmax_le).trans hdense
  have hft : es.length * Nat.iterClogBeta ((2 * es.length) / n) n ≤ 44 * es.length := by
    have h := Nat.mul_iterClogBeta_div_le_iterLog (by decide : 1 ≤ 3) es.length n
    rw [Nat.mul_assoc] at h
    omega
  refine (denseCaseProg_spec h16 hwf hin hin_lt (hfit.of_le (by nlinarith))).mono
    (by nlinarith) fun res s' ⟨hnv, hge, hed_fr, hfr_le, hwf', hmsf⟩ =>
      ⟨hnv, hge, hed_fr, hfr_le.trans (by nlinarith), hwf', hmsf⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase
