/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.Scan
public import CslibFrontier.Foundations.Data.Nat.IterLog
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.ValidProg
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

/-!
# Fredman–Tarjan Bounded-Heap Phase Driver and Phase-Rank Decrease

Implements and verifies a single bounded-heap contraction phase step (`ftPhaseProg`) and its
`Nat.iterClogBeta` phase-rank decrease (`ftPhase_rank_lt_of_shrink`) atop `DenseCase/Scan`,
formalizing the inner phase of `[FredmanTarjan1987]` (Section 3, "Minimum Spanning Trees",
pp. 605–607) as structured for `[PettieRamachandran2002]` (Section 3.4, `DenseCase`) toward
issue `#8624`.

## Source Mapping and Single-Phase Scope

* **Single-phase scope (`#8624`)**: `ftPhaseProg` implements one bounded-heap contraction phase
  from a caller-supplied `HoldsIndexedEdges` and `HoldsUndirCSR` layout; inter-phase contraction,
  deduplication, isolated-vertex compaction, and the full multi-phase `O(m β(m, n))` `DenseCase`
  driver compose with `GraphOps.{Components, Dedup}` in follow-up modules under `#8624`.
* **Parameters, model, and multigraphs**: `mRef` supplies the outer reference edge count with
  word-safe clamped heap-size threshold `min n (2 ^ ((2 * mRef) / n))` (`memoryCost` bounded by
  `234 * es.length + 156 * n + 184 * mRef + 7` and uniform `Program .standard` register work at
  most `(2 * mRef) / n + 2`), and `es : List (IndexedEdge n)` admits disconnected multigraphs
  with self-loops, parallel edges, and duplicate `ℕ` weights.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ftPhaseProg`: full bounded-heap
  contraction phase as a `Memory.Prog FTPhaseOut`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ftPhaseProgSafe`: word-width safety
  precondition for `ftPhaseProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ftPhaseRank`: potential rank
  `Nat.iterClogBeta ((2 * mRef) / nCur) nCur` measuring remaining contraction phases.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.realizes_ftPhaseProg`: `Realizes .exact`
  witness with `work ≤ (2 * args.mRef) / args.n + 2`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ftPhaseProg_spec`: correctness,
  framing, and `memoryCost ≤ 234 * es.length + 156 * n + 184 * mRef + 7`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.ftPhase_rank_lt_of_shrink`: strict
  phase-rank drop across surviving non-isolated supervertices.

## References

* `[FredmanTarjan1987]`: Michael L. Fredman and Robert Endre Tarjan, "Fibonacci Heaps and Their Uses
  in Improved Network Optimization Algorithms", *JACM* 34(3), 1987, Section 3 ("Minimum Spanning
  Trees"), pp. 605–607.
* `[PettieRamachandran2002]`: Seth Pettie and Vijaya Ramachandran, "An Optimal Minimum Spanning
  Tree Algorithm", *JACM* 49(1), 2002, Section 3.4 (`DenseCase`).
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.FibonacciHeap
open Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.MinimumSpanningForest
open Cslib.Query.MinimumSpanningForest

/-! ## Private Inner Driver Sub-Programs and Word-Encoded Arguments -/

private structure FTAuxEnv where
  auxBase : ℕ
  n : ℕ

private word_enc_structure encFTAuxEnv : FTAuxEnv where
  auxBase : wordWords,
  n : wordWords

private instance : WordEncoding FTAuxEnv := ⟨2, encFTAuxEnv⟩

private structure FTPhaseIterAcc where
  sLim : ℕ
  nComp : ℕ
  selLen : ℕ

private word_enc_structure encFTPhaseIterAcc : FTPhaseIterAcc where
  sLim : wordWords,
  nComp : wordWords,
  selLen : wordWords

private instance : WordEncoding FTPhaseIterAcc := ⟨3, encFTPhaseIterAcc⟩

private structure FTPhaseBodyArgs where
  ctx : FTCtx
  selLen : ℕ

private word_enc_structure encFTPhaseBodyArgs : FTPhaseBodyArgs where
  ctx : encFTCtx,
  selLen : wordWords

private instance : WordEncoding FTPhaseBodyArgs := ⟨10, encFTPhaseBodyArgs⟩

private def ftInitTrStep (d : FTAuxEnv × ℕ) : Memory.Prog ℕ := do
  Memory.write (d.1.auxBase + d.2) d.1.n
  pure (d.2 + 1)

private def ftInitTrStepSafe (w : ℕ) (d : FTAuxEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.1.auxBase + d.1.n) ∧ Fits w d.1.n ∧ Fits w (d.2 + 1) ∧
    d.1.auxBase + d.2 < s.frontier

private theorem realizes_ftInitTrStep : Realizes .exact
    ftInitTrStep (appendWords encFTAuxEnv wordWords) wordWords ftInitTrStepSafe
    (fun _ _ => 0) := by
  unfold ftInitTrStep
  realize
  all_goals
    rcases h with ⟨h16, haux, hn, hs1, hfr⟩
    have hfront := hmem.frontier_fits
    fits

private def ftTreeStep (d : FTCtx × FTPhaseIterAcc) : Memory.Prog FTPhaseIterAcc := do
  let trS ← Memory.read (d.1.auxBase + d.2.sLim)
  if trS < d.1.n then
    pure ⟨d.2.sLim + 1, d.2.nComp, d.2.selLen⟩
  else do
    let res ← ftRunTree ⟨d.1, d.2.sLim, d.2.nComp, d.2.selLen⟩
    pure ⟨d.2.sLim + 1, res.1, res.2⟩

private def ftTreeStepSafe (w : ℕ) (d : FTCtx × FTPhaseIterAcc) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.1.auxBase + 5 * d.1.n) ∧ Fits w (d.2.sLim + 1) ∧
    d.2.sLim < d.1.n ∧ d.1.auxBase + 5 * d.1.n ≤ s.frontier ∧
    (¬(s.mem (d.1.auxBase + d.2.sLim) < d.1.n) →
      ftRunTreeSafe w ⟨d.1, d.2.sLim, d.2.nComp, d.2.selLen⟩ s)

private theorem realizes_ftTreeStep : Realizes .exact
    ftTreeStep (appendWords encFTCtx encFTPhaseIterAcc) encFTPhaseIterAcc
    ftTreeStepSafe (fun _ _ => 0) := by
  unfold ftTreeStep
  realize [realizes_ftRunTree]
  all_goals
    rcases h with ⟨h16, haux, hs1, hs, haux_fr, hrun⟩
    have hfront := hmem.frontier_fits
    first
    | exact hrun (by assumption)
    | fits

private def ftWriteCompStep (d : FTAuxEnv × ℕ) : Memory.Prog ℕ := do
  let trV ← Memory.read (d.1.auxBase + d.2)
  let supV ← Memory.read (d.1.auxBase + 2 * d.1.n + trV)
  Memory.write (d.1.auxBase + 3 * d.1.n + d.2) supV
  pure (d.2 + 1)

private def ftWriteCompStepSafe (w : ℕ) (d : FTAuxEnv × ℕ) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.1.auxBase + 4 * d.1.n) ∧ Fits w (d.2 + 1) ∧
    d.2 < d.1.n ∧ d.1.auxBase + 4 * d.1.n ≤ s.frontier ∧ s.mem (d.1.auxBase + d.2) < d.1.n

private theorem realizes_ftWriteCompStep : Realizes .exact
    ftWriteCompStep (appendWords encFTAuxEnv wordWords) wordWords ftWriteCompStepSafe
    (fun _ _ => 0) := by
  unfold ftWriteCompStep
  realize
  all_goals
    rcases h with ⟨h16, haux, hv1, hv, hfr, htr⟩
    have hfront := hmem.frontier_fits
    fits

private def ftPhaseBody (d : FTPhaseBodyArgs) : Memory.Prog FTPhaseOut := do
  let _ ← iterate ftInitTrStep ⟨d.ctx.auxBase, d.ctx.n⟩ d.ctx.n 0
  let res ← iterate ftTreeStep d.ctx d.ctx.n ⟨0, 0, d.selLen⟩
  let _ ← iterate ftWriteCompStep ⟨d.ctx.auxBase, d.ctx.n⟩ d.ctx.n 0
  pure ⟨res.nComp, d.ctx.auxBase + 3 * d.ctx.n, res.selLen⟩

private def ftPhaseBodySafe (w : ℕ) (d : FTPhaseBodyArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (d.ctx.auxBase + 4 * d.ctx.n) ∧ Fits w (d.ctx.n + 1) ∧ Fits w d.selLen ∧
    iterationSafe ftInitTrStep ftInitTrStepSafe w ⟨d.ctx.auxBase, d.ctx.n⟩ d.ctx.n 0 s ∧
    let s₁ := (Memory.spec 0).clientState s
      (iterate ftInitTrStep ⟨d.ctx.auxBase, d.ctx.n⟩ d.ctx.n 0)
    iterationSafe ftTreeStep ftTreeStepSafe w d.ctx d.ctx.n ⟨0, 0, d.selLen⟩ s₁ ∧
    let s₂ := (Memory.spec 0).clientState s₁
      (iterate ftTreeStep d.ctx d.ctx.n ⟨0, 0, d.selLen⟩)
    iterationSafe ftWriteCompStep ftWriteCompStepSafe w ⟨d.ctx.auxBase, d.ctx.n⟩ d.ctx.n 0 s₂

private theorem realizes_ftPhaseBody : Realizes .exact
    ftPhaseBody WordEncoding.encode WordEncoding.encode ftPhaseBodySafe (fun _ _ => 0) := by
  unfold ftPhaseBody
  realize [realizes_ftInitTrStep, realizes_ftTreeStep, realizes_ftWriteCompStep]
  all_goals
    rcases h with ⟨h16, haux, hn1, hsl, hi1, hi2, hi3⟩
    first
    | exact iterationSafe_imp hi1 (fun _ => rfl) (fun _ _ hs => hs)
    | exact iterationSafe_imp hi2 (fun _ => rfl) (fun _ _ hs => hs)
    | exact iterationSafe_imp hi3 (fun _ => rfl) (fun _ _ hs => hs)
    | fits

/-! ## Public Phase Program and Realization -/

/-- Allocates heap and scratch space, computes `K_p`, and runs the bounded-heap contraction
phase for `args`, returning `FTPhaseOut` (`nComp`, `compBase`, `selLen'`). -/
def ftPhaseProg (args : FTPhaseArgs) : Memory.Prog FTPhaseOut := do
  let fhBase ← allocProg args.n
  let auxBase ← Memory.alloc (5 * args.n)
  let thresh ← (fun d : ℕ × ℕ => computeThreshProg d.1 d.2) (args.n, args.mRef)
  ftPhaseBody ⟨⟨args.n, args.m, args.edgeBase, args.offBase, args.adjBase,
    fhBase, auxBase, args.selBufBase, thresh⟩, args.selLen⟩

/-- Native safety domain for `ftPhaseProg`. -/
def ftPhaseProgSafe (w : ℕ) (args : FTPhaseArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (s.frontier + (14 * args.n + 5)) ∧
    let fhBase := (Memory.spec 0).clientResult s (allocProg args.n)
    let s₁ := (Memory.spec 0).clientState s (allocProg args.n)
    let auxBase := (Memory.spec 0).clientResult s₁ (Memory.alloc (5 * args.n))
    let s₂ := (Memory.spec 0).clientState s₁ (Memory.alloc (5 * args.n))
    computeThreshProgSafe w (args.n, args.mRef) s₂ ∧
    let thresh := (Memory.spec 0).clientResult s₂ (computeThreshProg args.n args.mRef)
    let s₃ := (Memory.spec 0).clientState s₂ (computeThreshProg args.n args.mRef)
    ftPhaseBodySafe w ⟨⟨args.n, args.m, args.edgeBase, args.offBase, args.adjBase,
      fhBase, auxBase, args.selBufBase, thresh⟩, args.selLen⟩ s₃

/-- Uniform exact-basis realization of `ftPhaseProg` (`work ≤ (2 * args.mRef) / args.n + 2`). -/
theorem realizes_ftPhaseProg : Realizes .exact
    ftPhaseProg WordEncoding.encode WordEncoding.encode ftPhaseProgSafe
    (fun args _ => (2 * args.mRef) / args.n + 2) := by
  have five (k : ℕ) : k + k + k + k + k = 5 * k := by omega
  realize [realizes_allocProg, realizes_computeThreshProg, realizes_ftPhaseBody]
    rewriting [ftPhaseProg, ← five]
  all_goals
    rcases h with ⟨h16, hfr, hct, hbody⟩
    dsimp only at hct hbody
    have h5 : d.n + d.n + d.n + d.n + d.n = 5 * d.n := by omega
    first
    | exact hfr.of_le (by omega)
    | (simp only [h5]; first | exact hct | exact hbody)

/-! ## Sub-Program Specifications -/

private theorem ftTreeStep_spec {w n K mRef : ℕ} {ctx : FTCtx} {es : List (IndexedEdge n)}
    {t : Fin n} {nComp selLen0 : ℕ} {selIdxs0 : List (Fin es.length)} {s : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s) (hwf : Memory.WellFormed w s)
    (hfh_inv : (framed hs.hn hs.hK ctx.fhBase).inv s)
    (hfh_empty : (framed hs.hn hs.hK ctx.fhBase).abs s = IndexedMinPQ.empty n)
    (hfh_pot : potential n ((layout n ctx.fhBase).abs s) = 0)
    (hphase : FTPhaseInv ctx es t.val nComp selLen0 (selLen0 + selIdxs0.length) selIdxs0 s.mem) :
    let prog := ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftTreeStepSafe w (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩) s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, a ∉ footprint n ctx.fhBase →
      (a < ctx.auxBase ∨ ctx.auxBase + 5 * n ≤ a) →
      (a < ctx.selBufBase + selLen0 ∨ ctx.selBufBase + selLen0 + n ≤ a) →
      s'.mem a = s.mem a) ∧
    (framed hs.hn hs.hK ctx.fhBase).inv s' ∧
    (framed hs.hn hs.hK ctx.fhBase).abs s' = IndexedMinPQ.empty n ∧
    potential n ((layout n ctx.fhBase).abs s') = 0 ∧
    res.sLim = t.val + 1 ∧
    (∃ selIdxs', FTPhaseInv ctx es (t.val + 1) res.nComp selLen0 res.selLen selIdxs' s'.mem) ∧
    memoryCost prog s + phasePot ctx n mRef (t.val + 1) s'.mem ≤
      phasePot ctx n mRef t.val s.mem := by
  have hcn := hs.cn
  have hn_fit1 : Fits w (n + 1) := by have := t.isLt; exact hs.fitAux.of_le (by omega)
  have hprog_eq : ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩) =
      (Memory.read (ctx.auxBase + t.val) >>= fun trS =>
       if trS < ctx.n then pure ⟨t.val + 1, nComp, selLen0 + selIdxs0.length⟩
       else do
         let res ← ftRunTree ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩
         pure ⟨t.val + 1, res.1, res.2⟩) := rfl
  have htr_fr : ctx.auxBase + t.val < s.frontier := by have := hs.auxFr; omega
  by_cases hvis : s.mem (ctx.auxBase + t.val) < n
  · have htr_lt : s.mem (ctx.auxBase + t.val) < t.val := by
      rcases hphase.hbound t with hlt | heq
      · exact hlt
      · omega
    have hite :
        (if s.mem (ctx.auxBase + t.val) < ctx.n then
          (pure ⟨t.val + 1, nComp, selLen0 + selIdxs0.length⟩ : Memory.Prog FTPhaseIterAcc)
         else do
          let res ← ftRunTree ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩
          pure ⟨t.val + 1, res.1, res.2⟩) =
        pure ⟨t.val + 1, nComp, selLen0 + selIdxs0.length⟩ :=
      ite_eq_left (by rw [hcn]; exact hvis)
    have hsafe : ftTreeStepSafe w (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩) s := by
      refine ⟨hs.fit16, by rw [hcn]; exact hs.fitAux,
        by dsimp only; exact hn_fit1.of_le (Nat.succ_le_succ t.isLt.le),
        by rw [hcn]; exact t.isLt, by rw [hcn]; exact hs.auxFr,
        fun hbad => absurd (hcn ▸ hvis) hbad⟩
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩))) := by
      rw [hprog_eq]
      refine validHistory_read_bind htr_fr ?_
      rw [hite]
      exact validHistory_pure w _ _
    have hst : (Memory.spec 0).clientState s
        (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)) = s := by
      rw [hprog_eq, StateTransitionSpec.clientState_bind, clientResult_read, clientState_read,
        hite, StateTransitionSpec.clientState_pure]
    have hres : (Memory.spec 0).clientResult s
        (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)) =
        ⟨t.val + 1, nComp, selLen0 + selIdxs0.length⟩ := by
      rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        hite, StateTransitionSpec.clientResult_pure]
    have hc : memoryCost (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)) s ≤ 1 := by
      rw [hprog_eq, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        hite, memoryCost_pure]
    have hvis_eq : visitedSet ctx.auxBase n (t.val + 1) s.mem =
        visitedSet ctx.auxBase n t.val s.mem := by
      ext v
      simp only [mem_visitedSet]
      rcases hphase.hbound v with hlt | heq <;> constructor <;> intro h <;> omega
    have hphase' : FTPhaseInv ctx es (t.val + 1) nComp selLen0 (selLen0 + selIdxs0.length)
        selIdxs0 s.mem :=
      ⟨fun v => by
          rcases hphase.hbound v with hlt | heq
          · exact Or.inl (hlt.trans (Nat.lt_succ_self _))
          · exact Or.inr heq,
        fun v hv => by
          by_cases hvt : v = t
          · rw [hvt]; exact htr_lt.trans (Nat.lt_succ_self _)
          · exact (hphase.hprev_vis v (by
              have : v.val ≠ t.val := fun heq => hvt (Fin.ext heq)
              omega)).trans (Nat.lt_succ_self _),
        hphase.hncomp_le.trans (Nat.le_succ _), hphase.hsel_len,
        by rw [hvis_eq]; exact hphase.hsel_card, hphase.hsel_nd,
        fun idx hidx => by rw [hvis_eq]; exact hphase.hsel_verts idx hidx,
        hphase.hacyclic, hphase.hext, hphase.hsel_buf,
        fun v hv => by rw [hvis_eq] at hv; exact hphase.hsup_range v hv,
        fun x hx y hy => by rw [hvis_eq] at hx hy; exact hphase.hcomp_rel x hx y hy,
        fun c => by
          obtain ⟨⟨v, hv, hveq⟩, hdeg⟩ := hphase.hcomp_deg c
          refine ⟨⟨v, by rw [hvis_eq]; exact hv, hveq⟩, ?_⟩
          rcases hdeg with hcl | ⟨A, Z, hA, hAeq, hZc, hZn⟩
          · left; intro e he; simp only [hvis_eq]; exact hcl e he
          · right; exact ⟨A, Z, by rw [hvis_eq]; exact hA, hAeq, hZc, hZn⟩⟩
    have hpot_le : memoryCost (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)) s +
        phasePot ctx n mRef (t.val + 1) s.mem ≤ phasePot ctx n mRef t.val s.mem := by
      have hsum_eq :
          (∑ v : Fin n,
            if s.mem (ctx.auxBase + v.val) < t.val + 1 then 0 else vertexPot ctx n mRef v s.mem) =
          ∑ v : Fin n,
            if s.mem (ctx.auxBase + v.val) < t.val then 0 else vertexPot ctx n mRef v s.mem := by
        refine Finset.sum_congr rfl fun v _ => ?_
        rcases hphase.hbound v with hlt | heq
        · rw [ite_eq_left (hlt.trans (Nat.lt_succ_self _)), ite_eq_left hlt]
        · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      have hsub_eq : (n - t.val) * 8 = 8 + (n - (t.val + 1)) * 8 := by
        have := t.isLt; omega
      simp only [phasePot_eq]
      rw [hsum_eq, hsub_eq]
      omega
    refine ⟨hsafe, hv, by rw [hst], by rw [hst]; exact hwf,
      fun _ _ _ _ => by rw [hst], by rw [hst]; exact hfh_inv, by rw [hst]; exact hfh_empty,
      by rw [hst]; exact hfh_pot, by rw [hres], ⟨selIdxs0, by rw [hst, hres]; exact hphase'⟩,
      by rw [hst]; exact hpot_le⟩
  · have ht_tr_n : s.mem (ctx.auxBase + t.val) = n := by
      rcases hphase.hbound t with hlt | heq
      · exact absurd (hlt.trans t.isLt) hvis
      · exact heq
    have hite :
        (if s.mem (ctx.auxBase + t.val) < ctx.n then
          (pure ⟨t.val + 1, nComp, selLen0 + selIdxs0.length⟩ : Memory.Prog FTPhaseIterAcc)
         else do
          let res ← ftRunTree ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩
          pure ⟨t.val + 1, res.1, res.2⟩) =
        (ftRunTree ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩ >>= fun res =>
          pure ⟨t.val + 1, res.1, res.2⟩) :=
      ite_eq_right (by rw [hcn]; exact hvis)
    have hrt := ftRunTree_spec hs hwf ht_tr_n hfh_inv hfh_empty hfh_pot hphase
    dsimp only at hrt
    set res := (Memory.spec 0).clientResult s
      (ftRunTree ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩)
    set s' := (Memory.spec 0).clientState s
      (ftRunTree ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩)
    rcases hrt with ⟨hsafe_rt, hv_rt, hfr', hwf', hmod', hinv', hemp', hpot', ⟨sel', hph'⟩, hcost'⟩
    have hsafe : ftTreeStepSafe w (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩) s :=
      ⟨hs.fit16, by rw [hcn]; exact hs.fitAux,
        by dsimp only; exact hn_fit1.of_le (Nat.succ_le_succ t.isLt.le),
        by rw [hcn]; exact t.isLt, by rw [hcn]; exact hs.auxFr, fun _ => hsafe_rt⟩
    have hv : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩))) := by
      rw [hprog_eq]
      refine validHistory_read_bind htr_fr ?_
      rw [hite]
      exact validHistory_bind_step hv_rt (validHistory_pure w _ _)
    have hst : (Memory.spec 0).clientState s
        (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)) = s' := by
      rw [hprog_eq, StateTransitionSpec.clientState_bind, clientResult_read, clientState_read,
        hite, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    have hres : (Memory.spec 0).clientResult s
        (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)) =
        ⟨t.val + 1, res.1, res.2⟩ := by
      rw [hprog_eq, StateTransitionSpec.clientResult_bind, clientResult_read, clientState_read,
        hite, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    have hc : memoryCost (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)) s ≤
        1 + memoryCost (ftRunTree ⟨ctx, t.val, nComp, selLen0 + selIdxs0.length⟩) s := by
      rw [hprog_eq, memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
        hite, memoryCost_bind', memoryCost_pure]
      omega
    have hpot_le : memoryCost (ftTreeStep (ctx, ⟨t.val, nComp, selLen0 + selIdxs0.length⟩)) s +
        phasePot ctx n mRef (t.val + 1) s'.mem ≤ phasePot ctx n mRef t.val s.mem := by
      have hsub_eq : (n - t.val) * 8 = 8 + (n - (t.val + 1)) * 8 := by
        have := t.isLt; omega
      simp only [phasePot_eq]
      omega
    refine ⟨hsafe, hv, by rw [hst]; exact hfr', by rw [hst]; exact hwf',
      fun a hfp haux hsel => by
        rw [hst]
        exact hmod' a hfp (by rcases haux with h | h <;> [left; right] <;> omega)
          (by rcases haux with h | h <;> [left; right] <;> omega)
          (by rcases haux with h | h <;> [left; right] <;> omega) hsel,
      by rw [hst]; exact hinv', by rw [hst]; exact hemp', by rw [hst]; exact hpot',
      by rw [hres], ⟨sel', by rw [hst, hres]; exact hph'⟩, by rw [hst]; exact hpot_le⟩

private theorem ftPhaseBody_spec {w n K mRef selLen0 : ℕ} {ctx : FTCtx}
    {es : List (IndexedEdge n)} {s : Memory.State}
    (hs : FTStatic w n K mRef selLen0 ctx es s) (hwf : Memory.WellFormed w s)
    (hn1 : 1 ≤ n)
    (hfh_inv : (framed hs.hn hs.hK ctx.fhBase).inv s)
    (hfh_empty : (framed hs.hn hs.hK ctx.fhBase).abs s = IndexedMinPQ.empty n)
    (hfh_pot : potential n ((layout n ctx.fhBase).abs s) = 0) :
    let prog := ftPhaseBody ⟨ctx, selLen0⟩
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftPhaseBodySafe w ⟨ctx, selLen0⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    (∀ a, a ∉ footprint n ctx.fhBase →
      (a < ctx.auxBase ∨ ctx.auxBase + 5 * n ≤ a) →
      (a < ctx.selBufBase + selLen0 ∨ ctx.selBufBase + selLen0 + n ≤ a) →
      s'.mem a = s.mem a) ∧
    res.compBase = ctx.auxBase + 3 * n ∧
    1 ≤ res.nComp ∧ res.nComp ≤ n ∧
    (∃ (selEs : List (IndexedEdge n)) (compFn : Fin n → Fin res.nComp),
      selEs.Subperm es ∧
      res.selLen = selLen0 + selEs.length ∧
      selEs.length + res.nComp = n ∧
      (∀ j (hj : j < selEs.length), s'.mem (ctx.selBufBase + selLen0 + j) = selEs[j].id) ∧
      IsAcyclic (selEs.map IndexedEdge.toWeighted) ∧
      (∃ F_ext : List (WeightedEdge n ℕ),
        IsMinSpanningForest (es.map IndexedEdge.toWeighted)
          (selEs.map IndexedEdge.toWeighted ++ F_ext)) ∧
      Function.Surjective compFn ∧
      (∀ u : Fin n, s'.mem (res.compBase + u.val) = (compFn u).val) ∧
      (∀ x y : Fin n, compFn x = compFn y ↔
        (edgePartition (selEs.map IndexedEdge.toWeighted)).rel x y = true) ∧
      (∀ c : Fin res.nComp,
        (∀ e ∈ es, compFn e.u = c ↔ compFn e.v = c) ∨
        ∃ A Z : Finset (Fin n),
          (∀ u ∈ A, compFn u = c) ∧
          ctx.thresh + 1 ≤ Z.card ∧
          ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z))) ∧
    memoryCost prog s ≤ 234 * es.length + 142 * n + 92 * (n * ((2 * mRef) / n)) := by
  have hcn := hs.cn
  have hcm := hs.cm
  have hn_fit1 : Fits w (n + 1) := hs.fitAux.of_le (by omega)
  let S₁ : Set ℕ := {a | ctx.auxBase ≤ a ∧ a < ctx.auxBase + n}
  let inv₁ (k acc : ℕ) (t : Memory.State) : Prop :=
    acc = k ∧ t.frontier = s.frontier ∧ Memory.WellFormed w t ∧
    (∀ a, a ∉ S₁ → t.mem a = s.mem a) ∧
    ∀ i < k, t.mem (ctx.auxBase + i) = n
  have hiter₁ := iterate_potential_spec ftInitTrStep ftInitTrStepSafe w ⟨ctx.auxBase, ctx.n⟩ 1
    ctx.n inv₁ (fun _ _ _ => 0) S₁ (fun k hk acc t ⟨hk_eq, htfr, htwf, htmod, htk⟩ => by
      subst hk_eq
      have hst_safe : ftInitTrStepSafe w (⟨ctx.auxBase, ctx.n⟩, acc) t := by
        dsimp only [ftInitTrStepSafe]
        rw [hcn]
        exact ⟨hs.fit16, hs.fitAux.of_le (by omega), hs.hn, hn_fit1.of_le (by omega),
          by have := hs.auxFr; omega⟩
      have hv : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (ftInitTrStep (⟨ctx.auxBase, ctx.n⟩, acc))) := by
        dsimp only [ftInitTrStep]
        exact validHistory_write_bind (by rw [htfr]; have := hs.auxFr; omega)
          (by rw [hcn]; exact hs.hn) (validHistory_pure w _ _)
      have hc : memoryCost (ftInitTrStep (⟨ctx.auxBase, ctx.n⟩, acc)) t ≤ 1 := by
        simp only [ftInitTrStep, client_simps]; omega
      have hst : (Memory.spec 0).clientState t (ftInitTrStep (⟨ctx.auxBase, ctx.n⟩, acc)) =
          ⟨Function.update t.mem (ctx.auxBase + acc) ctx.n, t.frontier⟩ := rfl
      have hres : (Memory.spec 0).clientResult t (ftInitTrStep (⟨ctx.auxBase, ctx.n⟩, acc)) =
          acc + 1 := rfl
      refine ⟨hst_safe, hv, by omega, ⟨by rw [hst], fun a _ ha => ?_⟩, ?_⟩
      · rw [hst]; dsimp only
        exact Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩) _ _
      · rw [hst, hres]
        refine ⟨rfl, htfr, wellFormed_clientState htwf hv, fun a ha => ?_, fun i hi => ?_⟩
        · dsimp only
          rw [Function.update_of_ne (fun h => ha ⟨by omega, by omega⟩), htmod a ha]
        · dsimp only
          by_cases hik : i = acc
          · subst hik; rw [Function.update_self, hcn]
          · rw [Function.update_of_ne (by omega)]; exact htk i (by omega))
    0 s ⟨rfl, rfl, hwf, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
  dsimp only at hiter₁
  set s₁ := (Memory.spec 0).clientState s
    (iterate ftInitTrStep ⟨ctx.auxBase, ctx.n⟩ ctx.n 0)
  rcases hiter₁ with ⟨hsafe₁, hv₁, hc₁, hmod₁_fr, _, hfr₁, hwf₁, hmod₁, htr_init⟩
  have hfp_disj₁ : ∀ a ∈ footprint n ctx.fhBase, a ∉ S₁ := by
    intro a ha hm
    simp only [footprint, Finset.mem_Ico] at ha
    simp only [S₁, Set.mem_ofPred_eq] at hm
    have := hs.fhLtAux; omega
  obtain ⟨hinv₁, habs₁, hpot₁⟩ := framed_preserved (s' := s₁) hfh_inv
    (fun a ha => hmod₁ a (hfp_disj₁ a ha)) (by rw [hfr₁])
    (by rw [hfr₁]; exact hwf.frontier_fits)
  have hemp₁ : (framed hs.hn hs.hK ctx.fhBase).abs s₁ = IndexedMinPQ.empty n :=
    habs₁.trans hfh_empty
  have hpot₁' : potential n ((layout n ctx.fhBase).abs s₁) = 0 := hpot₁.trans hfh_pot
  have hs₁ : FTStatic w n K mRef selLen0 ctx es s₁ :=
    hs.of_workMod (by rw [hfr₁]) fun a _ haux _ =>
      hmod₁ a fun hm => by
        simp only [S₁, Set.mem_ofPred_eq] at hm
        rcases haux with h | h <;> omega
  have hphase₀ : FTPhaseInv ctx es 0 0 selLen0 (selLen0 + ([] : List (Fin es.length)).length)
      [] s₁.mem := by
    have hvis0 : visitedSet ctx.auxBase n 0 s₁.mem = ∅ := by ext v; simp [mem_visitedSet]
    refine ⟨fun v => Or.inr (htr_init v.val (hcn ▸ v.isLt)), fun _ hv => absurd hv (by omega),
      le_rfl, rfl, by rw [hvis0]; simp, List.nodup_nil, fun _ h => by simp at h,
      by simp [isAcyclic_nil],
      exists_extend_isMinSpanningForest_of_subperm_msfEdges
        (es.map IndexedEdge.toWeighted) [] List.nil_subperm,
      fun _ hj => by simp at hj,
      fun _ hv => by rw [hvis0] at hv; simp at hv,
      fun _ hx => by rw [hvis0] at hx; simp at hx,
      fun c => absurd c.isLt (by omega)⟩
  let S₂ : Set ℕ := {a |
    a ∈ footprint n ctx.fhBase ∨
    (ctx.auxBase ≤ a ∧ a < ctx.auxBase + 5 * n) ∨
    (ctx.selBufBase + selLen0 ≤ a ∧ a < ctx.selBufBase + selLen0 + n)}
  let inv₂ (k : ℕ) (acc : FTPhaseIterAcc) (t : Memory.State) : Prop :=
    acc.sLim = k ∧ t.frontier = s₁.frontier ∧ Memory.WellFormed w t ∧
    (∀ a, a ∉ S₂ → t.mem a = s₁.mem a) ∧
    (framed hs.hn hs.hK ctx.fhBase).inv t ∧
    (framed hs.hn hs.hK ctx.fhBase).abs t = IndexedMinPQ.empty n ∧
    potential n ((layout n ctx.fhBase).abs t) = 0 ∧
    ∃ selIdxs, FTPhaseInv ctx es k acc.nComp selLen0 acc.selLen selIdxs t.mem
  have hiter₂ := iterate_potential_spec ftTreeStep ftTreeStepSafe w ctx 0 ctx.n inv₂
    (fun k _ t => phasePot ctx n mRef k t.mem) S₂
    (fun k hk acc t ⟨hk_eq, htfr, htwf, htmod, htfh_inv, htfh_emp, htfh_pot, selIdxs_k, hph_k⟩ => by
      have hk_n : k < n := hcn ▸ hk
      let tk : Fin n := ⟨k, hk_n⟩
      have hsel_eq : acc.selLen = selLen0 + selIdxs_k.length := hph_k.hsel_len
      have hacc_eq : acc = ⟨tk.val, acc.nComp, selLen0 + selIdxs_k.length⟩ := by
        cases acc; dsimp only [tk] at hk_eq hsel_eq ⊢; rw [hk_eq, hsel_eq]
      have hts := ftTreeStep_spec (hs₁.of_workMod (by rw [htfr]) fun a hfp haux hsel =>
          htmod a fun hm => by
            simp only [S₂, Set.mem_ofPred_eq] at hm
            rcases hm with hm | hm | hm
            · exact hfp hm
            · rcases haux with h | h <;> omega
            · rcases hsel with h | h <;> omega)
        htwf htfh_inv htfh_emp htfh_pot (t := tk) (hsel_eq ▸ hph_k)
      dsimp only at hts
      rw [← hacc_eq] at hts
      rcases hts with ⟨hsafe_ts, hv_ts, hfr_ts, hwf_ts, hmod_ts, hfh_ts, hemp_ts, hpot_ts',
        hsLim_ts, ⟨sel', hph'⟩, hpot_ts⟩
      refine ⟨hsafe_ts, hv_ts, by omega, ⟨by rw [hfr_ts], fun a _ ha => ?_⟩,
        hsLim_ts, hfr_ts.trans htfr, hwf_ts, fun a ha => ?_, hfh_ts, hemp_ts, hpot_ts', sel', hph'⟩
      · simp only [S₂, Set.mem_ofPred_eq, not_or, not_and] at ha
        exact hmod_ts a ha.1 (by omega) (by omega)
      · simp only [S₂, Set.mem_ofPred_eq, not_or, not_and] at ha
        rw [hmod_ts a ha.1 (by omega) (by omega), htmod a (by
          simp only [S₂, Set.mem_ofPred_eq, not_or, not_and]; exact ha)]
      ) ⟨0, 0, selLen0⟩ s₁
      ⟨rfl, rfl, hwf₁, fun _ _ => rfl, hinv₁, hemp₁, hpot₁', [], hphase₀⟩
  dsimp only at hiter₂
  set res₂ := (Memory.spec 0).clientResult s₁ (iterate ftTreeStep ctx ctx.n ⟨0, 0, selLen0⟩)
  set s₂ := (Memory.spec 0).clientState s₁ (iterate ftTreeStep ctx ctx.n ⟨0, 0, selLen0⟩)
  rcases hiter₂ with ⟨hsafe₂, hv₂, hc₂, hmod₂_fr, _, hfr₂, hwf₂, hmod₂, hfh₂, hemp₂, hpot₂,
    selIdxsF, hphF⟩
  have hvis_univ : visitedSet ctx.auxBase n ctx.n s₂.mem = Finset.univ := by
    ext v; simp only [mem_visitedSet, Finset.mem_univ, iff_true]
    exact hphF.hprev_vis v (hcn ▸ v.isLt)
  have htr_lt_n : ∀ i < n, s₂.mem (ctx.auxBase + i) < n := fun i hi => by
    have := hphF.hprev_vis ⟨i, hi⟩ (hcn ▸ hi)
    rwa [hcn] at this
  let S₃ : Set ℕ := {a | ctx.auxBase + 3 * n ≤ a ∧ a < ctx.auxBase + 4 * n}
  let inv₃ (k acc : ℕ) (t : Memory.State) : Prop :=
    acc = k ∧ t.frontier = s₂.frontier ∧ Memory.WellFormed w t ∧
    (∀ a, a ∉ S₃ → t.mem a = s₂.mem a) ∧
    ∀ i < k, t.mem (ctx.auxBase + 3 * n + i) =
      s₂.mem (ctx.auxBase + 2 * n + s₂.mem (ctx.auxBase + i))
  have hiter₃ := iterate_potential_spec ftWriteCompStep ftWriteCompStepSafe w
    ⟨ctx.auxBase, ctx.n⟩ 3 ctx.n inv₃ (fun _ _ _ => 0) S₃
    (fun k hk acc t ⟨hk_eq, htfr, htwf, htmod, hcomp⟩ => by
      subst hk_eq
      have hk_n : acc < n := hcn ▸ hk
      have htr_k : t.mem (ctx.auxBase + acc) = s₂.mem (ctx.auxBase + acc) :=
        htmod _ fun hm => by simp only [S₃, Set.mem_ofPred_eq] at hm; omega
      have hst_safe : ftWriteCompStepSafe w (⟨ctx.auxBase, ctx.n⟩, acc) t := by
        dsimp only [ftWriteCompStepSafe]
        rw [hcn]
        exact ⟨hs.fit16, hs.fitAux.of_le (by omega), hn_fit1.of_le (Nat.succ_le_succ hk_n.le),
          hk_n, by rw [htfr, hfr₂, hfr₁]; have := hs.auxFr; omega,
          by rw [htr_k]; exact htr_lt_n acc hk_n⟩
      have hv : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (ftWriteCompStep (⟨ctx.auxBase, ctx.n⟩, acc))) := by
        dsimp only [ftWriteCompStep]
        exact validHistory_read_bind (by rw [htfr, hfr₂, hfr₁]; have := hs.auxFr; omega)
          (validHistory_read_bind (by
            rw [htfr, hfr₂, hfr₁, hcn, htr_k]
            have := htr_lt_n acc hk_n; have := hs.auxFr; omega)
            (validHistory_write_bind (by rw [htfr, hfr₂, hfr₁, hcn]; have := hs.auxFr; omega)
              (htwf.mem_fits _) (validHistory_pure w _ _)))
      have hc : memoryCost (ftWriteCompStep (⟨ctx.auxBase, ctx.n⟩, acc)) t ≤ 3 := by
        simp only [ftWriteCompStep, client_simps]; omega
      have hsup_eq : t.mem (ctx.auxBase + 2 * ctx.n + t.mem (ctx.auxBase + acc)) =
          s₂.mem (ctx.auxBase + 2 * n + s₂.mem (ctx.auxBase + acc)) := by
        have := htr_lt_n acc hk_n
        rw [hcn, htr_k]
        exact htmod _ fun hm => by simp only [S₃, Set.mem_ofPred_eq] at hm; omega
      have hst : (Memory.spec 0).clientState t (ftWriteCompStep (⟨ctx.auxBase, ctx.n⟩, acc)) =
          ⟨Function.update t.mem (ctx.auxBase + 3 * ctx.n + acc)
            (t.mem (ctx.auxBase + 2 * ctx.n + t.mem (ctx.auxBase + acc))), t.frontier⟩ := rfl
      have hres : (Memory.spec 0).clientResult t (ftWriteCompStep (⟨ctx.auxBase, ctx.n⟩, acc)) =
          acc + 1 := rfl
      refine ⟨hst_safe, hv, by omega, ⟨by rw [hst], fun a _ ha => ?_⟩, ?_⟩
      · rw [hst]; dsimp only
        exact Function.update_of_ne (fun h => ha ⟨by rw [← hcn]; omega, by rw [← hcn]; omega⟩) _ _
      · rw [hst, hres]
        refine ⟨rfl, htfr, wellFormed_clientState htwf hv, fun a ha => ?_, fun i hi => ?_⟩
        · dsimp only
          rw [Function.update_of_ne (fun h => ha ⟨by rw [← hcn]; omega, by rw [← hcn]; omega⟩),
            htmod a ha]
        · dsimp only
          by_cases hik : i = acc
          · subst hik; rw [hcn, Function.update_self]; rw [hcn] at hsup_eq; exact hsup_eq
          · rw [hcn, Function.update_of_ne (by omega)]; exact hcomp i (by omega))
    0 s₂ ⟨rfl, rfl, hwf₂, fun _ _ => rfl, fun _ h => absurd h (by omega)⟩
  dsimp only at hiter₃
  set s₃ := (Memory.spec 0).clientState s₂
    (iterate ftWriteCompStep ⟨ctx.auxBase, ctx.n⟩ ctx.n 0)
  rcases hiter₃ with ⟨hsafe₃, hv₃, hc₃, _, _, hfr₃, hwf₃, hmod₃, hcomp_mem⟩
  have hprog_eq : ftPhaseBody ⟨ctx, selLen0⟩ =
      (iterate ftInitTrStep ⟨ctx.auxBase, ctx.n⟩ ctx.n 0 >>= fun _ =>
       iterate ftTreeStep ctx ctx.n ⟨0, 0, selLen0⟩ >>= fun res =>
       iterate ftWriteCompStep ⟨ctx.auxBase, ctx.n⟩ ctx.n 0 >>= fun _ =>
       pure ⟨res.nComp, ctx.auxBase + 3 * ctx.n, res.selLen⟩) := rfl
  have hsafe : ftPhaseBodySafe w ⟨ctx, selLen0⟩ s := by
    dsimp only [ftPhaseBodySafe]
    exact ⟨hs.fit16, by rw [hcn]; exact hs.fitAux.of_le (by omega), by rw [hcn]; exact hn_fit1,
      hs.fitSel.of_le (by omega), hsafe₁, hsafe₂, hsafe₃⟩
  have hv : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (ftPhaseBody ⟨ctx, selLen0⟩)) := by
    rw [hprog_eq]
    exact validHistory_bind_step hv₁ (validHistory_bind_step hv₂
      (validHistory_bind_step hv₃ (validHistory_pure w _ _)))
  have hst : (Memory.spec 0).clientState s (ftPhaseBody ⟨ctx, selLen0⟩) = s₃ := by
    rw [hprog_eq, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
  have hres : (Memory.spec 0).clientResult s (ftPhaseBody ⟨ctx, selLen0⟩) =
      ⟨res₂.nComp, ctx.auxBase + 3 * ctx.n, res₂.selLen⟩ := by
    rw [hprog_eq, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
  have hmod_all : ∀ a, a ∉ footprint n ctx.fhBase →
      (a < ctx.auxBase ∨ ctx.auxBase + 5 * n ≤ a) →
      (a < ctx.selBufBase + selLen0 ∨ ctx.selBufBase + selLen0 + n ≤ a) →
      s₃.mem a = s.mem a := by
    intro a hfp h1 h2
    rw [hmod₃ a (fun hm => by
        simp only [S₃, Set.mem_ofPred_eq] at hm; rcases h1 with h1 | h1 <;> omega),
      hmod₂ a (fun hm => by
        simp only [S₂, Set.mem_ofPred_eq] at hm
        rcases hm with hm | hm | hm
        · exact hfp hm
        · rcases h1 with h1 | h1 <;> omega
        · rcases h2 with h2 | h2 <;> omega),
      hmod₁ a (fun hm => by
        simp only [S₁, Set.mem_ofPred_eq] at hm; rcases h1 with h1 | h1 <;> omega)]
  have hnc_pos : 1 ≤ res₂.nComp := by
    have h1 := hphF.hsel_card
    rw [hvis_univ, Finset.card_univ, Fintype.card_fin] at h1
    by_contra h0
    have hnc0 : res₂.nComp = 0 := by omega
    have hsel_eq_n : selIdxsF.length = n := by omega
    have hcard_e := hphF.hacyclic.length_le_pred hn1
    simp only [List.length_map] at hcard_e
    omega
  let selEs := selIdxsF.map (fun i => es[i.val])
  let compFn : Fin n → Fin res₂.nComp := fun u =>
    ⟨s₃.mem (ctx.auxBase + 3 * n + u.val), by
      rw [hcomp_mem u.val (hcn ▸ u.isLt)]
      exact hphF.hsup_range u (by rw [hvis_univ]; exact Finset.mem_univ u)⟩
  have hcomp_eq : ∀ u : Fin n, (compFn u).val =
      s₂.mem (ctx.auxBase + 2 * n + s₂.mem (ctx.auxBase + u.val)) := fun u =>
    hcomp_mem u.val (hcn ▸ u.isLt)
  have hsel_buf_s3 : ∀ j (hj : j < selEs.length),
      s₃.mem (ctx.selBufBase + selLen0 + j) = selEs[j].id := by
    intro j hj
    have hj' : j < selIdxsF.length := by simpa only [selEs, List.length_map] using hj
    have hsel_lt_n : selIdxsF.length ≤ n := by
      have := hphF.hsel_card
      rw [hvis_univ, Finset.card_univ, Fintype.card_fin] at this
      omega
    rw [hmod₃ _ fun hm => by
      simp only [S₃, Set.mem_ofPred_eq] at hm; rcases hs.selDisjAux with hd | hd <;> omega]
    simpa only [selEs, List.getElem_map] using hphF.hsel_buf j hj'
  have hsurj : Function.Surjective compFn := by
    intro c
    obtain ⟨⟨v, _, hv_eq⟩, _⟩ := hphF.hcomp_deg c
    exact ⟨v, Fin.ext ((hcomp_eq v).trans hv_eq)⟩
  have hrel_comp : ∀ x y : Fin n, compFn x = compFn y ↔
      (edgePartition (selEs.map IndexedEdge.toWeighted)).rel x y = true := by
    intro x y
    rw [Fin.ext_iff, hcomp_eq x, hcomp_eq y]
    exact hphF.hcomp_rel x (by rw [hvis_univ]; exact Finset.mem_univ x)
      y (by rw [hvis_univ]; exact Finset.mem_univ y)
  have hdeg_comp : ∀ c : Fin res₂.nComp,
      (∀ e ∈ es, compFn e.u = c ↔ compFn e.v = c) ∨
      ∃ A Z : Finset (Fin n),
        (∀ u ∈ A, compFn u = c) ∧
        ctx.thresh + 1 ≤ Z.card ∧
        ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z) := by
    intro c
    obtain ⟨_, hdeg⟩ := hphF.hcomp_deg c
    rcases hdeg with hcl | ⟨Ac, Zc, _, hAc_eq, hZc_c, hZc_n⟩
    · left; intro e he
      have h1 := hcl e he
      simp only [hvis_univ, Finset.mem_univ, true_and, Fin.ext_iff, hcomp_eq] at h1 ⊢
      exact h1
    · right
      exact ⟨Ac, Zc, fun u hu => Fin.ext ((hcomp_eq u).trans (hAc_eq u hu)), hZc_c, hZc_n⟩
  have hcost_all : memoryCost (ftPhaseBody ⟨ctx, selLen0⟩) s ≤
      234 * es.length + 142 * n + 92 * (n * ((2 * mRef) / n)) := by
    have hpot_init : phasePot ctx n mRef 0 s₁.mem ≤
        234 * es.length + 138 * n + 92 * (n * ((2 * mRef) / n)) :=
      phasePot_zero_le hs₁.hcsr
    rw [hprog_eq, memoryCost_bind', memoryCost_bind', memoryCost_bind', memoryCost_pure]
    change memoryCost (iterate ftInitTrStep ⟨ctx.auxBase, ctx.n⟩ ctx.n 0) s +
      (memoryCost (iterate ftTreeStep ctx ctx.n ⟨0, 0, selLen0⟩) s₁ +
        (memoryCost (iterate ftWriteCompStep ⟨ctx.auxBase, ctx.n⟩ ctx.n 0) s₂ + 0)) ≤ _
    have hc₁' : memoryCost (iterate ftInitTrStep ⟨ctx.auxBase, ctx.n⟩ ctx.n 0) s ≤ n := by
      omega
    have hc₂' : memoryCost (iterate ftTreeStep ctx ctx.n ⟨0, 0, selLen0⟩) s₁ ≤
        phasePot ctx n mRef 0 s₁.mem := by
      rw [Nat.zero_mul, Nat.add_zero] at hc₂; omega
    have hc₃' : memoryCost (iterate ftWriteCompStep ⟨ctx.auxBase, ctx.n⟩ ctx.n 0) s₂ ≤ 3 * n := by
      omega
    omega
  refine ⟨hsafe, hv, by rw [hst, hfr₃, hfr₂, hfr₁], by rw [hst]; exact hwf₃,
    fun a hfp h1 h2 => by rw [hst]; exact hmod_all a hfp h1 h2,
    by rw [hres]; dsimp only; rw [hcn], by rw [hres]; exact hnc_pos,
    by rw [hres]; exact hcn ▸ hphF.hncomp_le, ?_, hcost_all⟩
  rw [hst, hres]
  dsimp only
  refine ⟨selEs, compFn, selIdxs_subperm_es hphF.hsel_nd,
    by simpa only [selEs, List.length_map] using hphF.hsel_len, ?_, hsel_buf_s3, hphF.hacyclic,
    hphF.hext, hsurj, fun u => by rw [hcn], hrel_comp, hdeg_comp⟩
  have hc := hphF.hsel_card
  rw [hvis_univ, Finset.card_univ, Fintype.card_fin] at hc
  simpa only [selEs, List.length_map] using hc

/-! ## Public Phase Specification and Phase-Rank Decrease -/

/-- Specification of `ftPhaseProg`: executes one Fredman–Tarjan bounded-heap phase on an active
graph `es`, producing `FTPhaseOut` (`nComp`, `compBase`, `selLen'`) with `1 ≤ nComp ≤ n`, acyclic
selected edges extending to a minimum spanning forest of `es`, supervertex map `comp`, and
Fredman–Tarjan degree/closed-component witness, in memory cost
`≤ 234 * es.length + 156 * n + 184 * mRef + 7`. -/
theorem ftPhaseProg_spec {w n mRef : ℕ} {es : List (IndexedEdge n)}
    {edgeBase offBase adjBase selBufBase selLen0 : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn1 : 1 ≤ n)
    (hfit_mRef : Fits w (2 * mRef + 1))
    (hfit_fr : Fits w (s.frontier + (14 * n + 5)))
    (hoff_fr : offBase + n + 1 ≤ s.frontier)
    (hadj_fr : adjBase + 4 * es.length ≤ s.frontier)
    (hedge_fr : edgeBase + 4 * es.length ≤ s.frontier)
    (hsel_fr : selBufBase + selLen0 + n ≤ s.frontier)
    (hsel_disj_edge : selBufBase + selLen0 + n ≤ edgeBase ∨
      edgeBase + 4 * es.length ≤ selBufBase + selLen0)
    (hsel_disj_off : selBufBase + selLen0 + n ≤ offBase ∨
      offBase + n + 1 ≤ selBufBase + selLen0)
    (hsel_disj_adj : selBufBase + selLen0 + n ≤ adjBase ∨
      adjBase + 4 * es.length ≤ selBufBase + selLen0)
    (hin : HoldsIndexedEdges edgeBase es s.mem)
    (hcsr : HoldsUndirCSR offBase adjBase es s.mem) :
    let args : FTPhaseArgs :=
      ⟨n, es.length, mRef, edgeBase, offBase, adjBase, selBufBase, selLen0⟩
    let prog := ftPhaseProg args
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    ftPhaseProgSafe w args s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier + (14 * n + 5) ∧
    Memory.WellFormed w s' ∧
    (∀ a < s.frontier,
      (a < selBufBase + selLen0 ∨ selBufBase + selLen0 + n ≤ a) → s'.mem a = s.mem a) ∧
    res.compBase + n ≤ s'.frontier ∧
    1 ≤ res.nComp ∧ res.nComp ≤ n ∧
    (∃ (selEs : List (IndexedEdge n)) (compFn : Fin n → Fin res.nComp),
      selEs.Subperm es ∧
      res.selLen = selLen0 + selEs.length ∧
      selEs.length + res.nComp = n ∧
      (∀ j (hj : j < selEs.length), s'.mem (selBufBase + selLen0 + j) = selEs[j].id) ∧
      IsAcyclic (selEs.map IndexedEdge.toWeighted) ∧
      (∃ F_ext : List (WeightedEdge n ℕ),
        IsMinSpanningForest (es.map IndexedEdge.toWeighted)
          (selEs.map IndexedEdge.toWeighted ++ F_ext)) ∧
      Function.Surjective compFn ∧
      (∀ u : Fin n, s'.mem (res.compBase + u.val) = (compFn u).val) ∧
      (∀ x y : Fin n, compFn x = compFn y ↔
        (edgePartition (selEs.map IndexedEdge.toWeighted)).rel x y = true) ∧
      (∀ c : Fin res.nComp,
        (∀ e ∈ es, compFn e.u = c ↔ compFn e.v = c) ∨
        ∃ A Z : Finset (Fin n),
          (∀ u ∈ A, compFn u = c) ∧
          min n (2 ^ ((2 * mRef) / n)) + 1 ≤ Z.card ∧
          ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z))) ∧
    memoryCost prog s ≤ 234 * es.length + 156 * n + 184 * mRef + 7 := by
  let K : ℕ := (es.map IndexedEdge.weight).foldr max 0
  have hK_es : ∀ e ∈ es, e.weight ≤ K := by
    intro e he
    suffices h : ∀ l : List ℕ, ∀ w ∈ l, w ≤ l.foldr max 0 from
      h (es.map IndexedEdge.weight) e.weight (List.mem_map.mpr ⟨e, he, rfl⟩)
    intro l x hx
    induction l with
    | nil => simp at hx
    | cons a t ih =>
      simp only [List.foldr_cons, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · exact le_max_left _ _
      · exact (ih hx).trans (le_max_right _ _)
  have hK : Fits w K := by
    suffices h : ∀ l : List ℕ, (∀ x ∈ l, Fits w x) → Fits w (l.foldr max 0) by
      refine h (es.map IndexedEdge.weight) fun x hx => ?_
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp he
      rw [← (hin i hi).2.2.1]
      exact hwf.mem_fits _
    intro l hl
    induction l with
    | nil => exact h16.of_le (by simp)
    | cons a t ih =>
      simp only [List.foldr_cons, Nat.max_def]
      split_ifs with hle
      · exact ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
      · exact hl a List.mem_cons_self
  have hfit_2m : Fits w (2 * es.length + 1) := by
    by_cases hm0 : es.length = 0
    · rw [hm0]; exact h16.of_le (by omega)
    · exact hwf.frontier_fits.of_le (by omega)
  have hfit_sel : Fits w (selLen0 + n + 1) := hfit_fr.of_le (by omega)
  have hn : Fits w n := hfit_fr.of_le (by omega)
  have hfh := allocProg_spec hwf hn hK (hfit_fr.of_le (by omega))
  dsimp only at hfh
  set fhBase := (Memory.spec 0).clientResult s (allocProg n)
  set s₁ := (Memory.spec 0).clientState s (allocProg n)
  rcases hfh with ⟨hv₁, hfhBase_eq, hfr₁, hwf₁, hmod₁_raw, hinv₁, hemp₁, hpot₁, hc₁⟩
  have hmod₁ : ∀ a < s.frontier, s₁.mem a = s.mem a := fun a ha =>
    hmod₁_raw a fun h => by simp only [footprint, Finset.mem_Ico, hfhBase_eq] at h; omega
  have hfit_aux : Fits w (s₁.frontier + 5 * n) := hfit_fr.of_le (by rw [hfr₁]; omega)
  have hv₂ : (Memory.spec w).ValidHistory s₁
      ((Memory.spec w).clientHistory s₁ (Memory.alloc (5 * n))) := validHistory_alloc hfit_aux
  set s₂ := (Memory.spec 0).clientState s₁ (Memory.alloc (5 * n))
  have haux_eq : (Memory.spec 0).clientResult s₁ (Memory.alloc (5 * n)) = s₁.frontier := rfl
  have hfr₂ : s₂.frontier = s₁.frontier + 5 * n := rfl
  have hwf₂ : Memory.WellFormed w s₂ := wellFormed_clientState hwf₁ hv₂
  have hmod₂ : ∀ a < s₁.frontier, s₂.mem a = s₁.mem a := fun a ha =>
    clear_of_not_owns (by simp only [Block.Owns]; omega)
  have hc₂ : memoryCost (Memory.alloc (5 * n)) s₁ ≤ 5 * n + 1 := by
    rw [memoryCost_alloc]
  obtain ⟨hinv₂, habs₂, hpot₂⟩ := framed_preserved (s' := s₂) hinv₁
    (fun a ha => hmod₂ a (by
      simp only [footprint, Finset.mem_Ico] at ha; rw [hfhBase_eq] at ha; rw [hfr₁]; omega))
    (by rw [hfr₂]; omega) (hfit_fr.of_le (by rw [hfr₂, hfr₁]; omega))
  have hct := computeThreshProg_spec (s := s₂) hfit_mRef (hfit_fr.of_le (by omega)) hn1
  dsimp only at hct
  set thresh := (Memory.spec 0).clientResult s₂ (computeThreshProg n mRef)
  set s₃ := (Memory.spec 0).clientState s₂ (computeThreshProg n mRef)
  rcases hct with ⟨hsafe_ct, hv₃, hs3_eq, hthresh_eq, _, hthresh_le_n, hc_ct⟩
  let ctx : FTCtx := ⟨n, es.length, edgeBase, offBase, adjBase, fhBase, s₁.frontier,
    selBufBase, thresh⟩
  have hs_ctx : FTStatic w n K mRef selLen0 ctx es s₂ :=
    { fit16 := h16
      cn := rfl
      cm := rfl
      hn := hn
      hK := hK
      fitFh := hfit_fr.of_le (by dsimp only [ctx]; rw [hfhBase_eq]; omega)
      fitAux := hfit_fr.of_le (by dsimp only [ctx]; rw [hfr₁]; omega)
      fitOff := hwf.frontier_fits.of_le hoff_fr
      fitAdj := hwf.frontier_fits.of_le hadj_fr
      fitEdge := hwf.frontier_fits.of_le hedge_fr
      fit2m := hfit_2m
      fitSel := hfit_sel
      offFr := by dsimp only [ctx]; rw [hfr₂, hfr₁]; omega
      adjFr := by dsimp only [ctx]; rw [hfr₂, hfr₁]; omega
      edgeFr := by dsimp only [ctx]; rw [hfr₂, hfr₁]; omega
      auxFr := by dsimp only [ctx]; rw [hfr₂]
      selFr := by dsimp only [ctx]; rw [hfr₂, hfr₁]; omega
      fhLtAux := by dsimp only [ctx]; rw [hfhBase_eq, hfr₁]
      edgeLtFh := by dsimp only [ctx]; rw [hfhBase_eq]; omega
      offLtFh := by dsimp only [ctx]; rw [hfhBase_eq]; omega
      adjLtFh := by dsimp only [ctx]; rw [hfhBase_eq]; omega
      selDisjFh := Or.inl (by dsimp only [ctx]; rw [hfhBase_eq]; omega)
      selDisjAux := Or.inl (by dsimp only [ctx]; rw [hfr₁]; omega)
      selDisjEdge := hsel_disj_edge
      selDisjOff := hsel_disj_off
      selDisjAdj := hsel_disj_adj
      hin := hin.congr fun a ha1 ha2 => by
        dsimp only [ctx] at ha1 ha2
        exact (hmod₂ a (by rw [hfr₁]; omega)).trans (hmod₁ a (by omega))
      hcsr := hcsr.congr
        (fun a ha1 ha2 => by
          dsimp only [ctx] at ha1 ha2
          exact (hmod₂ a (by rw [hfr₁]; omega)).trans (hmod₁ a (by omega)))
        (fun a ha1 ha2 => by
          dsimp only [ctx] at ha1 ha2
          exact (hmod₂ a (by rw [hfr₁]; omega)).trans (hmod₁ a (by omega)))
      hKes := hK_es
      threshLe := by dsimp only [ctx]; rw [hthresh_eq]; exact min_le_right _ _ }
  have hbody := ftPhaseBody_spec hs_ctx hwf₂ hn1 hinv₂ (habs₂.trans hemp₁) (hpot₂.trans hpot₁)
  dsimp only at hbody
  set resB := (Memory.spec 0).clientResult s₂ (ftPhaseBody ⟨ctx, selLen0⟩)
  set s₄ := (Memory.spec 0).clientState s₂ (ftPhaseBody ⟨ctx, selLen0⟩)
  rcases hbody with ⟨hsafe_b, hv_b, hfr₄, hwf₄, hmod₄, hcompBase_eq, hnc1, hnc_le,
    ⟨selEs, compFn, hsel_sub, hsel_len, hsel_card, hsel_buf, hac, hext, hsurj, hcomp_mem,
      hcomp_rel, hcomp_deg⟩, hc_b⟩
  let args : FTPhaseArgs := ⟨n, es.length, mRef, edgeBase, offBase, adjBase, selBufBase, selLen0⟩
  have hprog_eq : ftPhaseProg args =
      (allocProg n >>= fun fhB =>
       Memory.alloc (5 * n) >>= fun auxB =>
       computeThreshProg n mRef >>= fun th =>
       ftPhaseBody ⟨⟨n, es.length, edgeBase, offBase, adjBase, fhB, auxB, selBufBase, th⟩,
         selLen0⟩) := rfl
  have hsafe_all : ftPhaseProgSafe w args s := by
    dsimp only [ftPhaseProgSafe, args]
    refine ⟨h16, hfit_fr, hsafe_ct, ?_⟩
    change ftPhaseBodySafe w ⟨ctx, selLen0⟩ s₃
    rw [hs3_eq]; exact hsafe_b
  have hv_all : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (ftPhaseProg args)) := by
    rw [hprog_eq]
    refine validHistory_bind_step hv₁ ?_
    refine validHistory_bind_step hv₂ ?_
    refine validHistory_bind_step hv₃ ?_
    change (Memory.spec w).ValidHistory s₃
      ((Memory.spec w).clientHistory s₃ (ftPhaseBody ⟨ctx, selLen0⟩))
    rw [hs3_eq]; exact hv_b
  have hst_all : (Memory.spec 0).clientState s (ftPhaseProg args) = s₄ := by
    rw [hprog_eq, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
      StateTransitionSpec.clientState_bind]
    change (Memory.spec 0).clientState s₃ (ftPhaseBody ⟨ctx, selLen0⟩) = s₄
    rw [hs3_eq]
  have hres_all : (Memory.spec 0).clientResult s (ftPhaseProg args) = resB := by
    rw [hprog_eq, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
      StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s₃ (ftPhaseBody ⟨ctx, selLen0⟩) = resB
    rw [hs3_eq]
  have hcost_all :
      memoryCost (ftPhaseProg args) s ≤ 234 * es.length + 156 * n + 184 * mRef + 7 := by
    have hmul_div : n * ((2 * mRef) / n) ≤ 2 * mRef := Nat.mul_div_le (2 * mRef) n
    rw [hprog_eq, memoryCost_bind', memoryCost_bind', memoryCost_bind']
    change memoryCost (allocProg n) s + (memoryCost (Memory.alloc (5 * n)) s₁ +
      (memoryCost (computeThreshProg n mRef) s₂ +
        memoryCost (ftPhaseBody ⟨ctx, selLen0⟩) s₃)) ≤ _
    rw [hs3_eq, hc_ct]
    omega
  refine ⟨hsafe_all, hv_all, by rw [hst_all, hfr₄, hfr₂, hfr₁]; omega,
    by rw [hst_all]; exact hwf₄, fun a ha hsel => ?_,
    by dsimp only [ctx] at hcompBase_eq
       rw [hst_all, hres_all, hcompBase_eq, hfr₄, hfr₂, hfr₁]; omega,
    by rw [hres_all]; exact hnc1, by rw [hres_all]; exact hnc_le, ?_, hcost_all⟩
  · rw [hst_all]
    rw [hmod₄ a (by dsimp only [ctx]; simp only [footprint, Finset.mem_Ico]; rw [hfhBase_eq]; omega)
      (Or.inl (by dsimp only [ctx]; rw [hfr₁]; omega)) hsel,
      hmod₂ a (by rw [hfr₁]; omega), hmod₁ a ha]
  · rw [hst_all, hres_all]
    refine ⟨selEs, compFn, hsel_sub, hsel_len, hsel_card, hsel_buf, hac, hext, hsurj,
      hcomp_mem, hcomp_rel, fun c => ?_⟩
    have hc := hcomp_deg c
    dsimp only [ctx] at hc
    rwa [hthresh_eq] at hc

/-- Bounded-heap phase rank `β(m_ref, n_p) = Nat.iterClogBeta ((2 * m_ref) / n_p) n_p`
(and `0` when `n_p = 0`). -/
@[expose] def ftPhaseRank (mRef nCur : ℕ) : ℕ :=
  if nCur = 0 then 0 else Nat.iterClogBeta ((2 * mRef) / nCur) nCur

/-- Strictly decreasing phase rank whenever a phase produces `nOut ≤ nComp ≤ n` surviving
non-isolated vertices (`hnoniso`) atop loop-free deduplicated contracted edges `esDedup`. -/
theorem ftPhase_rank_lt_of_shrink {n nComp nOut mRef : ℕ}
    {es : List (IndexedEdge n)} {compFn : Fin n → Fin nComp}
    {esCon esDedup : List (IndexedEdge nComp)}
    {lift : Fin nOut → Fin nComp} {esOut : List (IndexedEdge nOut)}
    (hn1 : 1 ≤ n) (hm_le : es.length ≤ mRef) (hno : nOut ≤ nComp) (hnc : nComp ≤ n)
    (hdeg : ∀ c : Fin nComp,
      (∀ e ∈ es, compFn e.u = c ↔ compFn e.v = c) ∨
      ∃ A Z : Finset (Fin n),
        (∀ u ∈ A, compFn u = c) ∧
        min n (2 ^ ((2 * mRef) / n)) + 1 ≤ Z.card ∧
        ∀ z ∈ Z, z ∉ A ∧ ∃ e ∈ es, (e.u ∈ A ∧ e.v = z) ∨ (e.v ∈ A ∧ e.u = z))
    (hes_con : es.map (fun e => ⟨compFn e.u, compFn e.v, e.weight, e.id⟩) = esCon)
    (hdedup_sub : esDedup.Subperm esCon)
    (hdedup_noloop : ∀ e ∈ esDedup, e.u ≠ e.v)
    (hlift_inj : Function.Injective lift)
    (hes_out : esOut.map (fun e => ⟨lift e.u, lift e.v, e.weight, e.id⟩) = esDedup)
    (hnoniso : ∀ y : Fin nOut, ∃ e ∈ esOut, e.u = y ∨ e.v = y) :
    nOut ≤ n ∧ ftPhaseRank mRef nOut < ftPhaseRank mRef n := by
  have hn_le : nOut ≤ n := hno.trans hnc
  refine ⟨hn_le, ?_⟩
  dsimp only [ftPhaseRank]
  rw [ite_eq_right (Nat.ne_of_gt hn1)]
  by_cases hn0 : nOut = 0
  · rw [ite_eq_left hn0]
    exact Nat.one_le_iterClogBeta ((2 * mRef) / n) n
  rw [ite_eq_right hn0]
  have hnOut1 : 1 ≤ nOut := Nat.pos_of_ne_zero hn0
  have hmul := surviving_vertices_mul_thresh_le hdeg hes_con hdedup_sub hdedup_noloop hlift_inj
    hes_out hnoniso
  have hthresh_lt_n : 2 ^ ((2 * mRef) / n) < n := by
    let y0 : Fin nOut := ⟨0, hnOut1⟩
    obtain ⟨Ay, Zy, hAy, hZy_card, hZy_nbr⟩ :=
      exists_cut_witness_of_nonisolated hdeg hes_con hdedup_sub hdedup_noloop hes_out
        (hnoniso y0)
    have hAy_ne : Ay.Nonempty := by
      by_cases h0 : Ay.Nonempty
      · exact h0
      · rw [Finset.not_nonempty_iff_eq_empty] at h0
        obtain ⟨z, hz⟩ := Finset.card_pos.mp (lt_of_lt_of_le (Nat.succ_pos _) hZy_card)
        obtain ⟨_, _, _, (⟨hw, _⟩ | ⟨hw, _⟩)⟩ := hZy_nbr z hz <;> simp [h0] at hw
    have hdisj_AZ : Disjoint Ay Zy := Finset.disjoint_left.mpr fun z hzA hzZ =>
      (hZy_nbr z hzZ).1 hzA
    have hsum_AZ : Ay.card + Zy.card ≤ n := by
      rw [← Finset.card_union_of_disjoint hdisj_AZ]
      exact (Finset.card_le_univ _).trans (by simp)
    have hAy_pos : 1 ≤ Ay.card := Finset.card_pos.mpr hAy_ne
    by_contra hge
    have hmin_eq : min n (2 ^ ((2 * mRef) / n)) = n := min_eq_left (Nat.not_lt.mp hge)
    rw [hmin_eq] at hZy_card
    omega
  have hmin_eq : min n (2 ^ ((2 * mRef) / n)) = 2 ^ ((2 * mRef) / n) :=
    min_eq_right hthresh_lt_n.le
  rw [hmin_eq] at hmul
  have hmul_ref : nOut * (2 ^ ((2 * mRef) / n) + 1) ≤ 2 * mRef := hmul.trans (by omega)
  exact Nat.iterClogBeta_div_lt_of_mul_le hnOut1 hn_le hthresh_lt_n hmul_ref

end Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase
