/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Canonical
public import CslibFrontier.Algorithms.WordRAM.Kruskal
public import CslibFrontier.Computability.WordRAM.Realization.Absorb
public import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
public import CslibFrontier.Computability.WordRAM.Realization.Structure
public import CslibFrontier.Foundations.Data.Nat.IterLog
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Layout
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.PrecompSearch
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.Driver
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.IndexedEdges
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BaseOps
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BoruvkaStages
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.PartitionRound
import CslibFrontier.Computability.WordRAM.Realization.FramedLoop
import CslibFrontier.Computability.WordRAM.Realization.NatLog
import CslibFrontier.Computability.WordRAM.Realization.WhileAbsorb
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith

/-!
# Optimal Deterministic Minimum Spanning Forest Word-RAM Driver

Top-level assembly and Theorem 5.8 realization of Pettie and Ramachandran's optimal deterministic
minimum spanning forest algorithm on the Word RAM, corresponding to Section 2.1 (p. 18), Section 2.3
(pp. 19–20), Section 3.2 (pp. 21–22), Section 4.1 (p. 23), Section 5 (pp. 23–24), and Section 5.1
(pp. 25–27, Theorem 5.8 p. 27) of [PettieRamachandran2002] (#8624).

Given an `n`-vertex, `m`-edge weighted undirected multigraph in standard `Kruskal.encode` layout
`[n, m, u₀, v₀, w₀, ...]`, `optimalMSFProg` proceeds as follows:

1. Handles `m = 0` directly via `emitMSFEdges`.
2. Runs `initPreprocessProg` to index raw edges, eliminate self-loops and parallel heavier edges,
   and compact isolated vertices (`n₀ ≤ 2 * m₀`).
3. Computes `r0 = Nat.iterLog 3 n₀` using `iterLogProg 3` (`memoryCost = 0`).
4. For small instances (`r0 < 24`), solves the preprocessed graph via Fredman–Tarjan
   (`denseCaseProg`) and lifts selected original MSF edges back to `Kruskal.encodeEdges`.
5. For large instances (`24 ≤ r0`), builds the canonical decision-tree table via `precomputeDTProg`,
   executes Borůvka–partition rounds (`boundedWhile` over `pr02LoopBodyProg` certified via
   `boundedWhile_potential_spec`), and finishes any remaining dense/small graph via `denseCaseProg`
   before emitting `Kruskal.encodeEdges`.

`realizes_optimalMSFProg` and `optimalMSF_wordRAM_spec` compile `optimalMSFProg` into a fixed,
width-blind (`¬prog.ReadsWidth`), random-free (`prog.IsRandFree`) `Program .standard` executing in
`O(optDepthMN m n + m + n + 1)` instructions (`ExecutesList`) on raw multigraphs (where
`optDepthMN` over simple graphs saturates once `m > n.choose 2`, and isolated vertices separately
account for the vertex overhead), while `optimalMSF_simpleGraph_isMST_spec` realizes Theorem 5.8
in `O(optDepthMN m n + 1)` instructions on connected simple graphs, certifying both
`IsMinSpanningForest (graphEdges G wt) msfEs` and `SimpleGraph.IsMST`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.optimalMSFWordBound`: polynomial workspace
  value threshold using `Nat.iterLog 3` (logarithmic word width suffices for this threshold,
  with an additional `Fits w` condition for edge weights; any larger width `w` is allowed).
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSFArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encOptimalMSFArgs`: 2-word input descriptor
  `[numVertices, numEdges]` matching words `0, 1` of `Kruskal.encode`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.optimalMSFProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.optimalMSFSafe`: top-level Word-RAM MSF program
  over `Memory.Prog` and its native safety predicate.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_optimalMSFProg`: uniform
  `Realizes .exact` compilation certificate for `optimalMSFProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.optimalMSFProg_spec`: functional correctness and
  `O(optDepthMN m n + m + n + 1)` memory-cost bound for `optimalMSFProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.optimalMSF_wordRAM_spec`: width-blind,
  random-free `Program .standard` driver theorem executing in `O(optDepthMN m n + m + n + 1)`
  instructions (`ExecutesList`) on raw multigraphs (`IsMinSpanningForest`).
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.isMST_toSimpleGraph_of_isMinSpanningForest`:
  bridge from `IsMinSpanningForest` to Mathlib `SimpleGraph.IsMST` on connected graphs.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.optimalMSF_simpleGraph_isMST_spec`: Theorem 5.8
  of [PettieRamachandran2002] (Section 5.1, p. 27, #8624) on connected simple graphs
  (`IsMinSpanningForest` and `SimpleGraph.IsMST`) in `O(optDepthMN m n + 1)` `Program .standard`
  instructions.

## References

* [PettieRamachandran2002]: Seth Pettie and Vijaya Ramachandran, "An Optimal Minimum Spanning
  Tree Algorithm", *JACM* 49(1), 2002, Section 2.1 (p. 18), Section 2.3 (pp. 19–20), Section 3.2
  (pp. 21–22), Section 4.1 (p. 23), Section 5 (pp. 23–24), and Section 5.1 (pp. 25–27,
  Theorem 5.8 p. 27).
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Algorithms.WordRAM.Kruskal
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase

/-! ## Section 1: Public Word-Width Bound and Input Record -/

/-- Polynomial workspace value threshold for `optimalMSFProg` on `n` vertices and `m` edges:
`10000 * m + 60000 * n + 2 * m * max 1 (Nat.iterLog 3 n) + 200000`. Logarithmic word width
`w = O(log (m * max 1 (Nat.iterLog 3 n) + n + 1))` suffices to satisfy
`Fits w (optimalMSFWordBound n m)` (with an additional `∀ e ∈ es, Fits w e.weight` condition
for edge weights), and the driver theorems allow any larger word width `w`. -/
@[expose] def optimalMSFWordBound (n m : ℕ) : ℕ :=
  10000 * m + 60000 * n + 2 * m * max 1 (Nat.iterLog 3 n) + 200000

/-- Public argument record `[numVertices, numEdges]` for `optimalMSFProg`, matching words `0` and
`1` of `Kruskal.encode`. -/
structure OptimalMSFArgs where
  /-- Number of input vertices `n`. -/
  numVertices : ℕ
  /-- Number of stride-3 raw input edges `m`. -/
  numEdges : ℕ
  deriving DecidableEq

/-- Faithful 2-word encoding of `OptimalMSFArgs` as `[numVertices, numEdges]`. -/
word_enc_structure encOptimalMSFArgs : OptimalMSFArgs where
  numVertices : wordWords,
  numEdges : wordWords

/-- Registered `WordEncoding` instance for `OptimalMSFArgs`. -/
instance : WordEncoding OptimalMSFArgs := ⟨2, encOptimalMSFArgs⟩

/-! ## Section 2: Private Subroutines, Argument Records, and Safety Helpers -/

private theorem optimalMSFWordBound_ge (n m : ℕ) :
    10000 * m + 60000 * n + 200000 ≤ optimalMSFWordBound n m := by
  unfold optimalMSFWordBound; omega

private structure OptimalMSFFinishArgs where
  selBuf : ℕ
  numVerts : ℕ
  numEdges : ℕ
  edgeBase : ℕ
  selLen : ℕ
  deriving DecidableEq

private word_enc_structure encOptimalMSFFinishArgs : OptimalMSFFinishArgs where
  selBuf : wordWords,
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  selLen : wordWords

private instance : WordEncoding OptimalMSFFinishArgs := ⟨5, encOptimalMSFFinishArgs⟩

private structure OptimalMSFBranchArgs where
  origNumEdges : ℕ
  numVerts : ℕ
  numEdges : ℕ
  edgeBase : ℕ
  deriving DecidableEq

private word_enc_structure encOptimalMSFBranchArgs : OptimalMSFBranchArgs where
  origNumEdges : wordWords,
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords

private instance : WordEncoding OptimalMSFBranchArgs := ⟨4, encOptimalMSFBranchArgs⟩

private structure OptimalMSFBranchBArgs where
  origNumEdges : ℕ
  numVerts : ℕ
  numEdges : ℕ
  edgeBase : ℕ
  r0 : ℕ
  deriving DecidableEq

private word_enc_structure encOptimalMSFBranchBArgs : OptimalMSFBranchBArgs where
  origNumEdges : wordWords,
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  r0 : wordWords

private instance : WordEncoding OptimalMSFBranchBArgs := ⟨5, encOptimalMSFBranchBArgs⟩

private def emitMSFEdgesSafe (w : ℕ) (d : SelectedEdgesArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ d.selBase + d.count ≤ s.frontier ∧
  Fits w (s.frontier + (3 * d.count + 1)) ∧
  ∀ j < d.count, d.srcBase + 3 * s.mem (d.selBase + j) + 3 ≤ s.frontier

private theorem realizes_emitMSFEdges' :
    Realizes .exact emitMSFEdges WordEncoding.encode WordEncoding.encode
      emitMSFEdgesSafe (fun _ _ => 0) :=
  realizes_emitMSFEdges

private def denseCaseSafe (w : ℕ) (g : GraphSlice) (s : Memory.State) : Prop :=
  Fits w 16 ∧ g.edgeBase + 4 * g.numEdges ≤ s.frontier ∧
  Fits w (s.frontier + (21 * g.numEdges + 8 * g.numVertices +
    76 * g.numEdges * Nat.iterClogBeta ((2 * g.numEdges) / g.numVertices) g.numVertices + 3)) ∧
  ∀ j < g.numEdges,
    s.mem (g.edgeBase + 4 * j) < g.numVertices ∧
    s.mem (g.edgeBase + 4 * j + 1) < g.numVertices

private theorem realizes_denseCaseProg' :
    Realizes .exact denseCaseProg WordEncoding.encode WordEncoding.encode
      denseCaseSafe (fun _ _ => 0) :=
  realizes_denseCaseProg

private theorem edgePartitionFrom_eq_of_all_self {n : ℕ} {W : Type}
    (p : DisjointSet.Partition n) (es : List (WeightedEdge n W))
    (hself : ∀ e ∈ es, e.u = e.v) :
    edgePartitionFrom p es = p := by
  induction es generalizing p with
  | nil => rfl
  | cons e rest ih =>
    rw [edgePartitionFrom_cons, hself e List.mem_cons_self, DisjointSet.Partition.merge_self]
    exact ih p (fun f hf => hself f (List.mem_cons_of_mem _ hf))

private theorem isMinSpanningForest_nil_of_all_self {n : ℕ} (es : List (WeightedEdge n ℕ))
    (hself : ∀ e ∈ es, e.u = e.v) : IsMinSpanningForest es [] := by
  refine ⟨⟨List.nil_subperm, isAcyclic_nil, ?_⟩, fun _ _ => Nat.zero_le _⟩
  rw [edgePartition, edgePartition, edgePartitionFrom_nil,
    edgePartitionFrom_eq_of_all_self _ es hself]

private theorem realizes_consequence_of {B : Basis} {α δ : Type} {k l : ℕ}
    {p : δ → Memory.Prog α} {input : δ ↪ (Fin k → ℕ)} {output : α ↪ (Fin l → ℕ)}
    {safe safe' : ℕ → δ → Memory.State → Prop} {work work' : δ → Memory.State → ℕ}
    (h : Realizes B p input output safe work)
    (hsafe : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (p d)) →
      safe' w d s → safe w d s)
    (hwork : ∀ w d s, (∀ i, Fits w (input d i)) → Memory.WellFormed w s →
      safe' w d s → work d s ≤ work' d s) :
    Realizes B p input output safe' work' := by
  obtain ⟨n, C, emit, he⟩ := h
  refine ⟨n, C, emit, he.consequence_of hsafe fun hwords hmem _ hs' hy => ?_⟩
  exact hy.mono (Nat.mul_le_mul_left C (by have := hwork _ _ _ hwords hmem hs'; omega))

private theorem allocDirty_state_props {w len : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hfit : Fits w (s.frontier + len)) :
    (Memory.spec 0).clientResult s (Memory.allocDirty len) = s.frontier ∧
    ((Memory.spec 0).clientState s (Memory.allocDirty len)).frontier = s.frontier + len ∧
    ((Memory.spec 0).clientState s (Memory.allocDirty len)).mem = s.mem ∧
    Memory.WellFormed w ((Memory.spec 0).clientState s (Memory.allocDirty len)) := by
  have hs : (Memory.spec 0).clientState s (Memory.allocDirty len) = ⟨s.mem, s.frontier + len⟩ :=
    clientState_allocDirty 0 s len
  refine ⟨by simp, by rw [hs], by rw [hs], ?_⟩
  rw [hs]
  exact ⟨hfit, hwf.mem_fits⟩

private theorem realizes_iterLog3 : Realizes .exact
    (fun x : ℕ => iterLogProg 3 x) WordEncoding.encode WordEncoding.encode
    (fun w _ _ => Fits w 3) (fun x _ => 3 * (Nat.log 2 x + 3)) := by
  have hraw : Realizes .exact (fun x : ℕ => (fun p : ℕ × ℕ => iterLogProg p.1 p.2) (3, x))
      WordEncoding.encode WordEncoding.encode
      (fun w _ _ => Fits w 3) (fun x _ => 3 * (Nat.log 2 x + 3)) := by
    realize [realizes_iterLogProg]
    all_goals
      have h3 := h
      exact h3.of_le (by decide)
  exact hraw

/-! ## Section 3: Private Finish Stage (`optimalMSFFinishProg`) -/

private def optimalMSFFinishProg (a : OptimalMSFFinishArgs) : Memory.Prog ℕ :=
  if a.numEdges = 0 then emitMSFEdges ⟨3, a.selBuf, a.selLen⟩
  else do
    let dc ← denseCaseProg ⟨a.numVerts, a.numEdges, a.edgeBase⟩
    let tot ← appendSelIdsProg ⟨dc.edgeBase, a.selBuf, a.selLen, dc.numEdges⟩
    emitMSFEdges ⟨3, a.selBuf, tot⟩

private def optimalMSFFinishProgSafe (w : ℕ) (a : OptimalMSFFinishArgs)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (a.selLen + 1) ∧
  (a.numEdges = 0 → emitMSFEdgesSafe w ⟨3, a.selBuf, a.selLen⟩ s) ∧
  (a.numEdges ≠ 0 →
    denseCaseSafe w ⟨a.numVerts, a.numEdges, a.edgeBase⟩ s ∧
    let dc := (Memory.spec 0).clientResult s (denseCaseProg ⟨a.numVerts, a.numEdges, a.edgeBase⟩)
    let s₁ := (Memory.spec 0).clientState s (denseCaseProg ⟨a.numVerts, a.numEdges, a.edgeBase⟩)
    appendSelIdsProgSafe w ⟨dc.edgeBase, a.selBuf, a.selLen, dc.numEdges⟩ s₁ ∧
    let tot := (Memory.spec 0).clientResult s₁
      (appendSelIdsProg ⟨dc.edgeBase, a.selBuf, a.selLen, dc.numEdges⟩)
    let s₂ := (Memory.spec 0).clientState s₁
      (appendSelIdsProg ⟨dc.edgeBase, a.selBuf, a.selLen, dc.numEdges⟩)
    emitMSFEdgesSafe w ⟨3, a.selBuf, tot⟩ s₂)

private theorem realizes_optimalMSFFinishProg : Realizes .exact
    optimalMSFFinishProg WordEncoding.encode WordEncoding.encode
    optimalMSFFinishProgSafe (fun _ _ => 0) := by
  unfold optimalMSFFinishProg
  realize [realizes_emitMSFEdges', realizes_denseCaseProg', realizes_appendSelIdsProg]
  all_goals first
    | exact h.2.2.1 (by assumption)
    | exact h.2.2.2 (by assumption) |>.1
    | exact h.2.2.2 (by assumption) |>.2.1
    | exact h.2.2.2 (by assumption) |>.2.2
    | (have h16 := h.1; have hfront := hmem.frontier_fits; fits)

private theorem optimalMSFFinishProg_spec {w nOrig n₀ nEnd r0 selBuf ebEnd selLen : ℕ}
    {es : List (WeightedEdge nOrig ℕ)} {accIds : List (Fin es.length)}
    {esEnd : List (IndexedEdge nEnd)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn_le_n0 : nEnd ≤ n₀) (hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0)
    (hdense_cond : esEnd.length = 0 ∨ nEnd ≤ 64 ∨ nEnd * r0 ≤ 2 * esEnd.length)
    (hraw : HoldsEdges 3 es s.mem)
    (hraw_sel : 3 + 3 * es.length ≤ selBuf)
    (hsel_fr : selBuf + es.length ≤ s.frontier)
    (hacc_len : accIds.length = selLen)
    (hacc_mem : ∀ j (hj : j < accIds.length), s.mem (selBuf + j) = accIds[j].val)
    (hes_holds : HoldsIndexedEdges ebEnd esEnd s.mem)
    (hes_fr : ebEnd + 4 * esEnd.length ≤ s.frontier)
    (hinv : MSFLiftInv es accIds esEnd)
    (hfit : Fits w (s.frontier + 3365 * esEnd.length + 8 * nEnd + 3 * es.length + 97290)) :
    let st : OptimalMSFFinishArgs := ⟨selBuf, nEnd, esEnd.length, ebEnd, selLen⟩
    let prog := optimalMSFFinishProg st
    let outBase := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    optimalMSFFinishProgSafe w st s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    ∃ msfEs : List (WeightedEdge nOrig ℕ),
      IsMinSpanningForest es msfEs ∧
      msfEs.length ≤ es.length ∧
      outputList s'.mem outBase = Kruskal.encodeEdges msfEs ∧
      Fits w (outBase + 3 * msfEs.length) ∧
      memoryCost prog s ≤ 39188 * es.length + 18 * nEnd + 1137940 := by
  have hsum_le := hinv.sum_le
  have hfit_sel1 : Fits w (selLen + 1) := hfit.of_le (by omega)
  by_cases hm0 : esEnd.length = 0
  · have hnil : esEnd = [] := List.eq_nil_of_length_eq_zero hm0
    have hmsf_nil : IsMinSpanningForest (esEnd.map IndexedEdge.toWeighted)
        (([] : List (IndexedEdge nEnd)).map IndexedEdge.toWeighted) := by
      rw [hnil]
      exact ⟨⟨List.nil_subperm, isAcyclic_nil, rfl⟩, fun _ _ => Nat.zero_le _⟩
    obtain ⟨remIds, hrem_val, hrem_msf⟩ := hinv.2.2.2.2 [] List.nil_subperm hmsf_nil
    have hrem_nil : remIds = [] := by cases remIds <;> simp at hrem_val; rfl
    subst hrem_nil
    simp only [List.append_nil] at hrem_msf
    have hs_raw_fr : 3 + 3 * es.length ≤ s.frontier := by omega
    have hfit_emit : Fits w (s.frontier + (3 * accIds.length + 1)) := hfit.of_le (by omega)
    have hsrc_lt : ∀ j < accIds.length, 3 + 3 * s.mem (selBuf + j) + 3 ≤ s.frontier :=
      fun j hj => by rw [hacc_mem j hj]; have := accIds[j].isLt; omega
    have hemit := framedTriple_iff_realization.mp (emitMSFEdges_spec (w := w) (n := nOrig)
      (d := ⟨3, selBuf, accIds.length⟩) (es := es) (selIds := accIds) (s := s)
      h16 hwf hraw hs_raw_fr hacc_mem (by dsimp only; omega) rfl hfit_emit)
    dsimp only at hemit
    rw [hacc_len] at hemit
    rcases hemit with ⟨hv_e, hc_e, _, hout_eq, _, _, hout_list⟩
    have hsafe_e : emitMSFEdgesSafe w ⟨3, selBuf, selLen⟩ s :=
      ⟨h16, by dsimp only; omega, by dsimp only; rw [← hacc_len]; exact hfit_emit,
        fun j hj => by dsimp only at hj ⊢; rw [← hacc_len] at hj; exact hsrc_lt j hj⟩
    have hprog : optimalMSFFinishProg ⟨selBuf, nEnd, esEnd.length, ebEnd, selLen⟩ =
        emitMSFEdges ⟨3, selBuf, selLen⟩ := by simp [optimalMSFFinishProg, hm0]
    refine ⟨⟨h16, hfit_sel1, fun _ => hsafe_e, fun h => absurd hm0 h⟩, ?_,
      accIds.map fun i => es[i.val], hrem_msf, by simp only [List.length_map]; omega, ?_, ?_, ?_⟩
    · rw [hprog]; exact hv_e
    · rw [hprog, hout_list]
    · rw [hprog, hout_eq]; exact hfit.of_le (by simp only [List.length_map]; omega)
    · rw [hprog]; omega
  · have hm_pos : 0 < esEnd.length := Nat.pos_of_ne_zero hm0
    have hprog : optimalMSFFinishProg ⟨selBuf, nEnd, esEnd.length, ebEnd, selLen⟩ =
        (denseCaseProg ⟨nEnd, esEnd.length, ebEnd⟩ >>= fun dc =>
          appendSelIdsProg ⟨dc.edgeBase, selBuf, selLen, dc.numEdges⟩ >>= fun tot =>
          emitMSFEdges ⟨3, selBuf, tot⟩) := by
      simp [optimalMSFFinishProg, hm0]
    have hes_bd : ∀ j < esEnd.length,
        s.mem (ebEnd + 4 * j) < nEnd ∧ s.mem (ebEnd + 4 * j + 1) < nEnd := fun j hj => by
      obtain ⟨hu, hv, _, _⟩ := hes_holds j hj
      exact ⟨hu ▸ (esEnd[j]'hj).u.isLt, hv ▸ (esEnd[j]'hj).v.isLt⟩
    have hdc_bound :
        ∃ (hsafe1 : denseCaseSafe w ⟨nEnd, esEnd.length, ebEnd⟩ s)
          (hv1 : (Memory.spec w).ValidHistory s
            ((Memory.spec w).clientHistory s (denseCaseProg ⟨nEnd, esEnd.length, ebEnd⟩))),
          let dc := (Memory.spec 0).clientResult s (denseCaseProg ⟨nEnd, esEnd.length, ebEnd⟩)
          let s₁ := (Memory.spec 0).clientState s (denseCaseProg ⟨nEnd, esEnd.length, ebEnd⟩)
          s.frontier ≤ dc.edgeBase ∧
          dc.edgeBase + 4 * dc.numEdges ≤ s₁.frontier ∧
          s₁.frontier ≤ s.frontier + 3365 * esEnd.length + 8 * nEnd + 97283 ∧
          Memory.WellFormed w s₁ ∧
          (∀ a < s.frontier, s₁.mem a = s.mem a) ∧
          (∃ msfEs : List (IndexedEdge nEnd),
            msfEs.length = dc.numEdges ∧ HoldsIndexedEdges dc.edgeBase msfEs s₁.mem ∧
            msfEs.Subperm esEnd ∧
            IsMinSpanningForest (esEnd.map IndexedEdge.toWeighted)
              (msfEs.map IndexedEdge.toWeighted)) ∧
          memoryCost (denseCaseProg ⟨nEnd, esEnd.length, ebEnd⟩) s ≤
            39178 * esEnd.length + 18 * nEnd + 1137931 := by
      rcases hdense_cond with h0 | hn64 | hdense
      · exact absurd h0 hm0
      · have hlog64 : Nat.iterLog 3 nEnd ≤ 1 := by
          have h1 : Nat.iterLog 3 nEnd ≤ Nat.iterLog 3 64 := Nat.iterLog_mono 3 hn64
          have h64_eq : Nat.iterLog 3 64 = 1 := by decide
          omega
        have hbeta_le : esEnd.length * Nat.iterClogBeta ((2 * esEnd.length) / nEnd) nEnd ≤
            4 * esEnd.length + 1280 := by
          have h := Nat.mul_iterClogBeta_div_le_iterLog (by decide : 1 ≤ 3) esEnd.length nEnd
          simp only [Nat.reduceAdd, Nat.reduceMul, Nat.mul_assoc] at h
          have hm1 : max 1 (Nat.iterLog 3 nEnd) = 1 := by omega
          rw [hm1, Nat.mul_one] at h
          have hn1280 : 20 * nEnd ≤ 1280 := by omega
          omega
        have hfit_dc : Fits w (s.frontier +
            (21 * esEnd.length + 8 * nEnd +
              76 * esEnd.length * Nat.iterClogBeta ((2 * esEnd.length) / nEnd) nEnd + 3)) :=
          hfit.of_le (by rw [Nat.mul_assoc 76]; omega)
        have hspec := framedTriple_iff_realization.mp
          (denseCaseProg_spec h16 hwf hes_holds hes_fr hfit_dc)
        rcases hspec with ⟨hv1, hc1, hmod1, _, hdc_ge, hdc_fr, hs1_fr, hwf1, hmsf1⟩
        refine ⟨⟨h16, hes_fr, hfit_dc, hes_bd⟩, hv1, hdc_ge, hdc_fr, ?_, hwf1,
          fun a ha => hmod1.mem_eq_of_not_mem ha (Set.notMem_empty _), hmsf1, ?_⟩
        · rw [Nat.mul_assoc 76] at hs1_fr; omega
        · rw [Nat.mul_assoc 889] at hc1; omega
      · have hdense' : nEnd * max 1 (Nat.iterLog 3 n₀) ≤ 2 * esEnd.length :=
          (Nat.mul_le_mul_left nEnd hr0_log).trans hdense
        have hfit_dc : Fits w (s.frontier + (3365 * esEnd.length + 8 * nEnd + 3)) :=
          hfit.of_le (by omega)
        have hspec := framedTriple_iff_realization.mp
          (denseCaseProg_spec_of_dense h16 hwf hn_le_n0 hdense' hes_holds hes_fr hfit_dc)
        rcases hspec with ⟨hv1, hc1, hmod1, _, hdc_ge, hdc_fr, hs1_fr, hwf1, hmsf1⟩
        have hfit_safe : Fits w (s.frontier + (21 * esEnd.length + 8 * nEnd +
            76 * esEnd.length * Nat.iterClogBeta ((2 * esEnd.length) / nEnd) nEnd + 3)) := by
          have hiter_mono : Nat.iterLog 3 nEnd ≤ Nat.iterLog 3 n₀ := Nat.iterLog_mono 3 hn_le_n0
          have hmax_le : max 1 (Nat.iterLog 3 nEnd) ≤ max 1 (Nat.iterLog 3 n₀) :=
            max_le_max le_rfl hiter_mono
          have hft := Nat.mul_iterClogBeta_div_le_iterLog (by decide : 1 ≤ 3) esEnd.length nEnd
          simp only [Nat.reduceAdd, Nat.reduceMul, Nat.mul_assoc] at hft
          have hmul_iter : nEnd * max 1 (Nat.iterLog 3 nEnd) ≤ 2 * esEnd.length :=
            (Nat.mul_le_mul_left nEnd hmax_le).trans hdense'
          have hle44 : esEnd.length * Nat.iterClogBeta ((2 * esEnd.length) / nEnd) nEnd ≤
              44 * esEnd.length := by omega
          exact hfit_dc.of_le (by rw [Nat.mul_assoc 76]; omega)
        refine ⟨⟨h16, hes_fr, hfit_safe, hes_bd⟩, hv1, hdc_ge, hdc_fr, by omega, hwf1,
          fun a ha => hmod1.mem_eq_of_not_mem ha (Set.notMem_empty _), hmsf1, by omega⟩
    dsimp only at hdc_bound
    generalize h_dc : (Memory.spec 0).clientResult s
      (denseCaseProg ⟨nEnd, esEnd.length, ebEnd⟩) = dc at hdc_bound
    generalize h_s1 : (Memory.spec 0).clientState s
      (denseCaseProg ⟨nEnd, esEnd.length, ebEnd⟩) = s₁ at hdc_bound
    rcases hdc_bound with ⟨hsafe1, hv1, hdc1_ge_s, hdc_fr, hs1_fr, hwf1, hmod1,
      ⟨msfSub, hmsf_len, hmsf_holds, hmsf_sub, hmsf_msf⟩, hc1⟩
    obtain ⟨remIds, hrem_val, hrem_msf⟩ := hinv.2.2.2.2 msfSub hmsf_sub hmsf_msf
    have hrem_len : remIds.length = dc.numEdges := by
      have h1 := congrArg List.length hrem_val
      simp only [List.length_map] at h1
      omega
    have htot_le : accIds.length + remIds.length ≤ es.length := by
      have hm_le := hmsf_sub.length_le
      omega
    have hs_le_s1 : s.frontier ≤ s₁.frontier := by omega
    have h2 := framedTriple_iff_realization.mp
      (@appendSelIdsProg_spec w nEnd dc.edgeBase selBuf selLen msfSub s₁ h16 hwf1 hmsf_holds
        (by omega) (by omega) (Or.inr (by omega)))
    generalize h_tot : (Memory.spec 0).clientResult s₁
      (appendSelIdsProg ⟨dc.edgeBase, selBuf, selLen, msfSub.length⟩) = tot at h2
    generalize h_s2 : (Memory.spec 0).clientState s₁
      (appendSelIdsProg ⟨dc.edgeBase, selBuf, selLen, msfSub.length⟩) = s₂ at h2
    rcases h2 with ⟨hv2, hc2, hmod2, htot_eq, hs2_fr, hwf2, hset2⟩
    have hsafe2 : appendSelIdsProgSafe w ⟨dc.edgeBase, selBuf, selLen, msfSub.length⟩ s₁ :=
      ⟨h16, by dsimp only; omega, by dsimp only; omega⟩
    let allIds : List (Fin es.length) := accIds ++ remIds
    have hall_len : allIds.length = tot := by
      dsimp only [allIds]; rw [List.length_append, hacc_len, hrem_len, htot_eq, hmsf_len]
    have hraw2 : HoldsEdges 3 es s₂.mem :=
      holdsEdges_frame (holdsEdges_frame hraw fun a ha1 ha2 => hmod1 a (by omega))
        fun a ha1 ha2 => hmod2.mem_eq_of_not_mem (by omega) (by simp only [Set.mem_Ico]; omega)
    have hall_mem : ∀ j (hj : j < allIds.length), s₂.mem (selBuf + j) = allIds[j].val := by
      intro j hj
      dsimp only [allIds] at hj ⊢
      by_cases hj1 : j < accIds.length
      · rw [List.getElem_append_left hj1]
        exact (hmod2.mem_eq_of_not_mem (by omega)
          (by simp only [Set.mem_Ico]; omega)).trans
          ((hmod1 _ (by omega)).trans (hacc_mem j hj1))
      · have hj2 : j - accIds.length < remIds.length := by
          rw [List.length_append] at hj; omega
        rw [List.getElem_append_right (Nat.le_of_not_lt hj1)]
        have hj_msf : j - accIds.length < msfSub.length := by omega
        have heq_mem : selBuf + j = selBuf + selLen + (j - accIds.length) := by omega
        rw [heq_mem, hset2 (j - accIds.length) hj_msf]
        have hget_m := List.getElem_of_eq hrem_val
          (show j - accIds.length < (remIds.map Fin.val).length by simp [hj2])
        simp only [List.getElem_map] at hget_m
        exact hget_m.symm
    have hfit_emit : Fits w (s₂.frontier + (3 * allIds.length + 1)) :=
      hfit.of_le (by rw [hs2_fr]; omega)
    have hsrc_lt2 : ∀ j < allIds.length, 3 + 3 * s₂.mem (selBuf + j) + 3 ≤ s₂.frontier := by
      intro j hj
      rw [hall_mem j hj]
      have := allIds[j].isLt
      rw [hs2_fr]; omega
    have h3 := framedTriple_iff_realization.mp
      (emitMSFEdges_spec (w := w) (n := nOrig) (d := ⟨3, selBuf, allIds.length⟩) (es := es)
        (selIds := allIds) (s := s₂) h16 hwf2 hraw2 (by dsimp only; rw [hs2_fr]; omega) hall_mem
        (by dsimp only; rw [hs2_fr]; omega) rfl hfit_emit)
    dsimp only at h3
    rcases h3 with ⟨hv3, hc3, _, hout_eq, _, _, hout_list⟩
    have hsafe3 : emitMSFEdgesSafe w ⟨3, selBuf, allIds.length⟩ s₂ :=
      ⟨h16, by dsimp only; rw [hs2_fr]; omega, hfit_emit, hsrc_lt2⟩
    rw [hmsf_len] at h_tot h_s2 hsafe2 hv2 hc2
    rw [hall_len] at hv3 hsafe3 hout_eq hout_list hc3
    refine ⟨⟨h16, hfit_sel1, fun h => absurd h hm0, fun _ => ?_⟩, ?_, ?_⟩
    · dsimp only
      rw [h_dc, h_s1]
      refine ⟨hsafe1, hsafe2, ?_⟩
      rw [h_tot, h_s2]
      exact hsafe3
    · rw [hprog]
      refine validHistory_bind_step hv1 ?_
      rw [h_dc, h_s1]
      refine validHistory_bind_step hv2 ?_
      rw [h_tot, h_s2]
      exact hv3
    · refine ⟨allIds.map fun i => es[i.val], hrem_msf, by simp [allIds, htot_le], ?_, ?_, ?_⟩
      · rw [hprog, StateTransitionSpec.clientResult_bind, h_dc, h_s1,
          StateTransitionSpec.clientResult_bind, h_tot, h_s2,
          StateTransitionSpec.clientState_bind, h_dc, h_s1,
          StateTransitionSpec.clientState_bind, h_tot, h_s2, hout_list]
      · rw [hprog, StateTransitionSpec.clientResult_bind, h_dc, h_s1,
          StateTransitionSpec.clientResult_bind, h_tot, h_s2, hout_eq, hs2_fr]
        exact hfit.of_le (by simp only [List.length_map]; omega)
      · rw [hprog, memoryCost_bind', h_dc, h_s1, memoryCost_bind', h_tot, h_s2]
        omega

/-! ## Section 4: Private Small-Vertex (`optimalMSFBranchA`) & Large-Vertex (`optimalMSFBranchB`) -/

private def optimalMSFBranchA (a : OptimalMSFBranchArgs) : Memory.Prog ℕ := do
  let dc ← denseCaseProg ⟨a.numVerts, a.numEdges, a.edgeBase⟩
  let selBuf ← Memory.allocDirty a.origNumEdges
  let _ ← appendSelIdsProg ⟨dc.edgeBase, selBuf, 0, dc.numEdges⟩
  emitMSFEdges ⟨3, selBuf, dc.numEdges⟩

private def optimalMSFBranchASafe (w : ℕ) (a : OptimalMSFBranchArgs)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w a.origNumEdges ∧
  denseCaseSafe w ⟨a.numVerts, a.numEdges, a.edgeBase⟩ s ∧
  let dc := (Memory.spec 0).clientResult s (denseCaseProg ⟨a.numVerts, a.numEdges, a.edgeBase⟩)
  let s₁ := (Memory.spec 0).clientState s (denseCaseProg ⟨a.numVerts, a.numEdges, a.edgeBase⟩)
  Fits w (s₁.frontier + a.origNumEdges) ∧
  let selBuf := s₁.frontier
  let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + a.origNumEdges⟩
  appendSelIdsProgSafe w ⟨dc.edgeBase, selBuf, 0, dc.numEdges⟩ s₂ ∧
  let s₃ := (Memory.spec 0).clientState s₂ (appendSelIdsProg ⟨dc.edgeBase, selBuf, 0, dc.numEdges⟩)
  emitMSFEdgesSafe w ⟨3, selBuf, dc.numEdges⟩ s₃

private theorem realizes_optimalMSFBranchA : Realizes .exact
    optimalMSFBranchA WordEncoding.encode WordEncoding.encode
    optimalMSFBranchASafe (fun _ _ => 0) := by
  unfold optimalMSFBranchA
  realize [realizes_denseCaseProg', realizes_appendSelIdsProg, realizes_emitMSFEdges']
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2.2.1
    | exact h.2.2.2.2.2
    | (have h16 := h.1; have hfront := hmem.frontier_fits; fits)

private theorem optimalMSFBranchA_spec {w nOrig n₀ edgeBase₀ : ℕ}
    {es : List (WeightedEdge nOrig ℕ)} {es₀ : List (IndexedEdge n₀)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn₀_le : n₀ ≤ nOrig) (hm₀_le : es₀.length ≤ es.length)
    (hr0_lt : Nat.iterLog 3 n₀ < 24)
    (hraw : HoldsEdges 3 es s.mem) (hraw_fr : 3 + 3 * es.length ≤ s.frontier)
    (hes0_holds : HoldsIndexedEdges edgeBase₀ es₀ s.mem)
    (hes0_fr : edgeBase₀ + 4 * es₀.length ≤ s.frontier)
    (hinv0 : MSFLiftInv es [] es₀)
    (hfit : Fits w (s.frontier + 329 * es.length + 34968 * nOrig + 4)) :
    let a : OptimalMSFBranchArgs := ⟨es.length, n₀, es₀.length, edgeBase₀⟩
    let prog := optimalMSFBranchA a
    let outBase := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    optimalMSFBranchASafe w a s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    ∃ msfEs : List (WeightedEdge nOrig ℕ),
      IsMinSpanningForest es msfEs ∧
      msfEs.length ≤ es.length ∧
      outputList s'.mem outBase = Kruskal.encodeEdges msfEs ∧
      Fits w (outBase + 3 * msfEs.length) ∧
      memoryCost prog s ≤ 3628 * es.length + 408958 * nOrig + 16 := by
  have hlog_le23 : Nat.iterLog 3 n₀ ≤ 23 := by omega
  have hbeta : es₀.length * Nat.iterClogBeta ((2 * es₀.length) / n₀) n₀ ≤
      4 * es₀.length + 460 * n₀ := by
    have h := Nat.mul_iterClogBeta_div_le_iterLog (by decide : 1 ≤ 3) es₀.length n₀
    simp only [Nat.reduceAdd, Nat.reduceMul, Nat.mul_assoc] at h
    have hm23 : max 1 (Nat.iterLog 3 n₀) ≤ 23 := by omega
    have hmul : 20 * (n₀ * max 1 (Nat.iterLog 3 n₀)) ≤ 20 * (n₀ * 23) :=
      Nat.mul_le_mul_left 20 (Nat.mul_le_mul_left n₀ hm23)
    omega
  have hfit_dc : Fits w (s.frontier +
      (21 * es₀.length + 8 * n₀ +
        76 * es₀.length * Nat.iterClogBeta ((2 * es₀.length) / n₀) n₀ + 3)) :=
    hfit.of_le (by rw [Nat.mul_assoc 76]; omega)
  have hes0_bd : ∀ j < es₀.length,
      s.mem (edgeBase₀ + 4 * j) < n₀ ∧ s.mem (edgeBase₀ + 4 * j + 1) < n₀ := fun j hj => by
    obtain ⟨hu, hv, _, _⟩ := hes0_holds j hj
    exact ⟨hu ▸ (es₀[j]'hj).u.isLt, hv ▸ (es₀[j]'hj).v.isLt⟩
  have h1ft := denseCaseProg_spec h16 hwf hes0_holds hes0_fr hfit_dc
  have h1 := framedTriple_iff_realization.mp h1ft
  generalize h_dc : (Memory.spec 0).clientResult s
    (denseCaseProg ⟨n₀, es₀.length, edgeBase₀⟩) = dc at h1
  generalize h_s1 : (Memory.spec 0).clientState s
    (denseCaseProg ⟨n₀, es₀.length, edgeBase₀⟩) = s₁ at h1
  rcases h1 with ⟨-, -, hmod1, _, hdc1_ge_s, hdc_fr, hs1_fr, hwf1,
    ⟨msf0, hmsf0_len, hmsf0_holds, hmsf0_sub, hmsf0_msf⟩⟩
  rw [Nat.mul_assoc 76] at hs1_fr
  obtain ⟨remIds, hrem_val, hrem_msf⟩ := hinv0.2.2.2.2 msf0 hmsf0_sub hmsf0_msf
  simp only [List.nil_append] at hrem_msf
  have hrem_len : remIds.length = dc.numEdges := by
    have h := congrArg List.length hrem_val
    simp only [List.length_map] at h
    omega
  have hdc2_le : dc.numEdges ≤ es.length := hmsf0_len ▸ (hmsf0_sub.length_le.trans hm₀_le)
  have hfit_alloc : Fits w (s₁.frontier + es.length) := hfit.of_le (by omega)
  have hs_le_s1 : s.frontier ≤ s₁.frontier := hmod1.1
  obtain ⟨hselBuf_eq, hs2_fr, hs2_mem, hwf2⟩ := allocDirty_state_props hwf1 hfit_alloc
  set selBuf := (Memory.spec 0).clientResult s₁ (Memory.allocDirty es.length)
  set s₂ := (Memory.spec 0).clientState s₁ (Memory.allocDirty es.length)
  have hmsf0_holds2 : HoldsIndexedEdges dc.edgeBase msf0 s₂.mem := by
    rw [hs2_mem]; exact hmsf0_holds
  have h2ft := @appendSelIdsProg_spec w n₀ dc.edgeBase selBuf 0 msf0 s₂ h16 hwf2 hmsf0_holds2
    (by omega) (by rw [hs2_fr, hselBuf_eq, hmsf0_len]; omega) (Or.inl (by rw [hselBuf_eq]; omega))
  have h2 := framedTriple_iff_realization.mp h2ft
  generalize h_s3 : (Memory.spec 0).clientState s₂
    (appendSelIdsProg ⟨dc.edgeBase, selBuf, 0, msf0.length⟩) = s₃ at h2
  rcases h2 with ⟨-, -, hmod2, _, hs3_fr, hwf3, hset3⟩
  have hsafe2 : appendSelIdsProgSafe w ⟨dc.edgeBase, selBuf, 0, msf0.length⟩ s₂ :=
    ⟨h16, by dsimp only; omega, by dsimp only; rw [hs2_fr, hselBuf_eq, hmsf0_len]; omega⟩
  have hraw3 : HoldsEdges 3 es s₃.mem :=
    holdsEdges_frame
      (holdsEdges_frame hraw fun a ha1 ha2 => hmod1.mem_eq_of_not_mem (by omega) (by simp))
      fun a ha1 ha2 => hmod2.mem_eq_of_not_mem (by rw [hs2_fr]; omega)
        (by simp only [Set.mem_Ico]; rw [hselBuf_eq]; omega)
  have hrem_mem3 : ∀ j (hj : j < remIds.length), s₃.mem (selBuf + j) = remIds[j].val := by
    intro j hj
    have hj_m : j < msf0.length := by omega
    have h0 := hset3 j hj_m
    simp only [Nat.add_zero] at h0
    rw [h0]
    have hget := List.getElem_of_eq hrem_val
      (show j < (remIds.map Fin.val).length by simp [hj])
    simp only [List.getElem_map] at hget
    exact hget.symm
  have hfit_emit : Fits w (s₃.frontier + (3 * remIds.length + 1)) :=
    hfit.of_le (by rw [hs3_fr, hs2_fr, hrem_len]; omega)
  have hsrc_lt3 : ∀ j < remIds.length, 3 + 3 * s₃.mem (selBuf + j) + 3 ≤ s₃.frontier := by
    intro j hj
    rw [hrem_mem3 j hj]
    have := remIds[j].isLt
    rw [hs3_fr, hs2_fr]; omega
  have h3ft := emitMSFEdges_spec (w := w) (n := nOrig) (d := ⟨3, selBuf, remIds.length⟩) (es := es)
    (selIds := remIds) (s := s₃) h16 hwf3 hraw3 (by dsimp only; rw [hs3_fr, hs2_fr]; omega)
    hrem_mem3 (by dsimp only; rw [hs3_fr, hs2_fr, hselBuf_eq, hrem_len]; omega) rfl hfit_emit
  have hsafe3 : emitMSFEdgesSafe w ⟨3, selBuf, remIds.length⟩ s₃ :=
    ⟨h16, by dsimp only; rw [hs3_fr, hs2_fr, hselBuf_eq, hrem_len]; omega, hfit_emit, hsrc_lt3⟩
  have hs2_eq : s₂ = ⟨s₁.mem, s₁.frontier + es.length⟩ := by rw [← hs2_mem, ← hs2_fr]
  have h889 : 889 * es₀.length * Nat.iterClogBeta ((2 * es₀.length) / n₀) n₀ ≤
      889 * (4 * es₀.length + 460 * n₀) := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hbeta
  have hft : Memory.FramedTriple w s (optimalMSFBranchA ⟨es.length, n₀, es₀.length, edgeBase₀⟩)
      (3628 * es.length + 408958 * nOrig + 16) Set.univ fun outBase s' =>
        outputList s'.mem outBase = Kruskal.encodeEdges (remIds.map fun i => es[i.val]) ∧
        Fits w (outBase + 3 * (remIds.map fun i => es[i.val]).length) := by
    unfold optimalMSFBranchA
    eapply Memory.FramedTriple.mono (hQ := fun _ _ => id)
    · eapply Memory.FramedTriple.seq (h1ft.frame_mono (Set.subset_univ _)) subset_rfl
      on_goal 1 => rw [h_dc, h_s1]
      eapply Memory.FramedTriple.allocDirty_bind hfit_alloc
      on_goal 1 => rw [← hs2_eq, ← hselBuf_eq, ← hmsf0_len]
      eapply Memory.FramedTriple.seq (h2ft.frame_mono (Set.subset_univ _)) subset_rfl
      on_goal 1 => rw [h_s3, hmsf0_len, ← hrem_len]
      exact (h3ft.frame_mono (Set.subset_univ _)).mono le_rfl fun _ _ ⟨hout, _, _, hlist⟩ =>
        ⟨hlist, hout ▸ hfit.of_le (by simp only [List.length_map]; omega)⟩
    · dsimp only; omega
  obtain ⟨hv, hc, -, hlist, hfit_out⟩ := framedTriple_iff_realization.mp hft
  rw [hmsf0_len] at h_s3 hsafe2
  rw [hrem_len] at hsafe3
  refine ⟨⟨h16, hfit.of_le (by dsimp only; omega), ⟨h16, hes0_fr, hfit_dc, hes0_bd⟩, ?_⟩, hv,
    remIds.map fun i => es[i.val], hrem_msf, by simp [hrem_len, hdc2_le], hlist, hfit_out, hc⟩
  dsimp only
  rw [h_dc, h_s1]
  refine ⟨hfit_alloc, ?_⟩
  rw [← hs2_eq, ← hselBuf_eq]
  refine ⟨hsafe2, ?_⟩
  rw [h_s3]
  exact hsafe3

private def optimalMSFBranchB (a : OptimalMSFBranchBArgs) : Memory.Prog ℕ := do
  let tableBase ← precomputeDTProg a.r0
  let selBuf ← Memory.allocDirty a.origNumEdges
  let stFin ← boundedWhile (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
    pr02LoopBodyProg ⟨a.r0, tableBase, selBuf⟩ (a.origNumEdges + 1)
    ⟨1, a.numVerts, a.numEdges, a.edgeBase, 0⟩
  optimalMSFFinishProg ⟨selBuf, stFin.numVerts, stFin.numEdges, stFin.edgeBase, stFin.selLen⟩

private def optimalMSFBranchBSafe (w : ℕ) (a : OptimalMSFBranchBArgs)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w a.origNumEdges ∧ Fits w a.r0 ∧ Fits w a.numVerts ∧ Fits w a.numEdges ∧
  Fits w a.edgeBase ∧
  precomputeDTProgSafe w a.r0 s ∧
  let tableBase := (Memory.spec 0).clientResult s (precomputeDTProg a.r0)
  let s₁ := (Memory.spec 0).clientState s (precomputeDTProg a.r0)
  Fits w (s₁.frontier + a.origNumEdges) ∧
  let env : PR02LoopEnv := ⟨a.r0, tableBase, s₁.frontier⟩
  let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + a.origNumEdges⟩
  let st₀ : PR02LoopState := ⟨1, a.numVerts, a.numEdges, a.edgeBase, 0⟩
  whileSafe (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
    pr02LoopBodyProg pr02LoopBodyProgSafe w env (a.origNumEdges + 1) st₀ s₂ ∧
  let stFin := (Memory.spec 0).clientResult s₂
    (boundedWhile (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
      pr02LoopBodyProg env (a.origNumEdges + 1) st₀)
  let s₃ := (Memory.spec 0).clientState s₂
    (boundedWhile (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
      pr02LoopBodyProg env (a.origNumEdges + 1) st₀)
  optimalMSFFinishProgSafe w
    ⟨s₁.frontier, stFin.numVerts, stFin.numEdges, stFin.edgeBase, stFin.selLen⟩ s₃

private theorem realizes_optimalMSFBranchB : Realizes .exact
    optimalMSFBranchB WordEncoding.encode WordEncoding.encode
    optimalMSFBranchBSafe (fun a _ => a.origNumEdges + 1) := by
  have hraw : Realizes .exact optimalMSFBranchB WordEncoding.encode WordEncoding.encode
      optimalMSFBranchBSafe
      (fun a s =>
        let tableBase := (Memory.spec 0).clientResult s (precomputeDTProg a.r0)
        let s₁ := (Memory.spec 0).clientState s (precomputeDTProg a.r0)
        let env : PR02LoopEnv := ⟨a.r0, tableBase, s₁.frontier⟩
        let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + a.origNumEdges⟩
        let st₀ : PR02LoopState := ⟨1, a.numVerts, a.numEdges, a.edgeBase, 0⟩
        whileWork (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
          pr02LoopBodyProg (fun _ _ => 0) env (a.origNumEdges + 1) st₀ s₂) := by
    unfold optimalMSFBranchB
    realize [realizes_precomputeDTProg, realizes_pr02LoopBodyProg, realizes_optimalMSFFinishProg]
    · exact h.2.2.2.2.2.2.1
    · have h16 := h.1; have hfront := hmem.frontier_fits; have h1 := h.2.1
      have h2 := h.2.2.1; have h3 := h.2.2.2.1; have h4 := h.2.2.2.2.1
      have h5 := h.2.2.2.2.2.1; have h6 := h.2.2.2.2.2.2.2.1
      fits
    · intro _
      have hws := h.2.2.2.2.2.2.2.2.1
      let env : PR02LoopEnv :=
        ⟨d.r0, (Memory.spec 0).clientResult s (precomputeDTProg d.r0),
          ((Memory.spec 0).clientState s (precomputeDTProg d.r0)).frontier⟩
      exact whileSafe_imp (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
        (fun (_ : PR02LoopEnv) (st : PR02LoopState) => 0 < st.cont)
        (safe := pr02LoopBodyProgSafe)
        (safe' := fun w x s' => pr02LoopBodyProgSafe w (env, x.2) s')
        (fun _ => Iff.rfl) (fun _ => rfl) (fun _ _ _ hs => hs) hws
    · exact h.2.2.2.2.2.2.2.2.2
  refine hraw.consequence (fun _ _ _ _ _ h => h) fun a s => ?_
  simpa only [Nat.zero_add, Nat.mul_one] using
    whileWork_le _ _ (K := 0) (fun _ _ => le_rfl) _ (a.origNumEdges + 1) _ _

private theorem optimalMSFBranchB_spec {w nOrig n₀ edgeBase₀ : ℕ}
    {es : List (WeightedEdge nOrig ℕ)} {es₀ : List (IndexedEdge n₀)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn₀_le : n₀ ≤ nOrig) (hn₀_le_2m : n₀ ≤ 2 * es₀.length)
    (hm₀_le : es₀.length ≤ es.length) (hr0_ge : 24 ≤ Nat.iterLog 3 n₀)
    (hraw : HoldsEdges 3 es s.mem) (hraw_fr : 3 + 3 * es.length ≤ s.frontier)
    (hes0_holds : HoldsIndexedEdges edgeBase₀ es₀ s.mem)
    (hes0_fr : edgeBase₀ + 4 * es₀.length ≤ s.frontier)
    (hinv0 : MSFLiftInv es [] es₀)
    (hfit : Fits w (s.frontier + 4570 * es.length + 760 * nOrig +
      2 * es.length * max 1 (Nat.iterLog 3 nOrig) + 97400)) :
    let r0 := Nat.iterLog 3 n₀
    let a : OptimalMSFBranchBArgs := ⟨es.length, n₀, es₀.length, edgeBase₀, r0⟩
    let prog := optimalMSFBranchB a
    let outBase := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    optimalMSFBranchBSafe w a s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    ∃ msfEs : List (WeightedEdge nOrig ℕ),
      IsMinSpanningForest es msfEs ∧
      msfEs.length ≤ es.length ∧
      outputList s'.mem outBase = Kruskal.encodeEdges msfEs ∧
      Fits w (outBase + 3 * msfEs.length) ∧
      memoryCost prog s ≤
        30 * optDepthMN es.length nOrig + 59200 * es.length + 5020 * nOrig + 1138055 := by
  set r0 := Nat.iterLog 3 n₀
  have hdt_le : dtPrecompCost r0 ≤ n₀ := dtPrecompCost_iterLog_le_of_ge_24 hr0_ge
  have hr0_le_n0 : r0 ≤ n₀ := Nat.iterLog_le_self 3 n₀
  have hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0 := by omega
  have hr0_le_max : r0 ≤ max 1 (Nat.iterLog 3 nOrig) :=
    (Nat.iterLog_mono 3 hn₀_le).trans (le_max_right 1 _)
  have hmul_r0 : es₀.length * r0 ≤ es.length * max 1 (Nat.iterLog 3 nOrig) :=
    Nat.mul_le_mul hm₀_le hr0_le_max
  have hfit_dt : Fits w (s.frontier + dtPrecompCost r0) := hfit.of_le (by omega)
  have h1ft := precomputeDTProg_spec hwf ((precomputeDTProgSafe_iff w r0 s).mpr hfit_dt)
  have h1 := framedTriple_iff_realization.mp h1ft
  generalize h_tb : (Memory.spec 0).clientResult s (precomputeDTProg r0) = tableBase at h1
  generalize h_s1 : (Memory.spec 0).clientState s (precomputeDTProg r0) = s₁ at h1
  rcases h1 with ⟨-, -, hmod1, hwf1, hs1_fr, htab1, htib1⟩
  have hs_le_s1 : s.frontier ≤ s₁.frontier := hmod1.1
  have hfit_alloc : Fits w (s₁.frontier + es.length) := hfit.of_le (by omega)
  obtain ⟨hselBuf_eq, hs2_fr, hs2_mem, hwf2⟩ := allocDirty_state_props hwf1 hfit_alloc
  set selBuf := (Memory.spec 0).clientResult s₁ (Memory.allocDirty es.length)
  set s₂ := (Memory.spec 0).clientState s₁ (Memory.allocDirty es.length)
  let tableFrontier := s₁.frontier
  let env : PR02LoopEnv := ⟨r0, tableBase, selBuf⟩
  let guard : PR02LoopEnv → PR02LoopState → Prop := fun _ st => 0 < st.cont
  let fBudget := s₂.frontier + 1200 * es₀.length + 750 * n₀ + 2 * es₀.length * r0 + 100
  let fPot (st : PR02LoopState) : ℕ :=
    if st.cont = 1 then 1200 * st.numEdges + 750 * st.numVerts + 2 * st.numEdges * r0 + 100
    else 0
  let pot (st : PR02LoopState) (_ : Memory.State) : ℕ :=
    if st.cont = 1 then
      20000 * st.numEdges + 5000 * st.numVerts + 30 * optDepthMN st.numEdges st.numVerts + 110
    else 0
  let rank (st : PR02LoopState) (_ : Memory.State) : ℕ :=
    if st.cont = 1 then st.numEdges + 1 else 0
  let inv (st : PR02LoopState) (t : Memory.State) : Prop :=
    (st.cont = 0 ∨ st.cont = 1) ∧
    (st.cont = 0 → st.numEdges = 0 ∨ st.numVerts ≤ 64 ∨ st.numVerts * r0 ≤ 2 * st.numEdges) ∧
    st.numVerts ≤ n₀ ∧
    st.numEdges ≤ es₀.length ∧
    st.edgeBase + 4 * st.numEdges ≤ t.frontier ∧
    Memory.WellFormed w t ∧
    HoldsDTTable r0 tableBase t.mem ∧
    DTTableInBounds r0 tableBase tableFrontier t.mem ∧
    s₂.frontier ≤ t.frontier ∧
    t.frontier + fPot st ≤ fBudget ∧
    ∃ (accIds : List (Fin es.length)) (esCur : List (IndexedEdge st.numVerts)),
      esCur.length = st.numEdges ∧
      HoldsIndexedEdges st.edgeBase esCur t.mem ∧
      (st.cont = 1 → st.numVerts ≤ 2 * esCur.length) ∧
      accIds.length = st.selLen ∧
      (∀ j (hj : j < accIds.length), t.mem (selBuf + j) = accIds[j].val) ∧
      MSFLiftInv es accIds esCur
  have hzero : ∀ a t, inv a t → rank a t = 0 → ¬guard env a := by
    intro a t ⟨ha01, _⟩ hr hg
    dsimp only [rank] at hr
    dsimp only [guard] at hg
    rcases ha01 with h0 | h1
    · omega
    · simp [h1] at hr
  have hmul_2r0 : 2 * es₀.length * r0 ≤ 2 * es.length * max 1 (Nat.iterLog 3 nOrig) := by
    rw [Nat.mul_assoc, Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 hmul_r0
  have hstep : ∀ a t, inv a t → guard env a →
      pr02LoopBodyProgSafe w (env, a) t ∧
      (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (pr02LoopBodyProg (env, a))) ∧
      let a' := (Memory.spec 0).clientResult t (pr02LoopBodyProg (env, a))
      let t' := (Memory.spec 0).clientState t (pr02LoopBodyProg (env, a))
      memoryCost (pr02LoopBodyProg (env, a)) t + pot a' t' ≤ pot a t + 0 ∧
      Memory.Modifies (Set.Ico selBuf (selBuf + es.length)) t t' ∧
      inv a' t' ∧ rank a' t' < rank a t := by
    intro a t ⟨ha01, _, ha_n, ha_m, ha_eb, hwt, htab_t, htib_t, hs2_le_t, hfb_t,
      accIds, esCur, hesc_len, hholds_cur, ha_2m, hacc_len, hacc_mem, hinv_cur⟩ hg
    have ha1 : a.cont = 1 := by dsimp only [guard] at hg; rcases ha01 with h0 | h1 <;> omega
    have h2m_cur := ha_2m ha1
    have htf_t : tableFrontier ≤ t.frontier := by
      dsimp only [tableFrontier]; rw [hs2_fr] at hs2_le_t; omega
    have hmul_cur : 2 * esCur.length * r0 ≤ 2 * es₀.length * r0 := by
      rw [Nat.mul_assoc, Nat.mul_assoc]
      exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right r0 (by omega))
    have hfit_body : Fits w (t.frontier + 1200 * esCur.length + 750 * a.numVerts +
        2 * esCur.length * r0 + 100) := by
      have hfp : fPot a = 1200 * esCur.length + 750 * a.numVerts + 2 * esCur.length * r0 + 100 := by
        simp [fPot, ha1, hesc_len]
      have hfb_le : fBudget ≤ s.frontier + n₀ + es.length + 1200 * es₀.length + 750 * n₀ +
          2 * es.length * max 1 (Nat.iterLog 3 nOrig) + 100 := by
        dsimp only [fBudget]; rw [hs2_fr]; omega
      exact hfit.of_le (by omega)
    have hbd := pr02LoopBodyProg_spec (w := w) (n_orig := nOrig) (n₀ := n₀) (r0 := r0)
      (tableFrontier := tableFrontier) (nCur := a.numVerts) (es := es) (env := env) (st := a)
      (accIds := accIds) (esCur := esCur) (s := t) h16 hwt rfl hr0_ge hr0_log rfl hesc_len.symm
      ha_n h2m_cur htab_t htib_t htf_t (by dsimp only [env, tableFrontier]; omega)
      (by dsimp only [env, tableFrontier]; rw [hselBuf_eq, ← hs2_fr]; exact hs2_le_t) hholds_cur
      (by rw [hesc_len]; exact ha_eb) hacc_len hacc_mem hinv_cur hfit_body
    have hbd_r := framedTriple_iff_realization.mp hbd.2
    set a' := (Memory.spec 0).clientResult t (pr02LoopBodyProg (env, a))
    set t' := (Memory.spec 0).clientState t (pr02LoopBodyProg (env, a))
    rcases hbd_r with ⟨hv_b, _, hmod_b, ht_le_t', hfr_b, ha'01, ha'_exit, ha'_cont, ha'_n, ha'_m,
      ha'_eb, hwt', hmod_tb, hcost_b, accIds', esNext, hnext_len, hnext_holds, _, hacc'_len,
      hacc'_mem, hinv_next⟩
    have hsum_acc : accIds.length ≤ es.length := by have := hinv_cur.sum_le; omega
    have hmod_S : Memory.Modifies (Set.Ico selBuf (selBuf + es.length)) t t' :=
      hmod_b.mono fun x hx => by simp only [env, Set.mem_Ico] at hx ⊢; omega
    refine ⟨hbd.1, hv_b, ?_, hmod_S, ?_, ?_⟩
    · dsimp only [pot]; simp only [ha1, ↓reduceIte]; rw [← hesc_len]
      by_cases h1' : a'.cont = 1
      · simp only [h1', ↓reduceIte] at hcost_b ⊢; exact hcost_b
      · simp only [h1', ↓reduceIte, add_zero] at hcost_b ⊢; omega
    · have hfp_a : fPot a = 1200 * esCur.length + 750 * a.numVerts +
          2 * esCur.length * r0 + 100 := by simp [fPot, ha1, hesc_len]
      refine ⟨ha'01, ha'_exit, ha'_n, by omega, ha'_eb, hwt',
        htab_t.congr htib_t hmod_tb, htib_t.mono le_rfl hmod_tb, hs2_le_t.trans ht_le_t', ?_,
        accIds', esNext, hnext_len, hnext_holds, fun h1' => by
          have hc := (ha'_cont h1').2.2.2.1; omega, hacc'_len, hacc'_mem, hinv_next⟩
      dsimp only [fPot]
      by_cases h1' : a'.cont = 1
      · simp only [h1', ↓reduceIte] at hfr_b ⊢; omega
      · simp only [h1', ↓reduceIte, add_zero] at hfr_b ⊢; omega
    · dsimp only [rank]; simp only [ha1, ↓reduceIte]
      by_cases h1' : a'.cont = 1
      · simp only [h1', ↓reduceIte]; obtain ⟨hm_pos, _, h2m', _, _⟩ := ha'_cont h1'; omega
      · simp only [h1', ↓reduceIte]; omega
  have hraw2 : HoldsEdges 3 es s₂.mem :=
    hs2_mem ▸ holdsEdges_frame hraw fun a _ _ => hmod1.mem_eq_of_not_mem (by omega) (by simp)
  have hes0_holds2 : HoldsIndexedEdges edgeBase₀ es₀ s₂.mem :=
    hs2_mem ▸ hes0_holds.congr fun a _ _ => hmod1.mem_eq_of_not_mem (by omega) (by simp)
  have hinv_init : inv ⟨1, n₀, es₀.length, edgeBase₀, 0⟩ s₂ := by
    refine ⟨Or.inr rfl, fun h => by simp at h, le_rfl, le_rfl, by dsimp only; omega, hwf2,
      by rw [hs2_mem]; exact htab1, by rw [hs2_mem]; exact htib1, le_rfl,
      by dsimp only [fPot, fBudget]; simp only [↓reduceIte]; omega, [], es₀, rfl, hes0_holds2,
      fun _ => hn₀_le_2m, rfl, fun j hj => by simp at hj, hinv0⟩
  have hloop := boundedWhile_potential_spec guard pr02LoopBodyProg pr02LoopBodyProgSafe w env 0
    inv rank pot (Set.Ico selBuf (selBuf + es.length)) hzero hstep (es.length + 1)
    ⟨1, n₀, es₀.length, edgeBase₀, 0⟩ s₂ hinv_init (by simp [rank]; omega)
  dsimp only at hloop
  generalize h_stFin : (Memory.spec 0).clientResult s₂
    (boundedWhile guard pr02LoopBodyProg env (es.length + 1)
      ⟨1, n₀, es₀.length, edgeBase₀, 0⟩) = stFin at hloop
  generalize h_s3 : (Memory.spec 0).clientState s₂
    (boundedWhile guard pr02LoopBodyProg env (es.length + 1)
      ⟨1, n₀, es₀.length, edgeBase₀, 0⟩) = s₃ at hloop
  rcases hloop with ⟨hsafe_loop, hv_loop, hstop_loop, hinv_fin, hmod_loop, hcost_loop⟩
  have hs2_le_s3 : s₂.frontier ≤ s₃.frontier := hmod_loop.1
  rcases hinv_fin with ⟨hst01, hst_exit, hnFin_le, hmFin_le, hebFin_fr, hwf3, _, _, htf_s3,
    hfr_s3, accFin, esFin, hesFin_len, hesFin_holds, _, haccFin_len, haccFin_mem, hinvFin⟩
  have hst0 : stFin.cont = 0 := by dsimp only [guard] at hstop_loop; omega
  have hraw3 : HoldsEdges 3 es s₃.mem :=
    holdsEdges_frame hraw2 fun a ha1 ha2 =>
      hmod_loop.mem_eq_of_not_mem (by rw [hs2_fr]; omega)
        (by simp only [Set.mem_Ico]; rw [hselBuf_eq]; omega)
  have hfit_fin : Fits w (s₃.frontier + 3365 * esFin.length + 8 * stFin.numVerts +
      3 * es.length + 97290) := by
    have hs3_ub : s₃.frontier ≤ fBudget := by
      have : fPot stFin = 0 := by simp [fPot, hst0]
      omega
    have hfb_le : fBudget ≤ s.frontier + n₀ + es.length + 1200 * es₀.length + 750 * n₀ +
        2 * es.length * max 1 (Nat.iterLog 3 nOrig) + 100 := by
      dsimp only [fBudget]; rw [hs2_fr]; omega
    have hmfin_le : 3365 * esFin.length ≤ 3365 * es.length := by omega
    exact hfit.of_le (by omega)
  have hfin := optimalMSFFinishProg_spec (w := w) (nOrig := nOrig) (n₀ := n₀)
    (nEnd := stFin.numVerts) (r0 := r0) (selBuf := selBuf) (ebEnd := stFin.edgeBase)
    (selLen := stFin.selLen) (es := es) (accIds := accFin) (esEnd := esFin) (s := s₃) h16 hwf3
    hnFin_le hr0_log (by rw [hesFin_len]; exact hst_exit hst0) hraw3
    (by rw [hselBuf_eq]; exact hraw_fr.trans hs_le_s1)
    (by rw [hselBuf_eq]; exact htf_s3) haccFin_len haccFin_mem hesFin_holds
    (by rw [hesFin_len]; exact hebFin_fr) hinvFin hfit_fin
  rw [hesFin_len] at hfin
  dsimp only at hfin
  rcases hfin with ⟨hsafe_fin, hv_fin, msfEs, hmsf_msf, hmsf_len, hout_list, hfit_out, hc_fin⟩
  have hopt_init : pot ⟨1, n₀, es₀.length, edgeBase₀, 0⟩ s₂ =
      20000 * es₀.length + 5000 * n₀ + 30 * optDepthMN es₀.length n₀ + 110 := by
    simp [pot]
  have hopt_le : optDepthMN es₀.length n₀ ≤ optDepthMN es.length nOrig :=
    (optDepthMN_mono_m hm₀_le).trans (optDepthMN_mono_n hn₀_le)
  have hs2_eq : s₂ = ⟨s₁.mem, s₁.frontier + es.length⟩ := by rw [← hs2_mem, ← hs2_fr]
  have hpot0 : pot stFin s₃ = 0 := by simp [pot, hst0]
  dsimp only [env] at hcost_loop
  rw [hopt_init, hpot0, Nat.zero_mul, Nat.add_zero, Nat.add_zero] at hcost_loop
  have h30_opt : 30 * optDepthMN es₀.length n₀ ≤ 30 * optDepthMN es.length nOrig :=
    Nat.mul_le_mul_left 30 hopt_le
  have hft : Memory.FramedTriple w s (optimalMSFBranchB ⟨es.length, n₀, es₀.length, edgeBase₀, r0⟩)
      (30 * optDepthMN es.length nOrig + 59200 * es.length + 5020 * nOrig + 1138055) Set.univ
      fun outBase s' =>
        outputList s'.mem outBase = Kruskal.encodeEdges msfEs ∧
          Fits w (outBase + 3 * msfEs.length) := by
    unfold optimalMSFBranchB
    eapply Memory.FramedTriple.mono (hQ := fun _ _ => id)
    · eapply Memory.FramedTriple.seq (h1ft.frame_mono (Set.empty_subset _)) subset_rfl
      on_goal 1 => rw [h_tb, h_s1]
      eapply Memory.FramedTriple.allocDirty_bind hfit_alloc
      on_goal 1 => rw [← hs2_eq, ← hselBuf_eq]
      eapply Memory.FramedTriple.call_eq
        (Memory.FramedTriple.univ_of_realization hv_loop hcost_loop h_stFin h_s3) subset_rfl
      exact Memory.FramedTriple.call_eq_tail
        (Memory.FramedTriple.univ_of_realization hv_fin hc_fin rfl rfl) subset_rfl
        ⟨hout_list, hfit_out⟩
    · omega
  obtain ⟨hv, hc, -, hlist, hfit'⟩ := framedTriple_iff_realization.mp hft
  refine ⟨⟨h16, hfit.of_le (by dsimp only; omega), hfit.of_le (by dsimp only; omega),
      hfit.of_le (by dsimp only; omega), hfit.of_le (by dsimp only; omega),
      hfit.of_le (by dsimp only; omega), (precomputeDTProgSafe_iff w r0 s).mpr hfit_dt, ?_⟩, hv,
    msfEs, hmsf_msf, hmsf_len, hlist, hfit', hc⟩
  dsimp only
  rw [h_tb, h_s1]
  refine ⟨hfit_alloc, ?_⟩
  rw [← hs2_eq, ← hselBuf_eq]
  refine ⟨hsafe_loop, ?_⟩
  rw [h_stFin, h_s3]
  exact hsafe_fin

/-! ## Section 5: Private Dispatch (`optimalMSFPositiveProg`, `optimalMSFNonEmptyProg`) -/

private def optimalMSFPositiveProg (a : OptimalMSFBranchArgs) : Memory.Prog ℕ := do
  let r0 ← iterLogProg 3 a.numVerts
  if r0 < 24 then optimalMSFBranchA a
  else optimalMSFBranchB ⟨a.origNumEdges, a.numVerts, a.numEdges, a.edgeBase, r0⟩

private def optimalMSFPositiveSafe (w : ℕ) (a : OptimalMSFBranchArgs)
    (s : Memory.State) : Prop :=
  Fits w 24 ∧
  let r0 := (Memory.spec 0).clientResult s (iterLogProg 3 a.numVerts)
  let s₁ := (Memory.spec 0).clientState s (iterLogProg 3 a.numVerts)
  (r0 < 24 → optimalMSFBranchASafe w a s₁) ∧
  (¬r0 < 24 → optimalMSFBranchBSafe w ⟨a.origNumEdges, a.numVerts, a.numEdges, a.edgeBase, r0⟩ s₁)

private theorem realizes_optimalMSFPositiveProg : Realizes .exact
    optimalMSFPositiveProg WordEncoding.encode WordEncoding.encode
    optimalMSFPositiveSafe
    (fun a _ => 3 * (Nat.log 2 a.numVerts + 3) + (a.origNumEdges + 1)) := by
  have hraw : Realizes .exact optimalMSFPositiveProg WordEncoding.encode WordEncoding.encode
      optimalMSFPositiveSafe
      (fun a s =>
        3 * (Nat.log 2 a.numVerts + 3) +
          if (Memory.spec 0).clientResult s (iterLogProg 3 a.numVerts) < 24 then 0
          else a.origNumEdges + 1) := by
    unfold optimalMSFPositiveProg
    realize [realizes_iterLog3, realizes_optimalMSFBranchA, realizes_optimalMSFBranchB]
    all_goals first
      | exact h.1.of_le (by decide)
      | exact h.2.1 (by assumption)
      | exact h.2.2 (by assumption)
  refine hraw.consequence (fun _ _ _ _ _ h => h) fun a s => ?_
  split_ifs <;> omega

private def optimalMSFNonEmptyProg (a : OptimalMSFArgs) : Memory.Prog ℕ := do
  let pre ← initPreprocessProg ⟨a.numVertices, a.numEdges, 3⟩
  if pre.numEdges = 0 then emitMSFEdges ⟨3, 0, 0⟩
  else optimalMSFPositiveProg ⟨a.numEdges, pre.numVertices, pre.numEdges, pre.edgeBase⟩

private def optimalMSFNonEmptySafe (w : ℕ) (a : OptimalMSFArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  initPreprocessProgSafe w ⟨a.numVertices, a.numEdges, 3⟩ s ∧
  let pre := (Memory.spec 0).clientResult s (initPreprocessProg ⟨a.numVertices, a.numEdges, 3⟩)
  let s₁ := (Memory.spec 0).clientState s (initPreprocessProg ⟨a.numVertices, a.numEdges, 3⟩)
  (pre.numEdges = 0 → emitMSFEdgesSafe w ⟨3, 0, 0⟩ s₁) ∧
  (pre.numEdges ≠ 0 →
    optimalMSFPositiveSafe w ⟨a.numEdges, pre.numVertices, pre.numEdges, pre.edgeBase⟩ s₁)

private theorem realizes_optimalMSFNonEmptyProg : Realizes .exact
    optimalMSFNonEmptyProg WordEncoding.encode WordEncoding.encode
    optimalMSFNonEmptySafe
    (fun a _ => 3 * (Nat.log 2 a.numVertices + 3) + (a.numEdges + 1)) := by
  have hraw : Realizes .exact optimalMSFNonEmptyProg WordEncoding.encode WordEncoding.encode
      optimalMSFNonEmptySafe
      (fun a s =>
        let pre := (Memory.spec 0).clientResult s
          (initPreprocessProg ⟨a.numVertices, a.numEdges, 3⟩)
        if pre.numEdges = 0 then 0
        else 3 * (Nat.log 2 pre.numVertices + 3) + (a.numEdges + 1)) := by
    unfold optimalMSFNonEmptyProg
    realize [realizes_initPreprocessProg, realizes_emitMSFEdges', realizes_optimalMSFPositiveProg]
    · exact h.1.of_le (by decide)
    · exact h.2.1
    · exact h.1.of_le (by decide)
    · exact h.2.2.1 hc
    · exact h.2.2.2 hc
  refine realizes_consequence_of hraw (fun _ _ _ _ _ _ h => h) fun w a s _ hmem hsafe => ?_
  have hnv : ((Memory.spec 0).clientResult s
      (initPreprocessProg ⟨a.numVertices, a.numEdges, 3⟩)).numVertices ≤ a.numVertices :=
    initPreprocessProg_numVertices_le hmem hsafe.2.1
  have hlog_le : Nat.log 2 ((Memory.spec 0).clientResult s
      (initPreprocessProg ⟨a.numVertices, a.numEdges, 3⟩)).numVertices ≤
      Nat.log 2 a.numVertices := Nat.log_mono_right hnv
  dsimp only
  split_ifs <;> omega

private theorem optimalMSFNonEmptyProg_spec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hw_fit : ∀ e ∈ es, Fits w e.weight)
    (hfit : Fits w (optimalMSFWordBound n es.length)) :
    let s := Memory.State.init (Kruskal.encode es)
    let prog := optimalMSFNonEmptyProg ⟨n, es.length⟩
    let outBase := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    optimalMSFNonEmptySafe w ⟨n, es.length⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    ∃ msfEs : List (WeightedEdge n ℕ),
      IsMinSpanningForest es msfEs ∧
      msfEs.length ≤ es.length ∧
      outputList s'.mem outBase = Kruskal.encodeEdges msfEs ∧
      Fits w (outBase + 3 * msfEs.length) ∧
      memoryCost prog s ≤
        30 * optDepthMN es.length n + 78800 * es.length + 651500 * n + 1814300 := by
  set s := Memory.State.init (Kruskal.encode es)
  have hwb := optimalMSFWordBound_ge n es.length
  have h16 : Fits w 16 := hfit.of_le (by omega)
  have h24 : Fits w 24 := hfit.of_le (by omega)
  have hs_fr : s.frontier = 3 * es.length + 3 := by
    simp [s, Memory.State.init, Kruskal.length_encode]
  have hwf : Memory.WellFormed w s :=
    Memory.wellFormed_init (Kruskal.inputFits_encode es (hfit.of_le (by omega)) hw_fit)
      (hfit.of_le (by rw [Kruskal.length_encode]; omega))
  have hraw : HoldsEdges 3 es s.mem := holdsEdges_init (r := 0) es
  have hraw_bd : ∀ j < es.length,
      s.mem (3 + 3 * j) < n ∧ s.mem (3 + 3 * j + 1) < n := fun j hj => by
    obtain ⟨hu, hv, _⟩ := hraw j hj
    exact ⟨hu ▸ es[j].u.isLt, hv ▸ es[j].v.isLt⟩
  have hfit_init : Fits w (s.frontier + (21 * es.length + 3 * n + 1)) :=
    hfit.of_le (by rw [hs_fr]; omega)
  have h1 := framedTriple_iff_realization.mp
    (initPreprocessProg_spec (w := w) (n := n) (inBase := 3)
      (es := es) (s := s) h16 hwf hraw (by rw [hs_fr]; omega) hfit_init)
  have hsafe1 : initPreprocessProgSafe w ⟨n, es.length, 3⟩ s :=
    ⟨h16, by dsimp only; rw [hs_fr]; omega, hfit_init, hraw_bd⟩
  generalize h_pre : (Memory.spec 0).clientResult s
    (initPreprocessProg ⟨n, es.length, 3⟩) = pre at h1
  generalize h_s1 : (Memory.spec 0).clientState s (initPreprocessProg ⟨n, es.length, 3⟩) = s₁ at h1
  rcases h1 with ⟨hv1, hc1, hmod1, hpre1_2m, hpre1_n, hpre21_m, hpre_eb, hpre22_fr, hs1_fr, hwf1,
    es₀, hes₀_len, hes₀_holds, _, hself0, hinv0⟩
  have hprog : optimalMSFNonEmptyProg ⟨n, es.length⟩ =
      (initPreprocessProg ⟨n, es.length, 3⟩ >>= fun pre' =>
        if pre'.numEdges = 0 then emitMSFEdges ⟨3, 0, 0⟩
        else optimalMSFPositiveProg ⟨es.length, pre'.numVertices, pre'.numEdges, pre'.edgeBase⟩) :=
    rfl
  have hs_le_s1 : s.frontier ≤ s₁.frontier := hmod1.1
  have hraw1 : HoldsEdges 3 es s₁.mem :=
    holdsEdges_frame hraw fun a ha1 _ => hmod1.mem_eq_of_not_mem (by rw [hs_fr]; omega) (by simp)
  by_cases hm0 : pre.numEdges = 0
  · have hmsf_nil : IsMinSpanningForest es [] :=
      isMinSpanningForest_nil_of_all_self es (hself0.mp hm0)
    have hs1_ub : s₁.frontier ≤ 24 * es.length + 3 * n + 4 := by rw [hs_fr] at hs1_fr; omega
    have hs1_lb : 3 + 3 * es.length ≤ s₁.frontier := by rw [hs_fr] at hs_le_s1; omega
    have hfit_emit : Fits w (s₁.frontier + (3 * ([] : List (Fin es.length)).length + 1)) :=
      hfit.of_le (by simp only [List.length_nil]; omega)
    have hemit := framedTriple_iff_realization.mp
      (emitMSFEdges_spec (w := w) (n := n) (d := ⟨3, 0, ([] : List (Fin es.length)).length⟩)
        (es := es) (selIds := ([] : List (Fin es.length))) (s := s₁) h16 hwf1 hraw1
        hs1_lb (fun j hj => by simp at hj) (by simp only [List.length_nil]; omega) rfl hfit_emit)
    dsimp only at hemit
    simp only [List.length_nil] at hemit
    rcases hemit with ⟨hv_e, hc_e, _, hout_eq, _, _, hout_list⟩
    have hsafe_e : emitMSFEdgesSafe w ⟨3, 0, 0⟩ s₁ :=
      ⟨h16, by dsimp only; omega, by simpa using hfit_emit, fun j hj => by dsimp only at hj; omega⟩
    have hbr_0 : ite (pre.numEdges = 0) (emitMSFEdges ⟨3, 0, 0⟩)
        (optimalMSFPositiveProg ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase⟩) =
        emitMSFEdges ⟨3, 0, 0⟩ := by simp only [hm0, ↓reduceIte]
    refine ⟨⟨h16, hsafe1, ?_, ?_⟩, ?_, [], hmsf_nil, Nat.zero_le _, ?_, ?_, ?_⟩
    · dsimp only; rw [h_pre, h_s1]; exact fun _ => hsafe_e
    · dsimp only; rw [h_pre]; exact fun h => absurd hm0 h
    · rw [hprog]; exact validHistory_bind_step hv1 (by rw [h_pre, h_s1, hbr_0]; exact hv_e)
    · rw [hprog, StateTransitionSpec.clientResult_bind, h_pre, h_s1, hbr_0,
        StateTransitionSpec.clientState_bind, h_pre, h_s1, hbr_0, hout_list]; simp
    · rw [hprog, StateTransitionSpec.clientResult_bind, h_pre, h_s1, hbr_0, hout_eq]
      exact hfit.of_le (by simp only [List.length_nil]; omega)
    · rw [hprog, memoryCost_bind', h_pre, h_s1, hbr_0]; omega
  · have hm_pos : 0 < pre.numEdges := Nat.pos_of_ne_zero hm0
    have hl := framedTriple_iff_realization.mp (iterLogProg_spec w 3 pre.numVertices s₁)
    generalize h_r0 : (Memory.spec 0).clientResult s₁ (iterLogProg 3 pre.numVertices) = r0 at hl
    generalize h_s2 : (Memory.spec 0).clientState s₁ (iterLogProg 3 pre.numVertices) = s₂ at hl
    rcases hl with ⟨hv_l, hc_l, _, hs2_eq, hr0_eq⟩
    have hs2_fr : s₂.frontier = s₁.frontier := by rw [hs2_eq]
    have hraw2 : HoldsEdges 3 es s₂.mem := hs2_eq ▸ hraw1
    have hes₀_holds2 : HoldsIndexedEdges pre.edgeBase es₀ s₂.mem := hs2_eq ▸ hes₀_holds
    have hwf2 : Memory.WellFormed w s₂ := hs2_eq ▸ hwf1
    have hpos_prog : optimalMSFPositiveProg
          ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase⟩ =
        (iterLogProg 3 pre.numVertices >>= fun r0' =>
          if r0' < 24 then
            optimalMSFBranchA ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase⟩
          else optimalMSFBranchB ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase, r0'⟩) :=
      rfl
    have hm_ne : ite (pre.numEdges = 0) (emitMSFEdges ⟨3, 0, 0⟩)
        (optimalMSFPositiveProg ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase⟩) =
        optimalMSFPositiveProg ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase⟩ := by
      simp only [hm0, ↓reduceIte]
    have hs2_fr_ub : s₂.frontier ≤ 24 * es.length + 3 * n + 4 := by
      rw [hs2_fr]; rw [hs_fr] at hs1_fr; omega
    have hraw_fr2 : 3 + 3 * es.length ≤ s₂.frontier := by
      rw [hs2_fr]; rw [hs_fr] at hs_le_s1; omega
    have hpack : ∀ {subProg : Memory.Prog ℕ}
        (hbr : ite (r0 < 24)
            (optimalMSFBranchA ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase⟩)
            (optimalMSFBranchB ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase, r0⟩) =
          subProg)
        (hsafe_pos : (r0 < 24 → optimalMSFBranchASafe w
            ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase⟩ s₂) ∧
          (¬r0 < 24 → optimalMSFBranchBSafe w
            ⟨es.length, pre.numVertices, pre.numEdges, pre.edgeBase, r0⟩ s₂))
        (hv_sub : (Memory.spec w).ValidHistory s₂ ((Memory.spec w).clientHistory s₂ subProg))
        {msfEs : List (WeightedEdge n ℕ)} (hmsf_msf : IsMinSpanningForest es msfEs)
        (hmsf_len : msfEs.length ≤ es.length)
        (hout_list : outputList ((Memory.spec 0).clientState s₂ subProg).mem
          ((Memory.spec 0).clientResult s₂ subProg) = Kruskal.encodeEdges msfEs)
        (hfit_out : Fits w ((Memory.spec 0).clientResult s₂ subProg + 3 * msfEs.length))
        (hc_sub : memoryCost subProg s₂ + memoryCost (initPreprocessProg ⟨n, es.length, 3⟩) s +
          memoryCost (iterLogProg 3 pre.numVertices) s₁ ≤
          30 * optDepthMN es.length n + 78800 * es.length + 651500 * n + 1814300),
        optimalMSFNonEmptySafe w ⟨n, es.length⟩ s ∧
        (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (optimalMSFNonEmptyProg ⟨n, es.length⟩)) ∧
        ∃ msfEs' : List (WeightedEdge n ℕ),
          IsMinSpanningForest es msfEs' ∧ msfEs'.length ≤ es.length ∧
          outputList ((Memory.spec 0).clientState s (optimalMSFNonEmptyProg ⟨n, es.length⟩)).mem
            ((Memory.spec 0).clientResult s (optimalMSFNonEmptyProg ⟨n, es.length⟩)) =
            Kruskal.encodeEdges msfEs' ∧
          Fits w ((Memory.spec 0).clientResult s (optimalMSFNonEmptyProg ⟨n, es.length⟩) +
            3 * msfEs'.length) ∧
          memoryCost (optimalMSFNonEmptyProg ⟨n, es.length⟩) s ≤
            30 * optDepthMN es.length n + 78800 * es.length + 651500 * n + 1814300 := by
      intro subProg hbr hsafe_pos hv_sub msfEs hmsf_msf hmsf_len hout_list hfit_out hc_sub
      refine ⟨⟨h16, hsafe1, ?_, ?_⟩, ?_, msfEs, hmsf_msf, hmsf_len, ?_, ?_, ?_⟩
      · dsimp only; rw [h_pre]; exact fun h => absurd h hm0
      · dsimp only; rw [h_pre, h_s1]; refine fun _ => ⟨h24, ?_⟩; rw [h_r0, h_s2]; exact hsafe_pos
      · rw [hprog]; refine validHistory_bind_step hv1 ?_
        rw [h_pre, h_s1, hm_ne, hpos_prog]
        refine validHistory_bind_step hv_l ?_; rw [h_r0, h_s2, hbr]; exact hv_sub
      · rw [hprog, StateTransitionSpec.clientResult_bind, h_pre, h_s1, hm_ne,
          StateTransitionSpec.clientState_bind, h_pre, h_s1, hm_ne, hpos_prog,
          StateTransitionSpec.clientResult_bind, h_r0, h_s2, hbr,
          StateTransitionSpec.clientState_bind, h_r0, h_s2, hbr, hout_list]
      · rw [hprog, StateTransitionSpec.clientResult_bind, h_pre, h_s1, hm_ne, hpos_prog,
          StateTransitionSpec.clientResult_bind, h_r0, h_s2, hbr]; exact hfit_out
      · rw [hprog, memoryCost_bind', h_pre, h_s1, hm_ne, hpos_prog, memoryCost_bind',
          h_r0, h_s2, hbr]; omega
    by_cases hr24 : r0 < 24
    · have hA := optimalMSFBranchA_spec (w := w) (nOrig := n) (n₀ := pre.numVertices)
        (edgeBase₀ := pre.edgeBase) (es := es) (es₀ := es₀) (s := s₂) h16 hwf2 hpre1_n
        (by omega) (by rw [← hr0_eq]; exact hr24) hraw2 hraw_fr2
        hes₀_holds2 (by rw [hs2_fr, hes₀_len]; exact hpre22_fr) hinv0
        (hfit.of_le (by unfold optimalMSFWordBound; omega))
      rw [hes₀_len] at hA; dsimp only at hA
      rcases hA with ⟨hsafe_a, hv_a, msfEs, hmsf_msf, hmsf_len, hout_list, hfit_out, hc_a⟩
      exact hpack (by simp only [hr24, ↓reduceIte]) ⟨fun _ => hsafe_a, fun h => absurd hr24 h⟩
        hv_a hmsf_msf hmsf_len hout_list hfit_out (by omega)
    · have hB := optimalMSFBranchB_spec (w := w) (nOrig := n) (n₀ := pre.numVertices)
        (edgeBase₀ := pre.edgeBase) (es := es) (es₀ := es₀) (s := s₂) h16 hwf2 hpre1_n
        (by omega) (by omega) (by rw [← hr0_eq]; omega) hraw2 hraw_fr2
        hes₀_holds2 (by rw [hs2_fr, hes₀_len]; exact hpre22_fr) hinv0
        (hfit.of_le (by unfold optimalMSFWordBound; omega))
      rw [hes₀_len, ← hr0_eq] at hB; dsimp only at hB
      rcases hB with ⟨hsafe_b, hv_b, msfEs, hmsf_msf, hmsf_len, hout_list, hfit_out, hc_b⟩
      exact hpack (by simp only [hr24, ↓reduceIte]) ⟨fun h => absurd h hr24, fun _ => hsafe_b⟩
        hv_b hmsf_msf hmsf_len hout_list hfit_out (by omega)

/-! ## Section 6: Public Entry Point and Theorem 5.8 Specifications -/

/-- Top-level Pettie–Ramachandran deterministic minimum spanning forest program over
`Cslib.DataStructure.Memory.Prog`, returning the base address of a length-prefixed
`Kruskal.encodeEdges` array of minimum spanning forest edges. -/
def optimalMSFProg (a : OptimalMSFArgs) : Memory.Prog ℕ :=
  if a.numEdges = 0 then emitMSFEdges ⟨3, 0, 0⟩
  else optimalMSFNonEmptyProg a

/-- Native Word-RAM safety domain for `optimalMSFProg`. -/
def optimalMSFSafe (w : ℕ) (a : OptimalMSFArgs) (s : Memory.State) : Prop :=
  if a.numEdges = 0 then emitMSFEdgesSafe w ⟨3, 0, 0⟩ s
  else optimalMSFNonEmptySafe w a s

/-- Uniform `Realizes .exact` compilation certificate for `optimalMSFProg` (`O(m + log n + 1)`
local work from `iterLogProg 3` and the outer loop cutoff). -/
theorem realizes_optimalMSFProg :
    Realizes .exact optimalMSFProg WordEncoding.encode WordEncoding.encode
      optimalMSFSafe (fun a _ => 3 * (Nat.log 2 a.numVertices + 3) + (a.numEdges + 1)) := by
  have hraw : Realizes .exact optimalMSFProg WordEncoding.encode WordEncoding.encode
      optimalMSFSafe
      (fun a _ => if a.numEdges = 0 then 0
        else 3 * (Nat.log 2 a.numVertices + 3) + (a.numEdges + 1)) := by
    unfold optimalMSFProg
    realize [realizes_emitMSFEdges', realizes_optimalMSFNonEmptyProg]
    all_goals
      simp only [optimalMSFSafe] at h
      split_ifs at h
      first
        | exact h
        | (have h16 := h.1; have hfront := hmem.frontier_fits; fits)
  refine hraw.consequence (fun _ _ _ _ _ h => h) fun a _ => ?_
  split_ifs <;> omega

/-- Functional specification of `optimalMSFProg`: on `Memory.State.init (Kruskal.encode es)` at
any word width `w` with `∀ e ∈ es, Fits w e.weight` and
`Fits w (optimalMSFWordBound n es.length)`, `optimalMSFProg` halts safely and writes
`Kruskal.encodeEdges msfEs` for a minimum spanning forest `msfEs` in at most
`30 * optDepthMN es.length n + 78800 * es.length + 651500 * n + 1814300` memory operations. -/
theorem optimalMSFProg_spec {w n : ℕ} (es : List (WeightedEdge n ℕ))
    (hw_fit : ∀ e ∈ es, Fits w e.weight)
    (hfit : Fits w (optimalMSFWordBound n es.length)) :
    let s := Memory.State.init (Kruskal.encode es)
    let prog := optimalMSFProg ⟨n, es.length⟩
    let outBase := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    optimalMSFSafe w ⟨n, es.length⟩ s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    ∃ msfEs : List (WeightedEdge n ℕ),
      IsMinSpanningForest es msfEs ∧
      msfEs.length ≤ es.length ∧
      outputList s'.mem outBase = Kruskal.encodeEdges msfEs ∧
      Fits w (outBase + 3 * msfEs.length) ∧
      memoryCost prog s ≤
        30 * optDepthMN es.length n + 78800 * es.length + 651500 * n + 1814300 := by
  by_cases hm0 : es.length = 0
  · have hes_nil : es = [] := List.eq_nil_of_length_eq_zero hm0
    subst hes_nil
    set s := Memory.State.init (Kruskal.encode ([] : List (WeightedEdge n ℕ)))
    have hwb := optimalMSFWordBound_ge n 0
    have h16 : Fits w 16 := hfit.of_le (by simp only [List.length_nil] at hfit ⊢; omega)
    have hwf : Memory.WellFormed w s :=
      Memory.wellFormed_init (Kruskal.inputFits_encode []
        (hfit.of_le (by simp only [List.length_nil] at hfit ⊢; omega)) fun _ h => by simp at h)
        (hfit.of_le (by simp [Kruskal.length_encode]; omega))
    have hs_fr : s.frontier = 3 := by simp [s, Memory.State.init, Kruskal.length_encode]
    have hfit_emit : Fits w (s.frontier + (3 * ([] : List (Fin 0)).length + 1)) :=
      hfit.of_le (by rw [hs_fr]; simp only [List.length_nil] at hfit ⊢; omega)
    have hemit := framedTriple_iff_realization.mp
      (emitMSFEdges_spec (w := w) (n := n) (d := ⟨3, 0, ([] : List (Fin 0)).length⟩)
        (es := ([] : List (WeightedEdge n ℕ))) (selIds := ([] : List (Fin 0))) (s := s)
        h16 hwf (holdsEdges_init (r := 0) []) (by dsimp only; rw [hs_fr]; omega)
        (fun j hj => by simp at hj) (by dsimp only; rw [hs_fr]; omega) rfl hfit_emit)
    dsimp only at hemit; simp only [List.length_nil] at hemit
    rcases hemit with ⟨hv, hc, _, hout_eq, _, _, hout_list⟩
    have hsafe : emitMSFEdgesSafe w ⟨3, 0, 0⟩ s :=
      ⟨h16, by dsimp only; rw [hs_fr]; omega, by simpa using hfit_emit,
        fun j hj => by dsimp only at hj; omega⟩
    have hprog : optimalMSFProg ⟨n, ([] : List (WeightedEdge n ℕ)).length⟩ =
        emitMSFEdges ⟨3, 0, 0⟩ := by simp [optimalMSFProg]
    have hsafe' : optimalMSFSafe w ⟨n, ([] : List (WeightedEdge n ℕ)).length⟩ s := by
      simpa [optimalMSFSafe] using hsafe
    refine ⟨hsafe', ?_, [], isMinSpanningForest_nil_of_all_self [] (fun _ h => by simp at h),
      Nat.zero_le _, ?_, ?_, ?_⟩
    · rw [hprog]; exact hv
    · rw [hprog, hout_list]; simp
    · rw [hprog, hout_eq]
      exact hfit.of_le (by rw [hs_fr]; simp only [List.length_nil] at hfit ⊢; omega)
    · rw [hprog]; simp only [List.length_nil] at hc ⊢; omega
  · have hspec := optimalMSFNonEmptyProg_spec es hw_fit hfit
    have hprog : optimalMSFProg ⟨n, es.length⟩ = optimalMSFNonEmptyProg ⟨n, es.length⟩ := by
      simp [optimalMSFProg, hm0]
    have hsafe : optimalMSFSafe w ⟨n, es.length⟩ (Memory.State.init (Kruskal.encode es)) := by
      simpa [optimalMSFSafe, hm0] using hspec.1
    refine ⟨hsafe, ?_, ?_⟩
    · rw [hprog]; exact hspec.2.1
    · simpa [hprog] using hspec.2.2

/-- **Width-blind deterministic `O(optDepthMN m n + m + n + 1)` Word-RAM Minimum Spanning
Forest driver theorem**: there exists a single fixed, width-blind (`¬prog.ReadsWidth`),
random-free (`prog.IsRandFree`) standard-basis Word-RAM program `prog : Program .standard r` and
a universal constant `C : ℕ` such that for every vertex count `n : ℕ`, every weighted undirected
multigraph `es : List (WeightedEdge n ℕ)` (`m = es.length`), and every word width `w : ℕ`
satisfying `Fits w (optimalMSFWordBound n m)` and `∀ e ∈ es, Fits w e.weight`, running `prog` from
`State.init (Kruskal.encode es)` halts in `steps ≤ C * (optDepthMN m n + m + n + 1)` instructions
(`ExecutesList`), outputting `Kruskal.encodeEdges msfEs` for a minimum spanning forest `msfEs` of
`es` (`IsMinSpanningForest es msfEs`). Logarithmic word width suffices for the workspace threshold
`optimalMSFWordBound n m`, with an additional `Fits w` fit condition for edge weights, and the
theorem allows any larger word width `w`. On raw multigraphs, edge saturation of `optDepthMN m n`
at `optDepthMN (n.choose 2) n` follows from `m > n.choose 2` (absorbing input scanning and
deduplication into `+ m`), while isolated vertices separately explain the `+ n` vertex overhead;
see `optimalMSF_simpleGraph_isMST_spec` for the Theorem 5.8 `O(T*(m, n) + 1)` bound on connected
simple graphs. -/
theorem optimalMSF_wordRAM_spec :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∀ (n : ℕ) (es : List (WeightedEdge n ℕ)) (w : ℕ),
        (∀ e ∈ es, Fits w e.weight) →
        Fits w (optimalMSFWordBound n es.length) →
        ∃ steps : ℕ, ∃ msfEs : List (WeightedEdge n ℕ),
          ExecutesList w prog (State.init (Kruskal.encode es))
            (Kruskal.encodeEdges msfEs) steps ∧
          IsMinSpanningForest es msfEs ∧
          steps ≤ C * (optDepthMN es.length n + es.length + n + 1) := by
  obtain ⟨r, C, pc, prog₀, hnw₀, frontier, _, hprog⟩ :=
    realizes_optimalMSFProg.exists_standard_basis_init_program_state_from_words (0 : Fin 1)
  let prog := stripRand prog₀
  refine ⟨r, 1814320 * C + 2, prog, not_readsWidth_stripRand hnw₀, isRandFree_stripRand prog₀, ?_⟩
  intro n es w hw_fit hfit
  have hwb := optimalMSFWordBound_ge n es.length
  have hlayout : ∀ j : Fin 2, (Kruskal.encode es).getD j.val 0 =
      WordEncoding.encode (⟨n, es.length⟩ : OptimalMSFArgs) j := fun j => by fin_cases j <;> rfl
  have hk_le : 2 ≤ (Kruskal.encode es).length := by rw [Kruskal.length_encode]; omega
  have hfit_len1 : Fits w ((Kruskal.encode es).length + 1) := by
    rw [Kruskal.length_encode]; exact hfit.of_le (by omega)
  have hin : InputFits w (Kruskal.encode es) :=
    Kruskal.inputFits_encode es (hfit.of_le (by omega)) hw_fit
  have hspec := optimalMSFProg_spec es hw_fit hfit
  dsimp only at hspec
  rcases hspec with ⟨hsafe, hv, msfEs, hmsf_msf, hmsf_len, hout_list, hfit_out, hcost⟩
  obtain ⟨y, steps0, hruns0, hhalt0, hmem0, _, hsteps0⟩ :=
    hprog w ⟨n, es.length⟩ (Kruskal.encode es) hlayout hk_le hfit_len1 hin hsafe hv
  have hres_w : (Memory.spec w).clientResult (Memory.State.init (Kruskal.encode es))
      (optimalMSFProg ⟨n, es.length⟩) =
      (Memory.spec 0).clientResult (Memory.State.init (Kruskal.encode es))
        (optimalMSFProg ⟨n, es.length⟩) := clientResult_width w _ _
  have hstate_w : (Memory.spec w).clientState (Memory.State.init (Kruskal.encode es))
      (optimalMSFProg ⟨n, es.length⟩) =
      (Memory.spec 0).clientState (Memory.State.init (Kruskal.encode es))
        (optimalMSFProg ⟨n, es.length⟩) := clientState_width w _ _
  have hout_eq : outputList y.mem (WordEncoding.encode (α := ℕ)
      ((Memory.spec w).clientResult (Memory.State.init (Kruskal.encode es))
        (optimalMSFProg ⟨n, es.length⟩)) 0) = Kruskal.encodeEdges msfEs := by
    have hmem_w : y.mem = ((Memory.spec 0).clientState (Memory.State.init (Kruskal.encode es))
        (optimalMSFProg ⟨n, es.length⟩)).mem := by
      change (memoryState frontier y).mem = _; rw [hmem0, hstate_w]
    change outputList y.mem ((Memory.spec w).clientResult (Memory.State.init (Kruskal.encode es))
      (optimalMSFProg ⟨n, es.length⟩)) = _
    rw [hres_w, hmem_w, hout_list]
  have hfit_list : Fits w (WordEncoding.encode (α := ℕ)
      ((Memory.spec w).clientResult (Memory.State.init (Kruskal.encode es))
        (optimalMSFProg ⟨n, es.length⟩)) 0 + (Kruskal.encodeEdges msfEs).length) := by
    change Fits w ((Memory.spec w).clientResult (Memory.State.init (Kruskal.encode es))
      (optimalMSFProg ⟨n, es.length⟩) + (Kruskal.encodeEdges msfEs).length)
    rw [hres_w, Kruskal.length_encodeEdges]; exact hfit_out
  have hex : ExecutesList w prog (State.init (Kruskal.encode es))
      (Kruskal.encodeEdges msfEs) (steps0 + 1) :=
    ⟨⟨pc, y⟩, steps0, _, runs_stripRand hruns0, step_stripRand_of_halt hhalt0,
      hout_eq, hfit_list, rfl⟩
  have hlog_n : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hbound : steps0 + 1 ≤
      (1814320 * C + 2) * (optDepthMN es.length n + es.length + n + 1) := by
    have hcost_w : memoryCost (optimalMSFProg ⟨n, es.length⟩)
        (Memory.State.init (Kruskal.encode es)) +
        (3 * (Nat.log 2 n + 3) + (es.length + 1)) + 1 ≤
        1814320 * (optDepthMN es.length n + es.length + n + 1) := by omega
    have hC1 : C * (1814320 * (optDepthMN es.length n + es.length + n + 1)) + 1 ≤
        (1814320 * C + 2) * (optDepthMN es.length n + es.length + n + 1) := by nlinarith
    dsimp only at hsteps0
    exact hsteps0.trans (by have hc_le := Nat.mul_le_mul_left C hcost_w; omega)
  exact ⟨steps0 + 1, msfEs, hex, hmsf_msf, hbound⟩

/-- Any multigraph minimum spanning forest `msfEs` of `graphEdges G wt` on a connected simple
graph `G : SimpleGraph (Fin n)` induces a Mathlib minimum spanning tree (`SimpleGraph.IsMST`)
`toSimpleGraph msfEs` of `G`. -/
theorem isMST_toSimpleGraph_of_isMinSpanningForest {n : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {wt : Sym2 (Fin n) → ℕ}
    (hconn : G.Connected) {msfEs : List (WeightedEdge n ℕ)}
    (hmsf : IsMinSpanningForest (graphEdges G wt) msfEs) :
    G.IsMST wt (toSimpleGraph msfEs) := by
  classical
  have hmax : Maximal (fun H => H ≤ G ∧ H.IsAcyclic) (toSimpleGraph msfEs) := by
    simpa only [toSimpleGraph_graphEdges] using hmsf.1.toSimpleGraph_maximal_isAcyclic
  have hle : toSimpleGraph msfEs ≤ G := hmax.prop.1
  have htree : (toSimpleGraph msfEs).IsTree := (hconn.maximal_le_isAcyclic_iff_isTree hle).mp hmax
  refine ⟨⟨hle, htree⟩, fun T' ⟨hle', hT'⟩ => ?_⟩
  rw [SimpleGraph.edgeWeightSum_eq_sum_edgeFinset, SimpleGraph.edgeWeightSum_eq_sum_edgeFinset]
  have hwt_msf : ∀ e ∈ msfEs, e.weight = wt e.sym2 := fun e he =>
    ((mem_graphEdges G wt e).mp (hmsf.1.1.subset he)).2.2
  have hsum_msf : (∑ z ∈ (toSimpleGraph msfEs).edgeFinset, wt z) = totalWeight msfEs := by
    have h := hmsf.1.2.1.sum_edgeFinset_toSimpleGraph wt hwt_msf; convert h
  have hsf_T' : IsSpanningForest (graphEdges G wt) (graphEdges T' wt) :=
    isSpanningForest_graphEdges_of_maximal_isAcyclic wt
      ((hconn.maximal_le_isAcyclic_iff_isTree hle').mpr hT')
  have hle_wt : totalWeight msfEs ≤ totalWeight (graphEdges T' wt) :=
    hmsf.2 (graphEdges T' wt) hsf_T'
  have hsum_T' : totalWeight (graphEdges T' wt) = ∑ z ∈ T'.edgeFinset, wt z := by
    convert totalWeight_graphEdges T' wt
  omega

/-- **Theorem 5.8 (`O(T*(m, n) + 1)` deterministic Word-RAM MST on connected simple graphs)**
([PettieRamachandran2002], Section 5.1, p. 27, #8624): on connected `G : SimpleGraph (Fin n)`
with `m = G.edgeFinset.card` edges and natural weights `wt : Sym2 (Fin n) → ℕ` (allowing ties),
for every word width `w : ℕ` satisfying `Fits w (optimalMSFWordBound n m)` (logarithmic width
suffices for this workspace threshold, with the additional `Fits w` condition for edge weights,
and any larger width `w` is allowed), the width-blind, random-free standard-basis program `prog`
computes `Kruskal.encodeEdges msfEs` in `steps ≤ C * (optDepthMN m n + 1)` instructions,
certifying both `IsMinSpanningForest (graphEdges G wt) msfEs` (so `msfEs` consists of `n - 1`
canonical, duplicate-free, loop-free edges of `G` with preserved weights `e.weight = wt e.sym2`
and exact total weight) and `G.IsMST wt (toSimpleGraph msfEs)` (`m ≤ n.choose 2` matches exact-`m`
`optDepthMN` via `optDepthMN_eq_exact`, spanning-tree connectivity gives `n ≤ m + 1`, and
`le_two_mul_optDepthMN` absorbs `m` and `n` for `3 ≤ m`). -/
theorem optimalMSF_simpleGraph_isMST_spec :
    ∃ r C : ℕ, ∃ prog : Program .standard r, ¬prog.ReadsWidth ∧ prog.IsRandFree ∧
      ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (wt : Sym2 (Fin n) → ℕ)
        (w : ℕ),
        G.Connected →
        (∀ e ∈ graphEdges G wt, Fits w e.weight) →
        Fits w (optimalMSFWordBound n G.edgeFinset.card) →
        ∃ steps : ℕ, ∃ msfEs : List (WeightedEdge n ℕ),
          ExecutesList w prog (State.init (Kruskal.encode (graphEdges G wt)))
            (Kruskal.encodeEdges msfEs) steps ∧
          IsMinSpanningForest (graphEdges G wt) msfEs ∧
          G.IsMST wt (toSimpleGraph msfEs) ∧
          steps ≤ C * (optDepthMN G.edgeFinset.card n + 1) := by
  classical
  obtain ⟨r, C, prog, hnw, hrf, hspec⟩ := optimalMSF_wordRAM_spec
  refine ⟨r, 6 * C, prog, hnw, hrf, fun n G _ wt w hconn hw_fit hfit => ?_⟩
  have hfit' : Fits w (optimalMSFWordBound n (graphEdges G wt).length) := by rwa [length_graphEdges]
  obtain ⟨steps, msfEs, hex, hmsf, hst⟩ := hspec n (graphEdges G wt) w hw_fit hfit'
  rw [length_graphEdges] at hst
  have hmst : G.IsMST wt (toSimpleGraph msfEs) :=
    isMST_toSimpleGraph_of_isMinSpanningForest hconn hmsf
  have hn_le : n ≤ G.edgeFinset.card + 1 := by
    have htree_card : (toSimpleGraph msfEs).edgeFinset.card + 1 = Fintype.card (Fin n) := by
      convert hmst.1.2.card_edgeFinset
    have hcard_le : (toSimpleGraph msfEs).edgeFinset.card ≤ G.edgeFinset.card :=
      Finset.card_le_card (SimpleGraph.edgeFinset_mono hmst.1.1)
    rw [Fintype.card_fin] at htree_card; omega
  have hm_le : G.edgeFinset.card ≤ n.choose 2 := by
    simpa [Fintype.card_fin] using G.card_edgeFinset_le_card_choose_two
  have hsum_le : optDepthMN G.edgeFinset.card n + G.edgeFinset.card + n + 1 ≤
      6 * (optDepthMN G.edgeFinset.card n + 1) := by
    by_cases hm3 : 3 ≤ G.edgeFinset.card
    · have hn3 : 3 ≤ n := by
        by_contra hn_lt
        have hc : ∀ k < 3, k.choose 2 ≤ 1 := by decide
        have := hc n (by omega); omega
      have := le_two_mul_optDepthMN hm3 hn3 hm_le; omega
    · omega
  exact ⟨steps, msfEs, hex, hmsf, hmst, hst.trans (by nlinarith)⟩

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
