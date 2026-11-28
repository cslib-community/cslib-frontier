/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Layout
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BoruvkaStages
import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Contraction.Robust
import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Decomp
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BaseOps
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.PartitionEval
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.Bridges
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.Outer
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Foundations.Data.List.Subperm
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize

/-!
# Borůvka–Partition Outer Loop Body for Optimal MSF

Word-RAM outer loop body (`pr02LoopBodyProg`) toward Section 2.1 (p. 18), Section 3.2
(pp. 21–22), Section 5 (pp. 23–24), and Section 5.1 (pp. 25–27, Theorem 5.8 p. 27) of
[PettieRamachandran2002] (#8624).

Each outer iteration executes three Borůvka contraction stages (`boruvkaThreeStageProg`), checks the
dense/small stopping criterion (`0 < m' ∧ 64 < n' ∧ 2 * m' < n' * r0`), and when still sparse and
large invokes `partitionProg`, decision-tree evaluation (`pr02EvalDTLoop`), remainder-graph MSF
solving (`pr02SolveHRemProg`), edge concatenation (`concatThreeProg`), deduplication
(`dedupSimpleEdgesProg`), and isolated-vertex compaction (`compactVerticesProg`). Using three
Borůvka stages (`8×` vertex reduction) adapts the paper's two-round Boruvka2 on connected graphs
to `Partition`'s fixed `ε = 1 / 16` (`partRankThreshold = 8`) on general non-isolated multigraphs
(`n ≤ 2 * m`). Together these cut vertices by at least `8×`, halve edges, halve `optDepthMN`,
preserve `MSFLiftInv`, preserve `tableFrontier` and already-written selected edge IDs
`selBuf[0..st.selLen)`, and amortize total memory operations and frontier growth against
`20000 * m + 5000 * n + 30 * optDepthMN m n + 110`.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PR02LoopEnv`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encPR02LoopEnv`: loop environment record and its
  3-word encoding `[r0, tableBase, selBuf]`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.PR02LoopState`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encPR02LoopState`: loop state record and its
  5-word encoding `[cont, numVerts, numEdges, edgeBase, selLen]`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02LoopBodyProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02LoopBodyProgSafe`: Word-RAM outer loop body
  and its safety precondition.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_pr02LoopBodyProg`: uniform
  `Realizes .exact` (`work = 0`) certificate for `pr02LoopBodyProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02LoopBodyProg_spec`: framed specification
  for `pr02LoopBodyProg` establishing `MSFLiftInv` preservation, halving/potential drop, and tight
  `Set.Ico (env.selBuf + st.selLen) (env.selBuf + es.length)` framing.

## References

* [PettieRamachandran2002]: Seth Pettie and Vijaya Ramachandran, "An Optimal Minimum Spanning
  Tree Algorithm", *JACM* 49(1), 2002, Section 2.1 (p. 18), Section 3.2 (pp. 21–22), Section 5
  (pp. 23–24), and Section 5.1 (pp. 25–27, Theorem 5.8 p. 27).
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest

/-! ## Section 1: Public Loop Records and Private Merging Subroutines -/

/-- Environment record for the `OptimalMSF` outer Borůvka–partition loop: precomputation vertex
threshold `r0`, precomputed decision-tree lookup table `tableBase`, and base address `selBuf`
of the selected original edge-ID accumulator buffer. -/
structure PR02LoopEnv where
  /-- Vertex threshold `r0 = Nat.iterLog 3 n₀`. -/
  r0 : ℕ
  /-- Base address of precomputed decision-tree lookup table. -/
  tableBase : ℕ
  /-- Base address of accumulated selected original edge IDs. -/
  selBuf : ℕ
  deriving DecidableEq

/-- Faithful 3-word encoding of `PR02LoopEnv` as `[r0, tableBase, selBuf]`. -/
word_enc_structure encPR02LoopEnv : PR02LoopEnv where
  r0 : wordWords,
  tableBase : wordWords,
  selBuf : wordWords

/-- Registered `WordEncoding` instance for `PR02LoopEnv`. -/
instance : WordEncoding PR02LoopEnv := ⟨3, encPR02LoopEnv⟩

/-- State record carried across iterations of the `OptimalMSF` outer loop: continuation flag
`cont`, active vertex count `numVerts`, active edge count `numEdges`, active stride-4
`IndexedEdge` array base `edgeBase`, and accumulated selected-ID count `selLen`. -/
structure PR02LoopState where
  /-- Continuation flag (`1` to continue, `0` when dense/small exit triggers). -/
  cont : ℕ
  /-- Current active vertex count `nCur`. -/
  numVerts : ℕ
  /-- Current active simple-edge count `mCur`. -/
  numEdges : ℕ
  /-- Base address of current active stride-4 `IndexedEdge` array. -/
  edgeBase : ℕ
  /-- Number of selected original edge IDs currently written in `selBuf[0..selLen)`. -/
  selLen : ℕ
  deriving DecidableEq

/-- Faithful 5-word encoding of `PR02LoopState` as
`[cont, numVerts, numEdges, edgeBase, selLen]`. -/
word_enc_structure encPR02LoopState : PR02LoopState where
  cont : wordWords,
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  selLen : wordWords

/-- Registered `WordEncoding` instance for `PR02LoopState`. -/
instance : WordEncoding PR02LoopState := ⟨5, encPR02LoopState⟩

private structure MergeNextArgs where
  numVerts : ℕ
  fcBase : ℕ
  fcLen : ℕ
  hlBase : ℕ
  hlLen : ℕ
  mcBase : ℕ
  mcLen : ℕ
  deriving DecidableEq

private word_enc_structure encMergeNextArgs : MergeNextArgs where
  numVerts : wordWords,
  fcBase : wordWords,
  fcLen : wordWords,
  hlBase : wordWords,
  hlLen : wordWords,
  mcBase : wordWords,
  mcLen : wordWords

private instance : WordEncoding MergeNextArgs := ⟨7, encMergeNextArgs⟩

private theorem optDepthMN_halves_potential {m m' n n' : ℕ} (hm : 2 * m' ≤ m) (hn : 8 * n' ≤ n) :
    2 * optDepthMN m' n' ≤ optDepthMN m n :=
  (two_mul_optDepthMN_le m' n').trans ((optDepthMN_mono_m hm).trans (optDepthMN_mono_n (by omega)))

private def pr02MergeNextProg (a : MergeNextArgs) : Memory.Prog GraphSlice := do
  let merged ← concatThreeProg ⟨a.fcBase, a.fcLen, a.hlBase, a.hlLen, a.mcBase, a.mcLen⟩
  let dd ← dedupSimpleEdgesProg ⟨a.numVerts, a.fcLen + a.hlLen + a.mcLen, merged.base⟩
  let cp ← compactVerticesProg dd
  pure ⟨cp.numVertices, dd.numEdges, cp.edgeBase⟩

private def pr02MergeNextProgSafe (w : ℕ) (a : MergeNextArgs) (s : Memory.State) : Prop :=
  let tot := a.fcLen + a.hlLen + a.mcLen
  Fits w 16 ∧
  concatThreeProgSafe w ⟨a.fcBase, a.fcLen, a.hlBase, a.hlLen, a.mcBase, a.mcLen⟩ s ∧
  let merged := (Memory.spec 0).clientResult s
    (concatThreeProg ⟨a.fcBase, a.fcLen, a.hlBase, a.hlLen, a.mcBase, a.mcLen⟩)
  let s₁ := (Memory.spec 0).clientState s
    (concatThreeProg ⟨a.fcBase, a.fcLen, a.hlBase, a.hlLen, a.mcBase, a.mcLen⟩)
  merged.base + 4 * tot ≤ s₁.frontier ∧
  Fits w (s₁.frontier + (13 * tot + 2 * a.numVerts)) ∧
  (∀ j < tot, s₁.mem (merged.base + 4 * j) < a.numVerts ∧
    s₁.mem (merged.base + 4 * j + 1) < a.numVerts) ∧
  let dd := (Memory.spec 0).clientResult s₁ (dedupSimpleEdgesProg ⟨a.numVerts, tot, merged.base⟩)
  let s₂ := (Memory.spec 0).clientState s₁ (dedupSimpleEdgesProg ⟨a.numVerts, tot, merged.base⟩)
  dd.edgeBase + 4 * dd.numEdges ≤ s₂.frontier ∧
  Fits w (s₂.frontier + (dd.numVertices + 4 * dd.numEdges + 1)) ∧
  ∀ j < dd.numEdges, s₂.mem (dd.edgeBase + 4 * j) < dd.numVertices ∧
    s₂.mem (dd.edgeBase + 4 * j + 1) < dd.numVertices

private theorem realizes_pr02MergeNextProg : Realizes .exact
    pr02MergeNextProg WordEncoding.encode WordEncoding.encode
    pr02MergeNextProgSafe (fun _ _ => 0) := by
  unfold pr02MergeNextProg
  realize [realizes_concatThreeProg, realizes_dedupSimpleEdgesProg, realizes_compactVerticesProg]
  all_goals
    rcases h with ⟨h16, hc, hmg, hfit1, hbd1, hdd, hfit2, hbd2⟩
    have hfront := hmem.frontier_fits
    first
    | exact h16 | exact hc | exact hmg | exact hfit1 | exact hbd1
    | exact hdd | exact hfit2 | exact hbd2 | fits

private theorem pr02MergeNextProg_spec {w n_orig n' nConglom fcBase hlBase mcBase : ℕ}
    {es : List (WeightedEdge n_orig ℕ)} {accIds : List (Fin es.length)}
    {es' : List (IndexedEdge n')}
    {rounds : List (PartitionRoundWitness n')} {H_rem : List (IndexedEdge n')}
    {conglomFn : Fin n' → Fin nConglom}
    {F_comps : List (List (IndexedEdge n'))} {H_lift : List (IndexedEdge n')}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hinv : MSFLiftInv es accIds es')
    (hperm : ((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
      (rounds.flatMap PartitionRoundWitness.corrEdges)).Perm es')
    (hcov : ∀ x : Fin n', ∃ r ∈ rounds, x ∈ r.verts)
    (hconglom_rel : ∀ x y : Fin n', conglomFn x = conglomFn y ↔
      (edgePartition (rounds.flatMap fun r => r.tree.treeEdges)).rel x y = true)
    (hrounds_part : ∀ i : Fin rounds.length,
      let r := rounds[i.val]'i.isLt
      r.tree.treeEdges.Subperm (r.compGlobal.map IndexedEdge.toWeighted) ∧
      (∀ x ∈ r.verts, x ∈ (Finset.univ.filter fun j : Fin rounds.length =>
          j.val < i.val).biUnion (fun j => rounds[j.val].verts) →
        ∃ hpos : 0 < r.tree.numSteps,
          x = r.tree.vOut ⟨r.tree.numSteps - 1, Nat.sub_lt hpos Nat.one_pos⟩))
    (huncorr_rem : ∀ i : Fin rounds.length, ∀ e ∈ H_rem,
      ¬(e.u ∈ (rounds[i.val]'i.isLt).verts ∧ e.v ∈ (rounds[i.val]'i.isLt).verts) ∧
      ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
        (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
          e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
        (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight)
    (huncorr_tree : ∀ i j : Fin rounds.length, i.val < j.val →
      ∀ e ∈ (rounds[j.val]'j.isLt).tree.treeEdges,
        ∀ s_step : Fin (rounds[i.val]'i.isLt).tree.numSteps,
          (e.u ∈ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val ↔
            e.v ∉ (rounds[i.val]'i.isLt).tree.treeVerts s_step.val) →
          (rounds[i.val]'i.isLt).tree.wPop s_step ≤ e.weight)
    (hF_len : F_comps.length = rounds.length)
    (hF_sub : ∀ i : Fin rounds.length,
      (F_comps[i.val]'(by omega)).Subperm (rounds[i.val]'i.isLt).compGlobal)
    (hF_msf : ∀ i : Fin rounds.length,
      IsMinSpanningForest ((rounds[i.val]'i.isLt).compGlobal.map IndexedEdge.toWeighted)
        ((F_comps[i.val]'(by omega)).map IndexedEdge.toWeighted))
    (hHL_sub : H_lift.Subperm H_rem)
    (hHL_msf : IsMinSpanningForest
      (contractEdgeList conglomFn (H_rem.map IndexedEdge.toWeighted))
      (contractEdgeList conglomFn (H_lift.map IndexedEdge.toWeighted)))
    (hfc_holds : HoldsIndexedEdges fcBase F_comps.flatten s.mem)
    (hfc_lt : fcBase + 4 * F_comps.flatten.length ≤ s.frontier)
    (hhl_holds : HoldsIndexedEdges hlBase H_lift s.mem)
    (hhl_lt : hlBase + 4 * H_lift.length ≤ s.frontier)
    (hmc_holds : HoldsIndexedEdges mcBase (rounds.flatMap PartitionRoundWitness.corrEdges) s.mem)
    (hmc_lt : mcBase + 4 * (rounds.flatMap PartitionRoundWitness.corrEdges).length ≤ s.frontier)
    (hfit : Fits w (s.frontier + 21 * (F_comps.flatten.length + H_lift.length +
      (rounds.flatMap PartitionRoundWitness.corrEdges).length) + 3 * n' + 1)) :
    let M_C := rounds.flatMap PartitionRoundWitness.corrEdges
    let a : MergeNextArgs := ⟨n', fcBase, F_comps.flatten.length, hlBase, H_lift.length, mcBase,
      M_C.length⟩
    pr02MergeNextProgSafe w a s ∧
    Memory.FramedTriple w s (pr02MergeNextProg a)
      (63 * (F_comps.flatten.length + H_lift.length + M_C.length) + 9 * n' + 9) ∅
      fun nxt s' =>
        nxt.numVertices ≤ 2 * nxt.numEdges ∧
        nxt.numVertices ≤ n' ∧
        nxt.numEdges ≤ F_comps.flatten.length + H_lift.length + M_C.length ∧
        s.frontier ≤ nxt.edgeBase ∧
        nxt.edgeBase + 4 * nxt.numEdges ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + 21 * (F_comps.flatten.length + H_lift.length + M_C.length) +
          3 * n' ∧
        Memory.WellFormed w s' ∧
        ∃ esNext : List (IndexedEdge nxt.numVertices),
          esNext.length = nxt.numEdges ∧
          HoldsIndexedEdges nxt.edgeBase esNext s'.mem ∧
          IsSimple (edgeEnds (esNext.map IndexedEdge.toWeighted)) ∧
          MSFLiftInv es accIds esNext := by
  let F_C := F_comps.flatten
  let M_C := rounds.flatMap PartitionRoundWitness.corrEdges
  let L_merged := F_C ++ H_lift ++ M_C
  have hmg_len : L_merged.length = F_C.length + H_lift.length + M_C.length := by
    simp [L_merged, Nat.add_assoc]
  have hsafe_cat : concatThreeProgSafe w
      ⟨fcBase, F_C.length, hlBase, H_lift.length, mcBase, M_C.length⟩ s :=
    ⟨h16, hfit.of_le (by dsimp only [F_C, M_C]; omega), hfc_lt, hhl_lt, hmc_lt⟩
  have h1 := concatThreeProg_spec (w := w) (n := n') (base1 := fcBase) (base2 := hlBase)
    (base3 := mcBase) (L1 := F_C) (L2 := H_lift) (L3 := M_C) (s := s)
    hwf hfc_holds hfc_lt hhl_holds hhl_lt hmc_holds hmc_lt
    (hfit.of_le (by dsimp only [F_C, M_C]; omega))
  have h1r := framedTriple_iff_realization.mp h1
  set merged := (Memory.spec 0).clientResult s
    (concatThreeProg ⟨fcBase, F_C.length, hlBase, H_lift.length, mcBase, M_C.length⟩)
  set s₁ := (Memory.spec 0).clientState s
    (concatThreeProg ⟨fcBase, F_C.length, hlBase, H_lift.length, mcBase, M_C.length⟩)
  obtain ⟨_, _, _, hmerged_eq, _, hs1_fr, hwf1, hholds1⟩ := h1r
  have hmg_base : merged.base = s.frontier := by rw [hmerged_eq]
  have hbd1 : ∀ j < L_merged.length, s₁.mem (merged.base + 4 * j) < n' ∧
      s₁.mem (merged.base + 4 * j + 1) < n' := fun j hj => by
    obtain ⟨hu, hv, _, _⟩ := hholds1 j hj
    exact ⟨hu ▸ (L_merged[j]'hj).u.isLt, hv ▸ (L_merged[j]'hj).v.isLt⟩
  have h2 := dedupSimpleEdgesProg_spec (w := w) (n := n') (edgeBase := merged.base)
    (es := L_merged) (s := s₁) h16 hwf1 hholds1 (by rw [hmg_base, hs1_fr, hmg_len])
    (hfit.of_le (by rw [hs1_fr, hmg_len]; dsimp only [F_C, M_C]; omega))
  rw [hmg_len] at h2
  have h2r := framedTriple_iff_realization.mp h2
  set dd := (Memory.spec 0).clientResult s₁
    (dedupSimpleEdgesProg ⟨n', F_C.length + H_lift.length + M_C.length, merged.base⟩)
  set s₂ := (Memory.spec 0).clientState s₁
    (dedupSimpleEdgesProg ⟨n', F_C.length + H_lift.length + M_C.length, merged.base⟩)
  obtain ⟨_, _, _, hdd_n, hdd_end, hs2_fr, hwf2, es_dd, hdd_len, hdd_sub, hholds2, _, _, _⟩ := h2r
  have hbd2 : ∀ j < dd.numEdges, s₂.mem (dd.edgeBase + 4 * j) < dd.numVertices ∧
      s₂.mem (dd.edgeBase + 4 * j + 1) < dd.numVertices := fun j hj => by
    have hj' : j < es_dd.length := hdd_len.symm ▸ hj
    obtain ⟨hu, hv, _, _⟩ := hholds2 j hj'
    rw [hdd_n]
    exact ⟨hu ▸ (es_dd[j]'hj').u.isLt, hv ▸ (es_dd[j]'hj').v.isLt⟩
  have hm_dd_le : es_dd.length ≤ F_C.length + H_lift.length + M_C.length := by
    rw [← hmg_len]; exact hdd_sub.length_le
  have hsafe_mrg : pr02MergeNextProgSafe w
      ⟨n', fcBase, F_C.length, hlBase, H_lift.length, mcBase, M_C.length⟩ s := by
    dsimp only [pr02MergeNextProgSafe]
    refine ⟨h16, hsafe_cat, by rw [hmg_base, hs1_fr], ?_, ?_, hdd_end, ?_, hbd2⟩
    · exact hfit.of_le (by rw [hs1_fr]; dsimp only [F_C, M_C]; omega)
    · intro j hj
      exact hbd1 j (by rw [hmg_len]; exact hj)
    · change Fits w (s₂.frontier + (dd.numVertices + 4 * dd.numEdges + 1))
      exact hfit.of_le
        (by rw [hs1_fr] at hs2_fr; rw [hdd_n, ← hdd_len]; dsimp only [F_C, M_C] at *; omega)
  refine ⟨hsafe_mrg, ?_⟩
  dsimp only [pr02MergeNextProg]
  refine (Memory.FramedTriple.bind_same
    (c₂ := 55 * (F_C.length + H_lift.length + M_C.length) + 9 * n' + 8)
    (h1.mono le_rfl fun blk₁ t₁ ⟨hblk₁, _, ht1_fr, hwt1, hth1⟩ => ?_)).mono
    (by dsimp only [F_C, M_C]; omega) fun _ _ h => h
  have hs_le_t1 : s.frontier ≤ t₁.frontier := by rw [ht1_fr]; omega
  have h2' := dedupSimpleEdgesProg_spec (w := w) (n := n') (edgeBase := blk₁.base) (es := L_merged)
    (s := t₁) h16 hwt1 hth1 (by rw [hblk₁, ht1_fr, hmg_len])
    (hfit.of_le (by rw [ht1_fr, hmg_len]; dsimp only [F_C, M_C]; omega))
  rw [hmg_len] at h2'
  have h2'm : Memory.FramedTriple w t₁
      (dedupSimpleEdgesProg ⟨n', F_C.length + H_lift.length + M_C.length, blk₁.base⟩)
      (41 * (F_C.length + H_lift.length + M_C.length) + 6 * n' + 6) ∅ fun dd' t₂ =>
        Memory.Modifies ∅ t₁ t₂ ∧ dd'.numVertices = n' ∧
        dd'.edgeBase + 4 * dd'.numEdges ≤ t₂.frontier ∧
        t₂.frontier ≤ t₁.frontier + (13 * (F_C.length + H_lift.length + M_C.length) + 2 * n') ∧
        Memory.WellFormed w t₂ ∧ ∃ esOut : List (IndexedEdge n'), esOut.length = dd'.numEdges ∧
          esOut.Subperm L_merged ∧ HoldsIndexedEdges dd'.edgeBase esOut t₂.mem ∧
          esOut.map IndexedEdge.toWeighted =
            dedupSimpleEdges (L_merged.map IndexedEdge.toWeighted) ∧
          IsSimple (edgeEnds (esOut.map IndexedEdge.toWeighted)) ∧
          ∀ e ∈ L_merged, e.u ≠ e.v → ∃ e' ∈ esOut, s(e'.u, e'.v) = s(e.u, e.v) ∧
            e'.weight ≤ e.weight :=
    Memory.Triple.mono h2' le_rfl fun _ _ ⟨hm, hq⟩ => ⟨hm, hm, hq⟩
  refine (Memory.FramedTriple.bind_same
    (c₂ := 14 * (F_C.length + H_lift.length + M_C.length) + 3 * n' + 2)
    (h2'm.mono le_rfl fun dd' t₂
        ⟨hmod_t1_t2, hdd'_n, hdd'_end, ht2_fr, hwt2, es_dd', hdd'_len, hdd'_sub, hholds2',
          hdedup_rep, hsimp2', _⟩ => ?_)).mono (by omega) fun _ _ h => h
  have hdd'_le : es_dd'.length ≤ L_merged.length := hdd'_sub.length_le
  have hm_dd'_le : es_dd'.length ≤ F_C.length + H_lift.length + M_C.length := by
    rw [← hmg_len]; exact hdd'_le
  have h3 := compactVerticesProg_spec (w := w) (n := n') (edgeBase := dd'.edgeBase)
    (es := es_dd') (s := t₂) h16 hwt2 hholds2' (by rw [hdd'_len]; exact hdd'_end)
    (hfit.of_le (by dsimp only [F_C, M_C] at *; omega))
  have hdd'_eq : (⟨n', es_dd'.length, dd'.edgeBase⟩ : GraphSlice) = dd' := by
    cases dd'; simp only at hdd'_n hdd'_len; rw [hdd'_n, hdd'_len]
  rw [hdd'_eq] at h3
  refine (Memory.FramedTriple.bind_same (c₂ := 0) (h3.mono le_rfl fun cp t₃
    ⟨_, hcp_eb, hcp_n, ht3_fr, hwt3, lift_next, esNext, hlift_inj, hnext_len, hholds3, _, hnoiso,
      hlift_eq⟩ => ?_)).mono (by omega) fun _ _ h => h
  have hinv_next : MSFLiftInv es accIds esNext := by
    have hFC_sub : F_C.Subperm (rounds.flatMap PartitionRoundWitness.compGlobal) := by
      rw [List.flatMap_def]
      refine List.Subperm.flatten_of_forall₂ (List.forall₂_iff_get.mpr ⟨by simp [hF_len],
        fun i hi1 hi2 => by simpa using hF_sub ⟨i, by omega⟩⟩)
    have hmerged_sub : L_merged.Subperm es' := by
      have h1_sub : (F_C ++ H_lift).Subperm
          ((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem) :=
        hFC_sub.append hHL_sub
      exact (h1_sub.append (List.Subperm.refl M_C)).trans hperm.subperm
    have hnext_id_sub : (esNext.map IndexedEdge.id).Subperm (es'.map IndexedEdge.id) := by
      have heq_id : esNext.map IndexedEdge.id = es_dd'.map IndexedEdge.id := by
        rw [← hlift_eq, List.map_map]; rfl
      rw [heq_id]
      exact List.subperm_map IndexedEdge.id (hdd'_sub.trans hmerged_sub)
    refine ⟨hinv.1, hnext_id_sub.nodup hinv.2.1, fun e he => ?_, fun i hi e he => ?_,
      fun L_next hL_sub hL_msf => ?_⟩
    · have hid := hnext_id_sub.subset (List.mem_map.mpr ⟨e, he, rfl⟩)
      obtain ⟨e', he', heq⟩ := List.mem_map.mp hid
      exact heq ▸ hinv.2.2.1 e' he'
    · have hid := hnext_id_sub.subset (List.mem_map.mpr ⟨e, he, rfl⟩)
      obtain ⟨e', he', heq⟩ := List.mem_map.mp hid
      exact heq ▸ hinv.2.2.2.1 i hi e' he'
    · let L_dd : List (IndexedEdge n') :=
        L_next.map fun e => ⟨lift_next e.u, lift_next e.v, e.weight, e.id⟩
      have hLdd_sub_dd : L_dd.Subperm es_dd' := by
        rw [← hlift_eq]; exact List.subperm_map _ hL_sub
      have hLdd_sub_es' : L_dd.Subperm es' := (hLdd_sub_dd.trans hdd'_sub).trans hmerged_sub
      have hm1 : L_dd.map IndexedEdge.toWeighted =
          contractEdgeList lift_next (L_next.map IndexedEdge.toWeighted) := by
        simp [L_dd, contractEdgeList, List.map_map, Function.comp, contractEdge,
          IndexedEdge.toWeighted]
      have hLdd_msf_dd : IsMinSpanningForest (es_dd'.map IndexedEdge.toWeighted)
          (L_dd.map IndexedEdge.toWeighted) := by
        rw [hm1]; exact compactVertices_isMinSpanningForest hlift_inj hlift_eq hL_msf
      have hLdd_msf_merged : IsMinSpanningForest (L_merged.map IndexedEdge.toWeighted)
          (L_dd.map IndexedEdge.toWeighted) :=
        isMinSpanningForest_of_dedupSimpleEdges _ _ (hdedup_rep ▸ hLdd_msf_dd)
      have hperm_w : (((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++ M_C).map
          IndexedEdge.toWeighted).Perm (es'.map IndexedEdge.toWeighted) := hperm.map _
      have hLdd_msf_es' : IsMinSpanningForest (es'.map IndexedEdge.toWeighted)
          (L_dd.map IndexedEdge.toWeighted) := by
        have hm_eq : L_merged.map IndexedEdge.toWeighted =
            (F_comps.map (List.map IndexedEdge.toWeighted)).flatten ++
              H_lift.map IndexedEdge.toWeighted ++ M_C.map IndexedEdge.toWeighted := by
          simp [L_merged, F_C, List.map_append, List.map_flatten]
        rw [hm_eq] at hLdd_msf_merged
        exact partition_isMinSpanningForest hperm_w hcov hconglom_rel hrounds_part huncorr_rem
          huncorr_tree (by simp [hF_len]) (fun i => by simpa using hF_msf i)
          (List.subperm_map _ hHL_sub) hHL_msf hLdd_msf_merged
      obtain ⟨remIds, hrem_val, hrem_msf⟩ := hinv.2.2.2.2 L_dd hLdd_sub_es' hLdd_msf_es'
      exact ⟨remIds, hrem_val.trans (by simp [L_dd, List.map_map, Function.comp]), hrem_msf⟩
  have ht1_le_t2 : t₁.frontier ≤ t₂.frontier := hmod_t1_t2.1
  dsimp only [F_C, M_C] at hm_dd'_le ht1_fr ht2_fr
  refine Memory.FramedTriple.pure ⟨?_, hcp_n, by dsimp only; omega, ?_, ?_, ?_, hwt3,
    esNext, hnext_len.trans hdd'_len, hholds3, compactVertices_isSimple hlift_eq hsimp2', hinv_next⟩
  · have hc := card_le_two_mul_of_noIsolated hnoiso
    dsimp only
    omega
  · dsimp only; rw [hcp_eb]; omega
  · dsimp only; rw [hcp_eb]; omega
  · omega

private def pr02LoopAfterBoruvka (p : PR02LoopEnv × BoruvkaStageResult) :
    Memory.Prog PR02LoopState := do
  let part ← partitionProg ⟨p.2.numVertices, p.2.numEdges, p.2.edgeBase, p.1.r0⟩
  let fcBase ← Memory.allocDirty (4 * p.2.numVertices)
  let fcLen ← pr02EvalDTLoop
    ⟨part.numComps, p.1.tableBase, part.compMetaBase, part.liftMetaBase, fcBase⟩
  let hl ← pr02SolveHRemProg ⟨part.nConglom, part.hRemBase, part.hRemLen, part.conglomBase⟩
  let nxt ← pr02MergeNextProg
    ⟨p.2.numVertices, fcBase, fcLen, hl.edgeBase, hl.numEdges, part.mcBase, part.mcLen⟩
  pure ⟨1, nxt.numVertices, nxt.numEdges, nxt.edgeBase, p.2.selOff⟩

private def pr02LoopAfterBoruvkaSafe (w : ℕ) (p : PR02LoopEnv × BoruvkaStageResult)
    (s : Memory.State) : Prop :=
  Fits w 16 ∧
  partitionProgSafe w ⟨p.2.numVertices, p.2.numEdges, p.2.edgeBase, p.1.r0⟩ s ∧
  let part := (Memory.spec 0).clientResult s
    (partitionProg ⟨p.2.numVertices, p.2.numEdges, p.2.edgeBase, p.1.r0⟩)
  let s₁ := (Memory.spec 0).clientState s
    (partitionProg ⟨p.2.numVertices, p.2.numEdges, p.2.edgeBase, p.1.r0⟩)
  Fits w (s₁.frontier + 4 * p.2.numVertices) ∧
  let fcBase := s₁.frontier
  let s₂ : Memory.State := ⟨s₁.mem, s₁.frontier + 4 * p.2.numVertices⟩
  pr02EvalDTLoopSafe w
    ⟨part.numComps, p.1.tableBase, part.compMetaBase, part.liftMetaBase, fcBase⟩ s₂ ∧
  let fcLen := (Memory.spec 0).clientResult s₂
    (pr02EvalDTLoop ⟨part.numComps, p.1.tableBase, part.compMetaBase, part.liftMetaBase, fcBase⟩)
  let s₃ := (Memory.spec 0).clientState s₂
    (pr02EvalDTLoop ⟨part.numComps, p.1.tableBase, part.compMetaBase, part.liftMetaBase, fcBase⟩)
  pr02SolveHRemProgSafe w ⟨part.nConglom, part.hRemBase, part.hRemLen, part.conglomBase⟩ s₃ ∧
  let hl := (Memory.spec 0).clientResult s₃
    (pr02SolveHRemProg ⟨part.nConglom, part.hRemBase, part.hRemLen, part.conglomBase⟩)
  let s₄ := (Memory.spec 0).clientState s₃
    (pr02SolveHRemProg ⟨part.nConglom, part.hRemBase, part.hRemLen, part.conglomBase⟩)
  pr02MergeNextProgSafe w
    ⟨p.2.numVertices, fcBase, fcLen, hl.edgeBase, hl.numEdges, part.mcBase, part.mcLen⟩ s₄

private theorem realizes_pr02LoopAfterBoruvka : Realizes .exact
    pr02LoopAfterBoruvka
    (appendWords (WordEncoding.encode (α := PR02LoopEnv))
      (WordEncoding.encode (α := BoruvkaStageResult)))
    (WordEncoding.encode (α := PR02LoopState))
    pr02LoopAfterBoruvkaSafe (fun _ _ => 0) := by
  unfold pr02LoopAfterBoruvka
  realize [realizes_partitionProg, realizes_pr02EvalDTLoop, realizes_pr02SolveHRemProg,
    realizes_pr02MergeNextProg]
  all_goals
    have hfront := hmem.frontier_fits
    first
    | exact h.2.1 | exact h.2.2.2.1 | exact h.2.2.2.2.1 | exact h.2.2.2.2.2
    | (have h16 := h.1; have hf := h.2.2.1; fits)

private theorem pr02LoopAfterBoruvka_spec {w n_orig n₀ r0 tableFrontier n_prev m_prev : ℕ}
    {es : List (WeightedEdge n_orig ℕ)} {env : PR02LoopEnv} {b3 : BoruvkaStageResult}
    {accIds : List (Fin es.length)} {es' : List (IndexedEdge b3.numVertices)}
    {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hr0_env : env.r0 = r0) (hr0_ge : 24 ≤ r0)
    (hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0)
    (hn_8 : 8 * b3.numVertices ≤ n_prev) (hn_4m : 4 * b3.numVertices ≤ m_prev)
    (hn_le_n0 : b3.numVertices ≤ n₀) (hm_le_prev : b3.numEdges ≤ m_prev)
    (hn_pos : 64 < b3.numVertices)
    (htab : HoldsDTTable r0 env.tableBase s.mem)
    (htib : DTTableInBounds r0 env.tableBase tableFrontier s.mem)
    (htf : tableFrontier ≤ s.frontier)
    (hes'_len : es'.length = b3.numEdges)
    (hholds_es' : HoldsIndexedEdges b3.edgeBase es' s.mem)
    (hedges_fr : b3.edgeBase + 4 * b3.numEdges ≤ s.frontier)
    (hsimp_es' : IsSimple (edgeEnds (es'.map IndexedEdge.toWeighted)))
    (hinv : MSFLiftInv es accIds es')
    (hfit : Fits w (s.frontier + 1100 * m_prev + 201 * n_prev + m_prev * r0 + 1100)) :
    pr02LoopAfterBoruvkaSafe w (env, b3) s ∧
    Memory.FramedTriple w s (pr02LoopAfterBoruvka (env, b3))
      (9747 * m_prev + 2982 * n_prev + 15 * optDepthMN m_prev n_prev + 26) ∅
      fun st' s' =>
        st'.cont = 1 ∧
        st'.selLen = b3.selOff ∧
        8 * st'.numVerts ≤ n_prev ∧
        2 * st'.numEdges ≤ m_prev ∧
        st'.numVerts ≤ 2 * st'.numEdges ∧
        st'.numVerts ≤ n₀ ∧
        s.frontier ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + 439 * m_prev + 201 * n_prev + m_prev * r0 + 75 ∧
        st'.edgeBase + 4 * st'.numEdges ≤ s'.frontier ∧
        Memory.WellFormed w s' ∧
        (∀ a < s.frontier, s'.mem a = s.mem a) ∧
        2 * optDepthMN st'.numEdges st'.numVerts ≤ optDepthMN m_prev n_prev ∧
        ∃ esNext : List (IndexedEdge st'.numVerts),
          esNext.length = st'.numEdges ∧
          HoldsIndexedEdges st'.edgeBase esNext s'.mem ∧
          IsSimple (edgeEnds (esNext.map IndexedEdge.toWeighted)) ∧
          MSFLiftInv es accIds esNext := by
  have hr0_pos : 1 ≤ r0 := by omega
  have hmul_b3 : b3.numEdges * r0 ≤ m_prev * r0 := Nat.mul_le_mul_right r0 hm_le_prev
  have hfit_part : Fits w (s.frontier + 1100 * (es'.length + b3.numVertices + 1)) := by
    rw [hes'_len]
    have h1 : s.frontier + 1100 * (b3.numEdges + b3.numVertices + 1) ≤
        s.frontier + 1100 * m_prev + 201 * n_prev + m_prev * r0 + 1100 := by
      have ha : 1100 * b3.numEdges ≤ 1100 * m_prev := Nat.mul_le_mul_left 1100 hm_le_prev
      omega
    exact hfit.of_le h1
  have hp := partitionProg_spec (w := w) (n := b3.numVertices) (edgeBase := b3.edgeBase)
    (maxsize := env.r0) (es := es') (s := s) h16 hwf (by omega) hholds_es'
    (by rw [hes'_len]; exact hedges_fr) hfit_part hsimp_es'
  dsimp only at hp
  rw [hes'_len] at hp
  generalize h_part : (Memory.spec 0).clientResult s
    (partitionProg ⟨b3.numVertices, b3.numEdges, b3.edgeBase, env.r0⟩) = part at hp
  generalize h_s2 : (Memory.spec 0).clientState s
    (partitionProg ⟨b3.numVertices, b3.numEdges, b3.edgeBase, env.r0⟩) = s₂ at hp
  rcases hp with ⟨hsafe_p, hv_p, hwf₂, hmod₂, hs2_ge, hs2_fr, hcost_p,
    hnumComps, hmcLen, hhRemLen, hnConglom, hcm_end, hlm_end, hmc_end, hhr_end, hcg_end,
    hne_bases, rounds, H_rem, conglomFn, hrounds_len, hhRem_len, hhRem_sub, hperm,
    hMC_len, hMC_holds, hHR_holds, hcg_mem, _, hcg_rel, hcov, hrounds_meta, hrounds_bounds,
    hstop, huncorr_rem, hshared_last, huncorr_tree⟩
  obtain ⟨hcm_ge, hlm_ge, hmc_ge, hhr_ge, hcg_ge⟩ := hne_bases (by omega)
  have hhRem_len_m : H_rem.length ≤ b3.numEdges := by rw [← hes'_len]; exact hhRem_sub.length_le
  let fcBase := s₂.frontier
  let s₃ : Memory.State := ⟨s₂.mem, s₂.frontier + 4 * b3.numVertices⟩
  have hfit_s3 : Fits w (s₂.frontier + 4 * b3.numVertices) := by
    have h1 : s₂.frontier + 4 * b3.numVertices ≤
        s.frontier + 1100 * m_prev + 201 * n_prev + m_prev * r0 + 1100 := by omega
    exact hfit.of_le h1
  have hwf₃ : Memory.WellFormed w s₃ := ⟨hfit_s3, hwf₂.mem_fits⟩
  have htab_s3 : HoldsDTTable r0 env.tableBase s₃.mem :=
    htab.congr htib fun a ha => hmod₂ a (ha.trans_le htf)
  have htib_s3 : DTTableInBounds r0 env.tableBase tableFrontier s₃.mem :=
    htib.mono le_rfl fun a ha => hmod₂ a (ha.trans_le htf)
  have hfit_ev : Fits w (s₃.frontier + 5 * b3.numEdges + b3.numEdges * r0) := by
    have h1 : s₃.frontier + 5 * b3.numEdges + b3.numEdges * r0 ≤
        s.frontier + 1100 * m_prev + 201 * n_prev + m_prev * r0 + 1100 := by
      dsimp only [s₃]; omega
    exact hfit.of_le h1
  have hev := pr02EvalDTLoop_spec (w := w) (r0 := r0) (tableFrontier := tableFrontier)
    (n := b3.numVertices) (m' := b3.numEdges) (rounds := rounds) (H_rem := H_rem) (es' := es')
    (tableBase := env.tableBase) (compMetaBase := part.compMetaBase)
    (liftMetaBase := part.liftMetaBase) (fcBase := fcBase) (s := s₃)
    h16 hwf₃ hsimp_es' hperm hes'_len.le (by rw [hrounds_len]; exact hnumComps) htab_s3 htib_s3
    (htf.trans hs2_ge) (by rw [hrounds_len]; exact hcm_end) (by rw [hrounds_len]; exact hlm_end)
    (by dsimp only [s₃, fcBase]; omega) (hr0_env ▸ hrounds_meta)
    (fun i => ⟨(hrounds_bounds i).1, (hrounds_bounds i).2.1⟩) hfit_ev
  dsimp only at hev
  obtain ⟨hsafe_ev, hev_ft⟩ := hev
  have hev_r := framedTriple_iff_realization.mp hev_ft
  generalize h_fcl : (Memory.spec 0).clientResult s₃
    (pr02EvalDTLoop ⟨rounds.length, env.tableBase, part.compMetaBase, part.liftMetaBase, fcBase⟩) =
    fcLen at hev_r
  generalize h_s4 : (Memory.spec 0).clientState s₃
    (pr02EvalDTLoop ⟨rounds.length, env.tableBase, part.compMetaBase, part.liftMetaBase, fcBase⟩) =
    s₄ at hev_r
  rcases hev_r with ⟨hv_ev, hcost_ev, hmod_ev, hfcl_le, hs4_ge, hs4_fr, hwf₄,
    F_comps, hF_len, hF_flat, hF_holds, hF_msf⟩
  have hmod₄ : ∀ a < s₃.frontier, a ∉ Set.Ico fcBase (fcBase + 4 * b3.numVertices) →
      s₄.mem a = s₃.mem a := hmod_ev.2
  have hHR_holds_s4 : HoldsIndexedEdges part.hRemBase H_rem s₄.mem :=
    hHR_holds.congr fun a _ ha =>
      hmod₄ a (by rw [← hhRem_len] at hhr_end; dsimp only [s₃, fcBase]; omega)
        (by rw [← hhRem_len] at hhr_end; simp only [Set.mem_Ico]; dsimp only [fcBase]; omega)
  have hcg_mem_s4 : ∀ u : Fin b3.numVertices,
      s₄.mem (part.conglomBase + u.val) = (conglomFn u).val := fun u =>
    (hmod₄ _ (by dsimp only [s₃, fcBase]; omega)
      (by simp only [Set.mem_Ico]; dsimp only [fcBase]; omega)).trans (hcg_mem u)
  have hfit_hr : Fits w (s₄.frontier + 341 * H_rem.length + 1529 * b3.numVertices + 3) := by
    have h1 : s₄.frontier + 341 * H_rem.length + 1529 * b3.numVertices + 3 ≤
        s.frontier + 1100 * m_prev + 201 * n_prev + m_prev * r0 + 1100 := by
      dsimp only [s₃] at hs4_fr; omega
    exact hfit.of_le h1
  have hrem_p := pr02SolveHRemProg_spec (w := w) (n' := b3.numVertices)
    (nConglom := part.nConglom) (n₀ := n₀) (r0 := r0) (hRemBase := part.hRemBase)
    (conglomBase := part.conglomBase) (rounds := rounds) (H_rem := H_rem)
    (conglomFn := conglomFn) (s := s₄) h16 hwf₄ hn_le_n0 hnConglom hr0_log hHR_holds_s4
    (by rw [← hhRem_len] at hhr_end; dsimp only [s₃, fcBase] at hs4_ge; omega) hcg_mem_s4
    (by dsimp only [s₃, fcBase] at hs4_ge; omega) hcov hcg_rel
    (fun i => by
      rcases hstop i with h1 | h2 | h3
      · exact Or.inl (hr0_env ▸ h1)
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr h3))
    hfit_hr
  dsimp only at hrem_p
  rw [hhRem_len] at hrem_p
  obtain ⟨hsafe_hr, hrem_ft⟩ := hrem_p
  have hrem_r := framedTriple_iff_realization.mp hrem_ft
  generalize h_hl : (Memory.spec 0).clientResult s₄
    (pr02SolveHRemProg ⟨part.nConglom, part.hRemBase, part.hRemLen, part.conglomBase⟩) =
    hl at hrem_r
  generalize h_s5 : (Memory.spec 0).clientState s₄
    (pr02SolveHRemProg ⟨part.nConglom, part.hRemBase, part.hRemLen, part.conglomBase⟩) =
    s₅ at hrem_r
  rcases hrem_r with ⟨hv_hr, hcost_hr, hmod_hr, hhl_end, hhl_mul, hhl_le_rem, hs5_ge, hs5_fr,
    hwf₅, H_lift, hHl_len, hHl_holds, hHl_sub, hHl_msf⟩
  have h96_sum : 96 * (F_comps.flatten.length + H_lift.length +
      (rounds.flatMap PartitionRoundWitness.corrEdges).length) ≤ 37 * m_prev := by
    have h1_fc : 4 * F_comps.flatten.length ≤ m_prev := by omega
    have h2_hl : 96 * H_lift.length ≤ m_prev := by
      have h2a : H_lift.length * 24 ≤ H_lift.length * r0 := Nat.mul_le_mul_left _ hr0_ge
      have h2c : H_lift.length * r0 ≤ b3.numVertices := by rw [hHl_len]; exact hhl_mul
      omega
    have h3_mc : 8 * (rounds.flatMap PartitionRoundWitness.corrEdges).length ≤ m_prev := by omega
    omega
  have hsum_le_es : F_comps.flatten.length + H_lift.length +
      (rounds.flatMap PartitionRoundWitness.corrEdges).length ≤ m_prev := by omega
  have hfc_holds_s5 : HoldsIndexedEdges fcBase F_comps.flatten s₅.mem :=
    hF_holds.congr fun a _ ha2 =>
      hmod_hr.2 a (by dsimp only [s₃, fcBase] at hs4_ge; rw [hF_flat] at ha2; omega) (by simp)
  have hMC_holds_s5 : HoldsIndexedEdges part.mcBase
      (rounds.flatMap PartitionRoundWitness.corrEdges) s₅.mem :=
    (hMC_holds.congr fun a _ _ =>
      hmod₄ a (by rw [← hMC_len] at hmc_end; dsimp only [s₃, fcBase]; omega)
        (by rw [← hMC_len] at hmc_end; simp only [Set.mem_Ico]; dsimp only [fcBase]; omega)).congr
      fun a _ _ => hmod_hr.2 a
        (by rw [← hMC_len] at hmc_end; dsimp only [s₃, fcBase] at hs4_ge; omega) (by simp)
  have hfit_mrg : Fits w (s₅.frontier + 21 * (F_comps.flatten.length + H_lift.length +
      (rounds.flatMap PartitionRoundWitness.corrEdges).length) + 3 * b3.numVertices + 1) := by
    have h1 : s₅.frontier + 21 * (F_comps.flatten.length + H_lift.length +
        (rounds.flatMap PartitionRoundWitness.corrEdges).length) + 3 * b3.numVertices + 1 ≤
        s.frontier + 1100 * m_prev + 201 * n_prev + m_prev * r0 + 1100 := by
      dsimp only [s₃] at hs4_fr; omega
    exact hfit.of_le h1
  have hmrg := @pr02MergeNextProg_spec w n_orig b3.numVertices part.nConglom fcBase hl.edgeBase
    part.mcBase es accIds es' rounds H_rem conglomFn F_comps H_lift s₅
    h16 hwf₅ hinv hperm hcov hcg_rel
    (fun i => ⟨(hrounds_bounds i).2.2.2.2.2, hshared_last i⟩)
    huncorr_rem huncorr_tree hF_len (fun i => (hF_msf i).1) (fun i => (hF_msf i).2)
    hHl_sub hHl_msf hfc_holds_s5 (by dsimp only [s₃, fcBase] at hs4_ge; omega)
    hHl_holds (by rw [hHl_len]; exact hhl_end)
    hMC_holds_s5 (by rw [← hMC_len] at hmc_end; dsimp only [s₃, fcBase] at hs4_ge; omega)
    hfit_mrg
  dsimp only at hmrg
  rw [hF_flat, hHl_len, hMC_len] at hmrg
  obtain ⟨hsafe_mg, hmrg_ft⟩ := hmrg
  have hmrg_r := framedTriple_iff_realization.mp hmrg_ft
  generalize h_nxt : (Memory.spec 0).clientResult s₅
    (pr02MergeNextProg ⟨b3.numVertices, fcBase, fcLen, hl.edgeBase, hl.numEdges, part.mcBase,
      part.mcLen⟩) = nxt at hmrg_r
  generalize h_s6 : (Memory.spec 0).clientState s₅
    (pr02MergeNextProg ⟨b3.numVertices, fcBase, fcLen, hl.edgeBase, hl.numEdges, part.mcBase,
      part.mcLen⟩) = s₆ at hmrg_r
  rcases hmrg_r with ⟨hv_mg, hcost_mg, hmod_mg, hnxt_2m, hnxt_n', hnxt_m, _,
    hnxt_end, hs6_fr, hwf₆, esNext, hnext_len, hnext_holds, hnext_simp, hinv_next⟩
  have hs6_ge : s₅.frontier ≤ s₆.frontier := hmod_mg.1
  have hsafe_after : pr02LoopAfterBoruvkaSafe w (env, b3) s := by
    refine ⟨h16, hsafe_p, ?_⟩
    rw [h_part, h_s2]
    refine ⟨hfit_s3, hrounds_len ▸ hsafe_ev, ?_⟩
    rw [← hrounds_len, h_fcl, h_s4]
    refine ⟨hsafe_hr, ?_⟩
    rw [h_hl, h_s5]
    exact hsafe_mg
  refine ⟨hsafe_after, ?_⟩
  have hafter_eq : pr02LoopAfterBoruvka (env, b3) =
      (partitionProg ⟨b3.numVertices, b3.numEdges, b3.edgeBase, env.r0⟩ >>= fun part' =>
        Memory.allocDirty (4 * b3.numVertices) >>= fun fcBase' =>
          pr02EvalDTLoop ⟨part'.numComps, env.tableBase, part'.compMetaBase, part'.liftMetaBase,
            fcBase'⟩ >>= fun fcLen' =>
            pr02SolveHRemProg ⟨part'.nConglom, part'.hRemBase, part'.hRemLen, part'.conglomBase⟩ >>=
              fun hl' =>
                pr02MergeNextProg ⟨b3.numVertices, fcBase', fcLen', hl'.edgeBase, hl'.numEdges,
                  part'.mcBase, part'.mcLen⟩ >>= fun nxt' =>
                    pure (α := PR02LoopState)
                      ⟨1, nxt'.numVertices, nxt'.numEdges, nxt'.edgeBase, b3.selOff⟩) := rfl
  have hvh_after : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (pr02LoopAfterBoruvka (env, b3))) := by
    rw [hafter_eq]
    refine validHistory_bind_step hv_p ?_
    rw [h_part, h_s2]
    refine validHistory_allocDirty_bind hfit_s3 ?_
    change (Memory.spec w).ValidHistory s₃ _
    rw [← hrounds_len]
    refine validHistory_bind_step hv_ev ?_
    rw [h_fcl, h_s4]
    refine validHistory_bind_step hv_hr ?_
    rw [h_hl, h_s5]
    exact validHistory_bind_step hv_mg (validHistory_pure w _ _)
  have hres_after : (Memory.spec 0).clientResult s (pr02LoopAfterBoruvka (env, b3)) =
      ⟨1, nxt.numVertices, nxt.numEdges, nxt.edgeBase, b3.selOff⟩ := by
    rw [hafter_eq, StateTransitionSpec.clientResult_bind, h_part, h_s2,
      clientResult_bind_allocDirty]
    change (Memory.spec 0).clientResult s₃ _ = _
    rw [← hrounds_len, StateTransitionSpec.clientResult_bind, h_fcl, h_s4,
      StateTransitionSpec.clientResult_bind, h_hl, h_s5,
      StateTransitionSpec.clientResult_bind, h_nxt, StateTransitionSpec.clientResult_pure]
  have hst_after : (Memory.spec 0).clientState s (pr02LoopAfterBoruvka (env, b3)) = s₆ := by
    rw [hafter_eq, StateTransitionSpec.clientState_bind, h_part, h_s2,
      clientState_bind_allocDirty]
    change (Memory.spec 0).clientState s₃ _ = _
    rw [← hrounds_len, StateTransitionSpec.clientState_bind, h_fcl, h_s4,
      StateTransitionSpec.clientState_bind, h_hl, h_s5,
      StateTransitionSpec.clientState_bind, h_s6, StateTransitionSpec.clientState_pure]
  have hcost_after : memoryCost (pr02LoopAfterBoruvka (env, b3)) s ≤
      9747 * m_prev + 2982 * n_prev + 15 * optDepthMN m_prev n_prev + 26 := by
    have hopt_cur : optDepthMN b3.numEdges b3.numVertices ≤ optDepthMN m_prev n_prev :=
      (optDepthMN_mono_m hm_le_prev).trans (optDepthMN_mono_n (by omega))
    rw [hafter_eq, memoryCost_bind', h_part, h_s2, memoryCost_bind', memoryCost_allocDirty,
      clientResult_allocDirty, clientState_allocDirty]
    rw [← hrounds_len, memoryCost_bind', h_fcl, h_s4, memoryCost_bind', h_hl, h_s5,
      memoryCost_bind', h_nxt, memoryCost_pure, add_zero]
    dsimp only [fcBase, s₃] at hcost_ev hcost_mg
    rw [hF_flat, hHl_len, hMC_len] at hsum_le_es
    omega
  have hmod_after : Memory.Modifies ∅ s s₆ := by
    refine ⟨hs2_ge.trans (by dsimp only [s₃] at hs4_ge; omega), fun a ha _ => ?_⟩
    have h1 := hmod₂ a ha
    have h4 := hmod₄ a (by dsimp only [s₃]; omega)
      (by simp only [Set.mem_Ico]; dsimp only [fcBase]; omega)
    have h5 := hmod_hr.2 a (by dsimp only [s₃, fcBase] at hs4_ge; omega) (by simp)
    have h6 := hmod_mg.2 a (by dsimp only [s₃, fcBase] at hs4_ge; omega) (by simp)
    exact h6.trans (h5.trans (h4.trans h1))
  refine framedTriple_iff_realization.mpr ⟨hvh_after, hcost_after, hst_after ▸ hmod_after, ?_⟩
  rw [hres_after, hst_after]
  have hnxt_2m_prev : 2 * nxt.numEdges ≤ m_prev := by
    rw [← hF_flat, ← hHl_len, ← hMC_len] at hnxt_m; omega
  have hnxt_8n_prev : 8 * nxt.numVertices ≤ n_prev := by omega
  have hs6_fr_bound :
      s₆.frontier ≤ s.frontier + 439 * m_prev + 201 * n_prev + m_prev * r0 + 75 := by
    dsimp only [s₃] at hs4_fr
    rw [← hF_flat, ← hHl_len, ← hMC_len] at hs6_fr
    omega
  refine ⟨rfl, rfl, hnxt_8n_prev, hnxt_2m_prev, hnxt_2m, by dsimp only; omega, hmod_after.1,
    hs6_fr_bound, hnxt_end, hwf₆, fun a ha => hmod_after.2 a ha (by simp),
    optDepthMN_halves_potential hnxt_2m_prev hnxt_8n_prev,
    esNext, hnext_len, hnext_holds, hnext_simp, hinv_next⟩

/-! ## Section 2: Outer Loop Body (`pr02LoopBodyProg`) and Framed Potential Specification -/

/-- One outer Borůvka–partition iteration of `OptimalMSF`: executes three Borůvka contraction
stages via `boruvkaThreeStageProg`, tests whether the active graph remains large and sparse
(`0 < b3.numEdges ∧ 64 < b3.numVertices ∧ 2 * b3.numEdges < b3.numVertices * env.r0`), and either
runs a full partition–DT–remainder–compaction round (`cont = 1`) or halts (`cont = 0`). -/
def pr02LoopBodyProg (p : PR02LoopEnv × PR02LoopState) : Memory.Prog PR02LoopState := do
  let b3 ← boruvkaThreeStageProg
    ⟨p.2.numVerts, p.2.numEdges, p.2.edgeBase, p.1.selBuf, p.2.selLen⟩
  if 0 < b3.numEdges ∧ 64 < b3.numVertices ∧ 2 * b3.numEdges < b3.numVertices * p.1.r0 then
    pr02LoopAfterBoruvka (p.1, b3)
  else
    pure ⟨0, b3.numVertices, b3.numEdges, b3.edgeBase, b3.selOff⟩

/-- Word-RAM safety precondition for `pr02LoopBodyProg`. -/
def pr02LoopBodyProgSafe (w : ℕ) (p : PR02LoopEnv × PR02LoopState) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w 64 ∧
  boruvkaThreeStageProgSafe w ⟨p.2.numVerts, p.2.numEdges, p.2.edgeBase, p.1.selBuf, p.2.selLen⟩ s ∧
  let b3 := (Memory.spec 0).clientResult s
    (boruvkaThreeStageProg ⟨p.2.numVerts, p.2.numEdges, p.2.edgeBase, p.1.selBuf, p.2.selLen⟩)
  let s₁ := (Memory.spec 0).clientState s
    (boruvkaThreeStageProg ⟨p.2.numVerts, p.2.numEdges, p.2.edgeBase, p.1.selBuf, p.2.selLen⟩)
  (0 < b3.numEdges → 64 < b3.numVertices →
    Fits w (2 * b3.numEdges) ∧ Fits w (b3.numVertices * p.1.r0)) ∧
  (0 < b3.numEdges ∧ 64 < b3.numVertices ∧ 2 * b3.numEdges < b3.numVertices * p.1.r0 →
    pr02LoopAfterBoruvkaSafe w (p.1, b3) s₁)

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `pr02LoopBodyProg`. -/
theorem realizes_pr02LoopBodyProg : Realizes .exact
    pr02LoopBodyProg
    (appendWords (WordEncoding.encode (α := PR02LoopEnv))
      (WordEncoding.encode (α := PR02LoopState)))
    (WordEncoding.encode (α := PR02LoopState))
    pr02LoopBodyProgSafe (fun _ _ => 0) := by
  unfold pr02LoopBodyProg
  realize [realizes_boruvkaThreeStageProg, realizes_pr02LoopAfterBoruvka]
  all_goals
    have hfront := hmem.frontier_fits
    first
    | exact h.2.2.1
    | exact h.2.2.2.2 ⟨by assumption, by assumption, by assumption⟩
    | (have h16 := h.1; have h64 := h.2.1
       try (have hmul := h.2.2.2.1 (by assumption) (by assumption)
            have h1 := hmul.1; have h2 := hmul.2)
       fits)

/-- Framed specification of one outer Borůvka–partition iteration `pr02LoopBodyProg`: runs
`boruvkaThreeStageProg`, preserves `MSFLiftInv`, `tableFrontier`, and previously accumulated IDs
`selBuf[0..st.selLen)` (modifying only `Set.Ico (env.selBuf + st.selLen) (env.selBuf + es.length)`),
halves edges and `optDepthMN` while reducing vertices by `8×` on continuation (`st'.cont = 1`),
and satisfies the closed-form cost and frontier potential inequalities. -/
theorem pr02LoopBodyProg_spec {w n_orig n₀ r0 tableFrontier nCur : ℕ}
    {es : List (WeightedEdge n_orig ℕ)} {env : PR02LoopEnv} {st : PR02LoopState}
    {accIds : List (Fin es.length)} {esCur : List (IndexedEdge nCur)} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hr0_env : env.r0 = r0) (hr0_ge : 24 ≤ r0)
    (hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0)
    (hn_eq : st.numVerts = nCur) (hm_eq : st.numEdges = esCur.length)
    (hn_le_n0 : nCur ≤ n₀) (hn_le_2m : nCur ≤ 2 * esCur.length)
    (htab : HoldsDTTable r0 env.tableBase s.mem)
    (htib : DTTableInBounds r0 env.tableBase tableFrontier s.mem)
    (htf : tableFrontier ≤ s.frontier)
    (htf_sel : tableFrontier ≤ env.selBuf)
    (hsel_fr : env.selBuf + es.length ≤ s.frontier)
    (hholds : HoldsIndexedEdges st.edgeBase esCur s.mem)
    (hedges_fr : st.edgeBase + 4 * esCur.length ≤ s.frontier)
    (hacc_len : accIds.length = st.selLen)
    (hacc_mem : ∀ j (hj : j < accIds.length), s.mem (env.selBuf + j) = accIds[j].val)
    (hinv : MSFLiftInv es accIds esCur)
    (hfit : Fits w (s.frontier + 1200 * esCur.length + 750 * nCur + 2 * esCur.length * r0 + 100)) :
    let prog := pr02LoopBodyProg (env, st)
    pr02LoopBodyProgSafe w (env, st) s ∧
    Memory.FramedTriple w s prog
      (20000 * esCur.length + 5000 * nCur + 30 * optDepthMN esCur.length nCur + 110)
      (Set.Ico (env.selBuf + st.selLen) (env.selBuf + es.length)) fun st' s' =>
      s.frontier ≤ s'.frontier ∧
      s'.frontier + (if st'.cont = 1 then
        1200 * st'.numEdges + 750 * st'.numVerts + 2 * st'.numEdges * r0 + 100 else 0) ≤
        s.frontier + 1200 * esCur.length + 750 * nCur + 2 * esCur.length * r0 + 100 ∧
      (st'.cont = 0 ∨ st'.cont = 1) ∧
      (st'.cont = 0 →
        st'.numEdges = 0 ∨ st'.numVerts ≤ 64 ∨ st'.numVerts * r0 ≤ 2 * st'.numEdges) ∧
      (st'.cont = 1 → 1 ≤ esCur.length ∧ 8 * st'.numVerts ≤ nCur ∧ 2 * st'.numEdges ≤ esCur.length ∧
        st'.numVerts ≤ 2 * st'.numEdges ∧ st'.numVerts ≤ n₀) ∧
      st'.numVerts ≤ n₀ ∧
      st'.numEdges ≤ esCur.length ∧
      st'.edgeBase + 4 * st'.numEdges ≤ s'.frontier ∧
      Memory.WellFormed w s' ∧
      (∀ a < tableFrontier, s'.mem a = s.mem a) ∧
      memoryCost prog s + (if st'.cont = 1 then
        20000 * st'.numEdges + 5000 * st'.numVerts + 30 * optDepthMN st'.numEdges st'.numVerts + 110
        else 0) ≤
        20000 * esCur.length + 5000 * nCur + 30 * optDepthMN esCur.length nCur + 110 ∧
      ∃ (accIds' : List (Fin es.length)) (esNext : List (IndexedEdge st'.numVerts)),
        esNext.length = st'.numEdges ∧
        HoldsIndexedEdges st'.edgeBase esNext s'.mem ∧
        IsSimple (edgeEnds (esNext.map IndexedEdge.toWeighted)) ∧
        accIds'.length = st'.selLen ∧
        (∀ j (hj : j < accIds'.length), s'.mem (env.selBuf + j) = accIds'[j].val) ∧
        MSFLiftInv es accIds' esNext := by
  have hsum_le : accIds.length + esCur.length ≤ es.length := hinv.sum_le
  let bArgs : BoruvkaStageArgs := ⟨nCur, esCur.length, st.edgeBase, env.selBuf, accIds.length⟩
  have hargs_eq : (⟨st.numVerts, st.numEdges, st.edgeBase, env.selBuf, st.selLen⟩ :
      BoruvkaStageArgs) = bArgs := by
    simp only [bArgs, hn_eq, hm_eq, hacc_len]
  have hsafe_b3 : boruvkaThreeStageProgSafe w bArgs s := by
    refine ⟨h16, hedges_fr, by dsimp only [bArgs]; omega,
      hfit.of_le (by dsimp only [bArgs]; omega), fun j hj => ?_⟩
    obtain ⟨hu, hv, _, _⟩ := hholds j hj
    exact ⟨hu ▸ (esCur[j]'hj).u.isLt, hv ▸ (esCur[j]'hj).v.isLt⟩
  have hb3 := boruvkaThreeStageProg_spec (w := w) (n := n_orig) (nCur := nCur)
    (edgeBase := st.edgeBase) (selBase := env.selBuf) (es := es) (accIds := accIds)
    (esCur := esCur) (s := s) h16 hwf hholds hedges_fr hacc_mem (by omega) hinv
    (hfit.of_le (by omega))
  have hb3_r := framedTriple_iff_realization.mp hb3
  change (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (boruvkaThreeStageProg bArgs)) ∧
    memoryCost (boruvkaThreeStageProg bArgs) s ≤ 234 * esCur.length + 108 * nCur + 102 ∧
    _ at hb3_r
  set b3 := (Memory.spec 0).clientResult s (boruvkaThreeStageProg bArgs)
  set s₁ := (Memory.spec 0).clientState s (boruvkaThreeStageProg bArgs)
  rcases hb3_r with ⟨hv_b3, hcost_b3, hmod_b3, hn'_8, hoff_ge, hsum_b3, _, heb'_fr, hs1_fr,
    hwf₁, acc1, es', hes'_len, hholds_es', hsimp_es', hacc1_len, hacc1_mem, hinv1⟩
  have hs1_ge : s.frontier ≤ s₁.frontier := hmod_b3.1
  have hm'_le_m : b3.numEdges ≤ esCur.length := by omega
  have hS0_sub : Set.Ico (env.selBuf + accIds.length) (env.selBuf + accIds.length + esCur.length) ⊆
      Set.Ico (env.selBuf + st.selLen) (env.selBuf + es.length) := fun x hx => by
    simp only [Set.mem_Ico] at hx ⊢; omega
  have hmod_b3_S : Memory.Modifies (Set.Ico (env.selBuf + st.selLen) (env.selBuf + es.length))
      s s₁ := hmod_b3.mono hS0_sub
  have hmod_tf_s1 : ∀ a < tableFrontier, s₁.mem a = s.mem a := fun a ha =>
    hmod_b3_S.2 a (ha.trans_le htf) (by simp only [Set.mem_Ico]; omega)
  have hfit_64 : Fits w 64 := hfit.of_le (by omega)
  have hfit_mul : 0 < b3.numEdges → 64 < b3.numVertices →
      Fits w (2 * b3.numEdges) ∧ Fits w (b3.numVertices * env.r0) := fun _ _ => by
    have hmul_b3 : b3.numEdges * r0 ≤ esCur.length * r0 := Nat.mul_le_mul_right r0 hm'_le_m
    have hmul_n_r0 : b3.numVertices * r0 ≤ 2 * esCur.length * r0 := by
      have : 2 * esCur.length * r0 = 2 * (esCur.length * r0) := Nat.mul_assoc _ _ _
      exact Nat.mul_le_mul_right r0 (by omega)
    rw [hr0_env]
    exact ⟨hfit.of_le (by omega), hfit.of_le (by omega)⟩
  have hprog_eq : pr02LoopBodyProg (env, st) =
      (boruvkaThreeStageProg bArgs >>= fun b3' =>
        if 0 < b3'.numEdges ∧ 64 < b3'.numVertices ∧
            2 * b3'.numEdges < b3'.numVertices * env.r0 then
          pr02LoopAfterBoruvka (env, b3')
        else
          pure ⟨0, b3'.numVertices, b3'.numEdges, b3'.edgeBase, b3'.selOff⟩) := by
    simp only [pr02LoopBodyProg, hargs_eq]
  by_cases hcont : 0 < b3.numEdges ∧ 64 < b3.numVertices ∧ 2 * b3.numEdges < b3.numVertices * env.r0
  · have hm_pos : 1 ≤ esCur.length := by omega
    have hn_gt512 : 512 < nCur := by omega
    have htab_s1 : HoldsDTTable r0 env.tableBase s₁.mem := htab.congr htib hmod_tf_s1
    have htib_s1 : DTTableInBounds r0 env.tableBase tableFrontier s₁.mem :=
      htib.mono le_rfl hmod_tf_s1
    have htf_s1 : tableFrontier ≤ s₁.frontier := htf.trans hs1_ge
    have hfit_af : Fits w (s₁.frontier + 1100 * esCur.length + 201 * nCur +
        esCur.length * r0 + 1100) := by
      have h2mul : 2 * esCur.length * r0 = 2 * (esCur.length * r0) := Nat.mul_assoc _ _ _
      exact hfit.of_le (by omega)
    have hafter := pr02LoopAfterBoruvka_spec (w := w) (n_orig := n_orig) (n₀ := n₀) (r0 := r0)
      (tableFrontier := tableFrontier) (n_prev := nCur) (m_prev := esCur.length) (es := es)
      (env := env) (b3 := b3) (accIds := acc1) (es' := es') (s := s₁)
      h16 hwf₁ hr0_env hr0_ge hr0_log hn'_8 (by omega) (by omega) hm'_le_m hcont.2.1
      htab_s1 htib_s1 htf_s1 hes'_len hholds_es' heb'_fr hsimp_es' hinv1 hfit_af
    obtain ⟨hsafe_af, hafter_ft⟩ := hafter
    have hafter_r := framedTriple_iff_realization.mp hafter_ft
    set nxt := (Memory.spec 0).clientResult s₁ (pr02LoopAfterBoruvka (env, b3))
    set s₂ := (Memory.spec 0).clientState s₁ (pr02LoopAfterBoruvka (env, b3))
    rcases hafter_r with ⟨hv_af, hcost_af, hmod_af, hnxt_cont, hnxt_sel, hnxt_8n, hnxt_2m_prev,
      hnxt_2m, hnxt_n0, hs2_ge, hs2_fr, hnxt_eb, hwf₂, hmod_s1_s2, hopt_halve,
      esNext, hnext_len, hnext_holds, hnext_simp, hinv_next⟩
    refine ⟨⟨h16, hfit_64, hargs_eq.symm ▸ hsafe_b3, ?_, ?_⟩, ?_⟩
    · rw [hargs_eq]; exact hfit_mul
    · intro _; rw [hargs_eq]; exact hsafe_af
    · have hvh : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (pr02LoopBodyProg (env, st))) := by
        rw [hprog_eq]; refine validHistory_bind_step hv_b3 ?_
        rw [ite_eq_left hcont]; exact hv_af
      have hres_pos : (Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st)) = nxt := by
        rw [hprog_eq, StateTransitionSpec.clientResult_bind, ite_eq_left hcont]
      have hst_pos : (Memory.spec 0).clientState s (pr02LoopBodyProg (env, st)) = s₂ := by
        rw [hprog_eq, StateTransitionSpec.clientState_bind, ite_eq_left hcont]
      have hcost_body : memoryCost (pr02LoopBodyProg (env, st)) s +
          (20000 * nxt.numEdges + 5000 * nxt.numVerts +
            30 * optDepthMN nxt.numEdges nxt.numVerts + 110) ≤
          20000 * esCur.length + 5000 * nCur + 30 * optDepthMN esCur.length nCur + 110 := by
        rw [hprog_eq, memoryCost_bind', ite_eq_left hcont]
        dsimp only [b3, s₁] at hcost_af
        omega
      have hmod_all : Memory.Modifies (Set.Ico (env.selBuf + st.selLen) (env.selBuf + es.length))
          s s₂ := hmod_b3_S.trans (hmod_af.mono (Set.empty_subset _))
      refine framedTriple_iff_realization.mpr ⟨hvh, by omega, hst_pos ▸ hmod_all, ?_⟩
      rw [hres_pos, hst_pos]
      have hmul_nxt_r0 : 2 * nxt.numEdges * r0 ≤ esCur.length * r0 :=
        Nat.mul_le_mul_right r0 hnxt_2m_prev
      refine ⟨hmod_all.1, ?_, Or.inr hnxt_cont, fun h => by omega,
        fun _ => ⟨hm_pos, hnxt_8n, hnxt_2m_prev, hnxt_2m, hnxt_n0⟩, hnxt_n0, by omega, hnxt_eb,
        hwf₂, fun a ha => (hmod_s1_s2 a (ha.trans_le htf_s1)).trans (hmod_tf_s1 a ha), ?_,
        acc1, esNext, hnext_len, hnext_holds, hnext_simp, hacc1_len.trans hnxt_sel.symm,
        fun j hj => (hmod_s1_s2 _ (by have := hinv1.sum_le; omega)).trans (hacc1_mem j hj),
        hinv_next⟩
      · simp only [hnxt_cont, ↓reduceIte]
        have h2mul : 2 * esCur.length * r0 = 2 * (esCur.length * r0) := Nat.mul_assoc _ _ _
        have h2mul' : 2 * nxt.numEdges * r0 = 2 * (nxt.numEdges * r0) := Nat.mul_assoc _ _ _
        omega
      · simp only [hnxt_cont, ↓reduceIte]
        exact hcost_body
  · refine ⟨⟨h16, hfit_64, hargs_eq.symm ▸ hsafe_b3, ?_, ?_⟩, ?_⟩
    · rw [hargs_eq]; exact hfit_mul
    · intro hc; rw [hargs_eq] at hc; exact absurd hc hcont
    · have hvh : (Memory.spec w).ValidHistory s
          ((Memory.spec w).clientHistory s (pr02LoopBodyProg (env, st))) := by
        rw [hprog_eq]; refine validHistory_bind_step hv_b3 ?_
        rw [ite_eq_right hcont]; exact validHistory_pure w _ _
      have hres_exit : (Memory.spec 0).clientResult s (pr02LoopBodyProg (env, st)) =
          ⟨0, b3.numVertices, b3.numEdges, b3.edgeBase, b3.selOff⟩ := by
        rw [hprog_eq, StateTransitionSpec.clientResult_bind, ite_eq_right hcont,
          StateTransitionSpec.clientResult_pure]
      have hst_exit : (Memory.spec 0).clientState s (pr02LoopBodyProg (env, st)) = s₁ := by
        rw [hprog_eq, StateTransitionSpec.clientState_bind, ite_eq_right hcont,
          StateTransitionSpec.clientState_pure]
      have hcost_exit : memoryCost (pr02LoopBodyProg (env, st)) s ≤
          234 * esCur.length + 108 * nCur + 102 := by
        rw [hprog_eq, memoryCost_bind', ite_eq_right hcont, memoryCost_pure, add_zero]
        exact hcost_b3
      refine framedTriple_iff_realization.mpr ⟨hvh, by omega, hst_exit ▸ hmod_b3_S, ?_⟩
      rw [hres_exit, hst_exit]
      dsimp only
      refine ⟨hs1_ge, by simp only [Nat.zero_ne_one, ↓reduceIte, add_zero]; omega,
        Or.inl rfl, fun _ => ?_, fun h => by simp at h, by omega,
        hm'_le_m, heb'_fr, hwf₁, hmod_tf_s1,
        by simp only [Nat.zero_ne_one, ↓reduceIte, add_zero]; omega,
        acc1, es', hes'_len, hholds_es', hsimp_es', hacc1_len, hacc1_mem, hinv1⟩
      rw [← hr0_env]; omega

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
