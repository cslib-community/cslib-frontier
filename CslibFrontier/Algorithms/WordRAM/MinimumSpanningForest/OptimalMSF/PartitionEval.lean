/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Layout
public import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.Bridges
public import CslibFrontier.Foundations.Data.Nat.IterLog
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DecisionTree.Eval
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.DenseCase.Driver
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.GraphOps.Components
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.OptimalMSF.BaseOps
import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.DjpLoop
import CslibFrontier.Computability.WordRAM.Realization.LoopFrame
import CslibFrontier.Foundations.Data.List.Subperm
import CslibFrontier.Tactic.Fits
import CslibFrontier.Tactic.Realize
import CslibFrontier.Tactic.ValidProg
import Mathlib.Tactic.Linarith

/-!
# Partition Component Evaluation and Remainder MSF Solver

Word-RAM partition-round decision-tree evaluation and remainder-graph contraction subroutines toward
Section 5 (pp. 23–24) and Section 5.1 (pp. 25–27, Theorem 5.8 p. 27) of
[PettieRamachandran2002] (#8624):

1. Component decision-tree evaluation (`pr02EvalDTLoop`): reads per-round `(numVerts, numEdges,
   edgeBase)` and vertex-lift metadata, evaluates each simple partition component using
   `evalDecisionTreeProg`, lifts the resulting local MSF edges to global indices via
   `liftEdgesProg`, and concatenates them into `fcBase` in `O(m' + optDepthMN m' n + n)` time.
2. Remainder-graph solver (`pr02SolveHRemProg`): retags uncorrupted remainder edges `H_rem`,
   contracts endpoints onto conglomerate labels (`contractEdgesProg`, `compactVerticesProg`), solves
   the dense contracted graph via `denseCaseProg`, and lifts selected original `H_rem` edges via
   `liftHRemProg` in `O(|H_rem| + n')` time.

## Main definitions

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.EvalDTLoopArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encEvalDTLoopArgs`: argument bundle and encoding
  for `pr02EvalDTLoop`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.SolveHRemArgs`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encSolveHRemArgs`: argument bundle and encoding
  for `pr02SolveHRemProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.SolveHRemResult`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.encSolveHRemResult`: result bundle and encoding
  for `pr02SolveHRemProg`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02EvalDTLoop`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02EvalDTLoopSafe`: partition-round decision-tree
  evaluation loop and its safety domain.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02SolveHRemProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02SolveHRemProgSafe`: remainder-graph MSF
  subroutine returning a `SolveHRemResult` and its safety domain.

## Main results

* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_pr02EvalDTLoop`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02EvalDTLoop_spec`: uniform `Realizes .exact`
  (`work = 0`) and `Memory.FramedTriple` specification for `pr02EvalDTLoop`.
* `Cslib.Algorithms.WordRAM.MinimumSpanningForest.realizes_pr02SolveHRemProg`,
  `Cslib.Algorithms.WordRAM.MinimumSpanningForest.pr02SolveHRemProg_spec`: uniform
  `Realizes .exact` (`work = 0`) and `Memory.FramedTriple` specification for `pr02SolveHRemProg`.

## References

* [S. Pettie and V. Ramachandran, *An Optimal Minimum Spanning Tree
  Algorithm*][PettieRamachandran2002], Section 5 (pp. 23–24) and Section 5.1 (pp. 25–27,
  Theorem 5.8 p. 27).
-/

public section

namespace Cslib.Algorithms.WordRAM.MinimumSpanningForest

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.Algorithms.Lean.Kruskal Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest.DenseCase

/-! ## Public Argument Bundles -/

/-- Input arguments for `pr02EvalDTLoop`: round count, decision-tree lookup table base, component
metadata array base, lift-table metadata array base, and global output buffer base. -/
structure EvalDTLoopArgs where
  /-- Number of partition rounds `rounds.length`. -/
  numRounds : ℕ
  /-- Base address of precomputed decision-tree lookup table. -/
  tableBase : ℕ
  /-- Base address of 3-word `(numVerts, numEdges, edgeBase)` component metadata records. -/
  compMetaBase : ℕ
  /-- Base address of per-round vertex-lift array pointers. -/
  liftMetaBase : ℕ
  /-- Base address of global output stride-4 `IndexedEdge` buffer. -/
  fcBase : ℕ
  deriving DecidableEq

/-- Faithful 5-word encoding of `EvalDTLoopArgs` as
`[numRounds, tableBase, compMetaBase, liftMetaBase, fcBase]`. -/
word_enc_structure encEvalDTLoopArgs : EvalDTLoopArgs where
  numRounds : wordWords,
  tableBase : wordWords,
  compMetaBase : wordWords,
  liftMetaBase : wordWords,
  fcBase : wordWords

/-- Registered `WordEncoding` instance for `EvalDTLoopArgs`. -/
instance : WordEncoding EvalDTLoopArgs := ⟨5, encEvalDTLoopArgs⟩

/-- Input arguments for `pr02SolveHRemProg`: conglomerate count, base and length of remaining
uncorrupted edges `H_rem`, and conglomerate label map base. -/
structure SolveHRemArgs where
  /-- Number of conglomerate vertices `nConglom`. -/
  numConglom : ℕ
  /-- Base address of stride-4 remaining edges `H_rem`. -/
  hRemBase : ℕ
  /-- Number of edges in `H_rem`. -/
  hRemLen : ℕ
  /-- Base address of `n'`-word array mapping each vertex to its conglomerate label. -/
  conglomBase : ℕ
  deriving DecidableEq

/-- Faithful 4-word encoding of `SolveHRemArgs` as
`[numConglom, hRemBase, hRemLen, conglomBase]`. -/
word_enc_structure encSolveHRemArgs : SolveHRemArgs where
  numConglom : wordWords,
  hRemBase : wordWords,
  hRemLen : wordWords,
  conglomBase : wordWords

/-- Registered `WordEncoding` instance for `SolveHRemArgs`. -/
instance : WordEncoding SolveHRemArgs := ⟨4, encSolveHRemArgs⟩

/-- Output of `pr02SolveHRemProg`: base address and edge count of the lifted stride-4 `H_lift`
edge array. -/
structure SolveHRemResult where
  /-- Base address of the freshly allocated stride-4 lifted `H_lift` edge array. -/
  edgeBase : ℕ
  /-- Number of edges in `H_lift`. -/
  numEdges : ℕ
  deriving DecidableEq

/-- Faithful 2-word encoding of `SolveHRemResult` as `[edgeBase, numEdges]`. -/
word_enc_structure encSolveHRemResult : SolveHRemResult where
  edgeBase : wordWords,
  numEdges : wordWords

/-- Registered `WordEncoding` instance for `SolveHRemResult`. -/
instance : WordEncoding SolveHRemResult := ⟨2, encSolveHRemResult⟩

/-! ## Private Helper Records and Combinatorial Lemmas -/

private structure CompMetaArgs where
  compMetaBase : ℕ
  liftMetaBase : ℕ
  idx : ℕ
  deriving DecidableEq

private word_enc_structure encCompMetaArgs : CompMetaArgs where
  compMetaBase : wordWords,
  liftMetaBase : wordWords,
  idx : wordWords

private instance : WordEncoding CompMetaArgs := ⟨3, encCompMetaArgs⟩

private structure CompMeta where
  numVerts : ℕ
  numEdges : ℕ
  edgeBase : ℕ
  liftBase : ℕ
  deriving DecidableEq

private word_enc_structure encCompMeta : CompMeta where
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  liftBase : wordWords

private instance : WordEncoding CompMeta := ⟨4, encCompMeta⟩

private structure EvalAndLiftArgs where
  tableBase : ℕ
  numVerts : ℕ
  numEdges : ℕ
  edgeBase : ℕ
  liftBase : ℕ
  fcBase : ℕ
  fcLen : ℕ
  deriving DecidableEq

private word_enc_structure encEvalAndLiftArgs : EvalAndLiftArgs where
  tableBase : wordWords,
  numVerts : wordWords,
  numEdges : wordWords,
  edgeBase : wordWords,
  liftBase : wordWords,
  fcBase : wordWords,
  fcLen : wordWords

private instance : WordEncoding EvalAndLiftArgs := ⟨7, encEvalAndLiftArgs⟩

private structure EvalDTLoopState where
  idx : ℕ
  fcLen : ℕ
  deriving DecidableEq

private word_enc_structure encEvalDTLoopState : EvalDTLoopState where
  idx : wordWords,
  fcLen : wordWords

private instance : WordEncoding EvalDTLoopState := ⟨2, encEvalDTLoopState⟩

private theorem sum_verts_sub_one_le {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (lens : List ℕ) (hlen : lens.length = rounds.length)
    (hle : ∀ i : Fin rounds.length,
      lens[i.val]'(by omega) ≤ (rounds[i.val]'i.isLt).verts.card - 1)
    (hinter : ∀ i : Fin rounds.length,
      ((rounds[i.val]'i.isLt).verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
        j.val < i.val).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card ≤ 1) :
    lens.sum ≤ n := by
  have haux : ∀ k (_hk : k ≤ rounds.length),
      (lens.take k).sum ≤ ((Finset.univ.filter fun j : Fin rounds.length =>
        j.val < k).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hk_lt : k < rounds.length := by omega
      have htake : lens.take (k + 1) = lens.take k ++ [lens[k]'(by omega)] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some]
      rw [htake, List.sum_append, List.sum_singleton]
      let U : Finset (Fin n) := (Finset.univ.filter fun j : Fin rounds.length =>
        j.val < k).biUnion (fun j => (rounds[j.val]'j.isLt).verts)
      have hU_succ : (Finset.univ.filter fun j : Fin rounds.length =>
          j.val < k + 1).biUnion (fun j => (rounds[j.val]'j.isLt).verts) =
          U ∪ (rounds[k]'hk_lt).verts := by
        ext x
        simp only [U, Finset.mem_union, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · rintro ⟨j, hj, hxj⟩
          by_cases hjk : j.val < k
          · exact Or.inl ⟨j, hjk, hxj⟩
          · rcases j with ⟨jv, hjv⟩
            have hjk_eq : jv = k := by simp only at hj hjk; omega
            subst hjk_eq
            exact Or.inr hxj
        · rintro (⟨j, hj, hxj⟩ | hxk)
          · exact ⟨j, Nat.lt_succ_of_lt hj, hxj⟩
          · exact ⟨⟨k, hk_lt⟩, Nat.lt_succ_self k, hxk⟩
      rw [hU_succ]
      have hcap := Finset.card_union_add_card_inter U (rounds[k]'hk_lt).verts
      have hk_val : (⟨k, hk_lt⟩ : Fin rounds.length).val = k := rfl
      have hi1 : ((rounds[k]'hk_lt).verts ∩ U).card ≤ 1 := by
        simpa only [hk_val] using hinter ⟨k, hk_lt⟩
      have hcard_pos : ((rounds[k]'hk_lt).verts ∩ U).card ≤ (rounds[k]'hk_lt).verts.card :=
        Finset.card_le_card Finset.inter_subset_left
      rw [Finset.inter_comm] at hcap
      have hl : lens[k]'(by omega) ≤ (rounds[k]'hk_lt).verts.card - 1 := by
        simpa only [hk_val] using hle ⟨k, hk_lt⟩
      have ih' := ih (by omega)
      dsimp only [U] at *
      omega
  have h1 := haux rounds.length le_rfl
  rw [List.take_of_length_le (by omega)] at h1
  have hle_n : ((Finset.univ.filter fun j : Fin rounds.length =>
      j.val < rounds.length).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card ≤ n := by
    calc ((Finset.univ.filter fun j : Fin rounds.length =>
          j.val < rounds.length).biUnion (fun j => (rounds[j.val]'j.isLt).verts)).card
        ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_univ _
      _ = n := Fintype.card_fin n
  exact h1.trans hle_n

private theorem sum_verts_sub_one_take_le {n : ℕ} (rounds : List (PartitionRoundWitness n))
    (hinter : ∀ i : Fin rounds.length,
      (rounds[i.val].verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
        j.val < i.val).biUnion (fun j => rounds[j.val].verts)).card ≤ 1)
    (k : ℕ) : ((rounds.take k).map fun r => r.verts.card - 1).sum ≤ n := by
  let lens := (rounds.take k).map fun r => r.verts.card - 1
  refine sum_verts_sub_one_le (rounds.take k) lens (by simp [lens]) (fun i => by
    simp [lens]) fun i => ?_
  have hi_take : i.val < min k rounds.length := by
    have := i.isLt
    simp only [List.length_take] at this
    exact this
  have hi_r : i.val < rounds.length := Nat.lt_of_lt_of_le hi_take (min_le_right _ _)
  have h1 := hinter ⟨i.val, hi_r⟩
  refine le_trans (Finset.card_le_card (Finset.inter_subset_inter ?_ ?_)) h1
  · simp [List.getElem_take]
  · intro x hx
    rw [Finset.mem_biUnion] at hx ⊢
    obtain ⟨j, hj, hxj⟩ := hx
    rw [Finset.mem_filter] at hj
    have hj_r : j.val < rounds.length := Nat.lt_of_lt_of_le j.isLt (by simp)
    refine ⟨⟨j.val, hj_r⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.2⟩, ?_⟩
    simpa [List.getElem_take] using hxj

/-! ## Private Metadata Read and Decision-Tree Evaluation Helpers -/

private def readCompMeta (a : CompMetaArgs) : Memory.Prog CompMeta := do
  let vi ← Memory.read (a.compMetaBase + 3 * a.idx)
  let mi ← Memory.read (a.compMetaBase + 3 * a.idx + 1)
  let eb ← Memory.read (a.compMetaBase + 3 * a.idx + 2)
  let lb ← Memory.read (a.liftMetaBase + a.idx)
  pure ⟨vi, mi, eb, lb⟩

private def readCompMetaSafe (w : ℕ) (a : CompMetaArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  a.compMetaBase + 3 * a.idx + 2 < s.frontier ∧
  a.liftMetaBase + a.idx < s.frontier

private theorem realizes_readCompMeta : Realizes .exact
    readCompMeta WordEncoding.encode WordEncoding.encode
    readCompMetaSafe (fun _ _ => 0) := by
  unfold readCompMeta
  realize
  all_goals
    have h16 := h.1
    have hlt1 := h.2.1
    have hlt2 := h.2.2
    have hfront := hmem.frontier_fits
    fits

private theorem readCompMeta_spec {w : ℕ} (a : CompMetaArgs) {s : Memory.State}
    (h16 : Fits w 16) (hlt1 : a.compMetaBase + 3 * a.idx + 2 < s.frontier)
    (hlt2 : a.liftMetaBase + a.idx < s.frontier) :
    readCompMetaSafe w a s ∧
    Memory.FramedTriple w s (readCompMeta a) 4 ∅ fun res s' =>
      res = ⟨s.mem (a.compMetaBase + 3 * a.idx), s.mem (a.compMetaBase + 3 * a.idx + 1),
        s.mem (a.compMetaBase + 3 * a.idx + 2), s.mem (a.liftMetaBase + a.idx)⟩ ∧
      s' = s := by
  refine ⟨⟨h16, hlt1, hlt2⟩, ?_⟩
  dsimp only [readCompMeta]
  exact Memory.FramedTriple.read_bind (by omega) <|
    Memory.FramedTriple.read_bind (by omega) <|
    Memory.FramedTriple.read_bind (by omega) <|
    Memory.FramedTriple.read_bind (by omega) <|
    Memory.FramedTriple.pure ⟨rfl, rfl⟩

private def evalAndLiftNonEmptyRaw (d : EvalAndLiftArgs) : Memory.Prog ℕ := do
  let tmpOut ← Memory.allocDirty (4 * d.numEdges)
  let fLen ← evalDecisionTreeProg ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, tmpOut⟩
  liftEdgesProg ⟨tmpOut, d.liftBase, d.fcBase, d.fcLen, fLen⟩

private def evalAndLiftNonEmptySafe (w : ℕ) (d : EvalAndLiftArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ Fits w (s.frontier + 4 * d.numEdges) ∧
  let tmpOut := s.frontier
  let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * d.numEdges⟩
  evalDecisionTreeProgSafe w ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, tmpOut⟩ s₁ ∧
  let fLen := (Memory.spec 0).clientResult s₁
    (evalDecisionTreeProg ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, tmpOut⟩)
  let s₂ := (Memory.spec 0).clientState s₁
    (evalDecisionTreeProg ⟨d.tableBase, d.numVerts, d.numEdges, d.edgeBase, tmpOut⟩)
  liftEdgesProgSafe w ⟨tmpOut, d.liftBase, d.fcBase, d.fcLen, fLen⟩ s₂

private theorem realizes_evalAndLiftNonEmptyRaw : Realizes .exact
    evalAndLiftNonEmptyRaw WordEncoding.encode WordEncoding.encode
    evalAndLiftNonEmptySafe (fun _ _ => 0) := by
  unfold evalAndLiftNonEmptyRaw
  realize [realizes_evalDecisionTreeProg, realizes_liftEdgesProg]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2
    | (have h16 := h.1; have hf := h.2.1; have hfront := hmem.frontier_fits; fits)

private def evalAndLiftDTComp (d : EvalAndLiftArgs) : Memory.Prog ℕ :=
  if d.numEdges = 0 then pure d.fcLen else evalAndLiftNonEmptyRaw d

private def evalAndLiftDTCompSafe (w : ℕ) (d : EvalAndLiftArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ (d.numEdges = 0 → Fits w d.fcLen) ∧
  (0 < d.numEdges → evalAndLiftNonEmptySafe w d s)

private theorem realizes_evalAndLiftDTComp : Realizes .exact
    evalAndLiftDTComp WordEncoding.encode WordEncoding.encode
    evalAndLiftDTCompSafe (fun _ _ => 0) := by
  unfold evalAndLiftDTComp
  realize [realizes_evalAndLiftNonEmptyRaw]
  exact h.2.2 (by omega)

private theorem evalAndLiftDTComp_spec {w r0 tableFrontier n : ℕ}
    {r : PartitionRoundWitness n} {tableBase eb lb fcBase fcLen : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hr_le : r.numVerts ≤ r0)
    (hlift_inj : Function.Injective r.lift)
    (hverts : ∀ e ∈ r.compGlobal, e.u ∈ r.verts ∧ e.v ∈ r.verts)
    (hnoiso : 1 ≤ r.compLocal.length → r.numVerts ≤ 2 * r.compLocal.length)
    (hsimp : IsSimple (edgeEnds (r.compLocal.map IndexedEdge.toWeighted)))
    (heb : HoldsIndexedEdges eb r.compLocal s.mem)
    (heb_fr : eb + 4 * r.compLocal.length ≤ s.frontier)
    (hlb : ∀ k : Fin r.numVerts, s.mem (lb + k.val) = (r.lift k).val)
    (hlb_fr : lb + r.numVerts ≤ s.frontier)
    (htab : HoldsDTTable r0 tableBase s.mem)
    (htib : DTTableInBounds r0 tableBase tableFrontier s.mem)
    (htf : tableFrontier ≤ s.frontier)
    (hfc_fr : fcBase + 4 * (fcLen + (r.verts.card - 1)) ≤ s.frontier)
    (hlb_fc : lb + r.numVerts ≤ fcBase)
    (_htf_fc : tableFrontier ≤ fcBase)
    (hfit : Fits w (s.frontier + (5 * r.compLocal.length + r.compLocal.length * r0))) :
    let d : EvalAndLiftArgs := ⟨tableBase, r.numVerts, r.compLocal.length, eb, lb, fcBase, fcLen⟩
    let optD := optDepth (edgeEnds (r.compLocal.map IndexedEdge.toWeighted))
    evalAndLiftDTCompSafe w d s ∧
    Memory.FramedTriple w s (evalAndLiftDTComp d) (25 * r.compLocal.length + 15 * optD + 16)
      (Set.Ico (fcBase + 4 * fcLen) (fcBase + 4 * (fcLen + (r.verts.card - 1))))
      fun fcLen' s' =>
        fcLen ≤ fcLen' ∧
        fcLen' ≤ fcLen + (r.verts.card - 1) ∧
        fcLen' ≤ fcLen + r.compLocal.length ∧
        s.frontier ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + (5 * r.compLocal.length + r.compLocal.length * r0) ∧
        Memory.WellFormed w s' ∧
        (∃ F_i : List (IndexedEdge n),
          F_i.length = fcLen' - fcLen ∧
          F_i.Subperm r.compGlobal ∧
          HoldsIndexedEdges (fcBase + 4 * fcLen) F_i s'.mem ∧
          IsMinSpanningForest (List.map IndexedEdge.toWeighted r.compGlobal)
            (List.map IndexedEdge.toWeighted F_i)) := by
  let d : EvalAndLiftArgs := ⟨tableBase, r.numVerts, r.compLocal.length, eb, lb, fcBase, fcLen⟩
  by_cases hm0 : r.compLocal.length = 0
  · have hloc_nil : r.compLocal = [] := List.eq_nil_of_length_eq_zero hm0
    have hglob_nil : r.compGlobal = [] := by
      simp [PartitionRoundWitness.compGlobal, hloc_nil]
    have hprog : evalAndLiftDTComp d = pure fcLen := by
      simp [evalAndLiftDTComp, d, hm0]
    have hfit_fcl : Fits w fcLen := hfit.of_le (by omega)
    refine ⟨⟨h16, fun _ => hfit_fcl, fun h => by simp [hm0] at h⟩, ?_⟩
    rw [hprog]
    refine Memory.FramedTriple.pure ⟨le_rfl, by omega, by omega, le_rfl, by omega, hwf,
      [], by simp, by simp [hglob_nil], by simp [HoldsIndexedEdges], ?_⟩
    simp only [hglob_nil, List.map_nil]
    exact (isMinSpanningForest_iff_threshold_partition _ _).mpr
      ⟨⟨List.Subperm.refl _, by simp [isAcyclic_nil], rfl⟩, fun _ => rfl⟩
  · have hm_pos : 0 < r.compLocal.length := Nat.pos_of_ne_zero hm0
    have hprog : evalAndLiftDTComp d = evalAndLiftNonEmptyRaw d := by
      simp [evalAndLiftDTComp, d, hm0]
    have hraw_eq : evalAndLiftNonEmptyRaw d =
        (Memory.allocDirty (4 * r.compLocal.length) >>= fun tmpOut =>
          evalDecisionTreeProg ⟨tableBase, r.numVerts, r.compLocal.length, eb, tmpOut⟩ >>=
            fun fLen => liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen⟩) := rfl
    let tmpOut := s.frontier
    let s₁ : Memory.State := ⟨s.mem, s.frontier + 4 * r.compLocal.length⟩
    have hfit_alloc : Fits w (s.frontier + 4 * r.compLocal.length) := hfit.of_le (by omega)
    have hwf₁ : Memory.WellFormed w s₁ := ⟨hfit_alloc, hwf.mem_fits⟩
    have hchoose : r.numVerts.choose 2 ≤ r.compLocal.length * r0 := by
      have hv2m := hnoiso hm_pos
      rw [Nat.choose_two_right]
      calc r.numVerts * (r.numVerts - 1) / 2
          ≤ r.numVerts * r0 / 2 := Nat.div_le_div_right (Nat.mul_le_mul_left _ (by omega))
        _ ≤ (2 * r.compLocal.length) * r0 / 2 :=
            Nat.div_le_div_right (Nat.mul_le_mul_right _ hv2m)
        _ = r.compLocal.length * r0 := by
            rw [Nat.mul_assoc, Nat.mul_div_right _ (by decide)]
    let dq : DTQuery := ⟨tableBase, r.numVerts, r.compLocal.length, eb, tmpOut⟩
    have hdt := evalDecisionTreeProg_spec (w := w) (r0 := r0) (tableFrontier := tableFrontier)
      (d := dq) (C := r.compLocal) (s := s₁) h16 hwf₁ hr_le rfl hsimp heb
      (by dsimp only [s₁, dq]; omega) (by dsimp only [s₁, dq, tmpOut]; omega)
      (Or.inl (by dsimp only [dq, tmpOut]; exact heb_fr)) htab htib
      (htf.trans (by dsimp only [s₁]; omega))
      (fun x hx _ => by dsimp only [dq, tmpOut] at *; omega)
      (hfit.of_le (by dsimp only [s₁, dq]; omega))
    dsimp only at hdt
    have hdt_fr := framedTriple_iff_realization.mp hdt
    set fLen := (Memory.spec 0).clientResult s₁ (evalDecisionTreeProg dq)
    set s₂ := (Memory.spec 0).clientState s₁ (evalDecisionTreeProg dq)
    obtain ⟨hv_dt, hcost_dt, hmod_dt, hsafe_dt, hwf₂, hs2_fr, hflen_le,
      F_loc, hFloc_len, hFloc_sub, hFloc_holds, hFloc_msf⟩ := hdt_fr
    have hfLen_eq : fLen = F_loc.length := hFloc_len.symm
    have hs2_ge : s₁.frontier ≤ s₂.frontier := hmod_dt.1
    have hlb2 : ∀ k : Fin r.numVerts, s₂.mem (lb + k.val) = (r.lift k).val := fun k =>
      (hmod_dt.mem_eq_of_not_mem (by dsimp only [s₁]; omega)
        (by simp only [Set.mem_Ico, not_and, not_lt, dq, tmpOut]; omega)).trans (hlb k)
    let F_i := F_loc.map fun e => (⟨r.lift e.u, r.lift e.v, e.weight, e.id⟩ : IndexedEdge n)
    have hFi_sub : F_i.Subperm r.compGlobal := List.subperm_map _ hFloc_sub
    have hFi_msf : IsMinSpanningForest (List.map IndexedEdge.toWeighted r.compGlobal)
        (List.map IndexedEdge.toWeighted F_i) := by
      have hm_eq : List.map IndexedEdge.toWeighted F_i =
          contractEdgeList r.lift (List.map IndexedEdge.toWeighted F_loc) := by
        simp [F_i, contractEdgeList, List.map_map, Function.comp, contractEdge,
          IndexedEdge.toWeighted]
      rw [hm_eq]
      exact compactVertices_isMinSpanningForest hlift_inj rfl hFloc_msf
    have hFi_card : F_i.length ≤ r.verts.card - 1 := by
      have hsub_mem : ∀ e ∈ List.map IndexedEdge.toWeighted F_i, e.u ∈ r.verts ∧ e.v ∈ r.verts := by
        intro e he
        rw [List.mem_map] at he
        obtain ⟨e', he', rfl⟩ := he
        exact hverts e' (hFi_sub.subset he')
      have hacyc : IsAcyclic (List.map IndexedEdge.toWeighted F_i) := hFi_msf.1.2.1
      simpa using isAcyclic_length_le_finset_sub_one r.verts _ hacyc hsub_mem
    have hFloc_card : F_loc.length ≤ r.verts.card - 1 := by simpa [F_i] using hFi_card
    have hdisj_lift : tmpOut + 4 * F_loc.length ≤ fcBase + 4 * fcLen ∨
        fcBase + 4 * (fcLen + F_loc.length) ≤ tmpOut :=
      Or.inr (by dsimp only [tmpOut]; omega)
    have hlb_lift : lb + r.numVerts ≤ fcBase + 4 * fcLen ∨
        fcBase + 4 * (fcLen + F_loc.length) ≤ lb :=
      Or.inl (by omega)
    have hFloc_end : tmpOut + 4 * F_loc.length ≤ s₂.frontier := by
      dsimp only [tmpOut]; dsimp only [s₁] at hs2_ge; omega
    have hfc_end : fcBase + 4 * (fcLen + F_loc.length) ≤ s₂.frontier := by
      dsimp only [s₁] at hs2_ge; omega
    have hlift := liftEdgesProg_spec (w := w) (nLoc := r.numVerts) (nGlob := n)
      (srcBase := tmpOut) (liftBase := lb) (dstBase := fcBase) (dstOff := fcLen)
      (C := F_loc) (lift := r.lift) (s := s₂) h16 hwf₂ hFloc_holds hFloc_end
      hlb2 (by dsimp only [s₁] at hs2_ge; omega) hfc_end hdisj_lift hlb_lift
    have hlift_fr := framedTriple_iff_realization.mp hlift
    set fcLen' := (Memory.spec 0).clientResult s₂
      (liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, F_loc.length⟩)
    set s₃ := (Memory.spec 0).clientState s₂
      (liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, F_loc.length⟩)
    obtain ⟨hv_l, hcost_l, hmod_l, hfc'_eq, hs3_fr, hwf₃, hholds_l⟩ := hlift_fr
    have hsafe_l : liftEdgesProgSafe w ⟨tmpOut, lb, fcBase, fcLen, F_loc.length⟩ s₂ := by
      refine ⟨h16, hFloc_end, hdisj_lift, fun k hk => ?_, hfc_end⟩
      obtain ⟨hu, hv, _, _⟩ := hFloc_holds k hk
      rw [hu, hv]
      have hu_lt := F_loc[k].u.isLt
      have hv_lt := F_loc[k].v.isLt
      dsimp only [dq] at hu_lt hv_lt
      dsimp only [s₁] at hs2_ge
      dsimp only
      exact ⟨by omega, by omega⟩
    have hsafe_ne : evalAndLiftDTCompSafe w d s := by
      refine ⟨h16, fun h => by dsimp only [d] at h; omega, fun _ => ?_⟩
      refine ⟨h16, hfit_alloc, hsafe_dt, ?_⟩
      change liftEdgesProgSafe w ⟨tmpOut, lb, fcBase, fcLen, fLen⟩ s₂
      rw [hfLen_eq]; exact hsafe_l
    have hres_eq : (Memory.spec 0).clientResult s (evalAndLiftDTComp d) = fcLen' := by
      rw [hprog, hraw_eq, clientResult_bind_allocDirty]
      change (Memory.spec 0).clientResult s₁
        (evalDecisionTreeProg dq >>= fun fLen_1 =>
          liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen_1⟩) = fcLen'
      rw [StateTransitionSpec.clientResult_bind]
      change (Memory.spec 0).clientResult s₂
        (liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen⟩) = fcLen'
      rw [hfLen_eq]
    have hst_eq : (Memory.spec 0).clientState s (evalAndLiftDTComp d) = s₃ := by
      rw [hprog, hraw_eq, clientState_bind_allocDirty]
      change (Memory.spec 0).clientState s₁
        (evalDecisionTreeProg dq >>= fun fLen_1 =>
          liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen_1⟩) = s₃
      rw [StateTransitionSpec.clientState_bind]
      change (Memory.spec 0).clientState s₂
        (liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen⟩) = s₃
      rw [hfLen_eq]
    refine ⟨hsafe_ne, framedTriple_iff_realization.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hprog, hraw_eq]
      refine validHistory_allocDirty_bind hfit_alloc ?_
      change (Memory.spec w).ValidHistory s₁
        ((Memory.spec w).clientHistory s₁
          (evalDecisionTreeProg dq >>= fun fLen_1 =>
            liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen_1⟩))
      refine validHistory_bind_step hv_dt ?_
      change (Memory.spec w).ValidHistory s₂
        ((Memory.spec w).clientHistory s₂
          (liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen⟩))
      rw [hfLen_eq]
      exact hv_l
    · rw [hprog, hraw_eq, memoryCost_bind', memoryCost_allocDirty, clientResult_allocDirty,
        clientState_allocDirty]
      change 1 + memoryCost
        (evalDecisionTreeProg dq >>= fun fLen_1 =>
          liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen_1⟩) s₁ ≤ _
      rw [memoryCost_bind']
      change 1 + (memoryCost (evalDecisionTreeProg dq) s₁ +
        memoryCost (liftEdgesProg ⟨tmpOut, lb, fcBase, fcLen, fLen⟩) s₂) ≤ _
      rw [hfLen_eq]
      have hF_le : F_loc.length ≤ r.compLocal.length := hFloc_sub.length_le
      omega
    · rw [hst_eq]
      refine ⟨by dsimp only [s₁] at hs2_ge; omega, fun x hx hnot => ?_⟩
      have hx2 : x < s₁.frontier := by dsimp only [s₁]; omega
      have hmod2' : s₃.mem x = s₂.mem x := hmod_l.mem_eq_of_not_mem
        (by dsimp only [s₁] at hs2_ge; omega)
        (by
          simp only [Set.mem_Ico, not_and, not_lt] at hnot ⊢
          intro hle; have := hnot hle; omega)
      have hmod1' : s₂.mem x = s₁.mem x := hmod_dt.mem_eq_of_not_mem hx2
        (by simp only [Set.mem_Ico, not_and, not_lt, dq, tmpOut]; omega)
      exact hmod2'.trans hmod1'
    · rw [hres_eq]; omega
    · rw [hres_eq]; omega
    · rw [hres_eq]; have := hFloc_sub.length_le; omega
    · rw [hst_eq, hs3_fr]; dsimp only [s₁] at hs2_ge; omega
    · rw [hst_eq, hs3_fr]; dsimp only [s₁, dq] at hs2_fr; omega
    · rw [hst_eq]; exact hwf₃
    · refine ⟨F_i, ?_, hFi_sub, ?_, hFi_msf⟩
      · rw [hres_eq]; simp [F_i]; omega
      · rw [hst_eq]; simpa [F_i] using hholds_l

/-! ## Partition Decision-Tree Evaluation Loop (`pr02EvalDTLoop`) -/

private def pr02EvalDTLoopStep (p : EvalDTLoopArgs × EvalDTLoopState) :
    Memory.Prog EvalDTLoopState := do
  let env := p.1
  let st := p.2
  let cm ← readCompMeta ⟨env.compMetaBase, env.liftMetaBase, st.idx⟩
  let fcLen' ← evalAndLiftDTComp
    ⟨env.tableBase, cm.numVerts, cm.numEdges, cm.edgeBase, cm.liftBase, env.fcBase, st.fcLen⟩
  pure ⟨st.idx + 1, fcLen'⟩

private def pr02EvalDTLoopStepSafe (w : ℕ) (p : EvalDTLoopArgs × EvalDTLoopState)
    (s : Memory.State) : Prop :=
  let env := p.1
  let st := p.2
  Fits w 16 ∧ Fits w (st.idx + 1) ∧
  readCompMetaSafe w ⟨env.compMetaBase, env.liftMetaBase, st.idx⟩ s ∧
  let cm := (Memory.spec 0).clientResult s
    (readCompMeta ⟨env.compMetaBase, env.liftMetaBase, st.idx⟩)
  let s₁ := (Memory.spec 0).clientState s
    (readCompMeta ⟨env.compMetaBase, env.liftMetaBase, st.idx⟩)
  evalAndLiftDTCompSafe w
    ⟨env.tableBase, cm.numVerts, cm.numEdges, cm.edgeBase, cm.liftBase, env.fcBase, st.fcLen⟩ s₁

private theorem realizes_pr02EvalDTLoopStep : Realizes .exact
    pr02EvalDTLoopStep
    (appendWords (WordEncoding.encode (α := EvalDTLoopArgs))
      (WordEncoding.encode (α := EvalDTLoopState)))
    (WordEncoding.encode (α := EvalDTLoopState))
    pr02EvalDTLoopStepSafe (fun _ _ => 0) := by
  unfold pr02EvalDTLoopStep
  realize [realizes_readCompMeta, realizes_evalAndLiftDTComp]
  all_goals first
    | exact h.2.2.1
    | exact h.2.2.2
    | (have h16 := h.1; have hf := h.2.1; have hfront := hmem.frontier_fits; fits)

/-- Evaluate all `env.numRounds` simple partition components via the precomputed decision-tree
table `env.tableBase`, lift each component MSF through its vertex-lift array, and concatenate the
global MSF edges into `env.fcBase`, returning the total edge count. -/
def pr02EvalDTLoop (env : EvalDTLoopArgs) : Memory.Prog ℕ := do
  let res ← iterate pr02EvalDTLoopStep env env.numRounds ⟨0, 0⟩
  pure res.fcLen

/-- Safety domain for `pr02EvalDTLoop`. -/
def pr02EvalDTLoopSafe (w : ℕ) (env : EvalDTLoopArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  iterationSafe pr02EvalDTLoopStep pr02EvalDTLoopStepSafe w env env.numRounds ⟨0, 0⟩ s

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `pr02EvalDTLoop`. -/
theorem realizes_pr02EvalDTLoop : Realizes .exact
    pr02EvalDTLoop WordEncoding.encode WordEncoding.encode
    pr02EvalDTLoopSafe (fun _ _ => 0) := by
  unfold pr02EvalDTLoop
  realize [realizes_pr02EvalDTLoopStep]
  exact iterationSafe_imp h.2 (fun _ => rfl) (fun _ _ hs => hs)

/-- Framed specification for `pr02EvalDTLoop`: evaluates all partition components via
`evalDecisionTreeProg` and lifts their MSFs into `fcBase`, modifying only
`Set.Ico fcBase (fcBase + 4 * n)`, in at most `25 * m' + 15 * optDepthMN m' n + 20 * n` memory
operations. -/
theorem pr02EvalDTLoop_spec {w r0 tableFrontier n m' : ℕ}
    {rounds : List (PartitionRoundWitness n)} {H_rem : List (IndexedEdge n)}
    {es' : List (IndexedEdge n)}
    {tableBase compMetaBase liftMetaBase fcBase : ℕ} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hsimp_es' : IsSimple (edgeEnds (es'.map IndexedEdge.toWeighted)))
    (hperm : ((rounds.flatMap PartitionRoundWitness.compGlobal) ++ H_rem ++
      (rounds.flatMap PartitionRoundWitness.corrEdges)).Perm es')
    (hes'_len : es'.length ≤ m')
    (hrounds_le : rounds.length ≤ n)
    (htab : HoldsDTTable r0 tableBase s.mem)
    (htib : DTTableInBounds r0 tableBase tableFrontier s.mem)
    (htf_fc : tableFrontier ≤ fcBase)
    (hmeta_fc : compMetaBase + 3 * rounds.length ≤ fcBase)
    (hlift_fc : liftMetaBase + rounds.length ≤ fcBase)
    (hfc_s : fcBase + 4 * n ≤ s.frontier)
    (hrounds_meta : PartitionRoundMeta r0 compMetaBase liftMetaBase rounds s.mem)
    (hrounds_fc : ∀ i : Fin rounds.length,
      let r := rounds[i.val]'i.isLt
      s.mem (compMetaBase + 3 * i.val + 2) + 4 * r.compLocal.length ≤ fcBase ∧
      s.mem (liftMetaBase + i.val) + r.numVerts ≤ fcBase)
    (hfit : Fits w (s.frontier + 5 * m' + m' * r0)) :
    let env : EvalDTLoopArgs := ⟨rounds.length, tableBase, compMetaBase, liftMetaBase, fcBase⟩
    pr02EvalDTLoopSafe w env s ∧
    Memory.FramedTriple w s (pr02EvalDTLoop env)
      (25 * m' + 15 * optDepthMN m' n + 20 * n) (Set.Ico fcBase (fcBase + 4 * n))
      fun fcLen s' =>
        fcLen ≤ n ∧
        s.frontier ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + 5 * m' + m' * r0 ∧
        Memory.WellFormed w s' ∧
        ∃ F_comps : List (List (IndexedEdge n)),
          ∃ (hF_len : F_comps.length = rounds.length),
            F_comps.flatten.length = fcLen ∧
            HoldsIndexedEdges fcBase F_comps.flatten s'.mem ∧
            ∀ i : Fin rounds.length,
              (F_comps[i.val]'(by omega)).Subperm rounds[i.val].compGlobal ∧
              IsMinSpanningForest
                (rounds[i.val].compGlobal.map IndexedEdge.toWeighted)
                ((F_comps[i.val]'(by omega)).map IndexedEdge.toWeighted) := by
  have hinter : ∀ i : Fin rounds.length,
      (rounds[i.val].verts ∩ (Finset.univ.filter fun j : Fin rounds.length =>
        j.val < i.val).biUnion (fun j => rounds[j.val].verts)).card ≤ 1 :=
    hrounds_meta.inter_prev_card_le_one
  have hsum_edges_le : (rounds.map fun r => r.compLocal.length).sum ≤ m' := by
    have hmap_len : ∀ L : List (PartitionRoundWitness n),
        (L.map fun r => r.compLocal.length).sum =
          (L.flatMap PartitionRoundWitness.compGlobal).length := fun L => by
      induction L with
      | nil => simp
      | cons r rs ih =>
        simp only [List.map_cons, List.sum_cons, List.flatMap_cons, List.length_append, ih,
          PartitionRoundWitness.compGlobal, List.length_map]
    have hperm_len := hperm.length_eq
    simp only [List.length_append] at hperm_len
    have := hmap_len rounds
    omega
  have hmul_edges_le : (rounds.map fun r => r.compLocal.length).sum * r0 ≤ m' * r0 :=
    Nat.mul_le_mul_right r0 hsum_edges_le
  have hfit_tot : Fits w (s.frontier + 5 * (rounds.map fun r => r.compLocal.length).sum +
      (rounds.map fun r => r.compLocal.length).sum * r0) :=
    hfit.of_le (by omega)
  have hopt_sum : (rounds.map fun r =>
        optDepth (edgeEnds (r.compLocal.map IndexedEdge.toWeighted))).sum ≤
      optDepthMN m' n := by
    have hsub_es' : (rounds.flatMap PartitionRoundWitness.compGlobal).Subperm es' :=
      (List.sublist_append_left _ _).subperm.trans
        ((List.sublist_append_left _ _).subperm.trans hperm.subperm)
    have hopt1 := partition_optDepth_sum_le hsimp_es' hsub_es' fun i =>
      ⟨hrounds_meta.lift_injective i, hrounds_meta.compGlobal_verts i,
       hrounds_meta.inter_prev_card_le_one i⟩
    exact hopt1.trans (optDepthMN_mono_m hes'_len)
  let env : EvalDTLoopArgs := ⟨rounds.length, tableBase, compMetaBase, liftMetaBase, fcBase⟩
  let S : Set ℕ := Set.Ico fcBase (fcBase + 4 * n)
  let inv (k : ℕ) (st : EvalDTLoopState) (t : Memory.State) : Prop :=
    st.idx = k ∧
    ∃ (hk_le : k ≤ rounds.length),
    st.fcLen ≤ ((rounds.take k).map fun r => r.verts.card - 1).sum ∧
    s.frontier ≤ t.frontier ∧
    t.frontier ≤ s.frontier + 5 * ((rounds.take k).map fun r => r.compLocal.length).sum +
      ((rounds.take k).map fun r => r.compLocal.length).sum * r0 ∧
    Memory.WellFormed w t ∧
    (∀ a < fcBase, t.mem a = s.mem a) ∧
    ∃ F_comps : List (List (IndexedEdge n)),
      ∃ (hF_len : F_comps.length = k),
        F_comps.flatten.length = st.fcLen ∧
        HoldsIndexedEdges fcBase F_comps.flatten t.mem ∧
        ∀ i (hi : i < k),
          (F_comps[i]'(by omega)).Subperm (rounds[i]'(by omega)).compGlobal ∧
          IsMinSpanningForest
            ((rounds[i]'(by omega)).compGlobal.map IndexedEdge.toWeighted)
            ((F_comps[i]'(by omega)).map IndexedEdge.toWeighted)
  let pot (k : ℕ) (_ : EvalDTLoopState) (_ : Memory.State) : ℕ :=
    25 * ((rounds.drop k).map fun r => r.compLocal.length).sum +
      15 * ((rounds.drop k).map fun r =>
        optDepth (edgeEnds (r.compLocal.map IndexedEdge.toWeighted))).sum
  have hstep : ∀ k < rounds.length, ∀ st t, inv k st t →
      pr02EvalDTLoopStepSafe w (env, st) t ∧
      (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (pr02EvalDTLoopStep (env, st))) ∧
      let st' := (Memory.spec 0).clientResult t (pr02EvalDTLoopStep (env, st))
      let t' := (Memory.spec 0).clientState t (pr02EvalDTLoopStep (env, st))
      memoryCost (pr02EvalDTLoopStep (env, st)) t + pot (k + 1) st' t' ≤ pot k st t + 20 ∧
      Memory.Modifies S t t' ∧
      inv (k + 1) st' t' := by
    intro k hk st t ⟨hidx, _, hfc_le, hs_t, ht_fr, htwf, hframe, F_comps, hF_len, hF_flat,
      hF_holds, hF_msf⟩
    rcases st with ⟨idx, fcLen⟩
    dsimp only at hidx hfc_le hF_flat ⊢
    subst idx
    let r := rounds[k]'hk
    let eb := s.mem (compMetaBase + 3 * k + 2)
    let lb := s.mem (liftMetaBase + k)
    have hv_eq : s.mem (compMetaBase + 3 * k) = r.numVerts := hrounds_meta.numVerts_eq ⟨k, hk⟩
    have hm_eq : s.mem (compMetaBase + 3 * k + 1) = r.compLocal.length :=
      hrounds_meta.numEdges_eq ⟨k, hk⟩
    obtain ⟨heb_fc, hlb_fc⟩ := hrounds_fc ⟨k, hk⟩
    change eb + 4 * r.compLocal.length ≤ fcBase at heb_fc
    change lb + r.numVerts ≤ fcBase at hlb_fc
    have heb_s0 : HoldsIndexedEdges eb r.compLocal s.mem := hrounds_meta.holdsEdges ⟨k, hk⟩
    have hlb_s0 : ∀ j : Fin r.numVerts, s.mem (lb + j.val) = (r.lift j).val :=
      hrounds_meta.lift_eq ⟨k, hk⟩
    have hr_le : r.numVerts ≤ r0 := hrounds_meta.numVerts_le ⟨k, hk⟩
    have hnoiso : 1 ≤ r.compLocal.length → r.numVerts ≤ 2 * r.compLocal.length :=
      hrounds_meta.numVerts_le_two_mul ⟨k, hk⟩
    have hlift_inj : Function.Injective r.lift := hrounds_meta.lift_injective ⟨k, hk⟩
    have hsimp_r : IsSimple (edgeEnds (r.compLocal.map IndexedEdge.toWeighted)) :=
      hrounds_meta.isSimple ⟨k, hk⟩
    have hverts_r : ∀ e ∈ r.compGlobal, e.u ∈ r.verts ∧ e.v ∈ r.verts :=
      hrounds_meta.compGlobal_verts ⟨k, hk⟩
    have htab_t : HoldsDTTable r0 tableBase t.mem :=
      htab.congr htib (fun a ha => hframe a (ha.trans_le htf_fc))
    have htib_t : DTTableInBounds r0 tableBase tableFrontier t.mem :=
      htib.mono le_rfl (fun a ha => hframe a (ha.trans_le htf_fc))
    have heb_t : HoldsIndexedEdges eb r.compLocal t.mem :=
      heb_s0.congr (fun a _ ha => hframe a (by omega))
    have hlb_t : ∀ j : Fin r.numVerts, t.mem (lb + j.val) = (r.lift j).val := fun j =>
      (hframe (lb + j.val) (by omega)).trans (hlb_s0 j)
    have htake_succ : rounds.take (k + 1) = rounds.take k ++ [r] :=
      List.take_succ_eq_append_getElem hk
    have hsum_take1 : ((rounds.take (k + 1)).map fun x => x.verts.card - 1).sum ≤ n :=
      sum_verts_sub_one_take_le rounds hinter (k + 1)
    have hsum_take1_eq : ((rounds.take (k + 1)).map fun x => x.verts.card - 1).sum =
        ((rounds.take k).map fun x => x.verts.card - 1).sum + (r.verts.card - 1) := by
      rw [htake_succ, List.map_append, List.sum_append]; simp [r]
    have hsum_edges1 : ((rounds.take (k + 1)).map fun x => x.compLocal.length).sum ≤
        (rounds.map fun x => x.compLocal.length).sum :=
      List.Sublist.sum_le_sum ((List.take_sublist (k + 1) rounds).map _) (fun _ _ => Nat.zero_le _)
    have hsum_edges1_eq : ((rounds.take (k + 1)).map fun x => x.compLocal.length).sum =
        ((rounds.take k).map fun x => x.compLocal.length).sum + r.compLocal.length := by
      rw [htake_succ, List.map_append, List.sum_append]; simp [r]
    have h5_add : 5 * ((rounds.take k).map fun x => x.compLocal.length).sum +
        5 * r.compLocal.length =
        5 * ((rounds.take (k + 1)).map fun x => x.compLocal.length).sum := by
      rw [hsum_edges1_eq, Nat.mul_add]
    have hrc := readCompMeta_spec (w := w) ⟨compMetaBase, liftMetaBase, k⟩ (s := t) h16
      (by dsimp only; omega) (by dsimp only; omega)
    obtain ⟨hsafe_rc, hrc_ft⟩ := hrc
    obtain ⟨hv_rc, hcost_rc, _, hres_rc, hst_rc⟩ := framedTriple_iff_realization.mp hrc_ft
    have hres_rc' : (Memory.spec 0).clientResult t
        (readCompMeta ⟨compMetaBase, liftMetaBase, k⟩) =
        ⟨r.numVerts, r.compLocal.length, eb, lb⟩ := by
      rw [hres_rc]
      rw [(hframe (compMetaBase + 3 * k) (by omega)).trans hv_eq,
        (hframe (compMetaBase + 3 * k + 1) (by omega)).trans hm_eq,
        hframe (compMetaBase + 3 * k + 2) (by omega), hframe (liftMetaBase + k) (by omega)]
    have hmul_edges1 : ((rounds.take (k + 1)).map fun x => x.compLocal.length).sum * r0 ≤
        (rounds.map fun x => x.compLocal.length).sum * r0 :=
      Nat.mul_le_mul_right r0 hsum_edges1
    have hmul_take_add : ((rounds.take k).map fun x => x.compLocal.length).sum * r0 +
        r.compLocal.length * r0 =
        ((rounds.take (k + 1)).map fun x => x.compLocal.length).sum * r0 := by
      rw [hsum_edges1_eq, Nat.add_mul]
    have hfit_eval : Fits w (t.frontier + (5 * r.compLocal.length + r.compLocal.length * r0)) :=
      hfit_tot.of_le (by linarith [ht_fr, h5_add, hsum_edges1, hmul_take_add, hmul_edges1])
    have hev := evalAndLiftDTComp_spec (w := w) (r0 := r0) (tableFrontier := tableFrontier)
      (n := n) (r := r) (tableBase := tableBase) (eb := eb) (lb := lb) (fcBase := fcBase)
      (fcLen := fcLen) h16 htwf hr_le hlift_inj hverts_r hnoiso hsimp_r heb_t
      (by omega) hlb_t (by omega) htab_t htib_t (by omega) (by omega) (by omega) htf_fc hfit_eval
    obtain ⟨hsafe_ev, hev_ft⟩ := hev
    obtain ⟨hv_ev, hcost_ev, hmod_ev, hfcl_le, hfcl_ub, _, hs'_ge, hs'_fr, hwf',
      F_k, hFk_len, hFk_sub, hFk_holds, hFk_msf⟩ := framedTriple_iff_realization.mp hev_ft
    set fcLen' := (Memory.spec 0).clientResult t (evalAndLiftDTComp
      ⟨tableBase, r.numVerts, r.compLocal.length, eb, lb, fcBase, fcLen⟩)
    set t' := (Memory.spec 0).clientState t (evalAndLiftDTComp
      ⟨tableBase, r.numVerts, r.compLocal.length, eb, lb, fcBase, fcLen⟩)
    have hstep_eq : pr02EvalDTLoopStep (env, ⟨k, fcLen⟩) =
        (readCompMeta ⟨compMetaBase, liftMetaBase, k⟩ >>= fun cm =>
          evalAndLiftDTComp
            ⟨tableBase, cm.numVerts, cm.numEdges, cm.edgeBase, cm.liftBase, fcBase, fcLen⟩ >>=
            fun x => pure ⟨k + 1, x⟩) := rfl
    have hfit_k1 : Fits w (k + 1) := hfit_tot.of_le (by omega)
    have hsafe_step : pr02EvalDTLoopStepSafe w (env, ⟨k, fcLen⟩) t := by
      refine ⟨h16, hfit_k1, hsafe_rc, ?_⟩
      dsimp only [env]
      rw [hres_rc', hst_rc]
      exact hsafe_ev
    have hv_step : (Memory.spec w).ValidHistory t
        ((Memory.spec w).clientHistory t (pr02EvalDTLoopStep (env, ⟨k, fcLen⟩))) := by
      rw [hstep_eq]
      refine validHistory_bind_step hv_rc ?_
      rw [hres_rc', hst_rc]
      exact validHistory_bind_step hv_ev (validHistory_pure w _ _)
    have hres_step : (Memory.spec 0).clientResult t (pr02EvalDTLoopStep (env, ⟨k, fcLen⟩)) =
        ⟨k + 1, fcLen'⟩ := by
      rw [hstep_eq, StateTransitionSpec.clientResult_bind, hres_rc', hst_rc,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    have hst_step : (Memory.spec 0).clientState t (pr02EvalDTLoopStep (env, ⟨k, fcLen⟩)) =
        t' := by
      rw [hstep_eq, StateTransitionSpec.clientState_bind, hres_rc', hst_rc,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    have hdrop_eq : rounds.drop k = r :: rounds.drop (k + 1) := List.drop_eq_getElem_cons hk
    have hpot_step : memoryCost (pr02EvalDTLoopStep (env, ⟨k, fcLen⟩)) t +
        pot (k + 1) ⟨k + 1, fcLen'⟩ t' ≤ pot k ⟨k, fcLen⟩ t + 20 := by
      rw [hstep_eq, memoryCost_bind', hres_rc', hst_rc, memoryCost_bind',
        memoryCost_pure, add_zero]
      dsimp only [pot]
      rw [hdrop_eq, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      omega
    have hmod_step : Memory.Modifies S t t' :=
      hmod_ev.mono fun a ha => by
        simp only [Set.mem_Ico] at ha ⊢
        exact ⟨by omega, by omega⟩
    have hframe' : ∀ a < fcBase, t'.mem a = s.mem a := fun a ha =>
      (hmod_step.mem_eq_of_not_mem (by omega)
        (by simp only [S, Set.mem_Ico, not_and, not_lt]; omega)).trans (hframe a ha)
    have hF_holds_t' : HoldsIndexedEdges fcBase F_comps.flatten t'.mem :=
      hF_holds.congr fun a ha ha2 => by
        rw [hF_flat] at ha2
        exact hmod_ev.mem_eq_of_not_mem (by omega)
          (by simp only [Set.mem_Ico, not_and, not_lt]; omega)
    have hF_holds' : HoldsIndexedEdges fcBase (F_comps ++ [F_k]).flatten t'.mem := by
      rw [List.flatten_concat]
      rw [← hF_flat] at hFk_holds
      exact holdsIndexedEdges_append hF_holds_t' hFk_holds
    have hF_flat' : (F_comps ++ [F_k]).flatten.length = fcLen' := by
      rw [List.flatten_concat, List.length_append, hF_flat, hFk_len]; omega
    have hF_msf' : ∀ i (hi : i < k + 1),
        ((F_comps ++ [F_k])[i]'(by simp [hF_len]; omega)).Subperm
          (rounds[i]'(by omega)).compGlobal ∧
        IsMinSpanningForest
          ((rounds[i]'(by omega)).compGlobal.map IndexedEdge.toWeighted)
          (((F_comps ++ [F_k])[i]'(by simp [hF_len]; omega)).map IndexedEdge.toWeighted) := by
      intro i hi
      by_cases hik : i = k
      · subst i
        have hget : (F_comps ++ [F_k])[k]'(by simp [hF_len]) = F_k := by
          rw [List.getElem_append_right (by omega)]; simp [hF_len]
        rw [hget]
        exact ⟨hFk_sub, hFk_msf⟩
      · have hik' : i < k := by omega
        rw [List.getElem_append_left (by omega)]
        exact hF_msf i hik'
    refine ⟨hsafe_step, hv_step, ?_, hst_step ▸ hmod_step, ?_⟩
    · rw [hres_step, hst_step]; exact hpot_step
    · rw [hres_step, hst_step]
      exact ⟨rfl, by omega,
        by change fcLen' ≤ fcLen + (r.verts.card - 1) at hfcl_ub
           linarith [hfcl_ub, hfc_le, hsum_take1_eq],
        hs_t.trans hs'_ge,
        by linarith [hs'_fr, ht_fr, h5_add, hmul_take_add], hwf', hframe',
        F_comps ++ [F_k], by simp [hF_len], hF_flat', hF_holds', hF_msf'⟩
  have hinv0 : inv 0 ⟨0, 0⟩ s :=
    ⟨rfl, Nat.zero_le _, by simp, le_rfl, by simp, hwf, fun _ _ => rfl, [], rfl, rfl,
      by simp [HoldsIndexedEdges], fun _ hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨hsafe_it, hv_it, hcost_it, hmod_it, ⟨_, _, hfc_le, hs_s', hs'_fr, hwf', _,
      F_comps, hF_len, hF_flat, hF_holds, hF_msf⟩⟩ :=
    iterate_potential_spec pr02EvalDTLoopStep pr02EvalDTLoopStepSafe w env 20 rounds.length
      inv pot S hstep ⟨0, 0⟩ s hinv0
  have hsum_le : ((rounds.take rounds.length).map fun r => r.verts.card - 1).sum ≤ n :=
    sum_verts_sub_one_take_le rounds hinter rounds.length
  have htake_all : rounds.take rounds.length = rounds := List.take_length
  rw [htake_all] at hsum_le hfc_le hs'_fr
  have hprog : pr02EvalDTLoop env =
      (iterate pr02EvalDTLoopStep env rounds.length ⟨0, 0⟩ >>= fun res => pure res.fcLen) := rfl
  refine ⟨⟨h16, hsafe_it⟩, framedTriple_iff_realization.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hprog]; exact validHistory_bind_step hv_it (validHistory_pure w _ _)
  · rw [hprog, memoryCost_bind', memoryCost_pure, add_zero]
    dsimp only [pot] at hcost_it
    simp only [List.drop_zero, List.drop_length, List.map_nil, List.sum_nil, mul_zero,
      add_zero] at hcost_it
    linarith [hcost_it, hopt_sum, hsum_edges_le, hrounds_le]
  · rw [hprog, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    exact hmod_it
  · rw [hprog, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
    exact hfc_le.trans hsum_le
  · rw [hprog, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    exact hs_s'
  · rw [hprog, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    linarith [hs'_fr, hsum_edges_le, hmul_edges_le]
  · rw [hprog, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
    exact hwf'
  · refine ⟨F_comps, hF_len, ?_, ?_, fun i => hF_msf i.val i.isLt⟩
    · rw [hprog, StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_pure]
      exact hF_flat
    · rw [hprog, StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_pure]
      exact hF_holds

/-! ## Remainder-Graph Contraction and MSF Solver (`pr02SolveHRemProg`) -/

private def pr02SolveHRemPrep (d : SolveHRemArgs) : Memory.Prog CompactResult := do
  let retagBase ← retagIndexedProg ⟨d.hRemBase, d.hRemLen⟩
  let conglomEdgeBase ← contractEdgesProg ⟨d.hRemLen, retagBase, d.conglomBase⟩
  compactVerticesProg ⟨d.numConglom, d.hRemLen, conglomEdgeBase⟩

private def pr02SolveHRemPrepSafe (w : ℕ) (d : SolveHRemArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  retagIndexedProgSafe w ⟨d.hRemBase, d.hRemLen⟩ s ∧
  let rb := (Memory.spec 0).clientResult s (retagIndexedProg ⟨d.hRemBase, d.hRemLen⟩)
  let s₁ := (Memory.spec 0).clientState s (retagIndexedProg ⟨d.hRemBase, d.hRemLen⟩)
  Fits w (s₁.frontier + 4 * d.hRemLen) ∧
  (∀ j < d.hRemLen, rb + 4 * j + 3 < s₁.frontier ∧
    d.conglomBase + s₁.mem (rb + 4 * j) < s₁.frontier ∧
    d.conglomBase + s₁.mem (rb + 4 * j + 1) < s₁.frontier) ∧
  let ceb := (Memory.spec 0).clientResult s₁
    (contractEdgesProg ⟨d.hRemLen, rb, d.conglomBase⟩)
  let s₂ := (Memory.spec 0).clientState s₁
    (contractEdgesProg ⟨d.hRemLen, rb, d.conglomBase⟩)
  ceb + 4 * d.hRemLen ≤ s₂.frontier ∧
  Fits w (s₂.frontier + (d.numConglom + 4 * d.hRemLen + 1)) ∧
  ∀ j < d.hRemLen,
    s₂.mem (ceb + 4 * j) < d.numConglom ∧ s₂.mem (ceb + 4 * j + 1) < d.numConglom

private theorem realizes_pr02SolveHRemPrep : Realizes .exact
    pr02SolveHRemPrep WordEncoding.encode WordEncoding.encode
    pr02SolveHRemPrepSafe (fun _ _ => 0) := by
  unfold pr02SolveHRemPrep
  realize [realizes_retagIndexedProg, realizes_contractEdgesProg, realizes_compactVerticesProg]
  all_goals
    dsimp only [pr02SolveHRemPrepSafe] at h
    rcases h with ⟨h16, hr, hfit1, hb1, hceb, hfit2, hb2⟩
    first
    | exact h16
    | exact hr
    | exact hfit1
    | exact hb1
    | exact hceb
    | exact hfit2
    | exact hb2

private def pr02SolveHRemNonEmpty (d : SolveHRemArgs) : Memory.Prog SolveHRemResult := do
  let compRes ← pr02SolveHRemPrep d
  let denseRes ← denseCaseProg ⟨compRes.numVertices, d.hRemLen, compRes.edgeBase⟩
  let liftBase ← liftHRemProg ⟨d.hRemBase, denseRes.edgeBase, denseRes.numEdges⟩
  pure ⟨liftBase, denseRes.numEdges⟩

private def pr02SolveHRemNonEmptySafe (w : ℕ) (d : SolveHRemArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧
  pr02SolveHRemPrepSafe w d s ∧
  let cr := (Memory.spec 0).clientResult s (pr02SolveHRemPrep d)
  let s₁ := (Memory.spec 0).clientState s (pr02SolveHRemPrep d)
  Fits w 16 ∧ cr.edgeBase + 4 * d.hRemLen ≤ s₁.frontier ∧
  Fits w (s₁.frontier + (21 * d.hRemLen + 8 * cr.numVertices +
    76 * d.hRemLen * Nat.iterClogBeta ((2 * d.hRemLen) / cr.numVertices) cr.numVertices + 3)) ∧
  (∀ j < d.hRemLen,
    s₁.mem (cr.edgeBase + 4 * j) < cr.numVertices ∧
    s₁.mem (cr.edgeBase + 4 * j + 1) < cr.numVertices) ∧
  let dr := (Memory.spec 0).clientResult s₁
    (denseCaseProg ⟨cr.numVertices, d.hRemLen, cr.edgeBase⟩)
  let s₂ := (Memory.spec 0).clientState s₁
    (denseCaseProg ⟨cr.numVertices, d.hRemLen, cr.edgeBase⟩)
  liftHRemProgSafe w ⟨d.hRemBase, dr.edgeBase, dr.numEdges⟩ s₂

private theorem realizes_pr02SolveHRemNonEmpty : Realizes .exact
    pr02SolveHRemNonEmpty WordEncoding.encode WordEncoding.encode
    pr02SolveHRemNonEmptySafe (fun _ _ => 0) := by
  unfold pr02SolveHRemNonEmpty
  realize [realizes_pr02SolveHRemPrep, realizes_denseCaseProg, realizes_liftHRemProg]
  all_goals
    dsimp only [pr02SolveHRemNonEmptySafe] at h
    rcases h with ⟨h16, hprep, h16d, hcr_eb, hfitd, hed_d, hlift⟩
    first
    | exact h16
    | exact hprep
    | exact hcr_eb
    | exact hfitd
    | exact hed_d
    | exact hlift

/-- Contract remaining uncorrupted edges `H_rem` along the conglomerate map `conglomBase`, solve
the resulting dense contracted graph with `denseCaseProg`, and lift the selected original `H_rem`
edges into a freshly allocated stride-4 edge array returned as a `SolveHRemResult`. -/
def pr02SolveHRemProg (a : SolveHRemArgs) : Memory.Prog SolveHRemResult :=
  if a.hRemLen = 0 then pure ⟨a.hRemBase, 0⟩ else pr02SolveHRemNonEmpty a

/-- Safety domain for `pr02SolveHRemProg`. -/
def pr02SolveHRemProgSafe (w : ℕ) (a : SolveHRemArgs) (s : Memory.State) : Prop :=
  Fits w 16 ∧ (a.hRemLen = 0 → Fits w a.hRemBase) ∧
  (0 < a.hRemLen → pr02SolveHRemNonEmptySafe w a s)

/-- Uniform `Realizes .exact` certificate (`work = 0`) for `pr02SolveHRemProg`. -/
theorem realizes_pr02SolveHRemProg : Realizes .exact
    pr02SolveHRemProg WordEncoding.encode WordEncoding.encode
    pr02SolveHRemProgSafe (fun _ _ => 0) := by
  unfold pr02SolveHRemProg
  realize [realizes_pr02SolveHRemNonEmpty]
  exact h.2.2 (by omega)

/-- Framed specification for `pr02SolveHRemProg`: contracts `H_rem` onto conglomerate vertices,
computes a contracted MSF via `denseCaseProg`, and emits the lifted `H_lift ⊆ H_rem` into a fresh
stride-4 edge array (`SolveHRemResult`) in at most `3659 * H_rem.length + 17801 * n' + 16` memory
operations while preserving all cells below `s.frontier` (`Modifies ∅`). -/
theorem pr02SolveHRemProg_spec {w n' nConglom n₀ r0 hRemBase conglomBase : ℕ}
    {rounds : List (PartitionRoundWitness n')} {H_rem : List (IndexedEdge n')}
    {conglomFn : Fin n' → Fin nConglom} {s : Memory.State}
    (h16 : Fits w 16) (hwf : Memory.WellFormed w s)
    (hn'_le : n' ≤ n₀) (hnConglom_le : nConglom ≤ n')
    (hr0_log : max 1 (Nat.iterLog 3 n₀) ≤ r0)
    (hrem_holds : HoldsIndexedEdges hRemBase H_rem s.mem)
    (hrem_lt : hRemBase + 4 * H_rem.length ≤ s.frontier)
    (hconglom_mem : ∀ u : Fin n', s.mem (conglomBase + u.val) = (conglomFn u).val)
    (hconglom_lt : conglomBase + n' ≤ s.frontier)
    (hcov : ∀ x : Fin n', ∃ r ∈ rounds, x ∈ r.verts)
    (hconglom_rel : ∀ x y : Fin n', conglomFn x = conglomFn y ↔
      (edgePartition (rounds.flatMap fun r => r.tree.treeEdges)).rel x y = true)
    (hstop : ∀ i : Fin rounds.length,
      r0 ≤ (rounds[i.val]'i.isLt).verts.card ∨
      (∃ j : Fin rounds.length, j.val < i.val ∧
        ((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∨
      ((∀ j : Fin rounds.length, j ≠ i →
        ¬((rounds[i.val]'i.isLt).verts ∩ (rounds[j.val]'j.isLt).verts).Nonempty) ∧
        ∀ e ∈ H_rem, e.u ∉ (rounds[i.val]'i.isLt).verts ∧
          e.v ∉ (rounds[i.val]'i.isLt).verts))
    (hfit : Fits w (s.frontier + 341 * H_rem.length + 1529 * n' + 3)) :
    let d : SolveHRemArgs := ⟨nConglom, hRemBase, H_rem.length, conglomBase⟩
    pr02SolveHRemProgSafe w d s ∧
    Memory.FramedTriple w s (pr02SolveHRemProg d)
      (3659 * H_rem.length + 17801 * n' + 16) ∅ fun res s' =>
        res.edgeBase + 4 * res.numEdges ≤ s'.frontier ∧
        res.numEdges * r0 ≤ n' ∧
        res.numEdges ≤ H_rem.length ∧
        s.frontier ≤ s'.frontier ∧
        s'.frontier ≤ s.frontier + 341 * H_rem.length + 1529 * n' + 3 ∧
        Memory.WellFormed w s' ∧
        ∃ H_lift : List (IndexedEdge n'),
          H_lift.length = res.numEdges ∧
          HoldsIndexedEdges res.edgeBase H_lift s'.mem ∧
          H_lift.Subperm H_rem ∧
          IsMinSpanningForest
            (contractEdgeList conglomFn (H_rem.map IndexedEdge.toWeighted))
            (contractEdgeList conglomFn (H_lift.map IndexedEdge.toWeighted)) := by
  let d : SolveHRemArgs := ⟨nConglom, hRemBase, H_rem.length, conglomBase⟩
  by_cases hm0 : H_rem.length = 0
  · have hnil : H_rem = [] := List.eq_nil_of_length_eq_zero hm0
    subst hnil
    have hprog : pr02SolveHRemProg d = pure ⟨hRemBase, 0⟩ := by
      simp [pr02SolveHRemProg, d]
    have hfit_hb : Fits w hRemBase := hfit.of_le (by omega)
    refine ⟨⟨h16, fun _ => hfit_hb, fun h => by simp at h⟩, ?_⟩
    rw [hprog]
    refine Memory.FramedTriple.pure ⟨by simpa using hrem_lt, by simp, Nat.zero_le _, le_rfl,
      by omega, hwf, [], rfl, fun _ hi => by simp at hi, List.Subperm.refl _, ?_⟩
    simp only [contractEdgeList, List.map_nil]
    exact (isMinSpanningForest_iff_threshold_partition _ _).mpr
      ⟨⟨List.Subperm.refl _, by simp [isAcyclic_nil], rfl⟩, fun _ => rfl⟩
  · have hm_pos : 0 < H_rem.length := Nat.pos_of_ne_zero hm0
    have hprog_ne : pr02SolveHRemProg d = pr02SolveHRemNonEmpty d := by
      simp [pr02SolveHRemProg, d, hm0]
    have h1 := retagIndexedProg_spec (w := w) (n := n') (srcBase := hRemBase) (es := H_rem)
      (s := s) h16 hwf hrem_holds hrem_lt (hfit.of_le (by omega))
    have h1_fr := framedTriple_iff_realization.mp h1
    set rb := (Memory.spec 0).clientResult s (retagIndexedProg ⟨hRemBase, H_rem.length⟩)
    set s₁ := (Memory.spec 0).clientState s (retagIndexedProg ⟨hRemBase, H_rem.length⟩)
    obtain ⟨hv1, hcost1, hmod1, hrb_eq, hs1_fr, hwf1, hholds1⟩ := h1_fr
    let H_retag := H_rem.mapIdx fun i e => (⟨e.u, e.v, e.weight, i⟩ : IndexedEdge n')
    have hretag_len : H_retag.length = H_rem.length := by simp [H_retag]
    have hcon_s1 : ∀ u : Fin n', s₁.mem (conglomBase + u.val) = (conglomFn u).val := fun u =>
      (hmod1.mem_eq_of_not_mem (by omega) (Set.notMem_empty _)).trans (hconglom_mem u)
    have h2 := contractEdgesProg_spec (w := w) (n := n') (n' := nConglom) (edgeBase := rb)
      (compBase := conglomBase) (es := H_retag) (compFn := fun u => (conglomFn u).val)
      (s := s₁) h16 hwf1 hholds1 (by rw [hrb_eq, hs1_fr, hretag_len]) hcon_s1
      (by rw [hs1_fr]; omega) (fun e _ => ⟨(conglomFn e.u).isLt, (conglomFn e.v).isLt⟩)
      (hfit.of_le (by rw [hs1_fr, hretag_len]; omega))
    simp only [H_retag, List.length_mapIdx] at h2
    have h2_fr := framedTriple_iff_realization.mp h2
    set ceb := (Memory.spec 0).clientResult s₁
      (contractEdgesProg ⟨H_rem.length, rb, conglomBase⟩)
    set s₂ := (Memory.spec 0).clientState s₁
      (contractEdgesProg ⟨H_rem.length, rb, conglomBase⟩)
    obtain ⟨hv2, hcost2, hmod2, hceb_eq, hs2_fr, hwf2, H_conglom, hHcon_len, hholds2,
      hHcon_entries⟩ := h2_fr
    have h3 := compactVerticesProg_spec (w := w) (n := nConglom) (edgeBase := ceb)
      (es := H_conglom) (s := s₂) h16 hwf2 hholds2 (by rw [hceb_eq, hs2_fr, hHcon_len])
      (hfit.of_le (by rw [hs2_fr, hs1_fr, hHcon_len]; omega))
    rw [hHcon_len] at h3
    have h3_fr := framedTriple_iff_realization.mp h3
    set cr := (Memory.spec 0).clientResult s₂
      (compactVerticesProg ⟨nConglom, H_rem.length, ceb⟩)
    set s₃ := (Memory.spec 0).clientState s₂
      (compactVerticesProg ⟨nConglom, H_rem.length, ceb⟩)
    obtain ⟨hv3, hcost3, hmod3, _, hcr1_eq, hcr2_le, hs3_fr, hwf3, lift_a, H_a, hlift_a_inj,
      hHa_len, hholds3, _, hHa_cov, hHa_lift⟩ := h3_fr
    have hretag_get : ∀ i (hi : i < H_rem.length),
        H_retag[i]'(by omega) =
          (⟨H_rem[i].u, H_rem[i].v, H_rem[i].weight, i⟩ : IndexedEdge n') := by
      intro i hi; dsimp only [H_retag]; rw [List.getElem_mapIdx]
    have hna_mul : cr.numVertices * r0 ≤ n' := by
      refine partition_conglom_active_verts_le hcov hconglom_rel hstop hlift_a_inj fun y => ?_
      obtain ⟨e_a, he_a, he_uv⟩ := hHa_cov y
      obtain ⟨i, hi_a, hi_eq⟩ := List.mem_iff_getElem.mp he_a
      have hi_rem : i < H_rem.length := by omega
      have hi_map : i < (H_a.map fun e =>
          (⟨lift_a e.u, lift_a e.v, e.weight, e.id⟩ : IndexedEdge nConglom)).length := by
        simp [hi_a]
      have he_con_mem := List.getElem_of_eq hHa_lift hi_map
      simp only [List.getElem_map] at he_con_mem
      have hent := hHcon_entries i hi_rem (by omega)
      rw [hretag_get i hi_rem] at hent
      dsimp only at hent
      refine ⟨H_rem[i], List.getElem_mem hi_rem, ?_⟩
      rcases he_uv with hu | hv
      · left; apply Fin.ext
        rw [← hent.1, ← he_con_mem]; dsimp only
        rw [← hi_eq] at hu
        exact congrArg Fin.val (congrArg lift_a hu)
      · right; apply Fin.ext
        rw [← hent.2.1, ← he_con_mem]; dsimp only
        rw [← hi_eq] at hv
        exact congrArg Fin.val (congrArg lift_a hv)
    have hna_le_n' : cr.numVertices ≤ n' := hcr2_le.trans hnConglom_le
    have hiter_a : H_rem.length * Nat.iterClogBeta ((2 * H_rem.length) / cr.numVertices)
        cr.numVertices ≤ 4 * H_rem.length + 20 * n' := by
      have h1 := Nat.mul_iterClogBeta_div_le_iterLog (by decide : 1 ≤ 3) H_a.length cr.numVertices
      change H_a.length * Nat.iterClogBeta ((2 * H_a.length) / cr.numVertices) cr.numVertices ≤
        4 * H_a.length + 20 * cr.numVertices * max 1 (Nat.iterLog 3 cr.numVertices) at h1
      have h2 : Nat.iterLog 3 cr.numVertices ≤ Nat.iterLog 3 n₀ :=
        Nat.iterLog_mono 3 (hna_le_n'.trans hn'_le)
      have h3 : max 1 (Nat.iterLog 3 cr.numVertices) ≤ r0 :=
        (max_le_max le_rfl h2).trans hr0_log
      have h4 : 20 * cr.numVertices * max 1 (Nat.iterLog 3 cr.numVertices) ≤ 20 * n' := by
        calc 20 * cr.numVertices * max 1 (Nat.iterLog 3 cr.numVertices)
            ≤ 20 * cr.numVertices * r0 := Nat.mul_le_mul_left _ h3
          _ = 20 * (cr.numVertices * r0) := Nat.mul_assoc 20 cr.numVertices r0
          _ ≤ 20 * n' := Nat.mul_le_mul_left 20 hna_mul
      rw [hHa_len] at h1
      omega
    have hiter_a' : H_a.length * Nat.iterClogBeta ((2 * H_a.length) / cr.numVertices)
        cr.numVertices ≤ 4 * H_rem.length + 20 * n' := by
      simpa [hHa_len] using hiter_a
    have hfit4 : Fits w (s₃.frontier + (21 * H_a.length + 8 * cr.numVertices +
        76 * H_a.length * Nat.iterClogBeta ((2 * H_a.length) / cr.numVertices) cr.numVertices +
          3)) := by
      have h76 := Nat.mul_le_mul_left 76 hiter_a'
      exact hfit.of_le (by rw [hs3_fr, hs2_fr, hs1_fr, Nat.mul_assoc]; have := hHa_len; omega)
    have h4 := denseCaseProg_spec (w := w) (n := cr.numVertices) (edgeBase := cr.edgeBase)
      (es := H_a) (s := s₃) h16 hwf3 hholds3 (by rw [hcr1_eq, hs3_fr, hHa_len]) hfit4
    rw [hHa_len] at h4
    have h4_fr := framedTriple_iff_realization.mp h4
    set dr := (Memory.spec 0).clientResult s₃
      (denseCaseProg ⟨cr.numVertices, H_rem.length, cr.edgeBase⟩)
    set s₄ := (Memory.spec 0).clientState s₃
      (denseCaseProg ⟨cr.numVertices, H_rem.length, cr.edgeBase⟩)
    obtain ⟨hv4, hcost4, hmod4, _, hdr_fr_ge, hdr_fr_ed, hs4_fr, hwf4,
      msf_a, hmsfa_len, hmsfa_holds, hmsfa_sub, hmsfa_msf⟩ := h4_fr
    have hHa_id_range : H_a.map IndexedEdge.id = List.range H_rem.length := by
      apply List.ext_getElem
      · simp [hHa_len]
      · intro i hi1 _
        have hi_rem : i < H_rem.length := by simpa [hHa_len] using hi1
        have hi_map : i < (H_a.map fun e =>
            (⟨lift_a e.u, lift_a e.v, e.weight, e.id⟩ : IndexedEdge nConglom)).length := by
          simp [hHa_len, hi_rem]
        have he_con := List.getElem_of_eq hHa_lift hi_map
        have hent := hHcon_entries i hi_rem (by omega)
        simp only [List.getElem_map, List.getElem_range] at he_con ⊢
        rw [congrArg IndexedEdge.id he_con, hent.2.2.2, hretag_get i hi_rem]
    have hmsfa_ids : ∀ e ∈ msf_a, e.id < H_rem.length ∧
        ∃ hi : e.id < H_rem.length,
          (conglomFn (H_rem[e.id]'hi).u).val = (lift_a e.u).val ∧
          (conglomFn (H_rem[e.id]'hi).v).val = (lift_a e.v).val ∧
          (H_rem[e.id]'hi).weight = e.weight := by
      intro e he
      have he_ha : e ∈ H_a := hmsfa_sub.subset he
      obtain ⟨j, hj_a, rfl⟩ := List.mem_iff_getElem.mp he_ha
      have hj_rem : j < H_rem.length := by omega
      have hid_eq : (H_a[j]'hj_a).id = j := by
        have h := List.getElem_of_eq hHa_id_range (by simp only [List.length_map]; exact hj_a)
        simpa using h
      have hj_map : j < (H_a.map fun e =>
          (⟨lift_a e.u, lift_a e.v, e.weight, e.id⟩ : IndexedEdge nConglom)).length := by
        simp [hHa_len, hj_rem]
      have he_con := List.getElem_of_eq hHa_lift hj_map
      have hent := hHcon_entries j hj_rem (by omega)
      rw [hretag_get j hj_rem] at hent
      dsimp only at hent
      simp only [List.getElem_map] at he_con
      rw [hid_eq]
      refine ⟨hj_rem, hj_rem, ?_, ?_, ?_⟩
      · have := congrArg IndexedEdge.u he_con; rw [← hent.1, ← this]
      · have := congrArg IndexedEdge.v he_con; rw [← hent.2.1, ← this]
      · have := congrArg IndexedEdge.weight he_con; rw [← hent.2.2.1, ← this]
    have hmsfa_card : msf_a.length ≤ cr.numVertices := by
      have hacyc : IsAcyclic (msf_a.map IndexedEdge.toWeighted) := hmsfa_msf.1.2.1
      have hlen := isAcyclic_length_le_finset_sub_one (Finset.univ : Finset (Fin cr.numVertices)) _
        hacyc (fun _ _ => ⟨Finset.mem_univ _, Finset.mem_univ _⟩)
      simp only [Finset.card_univ, Fintype.card_fin, List.length_map] at hlen
      omega
    have hdr2_le_rem : dr.numEdges ≤ H_rem.length := by
      have := hmsfa_sub.length_le; omega
    have hs4_le : s₄.frontier ≤ s.frontier + 337 * H_rem.length + 1529 * n' + 3 := by
      have h76 := Nat.mul_le_mul_left 76 hiter_a
      rw [hs3_fr, hs2_fr, hs1_fr, Nat.mul_assoc] at hs4_fr
      omega
    have hmod14 : Memory.Modifies ∅ s s₄ :=
      ((hmod1.trans hmod2).trans hmod3).trans hmod4
    have hs3_le_s4 : s₃.frontier ≤ s₄.frontier := hmod4.1
    have hrem_holds_s4 : HoldsIndexedEdges hRemBase H_rem s₄.mem :=
      hrem_holds.congr fun a _ ha =>
        hmod14.mem_eq_of_not_mem (ha.trans_le hrem_lt) (Set.notMem_empty _)
    have h5 := liftHRemProg_spec (w := w) (n := n') (nA := cr.numVertices)
      (hRemBase := hRemBase) (msfBase := dr.edgeBase) (H_rem := H_rem) (H_msf := msf_a)
      (s := s₄) h16 hwf4 hrem_holds_s4 (by rw [hs3_fr, hs2_fr, hs1_fr] at hs3_le_s4; omega)
      hmsfa_holds (by rw [hmsfa_len]; exact hdr_fr_ed)
      (fun e he => (hmsfa_ids e he).1) (hfit.of_le (by rw [hmsfa_len]; omega))
    rw [hmsfa_len] at h5
    let prog5 := liftHRemProg ⟨hRemBase, dr.edgeBase, dr.numEdges⟩
    change Memory.FramedTriple w s₄ prog5 _ ∅ _ at h5
    have h5_fr := framedTriple_iff_realization.mp h5
    set lb := (Memory.spec 0).clientResult s₄ prog5
    set s₅ := (Memory.spec 0).clientState s₄ prog5
    obtain ⟨hv5, hcost5, hmod5, hlb_eq, hs5_fr, hwf5, hlift_holds⟩ := h5_fr
    have hprep_eq : pr02SolveHRemPrep d =
        (retagIndexedProg ⟨hRemBase, H_rem.length⟩ >>= fun rb' =>
          contractEdgesProg ⟨H_rem.length, rb', conglomBase⟩ >>= fun ceb' =>
            compactVerticesProg ⟨nConglom, H_rem.length, ceb'⟩) := rfl
    have hvh_prep : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (pr02SolveHRemPrep d)) := by
      rw [hprep_eq]
      refine validHistory_bind_step hv1 ?_
      refine validHistory_bind_step hv2 hv3
    have hres_prep : (Memory.spec 0).clientResult s (pr02SolveHRemPrep d) = cr := by
      rw [hprep_eq, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_bind]
    have hst_prep : (Memory.spec 0).clientState s (pr02SolveHRemPrep d) = s₃ := by
      rw [hprep_eq, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_bind]
    have hrb_fold : (Memory.spec 0).clientResult s
        (retagIndexedProg ⟨hRemBase, H_rem.length⟩) = rb := rfl
    have hs1_fold : (Memory.spec 0).clientState s
        (retagIndexedProg ⟨hRemBase, H_rem.length⟩) = s₁ := rfl
    have hceb_fold : (Memory.spec 0).clientResult s₁
        (contractEdgesProg ⟨H_rem.length, rb, conglomBase⟩) = ceb := rfl
    have hs2_fold : (Memory.spec 0).clientState s₁
        (contractEdgesProg ⟨H_rem.length, rb, conglomBase⟩) = s₂ := rfl
    have hsafe_prep : pr02SolveHRemPrepSafe w d s := by
      unfold pr02SolveHRemPrepSafe retagIndexedProgSafe
      dsimp only [d]
      simp only [hrb_fold, hs1_fold, hceb_fold, hs2_fold]
      refine ⟨h16, ⟨h16, hrem_lt, hfit.of_le (by omega)⟩,
        hfit.of_le (by rw [hs1_fr]; omega), fun j hj => ?_, ?_, ?_, fun j hj => ?_⟩
      · obtain ⟨hu, hv, _, _⟩ := hholds1 j (by rw [hretag_len]; exact hj)
        rw [hu, hv]
        have hu_lt := (H_retag[j]'(by rw [hretag_len]; exact hj)).u.isLt
        have hv_lt := (H_retag[j]'(by rw [hretag_len]; exact hj)).v.isLt
        rw [hrb_eq, hs1_fr]; omega
      · rw [hceb_eq, hs2_fr]
      · exact hfit.of_le (by rw [hs2_fr, hs1_fr]; omega)
      · obtain ⟨hu, hv, _, _⟩ := hholds2 j (by rw [hHcon_len]; exact hj)
        rw [hu, hv]
        exact ⟨(H_conglom[j]'(by rw [hHcon_len]; exact hj)).u.isLt,
          (H_conglom[j]'(by rw [hHcon_len]; exact hj)).v.isLt⟩
    have hcost_prep : memoryCost (pr02SolveHRemPrep d) s ≤
        32 * H_rem.length + 3 * n' + 4 := by
      rw [hprep_eq, memoryCost_bind', hrb_fold, hs1_fold, memoryCost_bind', hceb_fold, hs2_fold]
      omega
    have hne_eq : pr02SolveHRemNonEmpty d =
        (pr02SolveHRemPrep d >>= fun cr' =>
          denseCaseProg ⟨cr'.numVertices, H_rem.length, cr'.edgeBase⟩ >>= fun dr' =>
            liftHRemProg ⟨hRemBase, dr'.edgeBase, dr'.numEdges⟩ >>= fun lb' =>
              pure ⟨lb', dr'.numEdges⟩) := rfl
    have hvh_ne : (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (pr02SolveHRemNonEmpty d)) := by
      rw [hne_eq]
      refine validHistory_bind_step hvh_prep ?_
      rw [hres_prep, hst_prep]
      refine validHistory_bind_step hv4 ?_
      exact validHistory_bind_step hv5 (validHistory_pure w _ _)
    have hres_ne : (Memory.spec 0).clientResult s (pr02SolveHRemNonEmpty d) =
        ⟨lb, dr.numEdges⟩ := by
      rw [hne_eq, StateTransitionSpec.clientResult_bind, hres_prep, hst_prep,
        StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientResult_bind,
        StateTransitionSpec.clientResult_pure]
    have hst_ne : (Memory.spec 0).clientState s (pr02SolveHRemNonEmpty d) = s₅ := by
      rw [hne_eq, StateTransitionSpec.clientState_bind, hres_prep, hst_prep,
        StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind,
        StateTransitionSpec.clientState_pure]
    have hdr_fold : (Memory.spec 0).clientResult s₃
        (denseCaseProg ⟨cr.numVertices, H_rem.length, cr.edgeBase⟩) = dr := rfl
    have hs4_fold : (Memory.spec 0).clientState s₃
        (denseCaseProg ⟨cr.numVertices, H_rem.length, cr.edgeBase⟩) = s₄ := rfl
    have hsafe_ne : pr02SolveHRemNonEmptySafe w d s := by
      unfold pr02SolveHRemNonEmptySafe liftHRemProgSafe
      simp only [hres_prep, hst_prep]
      dsimp only [d]
      simp only [hdr_fold, hs4_fold]
      refine ⟨h16, hsafe_prep, h16, by rw [hcr1_eq, hs3_fr], ?_, fun j hj => ?_,
        h16, hdr_fr_ed, fun k hk => ?_, hfit.of_le (by have := hdr2_le_rem; omega)⟩
      · simpa [hHa_len] using hfit4
      · obtain ⟨hu, hv, _, _⟩ := hholds3 j (by rw [hHa_len]; exact hj)
        rw [hu, hv]
        exact ⟨(H_a[j]'(by rw [hHa_len]; exact hj)).u.isLt,
          (H_a[j]'(by rw [hHa_len]; exact hj)).v.isLt⟩
      · have hk' : k < msf_a.length := by rw [hmsfa_len]; exact hk
        have hid_eq := (hmsfa_holds k hk').2.2.2
        have hid_lt := (hmsfa_ids msf_a[k] (List.getElem_mem hk')).1
        rw [hid_eq]
        rw [hs3_fr, hs2_fr, hs1_fr] at hs3_le_s4
        omega
    have hcost4_le : memoryCost (denseCaseProg ⟨cr.numVertices, H_rem.length, cr.edgeBase⟩) s₃ ≤
        3618 * H_rem.length + 17798 * n' + 11 := by
      have h889 := Nat.mul_le_mul_left 889 hiter_a
      rw [Nat.mul_assoc] at hcost4
      omega
    have hcost_ne : memoryCost (pr02SolveHRemNonEmpty d) s ≤
        3659 * H_rem.length + 17801 * n' + 16 := by
      rw [hne_eq, memoryCost_bind', hres_prep, hst_prep, memoryCost_bind',
        hdr_fold, hs4_fold, memoryCost_bind', memoryCost_pure, add_zero]
      dsimp only [prog5] at hcost5
      omega
    let H_lift := msf_a.pmap (fun e he => H_rem[e.id]'(hmsfa_ids e he).1) (fun _ he => he)
    have hHlift_sub : H_lift.Subperm H_rem := by
      have hids_sub : (msf_a.map IndexedEdge.id).Subperm (List.range H_rem.length) := by
        rw [← hHa_id_range]
        exact List.subperm_map _ hmsfa_sub
      let idxToEdge : ℕ → IndexedEdge n' := fun i => H_rem.getD i (H_rem[0]'hm_pos)
      have hlift_map : H_lift = (msf_a.map IndexedEdge.id).map idxToEdge := by
        apply List.ext_getElem
        · simp [H_lift]
        · intro i hi1 _
          have hi_msf : i < msf_a.length := by simpa [H_lift] using hi1
          have hid_lt : msf_a[i].id < H_rem.length :=
            (hmsfa_ids msf_a[i] (List.getElem_mem hi_msf)).1
          simp [H_lift, idxToEdge, List.getD_eq_getElem?_getD, hid_lt]
      have hrem_map : (List.range H_rem.length).map idxToEdge = H_rem := by
        apply List.ext_getElem
        · simp
        · intro i hi1 _
          have hi_r : i < H_rem.length := by simpa using hi1
          simp [idxToEdge, List.getD_eq_getElem?_getD, hi_r]
      rw [hlift_map, ← hrem_map]
      exact List.subperm_map idxToEdge hids_sub
    have hHlift_msf : IsMinSpanningForest
        (contractEdgeList conglomFn (H_rem.map IndexedEdge.toWeighted))
        (contractEdgeList conglomFn (H_lift.map IndexedEdge.toWeighted)) := by
      have hcon_es_eq : contractEdgeList conglomFn (H_rem.map IndexedEdge.toWeighted) =
          H_conglom.map IndexedEdge.toWeighted := by
        apply List.ext_getElem
        · simp [contractEdgeList, hHcon_len]
        · intro i hi1 _
          have hi_rem : i < H_rem.length := by simpa [contractEdgeList] using hi1
          have hent := hHcon_entries i hi_rem (by omega)
          simp only [contractEdgeList, List.getElem_map, contractEdge, IndexedEdge.toWeighted]
          rw [hretag_get i hi_rem] at hent
          dsimp only at hent
          congr 1
          · exact Fin.ext hent.1.symm
          · exact Fin.ext hent.2.1.symm
          · exact hent.2.2.1.symm
      have hcon_lift_eq : contractEdgeList conglomFn (H_lift.map IndexedEdge.toWeighted) =
          contractEdgeList lift_a (msf_a.map IndexedEdge.toWeighted) := by
        apply List.ext_getElem
        · simp [contractEdgeList, H_lift]
        · intro i hi1 _
          have hi_msf : i < msf_a.length := by simpa [contractEdgeList, H_lift] using hi1
          obtain ⟨hi_rem, _, hu, hv, hw⟩ := hmsfa_ids msf_a[i] (List.getElem_mem hi_msf)
          have hu' : conglomFn (H_rem[msf_a[i].id]'hi_rem).u = lift_a msf_a[i].u := Fin.ext hu
          have hv' : conglomFn (H_rem[msf_a[i].id]'hi_rem).v = lift_a msf_a[i].v := Fin.ext hv
          simp only [contractEdgeList, List.getElem_map, List.getElem_pmap, H_lift,
            contractEdge, IndexedEdge.toWeighted, hu', hv', hw]
      rw [hcon_es_eq, hcon_lift_eq]
      exact compactVertices_isMinSpanningForest hlift_a_inj hHa_lift hmsfa_msf
    have hmul_dr2 : dr.numEdges * r0 ≤ n' := by
      rw [← hmsfa_len]
      exact (Nat.mul_le_mul_right r0 hmsfa_card).trans hna_mul
    have hmod_ne : Memory.Modifies ∅ s s₅ := hmod14.trans hmod5
    refine ⟨⟨h16, fun h => absurd h (by dsimp only [d]; omega), fun _ => hsafe_ne⟩,
      framedTriple_iff_realization.mpr ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [hprog_ne]; exact hvh_ne
    · rw [hprog_ne]; exact hcost_ne
    · rw [hprog_ne, hst_ne]; exact hmod_ne
    · rw [hprog_ne, hres_ne, hst_ne]; dsimp only; rw [hlb_eq, hs5_fr]
    · rw [hprog_ne, hres_ne]; exact hmul_dr2
    · rw [hprog_ne, hres_ne]; exact hdr2_le_rem
    · rw [hprog_ne, hst_ne, hs5_fr]; rw [hs3_fr, hs2_fr, hs1_fr] at hs3_le_s4; omega
    · rw [hprog_ne, hst_ne, hs5_fr]; omega
    · rw [hprog_ne, hst_ne]; exact hwf5
    · refine ⟨H_lift, ?_, ?_, hHlift_sub, hHlift_msf⟩
      · rw [hprog_ne, hres_ne]; simp [H_lift, hmsfa_len]
      · rw [hprog_ne, hres_ne, hst_ne]; dsimp only; exact hlift_holds

end Cslib.Algorithms.WordRAM.MinimumSpanningForest
