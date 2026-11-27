/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Algorithms.WordRAM.MinimumSpanningForest.Partition.Bridges
import Mathlib.Tactic.FinCases

/-!
# Tests for Word-RAM MSF Partition Round Bridges

Exercises `PartitionRoundWitness`, `PartitionRoundWitness.compGlobal`,
`PartitionRoundWitness.verts`, `partition_optDepth_sum_le`,
`partition_conglom_active_verts_le`, and `partition_isMinSpanningForest` across:

- a 5-vertex, 3-round overlapping conglomerate instance (`V₀ = {0, 1}`, `V₁ = {2, 0}` overlapping
  at shared vertex `0`, `V₂ = {3, 4}`), non-empty inter-conglomerate `H_rem` pruned down to
  `H_lift`, and non-empty corrupted border edges `corrEdges`;
- a 4-vertex, 2-round disjoint conglomerate instance with `n_a = 2`, `maxsize = 2`, `n = 4`;
- a 0-edge / 0-active-conglomerate boundary instance on `n = 2`;
- a 5-vertex, `numSteps = 2` overlapping multigraph witness exercising non-trivial `truncateDJP`
  (`D_pre.numSteps = 1`), parallel edges, and duplicate weights in `partition_isMinSpanningForest`;
- a 5-vertex witness exercising the third `hstop` branch (inactive `< maxsize` isolated component
  with no incident `H_rem` edges alongside active conglomerates).
-/

-- This test module intentionally exports no declarations.
set_option linter.privateModule false

namespace CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.PartitionBridges

open Cslib.DataStructure.DisjointSet
open Cslib.Algorithms.Lean.Kruskal
open Cslib.Query.MinimumSpanningForest
open Cslib.Algorithms.WordRAM.MinimumSpanningForest

/-! ## Multi-round overlapping conglomerate witness (`n = 5`) -/

private def tree5R0 : DynamicDJPTree 5 where
  numSteps := 1
  root := 0
  edge _ := ⟨0, 1, 1⟩
  wPop _ := 2
  vIn _ := 0
  vOut _ := 1
  edge_weight_le_wPop s := by fin_cases s; decide
  ends_match s := by fin_cases s; simp
  vIn_mem s := by fin_cases s; decide
  vOut_not_mem s := by fin_cases s; decide
  djp_future s s' hlt := by fin_cases s; fin_cases s'; simp_all

private def tree5R1 : DynamicDJPTree 5 where
  numSteps := 1
  root := 2
  edge _ := ⟨2, 0, 5⟩
  wPop _ := 5
  vIn _ := 2
  vOut _ := 0
  edge_weight_le_wPop s := by fin_cases s; decide
  ends_match s := by fin_cases s; simp
  vIn_mem s := by fin_cases s; decide
  vOut_not_mem s := by fin_cases s; decide
  djp_future s s' hlt := by fin_cases s; fin_cases s'; simp_all

private def tree5R2 : DynamicDJPTree 5 where
  numSteps := 1
  root := 3
  edge _ := ⟨3, 4, 3⟩
  wPop _ := 4
  vIn _ := 3
  vOut _ := 4
  edge_weight_le_wPop s := by fin_cases s; decide
  ends_match s := by fin_cases s; simp
  vIn_mem s := by fin_cases s; decide
  vOut_not_mem s := by fin_cases s; decide
  djp_future s s' hlt := by fin_cases s; fin_cases s'; simp_all

private def r5_0 : PartitionRoundWitness 5 where
  tree := tree5R0
  numVerts := 2
  lift k := ⟨k.val, by omega⟩
  compLocal := [⟨0, 1, 1, 0⟩]
  corrEdges := [⟨1, 2, 9, 5⟩]

private def r5_1 : PartitionRoundWitness 5 where
  tree := tree5R1
  numVerts := 2
  lift k := if k.val = 0 then 2 else 0
  compLocal := [⟨0, 1, 5, 1⟩]
  corrEdges := []

private def r5_2 : PartitionRoundWitness 5 where
  tree := tree5R2
  numVerts := 2
  lift k := ⟨k.val + 3, by omega⟩
  compLocal := [⟨0, 1, 3, 2⟩]
  corrEdges := [⟨1, 4, 11, 6⟩]

private def rounds5 : List (PartitionRoundWitness 5) := [r5_0, r5_1, r5_2]
private def hRem5 : List (IndexedEdge 5) := [⟨1, 3, 7, 3⟩, ⟨0, 4, 8, 4⟩]
private def es5 : List (IndexedEdge 5) :=
  (rounds5.flatMap PartitionRoundWitness.compGlobal) ++ hRem5 ++
    (rounds5.flatMap PartitionRoundWitness.corrEdges)

private def conglomFn5 (x : Fin 5) : Fin 2 := if x.val ≤ 2 then 0 else 1
private def fComps5 : List (List (WeightedEdge 5 ℕ)) := [[⟨0, 1, 1⟩], [⟨2, 0, 5⟩], [⟨3, 4, 3⟩]]
private def hLift5 : List (WeightedEdge 5 ℕ) := [⟨1, 3, 7⟩]
private def f5 : List (WeightedEdge 5 ℕ) := [⟨0, 1, 1⟩, ⟨3, 4, 3⟩, ⟨2, 0, 5⟩, ⟨1, 3, 7⟩]

example :
    r5_0.compGlobal = [⟨0, 1, 1, 0⟩] ∧
      r5_1.compGlobal = [⟨2, 0, 5, 1⟩] ∧
      r5_2.compGlobal = [⟨3, 4, 3, 2⟩] ∧
      r5_0.verts = ({0, 1} : Finset (Fin 5)) ∧
      r5_1.verts = ({2, 0} : Finset (Fin 5)) ∧
      r5_2.verts = ({3, 4} : Finset (Fin 5)) := by
  refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩ <;> decide

private theorem rounds5_hsimp :
    IsSimple (edgeEnds (es5.map IndexedEdge.toWeighted)) := by
  rw [isSimple_iff]
  refine ⟨fun i => by fin_cases i <;> decide, fun i j hij => by
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)⟩

private theorem rounds5_cov : ∀ x : Fin 5, ∃ r ∈ rounds5, x ∈ r.verts := by
  intro x
  fin_cases x
  · exact ⟨r5_0, by simp [rounds5], by decide⟩
  · exact ⟨r5_0, by simp [rounds5], by decide⟩
  · exact ⟨r5_1, by simp [rounds5], by decide⟩
  · exact ⟨r5_2, by simp [rounds5], by decide⟩
  · exact ⟨r5_2, by simp [rounds5], by decide⟩

private theorem rounds5_conglom_rel : ∀ x y : Fin 5,
    conglomFn5 x = conglomFn5 y ↔
      (edgePartition (rounds5.flatMap fun r => r.tree.treeEdges)).rel x y = true := by
  intro x y
  fin_cases x <;> fin_cases y <;> decide

example :
    (rounds5.map fun r =>
        optDepth (edgeEnds (r.compLocal.map IndexedEdge.toWeighted))).sum ≤
      optDepthMN es5.length 5 ∧
      2 * 2 ≤ 5 ∧
      IsMinSpanningForest (es5.map IndexedEdge.toWeighted) f5 := by
  have hdepth := partition_optDepth_sum_le (es := es5) (rounds := rounds5)
    rounds5_hsimp ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)).subperm
    (fun i => by
      fin_cases i <;> dsimp only
      · refine ⟨fun a b h => by fin_cases a <;> fin_cases b <;> cases h <;> rfl,
          fun e he => by
            change e ∈ r5_0.compGlobal at he
            change e.u ∈ r5_0.verts ∧ e.v ∈ r5_0.verts
            simp only [r5_0, PartitionRoundWitness.compGlobal] at he
            rcases List.mem_map.mp he with ⟨_, he', rfl⟩
            rw [List.mem_singleton] at he'
            subst he'
            decide,
          by decide⟩
      · refine ⟨fun a b h => by fin_cases a <;> fin_cases b <;> cases h <;> rfl,
          fun e he => by
            change e ∈ r5_1.compGlobal at he
            change e.u ∈ r5_1.verts ∧ e.v ∈ r5_1.verts
            simp only [r5_1, PartitionRoundWitness.compGlobal] at he
            rcases List.mem_map.mp he with ⟨_, he', rfl⟩
            rw [List.mem_singleton] at he'
            subst he'
            decide,
          by decide⟩
      · refine ⟨fun a b h => by fin_cases a <;> fin_cases b <;> cases h <;> rfl,
          fun e he => by
            change e ∈ r5_2.compGlobal at he
            change e.u ∈ r5_2.verts ∧ e.v ∈ r5_2.verts
            simp only [r5_2, PartitionRoundWitness.compGlobal] at he
            rcases List.mem_map.mp he with ⟨_, he', rfl⟩
            rw [List.mem_singleton] at he'
            subst he'
            decide,
          by decide⟩)
  have hconglom := partition_conglom_active_verts_le (n := 5) (nConglom := 2) (n_a := 2)
    (maxsize := 2) (rounds := rounds5) (H_rem := hRem5) (conglomFn := conglomFn5)
    (lift_a := id) rounds5_cov rounds5_conglom_rel
    (fun i => by fin_cases i <;> decide)
    Function.injective_id
    (fun y => by fin_cases y <;> exact ⟨⟨1, 3, 7, 3⟩, by simp [hRem5], by decide⟩)
  have hF_msf : ∀ i : Fin rounds5.length,
      IsMinSpanningForest (rounds5[i.val].compGlobal.map IndexedEdge.toWeighted)
        (fComps5[i.val]'(by dsimp [fComps5, rounds5] at *; omega)) := by
    intro i
    fin_cases i <;> dsimp only [rounds5, fComps5]
    · have hk : kruskalEdges (r5_0.compGlobal.map IndexedEdge.toWeighted) = [⟨0, 1, 1⟩] := by
        rw [kruskalEdges, show sortEdges (r5_0.compGlobal.map IndexedEdge.toWeighted) =
          [⟨0, 1, 1⟩] by simp [r5_0, PartitionRoundWitness.compGlobal, IndexedEdge.toWeighted,
            sortEdges_singleton]]
        rfl
      exact hk ▸ kruskalEdges_isMinSpanningForest _
    · have hk : kruskalEdges (r5_1.compGlobal.map IndexedEdge.toWeighted) = [⟨2, 0, 5⟩] := by
        rw [kruskalEdges, show sortEdges (r5_1.compGlobal.map IndexedEdge.toWeighted) =
          [⟨2, 0, 5⟩] by simp [r5_1, PartitionRoundWitness.compGlobal, IndexedEdge.toWeighted,
            sortEdges_singleton]]
        rfl
      exact hk ▸ kruskalEdges_isMinSpanningForest _
    · have hk : kruskalEdges (r5_2.compGlobal.map IndexedEdge.toWeighted) = [⟨3, 4, 3⟩] := by
        rw [kruskalEdges, show sortEdges (r5_2.compGlobal.map IndexedEdge.toWeighted) =
          [⟨3, 4, 3⟩] by simp [r5_2, PartitionRoundWitness.compGlobal, IndexedEdge.toWeighted,
            sortEdges_singleton]]
        rfl
      exact hk ▸ kruskalEdges_isMinSpanningForest _
  have hHL_msf : IsMinSpanningForest
      (contractEdgeList conglomFn5 (hRem5.map IndexedEdge.toWeighted))
      (contractEdgeList conglomFn5 hLift5) := by
    have hk : kruskalEdges (contractEdgeList conglomFn5 (hRem5.map IndexedEdge.toWeighted)) =
        contractEdgeList conglomFn5 hLift5 := by
      rw [kruskalEdges, show sortEdges
        (contractEdgeList conglomFn5 (hRem5.map IndexedEdge.toWeighted)) =
          [⟨0, 1, 7⟩, ⟨0, 1, 8⟩] by
            simp [hRem5, contractEdgeList, contractEdge, IndexedEdge.toWeighted, conglomFn5,
              sortEdges_cons_cons, sortEdges_singleton]]
      rfl
    exact hk ▸ kruskalEdges_isMinSpanningForest _
  have hF : IsMinSpanningForest
      (fComps5.flatten ++ hLift5 ++
        (rounds5.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) f5 := by
    have hk : kruskalEdges (fComps5.flatten ++ hLift5 ++
        (rounds5.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) = f5 := by
      rw [kruskalEdges, show sortEdges (fComps5.flatten ++ hLift5 ++
        (rounds5.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) =
          [⟨0, 1, 1⟩, ⟨3, 4, 3⟩, ⟨2, 0, 5⟩, ⟨1, 3, 7⟩, ⟨1, 2, 9⟩, ⟨1, 4, 11⟩] by
            simp [fComps5, hLift5, rounds5, r5_0, r5_1, r5_2, IndexedEdge.toWeighted,
              sortEdges_cons_cons, sortEdges_singleton]]
      rfl
    exact hk ▸ kruskalEdges_isMinSpanningForest _
  have hmsf := partition_isMinSpanningForest (n := 5) (nConglom := 2)
    (es := es5.map IndexedEdge.toWeighted) (rounds := rounds5) (H_rem := hRem5)
    (conglomFn := conglomFn5) (F_comps := fComps5) (H_lift := hLift5) (F := f5)
    (List.Perm.refl _) rounds5_cov rounds5_conglom_rel
    (fun i => by
      fin_cases i
      · refine ⟨(show tree5R0.treeEdges.Sublist _ by decide).subperm, fun x hx hprev => ?_⟩
        fin_cases x <;> first | exact absurd hx (by decide) | exact absurd hprev (by decide)
      · refine ⟨(show tree5R1.treeEdges.Sublist _ by decide).subperm, fun x hx hprev => ?_⟩
        refine ⟨by decide, ?_⟩
        fin_cases x <;> first | rfl | exact absurd hx (by decide) | exact absurd hprev (by decide)
      · refine ⟨(show tree5R2.treeEdges.Sublist _ by decide).subperm, fun x hx hprev => ?_⟩
        fin_cases x <;> first | exact absurd hx (by decide) | exact absurd hprev (by decide))
    (fun i e he => by
      fin_cases i <;>
        simp only [hRem5, List.mem_cons, List.not_mem_nil, or_false] at he <;>
        rcases he with rfl | rfl <;>
        refine ⟨by decide, fun s hs => ?_⟩ <;>
        fin_cases s <;> decide)
    (fun i j hij e he => by
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd hij (by decide)
        | (obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
           fin_cases s
           intro s₀ hs
           fin_cases s₀
           first | decide | exact absurd hs (by decide)))
    rfl hF_msf
    (show hLift5.Sublist (hRem5.map IndexedEdge.toWeighted) by decide).subperm
    hHL_msf hF
  exact ⟨hdepth, hconglom, hmsf⟩

/-! ## Disjoint exact-pack witness (`n = 4`, `n_a = maxsize = 2`) -/

private def tree4R0 : DynamicDJPTree 4 where
  numSteps := 1
  root := 0
  edge _ := ⟨0, 1, 2⟩
  wPop _ := 2
  vIn _ := 0
  vOut _ := 1
  edge_weight_le_wPop s := by fin_cases s; decide
  ends_match s := by fin_cases s; simp
  vIn_mem s := by fin_cases s; decide
  vOut_not_mem s := by fin_cases s; decide
  djp_future s s' hlt := by fin_cases s; fin_cases s'; simp_all

private def tree4R1 : DynamicDJPTree 4 where
  numSteps := 1
  root := 2
  edge _ := ⟨2, 3, 3⟩
  wPop _ := 3
  vIn _ := 2
  vOut _ := 3
  edge_weight_le_wPop s := by fin_cases s; decide
  ends_match s := by fin_cases s; simp
  vIn_mem s := by fin_cases s; decide
  vOut_not_mem s := by fin_cases s; decide
  djp_future s s' hlt := by fin_cases s; fin_cases s'; simp_all

private def r4_0 : PartitionRoundWitness 4 where
  tree := tree4R0
  numVerts := 2
  lift k := ⟨k.val, by omega⟩
  compLocal := [⟨0, 1, 2, 0⟩]
  corrEdges := [⟨0, 3, 9, 3⟩]

private def r4_1 : PartitionRoundWitness 4 where
  tree := tree4R1
  numVerts := 2
  lift k := ⟨k.val + 2, by omega⟩
  compLocal := [⟨0, 1, 3, 1⟩]
  corrEdges := []

private def rounds4 : List (PartitionRoundWitness 4) := [r4_0, r4_1]
private def hRem4 : List (IndexedEdge 4) := [⟨1, 2, 4, 2⟩]
private def es4 : List (IndexedEdge 4) :=
  (rounds4.flatMap PartitionRoundWitness.compGlobal) ++ hRem4 ++
    (rounds4.flatMap PartitionRoundWitness.corrEdges)

private def conglomFn4 (x : Fin 4) : Fin 2 := ⟨x.val / 2, by omega⟩
private def fComps4 : List (List (WeightedEdge 4 ℕ)) := [[⟨0, 1, 2⟩], [⟨2, 3, 3⟩]]
private def hLift4 : List (WeightedEdge 4 ℕ) := [⟨1, 2, 4⟩]
private def f4 : List (WeightedEdge 4 ℕ) := [⟨0, 1, 2⟩, ⟨2, 3, 3⟩, ⟨1, 2, 4⟩]

example :
    2 * 2 ≤ 4 ∧
      (rounds4.map fun r =>
          optDepth (edgeEnds (r.compLocal.map IndexedEdge.toWeighted))).sum ≤
        optDepthMN es4.length 4 ∧
      IsMinSpanningForest (es4.map IndexedEdge.toWeighted) f4 := by
  have hcov : ∀ x : Fin 4, ∃ r ∈ rounds4, x ∈ r.verts := fun x => by
    fin_cases x
    · exact ⟨r4_0, by simp [rounds4], by decide⟩
    · exact ⟨r4_0, by simp [rounds4], by decide⟩
    · exact ⟨r4_1, by simp [rounds4], by decide⟩
    · exact ⟨r4_1, by simp [rounds4], by decide⟩
  have hrel : ∀ x y : Fin 4, conglomFn4 x = conglomFn4 y ↔
      (edgePartition (rounds4.flatMap fun r => r.tree.treeEdges)).rel x y = true :=
    fun x y => by fin_cases x <;> fin_cases y <;> decide
  have hconglom := partition_conglom_active_verts_le (n := 4) (nConglom := 2) (n_a := 2)
    (maxsize := 2) (rounds := rounds4) (H_rem := hRem4) (conglomFn := conglomFn4)
    (lift_a := id) hcov hrel
    (fun i => by fin_cases i <;> decide) Function.injective_id
    (fun y => by fin_cases y <;> exact ⟨⟨1, 2, 4, 2⟩, by simp [hRem4], by decide⟩)
  have hsimp : IsSimple (edgeEnds (es4.map IndexedEdge.toWeighted)) := by
    rw [isSimple_iff]
    refine ⟨fun i => by fin_cases i <;> decide, fun i j hij => by
      fin_cases i <;> fin_cases j <;> first | rfl | exact absurd hij (by decide)⟩
  have hdepth := partition_optDepth_sum_le (es := es4) (rounds := rounds4)
    hsimp ((List.sublist_append_left _ _).trans (List.sublist_append_left _ _)).subperm
    (fun i => by
      fin_cases i <;> dsimp only
      · exact ⟨fun a b h => by fin_cases a <;> fin_cases b <;> cases h <;> rfl,
          fun e he => by
            change e ∈ r4_0.compGlobal at he
            change e.u ∈ r4_0.verts ∧ e.v ∈ r4_0.verts
            simp only [r4_0, PartitionRoundWitness.compGlobal] at he
            rcases List.mem_map.mp he with ⟨_, he', rfl⟩
            rw [List.mem_singleton] at he'
            subst he'
            decide,
          by decide⟩
      · exact ⟨fun a b h => by fin_cases a <;> fin_cases b <;> cases h <;> rfl,
          fun e he => by
            change e ∈ r4_1.compGlobal at he
            change e.u ∈ r4_1.verts ∧ e.v ∈ r4_1.verts
            simp only [r4_1, PartitionRoundWitness.compGlobal] at he
            rcases List.mem_map.mp he with ⟨_, he', rfl⟩
            rw [List.mem_singleton] at he'
            subst he'
            decide,
          by decide⟩)
  have hF_msf : ∀ i : Fin rounds4.length,
      IsMinSpanningForest (rounds4[i.val].compGlobal.map IndexedEdge.toWeighted)
        (fComps4[i.val]'(by dsimp [fComps4, rounds4] at *; omega)) := by
    intro i
    fin_cases i <;> dsimp only [rounds4, fComps4]
    · have hk : kruskalEdges (r4_0.compGlobal.map IndexedEdge.toWeighted) = [⟨0, 1, 2⟩] := by
        rw [kruskalEdges, show sortEdges (r4_0.compGlobal.map IndexedEdge.toWeighted) =
          [⟨0, 1, 2⟩] by simp [r4_0, PartitionRoundWitness.compGlobal, IndexedEdge.toWeighted,
            sortEdges_singleton]]
        rfl
      exact hk ▸ kruskalEdges_isMinSpanningForest _
    · have hk : kruskalEdges (r4_1.compGlobal.map IndexedEdge.toWeighted) = [⟨2, 3, 3⟩] := by
        rw [kruskalEdges, show sortEdges (r4_1.compGlobal.map IndexedEdge.toWeighted) =
          [⟨2, 3, 3⟩] by simp [r4_1, PartitionRoundWitness.compGlobal, IndexedEdge.toWeighted,
            sortEdges_singleton]]
        rfl
      exact hk ▸ kruskalEdges_isMinSpanningForest _
  have hHL_msf : IsMinSpanningForest
      (contractEdgeList conglomFn4 (hRem4.map IndexedEdge.toWeighted))
      (contractEdgeList conglomFn4 hLift4) := by
    have hk : kruskalEdges (contractEdgeList conglomFn4 (hRem4.map IndexedEdge.toWeighted)) =
        contractEdgeList conglomFn4 hLift4 := by
      rw [kruskalEdges, show sortEdges
        (contractEdgeList conglomFn4 (hRem4.map IndexedEdge.toWeighted)) = [⟨0, 1, 4⟩] by
          simp [hRem4, contractEdgeList, contractEdge, IndexedEdge.toWeighted, conglomFn4,
            sortEdges_singleton]]
      rfl
    have hmsf' := kruskalEdges_isMinSpanningForest
      (contractEdgeList conglomFn4 (hRem4.map IndexedEdge.toWeighted))
    rwa [hk] at hmsf'
  have hF : IsMinSpanningForest
      (fComps4.flatten ++ hLift4 ++
        (rounds4.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) f4 := by
    have hk : kruskalEdges (fComps4.flatten ++ hLift4 ++
        (rounds4.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) = f4 := by
      rw [kruskalEdges, show sortEdges (fComps4.flatten ++ hLift4 ++
        (rounds4.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) =
          [⟨0, 1, 2⟩, ⟨2, 3, 3⟩, ⟨1, 2, 4⟩, ⟨0, 3, 9⟩] by
            simp [fComps4, hLift4, rounds4, r4_0, r4_1, IndexedEdge.toWeighted,
              sortEdges_cons_cons, sortEdges_singleton]]
      rfl
    exact hk ▸ kruskalEdges_isMinSpanningForest _
  have hmsf := partition_isMinSpanningForest (n := 4) (nConglom := 2)
    (es := es4.map IndexedEdge.toWeighted) (rounds := rounds4) (H_rem := hRem4)
    (conglomFn := conglomFn4) (F_comps := fComps4) (H_lift := hLift4) (F := f4)
    (List.Perm.refl _) hcov hrel
    (fun i => by
      fin_cases i
      · refine ⟨(show tree4R0.treeEdges.Sublist _ by decide).subperm, fun x hx hprev => ?_⟩
        fin_cases x <;> first | exact absurd hx (by decide) | exact absurd hprev (by decide)
      · refine ⟨(show tree4R1.treeEdges.Sublist _ by decide).subperm, fun x hx hprev => ?_⟩
        fin_cases x <;> first | exact absurd hx (by decide) | exact absurd hprev (by decide))
    (fun i e he => by
      fin_cases i <;>
        simp only [hRem4, List.mem_cons, List.not_mem_nil, or_false] at he <;>
        rcases he with rfl <;>
        refine ⟨by decide, fun s hs => ?_⟩ <;>
        fin_cases s <;> decide)
    (fun i j hij e he => by
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd hij (by decide)
        | (obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
           fin_cases s
           intro s₀ _
           fin_cases s₀
           decide))
    rfl hF_msf
    (show hLift4.Sublist (hRem4.map IndexedEdge.toWeighted) by decide).subperm
    hHL_msf hF
  exact ⟨hconglom, hdepth, hmsf⟩

/-! ## Boundary instance: isolated vertices, zero active conglomerates (`n = 2`) -/

private def tree2Iso (x : Fin 2) : DynamicDJPTree 2 where
  numSteps := 0
  root := x
  edge s := Fin.elim0 s
  wPop s := Fin.elim0 s
  vIn s := Fin.elim0 s
  vOut s := Fin.elim0 s
  edge_weight_le_wPop s := Fin.elim0 s
  ends_match s := Fin.elim0 s
  vIn_mem s := Fin.elim0 s
  vOut_not_mem s := Fin.elim0 s
  djp_future s := Fin.elim0 s

private def r2_0 : PartitionRoundWitness 2 where
  tree := tree2Iso 0
  numVerts := 1
  lift _ := 0
  compLocal := []
  corrEdges := []

private def r2_1 : PartitionRoundWitness 2 where
  tree := tree2Iso 1
  numVerts := 1
  lift _ := 1
  compLocal := []
  corrEdges := []

private def rounds2 : List (PartitionRoundWitness 2) := [r2_0, r2_1]

example :
    0 * 1 ≤ 2 ∧
      IsMinSpanningForest ([] : List (WeightedEdge 2 ℕ)) ([] : List (WeightedEdge 2 ℕ)) := by
  have hconglom := partition_conglom_active_verts_le (n := 2) (nConglom := 2) (n_a := 0)
    (maxsize := 1) (rounds := rounds2) (H_rem := []) (conglomFn := id)
    (lift_a := Fin.elim0)
    (fun x => by fin_cases x <;> [exact ⟨r2_0, by simp [rounds2], by decide⟩;
      exact ⟨r2_1, by simp [rounds2], by decide⟩])
    (fun x y => by fin_cases x <;> fin_cases y <;> decide)
    (fun i => by fin_cases i <;> exact .inl (by decide))
    (fun a => Fin.elim0 a)
    (fun y => Fin.elim0 y)
  have hkr : kruskalEdges ([] : List (WeightedEdge 2 ℕ)) = [] := by
    rw [kruskalEdges, sortEdges_nil]
    rfl
  have h0 : IsMinSpanningForest ([] : List (WeightedEdge 2 ℕ)) [] := by
    have h := kruskalEdges_isMinSpanningForest ([] : List (WeightedEdge 2 ℕ))
    rwa [hkr] at h
  have hmsf := partition_isMinSpanningForest (n := 2) (nConglom := 2)
    (es := []) (rounds := rounds2) (H_rem := []) (conglomFn := id)
    (F_comps := [[], []]) (H_lift := []) (F := [])
    (List.Perm.refl _)
    (fun x => by fin_cases x <;> [exact ⟨r2_0, by simp [rounds2], by decide⟩;
      exact ⟨r2_1, by simp [rounds2], by decide⟩])
    (fun x y => by fin_cases x <;> fin_cases y <;> decide)
    (fun i => by
      fin_cases i <;>
        exact ⟨List.Subperm.refl _, fun x hx hprev => by
          fin_cases x <;> first | exact absurd hx (by decide) | exact absurd hprev (by decide)⟩)
    (fun _ _ he => by simp at he)
    (fun i j _ _ he => by
      obtain ⟨s, _, _⟩ := List.mem_map.mp he
      fin_cases i <;> fin_cases j <;> exact Fin.elim0 s)
    rfl
    (fun i => by
      fin_cases i
      · change IsMinSpanningForest [] []; exact h0
      · change IsMinSpanningForest [] []; exact h0)
    (List.Subperm.refl _)
    (by change IsMinSpanningForest [] []; exact h0)
    (by change IsMinSpanningForest [] []; exact h0)
  exact ⟨hconglom, hmsf⟩

/-! ## Multi-step overlapping multigraph witness (`numSteps = 2`, parallel & duplicate weights) -/

private def tree5M0 : DynamicDJPTree 5 where
  numSteps := 1
  root := 0
  edge _ := ⟨0, 1, 2⟩
  wPop _ := 2
  vIn _ := 0
  vOut _ := 1
  edge_weight_le_wPop s := by fin_cases s; decide
  ends_match s := by fin_cases s; simp
  vIn_mem s := by fin_cases s; decide
  vOut_not_mem s := by fin_cases s; decide
  djp_future s s' hlt := by fin_cases s; fin_cases s'; simp_all

private def tree5M1 : DynamicDJPTree 5 where
  numSteps := 2
  root := 2
  edge s := if s.val = 0 then ⟨2, 3, 2⟩ else ⟨2, 1, 4⟩
  wPop s := if s.val = 0 then 2 else 4
  vIn _ := 2
  vOut s := if s.val = 0 then 3 else 1
  edge_weight_le_wPop s := by fin_cases s <;> decide
  ends_match s := by fin_cases s <;> simp
  vIn_mem s := by fin_cases s <;> decide
  vOut_not_mem s := by fin_cases s <;> decide
  djp_future s s' hlt _ := by
    fin_cases s <;> fin_cases s' <;> first | exact absurd hlt (by decide) | decide

private def tree5Iso (x : Fin 5) : DynamicDJPTree 5 where
  numSteps := 0
  root := x
  edge s := Fin.elim0 s
  wPop s := Fin.elim0 s
  vIn s := Fin.elim0 s
  vOut s := Fin.elim0 s
  edge_weight_le_wPop s := Fin.elim0 s
  ends_match s := Fin.elim0 s
  vIn_mem s := Fin.elim0 s
  vOut_not_mem s := Fin.elim0 s
  djp_future s := Fin.elim0 s

private def r5M_0 : PartitionRoundWitness 5 where
  tree := tree5M0
  numVerts := 2
  lift k := ⟨k.val, by omega⟩
  compLocal := [⟨0, 1, 2, 0⟩]
  corrEdges := [⟨0, 2, 7, 7⟩]

private def r5M_1 : PartitionRoundWitness 5 where
  tree := tree5M1
  numVerts := 3
  lift k := if k.val = 0 then 2 else if k.val = 1 then 3 else 1
  compLocal := [⟨0, 1, 2, 1⟩, ⟨0, 1, 2, 2⟩, ⟨0, 2, 4, 3⟩]
  corrEdges := []

private def r5M_2 : PartitionRoundWitness 5 where
  tree := tree5Iso 4
  numVerts := 1
  lift _ := 4
  compLocal := []
  corrEdges := []

private def rounds5M : List (PartitionRoundWitness 5) := [r5M_0, r5M_1, r5M_2]
private def hRem5M : List (IndexedEdge 5) := [⟨0, 4, 5, 4⟩, ⟨0, 4, 5, 5⟩, ⟨3, 4, 6, 6⟩]
private def es5M : List (IndexedEdge 5) :=
  (rounds5M.flatMap PartitionRoundWitness.compGlobal) ++ hRem5M ++
    (rounds5M.flatMap PartitionRoundWitness.corrEdges)

private def conglomFn5M (x : Fin 5) : Fin 2 := if x.val ≤ 3 then 0 else 1
private def fComps5M : List (List (WeightedEdge 5 ℕ)) :=
  [[⟨0, 1, 2⟩], [⟨2, 3, 2⟩, ⟨2, 1, 4⟩], []]
private def hLift5M : List (WeightedEdge 5 ℕ) := [⟨0, 4, 5⟩]
private def f5M : List (WeightedEdge 5 ℕ) :=
  [⟨0, 1, 2⟩, ⟨2, 3, 2⟩, ⟨2, 1, 4⟩, ⟨0, 4, 5⟩]

example : IsMinSpanningForest (es5M.map IndexedEdge.toWeighted) f5M := by
  have hcov : ∀ x : Fin 5, ∃ r ∈ rounds5M, x ∈ r.verts := fun x => by
    fin_cases x
    · exact ⟨r5M_0, by simp [rounds5M], by decide⟩
    · exact ⟨r5M_0, by simp [rounds5M], by decide⟩
    · exact ⟨r5M_1, by simp [rounds5M], by decide⟩
    · exact ⟨r5M_1, by simp [rounds5M], by decide⟩
    · exact ⟨r5M_2, by simp [rounds5M], by decide⟩
  have hrel : ∀ x y : Fin 5, conglomFn5M x = conglomFn5M y ↔
      (edgePartition (rounds5M.flatMap fun r => r.tree.treeEdges)).rel x y = true :=
    fun x y => by fin_cases x <;> fin_cases y <;> decide
  have hF_msf : ∀ i : Fin rounds5M.length,
      IsMinSpanningForest (rounds5M[i.val].compGlobal.map IndexedEdge.toWeighted)
        (fComps5M[i.val]'(by dsimp [fComps5M, rounds5M] at *; omega)) := by
    intro i
    fin_cases i <;> dsimp only [rounds5M, fComps5M]
    · have hk : kruskalEdges (r5M_0.compGlobal.map IndexedEdge.toWeighted) = [⟨0, 1, 2⟩] := by
        rw [kruskalEdges, show sortEdges (r5M_0.compGlobal.map IndexedEdge.toWeighted) =
          [⟨0, 1, 2⟩] by simp [r5M_0, PartitionRoundWitness.compGlobal, IndexedEdge.toWeighted,
            sortEdges_singleton]]
        rfl
      exact hk ▸ kruskalEdges_isMinSpanningForest _
    · have hk : kruskalEdges (r5M_1.compGlobal.map IndexedEdge.toWeighted) =
          [⟨2, 3, 2⟩, ⟨2, 1, 4⟩] := by
        rw [kruskalEdges, show sortEdges (r5M_1.compGlobal.map IndexedEdge.toWeighted) =
          [⟨2, 3, 2⟩, ⟨2, 3, 2⟩, ⟨2, 1, 4⟩] by
            simp [r5M_1, PartitionRoundWitness.compGlobal, IndexedEdge.toWeighted,
              sortEdges_cons_cons, sortEdges_singleton]]
        rfl
      exact hk ▸ kruskalEdges_isMinSpanningForest _
    · have hk : kruskalEdges (r5M_2.compGlobal.map IndexedEdge.toWeighted) = [] := by
        rw [kruskalEdges, show sortEdges (r5M_2.compGlobal.map IndexedEdge.toWeighted) = [] by
          simp [r5M_2, PartitionRoundWitness.compGlobal, sortEdges_nil]]
        rfl
      exact hk ▸ kruskalEdges_isMinSpanningForest _
  have hHL_msf : IsMinSpanningForest
      (contractEdgeList conglomFn5M (hRem5M.map IndexedEdge.toWeighted))
      (contractEdgeList conglomFn5M hLift5M) := by
    have hk : kruskalEdges (contractEdgeList conglomFn5M (hRem5M.map IndexedEdge.toWeighted)) =
        contractEdgeList conglomFn5M hLift5M := by
      rw [kruskalEdges, show sortEdges
        (contractEdgeList conglomFn5M (hRem5M.map IndexedEdge.toWeighted)) =
          [⟨0, 1, 5⟩, ⟨0, 1, 5⟩, ⟨0, 1, 6⟩] by
            simp [hRem5M, contractEdgeList, contractEdge, IndexedEdge.toWeighted, conglomFn5M,
              sortEdges_cons_cons, sortEdges_singleton]]
      rfl
    exact hk ▸ kruskalEdges_isMinSpanningForest _
  have hF : IsMinSpanningForest
      (fComps5M.flatten ++ hLift5M ++
        (rounds5M.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) f5M := by
    have hk : kruskalEdges (fComps5M.flatten ++ hLift5M ++
        (rounds5M.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) =
        f5M := by
      rw [kruskalEdges, show sortEdges (fComps5M.flatten ++ hLift5M ++
        (rounds5M.flatMap PartitionRoundWitness.corrEdges).map IndexedEdge.toWeighted) =
          [⟨0, 1, 2⟩, ⟨2, 3, 2⟩, ⟨2, 1, 4⟩, ⟨0, 4, 5⟩, ⟨0, 2, 7⟩] by
            simp [fComps5M, hLift5M, rounds5M, r5M_0, r5M_1, r5M_2, IndexedEdge.toWeighted,
              sortEdges_cons_cons, sortEdges_singleton]]
      rfl
    exact hk ▸ kruskalEdges_isMinSpanningForest _
  exact partition_isMinSpanningForest (n := 5) (nConglom := 2)
    (es := es5M.map IndexedEdge.toWeighted) (rounds := rounds5M) (H_rem := hRem5M)
    (conglomFn := conglomFn5M) (F_comps := fComps5M) (H_lift := hLift5M) (F := f5M)
    (List.Perm.refl _) hcov hrel
    (fun i => by
      fin_cases i
      · refine ⟨(show tree5M0.treeEdges.Sublist _ by decide).subperm, fun x hx hprev => ?_⟩
        fin_cases x <;> first | exact absurd hx (by decide) | exact absurd hprev (by decide)
      · refine ⟨(show tree5M1.treeEdges.Sublist _ by decide).subperm, fun x hx hprev => ?_⟩
        refine ⟨by decide, ?_⟩
        fin_cases x <;> first | rfl | exact absurd hx (by decide) | exact absurd hprev (by decide)
      · exact ⟨List.Subperm.refl _, fun x hx hprev => by
          fin_cases x <;> first | exact absurd hx (by decide) | exact absurd hprev (by decide)⟩)
    (fun i e he => by
      fin_cases i <;>
        simp only [hRem5M, List.mem_cons, List.not_mem_nil, or_false] at he <;>
        rcases he with rfl | rfl | rfl <;>
        refine ⟨by decide, fun s hs => ?_⟩ <;>
        fin_cases s <;> decide)
    (fun i j hij e he => by
      fin_cases i <;> fin_cases j <;>
        first
        | exact absurd hij (by decide)
        | (obtain ⟨s, _, rfl⟩ := List.mem_map.mp he
           fin_cases s <;> intro s₀ _ <;> fin_cases s₀ <;> decide))
    rfl hF_msf
    (show hLift5M.Sublist (hRem5M.map IndexedEdge.toWeighted) by decide).subperm
    hHL_msf hF

/-! ## Boundary instance: inactive `< maxsize` isolated component (`n = 5`, 3rd `hstop` branch) -/

private def r5B_1 : PartitionRoundWitness 5 where
  tree := tree5Iso 2
  numVerts := 1
  lift _ := 2
  compLocal := []
  corrEdges := []

private def rounds5B : List (PartitionRoundWitness 5) := [r5_0, r5B_1, r5_2]
private def hRem5B : List (IndexedEdge 5) := [⟨1, 3, 7, 0⟩]
private def conglomFn5B (x : Fin 5) : Fin 3 :=
  if x.val ≤ 1 then 0 else if x.val = 2 then 1 else 2

example : 2 * 2 ≤ 5 := by
  refine partition_conglom_active_verts_le (n := 5) (nConglom := 3) (n_a := 2) (maxsize := 2)
    (rounds := rounds5B) (H_rem := hRem5B) (conglomFn := conglomFn5B)
    (lift_a := fun y => if y.val = 0 then 0 else 2)
    (fun x => by
      fin_cases x
      · exact ⟨r5_0, by simp [rounds5B], by decide⟩
      · exact ⟨r5_0, by simp [rounds5B], by decide⟩
      · exact ⟨r5B_1, by simp [rounds5B], by decide⟩
      · exact ⟨r5_2, by simp [rounds5B], by decide⟩
      · exact ⟨r5_2, by simp [rounds5B], by decide⟩)
    (fun x y => by fin_cases x <;> fin_cases y <;> decide)
    (fun i => by
      fin_cases i
      · exact .inl (by decide)
      · exact .inr (.inr ⟨fun j hne => by
          fin_cases j <;> first | exact absurd rfl hne | decide,
          fun e he => by
            simp only [hRem5B, List.mem_cons, List.not_mem_nil, or_false] at he
            subst he; decide⟩)
      · exact .inl (by decide))
    (fun a b h => by fin_cases a <;> fin_cases b <;> cases h <;> rfl)
    (fun y => by fin_cases y <;> exact ⟨⟨1, 3, 7, 0⟩, by simp [hRem5B], by decide⟩)

end CslibFrontierTests.Algorithms.WordRAM.MinimumSpanningForest.PartitionBridges
