/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Lean.Kruskal.SimpleGraph
import CslibFrontier.Algorithms.WordRAM.Kruskal

meta import CslibFrontier.Algorithms.Lean.Kruskal.SimpleGraph
meta import CslibFrontier.Algorithms.WordRAM.Kruskal
meta import CslibFrontier.Computability.WordRAM.Structured.FastEval

/-!
# Worked Kruskal Minimum Spanning Forest, Tree, and Word-RAM Examples

These kernel-checked examples (using no `native_decide`) exercise:

1. Empty-vertex (`n = 0`), singleton (`n = 1`), and negative-weight self-loop boundary cases,
   alongside `encodeEdges_injective`, `inputFits_encode`, and `kruskalCode.eval`.
2. A 6-vertex disconnected multigraph with negative `ℤ` weights, parallel edges, a negative-weight
   self-loop `(2, 2, -10)` (rejected despite having minimum weight), and duplicate weights — showing
   both `IsMinSpanningForest` and a concrete non-uniqueness witness (`¬F₁.Perm F₂`) when edge
   weights are not pairwise distinct, plus negative witnesses (`¬IsAcyclic`, `¬IsSpanningForest`,
   `¬IsMinSpanningForest`) — together with a `ℕ`-weight Word-RAM counterpart verifying stable
   tie-breaking and instruction bounds.
3. Distinct-weight uniqueness (`perm_kruskalEdges_of_isMinSpanningTree_of_nodup_weights`) and the
   end-to-end Word-RAM `ExecutesList` running-time bound (`kruskalProgram_spec`) on a connected
   4-vertex graph.
4. End-to-end `SimpleGraph` bridge (`graphEdges`, `kruskalGraph`, `kruskalGraph_isTree`,
   `sum_edgeFinset_kruskalGraph_le_of_isTree`, `eq_toSimpleGraph_kruskalGraph_of_isTree_of_injOn`,
   and `kruskalProgram_graphEdges_spec`) on `K₄` with distinct undirected edge weights.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

namespace CslibFrontierTests.Kruskal

open Cslib.WordRAM
open Cslib.Algorithms.Lean.Kruskal
open Cslib.Algorithms.WordRAM.Kruskal
open Cslib.DataStructure.DisjointSet

private meta def evalKruskal {n : ℕ} (w : ℕ) (es : List (WeightedEdge n ℕ)) :
    Option (List ℕ × ℕ) :=
  (kruskalCode.eval w 4096 (Data.init (encode es))).map fun (x, t) =>
    (outputList x.mem (x.regs Reg.out), t + 1)

/-! ### 1. Boundary cases (`n = 0`, `n = 1`, self-loops, encoding admissibility) -/

example :
    kruskalEdges ([] : List (WeightedEdge 0 ℕ)) = [] ∧
      kruskalEdges ([⟨0, 0, (-10 : ℤ)⟩] : List (WeightedEdge 1 ℤ)) = [] ∧
      ¬IsAcyclic ([⟨0, 0, (-10 : ℤ)⟩] : List (WeightedEdge 1 ℤ)) ∧
      Function.Injective (encodeEdges (n := 4)) ∧
      InputFits 8 (encode ([⟨0, 0, 5⟩] : List (WeightedEdge 1 ℕ))) := by
  refine ⟨by simp [kruskalEdges], by simp [kruskalEdges], by decide,
    encodeEdges_injective 4,
    inputFits_encode [⟨0, 0, 5⟩] (by decide)
      (by intro e he; rw [List.mem_singleton] at he; subst he; decide)⟩

#guard (evalKruskal 8 ([] : List (WeightedEdge 0 ℕ))) == some ([], 34)
#guard
  match evalKruskal 8 ([⟨0, 0, 5⟩] : List (WeightedEdge 1 ℕ)) with
  | some (out, steps) =>
    out == [] && steps ≤ 52 * 1 * Nat.clog 2 1 + 16 * 1 * Nat.log 2 1 + 69 + 7 + 34
  | none => false

/-! ### 2. Disconnected multigraph with negative & duplicate weights (`Fin 6`) -/

/-- Six-vertex multigraph with components `{0, 1, 2}`, `{3, 4}`, and `{5}`:
- negative-weight self-loop `(2, 2, -10)` (must be rejected despite smallest weight),
- negative bridge `(1, 2, -4)`,
- tied cycle edges `(0, 1, 2)` and `(0, 2, 2)`,
- parallel heavier edge `(0, 1, 7)`,
- component `{3, 4}` with parallel edges `(3, 4, -1)` and `(4, 3, 5)`. -/
def disconnectedMulti : List (WeightedEdge 6 ℤ) :=
  [ ⟨0, 1, 7⟩
  , ⟨2, 2, -10⟩
  , ⟨0, 2, 2⟩
  , ⟨3, 4, -1⟩
  , ⟨1, 2, -4⟩
  , ⟨4, 3, 5⟩
  , ⟨0, 1, 2⟩ ]

theorem sortEdges_disconnectedMulti :
    sortEdges disconnectedMulti =
      [ ⟨2, 2, -10⟩
      , ⟨1, 2, -4⟩
      , ⟨3, 4, -1⟩
      , ⟨0, 2, 2⟩
      , ⟨0, 1, 2⟩
      , ⟨4, 3, 5⟩
      , ⟨0, 1, 7⟩ ] := by
  simp [disconnectedMulti, sortEdges_cons_cons]

theorem kruskalEdges_disconnectedMulti :
    kruskalEdges disconnectedMulti = [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 2, 2⟩] := by
  rw [kruskalEdges, sortEdges_disconnectedMulti]
  rfl

-- Kruskal rejects `(2, 2, -10)`, `(0, 1, 2)` (closing triangle `{0, 1, 2}` after `(1, 2, -4)` and
-- `(0, 2, 2)`), `(4, 3, 5)`, and `(0, 1, 7)`, achieving minimum total weight `-4 + -1 + 2 = -3`
-- across `3` connected components.
example :
    kruskalEdges disconnectedMulti = [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 2, 2⟩] ∧
      totalWeight (kruskalEdges disconnectedMulti) = -3 ∧
      IsMinSpanningForest disconnectedMulti (kruskalEdges disconnectedMulti) := by
  refine ⟨kruskalEdges_disconnectedMulti, ?_,
    kruskalEdges_isMinSpanningForest disconnectedMulti⟩
  rw [kruskalEdges_disconnectedMulti]
  simp

/-- Nonnegative-weight counterpart (`+ 10` shift) exercising Word-RAM stable merge sort on tied
weights (`(0, 2, 12)` before `(0, 1, 12)`), self-loops (`(2, 2, 0)`), and parallel edges. -/
def disconnectedMultiNat : List (WeightedEdge 6 ℕ) :=
  [ ⟨0, 1, 17⟩
  , ⟨2, 2, 0⟩
  , ⟨0, 2, 12⟩
  , ⟨3, 4, 9⟩
  , ⟨1, 2, 6⟩
  , ⟨4, 3, 15⟩
  , ⟨0, 1, 12⟩ ]

#guard
  match evalKruskal 8 disconnectedMultiNat with
  | some (out, steps) =>
    out == encodeEdges (kruskalEdges disconnectedMultiNat) &&
      out == [1, 2, 6, 3, 4, 9, 0, 2, 12] &&
      steps ≤ 52 * 7 * Nat.clog 2 7 + 16 * 7 * Nat.log 2 6 + 69 * 7 + 7 * 6 + 34
  | none => false

/-- Alternate minimum spanning forest choosing `(0, 1, 2)` instead of the tied edge `(0, 2, 2)`. -/
def altMinForest : List (WeightedEdge 6 ℤ) :=
  [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 1, 2⟩]

/-- Suboptimal spanning forest choosing `(0, 1, 7)` (total weight `2 > -3`). -/
def suboptimalForest : List (WeightedEdge 6 ℤ) :=
  [⟨1, 2, -4⟩, ⟨3, 4, -1⟩, ⟨0, 1, 7⟩]

/-- Non-spanning acyclic subset omitting `(3, 4, -1)` (`4` components instead of `3`). -/
def nonSpanningForest : List (WeightedEdge 6 ℤ) :=
  [⟨1, 2, -4⟩, ⟨0, 2, 2⟩]

-- Both `kruskalEdges disconnectedMulti` and `altMinForest` are `IsMinSpanningForest`, yet they are
-- not permutations (`¬altMinForest.Perm (kruskalEdges disconnectedMulti)`), showing necessity of
-- the distinct-weights hypothesis in `perm_kruskalEdges_of_isMinSpanningForest_of_nodup_weights`.
example :
    IsMinSpanningForest disconnectedMulti altMinForest ∧
      ¬altMinForest.Perm (kruskalEdges disconnectedMulti) ∧
      IsSpanningForest disconnectedMulti suboptimalForest ∧
      ¬IsMinSpanningForest disconnectedMulti suboptimalForest ∧
      IsAcyclic nonSpanningForest ∧
      ¬IsSpanningForest disconnectedMulti nonSpanningForest := by
  have hk_eq := kruskalEdges_disconnectedMulti
  have halt_sf : IsSpanningForest disconnectedMulti altMinForest := by
    refine ⟨?_, by decide, by decide⟩
    exact ⟨[⟨3, 4, -1⟩, ⟨1, 2, -4⟩, ⟨0, 1, 2⟩], by decide, by decide⟩
  have hsub_sf : IsSpanningForest disconnectedMulti suboptimalForest := by
    refine ⟨?_, by decide, by decide⟩
    exact ⟨[⟨0, 1, 7⟩, ⟨3, 4, -1⟩, ⟨1, 2, -4⟩], by decide, by decide⟩
  refine ⟨⟨halt_sf, ?_⟩, ?_, hsub_sf, ?_, by decide, ?_⟩
  · intro F' hF'
    have hmin := (kruskalEdges_isMinSpanningForest disconnectedMulti).2 F' hF'
    have heq : totalWeight altMinForest = totalWeight (kruskalEdges disconnectedMulti) := by
      rw [hk_eq]
      simp [altMinForest]
    exact heq.trans_le hmin
  · rw [hk_eq]
    decide
  · intro hmin
    have hle := hmin.2 (kruskalEdges disconnectedMulti)
      (kruskalEdges_isSpanningForest disconnectedMulti)
    rw [hk_eq] at hle
    simp [suboptimalForest] at hle
  · intro hsf
    have hcomp := congrArg Partition.numComponents hsf.2.2
    revert hcomp
    decide

/-! ### 3. Connected graph with distinct weights & Word-RAM `ExecutesList` bound (`Fin 4`) -/

def diamondEdges : List (WeightedEdge 4 ℕ) :=
  [ ⟨0, 3, 9⟩
  , ⟨0, 1, 1⟩
  , ⟨1, 2, 4⟩
  , ⟨0, 2, 3⟩
  , ⟨2, 3, 2⟩ ]

#guard
  match evalKruskal 8 diamondEdges with
  | some (out, steps) =>
    out == [0, 1, 1, 2, 3, 2, 0, 2, 3] &&
      steps ≤ 52 * 5 * Nat.clog 2 5 + 16 * 5 * Nat.log 2 4 + 69 * 5 + 7 * 4 + 34
  | none => false

example :
    kruskalEdges diamondEdges = [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩] ∧
      totalWeight (kruskalEdges diamondEdges) = 6 ∧
      IsMinSpanningTree diamondEdges (kruskalEdges diamondEdges) ∧
      (∀ T, IsMinSpanningTree diamondEdges T → T.Perm [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩]) ∧
      ∃ steps : ℕ,
        ExecutesList 8 kruskalProgram (.init (encode diamondEdges))
          [0, 1, 1, 2, 3, 2, 0, 2, 3] steps ∧
        steps ≤ 52 * diamondEdges.length * Nat.clog 2 diamondEdges.length +
          16 * diamondEdges.length * Nat.log 2 4 + 69 * diamondEdges.length + 7 * 4 + 34 := by
  have hconn : (edgePartition diamondEdges).numComponents = 1 := by decide
  have hnodup : (diamondEdges.map WeightedEdge.weight).Nodup := by decide
  have hsort : sortEdges diamondEdges =
      [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩, ⟨1, 2, 4⟩, ⟨0, 3, 9⟩] := by
    simp [diamondEdges, sortEdges_cons_cons]
  have hk : kruskalEdges diamondEdges = [⟨0, 1, 1⟩, ⟨2, 3, 2⟩, ⟨0, 2, 3⟩] := by
    rw [kruskalEdges, hsort]
    rfl
  obtain ⟨steps, hex, hst, _⟩ := kruskalProgram_spec (w := 8) diamondEdges (by decide)
  rw [hk] at hex
  refine ⟨hk, ?_, kruskalEdges_isMinSpanningTree hconn, ?_, ⟨steps, hex, hst⟩⟩
  · rw [hk]
    simp
  · intro T hT
    rw [← hk]
    exact perm_kruskalEdges_of_isMinSpanningTree_of_nodup_weights hconn hnodup hT

/-! ### 4. Weighted `SimpleGraph (Fin 4)` bridge on `K₄` -/

/-- Complete graph `K₄` with kernel-reducible `DecidableRel` adjacency. -/
def k4Graph : SimpleGraph (Fin 4) where
  Adj u v := u ≠ v
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨fun _ h => h rfl⟩

instance : DecidableRel k4Graph.Adj := fun u v => inferInstanceAs (Decidable (u ≠ v))

theorem k4Graph_eq_top : k4Graph = ⊤ := by
  ext u v
  simp [k4Graph]

/-- Injective symmetric edge weight on `Sym2 (Fin 4)` via kernel-reducible `Quot.lift`:
`2 ^ u + 2 ^ v` gives distinct values for all unordered pairs `{u, v}` with `u ≠ v`
(`{0,1} ↦ 3`, `{0,2} ↦ 5`, `{1,2} ↦ 6`, `{0,3} ↦ 9`, `{1,3} ↦ 10`, `{2,3} ↦ 12`). -/
def k4Weight : Sym2 (Fin 4) → ℕ :=
  Quot.lift (fun p : Fin 4 × Fin 4 => 2 ^ p.1.1 + 2 ^ p.2.1) fun a b h => by
    cases h
    · rfl
    · exact Nat.add_comm _ _

theorem k4Weight_injOn : Set.InjOn k4Weight k4Graph.edgeSet := by
  intro z₁ hz₁ z₂ hz₂ hw
  revert z₁ z₂
  decide

#guard
  match evalKruskal 8 (graphEdges k4Graph k4Weight) with
  | some (out, steps) =>
    out == [0, 1, 3, 0, 2, 5, 0, 3, 9] &&
      steps ≤ 52 * 6 * Nat.clog 2 6 + 16 * 6 * Nat.log 2 4 + 69 * 6 + 7 * 4 + 34
  | none => false

-- On `K₄`, Kruskal selects the star `{0, 1}` (weight 3), `{0, 2}` (weight 5), `{0, 3}` (weight 9)
-- of total weight `17` (avoiding `{1, 2}` of weight 6 because `1` and `2` are already connected
-- through `0`), and `toSimpleGraph (kruskalGraph k4Graph k4Weight)` is the unique minimum spanning
-- tree of `K₄`!
example :
    (graphEdges k4Graph k4Weight).length = 6 ∧
      kruskalGraph k4Graph k4Weight =
        [⟨0, 1, 3⟩, ⟨0, 2, 5⟩, ⟨0, 3, 9⟩] ∧
      (toSimpleGraph (kruskalGraph k4Graph k4Weight)).IsTree ∧
      k4Graph.IsMST k4Weight (toSimpleGraph (kruskalGraph k4Graph k4Weight)) ∧
      (∀ T : SimpleGraph (Fin 4),
        k4Graph.IsMST k4Weight T ↔ T = toSimpleGraph (kruskalGraph k4Graph k4Weight)) ∧
      (∑ z ∈ (toSimpleGraph (kruskalGraph k4Graph k4Weight)).edgeFinset,
          k4Weight z) = 17 ∧
      (∀ (T : SimpleGraph (Fin 4)) [Fintype T.edgeSet],
        T.IsTree →
        17 ≤ ∑ z ∈ T.edgeFinset, k4Weight z) ∧
      (∀ (T : SimpleGraph (Fin 4)) [Fintype T.edgeSet],
        T.IsTree →
        (∑ z ∈ T.edgeFinset, k4Weight z) ≤ 17 →
        T = toSimpleGraph (kruskalGraph k4Graph k4Weight)) ∧
      ∃ steps : ℕ,
        ExecutesList 8 kruskalProgram (.init (encode (graphEdges k4Graph k4Weight)))
          [0, 1, 3, 0, 2, 5, 0, 3, 9] steps ∧
        steps ≤ 52 * 6 * Nat.clog 2 6 + 16 * 6 * Nat.log 2 4 + 69 * 6 + 7 * 4 + 34 := by
  have hconn : k4Graph.Connected := by
    rw [k4Graph_eq_top]
    exact SimpleGraph.connected_top
  have hge : graphEdges k4Graph k4Weight =
      [⟨0, 1, 3⟩, ⟨0, 2, 5⟩, ⟨0, 3, 9⟩, ⟨1, 2, 6⟩, ⟨1, 3, 10⟩, ⟨2, 3, 12⟩] := rfl
  have hsort : sortEdges (graphEdges k4Graph k4Weight) =
      [⟨0, 1, 3⟩, ⟨0, 2, 5⟩, ⟨1, 2, 6⟩, ⟨0, 3, 9⟩, ⟨1, 3, 10⟩, ⟨2, 3, 12⟩] := by
    rw [hge]
    simp [sortEdges_cons_cons]
  have hk : kruskalGraph k4Graph k4Weight = [⟨0, 1, 3⟩, ⟨0, 2, 5⟩, ⟨0, 3, 9⟩] := by
    rw [kruskalGraph, kruskalEdges, hsort]
    rfl
  have hsum :
      (∑ z ∈ (toSimpleGraph (kruskalGraph k4Graph k4Weight)).edgeFinset,
        k4Weight z) = 17 := by
    rw [sum_edgeFinset_toSimpleGraph_kruskalGraph, hk]
    rfl
  have hcard : k4Graph.edgeFinset.card = 6 := by
    rw [← length_graphEdges k4Graph k4Weight]
    rfl
  obtain ⟨steps, hex, hst, _⟩ :=
    kruskalProgram_graphEdges_spec (w := 8) k4Graph k4Weight (by rw [hcard]; decide)
  rw [hk] at hex
  rw [hcard] at hst
  refine ⟨rfl, hk, (kruskalGraph_isTree hconn k4Weight).1,
    kruskalGraph_isMST hconn k4Weight,
    fun T => isMST_iff_eq_toSimpleGraph_kruskalGraph_of_injOn hconn k4Weight k4Weight_injOn,
    hsum, ?_, ?_, ⟨steps, hex, hst⟩⟩
  · intro T _ hT
    have hle : T ≤ k4Graph := by rw [k4Graph_eq_top]; exact le_top
    rw [← hsum]
    exact sum_edgeFinset_kruskalGraph_le_of_isTree hconn k4Weight T hle hT
  · intro T _ hT hopt
    have hle : T ≤ k4Graph := by rw [k4Graph_eq_top]; exact le_top
    rw [← hsum] at hopt
    exact eq_toSimpleGraph_kruskalGraph_of_isTree_of_injOn hconn k4Weight k4Weight_injOn hle hT hopt

end CslibFrontierTests.Kruskal
