/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.IndependentSetFPT
import CslibFrontier.Foundations.Data.List.FoldMax
import Mathlib.Data.List.OfFn

/-!
# Serialized MWIS instance model and FPT word/step bounds

This module defines the flat word-serializable maximum-weight independent set instance bundle
`MWISInstance`, the bag serialization `encodeBag`, vertex weight/adjacency accessors, space and
step envelopes (`wordBound`, `stepBound`, `mwisFPTBound`), compilation `MWISInstance.ofRooted`
from a `RootedTreeDecomposition`, and width-`k` bounds `maxBagLen_ofRooted_le` and
`stepBound_ofRooted_le`.

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.encodeBag`: length-prefixed bag word list.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance`: flat word-serializable instance bundle
  with `MWISInstance.wt`, `MWISInstance.adj`, `MWISInstance.encode`, `MWISInstance.maxBagLen`,
  `MWISInstance.maxWeight`, `MWISInstance.wordBound`, `MWISInstance.stepBound`, and
  `MWISInstance.ofRooted`.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.mwisFPTBound`: closed-form width-`k` step bound
  `6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))`.

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.maxBagLen_ofRooted_le`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.MWISInstance.stepBound_ofRooted_le`: width-`k`
  bounds on `maxBagLen` and `stepBound`.
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open SimpleGraph
open Cslib.Algorithms.Lean.TreeDecomposition

/-- Length-prefixed word serialization `[B.length] ++ B` of an ordered bag `B`. -/
@[expose] def encodeBag (B : List ℕ) : List ℕ :=
  B.length :: B

/-- Word-encoded instance of maximum-weight independent set over a rooted tree decomposition on
`numNodes + 1` nodes (`0` is the root) and `numVerts` graph vertices `0, …, numVerts - 1`. -/
structure MWISInstance where
  /-- Number of graph vertices `m`. -/
  numVerts : ℕ
  /-- Parameter `n` such that the decomposition has `n + 1` nodes `0, …, n`. -/
  numNodes : ℕ
  /-- Vertex weights `weights[0 .. m - 1]`. -/
  weights : List ℕ
  /-- Flattened row-major `m × m` adjacency indicators (`0` non-adjacent, nonzero adjacent). -/
  adjMatrix : List ℕ
  /-- Parent node indices `parents[0 .. n]`. -/
  parents : List ℕ
  /-- Ordered vertex lists `bags[0 .. n]`. -/
  bags : List (List ℕ)
  /-- `weights` has length `numVerts`. -/
  weights_len : weights.length = numVerts
  /-- `adjMatrix` has length `numVerts * numVerts`. -/
  adjMatrix_len : adjMatrix.length = numVerts * numVerts
  /-- `parents` has length `numNodes + 1`. -/
  parents_len : parents.length = numNodes + 1
  /-- `bags` has length `numNodes + 1`. -/
  bags_len : bags.length = numNodes + 1
  /-- Every nonroot node `1 ≤ i ≤ numNodes` has parent strictly preceding `i`. -/
  parents_lt : ∀ i : Fin parents.length, 1 ≤ i.val → parents[i] < i.val
  /-- Every vertex in every bag is `< numVerts`. -/
  bags_lt : ∀ B ∈ bags, ∀ v ∈ B, v < numVerts

namespace MWISInstance

/-- Weight lookup `weights.getD u 0` of vertex `u`. -/
@[expose] def wt (inst : MWISInstance) (u : ℕ) : ℕ :=
  inst.weights.getD u 0

/-- Adjacency indicator `adjMatrix[u * numVerts + v] ≠ 0`. -/
@[expose] def adj (inst : MWISInstance) (u v : ℕ) : Bool :=
  decide (inst.adjMatrix.getD (u * inst.numVerts + v) 0 ≠ 0)

/-- Flat word-list encoding `[numVerts, numNodes] ++ weights ++ adjMatrix ++ parents ++
bags.flatMap encodeBag`. -/
@[expose] def encode (inst : MWISInstance) : List ℕ :=
  [inst.numVerts, inst.numNodes] ++
    inst.weights ++ inst.adjMatrix ++ inst.parents ++ inst.bags.flatMap encodeBag

/-- Maximum bag length across `inst.bags` (`≤ k + 1` when `R.width ≤ k`). -/
@[expose] def maxBagLen (inst : MWISInstance) : ℕ :=
  (inst.bags.map List.length).foldl max 0

/-- Maximum vertex weight across `inst.weights` (`0` if `numVerts = 0`). -/
@[expose] def maxWeight (inst : MWISInstance) : ℕ :=
  inst.weights.foldl max 0

/-- Word-value upper bound covering literal constants, peak memory frontier across initial table
allocation and all `numNodes` scratch `best` allocations, `2 ^ maxBagLen`, and maximum DP table
value `(numNodes + 1) * maxBagLen * maxWeight`. -/
@[expose] def wordBound (inst : MWISInstance) : ℕ :=
  let n := inst.numNodes
  let M := inst.maxBagLen
  8 +
    (inst.encode.length + 1 + 4 * (n + 1) + (2 * n + 1) * 2 ^ M) +
    (n + 1) * M * inst.maxWeight

/-- Upper bound on the oracle memory cost (`memoryCost`) of the Word-RAM MWIS program on `inst`. -/
@[expose] def stepBound (inst : MWISInstance) : ℕ :=
  let n := inst.numNodes
  let M := inst.maxBagLen
  6 + (n + 1) * (2 ^ M * (5 * M ^ 2 + 6 * M + 32))

/-- Compile a graph `G : SimpleGraph V` (`e : V ≃ Fin m`), rooted tree decomposition
`R : G.RootedTreeDecomposition n`, vertex weights `w : V → ℕ`, and bag lists
`L : Fin (n + 1) → List V` into a flat `MWISInstance`. -/
@[expose] def ofRooted {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj]
    {m n : ℕ} (e : V ≃ Fin m) (R : G.RootedTreeDecomposition n) (w : V → ℕ)
    (L : Fin (n + 1) → List V) : MWISInstance where
  numVerts := m
  numNodes := n
  weights := List.ofFn fun u : Fin m => w (e.symm u)
  adjMatrix := List.ofFn fun idx : Fin (m * m) =>
    have hm : 0 < m := Nat.pos_of_ne_zero fun h0 => by subst h0; exact Fin.elim0 idx
    if G.Adj (e.symm ⟨idx.val / m, Nat.div_lt_of_lt_mul idx.isLt⟩)
        (e.symm ⟨idx.val % m, Nat.mod_lt _ hm⟩) then 1 else 0
  parents := List.ofFn fun i : Fin (n + 1) => (R.parent i).val
  bags := List.ofFn fun i : Fin (n + 1) => (L i).map fun v => (e v).val
  weights_len := List.length_ofFn
  adjMatrix_len := List.length_ofFn
  parents_len := List.length_ofFn
  bags_len := List.length_ofFn
  parents_lt := fun idx h1 => by
    have hi : idx.val < n + 1 := by simpa only [List.length_ofFn] using idx.isLt
    have hne : (⟨idx.val, hi⟩ : Fin (n + 1)) ≠ 0 := fun h => by
      have := congrArg Fin.val h
      simp only [Fin.val_zero] at this
      omega
    have hget : (List.ofFn fun i : Fin (n + 1) => (R.parent i).val)[idx] =
        (R.parent ⟨idx.val, hi⟩).val := by
      simp only [Fin.getElem_fin, List.getElem_ofFn]
    rw [hget]
    exact R.parent_lt ⟨idx.val, hi⟩ hne
  bags_lt := fun B hB v hv => by
    rw [List.mem_ofFn] at hB
    obtain ⟨i, rfl⟩ := hB
    rw [List.mem_map] at hv
    obtain ⟨x, _, rfl⟩ := hv
    exact (e x).isLt

end MWISInstance

/-- Closed-form FPT step bound `6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))`
for rooted tree decompositions on `n + 1` nodes of width at most `k`. -/
@[expose] def mwisFPTBound (n k : ℕ) : ℕ :=
  6 + (n + 1) * (2 ^ (k + 1) * (5 * (k + 1) ^ 2 + 6 * (k + 1) + 32))

/-- Under `IsBagOrder R L` and `R.width ≤ k`, every bag has length at most `k + 1`. -/
theorem MWISInstance.maxBagLen_ofRooted_le {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} (e : V ≃ Fin m)
    (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) {k : ℕ} (hk : R.width ≤ k) :
    (MWISInstance.ofRooted e R w L).maxBagLen ≤ k + 1 := by
  refine List.foldl_max_le (Nat.zero_le _) fun len hlen => ?_
  rw [List.mem_map] at hlen
  obtain ⟨B, hB, rfl⟩ := hlen
  dsimp only [MWISInstance.ofRooted] at hB
  rw [List.mem_ofFn] at hB
  obtain ⟨i, rfl⟩ := hB
  rw [List.length_map, ← List.toFinset_card_of_nodup (hL i).1, (hL i).2]
  exact R.width_le_iff.1 hk i

/-- Under `IsBagOrder R L` and `R.width ≤ k`, `stepBound` is bounded by `mwisFPTBound n k`. -/
theorem MWISInstance.stepBound_ofRooted_le {V : Type*} {G : SimpleGraph V}
    [DecidableEq V] [DecidableRel G.Adj] {m n : ℕ} (e : V ≃ Fin m)
    (R : G.RootedTreeDecomposition n) (w : V → ℕ) {L : Fin (n + 1) → List V}
    (hL : IsBagOrder R L) {k : ℕ} (hk : R.width ≤ k) :
    (MWISInstance.ofRooted e R w L).stepBound ≤ mwisFPTBound n k := by
  have hM := MWISInstance.maxBagLen_ofRooted_le e R w hL hk
  have hn : (MWISInstance.ofRooted e R w L).numNodes = n := rfl
  unfold MWISInstance.stepBound mwisFPTBound
  rw [hn]
  dsimp only
  have hpow : 2 ^ (MWISInstance.ofRooted e R w L).maxBagLen ≤ 2 ^ (k + 1) :=
    Nat.pow_le_pow_right (by decide) hM
  have hpoly :
      5 * (MWISInstance.ofRooted e R w L).maxBagLen ^ 2 +
          6 * (MWISInstance.ofRooted e R w L).maxBagLen + 32 ≤
        5 * (k + 1) ^ 2 + 6 * (k + 1) + 32 :=
    Nat.add_le_add_right
      (Nat.add_le_add (Nat.mul_le_mul_left 5 (Nat.pow_le_pow_left hM 2))
        (Nat.mul_le_mul_left 6 hM)) 32
  exact Nat.add_le_add_left (Nat.mul_le_mul_left (n + 1) (Nat.mul_le_mul hpow hpoly)) 6

end Cslib.Algorithms.WordRAM.TreeDecomposition
