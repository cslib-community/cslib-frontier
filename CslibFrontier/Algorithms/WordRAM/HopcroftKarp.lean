/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Hopcroft–Karp maximum bipartite matching on the word RAM

This file implements and proves machine-level running-time bounds on the standard-basis word RAM
(`Basis.standard`) for:

1. **Sparse Hopcroft–Karp (`O((m + r + |E|) √ν)`):** given a bipartite graph on `Fin m × Fin r`
   represented in compressed sparse row (CSR) format (`SparseInstance`), `coreCode` alternates
   queue-based breadth-first layering (`O(m + r + |E|)` instructions per round) and iterative
   explicit-stack depth-first augmentation (`O(m + r + |E|)` instructions per phase), matching the
   pure specification `Cslib.Algorithms.Lean.MaxFlow.hopcroftKarp` (`IsMaxMatching`, at most
   `2⌊√ν⌋` augmenting phases by `IsPhaseRun.le_two_mul_sqrt`). This yields end-to-end `State.init`
   programs for maximum matching (`sparseMatchingProgram`), matching cardinality
   (`sparseCardProgram`), and balanced perfect-matching decision (`sparsePerfectProgram`).
2. **Dense Hopcroft–Karp (`O((m + r)² √ν)`):** given an `m × r` `0/1` adjacency matrix
   (`DenseInstance`), converts the input matrix into exact CSR neighbour lists (`exactBipAdj`) in
   `O(m + m r)` instructions (`buildCSRCode` / `matrixSetupCode`) and invokes `coreCode`, agreeing
   with `hopcroftKarpDense`.

The `O(n^{5/2})` Dilworth minimum chain cover and maximum antichain endpoints built on top of
`matrixSetupCode` and `coreCode` live in `CslibFrontier.Algorithms.WordRAM.ChainCover`.

## Main definitions

* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance`: sparse CSR and dense matrix problem
  instances with their word encodings, word-width envelopes, and outputs
  (`SparseInstance.matchingPairs`, `DenseInstance.matchingPairs`, `matchingWords`).
* `Cslib.Algorithms.WordRAM.HopcroftKarp.CSRMem`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.BaseRegs`: in-memory CSR layout and base-register frame
  for `coreCode`.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.coreCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.buildCSRCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.matrixSetupCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseMatchingProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseCardProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparsePerfectProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseMatchingProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseCardProgram`: word-RAM subroutines and programs.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.coreTime`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseTime`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseTimeSqrtMin`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseTime`: instruction bounds.

## Main results

* `Cslib.Algorithms.WordRAM.HopcroftKarp.core_exec`: in-memory CSR execution of Hopcroft–Karp in
  `O((m + r + |E|) (√ν + 1))` instructions.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.exec_buildCSRCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.exec_matrixSetupCode`: dense/square `0/1`-matrix to CSR
  conversion in `O(m + m r)` instructions.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance.getElem_matchingWords_even`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance.getElem_matchingWords_odd`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance.isMaxMatching_matchingPairs`: flat-word
  pair indexing and dense maximum-matching optimality.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.executesList_sparseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.computesListInTime_sparseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.executes_sparseCard`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.decidesInTime_sparsePerfect`: sparse `O((m + r + |E|) √ν)`
  endpoints.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.executesList_denseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.computesListInTime_denseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.executes_denseCard`: dense `O((m + r)² √ν)` endpoints.

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest, and C. Stein,
  *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.Algorithms.WordRAM.HopcroftKarp

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow

/-! ## Problem instances and encodings -/

/-- A bipartite graph instance on `Fin m × Fin r` represented by left-vertex adjacency lists `adj`,
encoded in compressed sparse row (CSR) format. -/
structure SparseInstance where
  /-- Number of left vertices. -/
  m : ℕ
  /-- Number of right vertices. -/
  r : ℕ
  /-- Candidate right-neighbour list of each left vertex `u : Fin m`. -/
  adj : Fin m → List (Fin r)

namespace SparseInstance

/-- Bipartite edge indicator induced by `inst.adj`. -/
@[expose] def graph (inst : SparseInstance) : Fin inst.m × Fin inst.r → Bool :=
  fun p => decide (p.2 ∈ inst.adj p.1)

theorem bipAdjValid_graph (inst : SparseInstance) : BipAdjValid inst.graph inst.adj :=
  fun _ _ h => of_decide_eq_true h

/-- Starting CSR offset of left vertex `u` (`0 ≤ u ≤ m`). -/
@[expose] def offset (inst : SparseInstance) (u : ℕ) : ℕ :=
  (((List.finRange inst.m).take u).map fun i => (inst.adj i).length).sum

/-- Total number of CSR edge entries `∑ u, (adj u).length`. -/
@[expose] def numEdges (inst : SparseInstance) : ℕ := bipAdjSteps inst.adj

/-- Flattened right-endpoint word list of length `numEdges`. -/
@[expose] def flatEdges (inst : SparseInstance) : List ℕ :=
  (List.finRange inst.m).flatMap fun u => (inst.adj u).map Fin.val

/-- CSR word encoding `m :: r :: offsets ++ flatEdges` (`m + numEdges + 3` words). -/
@[expose] def encode (inst : SparseInstance) : List ℕ :=
  inst.m :: inst.r :: (List.range (inst.m + 1)).map inst.offset ++ inst.flatEdges

/-- Maximum matching size `ν` on `inst`. -/
@[expose] def maxMatchingCard (inst : SparseInstance) : ℕ :=
  (hopcroftKarp inst.graph inst.adj).matching.card

/-- Matched pairs `(u, v)` of `(hopcroftKarp inst.graph inst.adj).matching`, ordered by ascending
right vertex `v : Fin inst.r`. -/
@[expose] def matchingPairs (inst : SparseInstance) : List (Fin inst.m × Fin inst.r) :=
  (List.finRange inst.r).filterMap fun v =>
    match (List.finRange inst.m).find?
        (fun u => decide ((u, v) ∈ (hopcroftKarp inst.graph inst.adj).matching)) with
    | some u => some (u, v)
    | none => none

/-- Flat output word list `[u₀, v₀, u₁, v₁, …]` of length `2 * maxMatchingCard`. -/
@[expose] def matchingWords (inst : SparseInstance) : List ℕ :=
  inst.matchingPairs.flatMap fun e => [e.1.val, e.2.val]

/-- Sufficient word-value envelope for all input words, CSR pointers, workspace addresses, and
output words on `inst`. -/
@[expose] def wordBound (inst : SparseInstance) : ℕ :=
  7 * inst.m + 6 * inst.r + inst.numEdges + 12

theorem offset_zero (inst : SparseInstance) : inst.offset 0 = 0 := by
  simp [offset]

theorem offset_succ (inst : SparseInstance) {u : ℕ} (hu : u < inst.m) :
    inst.offset (u + 1) = inst.offset u + (inst.adj ⟨u, hu⟩).length := by
  have hl : u < (List.finRange inst.m).length := by simpa using hu
  simp [offset, List.take_add_one, List.getElem?_eq_getElem hl]

theorem offset_m (inst : SparseInstance) : inst.offset inst.m = inst.numEdges := by
  rw [offset, List.take_of_length_le (by simp), ← Fin.sum_univ_def]
  rfl

theorem offset_mono (inst : SparseInstance) {u v : ℕ} (h : u ≤ v) :
    inst.offset u ≤ inst.offset v :=
  ((List.take_sublist_take_left h).map _).sum_le_sum fun _ _ => Nat.zero_le _

theorem offset_le_numEdges (inst : SparseInstance) (u : ℕ) :
    inst.offset u ≤ inst.numEdges := by
  rw [← inst.offset_m]
  by_cases h : u ≤ inst.m
  · exact inst.offset_mono h
  · rw [offset, List.take_of_length_le (by simp; omega),
      offset, List.take_of_length_le (by simp)]

theorem length_flatEdges (inst : SparseInstance) :
    inst.flatEdges.length = inst.numEdges := by
  simp [flatEdges, numEdges, bipAdjSteps, List.length_flatMap, ← Fin.sum_univ_def]

theorem encode_length (inst : SparseInstance) :
    inst.encode.length = inst.m + inst.numEdges + 3 := by
  simp only [encode, List.cons_append, List.length_cons, List.length_append, List.length_map,
    List.length_range, inst.length_flatEdges]
  omega

private theorem flatEdges_eq_append (inst : SparseInstance) (u : Fin inst.m) :
    inst.flatEdges =
      ((List.finRange inst.m).take u.val).flatMap (fun i => (inst.adj i).map Fin.val) ++
        ((inst.adj u).map Fin.val ++
          ((List.finRange inst.m).drop (u.val + 1)).flatMap
            (fun i => (inst.adj i).map Fin.val)) := by
  have hu : u.val < (List.finRange inst.m).length := by simp
  conv_lhs => rw [flatEdges, ← List.take_append_drop u.val (List.finRange inst.m),
    List.drop_eq_getElem_cons hu]
  simp [List.flatMap_append]

private theorem length_take_flatEdges (inst : SparseInstance) (u : ℕ) :
    (((List.finRange inst.m).take u).flatMap (fun i => (inst.adj i).map Fin.val)).length =
      inst.offset u := by
  simp [offset, List.length_flatMap]

theorem offset_add_lt_numEdges (inst : SparseInstance) (u : Fin inst.m) {i : ℕ}
    (hi : i < (inst.adj u).length) : inst.offset u.val + i < inst.numEdges := by
  rw [← inst.length_flatEdges, inst.flatEdges_eq_append u, List.length_append, List.length_append,
    inst.length_take_flatEdges]
  simp only [List.length_map]
  omega

private theorem flatEdges_getElem (inst : SparseInstance) (u : Fin inst.m) {i : ℕ}
    (hi : i < (inst.adj u).length) :
    inst.flatEdges[inst.offset u.val + i]'(by
      rw [inst.length_flatEdges]; exact inst.offset_add_lt_numEdges u hi) =
      ((inst.adj u)[i]'hi).val := by
  simp only [inst.flatEdges_eq_append u, ← inst.length_take_flatEdges u.val,
    List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simp [hi]), List.getElem_map]

private theorem init_mem_m {reg : ℕ} (inst : SparseInstance) :
    (Data.init inst.encode : Data reg).mem 1 = inst.m := rfl

private theorem init_mem_r {reg : ℕ} (inst : SparseInstance) :
    (Data.init inst.encode : Data reg).mem 2 = inst.r := rfl

private theorem init_mem_offset {reg : ℕ} (inst : SparseInstance) {u : ℕ} (hu : u ≤ inst.m) :
    (Data.init inst.encode : Data reg).mem (3 + u) = inst.offset u := by
  have hreal := Data.init_realizes_append (r := reg) [inst.m, inst.r]
    ((List.range (inst.m + 1)).map inst.offset) inst.flatEdges
  have henc : [inst.m, inst.r] ++ (((List.range (inst.m + 1)).map inst.offset) ++ inst.flatEdges) =
      inst.encode := by simp [encode]
  rw [henc] at hreal
  have h := hreal ⟨u, by simp; omega⟩
  simpa [Block.read] using h

private theorem init_mem_edge {reg : ℕ} (inst : SparseInstance) (u : Fin inst.m) {i : ℕ}
    (hi : i < (inst.adj u).length) :
    (Data.init inst.encode : Data reg).mem (inst.m + 4 + (inst.offset u.val + i)) =
      ((inst.adj u)[i]'hi).val := by
  let pre := [inst.m, inst.r] ++ (List.range (inst.m + 1)).map inst.offset
  have hreal := Data.init_realizes_append (r := reg) pre inst.flatEdges []
  have henc : pre ++ (inst.flatEdges ++ []) = inst.encode := by simp [pre, encode]
  rw [henc] at hreal
  have hpre : pre.length + 1 = inst.m + 4 := by simp [pre]
  have hlt : inst.offset u.val + i < inst.flatEdges.length := by
    rw [inst.length_flatEdges]
    exact inst.offset_add_lt_numEdges u hi
  have h := hreal ⟨inst.offset u.val + i, hlt⟩
  change (Data.init inst.encode : Data reg).mem (pre.length + 1 + (inst.offset u.val + i)) =
    inst.flatEdges[inst.offset u.val + i] at h
  rw [hpre, inst.flatEdges_getElem u hi] at h
  exact h

theorem inputFits_encode {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  refine ⟨hw.of_le (by rw [inst.encode_length]; unfold wordBound; omega), fun x hx => ?_⟩
  simp only [encode, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_range] at hx
  rcases hx with rfl | rfl | ⟨u, _, rfl⟩ | hx
  · exact hw.of_le (by unfold wordBound; omega)
  · exact hw.of_le (by unfold wordBound; omega)
  · have := inst.offset_le_numEdges u
    exact hw.of_le (by unfold wordBound; omega)
  · simp only [flatEdges, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map] at hx
    obtain ⟨_, v, _, rfl⟩ := hx
    have := v.isLt
    exact hw.of_le (by unfold wordBound; omega)

private theorem find_mate_eq (inst : SparseInstance) (v : Fin inst.r) :
    (List.finRange inst.m).find?
        (fun u => decide ((u, v) ∈ (hopcroftKarp inst.graph inst.adj).matching)) =
      vget (hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).mate v := by
  have hM := (hopcroftKarp_correct inst.bipAdjValid_graph).1.1
  rw [hopcroftKarp_matching_eq_mateMatching] at hM ⊢
  set mate := (hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).mate
  let p : Fin inst.m → Bool := fun u => decide ((u, v) ∈ mateMatching mate)
  change (List.finRange inst.m).find? p = vget mate v
  cases hm : vget mate v with
  | none =>
    rw [List.find?_eq_none]
    intro u _
    simp [p, mem_mateMatching, hm]
  | some u₀ =>
    cases hf : (List.finRange inst.m).find? p with
    | none =>
      have hfalse := (List.find?_eq_none.mp hf) u₀ (List.mem_finRange u₀)
      simp [p, mem_mateMatching, hm] at hfalse
    | some u₁ =>
      have hp₁ : p u₁ = true := List.find?_some hf
      have hu₁ : (u₁, v) ∈ mateMatching mate := of_decide_eq_true hp₁
      have hu₀ : (u₀, v) ∈ mateMatching mate := mem_mateMatching.mpr hm
      exact congrArg some (hM.2.2 u₁ u₀ v hu₁ hu₀)

private theorem matchingPairs_eq_mate_filterMap (inst : SparseInstance) :
    inst.matchingPairs =
      (List.finRange inst.r).filterMap fun v =>
        match vget (hkLoop inst.graph inst.adj (inst.m + 1) 0
            (Vector.replicate inst.r none)).mate v with
        | some u => some (u, v)
        | none => none := by
  unfold matchingPairs
  refine List.filterMap_congr fun v _ => ?_
  rw [inst.find_mate_eq v]

/-- `inst.matchingPairs.toFinset` equals `(hopcroftKarp inst.graph inst.adj).matching`, hence is a
maximum matching of `inst.graph`. -/
theorem toFinset_matchingPairs (inst : SparseInstance) :
    inst.matchingPairs.toFinset = (hopcroftKarp inst.graph inst.adj).matching := by
  rw [inst.matchingPairs_eq_mate_filterMap, hopcroftKarp_matching_eq_mateMatching]
  set mate := (hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).mate
  ext ⟨u, v⟩
  simp only [List.mem_toFinset, List.mem_filterMap, List.mem_finRange, true_and, mem_mateMatching]
  constructor
  · rintro ⟨v', hm⟩
    cases h : vget mate v' with
    | none => simp [h] at hm
    | some u' =>
      simp only [h, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      exact h
  · intro hm
    exact ⟨v, by simp [hm]⟩

theorem isMaxMatching_matchingPairs (inst : SparseInstance) :
    IsMaxMatching inst.graph inst.matchingPairs.toFinset := by
  rw [inst.toFinset_matchingPairs]
  exact (hopcroftKarp_correct inst.bipAdjValid_graph).1

theorem nodup_matchingPairs (inst : SparseInstance) : inst.matchingPairs.Nodup := by
  rw [inst.matchingPairs_eq_mate_filterMap]
  set mate := (hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).mate
  refine List.Nodup.filterMap ?_ (List.nodup_finRange inst.r)
  intro v₁ v₂ e h₁ h₂
  cases hm₁ : vget mate v₁
  · simp [hm₁] at h₁
  cases hm₂ : vget mate v₂
  · simp [hm₂] at h₂
  simp only [hm₁, Option.mem_def, Option.some.injEq] at h₁
  simp only [hm₂, Option.mem_def, Option.some.injEq] at h₂
  subst h₁
  exact (Prod.mk.inj h₂).2.symm

theorem length_matchingPairs (inst : SparseInstance) :
    inst.matchingPairs.length = inst.maxMatchingCard := by
  rw [← List.toFinset_card_of_nodup inst.nodup_matchingPairs, inst.toFinset_matchingPairs]
  rfl

theorem length_matchingWords (inst : SparseInstance) :
    inst.matchingWords.length = 2 * inst.maxMatchingCard := by
  simp [matchingWords, List.length_flatMap, inst.length_matchingPairs, Nat.mul_comm]

/-- Entry `2 * i` of `inst.matchingWords` is the left endpoint of the `i`-th matched edge. -/
theorem getElem_matchingWords_even (inst : SparseInstance) {i : ℕ}
    (hi : i < inst.matchingPairs.length) :
    inst.matchingWords[2 * i]'(by
      rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
      (inst.matchingPairs[i]'hi).1.val := by
  have h := List.getElem?_flatMap_mul_add inst.matchingPairs
    (fun e => [e.1.val, e.2.val]) 2 (fun _ _ => rfl) hi (show 0 < 2 by decide)
  rw [Nat.mul_comm, Nat.add_zero] at h
  have hget : inst.matchingWords[2 * i]? = some (inst.matchingPairs[i]'hi).1.val := by
    simpa [matchingWords] using h
  rw [List.getElem?_eq_getElem
    (by rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega)] at hget
  exact Option.some.inj hget

/-- Entry `2 * i + 1` of `inst.matchingWords` is the right endpoint of the `i`-th matched edge. -/
theorem getElem_matchingWords_odd (inst : SparseInstance) {i : ℕ}
    (hi : i < inst.matchingPairs.length) :
    inst.matchingWords[2 * i + 1]'(by
      rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
      (inst.matchingPairs[i]'hi).2.val := by
  have h := List.getElem?_flatMap_mul_add inst.matchingPairs
    (fun e => [e.1.val, e.2.val]) 2 (fun _ _ => rfl) hi (show 1 < 2 by decide)
  rw [Nat.mul_comm] at h
  have hget : inst.matchingWords[2 * i + 1]? = some (inst.matchingPairs[i]'hi).2.val := by
    simpa [matchingWords] using h
  rw [List.getElem?_eq_getElem
    (by rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega)] at hget
  exact Option.some.inj hget

end SparseInstance

/-- A dense bipartite graph instance on `Fin m × Fin r` represented by an `m × r` `0/1` adjacency
matrix. -/
structure DenseInstance where
  /-- Number of left vertices. -/
  m : ℕ
  /-- Number of right vertices. -/
  r : ℕ
  /-- Bipartite edge indicator `Fin m × Fin r → Bool`. -/
  graph : Fin m × Fin r → Bool

namespace DenseInstance

/-- Underlying exact CSR instance `⟨m, r, exactBipAdj graph⟩`. -/
@[expose] def toSparse (inst : DenseInstance) : SparseInstance where
  m := inst.m
  r := inst.r
  adj := exactBipAdj inst.graph

/-- Row-major word encoding `m :: r :: matrixWords` (`2 + m * r` words). -/
@[expose] def encode (inst : DenseInstance) : List ℕ :=
  inst.m :: inst.r :: (List.finRange inst.m).flatMap fun u =>
    (List.finRange inst.r).map fun v => if inst.graph (u, v) then 1 else 0

/-- Maximum matching size `ν` of `inst.graph`. -/
@[expose] def maxMatchingCard (inst : DenseInstance) : ℕ :=
  (hopcroftKarpDense inst.graph).matching.card

/-- Ordered edge list of the maximum matching computed by dense Hopcroft–Karp on `inst.graph`. -/
@[expose] def matchingPairs (inst : DenseInstance) : List (Fin inst.m × Fin inst.r) :=
  inst.toSparse.matchingPairs

/-- Flat output word list `[u₀, v₀, u₁, v₁, …]` of a maximum matching of `inst.graph`. -/
@[expose] def matchingWords (inst : DenseInstance) : List ℕ :=
  inst.toSparse.matchingWords

/-- Sufficient word-value envelope for dense Hopcroft–Karp on `inst`. -/
@[expose] def wordBound (inst : DenseInstance) : ℕ :=
  2 * inst.m * inst.r + 8 * inst.m + 6 * inst.r + 14

@[simp] theorem toSparse_graph (inst : DenseInstance) : inst.toSparse.graph = inst.graph := by
  rcases inst with ⟨m, r, graph⟩
  dsimp only [toSparse]
  ext ⟨u, v⟩
  cases h : graph (u, v) <;> simp [SparseInstance.graph, exactBipAdj, h]

theorem maxMatchingCard_eq_toSparse (inst : DenseInstance) :
    inst.maxMatchingCard = inst.toSparse.maxMatchingCard := by
  rw [maxMatchingCard, SparseInstance.maxMatchingCard, inst.toSparse_graph,
    ← hopcroftKarp_exactBipAdj]
  rfl

theorem toFinset_matchingPairs (inst : DenseInstance) :
    inst.matchingPairs.toFinset = (hopcroftKarpDense inst.graph).matching := by
  change inst.toSparse.matchingPairs.toFinset = _
  rw [inst.toSparse.toFinset_matchingPairs, inst.toSparse_graph]
  exact congrArg HopcroftKarpOutput.matching (hopcroftKarp_exactBipAdj inst.graph)

/-- `inst.matchingPairs.toFinset` is a maximum matching of `inst.graph`. -/
theorem isMaxMatching_matchingPairs (inst : DenseInstance) :
    IsMaxMatching inst.graph inst.matchingPairs.toFinset := by
  rw [inst.toFinset_matchingPairs]
  exact (hopcroftKarpDense_correct inst.graph).1

theorem nodup_matchingPairs (inst : DenseInstance) : inst.matchingPairs.Nodup :=
  inst.toSparse.nodup_matchingPairs

theorem length_matchingPairs (inst : DenseInstance) :
    inst.matchingPairs.length = inst.maxMatchingCard := by
  rw [inst.maxMatchingCard_eq_toSparse]
  exact inst.toSparse.length_matchingPairs

theorem length_matchingWords (inst : DenseInstance) :
    inst.matchingWords.length = 2 * inst.maxMatchingCard := by
  rw [inst.maxMatchingCard_eq_toSparse]
  exact inst.toSparse.length_matchingWords

/-- Entry `2 * i` of `inst.matchingWords` is the left endpoint of the `i`-th matched edge. -/
theorem getElem_matchingWords_even (inst : DenseInstance) {i : ℕ}
    (hi : i < inst.matchingPairs.length) :
    inst.matchingWords[2 * i]'(by
      rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
      (inst.matchingPairs[i]'hi).1.val :=
  inst.toSparse.getElem_matchingWords_even hi

/-- Entry `2 * i + 1` of `inst.matchingWords` is the right endpoint of the `i`-th matched edge. -/
theorem getElem_matchingWords_odd (inst : DenseInstance) {i : ℕ}
    (hi : i < inst.matchingPairs.length) :
    inst.matchingWords[2 * i + 1]'(by
      rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
      (inst.matchingPairs[i]'hi).2.val :=
  inst.toSparse.getElem_matchingWords_odd hi

theorem numEdges_toSparse_le (inst : DenseInstance) :
    inst.toSparse.numEdges ≤ inst.m * inst.r :=
  bipAdjSteps_exactBipAdj_le inst.graph

theorem encode_length (inst : DenseInstance) :
    inst.encode.length = 2 + inst.m * inst.r := by
  simp only [encode, List.length_cons, List.length_flatMap, List.length_map, List.length_finRange,
    List.map_const', List.sum_replicate, smul_eq_mul]
  omega

private theorem init_mem_m {reg : ℕ} (inst : DenseInstance) :
    (Data.init inst.encode : Data reg).mem 1 = inst.m := rfl

private theorem init_mem_r {reg : ℕ} (inst : DenseInstance) :
    (Data.init inst.encode : Data reg).mem 2 = inst.r := rfl

private theorem init_mem_entry {reg : ℕ} (inst : DenseInstance) (u : Fin inst.m) (v : Fin inst.r) :
    (Data.init inst.encode : Data reg).mem (3 + (u.val * inst.r + v.val)) =
      if inst.graph (u, v) then 1 else 0 := by
  let g : Fin inst.m → List ℕ := fun u' =>
    (List.finRange inst.r).map fun v' => if inst.graph (u', v') then 1 else 0
  have h := List.getElem?_flatMap_mul_add (List.finRange inst.m) g inst.r
    (fun _ _ => by simp [g]) (show u.val < (List.finRange inst.m).length by simp) v.isLt
  rw [show 3 + (u.val * inst.r + v.val) = (u.val * inst.r + v.val) + 1 + 1 + 1 by omega,
    Data.init_mem_succ, encode, List.getD_cons_succ, List.getD_cons_succ,
    List.getD_eq_getElem?_getD, h]
  simp [g]

theorem inputFits_encode {w : ℕ} (inst : DenseInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  refine ⟨hw.of_le (by rw [inst.encode_length]; unfold wordBound; nlinarith), fun x hx => ?_⟩
  simp only [encode, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_map] at hx
  rcases hx with rfl | rfl | ⟨u, v, rfl⟩
  · exact hw.of_le (by unfold wordBound; nlinarith)
  · exact hw.of_le (by unfold wordBound; nlinarith)
  · split_ifs <;> exact hw.of_le (by unfold wordBound; nlinarith)

end DenseInstance

/-! ## Registers and memory layout -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 34 := ⟨0, by decide⟩
/-- Constant `1`. -/
abbrev one : Fin 34 := ⟨1, by decide⟩
/-- Constant `2`. -/
abbrev two : Fin 34 := ⟨2, by decide⟩
/-- Left side size `m`. -/
abbrev rm : Fin 34 := ⟨3, by decide⟩
/-- Right side size `r`. -/
abbrev rr : Fin 34 := ⟨4, by decide⟩
/-- Total CSR edge entries `numEdges`. -/
abbrev rE : Fin 34 := ⟨5, by decide⟩
/-- Base address of CSR `offset[0..m]`. -/
abbrev bOffReg : Fin 34 := ⟨6, by decide⟩
/-- Base address of CSR `edges[0..numEdges)`. -/
abbrev bEdgesReg : Fin 34 := ⟨7, by decide⟩
/-- Base address of `colMate[0..r)`. -/
abbrev bColMateReg : Fin 34 := ⟨8, by decide⟩
/-- Base address of matched-left flags `ml[0..m)`. -/
abbrev bMLReg : Fin 34 := ⟨9, by decide⟩
/-- Base address of layer distances `dist[0..m)`. -/
abbrev bDistReg : Fin 34 := ⟨10, by decide⟩
/-- Base address of BFS queue `queue[0..m)`. -/
abbrev bQueueReg : Fin 34 := ⟨11, by decide⟩
/-- Base address of DFS visited flags `vis[0..r)`. -/
abbrev bVisReg : Fin 34 := ⟨12, by decide⟩
/-- Base address of DFS left-vertex stack `stackU[0..m + 2)`. -/
abbrev bStackUReg : Fin 34 := ⟨13, by decide⟩
/-- Base address of DFS right-vertex stack `stackV[0..m + 2)`. -/
abbrev bStackVReg : Fin 34 := ⟨14, by decide⟩
/-- Base address of DFS current-arc cursor stack `stackPos[0..m + 2)`. -/
abbrev bStackPosReg : Fin 34 := ⟨15, by decide⟩
/-- Base address of phase rematch left endpoints `augU[0..r)`. -/
abbrev bAugUReg : Fin 34 := ⟨16, by decide⟩
/-- Base address of phase rematch right endpoints `augV[0..r)`. -/
abbrev bAugVReg : Fin 34 := ⟨17, by decide⟩
/-- Output header address register (for `ExecutesList` programs). -/
abbrev outBase : Fin 34 := ⟨18, by decide⟩
private abbrev phaseActive : Fin 34 := ⟨19, by decide⟩
private abbrev rk : Fin 34 := ⟨20, by decide⟩
private abbrev rfound : Fin 34 := ⟨21, by decide⟩
private abbrev qHead : Fin 34 := ⟨22, by decide⟩
private abbrev qTail : Fin 34 := ⟨23, by decide⟩
private abbrev layerEnd : Fin 34 := ⟨24, by decide⟩
private abbrev rd : Fin 34 := ⟨25, by decide⟩
private abbrev augLen : Fin 34 := ⟨26, by decide⟩
/-- Scalar output / loop-active register (for `Executes` programs). -/
abbrev acc : Fin 34 := ⟨27, by decide⟩
private abbrev active : Fin 34 := acc
private abbrev idx : Fin 34 := ⟨28, by decide⟩
private abbrev limit : Fin 34 := ⟨29, by decide⟩
private abbrev addr : Fin 34 := ⟨30, by decide⟩
private abbrev val : Fin 34 := ⟨31, by decide⟩
private abbrev val2 : Fin 34 := ⟨32, by decide⟩
private abbrev tmp : Fin 34 := ⟨33, by decide⟩

end Reg

open Reg

/-- Encode `Option (Fin m)` into `{0, …, m}` with `none ↦ m`. -/
private def encodeOptFin {m : ℕ} : Option (Fin m) → ℕ
  | some u => u.val
  | none => m

/-- Encode `Option ℕ` layer distances with `none ↦ 0` and `some j ↦ j + 1`. -/
private def encodeDist : Option ℕ → ℕ
  | none => 0
  | some j => j + 1

/-- In-memory CSR representation of `inst : SparseInstance` starting at `bOff`. -/
structure CSRMem (inst : SparseInstance) (bOff : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- `offset[u]` for `0 ≤ u ≤ m`. -/
  hoff : ∀ {u : ℕ}, u ≤ inst.m → mem (bOff + u) = inst.offset u
  /-- `edges[offset u + i]` for `u : Fin m`, `i < (adj u).length`. -/
  hedge : ∀ (u : Fin inst.m) {i : ℕ} (hi : i < (inst.adj u).length),
    mem (bOff + inst.m + 1 + (inst.offset u.val + i)) = ((inst.adj u)[i]'hi).val

theorem CSRMem.of_outside {inst : SparseInstance} {bOff : ℕ} {mem mem' : ℕ → ℕ}
    (h : CSRMem inst bOff mem)
    (hf : ∀ a, bOff ≤ a ∧ a < bOff + inst.m + 1 + inst.numEdges → mem' a = mem a) :
    CSRMem inst bOff mem' where
  hoff {u} hu := (hf _ ⟨by omega, by omega⟩).trans (h.hoff hu)
  hedge u {i} hi := by
    have hlt := inst.offset_add_lt_numEdges u hi
    exact (hf _ ⟨by omega, by omega⟩).trans (h.hedge u hi)

/-- Read-only constant and workspace base-pointer registers (`0 .. 18`) for `coreCode`. -/
structure BaseRegs (inst : SparseInstance) (bOff : ℕ) (x : Data 34) : Prop where
  /-- `zero = 0`. -/
  hzero : x.regs zero = 0
  /-- `one = 1`. -/
  hone : x.regs one = 1
  /-- `two = 2`. -/
  htwo : x.regs two = 2
  /-- `rm = m`. -/
  hrm : x.regs rm = inst.m
  /-- `rr = r`. -/
  hrr : x.regs rr = inst.r
  /-- `rE = numEdges`. -/
  hrE : x.regs rE = inst.numEdges
  /-- `bOffReg = bOff`. -/
  hbOff : x.regs bOffReg = bOff
  /-- `bEdgesReg = bOff + m + 1`. -/
  hbEdges : x.regs bEdgesReg = bOff + inst.m + 1
  /-- `bColMateReg = bWork`. -/
  hbColMate : x.regs bColMateReg = bOff + inst.m + 1 + inst.numEdges
  /-- `bMLReg = bWork + r`. -/
  hbML : x.regs bMLReg = bOff + inst.m + 1 + inst.numEdges + inst.r
  /-- `bDistReg = bWork + r + m`. -/
  hbDist : x.regs bDistReg = bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m
  /-- `bQueueReg = bWork + r + 2 * m`. -/
  hbQueue : x.regs bQueueReg = bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m
  /-- `bVisReg = bWork + r + 3 * m`. -/
  hbVis : x.regs bVisReg = bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m
  /-- `bStackUReg = bWork + 2 * r + 3 * m`. -/
  hbStackU : x.regs bStackUReg = bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m
  /-- `bStackVReg = bWork + 2 * r + 4 * m + 2`. -/
  hbStackV : x.regs bStackVReg = bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2
  /-- `bStackPosReg = bWork + 2 * r + 5 * m + 4`. -/
  hbStackPos : x.regs bStackPosReg =
    bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4
  /-- `bAugUReg = bWork + 2 * r + 6 * m + 6`. -/
  hbAugU : x.regs bAugUReg = bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6
  /-- `bAugVReg = bWork + 3 * r + 6 * m + 6`. -/
  hbAugV : x.regs bAugVReg = bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6
  /-- `outBase = bWork + 4 * r + 6 * m + 6`. -/
  houtBase : x.regs outBase = bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6

/-- Transport `BaseRegs` across states that agree on registers `0 .. 18`. -/
theorem BaseRegs.of_eq {inst : SparseInstance} {bOff : ℕ} {x y : Data 34}
    (hb : BaseRegs inst bOff x) (heq : ∀ i : Fin 34, i.val < 19 → y.regs i = x.regs i) :
    BaseRegs inst bOff y where
  hzero := (heq zero (by decide)).trans hb.hzero
  hone := (heq one (by decide)).trans hb.hone
  htwo := (heq two (by decide)).trans hb.htwo
  hrm := (heq rm (by decide)).trans hb.hrm
  hrr := (heq rr (by decide)).trans hb.hrr
  hrE := (heq rE (by decide)).trans hb.hrE
  hbOff := (heq bOffReg (by decide)).trans hb.hbOff
  hbEdges := (heq bEdgesReg (by decide)).trans hb.hbEdges
  hbColMate := (heq bColMateReg (by decide)).trans hb.hbColMate
  hbML := (heq bMLReg (by decide)).trans hb.hbML
  hbDist := (heq bDistReg (by decide)).trans hb.hbDist
  hbQueue := (heq bQueueReg (by decide)).trans hb.hbQueue
  hbVis := (heq bVisReg (by decide)).trans hb.hbVis
  hbStackU := (heq bStackUReg (by decide)).trans hb.hbStackU
  hbStackV := (heq bStackVReg (by decide)).trans hb.hbStackV
  hbStackPos := (heq bStackPosReg (by decide)).trans hb.hbStackPos
  hbAugU := (heq bAugUReg (by decide)).trans hb.hbAugU
  hbAugV := (heq bAugVReg (by decide)).trans hb.hbAugV
  houtBase := (heq outBase (by decide)).trans hb.houtBase

private def MateMem {m r : ℕ} (bColMate : ℕ) (mate : Vector (Option (Fin m)) r) (mem : ℕ → ℕ) :
    Prop :=
  ∀ v : Fin r, mem (bColMate + v.val) = encodeOptFin (vget mate v)

private def DistMem {m : ℕ} (bDist : ℕ) (dist : Vector (Option ℕ) m) (mem : ℕ → ℕ) : Prop :=
  ∀ u : Fin m, mem (bDist + u.val) = encodeDist (vget dist u)

private def VisMem {r : ℕ} (bVis : ℕ) (vis : Vector Bool r) (mem : ℕ → ℕ) : Prop :=
  ∀ v : Fin r, mem (bVis + v.val) = if vget vis v = true then 1 else 0

private def QueueSlice {m : ℕ} (bQueue start : ℕ) (xs : List (Fin m)) (mem : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, (hi : i < xs.length) → mem (bQueue + start + i) = (xs[i]'hi).val

/-! ## Block zero-fill and constant-fill helpers -/

/-- Zero-fill `[x.regs baseReg, x.regs baseReg + x.regs lenReg)` via `Cslib.WordRAM.zeroFill`. -/
private def clearAt (baseReg lenReg : Fin 34) : Code .standard 34 :=
  .seq (ram[ addr ← baseReg; limit ← baseReg + lenReg ]) (zeroFill addr limit zero one)

private theorem exec_clearAt {w : ℕ} (baseReg lenReg : Fin 34)
    (hb_lt : baseReg.val < 29) (hl_lt : lenReg.val < 29) (x : Data 34)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hfit : Fits w (x.regs baseReg + x.regs lenReg)) :
    ∃ y, ExecWithin w (clearAt baseReg lenReg) x y (4 * x.regs lenReg + 4) ∧
      (∀ i : Fin 34, i.val < 29 → y.regs i = x.regs i) ∧
      y.mem = clear x.mem (x.regs baseReg) (x.regs lenReg) := by
  have hba : baseReg ≠ addr := fun h => by subst h; simp at hb_lt
  have hla : lenReg ≠ addr := fun h => by subst h; simp at hl_lt
  have hstep₁ : ∃ s₁, ExecWithin w (ram[ addr ← baseReg; limit ← baseReg + lenReg ] :
      Code .standard 34) x s₁ 2 ∧
      s₁ = (x.set addr (x.regs baseReg)).set limit (x.regs baseReg + x.regs lenReg) := by
    refine WP.exists_execWithin ?_
    wram_exec [hla, hfit]
    rfl
  obtain ⟨s₁, he₁, rfl⟩ := hstep₁
  let st := (x.set addr (x.regs baseReg)).set limit (x.regs baseReg + x.regs lenReg)
  have hs₁_addr : st.regs addr = x.regs baseReg := by simp [st]
  have hs₁_lim : st.regs limit = x.regs baseReg + x.regs lenReg := by simp [st]
  have hs₁_0 : st.regs zero = 0 := by wram_simp [st, h0]
  have hs₁_1 : st.regs one = 1 := by wram_simp [st, h1]
  have hzf := (zeroFill_exec (w := w) (cur := addr) (stop := limit) (zero := zero) (one := one)
    (x := st) (by decide) (by decide) (by decide) hs₁_0 hs₁_1
    (by rw [hs₁_addr, hs₁_lim]; omega) (by rwa [hs₁_lim])).within
  refine ⟨_, (he₁.seq hzf).mono (by rw [hs₁_addr, hs₁_lim]; omega), fun i hi => ?_, ?_⟩
  · have hia : i ≠ addr := fun h => by subst h; simp at hi
    have hil : i ≠ limit := fun h => by subst h; simp at hi
    simp [st, Function.update_of_ne hia, hil]
  · simp [st, hs₁_addr, hs₁_lim]

private abbrev fillConst (baseReg lenReg valReg : Fin 34) : Code .standard 34 :=
  Cslib.WordRAM.fillConst baseReg lenReg valReg one idx addr

private theorem exec_fillConst {w : ℕ} (baseReg lenReg valReg : Fin 34)
    (hb_lt : baseReg.val < 28) (hl_lt : lenReg.val < 28) (hv_lt : valReg.val < 28)
    (x : Data 34) (h1 : x.regs one = 1)
    (hfit_end : Fits w (x.regs baseReg + x.regs lenReg))
    (hfit_len : Fits w (x.regs lenReg)) :
    ∃ y, ExecWithin w (fillConst baseReg lenReg valReg) x y (5 * x.regs lenReg + 3) ∧
      (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ k < x.regs lenReg, y.mem (x.regs baseReg + k) = x.regs valReg) ∧
      (∀ a, ¬(x.regs baseReg ≤ a ∧ a < x.regs baseReg + x.regs lenReg) → y.mem a = x.mem a) := by
  have hne : ∀ j : Fin 34, j.val < 28 → idx ≠ j ∧ addr ≠ j := fun j hj =>
    ⟨fun h => by subst h; simp at hj, fun h => by subst h; simp at hj⟩
  obtain ⟨y, he, hr, _, hmem⟩ := Cslib.WordRAM.fillConst_exec (w := w)
    (base := baseReg) (len := lenReg) (val := valReg) (one := one) (idx := idx) (addr := addr)
    (hne baseReg hb_lt).1 (hne lenReg hl_lt).1 (hne valReg hv_lt).1 (by decide)
    (hne baseReg hb_lt).2 (hne lenReg hl_lt).2 (hne valReg hv_lt).2 (by decide) (by decide)
    h1 hfit_end hfit_len
  exact ⟨y, he.within, fun i hi => hr i (hne i hi).1.symm (hne i hi).2.symm,
    fun k hk => by rw [hmem]; exact fill_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩,
    fun a ha => by rw [hmem]; exact fill_of_not_owns ha⟩

/-! ## Section 2: Queue-based breadth-first layering (`bfsCode`) -/

private def markMLBody : Code .standard 34 := ram[
  addr ← bColMateReg + idx; val ← *addr;
  if val < rm then [ addr ← bMLReg + val; *addr ← one ] else [ tmp ← zero ];
  idx ← idx + one ]

private def markMLCode : Code .standard 34 :=
  .seq (clearAt bMLReg rm) (.seq (ram[ idx ← #0 ]) (.loop (.lt idx rr) markMLBody))

private theorem exec_markMLCode {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} (x : Data 34)
    (hb : BaseRegs inst bOff x) (hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w markMLCode x y (4 * inst.m + 8 * inst.r + 7) ∧
      (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ u : Fin inst.m, y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + u.val) =
        if vget (hkMatchedLeft mate) u = true then 1 else 0) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) → y.mem a = x.mem a) := by
  obtain ⟨y₁, he₁, hr₁, hmem₁⟩ := exec_clearAt bMLReg rm (by decide) (by decide) x
    hb.hzero hb.hone (by rw [hb.hbML, hb.hrm]; exact hfit.of_le (by omega))
  rw [hb.hrm] at he₁
  rw [hb.hbML, hb.hrm] at hmem₁
  have hb₁ : BaseRegs inst bOff y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  let P (k : ℕ) (y : Data 34) : Prop :=
    (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ u : Fin inst.m, y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + u.val) =
        if vget (((List.finRange inst.r).take k).foldl (hkMarkStep mate)
            (Vector.replicate inst.m false)) u = true then 1 else 0) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) → y.mem a = x.mem a)
  have hs₀ : ∃ s₀, ExecWithin w (ram[ idx ← #0 ] : Code .standard 34) y₁ s₀ 1 ∧
      s₀ = y₁.set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  have hP₀ : P 0 (y₁.set idx 0) := by
    refine ⟨fun i hi => by wram_simp [hr₁ i (by omega)], fun u => ?_, fun a ha => ?_⟩
    · have := u.isLt
      simp only [Data.set, List.take_zero, List.foldl_nil, vget_replicate, Bool.false_eq_true,
        ↓reduceIte, hmem₁]
      exact clear_of_owns (by simp only [Block.Owns]; omega)
    · simp only [Data.set, hmem₁]
      exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.r) :
      ∃ z, ExecWithin w markMLBody y z 6 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let v : Fin inst.r := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hcol_v :
        y.mem (bOff + inst.m + 1 + inst.numEdges + y.regs idx) = encodeOptFin (vget mate v) := by
      rw [hf _ (by omega)]
      exact hmate v
    have htk : (List.finRange inst.r).take (y.regs idx + 1) =
        (List.finRange inst.r).take (y.regs idx) ++ [v] := List.take_succ_finRange hlt
    have hf1 : Fits w (bOff + inst.m + 1 + inst.numEdges + y.regs idx) := hfit.of_le (by omega)
    have hf2 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold markMLBody
    cases hmv : vget mate v with
    | none =>
      have henc : encodeOptFin (vget mate v) = inst.m := by simp [hmv, encodeOptFin]
      have hnl : ¬inst.m < inst.m := Nat.lt_irrefl _
      wram_exec [hby.hbColMate, hby.hrm, hby.hzero, hby.hone, hcol_v, henc, hnl, hf1, hf2]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], fun u => ?_, fun a ha => by wram_simp [hf a ha]⟩,
        by wram_simp⟩
      wram_simp
      rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, hkMarkStep, hmv]
      exact hm u
    | some w₀ =>
      have henc : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
      have hwlt : w₀.val < inst.m := w₀.isLt
      have hf3 : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + w₀.val) :=
        hfit.of_le (by omega)
      wram_exec [hby.hbColMate, hby.hbML, hby.hrm, hby.hzero, hby.hone, hcol_v, henc, hwlt,
        hf1, hf2, hf3]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], fun u => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil, hkMarkStep, hmv]
        rcases eq_or_ne u w₀ with rfl | hne
        · wram_simp
          simp
        · have hne_val : u.val ≠ w₀.val := fun h => hne (Fin.ext h)
          wram_simp
          rw [vget_vset_ne _ _ hne.symm]
          exact hm u
      · wram_simp
        exact hf a ha
  obtain ⟨y, hl, hPr, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rr (by decide)).trans hb.hrr) hbody
    (x := y₁.set idx 0) (by simp) (by simpa using hP₀)
  refine ⟨y, (he₁.seq (he₀.seq hl)).mono (by simp; omega), hPr.1, fun u => ?_, hPr.2.2⟩
  have hfull : (List.finRange inst.r).take inst.r = List.finRange inst.r :=
    List.take_of_length_le (by simp)
  have hu_eq := hPr.2.1 u
  rw [hfull] at hu_eq
  exact hu_eq

private def seedBfsBody : Code .standard 34 := ram[
  addr ← bMLReg + idx; val ← *addr;
  if val = zero then [
    addr ← bDistReg + idx; *addr ← one;
    addr ← bQueueReg + qTail; *addr ← idx;
    qTail ← qTail + one
  ] else [ tmp ← zero ];
  idx ← idx + one ]

private def seedBfsCode : Code .standard 34 :=
  .seq (clearAt bDistReg rm)
    (.seq (ram[ qHead ← #0; qTail ← #0; rk ← #0; rfound ← #0; idx ← #0 ])
      (.seq (.loop (.lt idx rm) seedBfsBody)
        (ram[ if qHead < qTail then [ active ← one ] else [ active ← zero ] ])))

private theorem exec_seedBfsCode {w bOff : ℕ} {inst : SparseInstance}
    {ml : Vector Bool inst.m} (x : Data 34) (hb : BaseRegs inst bOff x)
    (hml : ∀ u : Fin inst.m, x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + u.val) =
      if vget ml u = true then 1 else 0)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let p := (List.finRange inst.m).foldl (hkBfsInitStep ml) (Vector.replicate inst.m none, [])
    ∃ y, ExecWithin w seedBfsCode x y (15 * inst.m + 14) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) p.1 y.mem ∧
      QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) 0 p.2 y.mem ∧
      y.regs qHead = 0 ∧
      y.regs qTail = p.2.length ∧
      y.regs rk = 0 ∧
      y.regs rfound = 0 ∧
      y.regs active = (if p.2 = [] then 0 else 1) ∧
      p.2.Nodup ∧
      (∀ u : Fin inst.m, vget p.1 u ≠ none ↔ u ∈ p.2) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  intro p
  obtain ⟨y₁, he₁, hr₁, hmem₁⟩ := exec_clearAt bDistReg rm (by decide) (by decide) x
    hb.hzero hb.hone (by rw [hb.hbDist, hb.hrm]; exact hfit.of_le (by omega))
  rw [hb.hrm] at he₁
  rw [hb.hbDist, hb.hrm] at hmem₁
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ qHead ← #0; qTail ← #0; rk ← #0; rfound ← #0; idx ← #0 ] : Code .standard 34) y₁ s₀ 5 ∧
      s₀ = ((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let pk (k : ℕ) :=
    ((List.finRange inst.m).take k).foldl (hkBfsInitStep ml) (Vector.replicate inst.m none, [])
  let P (k : ℕ) (y : Data 34) : Prop :=
    (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) (pk k).1 y.mem ∧
      QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) 0 (pk k).2 y.mem ∧
      y.regs qHead = 0 ∧
      y.regs qTail = (pk k).2.length ∧
      y.regs rk = 0 ∧
      y.regs rfound = 0 ∧
      (pk k).2.Nodup ∧
      (∀ x₀ ∈ (pk k).2, x₀.val < k) ∧
      (∀ u : Fin inst.m, vget (pk k).1 u ≠ none ↔ u ∈ (pk k).2) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + k) → y.mem a = x.mem a)
  have hP₀ : P 0 (((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0) := by
    refine ⟨fun i hi => by wram_simp [hr₁ i (by omega)], fun u => ?_,
      fun i hi => by simp [pk] at hi,
      by wram_simp, by wram_simp; simp [pk], by wram_simp, by wram_simp, by simp [pk],
      fun _ h => by simp [pk] at h, fun u => by simp [pk, vget_replicate], fun a ha => ?_⟩
    · have := u.isLt
      simp only [Data.set, pk, List.take_zero, List.foldl_nil, vget_replicate, encodeDist, hmem₁]
      exact clear_of_owns (by simp only [Block.Owns]; omega)
    · simp only [Data.set, hmem₁]
      exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.m) :
      ∃ z, ExecWithin w seedBfsBody y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hdM, hqM, hqh, hqt, hrk, hrf, hnd, hlt_mem, hiff, hf⟩ := hy
    let u : Fin inst.m := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hml_u : y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + y.regs idx) =
        if vget ml u = true then 1 else 0 := by
      rw [hf _ (by omega)]
      exact hml u
    have hlen_le : (pk (y.regs idx)).2.length ≤ y.regs idx := by
      have hsub : (pk (y.regs idx)).2.Sublist ((List.finRange inst.m).take (y.regs idx)) := by
        have hgen : ∀ (ls : List (Fin inst.m))
            (st : Vector (Option ℕ) inst.m × List (Fin inst.m)),
            (ls.foldl (hkBfsInitStep ml) st).2.Sublist (st.2 ++ ls) := by
          intro ls
          induction ls with
          | nil => intro st; simp
          | cons a ls ih =>
            intro st
            simp only [List.foldl_cons, hkBfsInitStep]
            split_ifs
            · exact (ih st).trans ((List.sublist_cons_self a ls).append_left st.2)
            · simpa [List.append_assoc] using ih (vset st.1 a (some 0), st.2 ++ [a])
        simpa [pk] using hgen ((List.finRange inst.m).take (y.regs idx))
          (Vector.replicate inst.m none, [])
      exact hsub.length_le.trans (by simp)
    have htk : pk (y.regs idx + 1) = hkBfsInitStep ml (pk (y.regs idx)) u := by
      simp only [pk, List.take_succ_finRange hlt, List.foldl_append, List.foldl_cons,
        List.foldl_nil]
      rfl
    have hf1 : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + y.regs idx) :=
      hfit.of_le (by omega)
    have hf2 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold seedBfsBody
    by_cases hmu : vget ml u = true
    · have hval1 : (if vget ml u = true then 1 else 0) = 1 := ite_eq_left hmu
      have hpk1 : pk (y.regs idx + 1) = pk (y.regs idx) := by
        rw [htk, hkBfsInitStep, ite_eq_left hmu]
      wram_exec [hby.hbML, hby.hzero, hby.hone, hml_u, hval1, hf1, hf2]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], ?_, ?_, by wram_simp [hqh], ?_,
        by wram_simp [hrk], by wram_simp [hrf], ?_, ?_, ?_, fun a ha => ?_⟩, by wram_simp⟩
      · intro w₀; wram_simp; rw [hpk1]; exact hdM w₀
      · intro i hi; wram_simp; simp only [hpk1] at hi ⊢; exact hqM i hi
      · wram_simp; rw [hpk1]; exact hqt
      · rw [hpk1]; exact hnd
      · intro x₀ hx₀; rw [hpk1] at hx₀; exact Nat.lt_succ_of_lt (hlt_mem x₀ hx₀)
      · intro w₀; rw [hpk1]; exact hiff w₀
      · wram_simp; exact hf a (by omega)
    · have hval0 : (if vget ml u = true then 1 else 0) = 0 := ite_eq_right hmu
      have hf3 : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + y.regs idx) :=
        hfit.of_le (by omega)
      have hf4 : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m +
          (pk (y.regs idx)).2.length) := hfit.of_le (by omega)
      have hf5 : Fits w ((pk (y.regs idx)).2.length + 1) := hfit.of_le (by omega)
      have hu_not_mem : u ∉ (pk (y.regs idx)).2 := fun h => Nat.lt_irrefl _ (hlt_mem u h)
      have hpk0 : pk (y.regs idx + 1) =
          (vset (pk (y.regs idx)).1 u (some 0), (pk (y.regs idx)).2 ++ [u]) := by
        rw [htk, hkBfsInitStep, ite_eq_right hmu]
      wram_exec [hby.hbML, hby.hbDist, hby.hbQueue, hby.hzero, hby.hone, hml_u, hval0, hqt,
        hf1, hf2, hf3, hf4, hf5]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], ?_, ?_, by wram_simp [hqh], ?_,
        by wram_simp [hrk], by wram_simp [hrf], ?_, ?_, ?_, fun a ha => ?_⟩, by wram_simp⟩
      · intro w₀
        have := w₀.isLt
        rw [hpk0]
        rcases eq_or_ne w₀ u with rfl | hne
        · wram_simp
          simp [encodeDist]
        · have hne_val : w₀.val ≠ y.regs idx := fun h => hne (Fin.ext h)
          wram_simp
          rw [vget_vset_ne _ _ hne.symm]
          exact hdM w₀
      · intro i hi
        have hlen_eq : (pk (y.regs idx + 1)).2 = (pk (y.regs idx)).2 ++ [u] := by rw [hpk0]
        have hi_lt : i < (pk (y.regs idx)).2.length + 1 := by
          rw [hlen_eq, List.length_append, List.length_singleton] at hi
          exact hi
        by_cases hlt_i : i < (pk (y.regs idx)).2.length
        · wram_simp
          have hget : ((pk (y.regs idx + 1)).2[i]'hi) = ((pk (y.regs idx)).2[i]'hlt_i) := by
            simp only [hlen_eq, List.getElem_append_left hlt_i]
          rw [hget]
          exact hqM i hlt_i
        · have heqi : i = (pk (y.regs idx)).2.length := by omega
          subst heqi
          wram_simp
          have hget : ((pk (y.regs idx + 1)).2[(pk (y.regs idx)).2.length]'hi) = u := by
            simp [hlen_eq]
          simp [hget, u]
      · wram_simp
        rw [hpk0]
        simp
      · rw [hpk0]
        exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton u, fun a ha b hb hab => by
          obtain rfl := List.mem_singleton.mp hb; subst hab; exact hu_not_mem ha⟩
      · intro x₀ hx₀
        rw [hpk0, List.mem_append, List.mem_singleton] at hx₀
        rcases hx₀ with hx₀ | rfl
        · exact Nat.lt_succ_of_lt (hlt_mem x₀ hx₀)
        · exact Nat.lt_succ_self _
      · intro w₀
        rw [hpk0]
        rcases eq_or_ne w₀ u with rfl | hne
        · simp
        · simp [vget_vset_ne _ _ hne.symm, hiff w₀, hne]
      · wram_simp
        exact hf a (by omega)
  obtain ⟨y₂, hl, hPm⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rm (by decide)).trans hb.hrm) hbody
    (x := ((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0) (by simp)
    (by simpa using hP₀)
  obtain ⟨⟨hr₂, hdM₂, hqM₂, hqh₂, hqt₂, hrk₂, hrf₂, hnd₂, _, hiff₂, hf₂⟩, _⟩ := hPm
  have hfull : pk inst.m = p := by
    dsimp only [pk, p]
    rw [List.take_of_length_le (by simp)]
  rw [hfull] at hdM₂ hqM₂ hqt₂ hnd₂ hiff₂
  have hb₂ : BaseRegs inst bOff y₂ := hb.of_eq fun i hi => hr₂ i (by omega)
  have hact : ∃ y₃, ExecWithin w
      (ram[ if qHead < qTail then [ active ← one ] else [ active ← zero ] ] : Code .standard 34)
      y₂ y₃ 3 ∧
      (∀ i : Fin 34, i.val < 20 → y₃.regs i = x.regs i) ∧
      y₃.mem = y₂.mem ∧
      y₃.regs qHead = 0 ∧ y₃.regs qTail = p.2.length ∧ y₃.regs rk = 0 ∧ y₃.regs rfound = 0 ∧
      y₃.regs active = (if p.2 = [] then 0 else 1) := by
    refine WP.exists_execWithin ?_
    by_cases hne : 0 < p.2.length
    · have hne_nil : p.2 ≠ [] := List.ne_nil_of_length_pos hne
      wram_exec [hqh₂, hqt₂, hb₂.hone, hb₂.hzero, hne]
      exact ⟨fun i hi => by wram_simp [hr₂ i hi], rfl, by wram_simp [hqh₂], by wram_simp [hqt₂],
        by wram_simp [hrk₂], by wram_simp [hrf₂], by wram_simp [ite_eq_right hne_nil]⟩
    · have hnil : p.2 = [] := List.eq_nil_of_length_eq_zero (by omega)
      wram_exec [hqh₂, hqt₂, hb₂.hone, hb₂.hzero, hne]
      exact ⟨fun i hi => by wram_simp [hr₂ i hi], rfl, by wram_simp [hqh₂], by wram_simp [hqt₂],
        by wram_simp [hrk₂], by wram_simp [hrf₂], by wram_simp [hnil]⟩
  obtain ⟨y₃, he_act, hr₃, hmem₃, hqh₃, hqt₃, hrk₃, hrf₃, ha₃⟩ := hact
  refine ⟨y₃, (he₁.seq (he₀.seq (hl.seq he_act))).mono (by simp; omega), hr₃,
    hmem₃ ▸ hdM₂, hmem₃ ▸ hqM₂, hqh₃, hqt₃, hrk₃, hrf₃, ha₃, hnd₂, hiff₂,
    fun a ha => (congrFun hmem₃ a).trans (hf₂ a (by omega))⟩

private def bfsEdgeBody : Code .standard 34 := ram[
  addr ← bEdgesReg + idx; val ← *addr;
  addr ← bColMateReg + val; val2 ← *addr;
  if val2 = rm then [ rfound ← one ] else [
    addr ← bDistReg + val2; tmp ← *addr;
    if tmp = zero then [
      tmp ← rk + two;
      addr ← bDistReg + val2; *addr ← tmp;
      addr ← bQueueReg + qTail; *addr ← val2;
      qTail ← qTail + one
    ] else [ tmp ← zero ]
  ];
  idx ← idx + one ]

private def bfsVertexBody : Code .standard 34 :=
  .seq (ram[
    addr ← bQueueReg + qHead; val ← *addr;
    qHead ← qHead + one;
    addr ← bOffReg + val; idx ← *addr;
    addr ← addr + one; limit ← *addr ])
  (.loop (.lt idx limit) bfsEdgeBody)

private def bfsLayerBody : Code .standard 34 :=
  .seq (ram[ layerEnd ← qTail ])
    (.seq (.loop (.lt qHead layerEnd) bfsVertexBody)
      (ram[
        if rfound = one then [ active ← zero ] else [
          if qHead = qTail then [ active ← zero ] else [ rk ← rk + one ]
        ] ]))

private def bfsCode : Code .standard 34 :=
  .seq markMLCode (.seq seedBfsCode (.loop (.eq active one) bfsLayerBody))

private def bfsVertWeight (inst : SparseInstance) (u : Fin inst.m) : ℕ :=
  18 * (inst.adj u).length + 11

private theorem sum_bfsVertWeight (inst : SparseInstance) :
    ∑ u, bfsVertWeight inst u = 18 * inst.numEdges + 11 * inst.m := by
  simp [bfsVertWeight, SparseInstance.numEdges, bipAdjSteps, Finset.sum_add_distrib,
    ← Finset.mul_sum, Finset.sum_const, Nat.mul_comm]

private theorem exec_bfsEdgeLoop {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} (j qh le : ℕ)
    (u : Fin inst.m) (s : HKBfsState inst.m) (queued : List (Fin inst.m))
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem)
    (hdM : DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) s.dist x.mem)
    (hq_pre : QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) qh
      queued x.mem)
    (hq_next : QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) le
      s.next x.mem)
    (hle_eq : qh + queued.length = le)
    (hidx : x.regs idx = inst.offset u.val)
    (hlim : x.regs limit = inst.offset (u.val + 1))
    (hrk : x.regs rk = j)
    (hrf : x.regs rfound = (if s.found then 1 else 0))
    (hqh : x.regs qHead = qh)
    (hle : x.regs layerEnd = le)
    (hqt : x.regs qTail = le + s.next.length)
    (hact : x.regs active = 1)
    (hiff : ∀ w₀ : Fin inst.m, vget s.dist w₀ = none → w₀ ∉ s.next)
    (hqt_bound : le + (Finset.univ.filter fun w₀ => vget s.dist w₀ = none).card + s.next.length ≤
      inst.m)
    (hj_le : j ≤ inst.m + 1)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let sF := (inst.adj u).foldl (hkBfsStep inst.graph mate j u) s
    ∃ y, ExecWithin w (.loop (.lt idx limit) bfsEdgeBody) x y (18 * (inst.adj u).length + 2) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) sF.dist y.mem ∧
      QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) qh queued y.mem ∧
      QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) le sF.next y.mem ∧
      y.regs rk = j ∧
      y.regs rfound = (if sF.found then 1 else 0) ∧
      y.regs qHead = qh ∧
      y.regs layerEnd = le ∧
      y.regs qTail = le + sF.next.length ∧
      y.regs active = 1 ∧
      (∀ w₀ : Fin inst.m, vget sF.dist w₀ = none → w₀ ∉ sF.next) ∧
      le + (Finset.univ.filter fun w₀ => vget sF.dist w₀ = none).card + sF.next.length ≤ inst.m ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  intro sF
  let sk (k : ℕ) : HKBfsState inst.m :=
    ((inst.adj u).take (k - inst.offset u.val)).foldl (hkBfsStep inst.graph mate j u) s
  have hoff_succ : inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length :=
    inst.offset_succ u.isLt
  let P (k : ℕ) (y : Data 34) : Prop :=
    inst.offset u.val ≤ k ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      y.regs limit = inst.offset (u.val + 1) ∧
      DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) (sk k).dist y.mem ∧
      QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) qh queued y.mem ∧
      QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) le (sk k).next y.mem ∧
      y.regs rk = j ∧
      y.regs rfound = (if (sk k).found then 1 else 0) ∧
      y.regs qHead = qh ∧
      y.regs layerEnd = le ∧
      y.regs qTail = le + (sk k).next.length ∧
      y.regs active = 1 ∧
      (∀ w₀ : Fin inst.m, vget (sk k).dist w₀ = none → w₀ ∉ (sk k).next) ∧
      le + (Finset.univ.filter fun w₀ => vget (sk k).dist w₀ = none).card + (sk k).next.length ≤
        inst.m ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a)
  have hsk₀ : sk (x.regs idx) = s := by simp [sk, hidx]
  have hP₀ : P (x.regs idx) x := by
    dsimp only [P]
    rw [hsk₀]
    exact ⟨by omega, fun _ _ => rfl, hlim, hdM, hq_pre, hq_next, hrk, hrf, hqh, hle, hqt, hact,
      hiff, hqt_bound, fun _ _ => rfl⟩
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.offset (u.val + 1)) :
      ∃ z, ExecWithin w bfsEdgeBody y z 16 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hge, hr, hlim_y, hdMy, hq_pre_y, hq_next_y, hrk_y, hrf_y, hqh_y, hle_y, hqt_y,
      hact_y, hiff_y, hbound_y, hf_y⟩ := hy
    let t := y.regs idx - inst.offset u.val
    have ht_lt : t < (inst.adj u).length := by dsimp only [t]; omega
    let v : Fin inst.r := (inst.adj u)[t]'ht_lt
    have hv_mem : v ∈ inst.adj u := List.getElem_mem ht_lt
    have hGu : inst.graph (u, v) = true := decide_eq_true hv_mem
    have hsk_step : sk (y.regs idx + 1) = hkBfsStep inst.graph mate j u (sk (y.regs idx)) v := by
      have hsub : y.regs idx + 1 - inst.offset u.val = t + 1 := by dsimp only [t]; omega
      simp only [sk, hsub, List.take_add_one, List.getElem?_eq_getElem ht_lt, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil, v]
      rfl
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hp_eq : y.regs idx = inst.offset u.val + t := by dsimp only [t]; omega
    have hedge_y : y.mem (bOff + inst.m + 1 + y.regs idx) = v.val := by
      rw [hf_y _ (by have := inst.offset_add_lt_numEdges u ht_lt; omega), hp_eq]
      exact hcsr.hedge u ht_lt
    have hmate_v :
        y.mem (bOff + inst.m + 1 + inst.numEdges + v.val) = encodeOptFin (vget mate v) := by
      rw [hf_y _ (by have := v.isLt; omega)]
      exact hmate v
    have hf_edge : Fits w (bOff + inst.m + 1 + y.regs idx) :=
      hfit.of_le (by have := inst.offset_add_lt_numEdges u ht_lt; omega)
    have hf_col : Fits w (bOff + inst.m + 1 + inst.numEdges + v.val) :=
      hfit.of_le (by have := v.isLt; omega)
    have hf_idx1 : Fits w (y.regs idx + 1) :=
      hfit.of_le (by have := inst.offset_le_numEdges (u.val + 1); omega)
    refine WP.exists_execWithin ?_
    unfold bfsEdgeBody
    cases hmv : vget mate v with
    | none =>
      have henc : encodeOptFin (vget mate v) = inst.m := by simp [hmv, encodeOptFin]
      wram_exec [hby.hbEdges, hby.hbColMate, hby.hrm, hby.hone, hedge_y, hmate_v, henc,
        hf_edge, hf_col, hf_idx1]
      refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], by wram_simp [hlim_y], ?_,
        ?_, ?_, by wram_simp [hrk_y], ?_, by wram_simp [hqh_y], by wram_simp [hle_y],
        ?_, by wram_simp [hact_y], ?_, ?_, fun a ha => by wram_simp [hf_y a ha]⟩, by wram_simp⟩
      · wram_simp; rw [hsk_step]; simpa [hkBfsStep, hGu, hmv] using hdMy
      · wram_simp; exact hq_pre_y
      · wram_simp; rw [hsk_step]; simpa [hkBfsStep, hGu, hmv] using hq_next_y
      · wram_simp; rw [hsk_step]; simp [hkBfsStep, hGu, hmv]
      · wram_simp; rw [hsk_step]; simpa [hkBfsStep, hGu, hmv] using hqt_y
      · rw [hsk_step]; simpa [hkBfsStep, hGu, hmv] using hiff_y
      · rw [hsk_step]; simpa [hkBfsStep, hGu, hmv] using hbound_y
    | some w₀ =>
      have henc : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
      have hw_ne : w₀.val ≠ inst.m := ne_of_lt w₀.isLt
      have hdist_w : y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + w₀.val) =
          encodeDist (vget (sk (y.regs idx)).dist w₀) :=
        hdMy w₀
      have hf_dw : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + w₀.val) :=
        hfit.of_le (by have := w₀.isLt; omega)
      cases hdw : vget (sk (y.regs idx)).dist w₀ with
      | none =>
        have henc_d : encodeDist (vget (sk (y.regs idx)).dist w₀) = 0 := by
          simp [hdw, encodeDist]
        have hw_in_filt : w₀ ∈ Finset.univ.filter
            (fun x₀ => vget (sk (y.regs idx)).dist x₀ = none) := by simp [hdw]
        have hpos_card : 1 ≤ (Finset.univ.filter
            (fun x₀ => vget (sk (y.regs idx)).dist x₀ = none)).card :=
          Finset.card_pos.mpr ⟨w₀, hw_in_filt⟩
        have hqt_lt_m : le + (sk (y.regs idx)).next.length < inst.m := by omega
        have hf_j2 : Fits w (j + 2) := hfit.of_le (by omega)
        have hf_qw : Fits w
            (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m +
              (le + (sk (y.regs idx)).next.length)) :=
          hfit.of_le (by omega)
        have hf_qt1 : Fits w (le + (sk (y.regs idx)).next.length + 1) :=
          hfit.of_le (by omega)
        wram_exec [hby.hbEdges, hby.hbColMate, hby.hbDist, hby.hbQueue, hby.hrm, hby.hzero,
          hby.hone, hby.htwo, hrk_y, hqt_y, hedge_y, hmate_v, henc, hw_ne, hdist_w, henc_d,
          hf_edge, hf_col, hf_dw, hf_j2, hf_qw, hf_qt1, hf_idx1]
        have hfilt_eq : Finset.univ.filter
            (fun x₀ => vget (vset (sk (y.regs idx)).dist w₀ (some (j + 1))) x₀ = none) =
            (Finset.univ.filter (fun x₀ => vget (sk (y.regs idx)).dist x₀ = none)).erase w₀ := by
          ext x₀
          rcases eq_or_ne x₀ w₀ with rfl | hne
          · simp
          · simp [hne, vget_vset_ne _ _ hne.symm]
        have hcard_erase :
            (Finset.univ.filter
              (fun x₀ => vget (vset (sk (y.regs idx)).dist w₀ (some (j + 1))) x₀ = none)).card +
              1 =
            (Finset.univ.filter (fun x₀ => vget (sk (y.regs idx)).dist x₀ = none)).card := by
          rw [hfilt_eq]
          exact Finset.card_erase_add_one hw_in_filt
        refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], by wram_simp [hlim_y], ?_,
          ?_, ?_, by wram_simp [hrk_y], ?_, by wram_simp [hqh_y], by wram_simp [hle_y],
          ?_, by wram_simp [hact_y], ?_, ?_, fun a ha => ?_⟩, by wram_simp⟩
        · intro x₀
          have := x₀.isLt
          rw [hsk_step]
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte]
          rcases eq_or_ne x₀ w₀ with rfl | hne
          · wram_simp
            simp [encodeDist]
          · have hne_val : x₀.val ≠ w₀.val := fun h => hne (Fin.ext h)
            wram_simp
            rw [vget_vset_ne _ _ hne.symm]
            exact hdMy x₀
        · intro i hi
          have := w₀.isLt
          wram_simp
          exact hq_pre_y i hi
        · intro i hi
          have := w₀.isLt
          have hlen_next : (sk (y.regs idx + 1)).next = (sk (y.regs idx)).next ++ [w₀] := by
            rw [hsk_step]
            simp [hkBfsStep, hGu, hmv, hdw]
          have hi_lt : i < (sk (y.regs idx)).next.length + 1 := by
            rw [hlen_next, List.length_append, List.length_singleton] at hi
            exact hi
          by_cases hlt_i : i < (sk (y.regs idx)).next.length
          · wram_simp
            have hget : ((sk (y.regs idx + 1)).next[i]'hi) = ((sk (y.regs idx)).next[i]'hlt_i) := by
              simp only [hlen_next, List.getElem_append_left hlt_i]
            rw [hget]
            exact hq_next_y i hlt_i
          · have heqi : i = (sk (y.regs idx)).next.length := by omega
            subst heqi
            wram_simp
            have hget : ((sk (y.regs idx + 1)).next[(sk (y.regs idx)).next.length]'hi) = w₀ := by
              simp [hlen_next]
            simp [hget]
        · wram_simp [hrf_y]; rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw]
        · wram_simp; rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw]; omega
        · intro x₀ hx₀
          rw [hsk_step] at hx₀ ⊢
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte] at hx₀ ⊢
          have hxne : x₀ ≠ w₀ := fun h => by subst h; simp at hx₀
          rw [vget_vset_ne _ _ hxne.symm] at hx₀
          intro hmem
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hiff_y x₀ hx₀ hmem
          · exact hxne (List.mem_singleton.mp hmem)
        · rw [hsk_step]
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte, List.length_append,
            List.length_singleton]
          omega
        · have := w₀.isLt
          wram_simp
          exact hf_y a ha
      | some d₀ =>
        have henc_ne : encodeDist (vget (sk (y.regs idx)).dist w₀) ≠ 0 := by
          simp [hdw, encodeDist]
        wram_exec [hby.hbEdges, hby.hbColMate, hby.hbDist, hby.hrm, hby.hzero, hby.hone,
          hedge_y, hmate_v, henc, hw_ne, hdist_w, henc_ne, hf_edge, hf_col, hf_dw, hf_idx1]
        refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], by wram_simp [hlim_y], ?_,
          ?_, ?_, by wram_simp [hrk_y], ?_, by wram_simp [hqh_y], by wram_simp [hle_y],
          ?_, by wram_simp [hact_y], ?_, ?_, fun a ha => by wram_simp [hf_y a ha]⟩, by wram_simp⟩
        · wram_simp; rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hdMy
        · wram_simp; exact hq_pre_y
        · wram_simp; rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hq_next_y
        · wram_simp [hrf_y]; rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw]
        · wram_simp; rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hqt_y
        · rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hiff_y
        · rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hbound_y
  obtain ⟨y, hl, hPend, _⟩ := ExecWithin.loop_count P (fun y hy => hy.2.2.1) hbody
    (x := x) (by rw [hidx]; omega) hP₀
  have hsk_end : sk (inst.offset (u.val + 1)) = sF := by
    have hsub : inst.offset (u.val + 1) - inst.offset u.val = (inst.adj u).length := by omega
    simp [sk, hsub, List.take_of_length_le (le_refl _), sF]
  dsimp only [P] at hPend
  rw [hsk_end] at hPend
  obtain ⟨_, hr, _, hdM', hq_pre', hq_next', hrk', hrf', hqh', hle', hqt', hact',
    hiff', hbound', hf'⟩ := hPend
  exact ⟨y, hl.mono (by rw [hidx, hoff_succ]; omega), hr, hdM', hq_pre', hq_next',
    hrk', hrf', hqh', hle', hqt', hact', hiff', hbound', hf'⟩

private theorem exec_bfsFrontierLoop {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} (j qh le : ℕ)
    (frontier : List (Fin inst.m)) (s : HKBfsState inst.m)
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem)
    (hdM : DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) s.dist x.mem)
    (hq_pre : QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) qh
      frontier x.mem)
    (hq_next : QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) le
      s.next x.mem)
    (hle_eq : qh + frontier.length = le)
    (hrk : x.regs rk = j)
    (hrf : x.regs rfound = (if s.found then 1 else 0))
    (hqh : x.regs qHead = qh)
    (hle : x.regs layerEnd = le)
    (hqt : x.regs qTail = le + s.next.length)
    (hact : x.regs active = 1)
    (hiff : ∀ w₀ : Fin inst.m, vget s.dist w₀ = none → w₀ ∉ s.next)
    (hqt_bound : le + (Finset.univ.filter fun w₀ => vget s.dist w₀ = none).card + s.next.length ≤
      inst.m)
    (hj_le : j ≤ inst.m + 1)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let sF := hkBfsLayer inst.graph inst.adj mate j frontier s
    ∃ y, ExecWithin w (.loop (.lt qHead layerEnd) bfsVertexBody) x y
        ((frontier.map (bfsVertWeight inst)).sum + 2) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) sF.dist y.mem ∧
      QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) le sF.next y.mem ∧
      y.regs rk = j ∧
      y.regs rfound = (if sF.found then 1 else 0) ∧
      y.regs qHead = le ∧
      y.regs layerEnd = le ∧
      y.regs qTail = le + sF.next.length ∧
      y.regs active = 1 ∧
      (∀ w₀ : Fin inst.m, vget sF.dist w₀ = none → w₀ ∉ sF.next) ∧
      le + (Finset.univ.filter fun w₀ => vget sF.dist w₀ = none).card + sF.next.length ≤ inst.m ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  induction frontier generalizing qh s x with
  | nil =>
    have hc : ¬(Cond.lt qHead layerEnd).Holds x := by
      simp [Cond.holds_lt, hqh, hle, ← hle_eq]
    exact ⟨x, ExecWithin.loop_exit hc, fun _ _ => rfl, hdM, hq_next, hrk, hrf,
      by simp only [List.length_nil] at hle_eq; omega, hle, hqt, hact, hiff, hqt_bound,
      fun _ _ => rfl⟩
  | cons u us ih =>
    have hc : (Cond.lt qHead layerEnd).Holds x := by
      simp only [Cond.holds_lt, hqh, hle]
      simp only [List.length_cons] at hle_eq
      omega
    have hq_u : x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + qh) = u.val := by
      have h0 := hq_pre 0 (by simp)
      simpa using h0
    have hq_us : QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m)
        (qh + 1) us x.mem := fun i hi => by
      have h := hq_pre (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using h
    have hoff_u : x.mem (bOff + u.val) = inst.offset u.val := hcsr.hoff (le_of_lt u.isLt)
    have hoff_u1 : x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
      simpa [Nat.add_assoc] using hcsr.hoff u.isLt
    have hf_qu : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + qh) := by
      simp only [List.length_cons] at hle_eq
      exact hfit.of_le (by omega)
    have hf_qh1 : Fits w (qh + 1) := by
      simp only [List.length_cons] at hle_eq
      exact hfit.of_le (by omega)
    have hf_ou : Fits w (bOff + u.val) := hfit.of_le (by have := u.isLt; omega)
    have hf_ou1 : Fits w (bOff + u.val + 1) := hfit.of_le (by have := u.isLt; omega)
    have hsetup : ∃ x₁, ExecWithin w (ram[
        addr ← bQueueReg + qHead; val ← *addr;
        qHead ← qHead + one;
        addr ← bOffReg + val; idx ← *addr;
        addr ← addr + one; limit ← *addr ] : Code .standard 34) x x₁ 7 ∧
        x₁ = (((((((x.set addr (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m + qh)).set
          val u.val).set qHead (qh + 1)).set
          addr (bOff + u.val)).set idx (inst.offset u.val)).set addr (bOff + u.val + 1)).set
          limit (inst.offset (u.val + 1))) := by
      refine WP.exists_execWithin ?_
      wram_exec [hb.hbQueue, hb.hbOff, hb.hone, hqh, hq_u, hoff_u, hoff_u1,
        hf_qu, hf_qh1, hf_ou, hf_ou1]
      rfl
    obtain ⟨x₁, he_set, hx₁_eq⟩ := hsetup
    have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => by subst hx₁_eq; wram_simp
    obtain ⟨x₂, he_edges, hr₂, hdM₂, hq_us₂, hq_next₂, hrk₂, hrf₂, hqh₂, hle₂, hqt₂, hact₂,
      hiff₂, hbound₂, hf₂⟩ :=
      exec_bfsEdgeLoop j (qh + 1) le u s us x₁ hb₁ (by subst hx₁_eq; exact hcsr)
        (by subst hx₁_eq; exact hmate) (by subst hx₁_eq; exact hdM)
        (by subst hx₁_eq; exact hq_us) (by subst hx₁_eq; exact hq_next)
        (by simp only [List.length_cons] at hle_eq; omega)
        (by subst hx₁_eq; wram_simp) (by subst hx₁_eq; wram_simp)
        (by subst hx₁_eq; wram_simp [hrk]) (by subst hx₁_eq; wram_simp [hrf])
        (by subst hx₁_eq; wram_simp) (by subst hx₁_eq; wram_simp [hle])
        (by subst hx₁_eq; wram_simp [hqt]) (by subst hx₁_eq; wram_simp [hact])
        hiff hqt_bound hj_le hfit
    have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
    have hcsr₂ : CSRMem inst bOff x₂.mem :=
      hcsr.of_outside fun a ha => (hf₂ a (by omega)).trans (by subst hx₁_eq; rfl)
    have hmate₂ : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x₂.mem :=
      fun v => (hf₂ _ (by have := v.isLt; omega)).trans (by subst hx₁_eq; exact hmate v)
    obtain ⟨y, he_rest, hr₃, hdM₃, hq_next₃, hrk₃, hrf₃, hqh₃, hle₃, hqt₃, hact₃,
      hiff₃, hbound₃, hf₃⟩ :=
      ih (qh + 1) _ x₂ hb₂ hcsr₂ hmate₂ hdM₂ hq_us₂ hq_next₂
        (by simp only [List.length_cons] at hle_eq; omega)
        hrk₂ hrf₂ hqh₂ hle₂ hqt₂ hact₂ hiff₂ hbound₂
    refine ⟨y, (ExecWithin.loop_iter hc (he_set.seq he_edges) he_rest).mono ?_,
      fun i hi => (hr₃ i hi).trans ((hr₂ i hi).trans (by subst hx₁_eq; wram_simp)),
      hdM₃, hq_next₃, hrk₃, hrf₃, hqh₃, hle₃, hqt₃, hact₃, hiff₃, hbound₃,
      fun a ha => (hf₃ a ha).trans ((hf₂ a ha).trans (by subst hx₁_eq; rfl))⟩
    simp only [List.map_cons, List.sum_cons, bfsVertWeight]
    omega

private theorem exec_bfsLayersLoop {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
    (fuel j qh : ℕ) (dist : Vector (Option ℕ) inst.m) (frontier : List (Fin inst.m))
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem)
    (hdM : DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) dist x.mem)
    (hq_pre : QueueSlice (bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m) qh
      frontier x.mem)
    (hrk : x.regs rk = j)
    (hrf : x.regs rfound = 0)
    (hqh : x.regs qHead = qh)
    (hqt : x.regs qTail = qh + frontier.length)
    (hact : x.regs active = (if frontier = [] then 0 else 1))
    (hfuel : inst.m + 1 ≤ fuel + qh)
    (hbound : qh + frontier.length + (Finset.univ.filter fun w₀ => vget dist w₀ = none).card ≤
      inst.m)
    (hj_le : j + fuel ≤ inst.m + 1)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let res := hkBfsLoop inst.graph inst.adj mate fuel j dist frontier
    ∃ y, ExecWithin w (.loop (.eq active one) bfsLayerBody) x y
        (10 * fuel + (frontier.map (bfsVertWeight inst)).sum +
          vecPotential (· = none) (bfsVertWeight inst) dist + 2) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) res.dist y.mem ∧
      y.regs rk = res.k ∧
      y.regs rfound = (if res.found then 1 else 0) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  induction fuel generalizing j qh dist frontier x with
  | zero =>
    have hnil : frontier = [] := by
      cases frontier with
      | nil => rfl
      | cons _ _ => simp only [List.length_cons] at hbound; omega
    subst hnil
    have hc : ¬(Cond.eq active one).Holds x := by
      rw [Cond.holds_eq, hact, hb.hone]
      simp
    exact ⟨x, (ExecWithin.loop_exit hc).mono (by omega), fun _ _ => rfl, hdM, hrk, hrf,
      fun _ _ => rfl⟩
  | succ fuel ih =>
    by_cases hnil : frontier = []
    · subst hnil
      have hc : ¬(Cond.eq active one).Holds x := by
        rw [Cond.holds_eq, hact, hb.hone]
        simp
      refine ⟨x, (ExecWithin.loop_exit hc).mono (by omega), fun _ _ => rfl, ?_, ?_, ?_,
        fun _ _ => rfl⟩
      · simpa [hkBfsLoop, hkBfsLayer] using hdM
      · simpa [hkBfsLoop, hkBfsLayer] using hrk
      · simpa [hkBfsLoop, hkBfsLayer] using hrf
    · have hpos_f : 0 < frontier.length := List.length_pos_iff.mpr hnil
      have hc : (Cond.eq active one).Holds x := by
        rw [Cond.holds_eq, hact, hb.hone]
        simp [hnil]
      let le := qh + frontier.length
      have hs₁ : ∃ x₁, ExecWithin w (ram[ layerEnd ← qTail ] : Code .standard 34) x x₁ 1 ∧
          x₁ = x.set layerEnd le := by
        refine WP.exists_execWithin ?_
        wram_exec [hqt]
        rfl
      obtain ⟨x₁, he_le, rfl⟩ := hs₁
      have hb₁ : BaseRegs inst bOff (x.set layerEnd le) := hb.of_eq fun i hi => by wram_simp
      obtain ⟨x₂, he_front, hr₂, hdM₂, hq_next₂, hrk₂, hrf₂, hqh₂, hle₂, hqt₂, hact₂,
        _, hbound₂, hf₂⟩ :=
        exec_bfsFrontierLoop j qh le frontier ⟨dist, [], false⟩ (x.set layerEnd le) hb₁ hcsr
          hmate hdM hq_pre (fun _ hi => by simp at hi) rfl (by wram_simp [hrk])
          (by wram_simp [hrf]; simp) (by wram_simp [hqh]) (by wram_simp)
          (by wram_simp [hqt, le]; simp)
          (by wram_simp [hact, hnil]) (fun _ _ h => nomatch h)
          (by simp only [List.length_nil, Nat.add_zero, le]; exact hbound) (by omega) hfit
      set s := hkBfsLayer inst.graph inst.adj mate j frontier ⟨dist, [], false⟩ with hs_def
      have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
      have hpot := layerFold_potential inst.graph inst.adj mate (bfsVertWeight inst) j frontier
        ⟨dist, [], false⟩
      simp only [List.map_nil, List.sum_nil, Nat.add_zero, ← hs_def] at hpot
      by_cases hsf : s.found = true
      · have hrf_one : x₂.regs rfound = 1 := by simp [hrf₂, hsf]
        have htail : ∃ x₃, ExecWithin w (ram[
            if rfound = one then [ active ← zero ] else [
              if qHead = qTail then [ active ← zero ] else [ rk ← rk + one ] ] ] :
            Code .standard 34) x₂ x₃ 2 ∧
            x₃ = x₂.set active 0 := by
          refine WP.exists_execWithin ?_
          wram_exec [hrf_one, hb₂.hone, hb₂.hzero]
          rfl
        obtain ⟨x₃, he_tail, rfl⟩ := htail
        have hc₃ : ¬(Cond.eq active one).Holds (x₂.set active 0) := by
          rw [Cond.holds_eq]
          have ha0 : (x₂.set active 0).regs active = 0 := by wram_simp
          have ho1 : (x₂.set active 0).regs one = 1 := by wram_simp [hb₂.hone]
          omega
        have he_exit := ExecWithin.loop_exit (body := bfsLayerBody) (w := w) hc₃
        refine ⟨x₂.set active 0,
          (ExecWithin.loop_iter hc (he_le.seq (he_front.seq he_tail)) he_exit).mono (by omega),
          fun i hi => by wram_simp [hr₂ i hi], ?_, ?_, ?_,
          fun a ha => (hf₂ a ha)⟩
        · simpa [hkBfsLoop, ← hs_def, hsf] using hdM₂
        · wram_simp [hrk₂]; simp [hkBfsLoop, ← hs_def, hsf]
        · wram_simp [hrf_one]; simp [hkBfsLoop, ← hs_def, hsf]
      · have hrf_zero : x₂.regs rfound = 0 := by simp [hrf₂, hsf]
        by_cases hs_empty : s.next.isEmpty = true
        · have hs_nil : s.next = [] := List.isEmpty_iff.mp hs_empty
          have hqt_eq_le : x₂.regs qTail = le := by simp [hqt₂, hs_nil]
          have htail : ∃ x₃, ExecWithin w (ram[
              if rfound = one then [ active ← zero ] else [
                if qHead = qTail then [ active ← zero ] else [ rk ← rk + one ] ] ] :
              Code .standard 34) x₂ x₃ 4 ∧
              x₃ = x₂.set active 0 := by
            refine WP.exists_execWithin ?_
            wram_exec [hrf_zero, hb₂.hone, hb₂.hzero, hqh₂, hqt_eq_le]
            rfl
          obtain ⟨x₃, he_tail, rfl⟩ := htail
          have hc₃ : ¬(Cond.eq active one).Holds (x₂.set active 0) := by
            rw [Cond.holds_eq]
            have ha0 : (x₂.set active 0).regs active = 0 := by wram_simp
            have ho1 : (x₂.set active 0).regs one = 1 := by wram_simp [hb₂.hone]
            omega
          have he_exit := ExecWithin.loop_exit (body := bfsLayerBody) (w := w) hc₃
          refine ⟨x₂.set active 0,
            (ExecWithin.loop_iter hc (he_le.seq (he_front.seq he_tail)) he_exit).mono (by omega),
            fun i hi => by wram_simp [hr₂ i hi], ?_, ?_, ?_,
            fun a ha => hf₂ a ha⟩
          · simpa [hkBfsLoop, ← hs_def, hsf, hs_empty] using hdM₂
          · wram_simp [hrk₂]; simp [hkBfsLoop, ← hs_def, hsf, hs_empty]
          · wram_simp [hrf_zero]; simp [hkBfsLoop, ← hs_def, hsf, hs_empty]
        · have hs_nnil : s.next ≠ [] := fun h => hs_empty (by simp [h])
          have hlen_pos : 0 < s.next.length := List.length_pos_iff.mpr hs_nnil
          have hqh_ne_qt : x₂.regs qHead ≠ x₂.regs qTail := by rw [hqh₂, hqt₂]; omega
          have hf_j1 : Fits w (j + 1) := hfit.of_le (by omega)
          have htail : ∃ x₃, ExecWithin w (ram[
              if rfound = one then [ active ← zero ] else [
                if qHead = qTail then [ active ← zero ] else [ rk ← rk + one ] ] ] :
              Code .standard 34) x₂ x₃ 5 ∧
              x₃ = x₂.set rk (j + 1) := by
            refine WP.exists_execWithin ?_
            wram_exec [hrf_zero, hb₂.hone, hrk₂, hqh_ne_qt, hf_j1]
            rfl
          obtain ⟨x₃, he_tail, rfl⟩ := htail
          have hb₃ : BaseRegs inst bOff (x₂.set rk (j + 1)) := hb₂.of_eq fun i hi => by wram_simp
          have hcsr₃ : CSRMem inst bOff (x₂.set rk (j + 1)).mem :=
            hcsr.of_outside fun a ha => hf₂ a (by omega)
          have hmate₃ : MateMem (bOff + inst.m + 1 + inst.numEdges) mate (x₂.set rk (j + 1)).mem :=
            fun v => (hf₂ _ (by have := v.isLt; omega)).trans (hmate v)
          obtain ⟨y, he_rec, hr₄, hdM₄, hrk₄, hrf₄, hf₄⟩ :=
            ih (j + 1) le s.dist s.next (x₂.set rk (j + 1)) hb₃ hcsr₃ hmate₃ hdM₂ hq_next₂
              (by wram_simp) (by wram_simp [hrf_zero]) (by wram_simp [hqh₂])
              (by wram_simp [hqt₂]) (by wram_simp [hact₂, hs_nnil])
              (by omega) (by dsimp only [le] at hbound₂; omega) (by omega)
          refine ⟨y, (ExecWithin.loop_iter hc (he_le.seq (he_front.seq he_tail)) he_rec).mono ?_,
            fun i hi => (hr₄ i hi).trans (by wram_simp [hr₂ i hi]),
            ?_, ?_, ?_, fun a ha => (hf₄ a ha).trans (hf₂ a ha)⟩
          · omega
          · simpa [hkBfsLoop, ← hs_def, hsf, hs_empty] using hdM₄
          · simpa [hkBfsLoop, ← hs_def, hsf, hs_empty] using hrk₄
          · simpa [hkBfsLoop, ← hs_def, hsf, hs_empty] using hrf₄

private theorem exec_bfsCode {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let b := hkBfs inst.graph inst.adj mate
    ∃ y, ExecWithin w bfsCode x y (51 * inst.m + 8 * inst.r + 36 * inst.numEdges + 33) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) b.dist y.mem ∧
      y.regs rk = b.k ∧
      y.regs rfound = (if b.found then 1 else 0) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) → y.mem a = x.mem a) := by
  intro b
  obtain ⟨y₁, he₁, hr₁, hml₁, hf₁⟩ := exec_markMLCode x hb hmate hfit
  have hb₁ : BaseRegs inst bOff y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  obtain ⟨y₂, he₂, hr₂, hdM₂, hqM₂, hqh₂, hqt₂, hrk₂, hrf₂, hact₂, hnd₂, hiff₂, hf₂⟩ :=
    exec_seedBfsCode y₁ hb₁ hml₁ hfit
  set p := (List.finRange inst.m).foldl (hkBfsInitStep (hkMatchedLeft mate))
    (Vector.replicate inst.m none, [])
  have hb₂ : BaseRegs inst bOff y₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
  have hcsr₂ : CSRMem inst bOff y₂.mem :=
    hcsr.of_outside fun a ha => (hf₂ a (by omega)).trans (hf₁ a (by omega))
  have hmate₂ : MateMem (bOff + inst.m + 1 + inst.numEdges) mate y₂.mem :=
    fun v => (hf₂ _ (by have := v.isLt; omega)).trans
      ((hf₁ _ (by have := v.isLt; omega)).trans (hmate v))
  have hcard_bound :
      p.2.length + (Finset.univ.filter fun w₀ => vget p.1 w₀ = none).card ≤ inst.m := by
    have hlen_eq : p.2.length = (Finset.univ.filter fun w₀ => vget p.1 w₀ ≠ none).card := by
      rw [← List.toFinset_card_of_nodup hnd₂]
      congr 1
      ext w₀
      simp [hiff₂ w₀]
    rw [hlen_eq]
    have hdisj : Disjoint (Finset.univ.filter fun w₀ : Fin inst.m => vget p.1 w₀ ≠ none)
        (Finset.univ.filter fun w₀ : Fin inst.m => vget p.1 w₀ = none) :=
      Finset.disjoint_filter.mpr fun _ _ h₁ h₂ => h₁ h₂
    have hle_univ := Finset.card_le_univ
      ((Finset.univ.filter fun w₀ : Fin inst.m => vget p.1 w₀ ≠ none) ∪
        (Finset.univ.filter fun w₀ : Fin inst.m => vget p.1 w₀ = none))
    rw [Finset.card_union_of_disjoint hdisj, Fintype.card_fin] at hle_univ
    exact hle_univ
  obtain ⟨y₃, he₃, hr₃, hdM₃, hrk₃, hrf₃, hf₃⟩ :=
    exec_bfsLayersLoop (inst.m + 1) 0 0 p.1 p.2 y₂ hb₂ hcsr₂ hmate₂ hdM₂ hqM₂ hrk₂ hrf₂ hqh₂
      (by simpa using hqt₂) hact₂ (by omega) (by simpa using hcard_bound) (by omega) hfit
  have hinit_pot :
      vecPotential (fun x : Option ℕ => x = none) (bfsVertWeight inst) p.1 +
          (p.2.map (bfsVertWeight inst)).sum ≤
        vecPotential (fun x : Option ℕ => x = none) (bfsVertWeight inst)
            (Vector.replicate inst.m (none : Option ℕ)) +
          ((List.finRange inst.m).map (bfsVertWeight inst)).sum := by
    simpa [p] using bfsInit_potential (hkMatchedLeft mate) (bfsVertWeight inst)
      (List.finRange inst.m) (Vector.replicate inst.m (none : Option ℕ), [])
  have hrep_le := (vecPotential_le_sum (p := fun x : Option ℕ => x = none) (bfsVertWeight inst)
    (Vector.replicate inst.m (none : Option ℕ))).trans_eq (sum_bfsVertWeight inst)
  have hfin_sum : ((List.finRange inst.m).map (bfsVertWeight inst)).sum =
      18 * inst.numEdges + 11 * inst.m := by
    rw [← Fin.sum_univ_def]
    exact sum_bfsVertWeight inst
  refine ⟨y₃, (he₁.seq (he₂.seq he₃)).mono ?_,
    fun i hi => (hr₃ i hi).trans ((hr₂ i hi).trans (hr₁ i (by omega))),
    hdM₃, hrk₃, hrf₃,
    fun a ha => (hf₃ a (by omega)).trans ((hf₂ a (by omega)).trans (hf₁ a (by omega)))⟩
  omega


/-! ## Section 3: Iterative explicit-stack DFS phase (`dfsPhaseCode`) and `coreCode` -/

private theorem hkDfsLevel_acc {m r : ℕ} (G : Fin m × Fin r → Bool)
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m)
    (accept : Bool) (i : ℕ)
    (next : Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r)))
    (hnext : ∀ w₀ vis₀ acc₀, next w₀ vis₀ acc₀ =
      ((next w₀ vis₀ []).1, (next w₀ vis₀ []).2.map (· ++ acc₀)))
    (u : Fin m) (vs : List (Fin r)) (vis : Vector Bool r) (acc₀ : List (Fin m × Fin r)) :
    hkDfsLevel G mate dist accept i next u vs vis acc₀ =
      ((hkDfsLevel G mate dist accept i next u vs vis []).1,
        (hkDfsLevel G mate dist accept i next u vs vis []).2.map (· ++ acc₀)) := by
  induction vs generalizing vis with
  | nil => rfl
  | cons v vs ih =>
    dsimp only [hkDfsLevel]
    split
    · cases hm : vget mate v with
      | none =>
        dsimp only
        split
        · simp
        · exact ih vis
      | some w₀ =>
        dsimp only
        split
        · rw [hnext w₀ (vset vis v true) acc₀]
          cases h2 : (next w₀ (vset vis v true) []).2 with
          | none => exact ih (next w₀ (vset vis v true) []).1
          | some q => simp
        · exact ih vis
    · exact ih vis

private theorem hkDfs_acc {m r : ℕ} (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) :
    ∀ (f i : ℕ) (u : Fin m) (vis : Vector Bool r) (acc₀ : List (Fin m × Fin r)),
      hkDfs G adj mate dist f i u vis acc₀ =
        ((hkDfs G adj mate dist f i u vis []).1,
          (hkDfs G adj mate dist f i u vis []).2.map (· ++ acc₀))
  | 0, i, u, vis, acc₀ =>
    hkDfsLevel_acc G mate dist true i (fun _ vis _ => (vis, none)) (fun _ _ _ => rfl)
      u (adj u) vis acc₀
  | f + 1, i, u, vis, acc₀ =>
    hkDfsLevel_acc G mate dist false i (hkDfs G adj mate dist f (i + 1))
      (hkDfs_acc G adj mate dist f (i + 1)) u (adj u) vis acc₀

private def dfsNext {m r : ℕ} (G : Fin m × Fin r → Bool) (adj : Fin m → List (Fin r))
    (mate : Vector (Option (Fin m)) r) (dist : Vector (Option ℕ) m) :
    ℕ → ℕ → Fin m → Vector Bool r → List (Fin m × Fin r) →
      Vector Bool r × Option (List (Fin m × Fin r))
  | 0, _, _, vis, _ => (vis, none)
  | f + 1, i, w₀, vis, acc₀ => hkDfs G adj mate dist f (i + 1) w₀ vis acc₀

private theorem hkDfs_eq_dfsLevel {m r : ℕ} (G : Fin m × Fin r → Bool)
    (adj : Fin m → List (Fin r)) (mate : Vector (Option (Fin m)) r)
    (dist : Vector (Option ℕ) m) (f i : ℕ) (u : Fin m) (vis : Vector Bool r)
    (acc₀ : List (Fin m × Fin r)) :
    hkDfs G adj mate dist f i u vis acc₀ =
      hkDfsLevel G mate dist (decide (f = 0)) i
        (dfsNext G adj mate dist f i) u (adj u) vis acc₀ := by
  cases f <;> rfl

private def VisCovers {m r : ℕ} (vis : Vector Bool r) (ps : List (Fin m × Fin r)) : Prop :=
  (ps.map Prod.snd).Nodup ∧ ∀ e ∈ ps, vget vis e.2 = true

private theorem VisCovers.mono {m r : ℕ} {vis vis' : Vector Bool r} {ps : List (Fin m × Fin r)}
    (h : VisCovers vis ps) (hle : ∀ x, vget vis x = true → vget vis' x = true) :
    VisCovers vis' ps :=
  ⟨h.1, fun e he => hle e.2 (h.2 e he)⟩

private theorem VisCovers.snoc {m r : ℕ} {vis : Vector Bool r} {ps : List (Fin m × Fin r)}
    (h : VisCovers vis ps) (u : Fin m) {v : Fin r} (hv : vget vis v = false) :
    VisCovers (vset vis v true) (ps ++ [(u, v)]) := by
  have hv_not : v ∉ ps.map Prod.snd := by
    rw [List.mem_map]
    rintro ⟨e, he, rfl⟩
    exact Bool.false_ne_true (hv.symm.trans (h.2 e he))
  refine ⟨?_, fun e he => ?_⟩
  · rw [List.map_append, List.map_singleton]
    exact List.nodup_append.mpr ⟨h.1, List.nodup_singleton v, fun a ha b hb hab => by
      obtain rfl := List.mem_singleton.mp hb
      subst hab
      exact hv_not ha⟩
  · rcases List.mem_append.mp he with he | he
    · have hne : e.2 ≠ v := fun heq => hv_not (heq ▸ List.mem_map_of_mem he)
      rw [vget_vset_ne _ _ hne.symm]
      exact h.2 e he
    · obtain rfl := List.mem_singleton.mp he
      exact vget_vset_self vis v true

private theorem VisCovers.length_le {m r : ℕ} {vis : Vector Bool r} {ps : List (Fin m × Fin r)}
    (h : VisCovers vis ps) : ps.length ≤ r := by
  have hcard := h.1.length_le_card
  simpa using hcard

private def dfsVertWeight (inst : SparseInstance) (mate : Vector (Option (Fin inst.m)) inst.r)
    (v : Fin inst.r) : ℕ :=
  38 * hkDfsCost inst.adj mate v + 14

private def dfsPot (inst : SparseInstance) (mate : Vector (Option (Fin inst.m)) inst.r)
    (vis : Vector Bool inst.r) : ℕ :=
  vecPotential (fun b : Bool => b = false) (dfsVertWeight inst mate) vis

private theorem dfsPot_vset_true {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {vis : Vector Bool inst.r} {v : Fin inst.r}
    (hv : vget vis v = false) :
    dfsPot inst mate (vset vis v true) + dfsVertWeight inst mate v = dfsPot inst mate vis :=
  vecPotential_vset_add hv (by simp)

private theorem dfsPot_replicate_le {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
    (hM : IsMatching inst.graph (mateMatching mate)) :
    dfsPot inst mate (Vector.replicate inst.r false) ≤ 38 * inst.numEdges + 14 * inst.r := by
  have hcost := vecPotential_replicate_le (adj := inst.adj) hM
  have heq : dfsPot inst mate (Vector.replicate inst.r false) =
      38 * vecPotential (fun b : Bool => b = false) (hkDfsCost inst.adj mate)
        (Vector.replicate inst.r false) +
      ∑ _ ∈ Finset.univ.filter
        (fun v : Fin inst.r => vget (Vector.replicate inst.r false) v = false), 14 := by
    simp only [dfsPot, vecPotential, dfsVertWeight, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h14 : (∑ _ ∈ Finset.univ.filter
      (fun v : Fin inst.r => vget (Vector.replicate inst.r false) v = false), 14) ≤
      14 * inst.r := by
    refine (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)).trans ?_
    simp [Nat.mul_comm]
  rw [heq]
  change _ ≤ 38 * bipAdjSteps inst.adj + 14 * inst.r
  omega

private theorem hkDfsLevel_pure_props {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    (f d : ℕ)
    (hnext : ∀ (w₀ : Fin inst.m) (vis₀ : Vector Bool inst.r)
        (ps : List (Fin inst.m × Fin inst.r)),
      VisCovers vis₀ ps →
      (∀ x, vget vis₀ x = true →
        vget (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).1 x = true) ∧
      dfsPot inst mate (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).1 ≤
        dfsPot inst mate vis₀ ∧
      match (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).2 with
      | some qw =>
        VisCovers (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).1 (ps ++ qw) ∧
          qw.length = f
      | none =>
        VisCovers (dfsNext inst.graph inst.adj mate dist f d w₀ vis₀ []).1 ps)
    (u : Fin inst.m) (vs : List (Fin inst.r)) (vis : Vector Bool inst.r)
    (ps : List (Fin inst.m × Fin inst.r)) (hcovers : VisCovers vis ps) :
    (∀ x, vget vis x = true →
      vget (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 x = true) ∧
      dfsPot inst mate (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 ≤ dfsPot inst mate vis ∧
      match (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
          (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).2 with
      | some q =>
        VisCovers (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
          (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 (ps ++ q) ∧
          q.length = f + 1
      | none =>
        VisCovers (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
          (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 ps := by
  induction vs generalizing vis ps with
  | nil =>
    exact ⟨fun _ h => h, le_refl _, hcovers⟩
  | cons v vs ih =>
    dsimp only [hkDfsLevel]
    split
    · next hc =>
      cases hm : vget mate v with
      | none =>
        dsimp only
        split
        · next ha =>
          have hf0 : f = 0 := of_decide_eq_true ha
          subst hf0
          dsimp only
          have hpot := dfsPot_vset_true (inst := inst) (mate := mate) hc.2
          exact ⟨fun x hx => by
            rcases eq_or_ne x v with rfl | hne
            · simp
            · rwa [vget_vset_ne _ _ hne.symm],
            by omega, hcovers.snoc u hc.2, rfl⟩
        · exact ih vis ps hcovers
      | some w₀ =>
        dsimp only
        split
        · next hb =>
          have hcov1 : VisCovers (vset vis v true) (ps ++ [(u, v)]) := hcovers.snoc u hc.2
          have hpot1 := dfsPot_vset_true (inst := inst) (mate := mate) hc.2
          obtain ⟨hmono_w, hpot_w, hres_w⟩ := hnext w₀ (vset vis v true) (ps ++ [(u, v)]) hcov1
          have hmono_step : ∀ x, vget vis x = true →
              vget (dfsNext inst.graph inst.adj mate dist f d w₀ (vset vis v true) []).1 x =
                true := fun x hx =>
            hmono_w x (by
              rcases eq_or_ne x v with rfl | hne
              · exact vget_vset_self vis x true
              · rwa [vget_vset_ne _ _ hne.symm])
          cases hrw : (dfsNext inst.graph inst.adj mate dist f d w₀ (vset vis v true) []).2 with
          | some qw =>
            rw [hrw] at hres_w
            dsimp only
            have hf_ne : f ≠ 0 := fun h => by simp [h] at hb
            refine ⟨hmono_step, by omega, ?_, ?_⟩
            · simpa [List.append_assoc] using hres_w.1
            · have hqw_len := hres_w.2
              simp only [List.length_cons]
              omega
          | none =>
            rw [hrw] at hres_w
            dsimp only
            have hcov_back : VisCovers
                (dfsNext inst.graph inst.adj mate dist f d w₀ (vset vis v true) []).1 ps :=
              hcovers.mono hmono_step
            obtain ⟨hm2, hp2, hr2⟩ := ih _ ps hcov_back
            exact ⟨fun x hx => hm2 x (hmono_step x hx), by omega, hr2⟩
        · exact ih vis ps hcovers
    · exact ih vis ps hcovers

private theorem hkDfs_pure_props {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m} :
    ∀ (f d : ℕ) (u : Fin inst.m) (vis : Vector Bool inst.r)
      (ps : List (Fin inst.m × Fin inst.r)),
      VisCovers vis ps →
      (∀ x, vget vis x = true →
        vget (hkDfs inst.graph inst.adj mate dist f d u vis []).1 x = true) ∧
        dfsPot inst mate (hkDfs inst.graph inst.adj mate dist f d u vis []).1 ≤
          dfsPot inst mate vis ∧
        match (hkDfs inst.graph inst.adj mate dist f d u vis []).2 with
        | some q =>
          VisCovers (hkDfs inst.graph inst.adj mate dist f d u vis []).1 (ps ++ q) ∧
            q.length = f + 1
        | none =>
          VisCovers (hkDfs inst.graph inst.adj mate dist f d u vis []).1 ps
  | 0, d, u, vis, ps, hcovers => by
    rw [hkDfs_eq_dfsLevel]
    exact hkDfsLevel_pure_props 0 d (fun _ vis₀ ps₀ hc => ⟨fun _ h => h, le_refl _, hc⟩)
      u (inst.adj u) vis ps hcovers
  | f + 1, d, u, vis, ps, hcovers => by
    rw [hkDfs_eq_dfsLevel]
    exact hkDfsLevel_pure_props (f + 1) d
      (fun w₀ vis₀ ps₀ hc => hkDfs_pure_props f (d + 1) w₀ vis₀ ps₀ hc)
      u (inst.adj u) vis ps hcovers

private theorem hkDfsRoots_nodup_snd {inst : SparseInstance}
    (mate : Vector (Option (Fin inst.m)) inst.r) (dist : Vector (Option ℕ) inst.m) (k : ℕ) :
    ∀ (us : List (Fin inst.m)) (vis : Vector Bool inst.r)
      (acc₀ : List (Fin inst.m × Fin inst.r)),
      VisCovers vis acc₀ →
      ((hkDfsRoots inst.graph inst.adj mate dist k us vis acc₀).map Prod.snd).Nodup := by
  intro us
  induction us with
  | nil => intro _ _ hc; exact hc.1
  | cons u us ih =>
    intro vis acc₀ hc
    simp only [hkDfsRoots]
    split_ifs with hd
    · rw [hkDfs_acc]
      obtain ⟨_, _, hres⟩ := hkDfs_pure_props (inst := inst) (mate := mate) (dist := dist)
        k 0 u vis acc₀ hc
      cases hr : (hkDfs inst.graph inst.adj mate dist k 0 u vis []).2 with
      | none =>
        rw [hr] at hres
        exact ih _ acc₀ hres
      | some q =>
        rw [hr] at hres
        dsimp only [Option.map, Option.getD]
        have hperm : (q ++ acc₀).Perm (acc₀ ++ q) := List.perm_append_comm
        have hcov' : VisCovers (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 (q ++ acc₀) :=
          ⟨(hperm.map Prod.snd).nodup_iff.mpr hres.1.1, fun e he => hres.1.2 e (hperm.subset he)⟩
        exact ih _ (q ++ acc₀) hcov'
    · exact ih vis acc₀ hc

private def AugMem {m r : ℕ} (bAugU bAugV : ℕ) (ps : List (Fin m × Fin r)) (mem : ℕ → ℕ) : Prop :=
  ∀ i : ℕ, (hi : i < ps.length) →
    mem (bAugU + i) = (ps[i]'hi).1.val ∧ mem (bAugV + i) = (ps[i]'hi).2.val

private def copyAugBody : Code .standard 34 := ram[
  addr ← bStackUReg + idx; val ← *addr;
  addr ← bAugUReg + augLen; *addr ← val;
  addr ← bStackVReg + idx; val ← *addr;
  addr ← bAugVReg + augLen; *addr ← val;
  augLen ← augLen + one;
  idx ← idx + one ]

private def copyAugCode : Code .standard 34 :=
  .seq (ram[ limit ← rk + one; idx ← #0 ])
    (.loop (.lt idx limit) copyAugBody)

private theorem exec_copyAugCode {w bOff k : ℕ} {inst : SparseInstance}
    (augPairs stackPairs : List (Fin inst.m × Fin inst.r))
    (x : Data 34) (hb : BaseRegs inst bOff x)
    (hrk : x.regs rk = k)
    (haugLen : x.regs augLen = augPairs.length)
    (hact : x.regs active = 1)
    (hlen_st : stackPairs.length = k + 1)
    (hk_le : k ≤ inst.m + 1)
    (haug_fit : augPairs.length + (k + 1) ≤ inst.r)
    (haugM : AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
      (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6) augPairs x.mem)
    (hstackM : ∀ i : ℕ, (hi : i < k + 1) →
      x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
        (stackPairs[i]'(by omega)).1.val ∧
      x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
        (stackPairs[i]'(by omega)).2.val)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w copyAugCode x y (12 * (k + 1) + 4) ∧
      (∀ i : Fin 34, i.val < 26 → y.regs i = x.regs i) ∧
      y.regs active = 1 ∧
      y.regs augLen = (augPairs ++ stackPairs).length ∧
      AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
        (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
        (augPairs ++ stackPairs) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a) := by
  have hf_k1 : Fits w (k + 1) := hfit.of_le (by omega)
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ limit ← rk + one; idx ← #0 ] : Code .standard 34) x s₀ 2 ∧
      s₀ = (x.set limit (k + 1)).set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [hrk, hb.hone, hf_k1]
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let P (t : ℕ) (y : Data 34) : Prop :=
    t ≤ k + 1 ∧
      (∀ i : Fin 34, i.val < 26 → y.regs i = x.regs i) ∧
      y.regs active = 1 ∧
      y.regs limit = k + 1 ∧
      y.regs augLen = augPairs.length + t ∧
      AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
        (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
        (augPairs ++ stackPairs.take t) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a)
  have hP₀ : P 0 ((x.set limit (k + 1)).set idx 0) := by
    refine ⟨Nat.zero_le _, fun i hi => by wram_simp, by wram_simp [hact], by wram_simp,
      by wram_simp [haugLen], ?_, fun _ _ => rfl⟩
    simpa using haugM
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < k + 1) :
      ∃ z, ExecWithin w copyAugBody y z 10 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hact_y, hlim_y, hal_y, haug_y, hf_y⟩ := hy
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hlt_st : y.regs idx < stackPairs.length := by omega
    have hsu : y.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + y.regs idx) =
        (stackPairs[y.regs idx]'hlt_st).1.val := by
      rw [hf_y _ (by omega)]
      exact (hstackM (y.regs idx) hlt).1
    have hsv :
        y.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + y.regs idx) =
          (stackPairs[y.regs idx]'hlt_st).2.val := by
      rw [hf_y _ (by omega)]
      exact (hstackM (y.regs idx) hlt).2
    have hf1 : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + y.regs idx) :=
      hfit.of_le (by omega)
    have hf2 : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 +
        (augPairs.length + y.regs idx)) := hfit.of_le (by omega)
    have hf3 :
        Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + y.regs idx) :=
      hfit.of_le (by omega)
    have hf4 : Fits w (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6 +
        (augPairs.length + y.regs idx)) := hfit.of_le (by omega)
    have hf5 : Fits w (augPairs.length + y.regs idx + 1) := hfit.of_le (by omega)
    have hf6 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold copyAugBody
    wram_exec [hby.hbStackU, hby.hbAugU, hby.hbStackV, hby.hbAugV, hby.hone, hal_y,
      hsu, hsv, hf1, hf2, hf3, hf4, hf5, hf6]
    have htake_eq : augPairs ++ stackPairs.take (y.regs idx + 1) =
        (augPairs ++ stackPairs.take (y.regs idx)) ++ [stackPairs[y.regs idx]'hlt_st] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt_st, Option.toList_some,
        ← List.append_assoc]
    refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], by wram_simp [hact_y],
      by wram_simp [hlim_y], by wram_simp; omega, ?_, fun a ha => ?_⟩, by wram_simp⟩
    · intro i hi
      have hlen_old : (augPairs ++ stackPairs.take (y.regs idx)).length =
          augPairs.length + y.regs idx := by
        rw [List.length_append, List.length_take_of_le (by omega)]
      have hi_lt : i < augPairs.length + y.regs idx + 1 := by
        rw [htake_eq, List.length_append, List.length_singleton, hlen_old] at hi
        exact hi
      by_cases hlt_i : i < augPairs.length + y.regs idx
      · have hlt_old : i < (augPairs ++ stackPairs.take (y.regs idx)).length := by omega
        have hget : ((augPairs ++ stackPairs.take (y.regs idx + 1))[i]'hi) =
            ((augPairs ++ stackPairs.take (y.regs idx))[i]'hlt_old) := by
          simp only [htake_eq, List.getElem_append_left hlt_old]
        rw [hget]
        wram_simp
        exact haug_y i hlt_old
      · have heqi : i = augPairs.length + y.regs idx := by omega
        subst heqi
        have hget :
            ((augPairs ++ stackPairs.take (y.regs idx + 1))[augPairs.length + y.regs idx]'hi) =
              stackPairs[y.regs idx]'hlt_st := by
          simp only [htake_eq]
          rw [List.getElem_append_right (by omega)]
          simp [hlen_old]
        rw [hget]
        wram_simp
    · wram_simp
      exact hf_y a ha
  obtain ⟨y, hl, hPend, _⟩ := ExecWithin.loop_count P (fun y hy => hy.2.2.2.1) hbody
    (x := (x.set limit (k + 1)).set idx 0) (by simp) (by simpa using hP₀)
  obtain ⟨_, hr, hact', _, hal', haug', hf'⟩ := hPend
  have htake_full : stackPairs.take (k + 1) = stackPairs :=
    List.take_of_length_le (by omega)
  rw [htake_full] at haug'
  refine ⟨y, (he₀.seq hl).mono (by simp; omega), hr, hact',
    by rw [List.length_append, hlen_st]; exact hal', haug', hf'⟩

private def dfsStepBody : Code .standard 34 := ram[
  addr ← bStackUReg + rd; idx ← *addr;
  addr ← bOffReg + idx; addr ← addr + one; limit ← *addr;
  addr ← bStackPosReg + rd; val2 ← *addr;
  if val2 < limit then [
    tmp ← val2 + one;
    addr ← bStackPosReg + rd; *addr ← tmp;
    addr ← bEdgesReg + val2; val ← *addr;
    addr ← bVisReg + val; tmp ← *addr;
    if tmp = zero then [
      addr ← bColMateReg + val; val2 ← *addr;
      if val2 = rm then [
        if rd = rk then [
          addr ← bVisReg + val; *addr ← one;
          addr ← bStackVReg + rd; *addr ← val;
          ⟪copyAugCode⟫;
          active ← zero
        ] else [ tmp ← zero ]
      ] else [
        if rd < rk then [
          addr ← bDistReg + val2; tmp ← *addr;
          idx ← rd + two;
          if tmp = idx then [
            addr ← bVisReg + val; *addr ← one;
            addr ← bStackVReg + rd; *addr ← val;
            rd ← rd + one;
            addr ← bStackUReg + rd; *addr ← val2;
            addr ← bOffReg + val2; tmp ← *addr;
            addr ← bStackPosReg + rd; *addr ← tmp
          ] else [ tmp ← zero ]
        ] else [ tmp ← zero ]
      ]
    ] else [ tmp ← zero ]
  ] else [
    if rd = zero then [ active ← zero ] else [ rd ← rd - one ]
  ] ]

private def dfsLoop : Code .standard 34 :=
  .loop (.eq active one) dfsStepBody

/-- Bundled state invariant at stack depth `d` during `dfsLoop`. -/
private structure DfsFrame (inst : SparseInstance) (bOff k : ℕ)
    (mate : Vector (Option (Fin inst.m)) inst.r) (dist : Vector (Option ℕ) inst.m)
    (augPairs : List (Fin inst.m × Fin inst.r)) (d : ℕ)
    (path : List (Fin inst.m × Fin inst.r)) (u : Fin inst.m) (pre : List (Fin inst.r))
    (vis : Vector Bool inst.r) (x : Data 34) : Prop where
  hplen : path.length = d
  hcovers : VisCovers vis (augPairs ++ path)
  hb : BaseRegs inst bOff x
  hcsr : CSRMem inst bOff x.mem
  hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem
  hdM : DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) dist x.mem
  hvisM : VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) vis x.mem
  haugM : AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
    (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6) augPairs x.mem
  hstack : ∀ i : ℕ, (hi : i < d) →
    x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
      (path[i]'(by omega)).1.val ∧
    x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
      (path[i]'(by omega)).2.val
  hsu : x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + d) = u.val
  hsp : x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) =
    inst.offset u.val + pre.length
  hrk : x.regs rk = k
  hrd : x.regs rd = d
  hal : x.regs augLen = augPairs.length
  hact : x.regs active = 1

private def DfsSubtreeOutside (inst : SparseInstance) (bOff d a : ℕ) : Prop :=
  ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m) ∧
    ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + (d + 1) ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2) ∧
    ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + d ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4) ∧
    ¬(bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d ≤ a ∧
      a < bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)

private theorem exec_dfsStep_pop {w bOff k d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m} {pre : List (Fin inst.r)}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_le : d ≤ k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w dfsStepBody x y 12 ∧
      (∀ i : Fin 34, i.val < 25 → y.regs i = x.regs i) ∧
      y.regs augLen = augPairs.length ∧
      (if d = 0 then y.regs active = 0 else y.regs active = 1 ∧ y.regs rd = d - 1) ∧
      y.mem = x.mem := by
  have hu_lt := u.isLt
  have hoff_succ : inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length :=
    inst.offset_succ hu_lt
  have hpre_len : pre.length = (inst.adj u).length := by rw [hsplit]
  have hf_su : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + d) :=
    hfit.of_le (by omega)
  have hf_ou : Fits w (bOff + u.val) := hfit.of_le (by omega)
  have hf_ou1 : Fits w (bOff + u.val + 1) := hfit.of_le (by omega)
  have hf_sp : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) :=
    hfit.of_le (by omega)
  have hoff_u1 : x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
    simpa [Nat.add_assoc] using hfr.hcsr.hoff hu_lt
  have hnl : ¬inst.offset u.val + pre.length < inst.offset (u.val + 1) := by omega
  refine WP.exists_execWithin ?_
  unfold dfsStepBody
  by_cases hd0 : d = 0
  · subst hd0
    have hsu0 : x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m) = u.val := by
      simpa using hfr.hsu
    have hsp0 : x.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4) =
        inst.offset u.val + pre.length := by
      simpa using hfr.hsp
    have hf_su0 : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m) := by
      simpa using hf_su
    have hf_sp0 : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4) := by
      simpa using hf_sp
    wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hone, hfr.hb.hzero,
      hfr.hrd, hsu0, hoff_u1, hsp0, hnl, hf_su0, hf_ou, hf_ou1, hf_sp0]
    exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hal], by wram_simp, rfl⟩
  · wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hone, hfr.hb.hzero,
      hfr.hrd, hfr.hsu, hoff_u1, hfr.hsp, hnl, hd0, hf_su, hf_ou, hf_ou1, hf_sp]
    exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hal],
      by rw [ite_eq_right hd0]; exact ⟨by wram_simp [hfr.hact], by wram_simp⟩, rfl⟩

private theorem exec_dfsStep_skip {w bOff k d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_le : d ≤ k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hcond : vget vis v = true ∨
      (vget vis v = false ∧ vget mate v = none ∧ d ≠ k) ∨
      (vget vis v = false ∧ ∃ w₀, vget mate v = some w₀ ∧
        ¬(d < k ∧ vget dist w₀ = some (d + 1))))
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ x₁, ExecWithin w dfsStepBody x x₁ 27 ∧
      (∀ i : Fin 34, i.val < 25 → x₁.regs i = x.regs i) ∧
      DfsFrame inst bOff k mate dist augPairs d path u (pre ++ [v]) vis x₁ ∧
      (∀ a, DfsSubtreeOutside inst bOff d a → x₁.mem a = x.mem a) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        x₁.mem a = x.mem a) := by
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hoff_succ : inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length :=
    inst.offset_succ hu_lt
  have hpre_lt : pre.length < (inst.adj u).length := by
    rw [hsplit, List.length_append, List.length_cons]; omega
  have hed_lt := inst.offset_add_lt_numEdges u hpre_lt
  have hadj_get : (inst.adj u)[pre.length]'hpre_lt = v := by simp [hsplit]
  have hlt_lim : inst.offset u.val + pre.length < inst.offset (u.val + 1) := by omega
  have hedge_v : x.mem (bOff + inst.m + 1 + (inst.offset u.val + pre.length)) = v.val := by
    rw [hfr.hcsr.hedge u hpre_lt, hadj_get]
  have hoff_u1 : x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
    simpa [Nat.add_assoc] using hfr.hcsr.hoff hu_lt
  have hf_su : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + d) :=
    hfit.of_le (by omega)
  have hf_ou : Fits w (bOff + u.val) := hfit.of_le (by omega)
  have hf_ou1 : Fits w (bOff + u.val + 1) := hfit.of_le (by omega)
  have hf_sp : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) :=
    hfit.of_le (by omega)
  have hf_cur1 : Fits w (inst.offset u.val + pre.length + 1) :=
    hfit.of_le (by omega)
  have hf_ed : Fits w (bOff + inst.m + 1 + (inst.offset u.val + pre.length)) :=
    hfit.of_le (by omega)
  have hf_vis : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) :=
    hfit.of_le (by omega)
  have hf_cm : Fits w (bOff + inst.m + 1 + inst.numEdges + v.val) :=
    hfit.of_le (by omega)
  have hraw : ∃ x₁, ExecWithin w dfsStepBody x x₁ 27 ∧
      (∀ i : Fin 34, i.val < 25 → x₁.regs i = x.regs i) ∧
      x₁.regs rd = d ∧ x₁.regs augLen = augPairs.length ∧ x₁.regs active = 1 ∧
      x₁.mem = Function.update x.mem
        (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d)
        (inst.offset u.val + pre.length + 1) := by
    refine WP.exists_execWithin ?_
    unfold dfsStepBody
    rcases hcond with hvv_t | ⟨hvv_f, hmv, hd_ne⟩ | ⟨hvv_f, w₀, hmv, hnot⟩
    · have hvis_v :
          x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) = 1 := by
        rw [hfr.hvisM v, ite_eq_left hvv_t]
      wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
        hfr.hb.hbVis, hfr.hb.hone, hfr.hb.hzero, hfr.hrd, hfr.hsu, hoff_u1, hfr.hsp,
        hlt_lim, hedge_v, hvis_v, hf_su, hf_ou, hf_ou1, hf_sp, hf_cur1, hf_ed, hf_vis]
      exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hrd], by wram_simp [hfr.hal],
        by wram_simp [hfr.hact], rfl⟩
    · have hvis_v :
          x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) = 0 := by
        rw [hfr.hvisM v, ite_eq_right (by simp [hvv_f])]
      have hmate_v := hfr.hmate v
      have henc_m : encodeOptFin (vget mate v) = inst.m := by simp [hmv, encodeOptFin]
      wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
        hfr.hb.hbVis, hfr.hb.hbColMate, hfr.hb.hrm, hfr.hb.hone, hfr.hb.hzero,
        hfr.hrd, hfr.hrk, hd_ne, hfr.hsu, hoff_u1, hfr.hsp, hlt_lim, hedge_v, hvis_v,
        hmate_v, henc_m, hf_su, hf_ou, hf_ou1, hf_sp, hf_cur1, hf_ed, hf_vis, hf_cm]
      exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hrd], by wram_simp [hfr.hal],
        by wram_simp [hfr.hact], rfl⟩
    · have hw_lt := w₀.isLt
      have hvis_v :
          x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) = 0 := by
        rw [hfr.hvisM v, ite_eq_right (by simp [hvv_f])]
      have hmate_v := hfr.hmate v
      have henc_m : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
      have hw_ne : w₀.val ≠ inst.m := ne_of_lt hw_lt
      by_cases hd_lt : d < k
      · have hdw : vget dist w₀ ≠ some (d + 1) := fun h => hnot ⟨hd_lt, h⟩
        have hdist_w := hfr.hdM w₀
        have henc_ne : encodeDist (vget dist w₀) ≠ d + 2 := by
          cases h : vget dist w₀ with
          | none => simp [encodeDist]
          | some j =>
            simp only [encodeDist]
            intro heq
            exact hdw (by rw [h]; congr 1; omega)
        have hf_dw :
            Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + w₀.val) :=
          hfit.of_le (by omega)
        have hf_d2 : Fits w (d + 2) := hfit.of_le (by omega)
        wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
          hfr.hb.hbVis, hfr.hb.hbColMate, hfr.hb.hbDist, hfr.hb.hrm, hfr.hb.hone,
          hfr.hb.hzero, hfr.hb.htwo, hfr.hrd, hfr.hrk, hd_lt, hfr.hsu, hoff_u1, hfr.hsp,
          hlt_lim, hedge_v, hvis_v, hmate_v, henc_m, hw_ne, hdist_w, henc_ne,
          hf_su, hf_ou, hf_ou1, hf_sp, hf_cur1, hf_ed, hf_vis, hf_cm, hf_dw, hf_d2]
        exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hrd], by wram_simp [hfr.hal],
          by wram_simp [hfr.hact], rfl⟩
      · wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
          hfr.hb.hbVis, hfr.hb.hbColMate, hfr.hb.hrm, hfr.hb.hone, hfr.hb.hzero,
          hfr.hrd, hfr.hrk, hd_lt, hfr.hsu, hoff_u1, hfr.hsp, hlt_lim, hedge_v, hvis_v,
          hmate_v, henc_m, hw_ne, hf_su, hf_ou, hf_ou1, hf_sp, hf_cur1, hf_ed, hf_vis, hf_cm]
        exact ⟨fun i hi => by wram_simp, by wram_simp [hfr.hrd], by wram_simp [hfr.hal],
          by wram_simp [hfr.hact], rfl⟩
  obtain ⟨x₁, he_skip, hr₁, hrd₁, hal₁, hact₁, hmem₁⟩ := hraw
  have hplen := hfr.hplen
  refine ⟨x₁, he_skip, hr₁, ?_, ?_, ?_⟩
  · refine
      { hplen := hplen
        hcovers := hfr.hcovers
        hb := hfr.hb.of_eq fun i hi => hr₁ i (by omega)
        hcsr := hfr.hcsr.of_outside fun a ha => by rw [hmem₁, Function.update_of_ne (by omega)]
        hmate := fun v' => by
          rw [hmem₁, Function.update_of_ne (by have := v'.isLt; omega)]; exact hfr.hmate v'
        hdM := fun u' => by
          rw [hmem₁, Function.update_of_ne (by have := u'.isLt; omega)]; exact hfr.hdM u'
        hvisM := fun v' => by
          rw [hmem₁, Function.update_of_ne (by have := v'.isLt; omega)]; exact hfr.hvisM v'
        haugM := fun i hi => by
          have := hfr.hcovers.length_le
          simp only [List.length_append] at this
          rw [hmem₁, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr.haugM i hi
        hstack := fun i hi => by
          rw [hmem₁, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          exact hfr.hstack i hi
        hsu := by rw [hmem₁, Function.update_of_ne (by omega)]; exact hfr.hsu
        hsp := by rw [hmem₁, Function.update_self]; simp [Nat.add_assoc]
        hrk := (hr₁ rk (by decide)).trans hfr.hrk
        hrd := hrd₁
        hal := hal₁
        hact := hact₁ }
  · intro a ha
    simp only [DfsSubtreeOutside] at ha
    rw [hmem₁, Function.update_of_ne (by omega)]
  · intro a ha
    rw [hmem₁, Function.update_of_ne (by omega)]

private theorem exec_dfsStep_accept {w bOff k : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs k path u pre vis x)
    (hvv : vget vis v = false) (hmv : vget mate v = none)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ z, ExecWithin w dfsLoop x z (12 * (k + 1) + 33) ∧
      (∀ i : Fin 34, i.val < 25 → z.regs i = x.regs i) ∧
      z.regs augLen = (augPairs ++ (path ++ [(u, v)])).length ∧
      VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
        (vset vis v true) z.mem ∧
      AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
        (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
        (augPairs ++ (path ++ [(u, v)])) z.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        z.mem a = x.mem a) := by
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hoff_succ : inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length :=
    inst.offset_succ hu_lt
  have hpre_lt : pre.length < (inst.adj u).length := by
    rw [hsplit, List.length_append, List.length_cons]; omega
  have hed_lt := inst.offset_add_lt_numEdges u hpre_lt
  have hadj_get : (inst.adj u)[pre.length]'hpre_lt = v := by simp [hsplit]
  have hc_loop : (Cond.eq active one).Holds x := by
    rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
  have hlt_lim : inst.offset u.val + pre.length < inst.offset (u.val + 1) := by omega
  have hedge_v : x.mem (bOff + inst.m + 1 + (inst.offset u.val + pre.length)) = v.val := by
    rw [hfr.hcsr.hedge u hpre_lt, hadj_get]
  have hoff_u1 : x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
    simpa [Nat.add_assoc] using hfr.hcsr.hoff hu_lt
  have hvis_v : x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) = 0 := by
    rw [hfr.hvisM v, ite_eq_right (by simp [hvv])]
  have hmate_v := hfr.hmate v
  have henc_m : encodeOptFin (vget mate v) = inst.m := by simp [hmv, encodeOptFin]
  have hf_su : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + k) :=
    hfit.of_le (by omega)
  have hf_ou : Fits w (bOff + u.val) := hfit.of_le (by omega)
  have hf_ou1 : Fits w (bOff + u.val + 1) := hfit.of_le (by omega)
  have hf_sp : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + k) :=
    hfit.of_le (by omega)
  have hf_cur1 : Fits w (inst.offset u.val + pre.length + 1) :=
    hfit.of_le (by omega)
  have hf_ed : Fits w (bOff + inst.m + 1 + (inst.offset u.val + pre.length)) :=
    hfit.of_le (by omega)
  have hf_vis : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) :=
    hfit.of_le (by omega)
  have hf_cm : Fits w (bOff + inst.m + 1 + inst.numEdges + v.val) :=
    hfit.of_le (by omega)
  have hf_sv : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + k) :=
    hfit.of_le (by omega)
  have hplen := hfr.hplen
  have hcov_acc : VisCovers (vset vis v true) ((augPairs ++ path) ++ [(u, v)]) :=
    hfr.hcovers.snoc u hvv
  have haug_fit : augPairs.length + (k + 1) ≤ inst.r := by
    have := hcov_acc.length_le
    simp only [List.length_append, List.length_singleton, hplen] at this
    omega
  -- Execute dfsStepBody directly via WP.exists_execWithin
  have hstep : ∃ z, ExecWithin w dfsStepBody x z (12 * (k + 1) + 29) ∧
      (∀ i : Fin 34, i.val < 25 → z.regs i = x.regs i) ∧
      z.regs active = 0 ∧
      z.regs augLen = (augPairs ++ (path ++ [(u, v)])).length ∧
      VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
        (vset vis v true) z.mem ∧
      AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
        (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
        (augPairs ++ (path ++ [(u, v)])) z.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        z.mem a = x.mem a) := by
    refine WP.exists_execWithin ?_
    unfold dfsStepBody
    wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges,
      hfr.hb.hbVis, hfr.hb.hbColMate, hfr.hb.hbStackV, hfr.hb.hrm, hfr.hb.hone, hfr.hb.hzero,
      hfr.hrd, hfr.hrk, hfr.hsu, hoff_u1, hfr.hsp, hlt_lim, hedge_v, hvis_v, hmate_v, henc_m,
      hf_su, hf_ou, hf_ou1, hf_sp, hf_cur1, hf_ed, hf_vis, hf_cm, hf_sv]
    refine WP.name fun x_mid hx_mid => ?_
    have hb_mid : BaseRegs inst bOff x_mid :=
      hfr.hb.of_eq fun i hi => by subst hx_mid; wram_simp
    have hrk_mid : x_mid.regs rk = k := by subst hx_mid; wram_simp [hfr.hrk]
    have hal_mid : x_mid.regs augLen = augPairs.length := by subst hx_mid; wram_simp [hfr.hal]
    have hact_mid : x_mid.regs active = 1 := by subst hx_mid; wram_simp [hfr.hact]
    have haug_mid : AugMem
        (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
        (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
        augPairs x_mid.mem := by
      intro i hi
      have := hfr.hcovers.length_le
      simp only [List.length_append] at this
      have := v.isLt
      subst hx_mid
      wram_simp
      exact hfr.haugM i hi
    have hstack_mid : ∀ i : ℕ, (hi : i < k + 1) →
        x_mid.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
          ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)).1.val ∧
        x_mid.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
          ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)).2.val := by
      intro i hi
      have := v.isLt
      subst hx_mid
      by_cases hlt_k : i < k
      · have hlt_p : i < path.length := by omega
        have hget : ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)) = path[i]'hlt_p :=
          List.getElem_append_left hlt_p
        rw [hget]
        wram_simp
        exact hfr.hstack i hlt_k
      · have heq_k : i = k := by omega
        subst i
        have hlt_end : k < (path ++ [(u, v)]).length := by
          simp only [List.length_append, List.length_singleton, hplen]; omega
        have hget : (path ++ [(u, v)])[k]'hlt_end = (u, v) := by
          rw [List.getElem_append_right (by omega)]
          simp [hplen]
        rw [hget]
        wram_simp
        exact hfr.hsu
    obtain ⟨y_cp, he_cp, hr_cp, hact_cp, hal_cp, haug_cp, hf_cp⟩ :=
      exec_copyAugCode augPairs (path ++ [(u, v)]) x_mid hb_mid hrk_mid hal_mid
        hact_mid (by simp [hplen]) hk_le haug_fit haug_mid hstack_mid hfit
    refine WP.of_execWithin he_cp ?_
    have hz_mid : y_cp.regs zero = 0 := (hr_cp zero (by decide)).trans hb_mid.hzero
    wram_exec [hz_mid]
    refine ⟨fun i hi => ?_, by wram_simp, by wram_simp [hal_cp], ?_, haug_cp, fun a ha => ?_⟩
    · wram_simp
      exact (hr_cp i (by omega)).trans (by subst hx_mid; wram_simp)
    · intro v₀
      wram_simp
      rw [hf_cp _ (by have := v₀.isLt; omega)]
      have := v₀.isLt
      have := v.isLt
      subst hx_mid
      rcases eq_or_ne v₀ v with rfl | hne
      · wram_simp; simp
      · have hne_val : v₀.val ≠ v.val := fun h => hne (Fin.ext h)
        wram_simp
        rw [vget_vset_ne _ _ hne.symm]
        exact hfr.hvisM v₀
    · wram_simp
      rw [hf_cp a (by omega)]
      have := v.isLt
      subst hx_mid
      wram_simp
  obtain ⟨z, he_step, hr_z, hact_z, hal_z, hvis_z, haug_z, hf_z⟩ := hstep
  have hc_exit : ¬(Cond.eq active one).Holds z := by
    rw [Cond.holds_eq, hact_z, (hr_z one (by decide)).trans hfr.hb.hone]
    simp
  have he_exit := ExecWithin.loop_exit (body := dfsStepBody) (w := w) hc_exit
  exact ⟨z, (ExecWithin.loop_iter hc_loop he_step he_exit).mono (by omega),
    hr_z, hal_z, hvis_z, haug_z, hf_z⟩

private theorem exec_dfsStep_push {w bOff k d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u w₀ : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_lt_k : d < k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hvv : vget vis v = false) (hmv : vget mate v = some w₀)
    (hdw : vget dist w₀ = some (d + 1))
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ x_push, ExecWithin w dfsStepBody x x_push 36 ∧
      (∀ i : Fin 34, i.val < 25 → x_push.regs i = x.regs i) ∧
      DfsFrame inst bOff k mate dist augPairs (d + 1) (path ++ [(u, v)]) w₀ []
        (vset vis v true) x_push ∧
      x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) =
        inst.offset u.val + (pre ++ [v]).length ∧
      (∀ a, DfsSubtreeOutside inst bOff d a → x_push.mem a = x.mem a) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        x_push.mem a = x.mem a) := by
  have hu_lt := u.isLt
  have hv_lt := v.isLt
  have hw_lt := w₀.isLt
  have hoff_succ : inst.offset (u.val + 1) = inst.offset u.val + (inst.adj u).length :=
    inst.offset_succ hu_lt
  have hpre_lt : pre.length < (inst.adj u).length := by
    rw [hsplit, List.length_append, List.length_cons]; omega
  have hed_lt := inst.offset_add_lt_numEdges u hpre_lt
  have hadj_get : (inst.adj u)[pre.length]'hpre_lt = v := by simp [hsplit]
  have hlt_lim : inst.offset u.val + pre.length < inst.offset (u.val + 1) := by omega
  have hedge_v : x.mem (bOff + inst.m + 1 + (inst.offset u.val + pre.length)) = v.val := by
    rw [hfr.hcsr.hedge u hpre_lt, hadj_get]
  have hoff_u1 : x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
    simpa [Nat.add_assoc] using hfr.hcsr.hoff hu_lt
  have hvis_v : x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) = 0 := by
    rw [hfr.hvisM v, ite_eq_right (by simp [hvv])]
  have hmate_v := hfr.hmate v
  have henc_m : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
  have hw_ne : w₀.val ≠ inst.m := ne_of_lt hw_lt
  have hdist_w := hfr.hdM w₀
  have henc_dw : encodeDist (vget dist w₀) = d + 2 := by simp [hdw, encodeDist]
  have hoff_w : x.mem (bOff + w₀.val) = inst.offset w₀.val := hfr.hcsr.hoff (le_of_lt hw_lt)
  have hf_su : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + d) :=
    hfit.of_le (by omega)
  have hf_ou : Fits w (bOff + u.val) := hfit.of_le (by omega)
  have hf_ou1 : Fits w (bOff + u.val + 1) := hfit.of_le (by omega)
  have hf_sp : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) :=
    hfit.of_le (by omega)
  have hf_cur1 : Fits w (inst.offset u.val + pre.length + 1) :=
    hfit.of_le (by omega)
  have hf_ed : Fits w (bOff + inst.m + 1 + (inst.offset u.val + pre.length)) :=
    hfit.of_le (by omega)
  have hf_vis : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m + v.val) :=
    hfit.of_le (by omega)
  have hf_cm : Fits w (bOff + inst.m + 1 + inst.numEdges + v.val) :=
    hfit.of_le (by omega)
  have hf_dw : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + w₀.val) :=
    hfit.of_le (by omega)
  have hf_d2 : Fits w (d + 2) := hfit.of_le (by omega)
  have hf_sv : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + d) :=
    hfit.of_le (by omega)
  have hf_d1 : Fits w (d + 1) := hfit.of_le (by omega)
  have hf_su1 :
      Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + (d + 1)) :=
    hfit.of_le (by omega)
  have hf_ow : Fits w (bOff + w₀.val) := hfit.of_le (by omega)
  have hf_sp1 :
      Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + (d + 1)) :=
    hfit.of_le (by omega)
  have hplen := hfr.hplen
  have hraw : ∃ x_push, ExecWithin w dfsStepBody x x_push 36 ∧
      (∀ i : Fin 34, i.val < 25 → x_push.regs i = x.regs i) ∧
      x_push.regs rd = d + 1 ∧
      x_push.regs augLen = augPairs.length ∧
      x_push.regs active = 1 ∧
      VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
        (vset vis v true) x_push.mem ∧
      (∀ i : ℕ, (hi : i < d + 1) →
        x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + i) =
          ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)).1.val ∧
        x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 4 * inst.m + 2 + i) =
          ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)).2.val) ∧
      x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m + (d + 1)) =
        w₀.val ∧
      x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + d) =
        inst.offset u.val + (pre ++ [v]).length ∧
      x_push.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4 + (d + 1)) =
        inst.offset w₀.val ∧
      (∀ a, DfsSubtreeOutside inst bOff d a → x_push.mem a = x.mem a) := by
    refine WP.exists_execWithin ?_
    unfold dfsStepBody
    wram_exec [hfr.hb.hbStackU, hfr.hb.hbOff, hfr.hb.hbStackPos, hfr.hb.hbEdges, hfr.hb.hbVis,
      hfr.hb.hbColMate, hfr.hb.hbDist, hfr.hb.hbStackV, hfr.hb.hrm, hfr.hb.hone, hfr.hb.hzero,
      hfr.hb.htwo, hfr.hrd, hfr.hrk, hd_lt_k, hfr.hsu, hoff_u1, hfr.hsp, hlt_lim, hedge_v,
      hvis_v, hmate_v, henc_m, hw_ne, hdist_w, henc_dw, hoff_w,
      hf_su, hf_ou, hf_ou1, hf_sp, hf_cur1, hf_ed, hf_vis, hf_cm,
      hf_dw, hf_d2, hf_sv, hf_d1, hf_su1, hf_ow, hf_sp1]
    refine ⟨fun i hi => by wram_simp, by wram_simp, by wram_simp [hfr.hal],
      by wram_simp [hfr.hact], ?_, ?_, ?_, ?_, ?_, fun a ha => ?_⟩
    · intro v₀
      have := v₀.isLt
      have := v.isLt
      rcases eq_or_ne v₀ v with rfl | hne
      · wram_simp; simp
      · have hne_val : v₀.val ≠ v.val := fun h => hne (Fin.ext h)
        wram_simp
        rw [vget_vset_ne _ _ hne.symm]
        exact hfr.hvisM v₀
    · intro i hi
      have := v.isLt
      by_cases hlt_d : i < d
      · have hlt_p : i < path.length := by omega
        have hget : ((path ++ [(u, v)])[i]'(by simp [hplen]; omega)) = path[i]'hlt_p :=
          List.getElem_append_left hlt_p
        rw [hget]
        wram_simp
        exact hfr.hstack i hlt_d
      · have heq_d : i = d := by omega
        subst i
        have hlt_end : d < (path ++ [(u, v)]).length := by
          simp only [List.length_append, List.length_singleton, hplen]; omega
        have hget : (path ++ [(u, v)])[d]'hlt_end = (u, v) := by
          rw [List.getElem_append_right (by omega)]
          simp [hplen]
        rw [hget]
        wram_simp
        exact hfr.hsu
    · have := v.isLt; wram_simp
    · have := v.isLt; wram_simp; simp [Nat.add_assoc]
    · have := v.isLt; wram_simp
    · simp only [DfsSubtreeOutside] at ha
      have := v.isLt
      wram_simp
  obtain ⟨x_push, he_push, hr_p, hrd_p, hal_p, hact_p, hvis_p, hstack_p,
    hsu1_p, hspd_p, hsp1_p, hf_p⟩ := hraw
  have hcov_p : VisCovers (vset vis v true) (augPairs ++ (path ++ [(u, v)])) := by
    simpa [List.append_assoc] using hfr.hcovers.snoc u hvv
  refine ⟨x_push, he_push, hr_p, ?_, hspd_p, hf_p, fun a ha => hf_p a (by
    simp only [DfsSubtreeOutside]; omega)⟩
  exact
    { hplen := by simp [hplen]
      hcovers := hcov_p
      hb := hfr.hb.of_eq fun i hi => hr_p i (by omega)
      hcsr := hfr.hcsr.of_outside fun a ha => hf_p a (by simp only [DfsSubtreeOutside]; omega)
      hmate := fun v' =>
        (hf_p _ (by simp only [DfsSubtreeOutside]; have := v'.isLt; omega)).trans (hfr.hmate v')
      hdM := fun u' =>
        (hf_p _ (by simp only [DfsSubtreeOutside]; have := u'.isLt; omega)).trans (hfr.hdM u')
      hvisM := hvis_p
      haugM := fun i hi => by
        have := hfr.hcovers.length_le
        simp only [List.length_append] at this
        rw [hf_p _ (by simp only [DfsSubtreeOutside]; omega),
          hf_p _ (by simp only [DfsSubtreeOutside]; omega)]
        exact hfr.haugM i hi
      hstack := hstack_p
      hsu := hsu1_p
      hsp := by simpa using hsp1_p
      hrk := (hr_p rk (by decide)).trans hfr.hrk
      hrd := hrd_p
      hal := hal_p
      hact := hact_p }

private theorem exec_dfsLevel_skip {w bOff k f d : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    {augPairs path : List (Fin inst.m × Fin inst.r)} {u : Fin inst.m}
    {pre vs : List (Fin inst.r)} {v : Fin inst.r}
    {vis : Vector Bool inst.r} {x : Data 34}
    (hd_le : d ≤ k) (hk_le : k ≤ inst.m + 1)
    (hsplit : inst.adj u = pre ++ v :: vs)
    (hfr : DfsFrame inst bOff k mate dist augPairs d path u pre vis x)
    (hcond : vget vis v = true ∨
      (vget vis v = false ∧ vget mate v = none ∧ d ≠ k) ∨
      (vget vis v = false ∧ ∃ w₀, vget mate v = some w₀ ∧
        ¬(d < k ∧ vget dist w₀ = some (d + 1))))
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8))
    (heq_R : hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u (v :: vs) vis [] =
      hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u vs vis [])
    (ih_step : ∀ x₁, DfsFrame inst bOff k mate dist augPairs d path u (pre ++ [v]) vis x₁ →
      match (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
          (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).2 with
      | some q =>
        ∃ z, ExecWithin w dfsLoop x₁ z
            (38 * vs.length +
              (dfsPot inst mate vis -
                dfsPot inst mate
                  (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
                    (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1) +
              12 * (k + 1) + 33) ∧
          (∀ i : Fin 34, i.val < 25 → z.regs i = x₁.regs i) ∧
          z.regs augLen = (augPairs ++ (path ++ q)).length ∧
          VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
            (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
              (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 z.mem ∧
          AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
            (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
            (augPairs ++ (path ++ q)) z.mem ∧
          (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
              a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
            z.mem a = x₁.mem a)
      | none =>
        ∃ y,
          (∀ z T_after, ExecWithin w dfsLoop y z T_after →
            ExecWithin w dfsLoop x₁ z
              (38 * vs.length + 14 +
                (dfsPot inst mate vis -
                  dfsPot inst mate
                    (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
                      (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1) +
                T_after)) ∧
          (∀ i : Fin 34, i.val < 25 → y.regs i = x₁.regs i) ∧
          y.regs augLen = augPairs.length ∧
          (if d = 0 then y.regs active = 0 else y.regs active = 1 ∧ y.regs rd = d - 1) ∧
          VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
            (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
              (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 y.mem ∧
          (∀ a, DfsSubtreeOutside inst bOff d a → y.mem a = x₁.mem a)) :
    match (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
        (dfsNext inst.graph inst.adj mate dist f d) u (v :: vs) vis []).2 with
    | some q =>
      ∃ z, ExecWithin w dfsLoop x z
          (38 * (v :: vs).length +
            (dfsPot inst mate vis -
              dfsPot inst mate
                (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
                  (dfsNext inst.graph inst.adj mate dist f d) u (v :: vs) vis []).1) +
            12 * (k + 1) + 33) ∧
        (∀ i : Fin 34, i.val < 25 → z.regs i = x.regs i) ∧
        z.regs augLen = (augPairs ++ (path ++ q)).length ∧
        VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
          (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
            (dfsNext inst.graph inst.adj mate dist f d) u (v :: vs) vis []).1 z.mem ∧
        AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
          (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
          (augPairs ++ (path ++ q)) z.mem ∧
        (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
            a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
          z.mem a = x.mem a)
    | none =>
      ∃ y,
        (∀ z T_after, ExecWithin w dfsLoop y z T_after →
          ExecWithin w dfsLoop x z
            (38 * (v :: vs).length + 14 +
              (dfsPot inst mate vis -
                dfsPot inst mate
                  (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
                    (dfsNext inst.graph inst.adj mate dist f d) u (v :: vs) vis []).1) +
              T_after)) ∧
        (∀ i : Fin 34, i.val < 25 → y.regs i = x.regs i) ∧
        y.regs augLen = augPairs.length ∧
        (if d = 0 then y.regs active = 0 else y.regs active = 1 ∧ y.regs rd = d - 1) ∧
        VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
          (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
            (dfsNext inst.graph inst.adj mate dist f d) u (v :: vs) vis []).1 y.mem ∧
        (∀ a, DfsSubtreeOutside inst bOff d a → y.mem a = x.mem a) := by
  have hc_loop : (Cond.eq active one).Holds x := by
    rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
  obtain ⟨x₁, he_skip, hr₁, hfr₁, hf_sub₁, hf_all₁⟩ :=
    exec_dfsStep_skip hd_le hk_le hsplit hfr hcond hfit
  have hrec := ih_step x₁ hfr₁
  rw [heq_R]
  cases hr2 : (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
      (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).2 with
  | some q =>
    rw [hr2] at hrec
    obtain ⟨z, he_rest, hr_z, hal_z, hvis_z, haug_z, hf_z⟩ := hrec
    exact ⟨z, (ExecWithin.loop_iter hc_loop he_skip he_rest).mono
      (by simp only [List.length_cons]; omega),
      fun i hi => (hr_z i hi).trans (hr₁ i hi), hal_z, hvis_z, haug_z,
      fun a ha => (hf_z a ha).trans (hf_all₁ a ha)⟩
  | none =>
    rw [hr2] at hrec
    obtain ⟨y, htrans, hr_y, hal_y, hact_y, hvis_y, hf_y⟩ := hrec
    exact ⟨y, fun z T_after he_after =>
      (ExecWithin.loop_iter hc_loop he_skip (htrans z T_after he_after)).mono
        (by simp only [List.length_cons]; omega),
      fun i hi => (hr_y i hi).trans (hr₁ i hi), hal_y, hact_y, hvis_y,
      fun a ha => (hf_y a ha).trans (hf_sub₁ a ha)⟩

private theorem exec_dfsLevel {w bOff k : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    (hk_le : k ≤ inst.m + 1) (augPairs : List (Fin inst.m × Fin inst.r)) :
    ∀ (f d : ℕ), f + d = k →
      ∀ (path : List (Fin inst.m × Fin inst.r)) (u : Fin inst.m)
        (pre vs : List (Fin inst.r)) (vis : Vector Bool inst.r) (x : Data 34),
        inst.adj u = pre ++ vs →
        DfsFrame inst bOff k mate dist augPairs d path u pre vis x →
        Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8) →
        match (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
            (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).2 with
        | some q =>
          ∃ z, ExecWithin w dfsLoop x z
              (38 * vs.length +
                (dfsPot inst mate vis -
                  dfsPot inst mate
                    (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
                      (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1) +
                12 * (k + 1) + 33) ∧
            (∀ i : Fin 34, i.val < 25 → z.regs i = x.regs i) ∧
            z.regs augLen = (augPairs ++ (path ++ q)).length ∧
            VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
              (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
                (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 z.mem ∧
            AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
              (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
              (augPairs ++ (path ++ q)) z.mem ∧
            (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
                a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
              z.mem a = x.mem a)
        | none =>
          ∃ y,
            (∀ z T_after, ExecWithin w dfsLoop y z T_after →
              ExecWithin w dfsLoop x z
                (38 * vs.length + 14 +
                  (dfsPot inst mate vis -
                    dfsPot inst mate
                      (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
                        (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1) +
                  T_after)) ∧
            (∀ i : Fin 34, i.val < 25 → y.regs i = x.regs i) ∧
            y.regs augLen = augPairs.length ∧
            (if d = 0 then y.regs active = 0 else y.regs active = 1 ∧ y.regs rd = d - 1) ∧
            VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
              (hkDfsLevel inst.graph mate dist (decide (f = 0)) d
                (dfsNext inst.graph inst.adj mate dist f d) u vs vis []).1 y.mem ∧
            (∀ a, DfsSubtreeOutside inst bOff d a → y.mem a = x.mem a) := by
  intro f
  induction f with
  | zero =>
    intro d hfd path u pre vs vis x hsplit hfr hfit
    obtain rfl : d = k := by omega
    induction vs generalizing pre vis x with
    | nil =>
      have hc_loop : (Cond.eq active one).Holds x := by
        rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
      obtain ⟨y, he_pop, hr_y, hal_y, hact_y, hmem_y⟩ :=
        exec_dfsStep_pop (le_refl d) hk_le (by simpa using hsplit) hfr hfit
      dsimp only [hkDfsLevel]
      exact ⟨y, fun z T_after he_after =>
        (ExecWithin.loop_iter hc_loop he_pop he_after).mono (by omega),
        hr_y, hal_y, hact_y, hmem_y ▸ hfr.hvisM, fun a _ => congrFun hmem_y a⟩
    | cons v vs ih =>
      have hGu : inst.graph (u, v) = true := by
        apply decide_eq_true; rw [hsplit]; simp
      have hsplit' : inst.adj u = (pre ++ [v]) ++ vs := by simp [hsplit]
      by_cases hvv : vget vis v = false
      · cases hmv : vget mate v with
        | none =>
          obtain ⟨z, he_acc, hr_z, hal_z, hvis_z, haug_z, hf_z⟩ :=
            exec_dfsStep_accept hk_le hsplit hfr hvv hmv hfit
          have heq_R : hkDfsLevel inst.graph mate dist (decide (0 = 0)) d
              (dfsNext inst.graph inst.adj mate dist 0 d) u (v :: vs) vis [] =
              (vset vis v true, some [(u, v)]) := by
            simp [hkDfsLevel, hGu, hvv, hmv]
          rw [heq_R]
          dsimp only
          exact ⟨z, he_acc.mono (by omega), hr_z, hal_z, hvis_z, haug_z, hf_z⟩
        | some w₀ =>
          exact exec_dfsLevel_skip (le_refl d) hk_le hsplit hfr
            (Or.inr (Or.inr ⟨hvv, w₀, hmv, fun h => Nat.lt_irrefl d h.1⟩)) hfit
            (by simp [hkDfsLevel, hGu, hvv, hmv])
            (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ hsplit' hfr₁)
      · have hvv_t : vget vis v = true := Bool.eq_true_of_not_eq_false hvv
        exact exec_dfsLevel_skip (le_refl d) hk_le hsplit hfr (Or.inl hvv_t) hfit
          (by simp [hkDfsLevel, hvv_t])
          (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ hsplit' hfr₁)
  | succ f ih_f =>
    intro d hfd path u pre vs vis x hsplit hfr hfit
    have hd_lt_k : d < k := by omega
    have hd_le_k : d ≤ k := by omega
    have hd_ne_k : d ≠ k := by omega
    induction vs generalizing pre vis x with
    | nil =>
      have hc_loop : (Cond.eq active one).Holds x := by
        rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
      obtain ⟨y, he_pop, hr_y, hal_y, hact_y, hmem_y⟩ :=
        exec_dfsStep_pop hd_le_k hk_le (by simpa using hsplit) hfr hfit
      dsimp only [hkDfsLevel]
      exact ⟨y, fun z T_after he_after =>
        (ExecWithin.loop_iter hc_loop he_pop he_after).mono (by omega),
        hr_y, hal_y, hact_y, hmem_y ▸ hfr.hvisM, fun a _ => congrFun hmem_y a⟩
    | cons v vs ih =>
      have hc_loop : (Cond.eq active one).Holds x := by
        rw [Cond.holds_eq, hfr.hact, hfr.hb.hone]
      have hGu : inst.graph (u, v) = true := by
        apply decide_eq_true; rw [hsplit]; simp
      have hsplit' : inst.adj u = (pre ++ [v]) ++ vs := by simp [hsplit]
      by_cases hvv : vget vis v = false
      · cases hmv : vget mate v with
        | none =>
          exact exec_dfsLevel_skip hd_le_k hk_le hsplit hfr
            (Or.inr (Or.inl ⟨hvv, hmv, hd_ne_k⟩)) hfit
            (by simp [hkDfsLevel, hGu, hvv, hmv])
            (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ hsplit' hfr₁)
        | some w₀ =>
          by_cases hdw : vget dist w₀ = some (d + 1)
          · obtain ⟨x_push, he_push, hr_p, hfr_p, hspd_p, hf_sub_p, hf_all_p⟩ :=
              exec_dfsStep_push hd_lt_k hk_le hsplit hfr hvv hmv hdw hfit
            have hpot_v : dfsPot inst mate (vset vis v true) +
                (38 * (inst.adj w₀).length + 14) = dfsPot inst mate vis := by
              simpa [dfsVertWeight, hkDfsCost, hmv] using
                dfsPot_vset_true (inst := inst) (mate := mate) hvv
            have hchild := ih_f (d + 1) (by omega) (path ++ [(u, v)]) w₀ [] (inst.adj w₀)
              (vset vis v true) x_push rfl hfr_p hfit
            rw [← hkDfs_eq_dfsLevel] at hchild
            obtain ⟨_, hpot_child, hcov_child⟩ :=
              hkDfs_pure_props (inst := inst) (mate := mate) (dist := dist) f (d + 1) w₀
                (vset vis v true) (augPairs ++ (path ++ [(u, v)])) hfr_p.hcovers
            have heq_step : hkDfsLevel inst.graph mate dist (decide (f + 1 = 0)) d
                (dfsNext inst.graph inst.adj mate dist (f + 1) d) u (v :: vs) vis [] =
              let res := hkDfs inst.graph inst.adj mate dist f (d + 1) w₀ (vset vis v true) []
              match res.2 with
              | some qw => (res.1, some ((u, v) :: qw))
              | none => hkDfsLevel inst.graph mate dist (decide (f + 1 = 0)) d
                  (dfsNext inst.graph inst.adj mate dist (f + 1) d) u vs res.1 [] := by
              simp only [hkDfsLevel, hGu, hvv, hmv, hdw, dfsNext]
              cases (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀ (vset vis v true) []).2 <;>
                simp
            rw [heq_step]
            dsimp only
            cases hrw : (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀
                (vset vis v true) []).2 with
            | some qw =>
              rw [hrw] at hchild hcov_child
              dsimp only
              obtain ⟨z, he_child, hr_z, hal_z, hvis_z, haug_z, hf_z⟩ := hchild
              have hpath_assoc :
                  augPairs ++ ((path ++ [(u, v)]) ++ qw) =
                    augPairs ++ (path ++ ((u, v) :: qw)) := by
                simp [List.append_assoc]
              rw [hpath_assoc] at hal_z haug_z
              exact ⟨z, (ExecWithin.loop_iter hc_loop he_push he_child).mono
                (by simp only [List.length_cons]; omega),
                fun i hi => (hr_z i hi).trans (hr_p i hi), hal_z, hvis_z, haug_z,
                fun a ha => (hf_z a ha).trans (hf_all_p a ha)⟩
            | none =>
              rw [hrw] at hchild hcov_child
              dsimp only
              obtain ⟨y_pop, htrans_c, hr_c, hal_c, hact_c, hvis_c, hf_c⟩ := hchild
              rw [ite_eq_right (Nat.succ_ne_zero d)] at hact_c
              have hcov_back : VisCovers
                  (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀ (vset vis v true) []).1
                  (augPairs ++ path) := by
                refine ⟨hfr.hcovers.1, fun e he => hcov_child.2 e ?_⟩
                simp only [List.mem_append] at he ⊢
                rcases he with he | he
                · exact Or.inl he
                · exact Or.inr (Or.inl he)
              have hplen := hfr.hplen
              have hfr_pop : DfsFrame inst bOff k mate dist augPairs d path u (pre ++ [v])
                  (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀ (vset vis v true) []).1
                  y_pop :=
                { hplen := hplen
                  hcovers := hcov_back
                  hb := hfr_p.hb.of_eq fun i hi => hr_c i (by omega)
                  hcsr := hfr_p.hcsr.of_outside fun a ha =>
                    hf_c a (by simp only [DfsSubtreeOutside]; omega)
                  hmate := fun v' =>
                    (hf_c _ (by simp only [DfsSubtreeOutside]; have := v'.isLt; omega)).trans
                      (hfr_p.hmate v')
                  hdM := fun u' =>
                    (hf_c _ (by simp only [DfsSubtreeOutside]; have := u'.isLt; omega)).trans
                      (hfr_p.hdM u')
                  hvisM := hvis_c
                  haugM := fun i hi => by
                    have := hfr.hcovers.length_le
                    simp only [List.length_append] at this
                    rw [hf_c _ (by simp only [DfsSubtreeOutside]; omega),
                      hf_c _ (by simp only [DfsSubtreeOutside]; omega)]
                    exact hfr_p.haugM i hi
                  hstack := fun i hi => by
                    rw [hf_c _ (by simp only [DfsSubtreeOutside]; omega),
                      hf_c _ (by simp only [DfsSubtreeOutside]; omega),
                      hf_sub_p _ (by simp only [DfsSubtreeOutside]; omega),
                      hf_sub_p _ (by simp only [DfsSubtreeOutside]; omega)]
                    exact hfr.hstack i hi
                  hsu := by
                    rw [hf_c _ (by simp only [DfsSubtreeOutside]; omega),
                      hf_sub_p _ (by simp only [DfsSubtreeOutside]; omega)]
                    exact hfr.hsu
                  hsp := by
                    rw [hf_c _ (by simp only [DfsSubtreeOutside]; omega)]
                    exact hspd_p
                  hrk := (hr_c rk (by decide)).trans hfr_p.hrk
                  hrd := by simpa using hact_c.2
                  hal := hal_c
                  hact := hact_c.1 }
              have hpot_rem : dfsPot inst mate
                  (hkDfsLevel inst.graph mate dist (decide (f + 1 = 0)) d
                    (dfsNext inst.graph inst.adj mate dist (f + 1) d) u vs
                    (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀
                      (vset vis v true) []).1 []).1 ≤
                  dfsPot inst mate
                    (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀
                      (vset vis v true) []).1 :=
                (hkDfsLevel_pure_props (f + 1) d
                  (fun w' vis₀ ps₀ hc => hkDfs_pure_props f (d + 1) w' vis₀ ps₀ hc)
                  u vs _ (augPairs ++ path) hcov_back).2.1
              have hrem := ih (pre ++ [v]) _ y_pop hsplit' hfr_pop
              cases hr2 : (hkDfsLevel inst.graph mate dist (decide (f + 1 = 0)) d
                  (dfsNext inst.graph inst.adj mate dist (f + 1) d) u vs
                  (hkDfs inst.graph inst.adj mate dist f (d + 1) w₀
                    (vset vis v true) []).1 []).2 with
              | some q =>
                rw [hr2] at hrem
                obtain ⟨z, he_rem, hr_z, hal_z, hvis_z, haug_z, hf_z⟩ := hrem
                have he_c := htrans_c z _ he_rem
                refine ⟨z, (ExecWithin.loop_iter hc_loop he_push he_c).mono
                  (by simp only [List.length_cons]; omega),
                  fun i hi => (hr_z i hi).trans ((hr_c i hi).trans (hr_p i hi)),
                  hal_z, hvis_z, haug_z, fun a ha => ?_⟩
                exact (hf_z a ha).trans
                  ((hf_c a (by simp only [DfsSubtreeOutside]; omega)).trans (hf_all_p a ha))
              | none =>
                rw [hr2] at hrem
                obtain ⟨y_end, htrans_rem, hr_end, hal_end, hact_end, hvis_end, hf_end⟩ := hrem
                refine ⟨y_end, fun z T_after he_after =>
                  (ExecWithin.loop_iter hc_loop he_push
                    (htrans_c z _ (htrans_rem z T_after he_after))).mono
                    (by simp only [List.length_cons]; omega),
                  fun i hi => (hr_end i hi).trans ((hr_c i hi).trans (hr_p i hi)),
                  hal_end, hact_end, hvis_end, fun a ha => ?_⟩
                have ha_c : DfsSubtreeOutside inst bOff (d + 1) a := by
                  simp only [DfsSubtreeOutside] at ha ⊢; omega
                exact (hf_end a ha).trans ((hf_c a ha_c).trans (hf_sub_p a ha))
          · exact exec_dfsLevel_skip hd_le_k hk_le hsplit hfr
              (Or.inr (Or.inr ⟨hvv, w₀, hmv, fun h => hdw h.2⟩)) hfit
              (by simp [hkDfsLevel, hGu, hvv, hmv, hdw])
              (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ hsplit' hfr₁)
      · have hvv_t : vget vis v = true := Bool.eq_true_of_not_eq_false hvv
        exact exec_dfsLevel_skip hd_le_k hk_le hsplit hfr (Or.inl hvv_t) hfit
          (by simp [hkDfsLevel, hvv_t])
          (fun x₁ hfr₁ => ih (pre ++ [v]) vis x₁ hsplit' hfr₁)

private def dfsRootSetup : Code .standard 34 := ram[
  rd ← #0;
  addr ← bStackUReg; *addr ← qHead;
  addr ← bOffReg + qHead; val ← *addr;
  addr ← bStackPosReg; *addr ← val;
  active ← one ]

private def dfsRootBody : Code .standard 34 :=
  .seq (ram[ addr ← bDistReg + qHead; val ← *addr ])
    (.seq (.branch (.eq val one) (.seq dfsRootSetup dfsLoop) (ram[ tmp ← zero ]))
      (ram[ qHead ← qHead + one ]))

private def applyAugBody : Code .standard 34 := ram[
  addr ← bAugUReg + idx; val ← *addr;
  addr ← bAugVReg + idx; val2 ← *addr;
  addr ← bColMateReg + val2; *addr ← val;
  idx ← idx + one ]

private def applyAugCode : Code .standard 34 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx augLen) applyAugBody)

private def dfsPhaseCode : Code .standard 34 :=
  .seq (clearAt bVisReg rr)
    (.seq (ram[ augLen ← #0; qHead ← #0 ])
      (.seq (.loop (.lt qHead rm) dfsRootBody) applyAugCode))

private theorem exec_dfsRootsLoop {w bOff k : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    (hk_le : k ≤ inst.m + 1)
    (pre us : List (Fin inst.m)) (hsplit : List.finRange inst.m = pre ++ us)
    (vis : Vector Bool inst.r)
    (augPairs pureAcc : List (Fin inst.m × Fin inst.r))
    (hcovers : VisCovers vis augPairs)
    (hfin_eq : augPairs.toFinset = pureAcc.toFinset)
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem)
    (hdM : DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) dist x.mem)
    (hvisM : VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m) vis x.mem)
    (haugM : AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
      (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6) augPairs x.mem)
    (hrk : x.regs rk = k)
    (hqh : x.regs qHead = pre.length)
    (hal : x.regs augLen = augPairs.length)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y augPairs',
      ExecWithin w (.loop (.lt qHead rm) dfsRootBody) x y
        ((us.map (fun u => 38 * (inst.adj u).length + 49)).sum +
          dfsPot inst mate vis + 12 * (augPairs'.length - augPairs.length) + 2) ∧
      augPairs.length ≤ augPairs'.length ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      y.regs augLen = augPairs'.length ∧
      VisCovers (Vector.replicate inst.r true) augPairs' ∧
      augPairs'.toFinset = (hkDfsRoots inst.graph inst.adj mate dist k us vis pureAcc).toFinset ∧
      AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
        (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6) augPairs' y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a) := by
  induction us generalizing pre vis augPairs pureAcc x with
  | nil =>
    simp only [List.append_nil] at hsplit
    have hpre_m : pre.length = inst.m := by
      have := congrArg List.length hsplit; simpa using this.symm
    have hc : ¬(Cond.lt qHead rm).Holds x := by
      simp [Cond.holds_lt, hqh, hb.hrm, hpre_m]
    exact ⟨x, augPairs, (ExecWithin.loop_exit hc).mono (by omega), le_refl _,
      fun _ _ => rfl, hal, ⟨hcovers.1, fun _ _ => by simp [vget_replicate]⟩,
      hfin_eq, haugM, fun _ _ => rfl⟩
  | cons u us ih =>
    have hpre_lt : pre.length < inst.m := by
      have := congrArg List.length hsplit
      simp only [List.length_finRange, List.length_append, List.length_cons] at this
      omega
    have hu_val : u.val = pre.length := by
      have hget : (List.finRange inst.m)[pre.length]'(by simp [hpre_lt]) = u := by
        simp [hsplit]
      simpa using (congrArg Fin.val hget).symm
    have hc_loop : (Cond.lt qHead rm).Holds x := by
      simp [Cond.holds_lt, hqh, hb.hrm, hpre_lt]
    have hsplit' : List.finRange inst.m = (pre ++ [u]) ++ us := by simp [hsplit]
    have hf_du : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + pre.length) :=
      hfit.of_le (by omega)
    have hf_qh1 : Fits w (pre.length + 1) := hfit.of_le (by omega)
    have hdist_u :
        x.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + pre.length) =
          encodeDist (vget dist u) := by
      rw [← hu_val]
      exact hdM u
    have hchk : ∃ x_chk, ExecWithin w
        (ram[ addr ← bDistReg + qHead; val ← *addr ] : Code .standard 34) x x_chk 2 ∧
        x_chk = (x.set addr
          (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + pre.length)).set val
          (encodeDist (vget dist u)) := by
      refine WP.exists_execWithin ?_
      wram_exec [hb.hbDist, hqh, hdist_u, hf_du]
      rfl
    obtain ⟨x_chk, he_chk, rfl⟩ := hchk
    let x_chk := (x.set addr
      (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + pre.length)).set val
      (encodeDist (vget dist u))
    have hb_chk : BaseRegs inst bOff x_chk :=
      hb.of_eq fun i hi => by dsimp only [x_chk]; wram_simp
    by_cases hdu0 : vget dist u = some 0
    · have henc_1 : encodeDist (vget dist u) = 1 := by simp [hdu0, encodeDist]
      have hc_val1 : (Cond.eq val one).Holds x_chk := by
        rw [Cond.holds_eq, hb_chk.hone]
        dsimp only [x_chk]
        wram_simp [henc_1]
      have hf_ou : Fits w (bOff + pre.length) := hfit.of_le (by omega)
      have hoff_u : x_chk.mem (bOff + pre.length) = inst.offset u.val := by
        dsimp only [x_chk]
        rw [← hu_val]
        exact hcsr.hoff (le_of_lt u.isLt)
      have hqh_chk : x_chk.regs qHead = pre.length := by dsimp only [x_chk]; wram_simp [hqh]
      have hal_chk : x_chk.regs augLen = augPairs.length := by dsimp only [x_chk]; wram_simp [hal]
      have hrk_chk : x_chk.regs rk = k := by dsimp only [x_chk]; wram_simp [hrk]
      have hset : ∃ x_in, ExecWithin w dfsRootSetup x_chk x_in 8 ∧
          (∀ i : Fin 34, i.val < 25 → x_in.regs i = x.regs i) ∧
          x_in.regs rd = 0 ∧ x_in.regs augLen = augPairs.length ∧ x_in.regs active = 1 ∧
          x_in.mem = Function.update
            (Function.update x.mem
              (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 3 * inst.m) u.val)
            (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 5 * inst.m + 4)
            (inst.offset u.val) := by
        refine WP.exists_execWithin ?_
        unfold dfsRootSetup
        wram_exec [hb_chk.hbStackU, hb_chk.hbOff, hb_chk.hbStackPos, hb_chk.hone,
          hqh_chk, hoff_u, hf_ou]
        refine ⟨fun i hi => by dsimp only [x_chk]; wram_simp, by wram_simp,
          by wram_simp [hal_chk], by wram_simp, ?_⟩
        rw [← hu_val]
        rfl
      obtain ⟨x_in, he_in, hr_in, hrd_in, hal_in, hact_in, hmem_in⟩ := hset
      have hfr_in : DfsFrame inst bOff k mate dist augPairs 0 [] u [] vis x_in :=
        { hplen := rfl
          hcovers := by simpa using hcovers
          hb := hb.of_eq fun i hi => hr_in i (by omega)
          hcsr := hcsr.of_outside fun a ha => by
            rw [hmem_in, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
          hmate := fun v' => by
            rw [hmem_in, Function.update_of_ne (by have := v'.isLt; omega),
              Function.update_of_ne (by have := v'.isLt; omega)]
            exact hmate v'
          hdM := fun u' => by
            rw [hmem_in, Function.update_of_ne (by have := u'.isLt; omega),
              Function.update_of_ne (by have := u'.isLt; omega)]
            exact hdM u'
          hvisM := fun v' => by
            rw [hmem_in, Function.update_of_ne (by have := v'.isLt; omega),
              Function.update_of_ne (by have := v'.isLt; omega)]
            exact hvisM v'
          haugM := fun i hi => by
            have := hcovers.length_le
            rw [hmem_in, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
            exact haugM i hi
          hstack := fun _ hi => absurd hi (Nat.not_lt_zero _)
          hsu := by
            simp only [Nat.add_zero, hmem_in]
            rw [Function.update_of_ne (by omega), Function.update_self]
          hsp := by
            simp only [Nat.add_zero, List.length_nil, hmem_in]
            exact Function.update_self _ _ _
          hrk := (hr_in rk (by decide)).trans hrk
          hrd := hrd_in
          hal := hal_in
          hact := hact_in }
      have hdfs := exec_dfsLevel hk_le augPairs k 0 (by omega) [] u [] (inst.adj u)
        vis x_in rfl hfr_in hfit
      rw [← hkDfs_eq_dfsLevel] at hdfs
      obtain ⟨_, hpot_R, hcov_R⟩ :=
        hkDfs_pure_props (inst := inst) (mate := mate) (dist := dist) k 0 u vis augPairs hcovers
      have hacc_eq := hkDfs_acc inst.graph inst.adj mate dist k 0 u vis pureAcc
      have hbody_exec : ∃ x₁ aug₁,
          ExecWithin w dfsRootBody x x₁
            (38 * (inst.adj u).length + 47 +
              (dfsPot inst mate vis -
                dfsPot inst mate (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1) +
              12 * (aug₁.length - augPairs.length)) ∧
          augPairs.length ≤ aug₁.length ∧
          (∀ i : Fin 34, i.val < 22 → x₁.regs i = x.regs i) ∧
          x₁.regs qHead = pre.length + 1 ∧
          x₁.regs augLen = aug₁.length ∧
          VisCovers (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 aug₁ ∧
          aug₁.toFinset = ((hkDfs inst.graph inst.adj mate dist k 0 u vis pureAcc).2.getD
            pureAcc).toFinset ∧
          VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
            (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 x₁.mem ∧
          AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
            (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6) aug₁ x₁.mem ∧
          (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m ≤ a ∧
              a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
            x₁.mem a = x.mem a) := by
        have wrap_root (s_mid : Data 34) {t_dfs : ℕ}
            (he_dfs : ExecWithin w (.loop (.eq active one) dfsStepBody) x_in s_mid t_dfs)
            (hr_mid : ∀ i : Fin 34, i.val < 25 → s_mid.regs i = x_in.regs i) :
            ExecWithin w dfsRootBody x (s_mid.set qHead (pre.length + 1))
              (2 + ((8 + t_dfs + 1) + 1)) := by
          have hqh_mid : s_mid.regs qHead = pre.length :=
            (hr_mid qHead (by decide)).trans ((hr_in qHead (by decide)).trans hqh)
          have hone_mid : s_mid.regs one = 1 :=
            (hr_mid one (by decide)).trans hfr_in.hb.hone
          have hinc : ExecWithin w (ram[ qHead ← qHead + one ] : Code .standard 34)
              s_mid (s_mid.set qHead (pre.length + 1)) 1 := by
            refine WP.execWithin ?_
            wram_exec [hqh_mid, hone_mid, hf_qh1]
            rfl
          exact he_chk.seq
            (((he_in.seq he_dfs).branch_pos (neg := (ram[ tmp ← zero ] : Code .standard 34))
              hc_val1).seq hinc)
        cases hr2 : (hkDfs inst.graph inst.adj mate dist k 0 u vis []).2 with
        | some q =>
          rw [hr2] at hdfs hcov_R hacc_eq
          obtain ⟨z_mid, he_dfs, hr_mid, hal_mid, hvis_mid, haug_mid, hf_mid⟩ := hdfs
          simp only [List.nil_append] at hal_mid haug_mid
          have he_full := wrap_root z_mid he_dfs hr_mid
          have hq_len : q.length = k + 1 := hcov_R.2
          refine ⟨z_mid.set qHead (pre.length + 1), augPairs ++ q,
            he_full.mono (by rw [List.length_append, hq_len]; omega),
            by simp, fun i hi => by wram_simp [(hr_mid i (by omega)).trans (hr_in i (by omega))],
            by wram_simp, by wram_simp [hal_mid], hcov_R.1, ?_, hvis_mid, haug_mid,
            fun a ha => ?_⟩
          · rw [hacc_eq]
            simp [hfin_eq, Finset.union_comm]
          · dsimp only [Data.set]
            rw [hf_mid a ha, hmem_in, Function.update_of_ne (by omega),
              Function.update_of_ne (by omega)]
        | none =>
          rw [hr2] at hdfs hcov_R hacc_eq
          obtain ⟨y_mid, htrans, hr_mid, hal_mid, hact_mid, hvis_mid, hf_mid⟩ := hdfs
          simp only [↓reduceIte] at hact_mid
          have hc_exit : ¬(Cond.eq active one).Holds y_mid := by
            rw [Cond.holds_eq, hact_mid, (hr_mid one (by decide)).trans hfr_in.hb.hone]
            simp
          have he_dfs := htrans y_mid 2 (ExecWithin.loop_exit hc_exit)
          have he_full := wrap_root y_mid he_dfs hr_mid
          have haug_ymid : AugMem
              (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
              (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6)
              augPairs y_mid.mem := fun i hi => by
            have := hcovers.length_le
            rw [hf_mid _ (by simp only [DfsSubtreeOutside]; omega),
              hf_mid _ (by simp only [DfsSubtreeOutside]; omega)]
            exact hfr_in.haugM i hi
          refine ⟨y_mid.set qHead (pre.length + 1), augPairs,
            he_full.mono (by omega), le_refl _,
            fun i hi => by wram_simp [(hr_mid i (by omega)).trans (hr_in i (by omega))],
            by wram_simp, by wram_simp [hal_mid], hcov_R, ?_, hvis_mid, haug_ymid,
            fun a ha => ?_⟩
          · rw [hacc_eq]
            simp [hfin_eq]
          · dsimp only [Data.set]
            rw [hf_mid a (by simp only [DfsSubtreeOutside]; omega), hmem_in,
              Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      obtain ⟨x₁, aug₁, he_body, hlen_le₁, hr₁, hqh₁, hal₁, hcov₁, hfin₁, hvis₁, haug₁, hf₁⟩ :=
        hbody_exec
      have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => hr₁ i (by omega)
      have hcsr₁ : CSRMem inst bOff x₁.mem := hcsr.of_outside fun a ha => hf₁ a (by omega)
      have hmate₁ : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x₁.mem :=
        fun v' => (hf₁ _ (by have := v'.isLt; omega)).trans (hmate v')
      have hdM₁ : DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) dist x₁.mem :=
        fun u' => (hf₁ _ (by have := u'.isLt; omega)).trans (hdM u')
      obtain ⟨y, augPairs', he_rest, hlen_le₂, hr₂, hal₂, hcov₂, hfin₂, haug₂, hf₂⟩ :=
        ih (pre ++ [u]) hsplit' (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 aug₁
          ((hkDfs inst.graph inst.adj mate dist k 0 u vis pureAcc).2.getD pureAcc)
          hcov₁ hfin₁ x₁ hb₁ hcsr₁ hmate₁ hdM₁ hvis₁ haug₁
          ((hr₁ rk (by decide)).trans hrk) (by simpa using hqh₁) hal₁
      have heq_roots : hkDfsRoots inst.graph inst.adj mate dist k (u :: us) vis pureAcc =
          hkDfsRoots inst.graph inst.adj mate dist k us
            (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1
            ((hkDfs inst.graph inst.adj mate dist k 0 u vis pureAcc).2.getD pureAcc) := by
        have h1 : (hkDfs inst.graph inst.adj mate dist k 0 u vis pureAcc).1 =
            (hkDfs inst.graph inst.adj mate dist k 0 u vis []).1 := by
          rw [hkDfs_acc]
        simp only [hkDfsRoots, ite_eq_left hdu0, h1]
      refine ⟨y, augPairs', (ExecWithin.loop_iter hc_loop he_body he_rest).mono ?_,
        hlen_le₁.trans hlen_le₂,
        fun i hi => (hr₂ i hi).trans (hr₁ i (by omega)),
        hal₂, hcov₂, by rw [heq_roots]; exact hfin₂, haug₂,
        fun a ha => (hf₂ a ha).trans (hf₁ a ha)⟩
      simp only [List.map_cons, List.sum_cons]
      omega
    · have henc_ne1 : encodeDist (vget dist u) ≠ 1 := by
        cases h : vget dist u with
        | none => simp [encodeDist]
        | some j =>
          simp only [encodeDist]
          intro heq
          exact hdu0 (by rw [h]; congr 1; omega)
      have hc_nval1 : ¬(Cond.eq val one).Holds x_chk := by
        rw [Cond.holds_eq, hb_chk.hone]
        dsimp only [x_chk]
        wram_simp
        exact henc_ne1
      have hnop : ExecWithin w (ram[ tmp ← zero ] : Code .standard 34)
          x_chk (x_chk.set tmp 0) 1 := by
        refine WP.execWithin ?_
        wram_exec [hb_chk.hzero]
        rfl
      have hqh_chk : x_chk.regs qHead = pre.length := by
        dsimp only [x_chk]; wram_simp [hqh]
      have hinc : ExecWithin w (ram[ qHead ← qHead + one ] : Code .standard 34)
          (x_chk.set tmp 0) ((x_chk.set tmp 0).set qHead (pre.length + 1)) 1 := by
        refine WP.execWithin ?_
        wram_exec [hqh_chk, hb_chk.hone, hf_qh1]
        rfl
      have he_skip : ExecWithin w dfsRootBody x
          ((x_chk.set tmp 0).set qHead (pre.length + 1)) 6 :=
        he_chk.seq ((hnop.branch_neg hc_nval1).seq hinc)
      let x₁ := (x_chk.set tmp 0).set qHead (pre.length + 1)
      have hb₁ : BaseRegs inst bOff x₁ :=
        hb.of_eq fun i hi => by dsimp only [x₁, x_chk]; wram_simp
      obtain ⟨y, augPairs', he_rest, hlen_le₂, hr₂, hal₂, hcov₂, hfin₂, haug₂, hf₂⟩ :=
        ih (pre ++ [u]) hsplit' vis augPairs pureAcc hcovers hfin_eq x₁ hb₁
          hcsr hmate hdM hvisM haugM
          (by dsimp only [x₁, x_chk]; wram_simp [hrk])
          (by dsimp only [x₁, x_chk]; wram_simp; simp)
          (by dsimp only [x₁, x_chk]; wram_simp [hal])
      refine ⟨y, augPairs', (ExecWithin.loop_iter hc_loop he_skip he_rest).mono ?_,
        hlen_le₂,
        fun i hi => (hr₂ i hi).trans (by dsimp only [x₁, x_chk]; wram_simp),
        hal₂, hcov₂, by simpa [hkDfsRoots, hdu0] using hfin₂, haug₂,
        fun a ha => hf₂ a ha⟩
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem exec_applyAugCode {w bOff : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
    (augPairs : List (Fin inst.m × Fin inst.r))
    (hlen_le : augPairs.length ≤ inst.r)
    (x : Data 34) (hb : BaseRegs inst bOff x)
    (hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem)
    (haugM : AugMem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6)
      (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6) augPairs x.mem)
    (hal : x.regs augLen = augPairs.length)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w applyAugCode x y (9 * augPairs.length + 3) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      MateMem (bOff + inst.m + 1 + inst.numEdges) (hkApplyEdges mate augPairs) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r) → y.mem a = x.mem a) := by
  have hs₀ : ∃ s₀, ExecWithin w (ram[ idx ← #0 ] : Code .standard 34) x s₀ 1 ∧
      s₀ = x.set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let P (t : ℕ) (y : Data 34) : Prop :=
    t ≤ augPairs.length ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      y.regs augLen = augPairs.length ∧
      MateMem (bOff + inst.m + 1 + inst.numEdges) (hkApplyEdges mate (augPairs.take t)) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + inst.r) → y.mem a = x.mem a)
  have hP₀ : P 0 (x.set idx 0) := by
    refine ⟨Nat.zero_le _, fun i hi => by wram_simp, by wram_simp [hal], ?_, fun _ _ => rfl⟩
    simpa [hkApplyEdges] using hmate
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < augPairs.length) :
      ∃ z, ExecWithin w applyAugBody y z 7 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hal_y, hmate_y, hf_y⟩ := hy
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hau : y.mem (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 +
        y.regs idx) = (augPairs[y.regs idx]'hlt).1.val := by
      rw [hf_y _ (by omega)]
      exact (haugM (y.regs idx) hlt).1
    have hav : y.mem (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6 +
        y.regs idx) = (augPairs[y.regs idx]'hlt).2.val := by
      rw [hf_y _ (by omega)]
      exact (haugM (y.regs idx) hlt).2
    have hf1 : Fits w (bOff + inst.m + 1 + inst.numEdges + 2 * inst.r + 6 * inst.m + 6 +
        y.regs idx) := hfit.of_le (by omega)
    have hf2 : Fits w (bOff + inst.m + 1 + inst.numEdges + 3 * inst.r + 6 * inst.m + 6 +
        y.regs idx) := hfit.of_le (by omega)
    have hf3 : Fits w (bOff + inst.m + 1 + inst.numEdges + (augPairs[y.regs idx]'hlt).2.val) :=
      hfit.of_le (by have := (augPairs[y.regs idx]'hlt).2.isLt; omega)
    have hf4 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold applyAugBody
    wram_exec [hby.hbAugU, hby.hbAugV, hby.hbColMate, hby.hone, hau, hav, hf1, hf2, hf3, hf4]
    have htake_eq : hkApplyEdges mate (augPairs.take (y.regs idx + 1)) =
        vset (hkApplyEdges mate (augPairs.take (y.regs idx)))
          (augPairs[y.regs idx]'hlt).2 (some (augPairs[y.regs idx]'hlt).1) := by
      rw [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some]
      simp only [hkApplyEdges, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], by wram_simp [hal_y], ?_,
      fun a ha => ?_⟩, by wram_simp⟩
    · intro v₀
      have := v₀.isLt
      have := (augPairs[y.regs idx]'hlt).2.isLt
      rw [htake_eq]
      rcases eq_or_ne v₀ (augPairs[y.regs idx]'hlt).2 with rfl | hne
      · wram_simp
        simp [encodeOptFin]
      · have hne_val : v₀.val ≠ (augPairs[y.regs idx]'hlt).2.val := fun h => hne (Fin.ext h)
        wram_simp
        rw [vget_vset_ne _ _ hne.symm]
        exact hmate_y v₀
    · have := (augPairs[y.regs idx]'hlt).2.isLt
      wram_simp
      exact hf_y a ha
  obtain ⟨y, hl, hPend, _⟩ := ExecWithin.loop_count P (fun y hy => hy.2.2.1) hbody
    (x := x.set idx 0) (by simp) (by simpa using hP₀)
  obtain ⟨_, hr, _, hmate', hf'⟩ := hPend
  rw [List.take_of_length_le (le_refl _)] at hmate'
  exact ⟨y, (he₀.seq hl).mono (by simp; omega), hr, hmate', hf'⟩

private theorem exec_dfsPhaseCode {w bOff k : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r} {dist : Vector (Option ℕ) inst.m}
    (hM : IsMatching inst.graph (mateMatching mate))
    (hk_le : k ≤ inst.m + 1)
    (x : Data 34) (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hmate : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem)
    (hdM : DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) dist x.mem)
    (hrk : x.regs rk = k)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w dfsPhaseCode x y (49 * inst.m + 39 * inst.r + 76 * inst.numEdges + 11) ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      MateMem (bOff + inst.m + 1 + inst.numEdges)
        (hkPhase inst.graph inst.adj mate dist k) y.mem ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a) := by
  obtain ⟨y₁, he₁, hr₁, hmem₁⟩ := exec_clearAt bVisReg rr (by decide) (by decide) x
    hb.hzero hb.hone (by rw [hb.hbVis, hb.hrr]; exact hfit.of_le (by omega))
  rw [hb.hrr] at he₁
  rw [hb.hbVis, hb.hrr] at hmem₁
  have hs₀ : ∃ y₂, ExecWithin w
      (ram[ augLen ← #0; qHead ← #0 ] : Code .standard 34) y₁ y₂ 2 ∧
      y₂ = (y₁.set augLen 0).set qHead 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨y₂, he₂, rfl⟩ := hs₀
  let y₂ := (y₁.set augLen 0).set qHead 0
  have hb₂ : BaseRegs inst bOff y₂ :=
    hb.of_eq fun i hi => by dsimp only [y₂]; wram_simp [hr₁ i (by omega)]
  have hcsr₂ : CSRMem inst bOff y₂.mem := hcsr.of_outside fun a ha => by
    simp only [y₂, Data.set, hmem₁]
    exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  have hmate₂ : MateMem (bOff + inst.m + 1 + inst.numEdges) mate y₂.mem := fun v' => by
    have := v'.isLt
    simp only [y₂, Data.set, hmem₁]
    rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
    exact hmate v'
  have hdM₂ : DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) dist y₂.mem :=
    fun u' => by
      have := u'.isLt
      simp only [y₂, Data.set, hmem₁]
      rw [clear_of_not_owns (by simp only [Block.Owns]; omega)]
      exact hdM u'
  have hvis₂ : VisMem (bOff + inst.m + 1 + inst.numEdges + inst.r + 3 * inst.m)
      (Vector.replicate inst.r false) y₂.mem := fun v' => by
    have := v'.isLt
    simp only [y₂, Data.set, hmem₁, vget_replicate, Bool.false_eq_true, ↓reduceIte]
    exact clear_of_owns (by simp only [Block.Owns]; omega)
  have hcov₀ : VisCovers (Vector.replicate inst.r false) ([] : List (Fin inst.m × Fin inst.r)) :=
    ⟨List.nodup_nil, fun _ h => nomatch h⟩
  obtain ⟨y₃, augPairs', he₃, _, hr₃, hal₃, hcov₃, hfin₃, haug₃, hf₃⟩ :=
    exec_dfsRootsLoop hk_le [] (List.finRange inst.m) rfl (Vector.replicate inst.r false)
      [] [] hcov₀ rfl y₂ hb₂ hcsr₂ hmate₂ hdM₂ hvis₂ (fun _ hi => nomatch hi)
      (by dsimp only [y₂]; wram_simp [hr₁ rk (by decide), hrk])
      (by dsimp only [y₂]; wram_simp; rfl) (by dsimp only [y₂]; wram_simp; rfl) hfit
  have hlen_aug : augPairs'.length ≤ inst.r := hcov₃.length_le
  have hb₃ : BaseRegs inst bOff y₃ := hb₂.of_eq fun i hi => hr₃ i (by omega)
  have hmate₃ : MateMem (bOff + inst.m + 1 + inst.numEdges) mate y₃.mem :=
    fun v' => (hf₃ _ (by have := v'.isLt; omega)).trans (hmate₂ v')
  obtain ⟨y₄, he₄, hr₄, hmate₄, hf₄⟩ :=
    exec_applyAugCode augPairs' hlen_aug y₃ hb₃ hmate₃ haug₃ hal₃ hfit
  have hnd_es :
      ((hkDfsRoots inst.graph inst.adj mate dist k (List.finRange inst.m)
        (Vector.replicate inst.r false) []).map Prod.snd).Nodup :=
    hkDfsRoots_nodup_snd mate dist k (List.finRange inst.m)
      (Vector.replicate inst.r false) [] hcov₀
  have heq_apply :
      hkApplyEdges mate augPairs' = hkPhase inst.graph inst.adj mate dist k :=
    hkApplyEdges_eq_of_toFinset_eq mate hcov₃.1 hnd_es hfin₃
  rw [heq_apply] at hmate₄
  have hsum_roots :
      ((List.finRange inst.m).map (fun u => 38 * (inst.adj u).length + 49)).sum =
        38 * inst.numEdges + 49 * inst.m := by
    rw [← Fin.sum_univ_def]
    simp [SparseInstance.numEdges, bipAdjSteps, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_const, Nat.mul_comm]
  have hpot_init := dfsPot_replicate_le hM
  refine ⟨y₄, (he₁.seq (he₂.seq (he₃.seq he₄))).mono ?_,
    fun i hi => (hr₄ i hi).trans ((hr₃ i hi).trans
      (by dsimp only [y₂]; wram_simp [hr₁ i (by omega)])),
    hmate₄, fun a ha => ?_⟩
  · simp only [List.length_nil, Nat.sub_zero] at he₃
    omega
  · rw [hf₄ a (by omega), hf₃ a (by omega)]
    simp only [y₂, Data.set, hmem₁]
    exact clear_of_not_owns (by simp only [Block.Owns]; omega)

private def phaseRoundBody : Code .standard 34 :=
  .seq bfsCode
    (.branch (.eq rfound one) dfsPhaseCode (ram[ phaseActive ← zero ]))

/-- In-memory Hopcroft–Karp solver on a CSR bipartite graph `inst` stored at `bOff`.
Initializes `colMate[0..r)` to `m` (`none`), then alternates `bfsCode` and `dfsPhaseCode` until
no augmenting path remains, leaving the maximum matching in `colMate[0..r)` and the closed
alternating-layer distances in `dist[0..m)`. -/
def coreCode : Code .standard 34 :=
  .seq (fillConst bColMateReg rr rm)
    (.seq (ram[ phaseActive ← one ])
      (.loop (.eq phaseActive one) phaseRoundBody))

private def roundTime (m r E : ℕ) : ℕ :=
  100 * m + 47 * r + 112 * E + 48

/-- Instruction bound `O((m + r + E) (√ν + 1))` for `coreCode` on a CSR graph with sides `m, r`,
`E` edge entries, and maximum matching cardinality `ν`. -/
@[expose] def coreTime (m r E ν : ℕ) : ℕ :=
  (2 * Nat.sqrt ν + 1) * (100 * m + 47 * r + 112 * E + 48) + 5 * r + 6

private theorem exec_phaseLoop {w bOff : ℕ} {inst : SparseInstance} :
    ∀ (fuel n : ℕ) (mate : Vector (Option (Fin inst.m)) inst.r),
      IsMatching inst.graph (mateMatching mate) →
      inst.m < fuel + (mateMatching mate).card →
      ∀ (x : Data 34),
        BaseRegs inst bOff x →
        CSRMem inst bOff x.mem →
        MateMem (bOff + inst.m + 1 + inst.numEdges) mate x.mem →
        x.regs phaseActive = 1 →
        Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8) →
        let res := hkLoop inst.graph inst.adj fuel n mate
        ∃ y, ExecWithin w (.loop (.eq phaseActive one) phaseRoundBody) x y
            ((res.phases - n + 1) * roundTime inst.m inst.r inst.numEdges + 2) ∧
          (∀ i : Fin 34, i.val < 19 → y.regs i = x.regs i) ∧
          MateMem (bOff + inst.m + 1 + inst.numEdges) res.mate y.mem ∧
          DistMem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) res.dist y.mem ∧
          (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
              a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
            y.mem a = x.mem a) := by
  intro fuel
  induction fuel with
  | zero =>
    intro _ mate hM hfuel
    have := hM.card_le_card_left
    simp only [Fintype.card_fin] at this
    omega
  | succ fuel ih =>
    intro n mate hM hfuel x hb hcsr hmate hpa hfit
    have hc_loop : (Cond.eq phaseActive one).Holds x := by
      rw [Cond.holds_eq, hpa, hb.hone]
    obtain ⟨x₁, he_bfs, hr₁, hdM₁, hrk₁, hrf₁, hf₁⟩ := exec_bfsCode x hb hcsr hmate hfit
    set b := hkBfs inst.graph inst.adj mate with hb_def
    have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => hr₁ i (by omega)
    have hcsr₁ : CSRMem inst bOff x₁.mem := hcsr.of_outside fun a ha => hf₁ a (by omega)
    have hmate₁ : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x₁.mem :=
      fun v' => (hf₁ _ (by have := v'.isLt; omega)).trans (hmate v')
    have hpa₁ : x₁.regs phaseActive = 1 := (hr₁ phaseActive (by decide)).trans hpa
    by_cases hbf : b.found = true
    · have hc_rf : (Cond.eq rfound one).Holds x₁ := by
        rw [Cond.holds_eq, hrf₁, hb₁.hone, ite_eq_left hbf]
      have hk_le : b.k ≤ inst.m + 1 := hkBfs_k_le inst.graph inst.adj mate
      obtain ⟨x₂, he_dfs, hr₂, hmate₂, hf₂⟩ :=
        exec_dfsPhaseCode hM hk_le x₁ hb₁ hcsr₁ hmate₁ hdM₁ hrk₁ hfit
      have he_br :=
        he_dfs.branch_pos (neg := (ram[ phaseActive ← zero ] : Code .standard 34)) hc_rf
      have hb_spec := hkBfs_spec inst.bipAdjValid_graph (mate := mate)
      rw [← hb_def] at hb_spec
      obtain ⟨N, hN, hmate_aug⟩ :=
        hkPhase_spec (k := b.k) (dist := b.dist) inst.bipAdjValid_graph hM hb_spec.exact
      obtain ⟨t, ht, hfree⟩ := hb_spec.found_true hbf
      have hM' : IsMatching inst.graph
          (mateMatching (hkPhase inst.graph inst.adj mate b.dist b.k)) :=
        hmate_aug ▸ hN.isMatching_augment hM
      have hcard_lt : (mateMatching mate).card <
          (mateMatching (hkPhase inst.graph inst.adj mate b.dist b.k)).card :=
        hmate_aug ▸ hN.card_lt_card_augment_of_mem_altRight hM hb_spec.noShort ht hfree
      have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq fun i hi => hr₂ i (by omega)
      have hcsr₂ : CSRMem inst bOff x₂.mem := hcsr₁.of_outside fun a ha => hf₂ a (by omega)
      have hpa₂ : x₂.regs phaseActive = 1 := (hr₂ phaseActive (by decide)).trans hpa₁
      have hpost_phases := (hkLoop_spec inst.bipAdjValid_graph fuel (n + 1)
        (hkPhase inst.graph inst.adj mate b.dist b.k) hM' (by omega)).le_phases
      obtain ⟨y, he_rec, hr₃, hmate₃, hdM₃, hf₃⟩ :=
        ih (n + 1) (hkPhase inst.graph inst.adj mate b.dist b.k) hM' (by omega) x₂ hb₂ hcsr₂
          hmate₂ hpa₂ hfit
      dsimp only [hkLoop]
      rw [← hb_def, ite_eq_left hbf]
      set remPhases :=
        (hkLoop inst.graph inst.adj fuel (n + 1)
          (hkPhase inst.graph inst.adj mate b.dist b.k)).phases - (n + 1)
      have hph_arith :
          (hkLoop inst.graph inst.adj fuel (n + 1)
            (hkPhase inst.graph inst.adj mate b.dist b.k)).phases - n + 1 =
          (remPhases + 1) + 1 := by
        omega
      refine ⟨y, (ExecWithin.loop_iter hc_loop (he_bfs.seq he_br) he_rec).mono ?_,
        fun i hi => (hr₃ i hi).trans ((hr₂ i (by omega)).trans (hr₁ i (by omega))),
        hmate₃, hdM₃,
        fun a ha => (hf₃ a ha).trans ((hf₂ a ha).trans (hf₁ a (by omega)))⟩
      simp only [hph_arith, Nat.add_mul, Nat.one_mul, roundTime]
      omega
    · have hc_rf : ¬(Cond.eq rfound one).Holds x₁ := by
        rw [Cond.holds_eq, hrf₁, hb₁.hone, ite_eq_right hbf]
        simp
      have hstop : ExecWithin w (ram[ phaseActive ← zero ] : Code .standard 34)
          x₁ (x₁.set phaseActive 0) 1 := by
        refine WP.execWithin ?_
        wram_exec [hb₁.hzero]
        rfl
      have he_br := hstop.branch_neg (pos := dfsPhaseCode) hc_rf
      have hc_exit : ¬(Cond.eq phaseActive one).Holds (x₁.set phaseActive 0) := by
        rw [Cond.holds_eq]
        have ha0 : (x₁.set phaseActive 0).regs phaseActive = 0 := by wram_simp
        have ho1 : (x₁.set phaseActive 0).regs one = 1 := by wram_simp [hb₁.hone]
        omega
      have he_exit := ExecWithin.loop_exit (body := phaseRoundBody) (w := w) hc_exit
      dsimp only [hkLoop]
      rw [← hb_def, ite_eq_right hbf]
      refine ⟨x₁.set phaseActive 0,
        (ExecWithin.loop_iter hc_loop (he_bfs.seq he_br) he_exit).mono ?_,
        fun i hi => by wram_simp [hr₁ i (by omega)],
        hmate₁, hdM₁, fun a ha => hf₁ a (by omega)⟩
      change _ ≤ (n - n + 1) * roundTime inst.m inst.r inst.numEdges + 2
      simp only [Nat.sub_self, Nat.zero_add, Nat.one_mul, roundTime]
      omega

/-- **In-memory `O((m + r + |E|) (√ν + 1))` execution of Hopcroft–Karp (`coreCode`).**
Starting from any state `x` with `BaseRegs inst bOff x` and `CSRMem inst bOff x.mem`, `coreCode`
terminates within `coreTime inst.m inst.r inst.numEdges inst.maxMatchingCard` instructions, leaving
the maximum matching `res.mate` in `colMate[0..r)` and the closed alternating-layer distances
`res.dist` in `dist[0..m)`, while preserving `BaseRegs`, `CSRMem`, and all memory outside the
workspace `[bOff + m + 1 + numEdges, outBase)`. -/
theorem core_exec {w bOff : ℕ} (inst : SparseInstance) (x : Data 34)
    (hb : BaseRegs inst bOff x) (hcsr : CSRMem inst bOff x.mem)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    let res := hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)
    ∃ y, ExecWithin w coreCode x y
        (coreTime inst.m inst.r inst.numEdges inst.maxMatchingCard) ∧
      BaseRegs inst bOff y ∧
      CSRMem inst bOff y.mem ∧
      (∀ v : Fin inst.r, y.mem (bOff + inst.m + 1 + inst.numEdges + v.val) =
        match vget res.mate v with | some u => u.val | none => inst.m) ∧
      (∀ u : Fin inst.m, y.mem (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m + u.val) =
        match vget res.dist u with | none => 0 | some j => j + 1) ∧
      (∀ a, ¬(bOff + inst.m + 1 + inst.numEdges ≤ a ∧
          a < bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6) →
        y.mem a = x.mem a) := by
  obtain ⟨x₁, he₁, hr₁, hfill₁, hf₁⟩ := exec_fillConst bColMateReg rr rm
    (by decide) (by decide) (by decide) x hb.hone
    (by rw [hb.hbColMate, hb.hrr]; exact hfit.of_le (by omega))
    (by rw [hb.hrr]; exact hfit.of_le (by omega))
  rw [hb.hrr] at he₁ hfill₁
  rw [hb.hbColMate, hb.hrm] at hfill₁
  rw [hb.hbColMate, hb.hrr] at hf₁
  have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  have hs₂ : ∃ x₂, ExecWithin w (ram[ phaseActive ← one ] : Code .standard 34) x₁ x₂ 1 ∧
      x₂ = x₁.set phaseActive 1 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₁.hone]
    rfl
  obtain ⟨x₂, he₂, rfl⟩ := hs₂
  let x₂ := x₁.set phaseActive 1
  have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq fun i hi => by dsimp only [x₂]; wram_simp
  have hcsr₂ : CSRMem inst bOff x₂.mem := hcsr.of_outside fun a ha => hf₁ a (by omega)
  have hmate₂ : MateMem (bOff + inst.m + 1 + inst.numEdges)
      (Vector.replicate inst.r none) x₂.mem := fun v' => by
    simp only [x₂, Data.set, vget_replicate, encodeOptFin]
    exact hfill₁ v'.val v'.isLt
  have hM₀ : IsMatching inst.graph
      (mateMatching (Vector.replicate inst.r (none : Option (Fin inst.m)))) := by
    rw [mateMatching_replicate_none]
    exact ⟨by simp, by simp, by simp⟩
  have hcard₀ : (mateMatching (Vector.replicate inst.r (none : Option (Fin inst.m)))).card = 0 := by
    rw [mateMatching_replicate_none]; rfl
  obtain ⟨y, he₃, hr₃, hmate₃, hdM₃, hf₃⟩ :=
    exec_phaseLoop (inst.m + 1) 0 (Vector.replicate inst.r none) hM₀ (by omega) x₂ hb₂ hcsr₂
      hmate₂ (by dsimp only [x₂]; wram_simp) hfit
  have hph_bound :
      (hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).phases ≤
        2 * Nat.sqrt inst.maxMatchingCard :=
    (hopcroftKarp_correct inst.bipAdjValid_graph).2.2.2
  have he₃' : ExecWithin w (.loop (.eq phaseActive one) phaseRoundBody) x₂ y
      (((hkLoop inst.graph inst.adj (inst.m + 1) 0
          (Vector.replicate inst.r none)).phases + 1) *
        roundTime inst.m inst.r inst.numEdges + 2) := by
    simpa only [Nat.sub_zero] using he₃
  have hmul_le :
      ((hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).phases + 1) *
        roundTime inst.m inst.r inst.numEdges ≤
      (2 * Nat.sqrt inst.maxMatchingCard + 1) * roundTime inst.m inst.r inst.numEdges :=
    Nat.mul_le_mul_right _ (by omega)
  refine ⟨y, (he₁.seq (he₂.seq he₃')).mono ?_, hb₂.of_eq hr₃,
    hcsr₂.of_outside (fun a ha => hf₃ a (by omega)),
    fun v => by
      have hv := hmate₃ v
      cases h : vget (hkLoop inst.graph inst.adj (inst.m + 1) 0
          (Vector.replicate inst.r none)).mate v <;>
        simpa [encodeOptFin, h] using hv,
    fun u => by
      have hu := hdM₃ u
      cases h : vget (hkLoop inst.graph inst.adj (inst.m + 1) 0
          (Vector.replicate inst.r none)).dist u <;>
        simpa [encodeDist, h] using hu,
    fun a ha => (hf₃ a ha).trans (hf₁ a (by omega))⟩
  simp only [coreTime, roundTime] at hmul_le ⊢
  omega

/-! ## Section 4: End-to-end `State.init` programs (sparse and dense) -/

/-- Populate `bEdgesReg .. outBase` from `zero, one, two, rm, rr, rE, bOffReg`. -/
private def initBaseRegsFromCSR : Code .standard 34 := ram[
  bEdgesReg ← bOffReg + rm; bEdgesReg ← bEdgesReg + one;
  bColMateReg ← bEdgesReg + rE;
  bMLReg ← bColMateReg + rr;
  bDistReg ← bMLReg + rm;
  bQueueReg ← bDistReg + rm;
  bVisReg ← bQueueReg + rm;
  bStackUReg ← bVisReg + rr;
  bStackVReg ← bStackUReg + rm; bStackVReg ← bStackVReg + two;
  bStackPosReg ← bStackVReg + rm; bStackPosReg ← bStackPosReg + two;
  bAugUReg ← bStackPosReg + rm; bAugUReg ← bAugUReg + two;
  bAugVReg ← bAugUReg + rr;
  outBase ← bAugVReg + rr ]

private theorem exec_initBaseRegsFromCSR {w bOff : ℕ} (inst : SparseInstance) (x : Data 34)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (hrm : x.regs rm = inst.m) (hrr : x.regs rr = inst.r) (hrE : x.regs rE = inst.numEdges)
    (hbOff : x.regs bOffReg = bOff)
    (hfit : Fits w (bOff + 7 * inst.m + 5 * inst.r + inst.numEdges + 8)) :
    ∃ y, ExecWithin w initBaseRegsFromCSR x y 16 ∧
      BaseRegs inst bOff y ∧ y.mem = x.mem := by
  have hf1 : Fits w (bOff + inst.m) := hfit.of_le (by omega)
  have hf2 : Fits w (bOff + inst.m + 1) := hfit.of_le (by omega)
  have hf3 : Fits w (bOff + inst.m + 1 + inst.numEdges) := hfit.of_le (by omega)
  have hf4 : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r) := hfit.of_le (by omega)
  have hf5 : Fits w (bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) :=
    hfit.of_le (by omega)
  have hf6 : Fits w ((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) :=
    hfit.of_le (by omega)
  have hf7 : Fits w (((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) + inst.m) :=
    hfit.of_le (by omega)
  have hf8 : Fits w ((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) := hfit.of_le (by omega)
  have hf9 : Fits w (((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) + inst.m) := hfit.of_le (by omega)
  have hf10 : Fits w ((((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) + inst.m) + 2) := hfit.of_le (by omega)
  have hf11 : Fits w (((((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) + inst.m) + 2) + inst.m) := hfit.of_le (by omega)
  have hf12 : Fits w ((((((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) + inst.m) + 2) + inst.m) + 2) := hfit.of_le (by omega)
  have hf13 : Fits w (((((((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) + inst.m) + 2) + inst.m) + 2) + inst.m) := hfit.of_le (by omega)
  have hf14 : Fits w ((((((((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) + inst.m) + 2) + inst.m) + 2) + inst.m) + 2) := hfit.of_le (by omega)
  have hf15 : Fits w (((((((((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) + inst.m) + 2) + inst.m) + 2) + inst.m) + 2) + inst.r) :=
    hfit.of_le (by omega)
  have hf16 : Fits w ((((((((((((bOff + inst.m + 1 + inst.numEdges + inst.r + inst.m) + inst.m) +
      inst.m) + inst.r) + inst.m) + 2) + inst.m) + 2) + inst.m) + 2) + inst.r) + inst.r) :=
    hfit.of_le (by omega)
  refine WP.exists_execWithin ?_
  unfold initBaseRegsFromCSR
  wram_exec [h1, h2, hrm, hrr, hrE, hbOff,
    hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16]
  refine ⟨?_, rfl⟩
  exact
    { hzero := by wram_simp [h0]
      hone := by wram_simp [h1]
      htwo := by wram_simp [h2]
      hrm := by wram_simp [hrm]
      hrr := by wram_simp [hrr]
      hrE := by wram_simp [hrE]
      hbOff := by wram_simp [hbOff]
      hbEdges := by wram_simp
      hbColMate := by wram_simp
      hbML := by wram_simp
      hbDist := by wram_simp
      hbQueue := by wram_simp; omega
      hbVis := by wram_simp; omega
      hbStackU := by wram_simp; omega
      hbStackV := by wram_simp; omega
      hbStackPos := by wram_simp; omega
      hbAugU := by wram_simp; omega
      hbAugV := by wram_simp; omega
      houtBase := by wram_simp; omega }

private def emitMatchingBody : Code .standard 34 := ram[
  addr ← bColMateReg + idx; val ← *addr;
  if val < rm then [
    val2 ← two * acc;
    addr ← outBase + one; addr ← addr + val2; *addr ← val;
    addr ← addr + one; *addr ← idx;
    acc ← acc + one
  ] else [ tmp ← zero ];
  idx ← idx + one ]

private def emitMatchingCode : Code .standard 34 :=
  .seq (ram[ acc ← #0; idx ← #0 ])
    (.seq (.loop (.lt idx rr) emitMatchingBody)
      (ram[ val2 ← two * acc; addr ← outBase; *addr ← val2 ]))

private theorem exec_emitMatchingCode {w bOff : ℕ} (inst : SparseInstance) (x : Data 34)
    (hb : BaseRegs inst bOff x)
    (hmate : ∀ v : Fin inst.r, x.mem (bOff + inst.m + 1 + inst.numEdges + v.val) =
      match vget (hkLoop inst.graph inst.adj (inst.m + 1) 0
          (Vector.replicate inst.r none)).mate v with
      | some u => u.val
      | none => inst.m)
    (hfit : Fits w (bOff + 7 * inst.m + 6 * inst.r + inst.numEdges + 8)) :
    ∃ z, ExecWithin w emitMatchingCode x z (13 * inst.r + 7) ∧
      BaseRegs inst bOff z ∧
      outputList z.mem (z.regs outBase) = inst.matchingWords ∧
      Fits w (z.regs outBase + inst.matchingWords.length) ∧
      z.regs acc = inst.maxMatchingCard := by
  let mate := (hkLoop inst.graph inst.adj (inst.m + 1) 0 (Vector.replicate inst.r none)).mate
  let mp (t : ℕ) : List (Fin inst.m × Fin inst.r) :=
    ((List.finRange inst.r).take t).filterMap fun v =>
      match vget mate v with | some u => some (u, v) | none => none
  let mw (t : ℕ) : List ℕ := (mp t).flatMap fun e => [e.1.val, e.2.val]
  let bOut := bOff + inst.m + 1 + inst.numEdges + 4 * inst.r + 6 * inst.m + 6
  have hmp_len : ∀ t : ℕ, (mp t).length ≤ t := fun t => by
    calc (mp t).length ≤ ((List.finRange inst.r).take t).length := List.length_filterMap_le _ _
      _ ≤ t := List.length_take_le _ _
  have hmw_len : ∀ t : ℕ, (mw t).length = 2 * (mp t).length := fun t => by
    simp [mw, List.length_flatMap, Nat.mul_comm]
  have hs₀ : ∃ s₀, ExecWithin w (ram[ acc ← #0; idx ← #0 ] : Code .standard 34) x s₀ 2 ∧
      s₀ = (x.set acc 0).set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let P (t : ℕ) (y : Data 34) : Prop :=
    t ≤ inst.r ∧
      (∀ i : Fin 34, i.val < 19 → y.regs i = x.regs i) ∧
      y.regs acc = (mp t).length ∧
      (∀ k : ℕ, (hk : k < (mw t).length) → y.mem (bOut + 1 + k) = (mw t)[k]'hk) ∧
      (∀ a, ¬(bOut + 1 ≤ a ∧ a < bOut + 1 + 2 * t) → y.mem a = x.mem a)
  have hP₀ : P 0 ((x.set acc 0).set idx 0) :=
    ⟨Nat.zero_le _, fun i hi => by wram_simp, by wram_simp; simp [mp],
      fun _ hk => absurd hk (by simp [mw, mp]), fun _ _ => rfl⟩
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.r) :
      ∃ y', ExecWithin w emitMatchingBody y y' 11 ∧ P (y.regs idx + 1) y' ∧
        y'.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hacc_y, hblk_y, hf_y⟩ := hy
    have hby : BaseRegs inst bOff y := hb.of_eq hr
    let v : Fin inst.r := ⟨y.regs idx, hlt⟩
    have hv_lt := v.isLt
    have hmp_le : (mp (y.regs idx)).length ≤ y.regs idx := hmp_len (y.regs idx)
    have hcm_v : y.mem (bOff + inst.m + 1 + inst.numEdges + y.regs idx) =
        match vget mate v with | some u => u.val | none => inst.m := by
      rw [hf_y _ (by dsimp only [bOut]; omega)]
      exact hmate v
    have hf_cm : Fits w (bOff + inst.m + 1 + inst.numEdges + y.regs idx) :=
      hfit.of_le (by omega)
    have hf_idx1 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hmp_succ : mp (y.regs idx + 1) =
        match vget mate v with
        | some u => mp (y.regs idx) ++ [(u, v)]
        | none => mp (y.regs idx) := by
      dsimp only [mp]
      rw [List.take_succ_finRange hlt, List.filterMap_append]
      cases h : vget mate v <;> simp [v, h]
    refine WP.exists_execWithin ?_
    unfold emitMatchingBody
    cases hmv : vget mate v with
    | none =>
      rw [hmv] at hcm_v hmp_succ
      have hnl : ¬inst.m < inst.m := Nat.lt_irrefl _
      wram_exec [hby.hbColMate, hby.hrm, hby.hzero, hby.hone, hcm_v, hnl, hf_cm, hf_idx1]
      refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi],
        by wram_simp [hacc_y, hmp_succ], fun k hk => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · have hk' : k < (mw (y.regs idx)).length := by simpa [mw, hmp_succ] using hk
        simpa [mw, hmp_succ] using hblk_y k hk'
      · wram_simp
        exact hf_y a (by omega)
    | some u =>
      have hu_lt := u.isLt
      rw [hmv] at hcm_v hmp_succ
      have hf_2a : Fits w (2 * (mp (y.regs idx)).length) := hfit.of_le (by omega)
      have hf_o1 : Fits w (bOut + 1) := hfit.of_le (by dsimp only [bOut]; omega)
      have hf_o2 : Fits w ((bOut + 1) + 2 * (mp (y.regs idx)).length) :=
        hfit.of_le (by dsimp only [bOut]; omega)
      have hf_o3 : Fits w (((bOut + 1) + 2 * (mp (y.regs idx)).length) + 1) :=
        hfit.of_le (by dsimp only [bOut]; omega)
      have hf_a1 : Fits w ((mp (y.regs idx)).length + 1) := hfit.of_le (by omega)
      have hby_ob : y.regs outBase = bOut := hby.houtBase
      wram_exec [hby.hbColMate, hby.hrm, hby.htwo, hby_ob, hby.hone,
        hacc_y, hcm_v, hu_lt, hf_cm, hf_2a, hf_o1, hf_o2, hf_o3, hf_a1, hf_idx1]
      have hmw_succ : mw (y.regs idx + 1) = mw (y.regs idx) ++ [u.val, y.regs idx] := by
        dsimp only [mw]
        rw [hmp_succ, List.flatMap_append]
        rfl
      refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi],
        by wram_simp; rw [hmp_succ, List.length_append, List.length_singleton],
        fun k hk => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · have hmw_l := hmw_len (y.regs idx)
        have hk_lt2 : k < 2 * (mp (y.regs idx)).length + 2 := by
          have hk' := hk
          rw [hmw_succ, List.length_append, hmw_l] at hk'
          simpa using hk'
        simp only [hmw_succ]
        by_cases hk_old : k < (mw (y.regs idx)).length
        · rw [List.getElem_append_left hk_old]
          wram_simp
          exact hblk_y k hk_old
        · rw [List.getElem_append_right (Nat.le_of_not_lt hk_old)]
          by_cases hk_eq : k = 2 * (mp (y.regs idx)).length
          · subst hk_eq
            wram_simp
            simp [hmw_l]
          · have hk_eq1 : k = 2 * (mp (y.regs idx)).length + 1 := by omega
            subst hk_eq1
            wram_simp
            simp [hmw_l]
      · wram_simp
        exact hf_y a (by omega)
  obtain ⟨y₁, hl, hPr, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.2.1 rr (by decide)).trans hb.hrr) hbody
    (x := (x.set acc 0).set idx 0) (by simp) (by simpa using hP₀)
  obtain ⟨_, hr₁, hacc₁, hblk₁, _⟩ := hPr
  have hb₁ : BaseRegs inst bOff y₁ := hb.of_eq hr₁
  have hmp_full : mp inst.r = inst.matchingPairs := by
    dsimp only [mp, mate]
    rw [List.take_of_length_le (by simp), inst.matchingPairs_eq_mate_filterMap]
  have hmw_full : mw inst.r = inst.matchingWords := by
    dsimp only [mw, SparseInstance.matchingWords]
    rw [hmp_full]
  have hacc_card : y₁.regs acc = inst.maxMatchingCard := by
    rw [hacc₁, hmp_full, inst.length_matchingPairs]
  have hcard_le_r : inst.maxMatchingCard ≤ inst.r := by
    rw [← inst.length_matchingPairs, ← hmp_full]
    exact hmp_len inst.r
  have hf_2nu : Fits w (2 * inst.maxMatchingCard) := hfit.of_le (by omega)
  have hf_ob : Fits w bOut := hfit.of_le (by dsimp only [bOut]; omega)
  have hb₁_ob : y₁.regs outBase = bOut := hb₁.houtBase
  have htail : ∃ z, ExecWithin w
      (ram[ val2 ← two * acc; addr ← outBase; *addr ← val2 ] : Code .standard 34) y₁ z 3 ∧
      z = ((y₁.set val2 (2 * inst.maxMatchingCard)).set addr bOut).write
        bOut (2 * inst.maxMatchingCard) := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₁.htwo, hb₁_ob, hacc_card, hf_2nu, hf_ob]
    rfl
  obtain ⟨z, he_tail, rfl⟩ := htail
  let z := ((y₁.set val2 (2 * inst.maxMatchingCard)).set addr bOut).write
    bOut (2 * inst.maxMatchingCard)
  have hbz : BaseRegs inst bOff z := hb₁.of_eq fun i hi => by dsimp only [z]; wram_simp
  have hbz_ob : z.regs outBase = bOut := hbz.houtBase
  have hout_z : outputList z.mem (z.regs outBase) = inst.matchingWords := by
    rw [hbz_ob, outputList_eq_iff, inst.length_matchingWords]
    refine ⟨by dsimp only [z]; wram_simp, fun i => ?_⟩
    have hi_val : i.val < inst.matchingWords.length := i.isLt
    have hi_mw : i.val < (mw inst.r).length := by rwa [hmw_full]
    change z.mem (bOut + 1 + i.val) = inst.matchingWords[i.val]'hi_val
    have hmem_i : z.mem (bOut + 1 + i.val) = y₁.mem (bOut + 1 + i.val) := by
      dsimp only [z]
      wram_simp
    rw [hmem_i]
    simpa [hmw_full] using hblk₁ i.val hi_mw
  have hfit_out : Fits w (z.regs outBase + inst.matchingWords.length) := by
    rw [hbz.houtBase, inst.length_matchingWords]
    exact hfit.of_le (by omega)
  exact ⟨z, (he₀.seq (hl.seq he_tail)).mono (by simp; omega), hbz, hout_z, hfit_out,
    by dsimp only [z]; wram_simp [hacc_card]⟩

/-! ### 4A. Sparse CSR endpoints -/

/-- `inst` is balanced (`m = r`) and `inst.graph` admits a perfect matching. -/
@[expose] def SparseInstance.HasPerfectMatching (inst : SparseInstance) : Prop :=
  ∃ h : inst.m = inst.r,
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching fun p : Fin inst.m × Fin inst.m =>
      inst.graph (p.1, p.2.cast h)

theorem SparseInstance.hasPerfectMatching_iff (inst : SparseInstance) :
    inst.HasPerfectMatching ↔ inst.m = inst.r ∧ inst.maxMatchingCard = inst.m := by
  rcases inst with ⟨m, r, adj⟩
  dsimp only [SparseInstance.HasPerfectMatching, SparseInstance.maxMatchingCard]
  constructor
  · rintro ⟨rfl, hpm⟩
    have hiff := decidePerfectMatchingHK_eq_true_iff (SparseInstance.bipAdjValid_graph ⟨m, m, adj⟩)
    simp only [decidePerfectMatchingHK, decide_eq_true_iff] at hiff
    exact ⟨rfl, hiff.mpr hpm⟩
  · rintro ⟨rfl, hcard⟩
    have hiff := decidePerfectMatchingHK_eq_true_iff (SparseInstance.bipAdjValid_graph ⟨m, m, adj⟩)
    simp only [decidePerfectMatchingHK, decide_eq_true_iff] at hiff
    exact ⟨rfl, hiff.mp hcard⟩

instance (inst : SparseInstance) : Decidable inst.HasPerfectMatching :=
  decidable_of_iff (inst.m = inst.r ∧ inst.maxMatchingCard = inst.m)
    inst.hasPerfectMatching_iff.symm

private def sparseSetupCode : Code .standard 34 :=
  .seq (ram[
    zero ← #0; one ← #1; two ← #2;
    addr ← #1; rm ← *addr;
    addr ← #2; rr ← *addr;
    bOffReg ← #3;
    addr ← bOffReg + rm; rE ← *addr ])
  initBaseRegsFromCSR

private def sparseCode : Code .standard 34 :=
  .seq sparseSetupCode (.seq coreCode emitMatchingCode)

private def checkPerfectTail : Code .standard 34 := ram[
  if rm = rr then [
    if acc = rm then [ acc ← one ] else [ acc ← zero ]
  ] else [ acc ← zero ] ]

/-- Standard-basis word-RAM program returning `inst.matchingWords` (`ExecutesList`) on a CSR
bipartite graph `inst : SparseInstance`. -/
def sparseMatchingProgram : Program .standard 34 :=
  sparseCode.program outBase

/-- Standard-basis word-RAM program returning the maximum matching cardinality
`inst.maxMatchingCard` (`Executes`) on `inst : SparseInstance`. -/
def sparseCardProgram : Program .standard 34 :=
  sparseCode.program acc

/-- Standard-basis word-RAM program deciding `SparseInstance.HasPerfectMatching` (`1` iff balanced
and admitting a perfect matching, `0` otherwise). -/
def sparsePerfectProgram : Program .standard 34 :=
  (sparseCode.seq checkPerfectTail).program acc

/-- Instruction bound `O((m + r + E) (√ν + 1))` for `sparseMatchingProgram`, `sparseCardProgram`,
and `sparsePerfectProgram`. -/
@[expose] def sparseTime (m r E ν : ℕ) : ℕ :=
  (2 * Nat.sqrt ν + 1) * (100 * m + 47 * r + 112 * E + 48) + 18 * r + 45

/-- Instance-only `O((m + r + E) √(min m r))` upper bound on `sparseTime`. -/
@[expose] def sparseTimeSqrtMin (m r E : ℕ) : ℕ :=
  sparseTime m r E (min m r)

theorem SparseInstance.maxMatchingCard_le_min (inst : SparseInstance) :
    inst.maxMatchingCard ≤ min inst.m inst.r := by
  have hM := (hopcroftKarp_correct inst.bipAdjValid_graph).1.1
  have hl : inst.maxMatchingCard ≤ inst.m := by
    simpa [SparseInstance.maxMatchingCard] using hM.card_le_card_left
  have hr : inst.maxMatchingCard ≤ inst.r := by
    simpa [SparseInstance.maxMatchingCard] using hM.card_le_card_right
  omega

theorem sparseTime_le_sparseTimeSqrtMin (inst : SparseInstance) :
    sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard ≤
      sparseTimeSqrtMin inst.m inst.r inst.numEdges := by
  unfold sparseTimeSqrtMin sparseTime
  have hsq : Nat.sqrt inst.maxMatchingCard ≤ Nat.sqrt (min inst.m inst.r) :=
    Nat.sqrt_le_sqrt inst.maxMatchingCard_le_min
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.mul_le_mul_right _ (by omega)) _) _

private theorem exec_sparseCode {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    ∃ z, ExecWithin w sparseCode (Data.init inst.encode) z
        (sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard - 6) ∧
      BaseRegs inst 3 z ∧
      outputList z.mem (z.regs outBase) = inst.matchingWords ∧
      Fits w (z.regs outBase + inst.matchingWords.length) ∧
      z.regs acc = inst.maxMatchingCard := by
  have hfit_all : Fits w (3 + 7 * inst.m + 6 * inst.r + inst.numEdges + 8) :=
    hw.of_le (by unfold SparseInstance.wordBound; omega)
  have hf0 : Fits w 0 := hw.of_le (by unfold SparseInstance.wordBound; omega)
  have hf1 : Fits w 1 := hw.of_le (by unfold SparseInstance.wordBound; omega)
  have hf2 : Fits w 2 := hw.of_le (by unfold SparseInstance.wordBound; omega)
  have hf3 : Fits w 3 := hw.of_le (by unfold SparseInstance.wordBound; omega)
  have hf3m : Fits w (3 + inst.m) := hfit_all.of_le (by omega)
  have hm_mem : (Data.init inst.encode : Data 34).mem 1 = inst.m := inst.init_mem_m
  have hr_mem : (Data.init inst.encode : Data 34).mem 2 = inst.r := inst.init_mem_r
  have hE_mem : (Data.init inst.encode : Data 34).mem (3 + inst.m) = inst.numEdges := by
    rw [inst.init_mem_offset (le_refl inst.m), inst.offset_m]
  have hs_pre : ∃ y₀, ExecWithin w (ram[
      zero ← #0; one ← #1; two ← #2;
      addr ← #1; rm ← *addr;
      addr ← #2; rr ← *addr;
      bOffReg ← #3;
      addr ← bOffReg + rm; rE ← *addr ] : Code .standard 34) (Data.init inst.encode) y₀ 10 ∧
      y₀.regs zero = 0 ∧ y₀.regs one = 1 ∧ y₀.regs two = 2 ∧
      y₀.regs rm = inst.m ∧ y₀.regs rr = inst.r ∧ y₀.regs rE = inst.numEdges ∧
      y₀.regs bOffReg = 3 ∧ y₀.mem = (Data.init inst.encode : Data 34).mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hm_mem, hr_mem, hE_mem, hf0, hf1, hf2, hf3, hf3m]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, by wram_simp,
      by wram_simp, by wram_simp, rfl⟩
  obtain ⟨y₀, he_pre, h0, h1, h2, hrm, hrr, hrE, hbOff, hmem₀⟩ := hs_pre
  obtain ⟨y₁, he_init, hb₁, hmem₁⟩ := exec_initBaseRegsFromCSR inst y₀ h0 h1 h2 hrm hrr hrE hbOff
    (hfit_all.of_le (by omega))
  have hcsr₁ : CSRMem inst 3 y₁.mem :=
    { hoff := fun {u} hu => by rw [hmem₁, hmem₀]; exact inst.init_mem_offset hu
      hedge := fun u {i} hi => by
        rw [hmem₁, hmem₀]
        simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using inst.init_mem_edge u hi }
  obtain ⟨y₂, he_core, hb₂, _, hmate₂, _, _⟩ := core_exec inst y₁ hb₁ hcsr₁
    (hfit_all.of_le (by omega))
  obtain ⟨z, he_emit, hbz, hout_z, hfit_out, hacc_z⟩ :=
    exec_emitMatchingCode inst y₂ hb₂ hmate₂ hfit_all
  refine ⟨z, ((he_pre.seq he_init).seq (he_core.seq he_emit)).mono ?_,
    hbz, hout_z, hfit_out, hacc_z⟩
  unfold sparseTime coreTime
  omega

/-- **`O((m + r + |E|) √ν)` Word-RAM maximum bipartite matching (`ExecutesList`).** -/
theorem executesList_sparseMatching {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w sparseMatchingProgram (.init inst.encode) inst.matchingWords steps ∧
      steps ≤ sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard := by
  obtain ⟨z, ⟨t, ht, hex⟩, _, hout, hfit, _⟩ := exec_sparseCode inst hw
  refine ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout]), ?_⟩
  unfold sparseTime at ht ⊢
  omega

/-- Instance-only `O((m + r + |E|) √(min m r))` corollary of `executesList_sparseMatching`. -/
theorem executesList_sparseMatching_sqrt_min {w : ℕ} (inst : SparseInstance)
    (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w sparseMatchingProgram (.init inst.encode) inst.matchingWords steps ∧
      steps ≤ sparseTimeSqrtMin inst.m inst.r inst.numEdges := by
  obtain ⟨steps, hex, hle⟩ := executesList_sparseMatching inst hw
  exact ⟨steps, hex, hle.trans (sparseTime_le_sparseTimeSqrtMin inst)⟩

/-- **`Program.ComputesListInTime` form of `executesList_sparseMatching`.** -/
theorem computesListInTime_sparseMatching :
    sparseMatchingProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) SparseInstance.matchingWords :=
  fun inst _ hw _ => executesList_sparseMatching inst hw

/-- **`O((m + r + |E|) √ν)` Word-RAM maximum matching cardinality (`Executes`).** -/
theorem executes_sparseCard {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w sparseCardProgram (.init inst.encode) inst.maxMatchingCard steps ∧
      steps ≤ sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard := by
  obtain ⟨z, ⟨t, ht, hex⟩, _, _, _, hacc⟩ := exec_sparseCode inst hw
  refine ⟨t + 1, hacc ▸ hex.executes acc, ?_⟩
  unfold sparseTime at ht ⊢
  omega

/-- **`Program.ComputesInTime` form of `executes_sparseCard`.** -/
theorem computesInTime_sparseCard :
    sparseCardProgram.ComputesInTime (fun _ inst => inst.encode)
      (fun inst _ => sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) SparseInstance.maxMatchingCard :=
  fun inst _ hw _ => executes_sparseCard inst hw

/-- **`O((m + r + |E|) √ν)` Word-RAM perfect-matching decision (`Executes`).** -/
theorem executes_sparsePerfect {w : ℕ} (inst : SparseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w sparsePerfectProgram (.init inst.encode)
        (if inst.m = inst.r ∧ inst.maxMatchingCard = inst.m then 1 else 0) steps ∧
      steps ≤ sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard := by
  obtain ⟨z, he_sp, hbz, _, _, hacc_z⟩ := exec_sparseCode inst hw
  have htail : ∃ z', ExecWithin w checkPerfectTail z z' 5 ∧
      z'.regs acc = if inst.m = inst.r ∧ inst.maxMatchingCard = inst.m then 1 else 0 := by
    refine WP.exists_execWithin ?_
    unfold checkPerfectTail
    by_cases hmr : inst.m = inst.r
    · by_cases hcm : inst.maxMatchingCard = inst.m
      · wram_exec [hbz.hrm, hbz.hrr, hbz.hone, hacc_z, hmr, hcm]
        wram_simp; simp [hmr, hcm]
      · wram_exec [hbz.hrm, hbz.hrr, hbz.hzero, hacc_z, hmr, hcm]
        wram_simp; simp [hcm]
    · wram_exec [hbz.hrm, hbz.hrr, hbz.hzero, hmr]
      wram_simp; simp [hmr]
  obtain ⟨z', he_t, hacc'⟩ := htail
  obtain ⟨t, ht, hex⟩ := he_sp.seq he_t
  refine ⟨t + 1, hacc' ▸ hex.executes acc, ?_⟩
  unfold sparseTime at ht ⊢
  omega

/-- **`Program.DecidesInTime` form of `executes_sparsePerfect`.** -/
theorem decidesInTime_sparsePerfect :
    sparsePerfectProgram.DecidesInTime (fun _ (inst : SparseInstance) => inst.encode)
      {inst | inst.HasPerfectMatching}
      (fun inst _ => sparseTime inst.m inst.r inst.numEdges inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) := by
  intro inst w hw _
  obtain ⟨steps, hex, hle⟩ := executes_sparsePerfect inst hw
  refine ⟨_, steps, hex, hle, by split_ifs <;> omega, ?_⟩
  change _ ↔ inst.HasPerfectMatching
  rw [inst.hasPerfectMatching_iff]
  split_ifs with h <;> simp [h]

/-! ### 4B. Dense matrix-to-CSR conversion and dense endpoints -/

private def buildCSRColBody : Code .standard 34 := ram[
  val ← *qTail;
  qTail ← qTail + one;
  if val = one then [
    addr ← bEdgesReg + rE; *addr ← idx;
    rE ← rE + one
  ] else [ tmp ← zero ];
  idx ← idx + one ]

private def buildCSRRowBody : Code .standard 34 :=
  .seq (ram[ addr ← bOffReg + qHead; *addr ← rE; idx ← #0 ])
    (.seq (.loop (.lt idx rr) buildCSRColBody)
      (ram[ qHead ← qHead + one ]))

/-- Convert a row-major `m × r` `0/1` adjacency matrix stored starting at `matBase` into exact
CSR arrays starting at `bOffReg`, then initialize all `BaseRegs` workspace pointers. -/
def buildCSRCode (matBase : ℕ) : Code .standard 34 :=
  .seq (ram[ bEdgesReg ← bOffReg + rm; bEdgesReg ← bEdgesReg + one;
             rE ← #0; qHead ← #0; qTail ← #matBase ])
    (.seq (.loop (.lt qHead rm) buildCSRRowBody)
      (.seq (ram[ addr ← bOffReg + rm; *addr ← rE ])
        initBaseRegsFromCSR))

/-- Exact `O(m + m r)` matrix-to-CSR conversion and `BaseRegs` setup (`buildCSRCode`). -/
theorem exec_buildCSRCode {w m r matBase bOff : ℕ} (G : Fin m × Fin r → Bool) (x : Data 34)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1) (h2 : x.regs two = 2)
    (hrm : x.regs rm = m) (hrr : x.regs rr = r) (hbOff : x.regs bOffReg = bOff)
    (hmat_le : matBase + m * r ≤ bOff)
    (hmat : ∀ (u : Fin m) (v : Fin r),
      x.mem (matBase + (u.val * r + v.val)) = if G (u, v) then 1 else 0)
    (hfit : Fits w (bOff + 7 * m + 5 * r + m * r + 8)) :
    let sInst : SparseInstance := ⟨m, r, exactBipAdj G⟩
    ∃ z, ExecWithin w (buildCSRCode matBase) x z (9 * m * r + 8 * m + 25) ∧
      BaseRegs sInst bOff z ∧
      CSRMem sInst bOff z.mem := by
  let sInst : SparseInstance := ⟨m, r, exactBipAdj G⟩
  have hE_le : sInst.numEdges ≤ m * r := bipAdjSteps_exactBipAdj_le G
  have hf_bm : Fits w (bOff + m) := hfit.of_le (by omega)
  have hf_bm1 : Fits w (bOff + m + 1) := hfit.of_le (by omega)
  have hf_mb : Fits w matBase := hfit.of_le (by omega)
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ bEdgesReg ← bOffReg + rm; bEdgesReg ← bEdgesReg + one;
            rE ← #0; qHead ← #0; qTail ← #matBase ] : Code .standard 34) x s₀ 5 ∧
      s₀ = ((((x.set bEdgesReg (bOff + m)).set bEdgesReg (bOff + m + 1)).set rE 0).set
        qHead 0).set qTail matBase := by
    refine WP.exists_execWithin ?_
    wram_exec [hbOff, hrm, h1, hf_bm, hf_bm1, hf_mb]
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let s₀ := ((((x.set bEdgesReg (bOff + m)).set bEdgesReg (bOff + m + 1)).set rE 0).set
    qHead 0).set qTail matBase
  let PR (uIdx : ℕ) (y : Data 34) : Prop :=
    uIdx ≤ m ∧
      (∀ i : Fin 34, i.val < 22 → i ≠ rE → y.regs i = s₀.regs i) ∧
      y.regs qTail = matBase + uIdx * r ∧
      y.regs rE = sInst.offset uIdx ∧
      (∀ u' : ℕ, u' < uIdx → y.mem (bOff + u') = sInst.offset u') ∧
      (∀ (u' : Fin m), u'.val < uIdx → ∀ {i : ℕ} (hi : i < (sInst.adj u').length),
        y.mem (bOff + m + 1 + (sInst.offset u'.val + i)) = ((sInst.adj u')[i]'hi).val) ∧
      (∀ a, a < bOff → y.mem a = x.mem a)
  have hPR₀ : PR 0 s₀ :=
    ⟨Nat.zero_le _, fun _ _ _ => rfl, by dsimp only [s₀]; wram_simp; omega,
      by dsimp only [s₀]; wram_simp [sInst.offset_zero],
      fun _ hu => absurd hu (Nat.not_lt_zero _),
      fun _ hu => absurd hu (Nat.not_lt_zero _),
      fun _ _ => rfl⟩
  have hrowBody (y : Data 34) (hy : PR (y.regs qHead) y) (hu_lt : y.regs qHead < m) :
      ∃ z, ExecWithin w buildCSRRowBody y z (9 * r + 6) ∧ PR (y.regs qHead + 1) z ∧
        z.regs qHead = y.regs qHead + 1 := by
    obtain ⟨_, hr_y, hqt_y, hrE_y, hoff_y, hedge_y, hlow_y⟩ := hy
    let u : Fin m := ⟨y.regs qHead, hu_lt⟩
    have hoff_succ : sInst.offset (u.val + 1) = sInst.offset u.val + (sInst.adj u).length :=
      sInst.offset_succ hu_lt
    have hoff_u1_le : sInst.offset (u.val + 1) ≤ m * r :=
      (sInst.offset_le_numEdges (u.val + 1)).trans hE_le
    have hy_bOff : y.regs bOffReg = bOff := by
      rw [hr_y bOffReg (by decide) (by decide)]; dsimp only [s₀]; wram_simp [hbOff]
    have hy_bEdges : y.regs bEdgesReg = bOff + m + 1 := by
      rw [hr_y bEdgesReg (by decide) (by decide)]; dsimp only [s₀]; wram_simp
    have hy_zero : y.regs zero = 0 := by
      rw [hr_y zero (by decide) (by decide)]; dsimp only [s₀]; wram_simp [h0]
    have hy_one : y.regs one = 1 := by
      rw [hr_y one (by decide) (by decide)]; dsimp only [s₀]; wram_simp [h1]
    have hy_rr : y.regs rr = r := by
      rw [hr_y rr (by decide) (by decide)]; dsimp only [s₀]; wram_simp [hrr]
    have hf_off_u : Fits w (bOff + y.regs qHead) := hfit.of_le (by omega)
    have hpre_row : ∃ y₁, ExecWithin w
        (ram[ addr ← bOffReg + qHead; *addr ← rE; idx ← #0 ] : Code .standard 34) y y₁ 3 ∧
        y₁ = ((y.set addr (bOff + y.regs qHead)).write
          (bOff + y.regs qHead) (sInst.offset u.val)).set idx 0 := by
      refine WP.exists_execWithin ?_
      wram_exec [hy_bOff, hrE_y, hf_off_u]
      rfl
    obtain ⟨y₁, he_pre_row, rfl⟩ := hpre_row
    let y₁ := ((y.set addr (bOff + y.regs qHead)).write
      (bOff + y.regs qHead) (sInst.offset u.val)).set idx 0
    let rowPre (t : ℕ) : List (Fin r) := ((List.finRange r).take t).filter fun v => G (u, v)
    have hrowPre_sub : ∀ t : ℕ, (rowPre t).length ≤ (sInst.adj u).length := fun t => by
      have hsub : (rowPre t).Sublist (sInst.adj u) :=
        List.Sublist.filter _ (List.take_sublist t (List.finRange r))
      exact hsub.length_le
    let PC (t : ℕ) (w_st : Data 34) : Prop :=
      t ≤ r ∧
        (∀ i : Fin 34, i.val < 28 → i ≠ rE → i ≠ qTail → w_st.regs i = y₁.regs i) ∧
        w_st.regs qTail = matBase + u.val * r + t ∧
        w_st.regs rE = sInst.offset u.val + (rowPre t).length ∧
        (∀ i : ℕ, (hi : i < (rowPre t).length) →
          w_st.mem (bOff + m + 1 + (sInst.offset u.val + i)) = ((rowPre t)[i]'hi).val) ∧
        (∀ a, ¬(bOff + m + 1 + sInst.offset u.val ≤ a ∧
            a < bOff + m + 1 + sInst.offset (u.val + 1)) → w_st.mem a = y₁.mem a)
    have hPC₀ : PC 0 y₁ :=
      ⟨Nat.zero_le _, fun _ _ _ _ => rfl,
        by dsimp only [y₁]; wram_simp [hqt_y]; rfl,
        by dsimp only [y₁, u]; wram_simp [hrE_y]; simp [rowPre],
        fun _ hi => absurd hi (by simp [rowPre]),
        fun _ _ => rfl⟩
    have hcolBody (w_st : Data 34) (hw_st : PC (w_st.regs idx) w_st)
        (hv_lt : w_st.regs idx < r) :
        ∃ w', ExecWithin w buildCSRColBody w_st w' 7 ∧ PC (w_st.regs idx + 1) w' ∧
          w'.regs idx = w_st.regs idx + 1 := by
      obtain ⟨_, hr_c, hqt_c, hrE_c, hed_c, hf_c⟩ := hw_st
      let v : Fin r := ⟨w_st.regs idx, hv_lt⟩
      have hmul_lt : u.val * r + w_st.regs idx < m * r := by
        calc u.val * r + w_st.regs idx < u.val * r + r := by omega
          _ = (u.val + 1) * r := by ring
          _ ≤ m * r := Nat.mul_le_mul_right r (by dsimp only [u]; omega)
      have hmat_addr_lt : matBase + u.val * r + w_st.regs idx < bOff := by omega
      have hmat_uv : w_st.mem (matBase + u.val * r + w_st.regs idx) =
          if G (u, v) then 1 else 0 := by
        rw [hf_c _ (by omega)]
        dsimp only [y₁, u]
        wram_simp
        rw [hlow_y _ hmat_addr_lt]
        simpa [Nat.add_assoc, u] using hmat u v
      have hw_one : w_st.regs one = 1 := by
        rw [hr_c one (by decide) (by decide) (by decide)]; dsimp only [y₁]; wram_simp [hy_one]
      have hw_zero : w_st.regs zero = 0 := by
        rw [hr_c zero (by decide) (by decide) (by decide)]; dsimp only [y₁]; wram_simp [hy_zero]
      have hw_bEdges : w_st.regs bEdgesReg = bOff + m + 1 := by
        rw [hr_c bEdgesReg (by decide) (by decide) (by decide)]
        dsimp only [y₁]; wram_simp [hy_bEdges]
      have hf_qt1 : Fits w (matBase + u.val * r + w_st.regs idx + 1) := hfit.of_le (by omega)
      have hf_idx1 : Fits w (w_st.regs idx + 1) := hfit.of_le (by omega)
      have hpre_succ : rowPre (w_st.regs idx + 1) =
          if G (u, v) then rowPre (w_st.regs idx) ++ [v] else rowPre (w_st.regs idx) := by
        dsimp only [rowPre]
        rw [List.take_succ_finRange hv_lt, List.filter_append]
        cases h : G (u, v) <;> simp [v, h]
      refine WP.exists_execWithin ?_
      unfold buildCSRColBody
      cases hG : G (u, v)
      · rw [hG] at hmat_uv hpre_succ
        simp only [Bool.false_eq_true, ↓reduceIte] at hmat_uv hpre_succ
        wram_exec [hqt_c, hw_one, hw_zero, hmat_uv, hf_qt1, hf_idx1]
        refine ⟨⟨by omega, fun i hi hne1 hne2 => by wram_simp [hr_c i hi hne1 hne2],
          by wram_simp; omega, by wram_simp [hrE_c, hpre_succ],
          by rw [hpre_succ]; exact hed_c, fun a ha => ?_⟩, by wram_simp⟩
        wram_simp
        exact hf_c a ha
      · rw [hG] at hmat_uv hpre_succ
        simp only [↓reduceIte] at hmat_uv hpre_succ
        have hlen_lt_adj : (rowPre (w_st.regs idx)).length < (sInst.adj u).length := by
          have hle1 := hrowPre_sub (w_st.regs idx + 1)
          rw [hpre_succ, List.length_append, List.length_singleton] at hle1
          omega
        have hf_ed_w : Fits w ((bOff + m + 1) +
            (sInst.offset u.val + (rowPre (w_st.regs idx)).length)) := hfit.of_le (by omega)
        have hf_rE1 : Fits w (sInst.offset u.val + (rowPre (w_st.regs idx)).length + 1) :=
          hfit.of_le (by omega)
        wram_exec [hqt_c, hw_one, hw_bEdges, hrE_c, hmat_uv, hf_qt1, hf_ed_w, hf_rE1, hf_idx1]
        refine ⟨⟨by omega, fun i hi hne1 hne2 => by wram_simp [hr_c i hi hne1 hne2],
          by wram_simp; omega,
          by wram_simp; rw [hpre_succ, List.length_append, List.length_singleton]; omega,
          fun i hi => ?_, fun a ha => ?_⟩, by wram_simp⟩
        · simp only [hpre_succ] at hi ⊢
          rw [List.length_append, List.length_singleton] at hi
          by_cases hi_lt : i < (rowPre (w_st.regs idx)).length
          · rw [List.getElem_append_left hi_lt]
            wram_simp
            exact hed_c i hi_lt
          · have hi_eq : i = (rowPre (w_st.regs idx)).length := by omega
            subst hi_eq
            rw [List.getElem_append_right (le_refl _)]
            wram_simp
            simp [v]
        · wram_simp
          exact hf_c a ha
    have hy₁_idx : y₁.regs idx = 0 := by dsimp only [y₁]; wram_simp
    obtain ⟨y₂, hl_col, hPCr, _⟩ := ExecWithin.loop_count PC
      (fun w_st hw_st => by
        rw [hw_st.2.1 rr (by decide) (by decide) (by decide)]
        dsimp only [y₁]; wram_simp [hy_rr])
      hcolBody (x := y₁) (by rw [hy₁_idx]; exact Nat.zero_le r) (by rw [hy₁_idx]; exact hPC₀)
    rw [hy₁_idx, Nat.sub_zero] at hl_col
    obtain ⟨_, hr_c2, hqt_c2, hrE_c2, hed_c2, hf_c2⟩ := hPCr
    have hrowPre_full : rowPre r = sInst.adj u := by
      dsimp only [rowPre, sInst, exactBipAdj]
      rw [List.take_of_length_le (by simp)]
    have hy₂_qh : y₂.regs qHead = y.regs qHead := by
      rw [hr_c2 qHead (by decide) (by decide) (by decide)]; dsimp only [y₁]; wram_simp
    have hy₂_one : y₂.regs one = 1 := by
      rw [hr_c2 one (by decide) (by decide) (by decide)]; dsimp only [y₁]; wram_simp [hy_one]
    have hf_qh1 : Fits w (y.regs qHead + 1) := hfit.of_le (by omega)
    have hpost_row : ∃ z, ExecWithin w (ram[ qHead ← qHead + one ] : Code .standard 34) y₂ z 1 ∧
        z = y₂.set qHead (y.regs qHead + 1) := by
      refine WP.exists_execWithin ?_
      wram_exec [hy₂_qh, hy₂_one, hf_qh1]
      rfl
    obtain ⟨z, he_post_row, rfl⟩ := hpost_row
    refine ⟨_, (he_pre_row.seq (hl_col.seq he_post_row)).mono (by omega),
      ⟨by omega, fun i hi hne => ?_, ?_, ?_, fun u' hu' => ?_, fun u' hu' {i} hi => ?_,
        fun a ha => ?_⟩, by wram_simp⟩
    · wram_simp
      rw [hr_c2 i (by omega) hne (by intro h; subst h; simp at hi)]
      dsimp only [y₁]; wram_simp [hr_y i hi hne]
    · wram_simp [hqt_c2]
      change matBase + u.val * r + r = matBase + (u.val + 1) * r
      ring
    · wram_simp [hrE_c2]
      rw [hrowPre_full, ← hoff_succ]
    · dsimp only [Data.set]
      rw [hf_c2 _ (by omega)]
      dsimp only [y₁, u]
      by_cases heq_u : u' = y.regs qHead
      · subst heq_u; wram_simp
      · wram_simp; exact hoff_y u' (by omega)
    · dsimp only [Data.set]
      by_cases heq_u : u' = u
      · subst heq_u
        have hi' : i < (rowPre r).length := by rwa [hrowPre_full]
        simpa [hrowPre_full] using hed_c2 i hi'
      · have hne_val : u'.val ≠ y.regs qHead := fun h => heq_u (Fin.ext h)
        have hu'_lt : u'.val < u.val := by dsimp only [u]; omega
        have hle_end : sInst.offset (u'.val + 1) ≤ sInst.offset u.val :=
          sInst.offset_mono (by omega)
        have hoff_u'_succ : sInst.offset (u'.val + 1) =
            sInst.offset u'.val + (sInst.adj u').length := sInst.offset_succ u'.isLt
        rw [hf_c2 _ (by omega)]
        dsimp only [y₁]
        wram_simp
        exact hedge_y u' hu'_lt hi
    · dsimp only [Data.set]
      rw [hf_c2 a (by omega)]
      dsimp only [y₁]
      wram_simp [hlow_y a ha]
  have hs₀_qh : s₀.regs qHead = 0 := by dsimp only [s₀]; wram_simp
  obtain ⟨y_end, hl_row, hPRm, _⟩ := ExecWithin.loop_count PR
    (fun y hy => by
      rw [hy.2.1 rm (by decide) (by decide)]
      dsimp only [s₀]; wram_simp [hrm])
    hrowBody (x := s₀) (by rw [hs₀_qh]; exact Nat.zero_le m) (by rw [hs₀_qh]; exact hPR₀)
  rw [hs₀_qh, Nat.sub_zero] at hl_row
  obtain ⟨_, hr_m, _, hrE_m, hoff_m, hedge_m, _⟩ := hPRm
  have hend_bOff : y_end.regs bOffReg = bOff := by
    rw [hr_m bOffReg (by decide) (by decide)]; dsimp only [s₀]; wram_simp [hbOff]
  have hend_rm : y_end.regs rm = m := by
    rw [hr_m rm (by decide) (by decide)]; dsimp only [s₀]; wram_simp [hrm]
  have hs_last : ∃ y_last, ExecWithin w
      (ram[ addr ← bOffReg + rm; *addr ← rE ] : Code .standard 34) y_end y_last 2 ∧
      y_last = (y_end.set addr (bOff + m)).write (bOff + m) (sInst.offset m) := by
    refine WP.exists_execWithin ?_
    wram_exec [hend_bOff, hend_rm, hrE_m, hf_bm]
    rfl
  obtain ⟨y_last, he_last, rfl⟩ := hs_last
  let y_last := (y_end.set addr (bOff + m)).write (bOff + m) (sInst.offset m)
  have hlast_0 : y_last.regs zero = 0 := by
    dsimp only [y_last]; wram_simp
    rw [hr_m zero (by decide) (by decide)]; dsimp only [s₀]; wram_simp [h0]
  have hlast_1 : y_last.regs one = 1 := by
    dsimp only [y_last]; wram_simp
    rw [hr_m one (by decide) (by decide)]; dsimp only [s₀]; wram_simp [h1]
  have hlast_2 : y_last.regs two = 2 := by
    dsimp only [y_last]; wram_simp
    rw [hr_m two (by decide) (by decide)]; dsimp only [s₀]; wram_simp [h2]
  have hlast_rm : y_last.regs rm = sInst.m := by
    dsimp only [y_last, sInst]; wram_simp [hend_rm]
  have hlast_rr : y_last.regs rr = sInst.r := by
    dsimp only [y_last, sInst]; wram_simp
    rw [hr_m rr (by decide) (by decide)]; dsimp only [s₀]; wram_simp [hrr]
  have hlast_rE : y_last.regs rE = sInst.numEdges := by
    dsimp only [y_last]; wram_simp [hrE_m]; exact sInst.offset_m
  have hlast_bOff : y_last.regs bOffReg = bOff := by
    dsimp only [y_last]; wram_simp [hend_bOff]
  have hfit_init : Fits w (bOff + 7 * sInst.m + 5 * sInst.r + sInst.numEdges + 8) := by
    change Fits w (bOff + 7 * m + 5 * r + sInst.numEdges + 8)
    exact hfit.of_le (by omega)
  obtain ⟨z, he_init, hbz, hmem_z⟩ := exec_initBaseRegsFromCSR sInst y_last
    hlast_0 hlast_1 hlast_2 hlast_rm hlast_rr hlast_rE hlast_bOff hfit_init
  have hcsrz : CSRMem sInst bOff z.mem :=
    { hoff := fun {u'} hu' => by
        rw [hmem_z]
        dsimp only [y_last]
        by_cases heq : u' = m
        · subst heq; wram_simp
        · wram_simp; exact hoff_m u' (by dsimp only [sInst] at hu'; omega)
      hedge := fun u' {i} hi => by
        have hed_u' := sInst.offset_add_lt_numEdges u' hi
        rw [hmem_z]
        dsimp only [y_last]
        wram_simp
        exact hedge_m u' u'.isLt hi }
  refine ⟨z, (he₀.seq (hl_row.seq (he_last.seq he_init))).mono ?_, hbz, hcsrz⟩
  nlinarith

/-- Read header dimensions (`m`, and `r` if `isSquare = false` else `r = m`) from input memory,
compute `bOffReg := matBase + m * r` (with `matBase = 2` if `isSquare` else `3`), and convert
the row-major `m × r` `0/1` adjacency matrix starting at `matBase` into exact CSR arrays. -/
def matrixSetupCode (isSquare : Bool) : Code .standard 34 :=
  .seq (ram[ zero ← #0; one ← #1; two ← #2; addr ← #1; rm ← *addr ])
    (.seq (if isSquare then ram[ rr ← rm; val ← rm * rr; bOffReg ← two + val ]
           else ram[ addr ← #2; rr ← *addr; val ← rm * rr;
                     bOffReg ← #3; bOffReg ← bOffReg + val ])
      (buildCSRCode (if isSquare then 2 else 3)))

/-- Shared header-read and matrix-to-CSR conversion for dense (`isSquare = false`, header `[m, r]`)
and square poset (`isSquare = true`, header `[n]`) encodings. -/
theorem exec_matrixSetupCode {w m r : ℕ} (isSquare : Bool) (hsq : isSquare = true → m = r)
    (G : Fin m × Fin r → Bool) (input : List ℕ)
    (hm : (Data.init input : Data 34).mem 1 = m)
    (hr : isSquare = false → (Data.init input : Data 34).mem 2 = r)
    (hmat : ∀ (u : Fin m) (v : Fin r),
      (Data.init input : Data 34).mem ((if isSquare then 2 else 3) + (u.val * r + v.val)) =
        if G (u, v) then 1 else 0)
    (hfit : Fits w ((if isSquare then 2 else 3) + m * r + 7 * m + 5 * r + m * r + 8)) :
    ∃ y, ExecWithin w (matrixSetupCode isSquare) (Data.init input) y
        (9 * m * r + 8 * m + (if isSquare then 33 else 35)) ∧
      BaseRegs ⟨m, r, exactBipAdj G⟩ ((if isSquare then 2 else 3) + m * r) y ∧
      CSRMem ⟨m, r, exactBipAdj G⟩ ((if isSquare then 2 else 3) + m * r) y.mem := by
  have hf0 : Fits w 0 := hfit.of_le (by cases isSquare <;> omega)
  have hf1 : Fits w 1 := hfit.of_le (by cases isSquare <;> omega)
  have hf2 : Fits w 2 := hfit.of_le (by cases isSquare <;> omega)
  have hf3 : Fits w 3 := hfit.of_le (by cases isSquare <;> omega)
  have hfmr : Fits w (m * r) := hfit.of_le (by cases isSquare <;> omega)
  have hs_pre : ∃ y₀, ExecWithin w
      (ram[ zero ← #0; one ← #1; two ← #2; addr ← #1; rm ← *addr ] : Code .standard 34)
      (Data.init input) y₀ 5 ∧
      y₀.regs zero = 0 ∧ y₀.regs one = 1 ∧ y₀.regs two = 2 ∧
      y₀.regs rm = m ∧ y₀.mem = (Data.init input : Data 34).mem := by
    refine WP.exists_execWithin ?_
    wram_exec [hm, hf0, hf1, hf2]
    exact ⟨by wram_simp, by wram_simp, by wram_simp, by wram_simp, rfl⟩
  obtain ⟨y₀, he_pre, h0, h1, h2, hrm, hmem₀⟩ := hs_pre
  cases isSquare with
  | true =>
    obtain rfl := hsq rfl
    have hf2mm : Fits w (2 + m * m) := hfit.of_le (by omega)
    have hs_dim : ∃ y₁, ExecWithin w
        (ram[ rr ← rm; val ← rm * rr; bOffReg ← two + val ] : Code .standard 34) y₀ y₁ 3 ∧
        y₁.regs zero = 0 ∧ y₁.regs one = 1 ∧ y₁.regs two = 2 ∧
        y₁.regs rm = m ∧ y₁.regs rr = m ∧ y₁.regs bOffReg = 2 + m * m ∧
        y₁.mem = (Data.init input : Data 34).mem := by
      refine WP.exists_execWithin ?_
      wram_exec [h2, hrm, hfmr, hf2mm]
      exact ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2],
        by wram_simp [hrm], by wram_simp, by wram_simp, hmem₀⟩
    obtain ⟨y₁, he_dim, h0', h1', h2', hrm', hrr', hbOff', hmem₁⟩ := hs_dim
    obtain ⟨z, he_csr, hbz, hcsrz⟩ := exec_buildCSRCode (m := m) (r := m) (matBase := 2)
      (bOff := 2 + m * m) G y₁ h0' h1' h2' hrm' hrr' hbOff' (le_refl _)
      (fun u v => by rw [hmem₁]; exact hmat u v) hfit
    exact ⟨z, (he_pre.seq (he_dim.seq he_csr)).mono (by simp; omega), hbz, hcsrz⟩
  | false =>
    have hr_mem : y₀.mem 2 = r := by rw [hmem₀]; exact hr rfl
    have hf3mr : Fits w (3 + m * r) := hfit.of_le (by omega)
    have hs_dim : ∃ y₁, ExecWithin w
        (ram[ addr ← #2; rr ← *addr; val ← rm * rr;
              bOffReg ← #3; bOffReg ← bOffReg + val ] : Code .standard 34) y₀ y₁ 5 ∧
        y₁.regs zero = 0 ∧ y₁.regs one = 1 ∧ y₁.regs two = 2 ∧
        y₁.regs rm = m ∧ y₁.regs rr = r ∧ y₁.regs bOffReg = 3 + m * r ∧
        y₁.mem = (Data.init input : Data 34).mem := by
      refine WP.exists_execWithin ?_
      wram_exec [hrm, hr_mem, hf2, hf3, hfmr, hf3mr]
      exact ⟨by wram_simp [h0], by wram_simp [h1], by wram_simp [h2],
        by wram_simp [hrm], by wram_simp, by wram_simp, hmem₀⟩
    obtain ⟨y₁, he_dim, h0', h1', h2', hrm', hrr', hbOff', hmem₁⟩ := hs_dim
    obtain ⟨z, he_csr, hbz, hcsrz⟩ := exec_buildCSRCode (m := m) (r := r) (matBase := 3)
      (bOff := 3 + m * r) G y₁ h0' h1' h2' hrm' hrr' hbOff' (le_refl _)
      (fun u v => by rw [hmem₁]; exact hmat u v) hfit
    exact ⟨z, (he_pre.seq (he_dim.seq he_csr)).mono (by simp; omega), hbz, hcsrz⟩

private def denseCode : Code .standard 34 :=
  .seq (matrixSetupCode false) (.seq coreCode emitMatchingCode)

/-- Standard-basis word-RAM program returning `inst.matchingWords` (`ExecutesList`) on a dense
`m × r` `0/1` adjacency matrix `inst : DenseInstance`. -/
def denseMatchingProgram : Program .standard 34 :=
  denseCode.program outBase

/-- Standard-basis word-RAM program returning `inst.maxMatchingCard` (`Executes`) on
`inst : DenseInstance`. -/
def denseCardProgram : Program .standard 34 :=
  denseCode.program acc

/-- Instruction bound `O((m + r)² √ν)` for `denseMatchingProgram` and `denseCardProgram`. -/
@[expose] def denseTime (m r ν : ℕ) : ℕ :=
  (2 * Nat.sqrt ν + 1) * (112 * m * r + 100 * m + 47 * r + 48) +
    9 * m * r + 8 * m + 18 * r + 50

private theorem exec_denseCode {w : ℕ} (inst : DenseInstance) (hw : Fits w inst.wordBound) :
    ∃ z, ExecWithin w denseCode (Data.init inst.encode) z
        (denseTime inst.m inst.r inst.maxMatchingCard - 1) ∧
      outputList z.mem (z.regs outBase) = inst.matchingWords ∧
      Fits w (z.regs outBase + inst.matchingWords.length) ∧
      z.regs acc = inst.maxMatchingCard := by
  have hfit_all : Fits w ((3 + inst.m * inst.r) + 7 * inst.m + 6 * inst.r +
      inst.m * inst.r + 8) := hw.of_le (by unfold DenseInstance.wordBound; nlinarith)
  obtain ⟨y₁, he_setup, hb₁, hcsr₁⟩ :=
    exec_matrixSetupCode (m := inst.m) (r := inst.r) false (fun h => by cases h)
      inst.graph inst.encode inst.init_mem_m (fun _ => inst.init_mem_r)
      (fun u v => inst.init_mem_entry u v) (hfit_all.of_le (by simp; omega))
  have hE_le : inst.toSparse.numEdges ≤ inst.m * inst.r := inst.numEdges_toSparse_le
  have hfit_core : Fits w ((3 + inst.m * inst.r) + 7 * inst.toSparse.m + 5 * inst.toSparse.r +
      inst.toSparse.numEdges + 8) := by
    change Fits w ((3 + inst.m * inst.r) + 7 * inst.m + 5 * inst.r +
      inst.toSparse.numEdges + 8)
    exact hfit_all.of_le (by omega)
  have hfit_emit : Fits w ((3 + inst.m * inst.r) + 7 * inst.toSparse.m + 6 * inst.toSparse.r +
      inst.toSparse.numEdges + 8) := by
    change Fits w ((3 + inst.m * inst.r) + 7 * inst.m + 6 * inst.r +
      inst.toSparse.numEdges + 8)
    exact hfit_all.of_le (by omega)
  obtain ⟨y₂, he_core, hb₂, _, hmate₂, _, _⟩ := core_exec inst.toSparse y₁ hb₁ hcsr₁ hfit_core
  obtain ⟨z, he_emit, _, hout_z, hfit_out, hacc_z⟩ :=
    exec_emitMatchingCode inst.toSparse y₂ hb₂ hmate₂ hfit_emit
  rw [← inst.maxMatchingCard_eq_toSparse] at he_core hacc_z
  have hcore_le : coreTime inst.m inst.r inst.toSparse.numEdges inst.maxMatchingCard ≤
      (2 * Nat.sqrt inst.maxMatchingCard + 1) *
        (112 * inst.m * inst.r + 100 * inst.m + 47 * inst.r + 48) + 5 * inst.r + 6 := by
    unfold coreTime
    refine Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) _) _
    nlinarith
  refine ⟨z, (he_setup.seq (he_core.seq he_emit)).mono ?_,
    hout_z, hfit_out, hacc_z⟩
  unfold denseTime
  change (9 * inst.m * inst.r + 8 * inst.m + 35) +
      (coreTime inst.m inst.r inst.toSparse.numEdges inst.maxMatchingCard +
        (13 * inst.r + 7)) ≤ _
  omega

/-- **`O((m + r)² √ν)` Word-RAM dense maximum bipartite matching (`ExecutesList`).** -/
theorem executesList_denseMatching {w : ℕ} (inst : DenseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w denseMatchingProgram (.init inst.encode) inst.matchingWords steps ∧
      steps ≤ denseTime inst.m inst.r inst.maxMatchingCard := by
  obtain ⟨z, ⟨t, ht, hex⟩, hout, hfit, _⟩ := exec_denseCode inst hw
  refine ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout]), ?_⟩
  unfold denseTime at ht ⊢
  omega

/-- **`Program.ComputesListInTime` form of `executesList_denseMatching`.** -/
theorem computesListInTime_denseMatching :
    denseMatchingProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => denseTime inst.m inst.r inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) DenseInstance.matchingWords :=
  fun inst _ hw _ => executesList_denseMatching inst hw

/-- **`O((m + r)² √ν)` Word-RAM dense maximum matching cardinality (`Executes`).** -/
theorem executes_denseCard {w : ℕ} (inst : DenseInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, Executes w denseCardProgram (.init inst.encode) inst.maxMatchingCard steps ∧
      steps ≤ denseTime inst.m inst.r inst.maxMatchingCard := by
  obtain ⟨z, ⟨t, ht, hex⟩, _, _, hacc⟩ := exec_denseCode inst hw
  refine ⟨t + 1, hacc ▸ hex.executes acc, ?_⟩
  unfold denseTime at ht ⊢
  omega

/-- **`Program.ComputesInTime` form of `executes_denseCard`.** -/
theorem computesInTime_denseCard :
    denseCardProgram.ComputesInTime (fun _ inst => inst.encode)
      (fun inst _ => denseTime inst.m inst.r inst.maxMatchingCard)
      (fun inst w => Fits w inst.wordBound) DenseInstance.maxMatchingCard :=
  fun inst _ hw _ => executes_denseCard inst hw

end Cslib.Algorithms.WordRAM.HopcroftKarp
