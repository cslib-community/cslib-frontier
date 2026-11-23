/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.ChainCover
public import CslibFrontier.Computability.WordRAM.ListOutput
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.PreservesMask
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Hopcroft–Karp maximum bipartite matching and Dilworth chain covers on the word RAM

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
   `O(m + m r)` instructions and invokes `coreCode`, agreeing with `hopcroftKarpDense`.
3. **Dilworth minimum chain cover and maximum antichain (`O(n^{5/2})`):** given an `n × n` strict
   poset comparability matrix (`PosetInstance`, specialized to finite partial orders via
   `PosetInstance.ofEnum`), runs dense Hopcroft–Karp on Fulkerson's bipartite graph, merges chain
   labels in `O(n²)` instructions (`chainLabels_eq_foldl_rowMate`), and extracts the König
   uncovered antichain in `O(n)` instructions (`foldl_uncoveredStep`), matching `minChainCover`.

## Main definitions

* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.PosetInstance`: sparse CSR, dense matrix, and poset
  comparability problem instances with their word encodings, word-width envelopes, and outputs.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.coreCode`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseMatchingProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseCardProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparsePerfectProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseMatchingProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseCardProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.chainLabelsProgram`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.maxAntichainProgram`: word-RAM programs.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.coreTime`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseTime`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.sparseTimeSqrtMin`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.denseTime`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.chainCoverTime`: instruction bounds.

## Main results

* `Cslib.Algorithms.WordRAM.HopcroftKarp.core_exec`: in-memory CSR execution of Hopcroft–Karp in
  `O((m + r + |E|) (√ν + 1))` instructions.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.executesList_sparseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.computesListInTime_sparseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.executes_sparseCard`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.decidesInTime_sparsePerfect`: sparse `O((m + r + |E|) √ν)`
  endpoints.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.executesList_denseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.computesListInTime_denseMatching`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.executes_denseCard`: dense `O((m + r)² √ν)` endpoints.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.executesList_chainLabels`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.computesListInTime_chainLabels`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.executesList_maxAntichain`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.computesListInTime_maxAntichain`: `O(n^{5/2})` minimum
  chain cover and maximum antichain endpoints.

## References

* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [D. R. Fulkerson, *Note on Dilworth's decomposition theorem for partially ordered
  sets*][Fulkerson1956]
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
          ((List.finRange inst.m).drop (u.val + 1)).flatMap (fun i => (inst.adj i).map Fin.val)) := by
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

theorem flatEdges_getElem (inst : SparseInstance) (u : Fin inst.m) {i : ℕ}
    (hi : i < (inst.adj u).length) :
    inst.flatEdges[inst.offset u.val + i]'(by
      rw [inst.length_flatEdges]; exact inst.offset_add_lt_numEdges u hi) =
      ((inst.adj u)[i]'hi).val := by
  simp only [inst.flatEdges_eq_append u, ← inst.length_take_flatEdges u.val,
    List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
    List.getElem_append_left (by simp [hi]), List.getElem_map]

theorem init_mem_m {reg : ℕ} (inst : SparseInstance) :
    (Data.init inst.encode : Data reg).mem 1 = inst.m := rfl

theorem init_mem_r {reg : ℕ} (inst : SparseInstance) :
    (Data.init inst.encode : Data reg).mem 2 = inst.r := rfl

theorem init_mem_offset {reg : ℕ} (inst : SparseInstance) {u : ℕ} (hu : u ≤ inst.m) :
    (Data.init inst.encode : Data reg).mem (3 + u) = inst.offset u := by
  have hreal := Data.init_realizes_append (r := reg) [inst.m, inst.r]
    ((List.range (inst.m + 1)).map inst.offset) inst.flatEdges
  have henc : [inst.m, inst.r] ++ (((List.range (inst.m + 1)).map inst.offset) ++ inst.flatEdges) =
      inst.encode := by simp [encode]
  rw [henc] at hreal
  have h := hreal ⟨u, by simp; omega⟩
  simpa [Block.read] using h

theorem init_mem_edge {reg : ℕ} (inst : SparseInstance) (u : Fin inst.m) {i : ℕ}
    (hi : i < (inst.adj u).length) :
    (Data.init inst.encode : Data reg).mem (inst.m + 4 + (inst.offset u.val + i)) =
      ((inst.adj u)[i]'hi).val := by
  let pre := [inst.m, inst.r] ++ (List.range (inst.m + 1)).map inst.offset
  have hreal := Data.init_realizes_append (r := reg) pre inst.flatEdges []
  have henc : pre ++ (inst.flatEdges ++ []) = inst.encode := by simp [pre, encode]
  rw [henc] at hreal
  have hpre : pre.length + 1 = inst.m + 4 := by simp [pre]; omega
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
      have hu₁ : (u₁, v) ∈ mateMatching mate := of_decide_eq_true (List.find?_some hf)
      have hu₀ : (u₀, v) ∈ mateMatching mate := mem_mateMatching.mpr hm
      exact congrArg some (hM.2.2 u₁ u₀ v hu₁ hu₀)

theorem matchingPairs_eq_mate_filterMap (inst : SparseInstance) :
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
  ext ⟨u, v⟩
  simp only [List.mem_toFinset, List.mem_filterMap, List.mem_finRange, true_and, mem_mateMatching]
  constructor
  · rintro ⟨v', hm⟩
    cases h : vget _ v' with
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
  refine List.Nodup.filterMap ?_ (List.nodup_finRange inst.r)
  intro v₁ v₂ e h₁ h₂
  cases hm₁ : vget _ v₁ <;> simp [hm₁] at h₁
  cases hm₂ : vget _ v₂ <;> simp [hm₂] at h₂
  subst h₁
  exact (Prod.mk.inj h₂).2

theorem length_matchingPairs (inst : SparseInstance) :
    inst.matchingPairs.length = inst.maxMatchingCard := by
  rw [← List.toFinset_card_of_nodup inst.nodup_matchingPairs, inst.toFinset_matchingPairs]
  rfl

theorem length_matchingWords (inst : SparseInstance) :
    inst.matchingWords.length = 2 * inst.maxMatchingCard := by
  simp [matchingWords, List.length_flatMap, inst.length_matchingPairs]

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

/-- Flat output word list `[u₀, v₀, u₁, v₁, …]` of a maximum matching of `inst.graph`. -/
@[expose] def matchingWords (inst : DenseInstance) : List ℕ :=
  inst.toSparse.matchingWords

/-- Sufficient word-value envelope for dense Hopcroft–Karp on `inst`. -/
@[expose] def wordBound (inst : DenseInstance) : ℕ :=
  2 * inst.m * inst.r + 8 * inst.m + 6 * inst.r + 14

@[simp] theorem toSparse_graph (inst : DenseInstance) : inst.toSparse.graph = inst.graph := by
  ext ⟨u, v⟩
  simp [toSparse, SparseInstance.graph, exactBipAdj]

theorem maxMatchingCard_eq_toSparse (inst : DenseInstance) :
    inst.maxMatchingCard = inst.toSparse.maxMatchingCard := by
  simp [maxMatchingCard, SparseInstance.maxMatchingCard, toSparse, ← hopcroftKarp_exactBipAdj]

theorem numEdges_toSparse_le (inst : DenseInstance) :
    inst.toSparse.numEdges ≤ inst.m * inst.r :=
  bipAdjSteps_exactBipAdj_le inst.graph

theorem encode_length (inst : DenseInstance) :
    inst.encode.length = 2 + inst.m * inst.r := by
  simp [encode, List.length_flatMap, Nat.add_comm]

theorem init_mem_m {reg : ℕ} (inst : DenseInstance) :
    (Data.init inst.encode : Data reg).mem 1 = inst.m := rfl

theorem init_mem_r {reg : ℕ} (inst : DenseInstance) :
    (Data.init inst.encode : Data reg).mem 2 = inst.r := rfl

theorem init_mem_entry {reg : ℕ} (inst : DenseInstance) (u : Fin inst.m) (v : Fin inst.r) :
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

/-- An `n`-element strict comparability relation `lt : Fin n × Fin n → Bool` for computing a
Dilworth minimum chain cover and maximum antichain on the word RAM. -/
structure PosetInstance where
  /-- Number of elements of the poset. -/
  n : ℕ
  /-- Strict comparability indicator `lt (i, j) = true` when element `i` is strictly below `j`. -/
  lt : Fin n × Fin n → Bool

namespace PosetInstance

/-- Construct a `PosetInstance` from an enumerated poset `e : Fin n ≃ α`. -/
@[expose] def ofEnum {α : Type*} {n : ℕ} [LT α] [DecidableLT α] (e : Fin n ≃ α) : PosetInstance where
  n := n
  lt := enumLtGraph e

/-- Underlying `n × n` dense bipartite instance on `inst.lt`. -/
@[expose] def toDense (inst : PosetInstance) : DenseInstance where
  m := inst.n
  r := inst.n
  graph := inst.lt

/-- Row-major word encoding `n :: matrixWords` (`1 + n * n` words). -/
@[expose] def encode (inst : PosetInstance) : List ℕ :=
  inst.n :: (List.finRange inst.n).flatMap fun u =>
    (List.finRange inst.n).map fun v => if inst.lt (u, v) then 1 else 0

/-- Chain label list `[c₀, …, c_{n - 1}]` computed by Fulkerson's reduction on `inst.lt`. -/
@[expose] def chainLabelsList (inst : PosetInstance) : List ℕ :=
  let hk := hopcroftKarpDense inst.lt
  let lab := chainLabels hk.matching (List.finRange inst.n ×ˢ List.finRange inst.n)
    (Vector.ofFn id)
  (List.finRange inst.n).map fun i => (vget lab i).val

/-- Sorted index list of the König uncovered antichain of `inst.lt`. -/
@[expose] def antichainList (inst : PosetInstance) : List ℕ :=
  let hk := hopcroftKarpDense inst.lt
  ((List.finRange inst.n).filter fun i => decide (i ∈ hk.cover.uncovered)).map Fin.val

/-- Sufficient word-value envelope for `O(n^{5/2})` chain cover and antichain computation. -/
@[expose] def wordBound (inst : PosetInstance) : ℕ :=
  2 * inst.n * inst.n + 16 * inst.n + 16

theorem chainLabelsList_ofEnum {α : Type*} {n : ℕ} [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    (ofEnum e).chainLabelsList =
      (List.finRange n).map fun i => (vget (minChainCover e).labels i).val := rfl

theorem antichainList_ofEnum {α : Type*} {n : ℕ} [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    (ofEnum e).antichainList =
      ((List.finRange n).filter fun i => decide (i ∈ (minChainCover e).antichain)).map Fin.val := by
  simp [ofEnum, antichainList, minChainCover, foldl_uncoveredStep]

theorem length_antichainList_ofEnum {α : Type*} {n : ℕ} [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    (ofEnum e).antichainList.length = (minChainCover e).antichain.card := by
  rw [antichainList_ofEnum, List.length_map]
  have hnd : ((List.finRange n).filter fun i => decide (i ∈ (minChainCover e).antichain)).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  simp

theorem encode_length (inst : PosetInstance) :
    inst.encode.length = 1 + inst.n * inst.n := by
  simp [encode, List.length_flatMap, Nat.add_comm]

theorem init_mem_n {reg : ℕ} (inst : PosetInstance) :
    (Data.init inst.encode : Data reg).mem 1 = inst.n := rfl

theorem init_mem_entry {reg : ℕ} (inst : PosetInstance) (u v : Fin inst.n) :
    (Data.init inst.encode : Data reg).mem (2 + (u.val * inst.n + v.val)) =
      if inst.lt (u, v) then 1 else 0 := by
  let g : Fin inst.n → List ℕ := fun u' =>
    (List.finRange inst.n).map fun v' => if inst.lt (u', v') then 1 else 0
  have h := List.getElem?_flatMap_mul_add (List.finRange inst.n) g inst.n
    (fun _ _ => by simp [g]) (show u.val < (List.finRange inst.n).length by simp) v.isLt
  rw [show 2 + (u.val * inst.n + v.val) = (u.val * inst.n + v.val) + 1 + 1 by omega,
    Data.init_mem_succ, encode, List.getD_cons_succ, List.getD_eq_getElem?_getD, h]
  simp [g]

theorem inputFits_encode {w : ℕ} (inst : PosetInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  refine ⟨hw.of_le (by rw [inst.encode_length]; unfold wordBound; nlinarith), fun x hx => ?_⟩
  simp only [encode, List.mem_cons, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_map] at hx
  rcases hx with rfl | ⟨u, v, rfl⟩
  · exact hw.of_le (by unfold wordBound; nlinarith)
  · split_ifs <;> exact hw.of_le (by unfold wordBound; nlinarith)

end PosetInstance

/-! ## Registers and memory layout -/

namespace Reg

private abbrev zero : Fin 34 := ⟨0, by decide⟩
private abbrev one : Fin 34 := ⟨1, by decide⟩
private abbrev two : Fin 34 := ⟨2, by decide⟩
private abbrev rm : Fin 34 := ⟨3, by decide⟩
private abbrev rr : Fin 34 := ⟨4, by decide⟩
private abbrev rE : Fin 34 := ⟨5, by decide⟩
private abbrev bOffReg : Fin 34 := ⟨6, by decide⟩
private abbrev bEdgesReg : Fin 34 := ⟨7, by decide⟩
private abbrev bColMateReg : Fin 34 := ⟨8, by decide⟩
private abbrev bMLReg : Fin 34 := ⟨9, by decide⟩
private abbrev bDistReg : Fin 34 := ⟨10, by decide⟩
private abbrev bQueueReg : Fin 34 := ⟨11, by decide⟩
private abbrev bVisReg : Fin 34 := ⟨12, by decide⟩
private abbrev bStackUReg : Fin 34 := ⟨13, by decide⟩
private abbrev bStackVReg : Fin 34 := ⟨14, by decide⟩
private abbrev bStackPosReg : Fin 34 := ⟨15, by decide⟩
private abbrev bAugUReg : Fin 34 := ⟨16, by decide⟩
private abbrev bAugVReg : Fin 34 := ⟨17, by decide⟩
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

private theorem BaseRegs.of_eq {inst : SparseInstance} {bOff : ℕ} {x y : Data 34}
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

private theorem finRange_take_succ {n k : ℕ} (hk : k < n) :
    (List.finRange n).take (k + 1) = (List.finRange n).take k ++ [⟨k, hk⟩] := by
  have hlt : k < (List.finRange n).length := by simpa using hk
  rw [List.take_add_one, List.getElem?_eq_getElem hlt]
  simp

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
  let s₁ := (x.set addr (x.regs baseReg)).set limit (x.regs baseReg + x.regs lenReg)
  have hs₁_addr : s₁.regs addr = x.regs baseReg := by simp [s₁]
  have hs₁_lim : s₁.regs limit = x.regs baseReg + x.regs lenReg := by simp [s₁]
  have hs₁_0 : s₁.regs zero = 0 := by simp [s₁, h0]
  have hs₁_1 : s₁.regs one = 1 := by simp [s₁, h1]
  have hzf := (zeroFill_exec (w := w) (cur := addr) (stop := limit) (zero := zero) (one := one)
    (x := s₁) (by decide) (by decide) (by decide) hs₁_0 hs₁_1
    (by rw [hs₁_addr, hs₁_lim]; omega) (by rwa [hs₁_lim])).within
  refine ⟨_, (he₁.seq hzf).mono (by rw [hs₁_addr, hs₁_lim]; omega), fun i hi => ?_, ?_⟩
  · have hia : i ≠ addr := fun h => by subst h; simp at hi
    have hil : i ≠ limit := fun h => by subst h; simp at hi
    simp [s₁, Function.update_of_ne hia, hil]
  · simp [s₁, hs₁_addr, hs₁_lim]

private def fillConstBody (baseReg valReg : Fin 34) : Code .standard 34 := ram[
  addr ← baseReg + idx; *addr ← valReg; idx ← idx + one ]

private def fillConst (baseReg lenReg valReg : Fin 34) : Code .standard 34 :=
  .seq (ram[ idx ← #0 ]) (.loop (.lt idx lenReg) (fillConstBody baseReg valReg))

private theorem exec_fillConst {w : ℕ} (baseReg lenReg valReg : Fin 34)
    (hb_lt : baseReg.val < 28) (hl_lt : lenReg.val < 28) (hv_lt : valReg.val < 28)
    (x : Data 34) (h1 : x.regs one = 1)
    (hfit_end : Fits w (x.regs baseReg + x.regs lenReg))
    (hfit_len : Fits w (x.regs lenReg)) :
    ∃ y, ExecWithin w (fillConst baseReg lenReg valReg) x y (5 * x.regs lenReg + 3) ∧
      (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ k < x.regs lenReg, y.mem (x.regs baseReg + k) = x.regs valReg) ∧
      (∀ a, ¬(x.regs baseReg ≤ a ∧ a < x.regs baseReg + x.regs lenReg) → y.mem a = x.mem a) := by
  let b := x.regs baseReg
  let N := x.regs lenReg
  let v := x.regs valReg
  let P (k : ℕ) (y : Data 34) : Prop :=
    (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ j < k, y.mem (b + j) = v) ∧
      (∀ a, ¬(b ≤ a ∧ a < b + k) → y.mem a = x.mem a)
  have h0 : ∃ s₀, ExecWithin w (ram[ idx ← #0 ] : Code .standard 34) x s₀ 1 ∧
      s₀ = x.set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [Fits.zero w]
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := h0
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < N) :
      ∃ z, ExecWithin w (fillConstBody baseReg valReg) y z 3 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    have hby : y.regs baseReg = b := hr baseReg hb_lt
    have hvy : y.regs valReg = v := hr valReg hv_lt
    have hoy : y.regs one = 1 := (hr one (by decide)).trans h1
    have hfa : Fits w (b + y.regs idx) := hfit_end.of_le (by omega)
    have hfn : Fits w (y.regs idx + 1) := hfit_len.of_le (by omega)
    have hstep : ∃ z, ExecWithin w (fillConstBody baseReg valReg) y z 3 ∧
        z = ((y.set addr (b + y.regs idx)).write (b + y.regs idx) v).set idx (y.regs idx + 1) := by
      refine WP.exists_execWithin ?_
      unfold fillConstBody
      wram_exec [hby, hvy, hoy, hfa, hfn]
      rfl
    obtain ⟨z, he, rfl⟩ := hstep
    obtain ⟨hm', hf'⟩ := prefix_write_step hm hf (e := fun _ => v) rfl
    refine ⟨_, he, ⟨fun i hi => by wram_simp [hr i hi], hm', hf'⟩, by wram_simp⟩
  obtain ⟨y, hl, hPN, _⟩ := ExecWithin.loop_count P (fun y hy => hy.1 lenReg hl_lt) hbody
    (x := x.set idx 0) (by simp) ⟨fun i hi => by wram_simp, fun _ hj => by simp at hj,
      fun _ _ => rfl⟩
  exact ⟨y, (he₀.seq hl).mono (by simp [N]; omega), hPN.1, hPN.2.1, hPN.2.2⟩

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
  let bCol := bOff + inst.m + 1 + inst.numEdges
  let bML := bCol + inst.r
  obtain ⟨y₁, he₁, hr₁, hmem₁⟩ := exec_clearAt bMLReg rm (by decide) (by decide) x
    hb.hzero hb.hone (by rw [hb.hbML, hb.hrm]; exact hfit.of_le (by omega))
  rw [hb.hbML, hb.hrm] at he₁ hmem₁
  have hb₁ : BaseRegs inst bOff y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  let P (k : ℕ) (y : Data 34) : Prop :=
    (∀ i : Fin 34, i.val < 28 → y.regs i = x.regs i) ∧
      (∀ u : Fin inst.m, y.mem (bML + u.val) =
        if vget (((List.finRange inst.r).take k).foldl (hkMarkStep mate)
            (Vector.replicate inst.m false)) u = true then 1 else 0) ∧
      (∀ a, ¬(bML ≤ a ∧ a < bML + inst.m) → y.mem a = x.mem a)
  have hs₀ : ∃ s₀, ExecWithin w (ram[ idx ← #0 ] : Code .standard 34) y₁ s₀ 1 ∧
      s₀ = y₁.set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [Fits.zero w]
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  have hP₀ : P 0 (y₁.set idx 0) := by
    refine ⟨fun i hi => by wram_simp [hr₁ i (by omega)], fun u => ?_, fun a ha => ?_⟩
    · simp only [Data.set, List.take_zero, List.foldl_nil, vget_replicate, Bool.false_eq_true,
        ↓reduceIte, hmem₁]
      exact clear_of_owns ⟨by omega, by omega⟩
    · simp only [Data.set, hmem₁]
      exact clear_of_not_owns ha
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.r) :
      ∃ z, ExecWithin w markMLBody y z 6 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hm, hf⟩ := hy
    let v : Fin inst.r := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hcol_v : y.mem (bCol + y.regs idx) = encodeOptFin (vget mate v) := by
      rw [hf _ (by omega)]
      exact hmate v
    have htk := finRange_take_succ hlt
    have hf1 : Fits w (bCol + y.regs idx) := hfit.of_le (by omega)
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
      rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simpa [hkMarkStep, hmv] using hm u
    | some w₀ =>
      have henc : encodeOptFin (vget mate v) = w₀.val := by simp [hmv, encodeOptFin]
      have hwlt : w₀.val < inst.m := w₀.isLt
      have hf3 : Fits w (bML + w₀.val) := hfit.of_le (by omega)
      wram_exec [hby.hbColMate, hby.hbML, hby.hrm, hby.hzero, hby.hone, hcol_v, henc, hwlt,
        hf1, hf2, hf3]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], fun u => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · wram_simp
        rw [htk, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [hkMarkStep, hmv]
        rcases eq_or_ne u w₀ with rfl | hne
        · simp [bML, bCol]
        · have hne_a : bML + u.val ≠ bML + w₀.val := fun h => hne (Fin.ext (by omega))
          simpa [bML, bCol, Function.update_of_ne hne_a, vget_vset_ne _ _ hne.symm] using hm u
      · wram_simp
        rw [Function.update_of_ne (by omega)]
        exact hf a ha
  obtain ⟨y, hl, hPr, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rr (by decide)).trans hb.hrr) hbody
    (x := y₁.set idx 0) (by simp) (by simpa using hP₀)
  refine ⟨y, (he₁.seq (he₀.seq hl)).mono (by simp; omega), hPr.1, fun u => ?_, hPr.2.2⟩
  have hfull : (List.finRange inst.r).take inst.r = List.finRange inst.r :=
    List.take_of_length_le (by simp)
  simpa [hkMatchedLeft, hfull] using hPr.2.1 u

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
  let bML := bOff + inst.m + 1 + inst.numEdges + inst.r
  let bDist := bML + inst.m
  let bQueue := bDist + inst.m
  obtain ⟨y₁, he₁, hr₁, hmem₁⟩ := exec_clearAt bDistReg rm (by decide) (by decide) x
    hb.hzero hb.hone (by rw [hb.hbDist, hb.hrm]; exact hfit.of_le (by omega))
  rw [hb.hbDist, hb.hrm] at he₁ hmem₁
  have hs₀ : ∃ s₀, ExecWithin w
      (ram[ qHead ← #0; qTail ← #0; rk ← #0; rfound ← #0; idx ← #0 ] : Code .standard 34) y₁ s₀ 5 ∧
      s₀ = ((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [Fits.zero w]
    rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let pk (k : ℕ) :=
    ((List.finRange inst.m).take k).foldl (hkBfsInitStep ml) (Vector.replicate inst.m none, [])
  let P (k : ℕ) (y : Data 34) : Prop :=
    (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      DistMem bDist (pk k).1 y.mem ∧
      QueueSlice bQueue 0 (pk k).2 y.mem ∧
      y.regs qHead = 0 ∧
      y.regs qTail = (pk k).2.length ∧
      y.regs rk = 0 ∧
      y.regs rfound = 0 ∧
      (pk k).2.Nodup ∧
      (∀ x₀ ∈ (pk k).2, x₀.val < k) ∧
      (∀ u : Fin inst.m, vget (pk k).1 u ≠ none ↔ u ∈ (pk k).2) ∧
      (∀ a, ¬(bDist ≤ a ∧ a < bQueue + k) → y.mem a = x.mem a)
  have hP₀ : P 0 (((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0) := by
    refine ⟨fun i hi => by wram_simp [hr₁ i (by omega)], fun u => ?_, fun i hi => by simp [pk] at hi,
      by wram_simp, by wram_simp; simp [pk], by wram_simp, by wram_simp, by simp [pk],
      fun _ h => by simp [pk] at h, fun u => by simp [pk, vget_replicate], fun a ha => ?_⟩
    · simp only [Data.set, pk, List.take_zero, List.foldl_nil, vget_replicate, encodeDist, hmem₁]
      exact clear_of_owns ⟨by omega, by omega⟩
    · simp only [Data.set, hmem₁]
      exact clear_of_not_owns (by omega)
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.m) :
      ∃ z, ExecWithin w seedBfsBody y z 9 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hr, hdM, hqM, hqh, hqt, hrk, hrf, hnd, hlt_mem, hiff, hf⟩ := hy
    let u : Fin inst.m := ⟨y.regs idx, hlt⟩
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hml_u : y.mem (bML + y.regs idx) = if vget ml u = true then 1 else 0 := by
      rw [hf _ (by omega)]
      exact hml u
    have hlen_le : (pk (y.regs idx)).2.length ≤ y.regs idx := by
      have hsub : (pk (y.regs idx)).2.Sublist ((List.finRange inst.m).take (y.regs idx)) := by
        clear hml_u hby hr hdM hqM hqh hqt hrk hrf hnd hlt_mem hiff hf
        generalize (List.finRange inst.m).take (y.regs idx) = ls
        have hgen : ∀ (ls : List (Fin inst.m)) (acc : Vector (Option ℕ) inst.m × List (Fin inst.m)),
            (ls.foldl (hkBfsInitStep ml) acc).2 <+ acc.2 ++ ls := by
          intro ls
          induction ls with
          | nil => intro acc; simp
          | cons a ls ih =>
            intro acc
            simp only [List.foldl_cons, hkBfsInitStep]
            split_ifs
            · exact (ih acc).trans (List.sublist_append_of_sublist_right (List.sublist_cons_self _ _))
            · simpa [List.append_assoc] using ih (vset acc.1 a (some 0), acc.2 ++ [a])
        simpa [pk] using hgen ls (Vector.replicate inst.m none, [])
      exact hsub.length_le.trans (by simp; omega)
    have htk : pk (y.regs idx + 1) = hkBfsInitStep ml (pk (y.regs idx)) u := by
      simp only [pk, finRange_take_succ hlt, List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hf1 : Fits w (bML + y.regs idx) := hfit.of_le (by omega)
    have hf2 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold seedBfsBody
    by_cases hmu : vget ml u = true
    · have hval1 : (if vget ml u = true then 1 else 0) = 1 := ite_eq_left hmu
      wram_exec [hby.hbML, hby.hzero, hby.hone, hml_u, hval1, hf1, hf2]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], ?_, ?_, by wram_simp [hqh], ?_,
        by wram_simp [hrk], by wram_simp [hrf], ?_, ?_, ?_, fun a ha => ?_⟩, by wram_simp⟩
      · intro w₀; wram_simp; rw [htk, hkBfsInitStep, ite_eq_left hmu]; exact hdM w₀
      · intro i hi; wram_simp; rw [htk, hkBfsInitStep, ite_eq_left hmu] at hi ⊢; exact hqM i hi
      · wram_simp; rw [htk, hkBfsInitStep, ite_eq_left hmu]; exact hqt
      · rw [htk, hkBfsInitStep, ite_eq_left hmu]; exact hnd
      · intro x₀ hx₀; rw [htk, hkBfsInitStep, ite_eq_left hmu] at hx₀
        exact Nat.lt_succ_of_lt (hlt_mem x₀ hx₀)
      · intro w₀; rw [htk, hkBfsInitStep, ite_eq_left hmu]; exact hiff w₀
      · wram_simp; exact hf a (by omega)
    · have hval0 : (if vget ml u = true then 1 else 0) = 0 := ite_eq_right hmu
      have hf3 : Fits w (bDist + y.regs idx) := hfit.of_le (by omega)
      have hf4 : Fits w (bQueue + (pk (y.regs idx)).2.length) := hfit.of_le (by omega)
      have hf5 : Fits w ((pk (y.regs idx)).2.length + 1) := hfit.of_le (by omega)
      have hu_not_mem : u ∉ (pk (y.regs idx)).2 := fun h => Nat.lt_irrefl _ (hlt_mem u h)
      wram_exec [hby.hbML, hby.hbDist, hby.hbQueue, hby.hzero, hby.hone, hml_u, hval0, hqt,
        hf1, hf2, hf3, hf4, hf5]
      refine ⟨⟨fun i hi => by wram_simp [hr i hi], ?_, ?_, by wram_simp [hqh], ?_,
        by wram_simp [hrk], by wram_simp [hrf], ?_, ?_, ?_, fun a ha => ?_⟩, by wram_simp⟩
      · intro w₀
        wram_simp
        rw [htk, hkBfsInitStep, ite_eq_right hmu]
        rcases eq_or_ne w₀ u with rfl | hne
        · simp [bDist, bML, encodeDist]
        · have hne_a : bDist + w₀.val ≠ bDist + y.regs idx := fun h => hne (Fin.ext (by omega))
          have hne_q : bDist + w₀.val ≠ bQueue + (pk (y.regs idx)).2.length := by omega
          rw [Function.update_of_ne hne_q, Function.update_of_ne hne_a, vget_vset_ne _ _ hne.symm]
          exact hdM w₀
      · intro i hi
        wram_simp
        rw [htk, hkBfsInitStep, ite_eq_right hmu] at hi ⊢
        simp only [List.length_append, List.length_singleton] at hi
        by_cases hlt_i : i < (pk (y.regs idx)).2.length
        · rw [Nat.add_zero, Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            List.getElem_append_left hlt_i]
          simpa using hqM i hlt_i
        · have heqi : i = (pk (y.regs idx)).2.length := by omega
          subst heqi
          simp [bQueue, bDist, bML, u]
      · wram_simp [htk, hkBfsInitStep, ite_eq_right hmu]
      · rw [htk, hkBfsInitStep, ite_eq_right hmu]
        exact List.nodup_append.mpr ⟨hnd, List.nodup_singleton u, fun a ha b hb hab => by
          obtain rfl := List.mem_singleton.mp hb; subst hab; exact hu_not_mem ha⟩
      · intro x₀ hx₀
        rw [htk, hkBfsInitStep, ite_eq_right hmu, List.mem_append, List.mem_singleton] at hx₀
        rcases hx₀ with hx₀ | rfl
        · exact Nat.lt_succ_of_lt (hlt_mem x₀ hx₀)
        · exact Nat.lt_succ_self _
      · intro w₀
        rw [htk, hkBfsInitStep, ite_eq_right hmu]
        rcases eq_or_ne w₀ u with rfl | hne
        · simp
        · simp [vget_vset_ne _ _ hne.symm, hiff w₀, hne]
      · wram_simp
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
        exact hf a (by omega)
  obtain ⟨y₂, hl, hPm⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.1 rm (by decide)).trans hb.hrm) hbody
    (x := ((((y₁.set qHead 0).set qTail 0).set rk 0).set rfound 0).set idx 0) (by simp)
    (by simpa using hP₀)
  obtain ⟨⟨hr₂, hdM₂, hqM₂, hqh₂, hqt₂, hrk₂, hrf₂, hnd₂, _, hiff₂, hf₂⟩, _⟩ := hPm
  have hfull : pk inst.m = p := by
    simp [pk, p, List.take_of_length_le (by simp)]
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
    fun a ha => (congrFun hmem₃ a).trans (hf₂ a ha)⟩

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
    ← Finset.mul_sum, Finset.sum_const]

private theorem exec_bfsEdgeLoop {w bOff j qh le : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
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
    (hcard_q : ∀ s' : HKBfsState inst.m,
      (∀ w₀, vget s'.dist w₀ ≠ none → vget s.dist w₀ ≠ none ∨ w₀ ∈ s'.next) →
      s'.next.Nodup → le + s'.next.length ≤ inst.m → True)
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
  let bEdges := bOff + inst.m + 1
  let bCol := bEdges + inst.numEdges
  let bDist := bCol + inst.r + inst.m
  let bQueue := bDist + inst.m
  let sk (k : ℕ) : HKBfsState inst.m :=
    ((inst.adj u).take (k - inst.offset u.val)).foldl (hkBfsStep inst.graph mate j u) s
  have hoff_succ := inst.offset_succ u.isLt
  let P (k : ℕ) (y : Data 34) : Prop :=
    inst.offset u.val ≤ k ∧
      (∀ i : Fin 34, i.val < 20 → y.regs i = x.regs i) ∧
      y.regs limit = inst.offset (u.val + 1) ∧
      DistMem bDist (sk k).dist y.mem ∧
      QueueSlice bQueue qh queued y.mem ∧
      QueueSlice bQueue le (sk k).next y.mem ∧
      y.regs rk = j ∧
      y.regs rfound = (if (sk k).found then 1 else 0) ∧
      y.regs qHead = qh ∧
      y.regs layerEnd = le ∧
      y.regs qTail = le + (sk k).next.length ∧
      y.regs active = 1 ∧
      (∀ w₀ : Fin inst.m, vget (sk k).dist w₀ = none → w₀ ∉ (sk k).next) ∧
      le + (Finset.univ.filter fun w₀ => vget (sk k).dist w₀ = none).card + (sk k).next.length ≤
        inst.m ∧
      (∀ a, ¬(bDist ≤ a ∧ a < bQueue + inst.m) → y.mem a = x.mem a)
  have hsk₀ : sk (x.regs idx) = s := by simp [sk, hidx]
  have hP₀ : P (x.regs idx) x := by
    rw [hsk₀]
    exact ⟨by omega, fun _ _ => rfl, hlim, hdM, hq_pre, hq_next, hrk, hrf, hqh, hle, hqt, hact,
      hiff, hqt_bound, fun _ _ => rfl⟩
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.offset (u.val + 1)) :
      ∃ z, ExecWithin w bfsEdgeBody y z 16 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨hge, hr, hlim_y, hdMy, hq_pre_y, hq_next_y, hrk_y, hrf_y, hqh_y, hle_y, hqt_y,
      hact_y, hiff_y, hbound_y, hf_y⟩ := hy
    let t := y.regs idx - inst.offset u.val
    have ht_lt : t < (inst.adj u).length := by omega
    let v : Fin inst.r := (inst.adj u)[t]'ht_lt
    have hv_mem : v ∈ inst.adj u := List.getElem_mem ht_lt
    have hGu : inst.graph (u, v) = true := decide_eq_true hv_mem
    have hsk_step : sk (y.regs idx + 1) = hkBfsStep inst.graph mate j u (sk (y.regs idx)) v := by
      have hsub : y.regs idx + 1 - inst.offset u.val = t + 1 := by omega
      simp only [sk, hsub, List.take_add_one, List.getElem?_eq_getElem ht_lt, Option.toList_some,
        List.foldl_append, List.foldl_cons, List.foldl_nil, v]
    have hby : BaseRegs inst bOff y := hb.of_eq fun i hi => hr i (by omega)
    have hp_eq : y.regs idx = inst.offset u.val + t := by omega
    have hedge_y : y.mem (bEdges + y.regs idx) = v.val := by
      rw [hf_y _ (by have := inst.offset_add_lt_numEdges u ht_lt; omega), hp_eq]
      exact hcsr.hedge u ht_lt
    have hmate_v : y.mem (bCol + v.val) = encodeOptFin (vget mate v) := by
      rw [hf_y _ (by have := v.isLt; omega)]
      exact hmate v
    have hf_edge : Fits w (bEdges + y.regs idx) :=
      hfit.of_le (by have := inst.offset_add_lt_numEdges u ht_lt; omega)
    have hf_col : Fits w (bCol + v.val) := hfit.of_le (by have := v.isLt; omega)
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
      have hdist_w : y.mem (bDist + w₀.val) = encodeDist (vget (sk (y.regs idx)).dist w₀) :=
        hdMy w₀
      have hf_dw : Fits w (bDist + w₀.val) := hfit.of_le (by have := w₀.isLt; omega)
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
        have hf_qw : Fits w (bQueue + (le + (sk (y.regs idx)).next.length)) :=
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
          wram_simp
          rw [hsk_step]
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte]
          rcases eq_or_ne x₀ w₀ with rfl | hne
          · simp [bDist, bCol, bEdges, encodeDist]
          · have hne1 : bDist + x₀.val ≠ bQueue + (le + (sk (y.regs idx)).next.length) := by
              have := x₀.isLt; omega
            have hne2 : bDist + x₀.val ≠ bDist + w₀.val := fun h => hne (Fin.ext (by omega))
            rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
              vget_vset_ne _ _ hne.symm]
            exact hdMy x₀
        · intro i hi
          wram_simp
          have hne1 : bQueue + qh + i ≠ bQueue + (le + (sk (y.regs idx)).next.length) := by omega
          have hne2 : bQueue + qh + i ≠ bDist + w₀.val := by have := w₀.isLt; omega
          rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
          exact hq_pre_y i hi
        · intro i hi
          wram_simp
          rw [hsk_step] at hi ⊢
          simp only [hkBfsStep, hGu, hmv, hdw, ↓reduceIte, List.length_append,
            List.length_singleton] at hi ⊢
          by_cases hlt_i : i < (sk (y.regs idx)).next.length
          · have hne1 : bQueue + le + i ≠ bQueue + (le + (sk (y.regs idx)).next.length) := by omega
            have hne2 : bQueue + le + i ≠ bDist + w₀.val := by have := w₀.isLt; omega
            rw [Function.update_of_ne hne1, Function.update_of_ne hne2,
              List.getElem_append_left hlt_i]
            exact hq_next_y i hlt_i
          · have heqi : i = (sk (y.regs idx)).next.length := by omega
            subst heqi
            simp [bQueue, bDist, bCol, bEdges, Nat.add_assoc]
        · wram_simp; rw [hsk_step]; simp [hkBfsStep, hGu, hmv, hdw, hrf_y]
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
        · wram_simp
          rw [Function.update_of_ne (by omega),
            Function.update_of_ne (by have := w₀.isLt; omega)]
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
        · wram_simp; rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hrf_y
        · wram_simp; rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hqt_y
        · rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hiff_y
        · rw [hsk_step]; simpa [hkBfsStep, hGu, hmv, hdw] using hbound_y
  obtain ⟨y, hl, hPend, _⟩ := ExecWithin.loop_count P (fun y hy => hy.2.1) hbody
    (x := x) (by rw [hidx, hoff_succ]; omega) hP₀
  have hsk_end : sk (inst.offset (u.val + 1)) = sF := by
    have hsub : inst.offset (u.val + 1) - inst.offset u.val = (inst.adj u).length := by omega
    simp [sk, hsub, List.take_of_length_le (le_refl _), sF]
  rw [hsk_end] at hPend
  obtain ⟨_, hr, _, hdM', hq_pre', hq_next', hrk', hrf', hqh', hle', hqt', hact',
    hiff', hbound', hf'⟩ := hPend
  exact ⟨y, hl.mono (by rw [hidx, hoff_succ]; omega), hr, hdM', hq_pre', hq_next',
    hrk', hrf', hqh', hle', hqt', hact', hiff', hbound', hf'⟩

private theorem exec_bfsFrontierLoop {w bOff j qh le : ℕ} {inst : SparseInstance}
    {mate : Vector (Option (Fin inst.m)) inst.r}
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
      simp [Cond.Holds, hqh, hle, ← hle_eq]
    exact ⟨x, ExecWithin.loop_exit hc, fun _ _ => rfl, hdM, hq_next, hrk, hrf,
      by omega, hle, hqt, hact, hiff, hqt_bound, fun _ _ => rfl⟩
  | cons u us ih =>
    have hc : (Cond.lt qHead layerEnd).Holds x := by
      simp only [Cond.Holds, hqh, hle]
      simp only [List.length_cons] at hle_eq
      omega
    let bQueue := bOff + inst.m + 1 + inst.numEdges + inst.r + 2 * inst.m
    have hq_u : x.mem (bQueue + qh) = u.val := by
      simpa using hq_pre 0 (by simp)
    have hq_us : QueueSlice bQueue (qh + 1) us x.mem := fun i hi => by
      have h := hq_pre (i + 1) (by simp; omega)
      simpa [Nat.add_assoc, Nat.add_comm 1 i] using h
    have hoff_u : x.mem (bOff + u.val) = inst.offset u.val := hcsr.hoff (le_of_lt u.isLt)
    have hoff_u1 : x.mem (bOff + u.val + 1) = inst.offset (u.val + 1) := by
      simpa [Nat.add_assoc] using hcsr.hoff u.isLt
    have hf_qu : Fits w (bQueue + qh) := by
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
        x₁ = (((((x.set addr (bQueue + qh)).set val u.val).set qHead (qh + 1)).set
          addr (bOff + u.val)).set idx (inst.offset u.val)).set addr (bOff + u.val + 1) |>.set
          limit (inst.offset (u.val + 1)) := by
      refine WP.exists_execWithin ?_
      wram_exec [hb.hbQueue, hb.hbOff, hb.hone, hqh, hq_u, hoff_u, hoff_u1,
        hf_qu, hf_qh1, hf_ou, hf_ou1]
      rfl
    obtain ⟨x₁, he_set, rfl⟩ := hsetup
    have hb₁ : BaseRegs inst bOff x₁ := hb.of_eq fun i hi => by wram_simp
    obtain ⟨x₂, he_edges, hr₂, hdM₂, hq_us₂, hq_next₂, hrk₂, hrf₂, hqh₂, hle₂, hqt₂, hact₂,
      hiff₂, hbound₂, hf₂⟩ :=
      exec_bfsEdgeLoop u s us _ hb₁ hcsr hmate hdM hq_us hq_next
        (by simp only [List.length_cons] at hle_eq; omega)
        (by wram_simp) (by wram_simp) (by wram_simp [hrk]) (by wram_simp [hrf])
        (by wram_simp) (by wram_simp [hle]) (by wram_simp [hqt]) (by wram_simp [hact])
        hiff (fun _ _ _ _ => trivial) hqt_bound hj_le hfit
    have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq hr₂
    have hcsr₂ : CSRMem inst bOff x₂.mem := hcsr.of_outside fun a ha => hf₂ a (by omega)
    have hmate₂ : MateMem (bOff + inst.m + 1 + inst.numEdges) mate x₂.mem :=
      fun v => (hf₂ _ (by have := v.isLt; omega)).trans (hmate v)
    obtain ⟨y, he_rest, hr₃, hdM₃, hq_next₃, hrk₃, hrf₃, hqh₃, hle₃, hqt₃, hact₃,
      hiff₃, hbound₃, hf₃⟩ :=
      ih hb₂ hcsr₂ hmate₂ hdM₂ hq_us₂ hq_next₂
        (by simp only [List.length_cons] at hle_eq; omega)
        hrk₂ hrf₂ hqh₂ hle₂ hqt₂ hact₂ hiff₂ hbound₂ hj_le hfit
    refine ⟨y, (ExecWithin.loop_iter hc (he_set.seq he_edges) he_rest).mono ?_,
      fun i hi => (hr₃ i hi).trans ((hr₂ i hi).trans (by wram_simp)),
      hdM₃, hq_next₃, hrk₃, hrf₃, hqh₃, hle₃, hqt₃, hact₃, hiff₃, hbound₃,
      fun a ha => (hf₃ a ha).trans (hf₂ a ha)⟩
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
      simp [Cond.Holds, hact, hb.hone]
    exact ⟨x, (ExecWithin.loop_exit hc).mono (by omega), fun _ _ => rfl, hdM, hrk, hrf,
      fun _ _ => rfl⟩
  | succ fuel ih =>
    by_cases hnil : frontier = []
    · subst hnil
      have hc : ¬(Cond.eq active one).Holds x := by
        simp [Cond.Holds, hact, hb.hone]
      refine ⟨x, (ExecWithin.loop_exit hc).mono (by omega), fun _ _ => rfl, ?_, ?_, ?_,
        fun _ _ => rfl⟩
      · simpa [hkBfsLoop, hkBfsLayer] using hdM
      · simpa [hkBfsLoop, hkBfsLayer] using hrk
      · simpa [hkBfsLoop, hkBfsLayer] using hrf
    · have hpos_f : 0 < frontier.length := List.length_pos_iff.mpr hnil
      have hc : (Cond.eq active one).Holds x := by
        simp [Cond.Holds, hact, hnil, hb.hone]
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
        exec_bfsFrontierLoop frontier ⟨dist, [], false⟩ (x.set layerEnd le) hb₁ hcsr hmate hdM
          hq_pre (fun _ hi => by simp at hi) rfl (by wram_simp [hrk]) (by wram_simp [hrf])
          (by wram_simp [hqh]) (by wram_simp) (by wram_simp [hqt, le])
          (by wram_simp [hact, hnil]) (fun _ _ h => nomatch h)
          (by simp only [List.length_nil, Nat.add_zero, le]; exact hbound) (by omega) hfit
      set s := hkBfsLayer inst.graph inst.adj mate j frontier ⟨dist, [], false⟩ with hs_def
      have hb₂ : BaseRegs inst bOff x₂ := hb₁.of_eq hr₂
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
          simp [Cond.Holds, hb₂.hone]
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
            simp [Cond.Holds, hb₂.hone]
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
              (by omega) (by omega) (by omega) hfit
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
  have hb₂ : BaseRegs inst bOff y₂ := hb₁.of_eq hr₂
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
  have hinit_pot := bfsInit_potential (hkMatchedLeft mate) (bfsVertWeight inst)
    (List.finRange inst.m) (Vector.replicate inst.m none, [])
  simp only [List.map_nil, List.sum_nil, Nat.add_zero] at hinit_pot
  have hrep_le := (vecPotential_le_sum (p := (· = none)) (bfsVertWeight inst)
    (Vector.replicate inst.m none)).trans_eq (sum_bfsVertWeight inst)
  have hfin_sum : ((List.finRange inst.m).map (bfsVertWeight inst)).sum =
      18 * inst.numEdges + 11 * inst.m := by
    rw [← List.sum_toFinset _ (List.nodup_finRange inst.m), Finset.toFinset_coe]
    · simp [← sum_bfsVertWeight inst]
  refine ⟨y₃, (he₁.seq (he₂.seq he₃)).mono ?_,
    fun i hi => (hr₃ i hi).trans ((hr₂ i hi).trans (hr₁ i (by omega))),
    hdM₃, hrk₃, hrf₃,
    fun a ha => (hf₃ a (by omega)).trans ((hf₂ a (by omega)).trans (hf₁ a (by omega)))⟩
  change _ ≤ _ at hinit_pot
  omega

end Cslib.Algorithms.WordRAM.HopcroftKarp
