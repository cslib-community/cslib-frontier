/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.HopcroftKarp
public import CslibFrontier.Computability.WordRAM.Function
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

/-!
# Hopcroft–Karp instances, register layout, and CSR frame

Problem instances (`SparseInstance`, `DenseInstance`), their word encodings and maximum-matching
outputs, the public register layout (`Reg`), and the in-memory CSR and workspace-pointer invariants
(`CSRMem`, `BaseRegs`) for the word-RAM Hopcroft–Karp implementation.

## Main definitions

* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance`: sparse CSR and dense matrix bipartite
  graph instances, encodings, word-width envelopes, and ordered maximum-matching outputs.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.Reg.zero`, `Cslib.Algorithms.WordRAM.HopcroftKarp.Reg.acc`:
  public register indices (`0 .. 18` and scalar `acc` under namespace `Reg`).
* `Cslib.Algorithms.WordRAM.HopcroftKarp.CSRMem`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.BaseRegs`: in-memory CSR layout and base-register frame.

## Main results

* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance.isMaxMatching_matchingPairs`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance.isMaxMatching_matchingPairs`: optimality of
  the flat-word matching outputs.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance.getElem_matchingWords_even`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance.getElem_matchingWords_odd`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance.getElem_matchingWords_even`,
  `Cslib.Algorithms.WordRAM.HopcroftKarp.DenseInstance.getElem_matchingWords_odd`: flat-word pair
  indexing.
* `Cslib.Algorithms.WordRAM.HopcroftKarp.SparseInstance.hasPerfectMatching_iff`: balanced
  perfect-matching characterization.
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

/-- Entry `offset u + i` of `inst.flatEdges` is the `i`-th neighbour of `u`. -/
theorem flatEdges_getElem (inst : SparseInstance) (u : Fin inst.m) {i : ℕ}
    (hi : i < (inst.adj u).length) :
    inst.flatEdges[inst.offset u.val + i]'(by
      rw [inst.length_flatEdges]; exact inst.offset_add_lt_numEdges u hi) =
      ((inst.adj u)[i]'hi).val := by
  simp only [inst.flatEdges_eq_append u, ← inst.length_take_flatEdges u.val,
    List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  rw [List.getElem_append_left (by simp [hi]), List.getElem_map]

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

/-- `inst.matchingPairs` agrees with filtering the final `hkLoop` right-vertex mate vector. -/
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

private theorem getElem_matchingWords_pair (inst : SparseInstance) {i : ℕ} (j : ℕ)
    (hi : i < inst.matchingPairs.length) (hj : j < 2) :
    inst.matchingWords[2 * i + j]'(by
      rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
      [(inst.matchingPairs[i]'hi).1.val, (inst.matchingPairs[i]'hi).2.val][j]'hj := by
  have h := List.getElem?_flatMap_mul_add inst.matchingPairs
    (fun e => [e.1.val, e.2.val]) 2 (fun _ _ => rfl) hi hj
  rw [Nat.mul_comm] at h
  have hlen : 2 * i + j < inst.matchingWords.length := by
    rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega
  rw [show List.flatMap (fun e => [e.1.val, e.2.val]) inst.matchingPairs = inst.matchingWords
      from rfl, List.getElem?_eq_getElem hlen, List.getElem?_eq_getElem (by simpa using hj)] at h
  exact Option.some.inj h

/-- Entry `2 * i` of `inst.matchingWords` is the left endpoint of the `i`-th matched edge. -/
theorem getElem_matchingWords_even (inst : SparseInstance) {i : ℕ}
    (hi : i < inst.matchingPairs.length) :
    inst.matchingWords[2 * i]'(by
      rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
      (inst.matchingPairs[i]'hi).1.val :=
  inst.getElem_matchingWords_pair 0 hi (by decide)

/-- Entry `2 * i + 1` of `inst.matchingWords` is the right endpoint of the `i`-th matched edge. -/
theorem getElem_matchingWords_odd (inst : SparseInstance) {i : ℕ}
    (hi : i < inst.matchingPairs.length) :
    inst.matchingWords[2 * i + 1]'(by
      rw [inst.length_matchingWords, ← inst.length_matchingPairs]; omega) =
      (inst.matchingPairs[i]'hi).2.val :=
  inst.getElem_matchingWords_pair 1 hi (by decide)

/-- `inst` is balanced (`m = r`) and `inst.graph` admits a perfect matching. -/
@[expose] def HasPerfectMatching (inst : SparseInstance) : Prop :=
  ∃ h : inst.m = inst.r,
    Cslib.Circuits.BipartiteMatching.HasPerfectMatching fun p : Fin inst.m × Fin inst.m =>
      inst.graph (p.1, p.2.cast h)

theorem hasPerfectMatching_iff (inst : SparseInstance) :
    inst.HasPerfectMatching ↔ inst.m = inst.r ∧ inst.maxMatchingCard = inst.m := by
  rcases inst with ⟨m, r, adj⟩
  dsimp only [HasPerfectMatching, maxMatchingCard]
  constructor
  · rintro ⟨rfl, hpm⟩
    have hiff := decidePerfectMatchingHK_eq_true_iff (bipAdjValid_graph ⟨m, m, adj⟩)
    simp only [decidePerfectMatchingHK, decide_eq_true_iff] at hiff
    exact ⟨rfl, hiff.mpr hpm⟩
  · rintro ⟨rfl, hcard⟩
    have hiff := decidePerfectMatchingHK_eq_true_iff (bipAdjValid_graph ⟨m, m, adj⟩)
    simp only [decidePerfectMatchingHK, decide_eq_true_iff] at hiff
    exact ⟨rfl, hiff.mp hcard⟩

instance (inst : SparseInstance) : Decidable inst.HasPerfectMatching :=
  decidable_of_iff (inst.m = inst.r ∧ inst.maxMatchingCard = inst.m)
    inst.hasPerfectMatching_iff.symm

theorem maxMatchingCard_le_min (inst : SparseInstance) :
    inst.maxMatchingCard ≤ min inst.m inst.r := by
  have hM := (hopcroftKarp_correct inst.bipAdjValid_graph).1.1
  have hl : inst.maxMatchingCard ≤ inst.m := by
    simpa [maxMatchingCard] using hM.card_le_card_left
  have hr : inst.maxMatchingCard ≤ inst.r := by
    simpa [maxMatchingCard] using hM.card_le_card_right
  omega

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
/-- Scalar output / loop-active register (for `Executes` programs). -/
abbrev acc : Fin 34 := ⟨27, by decide⟩

end Reg

open Reg

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

end Cslib.Algorithms.WordRAM.HopcroftKarp
