/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Arborescence.Branching
public import CslibFrontier.Computability.WordRAM.Signed.Encoding
import CslibFrontier.Foundations.Data.List.RowMajor

/-!
# Flat Word-RAM inputs and parent-list specifications for Chu–Liu/Edmonds

This module defines the input structures `ArborescenceInput` and `BranchingInput`, their
row-major flat Word-RAM encodings (`flattenBoolMatrix`, `flattenSignedMatrix`, `encode`), the
polynomial word-value/address bound `wordBound`, and the expected parent-list output maps with
optimality characterizations.

## Main definitions

* `Cslib.Algorithms.WordRAM.Arborescence.wordBound`: polynomial bound
  `4 * (n + 1) * M₀ + 32 * (n + 1) ^ 2` on word values and workspace addresses.
* `Cslib.Algorithms.WordRAM.Arborescence.flattenBoolMatrix`,
  `Cslib.Algorithms.WordRAM.Arborescence.flattenSignedMatrix`: row-major flat word-list encodings
  of Boolean adjacency and signed cost/weight matrices.
* `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput`,
  `Cslib.Algorithms.WordRAM.Arborescence.BranchingInput`: weighted digraph inputs on `Fin n` with
  intrinsic magnitude and word-value/address bounds, flat word encodings, and expected parent-list
  outputs.

## Main results

* `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedParentList_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedParentList_spec`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedOutParentList_eq_nil_iff`,
  `Cslib.Algorithms.WordRAM.Arborescence.ArborescenceInput.expectedOutParentList_spec`,
  `Cslib.Algorithms.WordRAM.Arborescence.BranchingInput.expectedParentList_spec`: correctness and
  optimality characterizations of the encoded parent-list outputs.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence

open Cslib.Algorithms.Lean.Arborescence
open Cslib.WordRAM

/-! ### Word-value and address bound -/

public section

/-- Polynomial bound on word values and workspace addresses covering the rooted, reversed min-cost
reduced exit costs up to `4 * (n + 1) * M₀` together with all `O(n²)` workspace addresses.
The condition `Fits w (wordBound n M₀)` means `wordBound n M₀ < 2 ^ w`, so a word width `w` of
order `log(n + 2) + log(M₀ + 2)` bits suffices. -/
@[expose] def wordBound (n M₀ : ℕ) : ℕ :=
  4 * (n + 1) * M₀ + 32 * (n + 1) ^ 2

end

public section

/-- Row-major `n × n` Boolean matrix flattened to `0`/`1` words. -/
@[expose] def flattenBoolMatrix (n : ℕ) (a : Fin n → Fin n → Bool) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => if a u v then 1 else 0

/-- Row-major `n × n` signed integer matrix flattened via `Signed.encode`. -/
@[expose] def flattenSignedMatrix (n : ℕ) (c : Fin n → Fin n → ℤ) : List ℕ :=
  (List.finRange n).flatMap fun u => (List.finRange n).map fun v => Signed.encode (c u v)

@[simp] theorem length_flattenBoolMatrix (n : ℕ) (a : Fin n → Fin n → Bool) :
    (flattenBoolMatrix n a).length = n * n := by
  unfold flattenBoolMatrix
  rw [List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

@[simp] theorem length_flattenSignedMatrix (n : ℕ) (c : Fin n → Fin n → ℤ) :
    (flattenSignedMatrix n c).length = n * n := by
  unfold flattenSignedMatrix
  rw [List.length_flatMap]
  simp [List.map_const', List.sum_replicate]

theorem getD_flattenBoolMatrix (n : ℕ) (a : Fin n → Fin n → Bool) (u v : Fin n) :
    (flattenBoolMatrix n a).getD (u.1 * n + v.1) 0 = if a u v then 1 else 0 := by
  simpa only [flattenBoolMatrix, ← List.ofFn_eq_map] using
    List.getD_flatMap_ofFn (fun x y => if a x y then 1 else 0) 0 u v

theorem getD_flattenSignedMatrix (n : ℕ) (c : Fin n → Fin n → ℤ) (u v : Fin n) :
    (flattenSignedMatrix n c).getD (u.1 * n + v.1) 0 = Signed.encode (c u v) := by
  simpa only [flattenSignedMatrix, ← List.ofFn_eq_map] using
    List.getD_flatMap_ofFn (fun x y => Signed.encode (c x y)) 0 u v

/-- Rooted weighted digraph input on `Fin n` for Word-RAM Chu–Liu/Edmonds solvers. -/
structure ArborescenceInput where
  /-- Number of vertices. -/
  n : ℕ
  /-- Designated root vertex. -/
  root : Fin n
  /-- Boolean adjacency matrix (`adj u v = true` iff arc `u → v` is present). -/
  adj : Fin n → Fin n → Bool
  /-- Signed integer arc costs. -/
  cost : Fin n → Fin n → ℤ

/-- Underlying `Digraph (Fin I.n)` of an `ArborescenceInput`. -/
@[expose] def ArborescenceInput.digraph (I : ArborescenceInput) : Digraph (Fin I.n) where
  Adj u v := I.adj u v = true

instance (I : ArborescenceInput) : DecidableRel I.digraph.Adj :=
  fun u v => inferInstanceAs (Decidable (I.adj u v = true))

/-- Maximum absolute arc cost `max_{u, v} |I.cost u v|`. -/
@[expose] def ArborescenceInput.maxAbsCost (I : ArborescenceInput) : ℕ :=
  Finset.univ.sup fun p : Fin I.n × Fin I.n => (I.cost p.1 p.2).natAbs

theorem ArborescenceInput.natAbs_cost_le_maxAbsCost (I : ArborescenceInput) (u v : Fin I.n) :
    (I.cost u v).natAbs ≤ I.maxAbsCost :=
  Finset.le_sup (f := fun p : Fin I.n × Fin I.n => (I.cost p.1 p.2).natAbs)
    (Finset.mem_univ (u, v))

/-- Intrinsic polynomial word-value/address bound `wordBound I.n I.maxAbsCost`
(`Fits w I.wordBound` means `I.wordBound < 2 ^ w`, so `w` of order
`log(I.n + 2) + log(I.maxAbsCost + 2)` bits suffices). -/
@[expose] def ArborescenceInput.wordBound (I : ArborescenceInput) : ℕ :=
  Arborescence.wordBound I.n I.maxAbsCost

/-- Flat Word-RAM input word list `[n, root] ++ flattenBoolMatrix ++ flattenSignedMatrix`. -/
@[expose] def ArborescenceInput.encode (I : ArborescenceInput) : List ℕ :=
  I.n :: I.root.1 :: (flattenBoolMatrix I.n I.adj ++ flattenSignedMatrix I.n I.cost)

/-- Expected list output for minimum-cost spanning in-arborescence (`[]` when infeasible, or the
length-`n` parent list `[p(0), …, p(n - 1)]` when `edmonds I.digraph I.cost I.root = some p`). -/
@[expose] def ArborescenceInput.expectedParentList (I : ArborescenceInput) : List ℕ :=
  match edmonds I.digraph I.cost I.root with
  | some p => (List.finRange I.n).map fun v => (p v).1
  | none => []

/-- `I.expectedParentList` is empty iff `I.digraph` has no spanning in-arborescence rooted at
`I.root`. -/
theorem ArborescenceInput.expectedParentList_eq_nil_iff (I : ArborescenceInput) :
    I.expectedParentList = [] ↔ ∀ t, ¬ IsInArborescenceParent I.digraph.Adj I.root t := by
  unfold ArborescenceInput.expectedParentList
  cases h : edmonds I.digraph I.cost I.root with
  | none =>
    simp only [true_iff]
    exact edmonds_eq_none_iff.mp h
  | some p =>
    have hne : ((List.finRange I.n).map fun v => (p v).1) ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp only [List.length_map, List.length_finRange, List.length_nil] at hlen
      exact Nat.ne_of_gt I.root.pos hlen
    refine ⟨fun hnil => absurd hnil hne, fun hall => ?_⟩
    exact absurd (edmonds_spec.1 p h).1 (hall p)

/-- Whenever `I.expectedParentList` is nonempty, it encodes the parent map of a minimum-cost
spanning in-arborescence of `I.digraph` rooted at `I.root`. -/
theorem ArborescenceInput.expectedParentList_spec (I : ArborescenceInput)
    (hne : I.expectedParentList ≠ []) :
    ∃ p : Fin I.n → Fin I.n,
      I.expectedParentList = (List.finRange I.n).map (fun v => (p v).1) ∧
      (Digraph.parentDigraph I.root p).IsInArborescence I.root ∧
      Digraph.parentDigraph I.root p ≤ I.digraph ∧
      ∀ (T : Digraph (Fin I.n)) [DecidableRel T.Adj],
        T.IsInArborescence I.root → T ≤ I.digraph →
        arcCost (Digraph.parentDigraph I.root p) I.cost ≤ arcCost T I.cost := by
  unfold ArborescenceInput.expectedParentList at hne ⊢
  cases h : edmonds I.digraph I.cost I.root with
  | none => simp [h] at hne
  | some p =>
    obtain ⟨h1, h2, h3⟩ := edmonds_optimal h
    refine ⟨p, rfl, h1, h2, fun T _ hT hTG => ?_⟩
    convert h3 T hT hTG

/-- Expected list output for minimum-cost spanning out-arborescence (`[]` when infeasible, or the
length-`n` parent list `[p(0), …, p(n - 1)]` when `edmondsOut I.digraph I.cost I.root = some p`). -/
@[expose] def ArborescenceInput.expectedOutParentList (I : ArborescenceInput) : List ℕ :=
  match edmondsOut I.digraph I.cost I.root with
  | some p => (List.finRange I.n).map fun v => (p v).1
  | none => []

/-- `I.expectedOutParentList` is empty iff `I.digraph` has no spanning out-arborescence rooted at
`I.root`. -/
theorem ArborescenceInput.expectedOutParentList_eq_nil_iff (I : ArborescenceInput) :
    I.expectedOutParentList = [] ↔
      ∀ t, ¬ IsInArborescenceParent (fun u w => I.digraph.Adj w u) I.root t := by
  unfold ArborescenceInput.expectedOutParentList
  cases h : edmondsOut I.digraph I.cost I.root with
  | none =>
    simp only [true_iff]
    exact edmondsOut_spec.2 h
  | some p =>
    have hne : ((List.finRange I.n).map fun v => (p v).1) ≠ [] := by
      intro hnil
      have hlen := congrArg List.length hnil
      simp only [List.length_map, List.length_finRange, List.length_nil] at hlen
      exact Nat.ne_of_gt I.root.pos hlen
    refine ⟨fun hnil => absurd hnil hne, fun hall => ?_⟩
    exact absurd (edmondsOut_spec.1 p h).1 (hall p)

/-- Whenever `I.expectedOutParentList` is nonempty, it encodes the parent map of a minimum-cost
spanning out-arborescence of `I.digraph` rooted at `I.root`. -/
theorem ArborescenceInput.expectedOutParentList_spec (I : ArborescenceInput)
    (hne : I.expectedOutParentList ≠ []) :
    ∃ p : Fin I.n → Fin I.n,
      I.expectedOutParentList = (List.finRange I.n).map (fun v => (p v).1) ∧
      IsInArborescenceParent (fun u w => I.digraph.Adj w u) I.root p ∧
      ∀ t, IsInArborescenceParent (fun u w => I.digraph.Adj w u) I.root t →
        parentCost (fun u w => I.cost w u) I.root p ≤
          parentCost (fun u w => I.cost w u) I.root t := by
  unfold ArborescenceInput.expectedOutParentList at hne ⊢
  cases h : edmondsOut I.digraph I.cost I.root with
  | none => simp [h] at hne
  | some p =>
    obtain ⟨h1, h2⟩ := edmondsOut_spec.1 p h
    refine ⟨p, rfl, h1, fun t ht => ?_⟩
    convert h2 t ht

/-- Weighted digraph input on `Fin n` for Word-RAM maximum-weight branching. -/
structure BranchingInput where
  /-- Number of vertices. -/
  n : ℕ
  /-- Boolean adjacency matrix (`adj u v = true` iff arc `u → v` is present). -/
  adj : Fin n → Fin n → Bool
  /-- Signed integer arc weights. -/
  weight : Fin n → Fin n → ℤ

/-- Underlying `Digraph (Fin I.n)` of a `BranchingInput`. -/
@[expose] def BranchingInput.digraph (I : BranchingInput) : Digraph (Fin I.n) where
  Adj u v := I.adj u v = true

instance (I : BranchingInput) : DecidableRel I.digraph.Adj :=
  fun u v => inferInstanceAs (Decidable (I.adj u v = true))

/-- Maximum absolute arc weight `max_{u, v} |I.weight u v|` (`0` when `n = 0`). -/
@[expose] def BranchingInput.maxAbsWeight (I : BranchingInput) : ℕ :=
  Finset.univ.sup fun p : Fin I.n × Fin I.n => (I.weight p.1 p.2).natAbs

theorem BranchingInput.natAbs_weight_le_maxAbsWeight (I : BranchingInput) (u v : Fin I.n) :
    (I.weight u v).natAbs ≤ I.maxAbsWeight :=
  Finset.le_sup (f := fun p : Fin I.n × Fin I.n => (I.weight p.1 p.2).natAbs)
    (Finset.mem_univ (u, v))

/-- Intrinsic polynomial word-value/address bound `wordBound (I.n + 1) I.maxAbsWeight`
(`Fits w I.wordBound` means `I.wordBound < 2 ^ w`, so `w` of order
`log(I.n + 2) + log(I.maxAbsWeight + 2)` bits suffices). -/
@[expose] def BranchingInput.wordBound (I : BranchingInput) : ℕ :=
  Arborescence.wordBound (I.n + 1) I.maxAbsWeight

/-- Flat Word-RAM input word list `[n] ++ flattenBoolMatrix ++ flattenSignedMatrix`. -/
@[expose] def BranchingInput.encode (I : BranchingInput) : List ℕ :=
  I.n :: (flattenBoolMatrix I.n I.adj ++ flattenSignedMatrix I.n I.weight)

/-- Expected length-`n` parent list `[p(0), …, p(n - 1)]` of `optimumBranchingParent`. -/
@[expose] def BranchingInput.expectedParentList (I : BranchingInput) : List ℕ :=
  (List.finRange I.n).map fun v => (optimumBranchingParent I.digraph I.weight v).1

/-- `I.expectedParentList` encodes `optimumBranchingParent I.digraph I.weight`, whose branching
digraph `optimumBranching I.digraph I.weight` is a maximum-weight branching of `I.digraph`. -/
theorem BranchingInput.expectedParentList_spec (I : BranchingInput) :
    I.expectedParentList =
      (List.finRange I.n).map (fun v => (optimumBranchingParent I.digraph I.weight v).1) ∧
    (optimumBranching I.digraph I.weight).IsBranching ∧
    optimumBranching I.digraph I.weight ≤ I.digraph ∧
    ∀ (B : Digraph (Fin I.n)) [DecidableRel B.Adj],
      B.IsBranching → B ≤ I.digraph →
      arcCost B I.weight ≤ arcCost (optimumBranching I.digraph I.weight) I.weight := by
  obtain ⟨h1, h2, h3⟩ := optimumBranching_spec I.digraph I.weight
  refine ⟨rfl, h1, h2, fun B _ hB hBG => ?_⟩
  convert h3 B hB hBG

end

end Cslib.Algorithms.WordRAM.Arborescence
