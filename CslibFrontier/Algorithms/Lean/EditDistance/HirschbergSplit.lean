/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.Basic
public import Mathlib.Data.List.MinMax
import CslibFrontier.Foundations.Data.List.ArgMin

/-!
# Choosing a split column for edit-script reconstruction

Split the source into `left ++ right`. A forward row gives the distance from the left half
to every target prefix, and a backward row gives the distance from the right half to every
target suffix. Adding corresponding entries and selecting the first minimum finds a target
column where two independently optimal alignments concatenate to a whole optimal alignment.

The suffix-indexed grid computes the prefix scores on reversed words. Reversing the order of
a script leaves the cost of each operation unchanged, so asymmetric letter costs are allowed.
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

variable {α : Type*} (C : Costs α)

open EditScript

private theorem reverse_script (s : EditScript α) :
    src s.reverse = s.src.reverse ∧ tgt s.reverse = s.tgt.reverse ∧
      cost C s.reverse = s.cost C := by
  induction s with
  | nil => simp
  | cons o s ih =>
    obtain ⟨hs, ht, hc⟩ := ih
    cases o <;> simp [List.reverse_cons, src_append, tgt_append, cost_append,
      EditOp.src, EditOp.tgt, hs, ht, hc, Nat.add_comm]

/-- Reversing both words preserves their weighted edit distance. Each reversed script has the
same operations in reverse order, with the same individual costs. -/
theorem editDist_reverse (x y : List α) : editDist C x.reverse y.reverse = editDist C x y := by
  suffices le : ∀ u v : List α, editDist C u.reverse v.reverse ≤ editDist C u v by
    exact Nat.le_antisymm (le x y) (by simpa using le x.reverse y.reverse)
  intro u v
  obtain ⟨hs, ht, hc⟩ := reverse_script C (optScript C u v)
  simpa only [hs, ht, hc, src_optScript, tgt_optScript, cost_optScript] using
    editDist_le_cost C (optScript C u v).reverse

private theorem src_eq_filterMap (s : EditScript α) :
    s.src = s.filterMap (fun o => o.src.head?) := by
  induction s with
  | nil => simp
  | cons o s ih => cases o <;> simp [List.filterMap_cons, EditOp.src, ih]

/-- Cutting the source at a chosen boundary cuts an optimal script at a target column. -/
private theorem exists_split (l r y : List α) :
    ∃ k ≤ y.length, editDist C l (y.take k) + editDist C r (y.drop k) ≤ editDist C (l ++ r) y := by
  let s := optScript C (l ++ r) y
  have hs : s.filterMap (fun o => o.src.head?) = l ++ r := by
    rw [← src_eq_filterMap, src_optScript]
  obtain ⟨p, q, hpq, hp, hq⟩ := List.filterMap_eq_append_iff.mp hs
  rw [← src_eq_filterMap] at hp hq
  have hy : tgt p ++ tgt q = y := by rw [← tgt_append, ← hpq, tgt_optScript]
  have hcost : cost C p + cost C q = editDist C (l ++ r) y := by
    rw [← cost_append, ← hpq, cost_optScript]
  refine ⟨(tgt p).length, by simp [← hy], ?_⟩
  rw [← hcost, ← hy, List.take_left, List.drop_left, ← hp, ← hq]
  exact Nat.add_le_add (editDist_le_cost C p) (editDist_le_cost C q)

/-- Concatenating two optimal scripts bounds the cost of the whole alignment. -/
theorem editDist_append_le (x₁ x₂ y₁ y₂ : List α) :
    editDist C (x₁ ++ x₂) (y₁ ++ y₂) ≤ editDist C x₁ y₁ + editDist C x₂ y₂ := by
  simpa only [src_append, tgt_append, cost_append, src_optScript, tgt_optScript, cost_optScript]
    using editDist_le_cost C (optScript C x₁ y₁ ++ optScript C x₂ y₂)

/-- The sum of the forward and backward scores at every possible split column, in order. -/
@[expose] def splitCosts (left right y : List α) : List ℕ :=
  let D := wagnerFischer C
  List.zipWith (· + ·) (D.row y.reverse left.reverse).reverse (D.row y right)

@[simp] theorem length_splitCosts (left right y : List α) :
    (splitCosts C left right y).length = y.length + 1 := by
  simp [splitCosts]

/-- Column `k` records the cost of cutting the target just before index `k`. -/
theorem getElem_splitCosts (left right y : List α) (k : ℕ)
    (hk : k < (splitCosts C left right y).length) :
    (splitCosts C left right y)[k] = editDist C left (y.take k) + editDist C right (y.drop k) := by
  have hle : k ≤ y.length := by rw [length_splitCosts] at hk; omega
  simp only [splitCosts, List.getElem_zipWith, List.getElem_reverse, GridDP.getElem_row,
    GridDP.length_row, List.length_reverse, Nat.add_sub_cancel, List.drop_reverse]
  rw [show y.length - (y.length - k) = k by omega]
  exact congrArg (· + editDist C right (y.drop k)) (editDist_reverse C left (y.take k))

/-- The least-cost split column for `left ++ right` against `y`, taking the first minimum.
Each half contributes one score row, and the final scan compares their pointwise sums. -/
@[expose] def bestSplit (left right y : List α) : ℕ :=
  (((splitCosts C left right y).zipIdx.argmin Prod.fst).getD (0, 0)).2

private theorem bestSplit_min (left right y : List α) :
    let k := bestSplit C left right y
    k ≤ y.length ∧ ∀ j ≤ y.length,
      editDist C left (y.take k) + editDist C right (y.drop k) ≤
        editDist C left (y.take j) + editDist C right (y.drop j) := by
  let scores := splitCosts C left right y
  let best := (scores.zipIdx.argmin Prod.fst).getD (0, 0)
  have hlen : scores.length = y.length + 1 := length_splitCosts ..
  have hne : scores.zipIdx ≠ [] := by
    intro h
    have := congrArg List.length h
    simp [hlen] at this
  have hmem : best ∈ scores.zipIdx := List.getD_argmin_mem hne _
  have hbound := List.snd_lt_of_mem_zipIdx hmem
  have hscore : best.1 = scores[best.2] := List.fst_eq_of_mem_zipIdx hmem
  change best.2 ≤ y.length ∧ _
  refine ⟨by omega, ?_⟩
  intro j hj
  have hj' : j < scores.length := by omega
  have hmem' : (scores[j], j) ∈ scores.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hj')
  have hle : best.1 ≤ scores[j] := List.getD_argmin_le (f := Prod.fst) hmem' (0, 0)
  rw [hscore] at hle
  exact (getElem_splitCosts C left right y best.2 (by omega)) ▸
    (getElem_splitCosts C left right y j hj') ▸ hle

/-- The selected split column lies between the two ends of the target, inclusive. -/
theorem bestSplit_le_length (left right y : List α) : bestSplit C left right y ≤ y.length :=
  (bestSplit_min C left right y).1

/-- An optimal alignment through the selected column has the whole edit distance as its cost. -/
theorem bestSplit_spec (left right y : List α) :
    let k := bestSplit C left right y
    editDist C left (y.take k) + editDist C right (y.drop k) = editDist C (left ++ right) y := by
  let k := bestSplit C left right y
  obtain ⟨j, hj, h⟩ := exists_split C left right y
  refine Nat.le_antisymm (((bestSplit_min C left right y).2 j hj).trans h) ?_
  simpa only [List.take_append_drop] using editDist_append_le C left right (y.take k) (y.drop k)

end Cslib.Algorithms.Lean.EditDistance
