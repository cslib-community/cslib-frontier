/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.EditDistance.Hirschberg
public import Mathlib.Data.List.Infix
import Mathlib.Tactic.Linarith

/-!
# Row footprints of Hirschberg reconstruction

The same `hirschbergFold` that constructs the script counts grid entries and column visits on
the subproblems actually selected by `bestSplit`. At a split, each suffix of each source half
produces one score row. Four more passes visit the columns: reversing the forward row, adding the
rows pointwise, indexing the sums and selecting the least score. An empty side uses a single pass
over the other side. The singleton scan has one state per target suffix, including the empty one.

The row workspace is the capacity of a sequential schedule in logical list entries. Compute the
forward row with two rolling rows, reverse it, and retain the result while computing the backward
row with two rolling rows. The pointwise addition can hold both input rows and the sum row.
Indexing the sums uses two lists and the minimum scan uses the indexed list. Only the selected
column is needed by either recursive child. Input slices and their reversals, script cells,
scalar accumulators and the call stack are outside this row measure. The theorems count neither
machine instructions nor bytes of the Lean runtime.
-/

public section

namespace Cslib.Algorithms.Lean.EditDistance

variable {α : Type*}

/-- Entries visited in grid and column scans, and the workspace of the rolling-row schedule. -/
structure HirschbergProfile where
  /-- Sum of produced grid entries, column positions in the four split scans, and leaf visits. -/
  visits : ℕ
  /-- Largest simultaneous capacity of the schedule's score and indexed-score row buffers. -/
  rowSpace : ℕ
  deriving Repr, DecidableEq

/-- Local split footprint, including the initial row and boundary column in each rectangle. -/
def HirschbergProfile.split (left right y : List α) : HirschbergProfile :=
  let width := y.length + 1
  ⟨(left.length + 1) * width + (right.length + 1) * width + 4 * width, 3 * width⟩

/-- The rectangle and scan counts equal lengths of the rows and lists visited by the split.
The suffix lists on the right describe row production without materializing a table in the
alignment algorithm. -/
theorem HirschbergProfile.split_visits (C : Costs α) (left right y : List α) :
    let D := wagnerFischer C
    let forward := (D.row y.reverse left.reverse).reverse
    let scores := splitCosts C left right y
    (split left right y).visits =
      (left.reverse.tails.map fun s => (D.row y.reverse s).length).sum +
      (right.tails.map fun s => (D.row y s).length).sum +
      forward.length + scores.length + scores.length + scores.zipIdx.length := by
  simp [split]
  omega

/-- Three complete row buffers suffice for a saved forward row plus successive backward rows,
and for forward and backward rows plus their pointwise sums. An indexed score still occupies
one list entry. -/
theorem HirschbergProfile.split_rowSpace (C : Costs α) (left right y : List α)
    (a : α) (s : List α) :
    let D := wagnerFischer C
    let forward := (D.row y.reverse left.reverse).reverse
    let scores := splitCosts C left right y
    (split left right y).rowSpace =
      forward.length + (D.row y s).length + (D.row y (a :: s)).length ∧
    (split left right y).rowSpace = forward.length + (D.row y right).length + scores.length ∧
    scores.length + scores.zipIdx.length ≤ (split left right y).rowSpace := by
  simp [split]
  omega

private def profilesOn (C : Costs α) : List α → List α → HirschbergProfile :=
  hirschbergFold C (fun y => ⟨y.length, 0⟩) (fun x => ⟨x.length, 0⟩)
    (fun _ y => ⟨y.length + 1, 0⟩) fun left right y _ p q =>
      let localRows := HirschbergProfile.split left right y
      ⟨localRows.visits + p.visits + q.visits, max localRows.rowSpace (max p.rowSpace q.rowSpace)⟩

/-- Counts on the actual Hirschberg subproblems, with the shorter word placed across the rows
and the costs transposed when the input words are interchanged. -/
def hirschbergProfile (C : Costs α) (x y : List α) : HirschbergProfile :=
  if y.length ≤ x.length then profilesOn C x y else profilesOn C.transpose y x

-- The source halves have lengths a and b with a ≤ b ≤ a + 1. The children's rectangles omit
-- at least a full a-by-(i+j) rectangle. It covers the parent's rectangles and four column scans.
private theorem split_area {a b i j : ℕ} (ha : 0 < a) (hab : a ≤ b) (hba : b ≤ a + 1)
    (hy : 0 < i + j) :
    (a + b + 6) * (i + j + 1) + 18 * a * i + 18 * b * j ≤ 18 * (a + b) * (i + j) := by
  have hw : a + b + 6 ≤ 9 * a := by omega
  have hh : i + j + 1 ≤ 2 * (i + j) := by omega
  have hmul := Nat.mul_le_mul hw hh
  have hcross := Nat.mul_le_mul_right i hab
  nlinarith

private theorem profilesOn_bounds (C : Costs α) (x y : List α) :
    (profilesOn C x y).visits ≤ 18 * x.length * y.length + x.length + y.length ∧
    (profilesOn C x y).rowSpace ≤ 3 * (y.length + 1) := by
  match x, y with
  | [], y => simp [profilesOn, hirschbergFold]
  | a :: xs, [] => simp [profilesOn, hirschbergFold]
  | [a], c :: cs => simp [profilesOn, hirschbergFold]; omega
  | a :: b :: xs, c :: cs =>
    let x := a :: b :: xs
    let y := c :: cs
    let left := x.take (x.length / 2)
    let right := x.drop (x.length / 2)
    let k := bestSplit C left right y
    obtain ⟨lv, ls⟩ := profilesOn_bounds C left (y.take k)
    obtain ⟨rv, rs⟩ := profilesOn_bounds C right (y.drop k)
    have hx : left.length + right.length = x.length := by
      simp only [left, right, ← List.length_append, List.take_append_drop]
    have hy : (y.take k).length + (y.drop k).length = y.length := by
      rw [← List.length_append, List.take_append_drop]
    have aLen : left.length = x.length / 2 := by simp [left, Nat.div_le_self]
    have bLen : right.length = x.length - x.length / 2 := by simp [right]
    have two : 2 ≤ x.length := by simp [x]
    have positive : 0 < y.length := by simp [y]
    have area := split_area (a := left.length) (b := right.length)
      (i := (y.take k).length) (j := (y.drop k).length)
      (by omega) (by omega) (by omega) (by omega)
    rw [hx, hy] at area
    have here : profilesOn C x y =
        ⟨(HirschbergProfile.split left right y).visits +
          (profilesOn C left (y.take k)).visits + (profilesOn C right (y.drop k)).visits,
         max (HirschbergProfile.split left right y).rowSpace
           (max (profilesOn C left (y.take k)).rowSpace
             (profilesOn C right (y.drop k)).rowSpace)⟩ := by
      simp only [profilesOn, k, left, right, x, y, hirschbergFold]
    change (profilesOn C x y).visits ≤ _ ∧ (profilesOn C x y).rowSpace ≤ _
    rw [here]
    change _ ≤ 18 * x.length * y.length + x.length + y.length ∧ _ ≤ 3 * (y.length + 1)
    simp only [HirschbergProfile.split, max_le_iff]
    constructor
    · nlinarith
    · omega
termination_by x.length
decreasing_by
  all_goals simp [*]
  omega

/-- On arbitrary words the visited entries are quadratic with linear boundary terms, and the
sequential schedule needs at most three rows of the shorter word's width. -/
theorem hirschbergProfile_bounds (C : Costs α) (x y : List α) :
    (hirschbergProfile C x y).visits ≤ 18 * x.length * y.length + x.length + y.length ∧
    (hirschbergProfile C x y).rowSpace ≤ 3 * (min x.length y.length + 1) := by
  unfold hirschbergProfile
  split <;> rename_i h
  · simpa [Nat.min_eq_right h] using profilesOn_bounds C x y
  · simpa [Nat.min_eq_left (by omega : x.length ≤ y.length), Nat.mul_right_comm,
      Nat.add_right_comm] using profilesOn_bounds C.transpose y x

/-- For nonempty input words the two boundary terms are absorbed by the rectangle. -/
theorem hirschbergProfile_visits_le (C : Costs α) {x y : List α} (hx : x ≠ []) (hy : y ≠ []) :
    (hirschbergProfile C x y).visits ≤ 20 * x.length * y.length := by
  have ⟨hv, _⟩ := hirschbergProfile_bounds C x y
  have hx' : 1 ≤ x.length := List.length_pos_iff.mpr hx
  have hy' : 1 ≤ y.length := List.length_pos_iff.mpr hy
  have hxmul := Nat.mul_le_mul_left x.length hy'
  have hymul := Nat.mul_le_mul_right y.length hx'
  nlinarith

end Cslib.Algorithms.Lean.EditDistance
