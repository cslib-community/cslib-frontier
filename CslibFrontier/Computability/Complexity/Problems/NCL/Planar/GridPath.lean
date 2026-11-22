/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridRouting

/-!
# Integer orthogonal paths

Paths are finite concatenations of horizontal and downward vertical segments. Their traces
therefore describe actual orthogonal grid paths and are monotone in the vertical coordinate.

## Main definitions

* `Cslib.Complexity.NCL.GridRouting.Path`: finite orthogonal paths between specified endpoints.

## Main results

* `Cslib.Complexity.NCL.GridRouting.Path.row_bounds`: every path stays between its endpoint rows.
* `Cslib.Complexity.NCL.GridRouting.Elbow.path_contains_iff`: the routing trace is an orthogonal
  path trace.
-/

public section

namespace Cslib.Complexity.NCL.GridRouting

/-- A finite orthogonal path that never goes upward. -/
inductive Path : Point → Point → Type
  /-- A horizontal segment, in either direction. -/
  | horizontal (x x' y : ℕ) : Path (x, y) (x', y)
  /-- A downward vertical segment. -/
  | vertical (x y y' : ℕ) (h : y ≤ y') : Path (x, y) (x, y')
  /-- Concatenate two paths at their shared endpoint. -/
  | comp {p q r : Point} : Path p q → Path q r → Path p r

/-- Grid points on a path. -/
@[expose] def Path.Contains {p q : Point} : Path p q → Point → Prop
  | .horizontal x x' y, u => u.2 = y ∧ min x x' ≤ u.1 ∧ u.1 ≤ max x x'
  | .vertical x y y' _, u => u.1 = x ∧ y ≤ u.2 ∧ u.2 ≤ y'
  | .comp r s, u => r.Contains u ∨ s.Contains u

/-- The initial endpoint belongs to its path. -/
theorem Path.source_mem {p q : Point} (r : Path p q) : r.Contains p := by
  induction r with
  | horizontal => simp [Contains]
  | vertical _ _ _ h => exact ⟨rfl, le_rfl, h⟩
  | comp _ _ ih _ => exact .inl ih

/-- The final endpoint belongs to its path. -/
theorem Path.target_mem {p q : Point} (r : Path p q) : r.Contains q := by
  induction r with
  | horizontal => exact ⟨rfl, min_le_right _ _, le_max_right _ _⟩
  | vertical _ _ _ h => exact ⟨rfl, h, le_rfl⟩
  | comp _ _ _ ih => exact .inr ih

/-- A path's starting row precedes its final row. -/
theorem Path.source_row_le {p q : Point} (r : Path p q) : p.2 ≤ q.2 := by
  induction r with
  | horizontal => exact le_rfl
  | vertical _ _ _ h => exact h
  | comp _ _ ih ih' => exact ih.trans ih'

/-- Every point of a path lies between its endpoint rows. -/
theorem Path.row_bounds {p q : Point} (r : Path p q) {u : Point} (hu : r.Contains u) :
    p.2 ≤ u.2 ∧ u.2 ≤ q.2 := by
  induction r with
  | horizontal => exact ⟨hu.1.ge, hu.1.le⟩
  | vertical => exact hu.2
  | comp r s ihr ihs =>
    rcases hu with hu | hu
    · exact ⟨(ihr hu).1, (ihr hu).2.trans s.source_row_le⟩
    · exact ⟨r.source_row_le.trans (ihs hu).1, (ihs hu).2⟩

/-- Translate both endpoints and all segments by a nonnegative integer vector. -/
@[expose] def Path.translate {p q : Point} (r : Path p q) (dx dy : ℕ) :
    Path (p.1 + dx, p.2 + dy) (q.1 + dx, q.2 + dy) :=
  match r with
  | .horizontal x x' y => .horizontal (x + dx) (x' + dx) (y + dy)
  | .vertical x y y' h => .vertical (x + dx) (y + dy) (y' + dy) (Nat.add_le_add_right h dy)
  | .comp r s => .comp (r.translate dx dy) (s.translate dx dy)

/-- Membership in a translated path, expressed at an arbitrary grid point. -/
theorem Path.contains_translate {p q : Point} (r : Path p q) (dx dy : ℕ) (u : Point) :
    (r.translate dx dy).Contains u ↔
      dx ≤ u.1 ∧ dy ≤ u.2 ∧ r.Contains (u.1 - dx, u.2 - dy) := by
  induction r with
  | horizontal => simp only [translate, Contains]; omega
  | vertical => simp only [translate, Contains]; omega
  | comp r s ihr ihs => simp only [translate, Contains, ihr, ihs]; tauto

/-- Change endpoint names using proven equalities. -/
@[expose]
def Path.cast {p q p' q' : Point} (r : Path p q) (hp : p = p') (hq : q = q') : Path p' q' :=
  hp ▸ hq ▸ r

/-- Endpoint casts preserve the trace. -/
theorem Path.contains_cast_iff {p q p' q' : Point} (r : Path p q)
    (hp : p = p') (hq : q = q') (u : Point) : (r.cast hp hq).Contains u ↔ r.Contains u := by
  cases hp
  cases hq
  rfl

/-- A routing elbow as an explicit three-segment path. -/
@[expose] def Elbow.path (r : Elbow) : Path (r.source, 0) (r.target, r.height) :=
  (Path.vertical r.source 0 r.bend (Nat.zero_le _)).comp
    ((Path.horizontal r.source r.target r.bend).comp
      (Path.vertical r.target r.bend r.height r.bend_lt.le))

/-- The three-segment path has precisely the elbow's declared trace. -/
theorem Elbow.path_contains_iff (r : Elbow) (p : Point) :
    r.path.Contains p ↔ r.Contains p := by
  simp only [path, Path.Contains, Contains]
  omega

/-- The two routing bands as a single finite orthogonal path. -/
@[expose] def OrderedRouting.path {n : ℕ} {source target : Fin n → ℕ}
    (r : OrderedRouting source target) (i : Fin n) :
    Path (source i, 0) (target i, 2 * (n + 1)) :=
  ((r.upper i).path.cast (by rw [r.source_eq]) (by rw [r.upper_height]) :
    Path (source i, 0) ((r.upper i).target, n + 1)).comp
    (((r.lower i).path.translate 0 (n + 1)).cast
      (by simp only [Nat.add_zero, Nat.zero_add, r.join_eq])
      (by simp only [r.target_eq, r.lower_height, Nat.add_zero]; congr 1; omega))

/-- The routing witness records the trace of the complete orthogonal path. -/
theorem OrderedRouting.path_contains_iff {n : ℕ} {source target : Fin n → ℕ}
    (r : OrderedRouting source target) (i : Fin n) (p : Point) :
    (r.path i).Contains p ↔ r.Contains i p := by
  simp only [path, Path.Contains, Path.contains_cast_iff, Path.contains_translate,
    Nat.zero_le, Nat.sub_zero, true_and, Elbow.path_contains_iff, OrderedRouting.Contains]

end Cslib.Complexity.NCL.GridRouting
