/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fin.Basic
public import Mathlib.Order.Monotone.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.OfFn

/-!
# Ordered orthogonal routing

Ordered rows of ports can be connected by disjoint orthogonal paths on the integer grid.
For rightward routes, the rightmost path bends first; for leftward routes, the leftmost bends
first. Routing through a sufficiently distant intermediate row handles arbitrary ordered rows.

## Main definitions

* `Cslib.Complexity.NCL.GridRouting.Elbow`: a vertical-horizontal-vertical grid path.
* `Cslib.Complexity.NCL.GridRouting.OrderedRouting`: disjoint paths between two ordered rows.

## Main results

* `Cslib.Complexity.NCL.GridRouting.route`: an explicit routing of any two increasing rows.
-/

public section

namespace Cslib.Complexity.NCL.GridRouting

/-- A nonnegative lattice point, the Cartesian product of its two coordinate axes. -/
abbrev Point := ℕ × ℕ

/-- A path consisting of two vertical segments joined by a horizontal segment. -/
structure Elbow where
  /-- The column at its top endpoint. -/
  source : ℕ
  /-- The column at its bottom endpoint. -/
  target : ℕ
  /-- The row of the horizontal segment. -/
  bend : ℕ
  /-- The row of the bottom endpoint. -/
  height : ℕ
  /-- The horizontal segment lies below the top row. -/
  bend_pos : 0 < bend
  /-- The horizontal segment lies above the bottom row. -/
  bend_lt : bend < height

/-- The grid points occupied by the three segments, including their endpoints. -/
@[expose] def Elbow.Contains (r : Elbow) (p : Point) : Prop :=
  (p.1 = r.source ∧ p.2 ≤ r.bend) ∨
    (p.2 = r.bend ∧ min r.source r.target ≤ p.1 ∧ p.1 ≤ max r.source r.target) ∨
    (p.1 = r.target ∧ r.bend ≤ p.2 ∧ p.2 ≤ r.height)

/-- Every occupied row lies inside the routing band. -/
theorem Elbow.row_le (r : Elbow) {p : Point} (hp : r.Contains p) : p.2 ≤ r.height := by
  rcases hp with h | h | h <;> have := r.bend_lt.le <;> omega

/-- The top endpoint belongs to the path. -/
theorem Elbow.source_mem (r : Elbow) : r.Contains (r.source, 0) :=
  Or.inl ⟨rfl, Nat.zero_le _⟩

/-- The bottom endpoint belongs to the path. -/
theorem Elbow.target_mem (r : Elbow) : r.Contains (r.target, r.height) :=
  Or.inr (Or.inr ⟨rfl, r.bend_lt.le, le_rfl⟩)

/-- Only the source lies on the top row. -/
theorem Elbow.top_iff (r : Elbow) (x : ℕ) : r.Contains (x, 0) ↔ x = r.source := by
  have := r.bend_pos
  simp only [Elbow.Contains]
  omega

/-- Only the target lies on the bottom row. -/
theorem Elbow.bottom_iff (r : Elbow) (x : ℕ) :
    r.Contains (x, r.height) ↔ x = r.target := by
  have := r.bend_lt
  simp only [Elbow.Contains]
  omega

private theorem disjoint_right (r s : Elbow) (hsource : r.source < s.source)
    (htarget : r.target < s.target) (hr : r.source ≤ r.target)
    (hs : s.source ≤ s.target) (hbend : s.bend < r.bend) :
    ∀ p, ¬(r.Contains p ∧ s.Contains p) := by
  rintro p ⟨hrp, hsp⟩
  simp only [Elbow.Contains, Nat.min_eq_left hr, Nat.max_eq_right hr,
    Nat.min_eq_left hs, Nat.max_eq_right hs] at hrp hsp
  rcases hrp with h | h | h <;> rcases hsp with h' | h' | h' <;> omega

private theorem disjoint_left (r s : Elbow) (hsource : r.source < s.source)
    (htarget : r.target < s.target) (hr : r.target ≤ r.source)
    (hs : s.target ≤ s.source) (hbend : r.bend < s.bend) :
    ∀ p, ¬(r.Contains p ∧ s.Contains p) := by
  rintro p ⟨hrp, hsp⟩
  simp only [Elbow.Contains, Nat.min_eq_right hr, Nat.max_eq_left hr,
    Nat.min_eq_right hs, Nat.max_eq_left hs] at hrp hsp
  rcases hrp with h | h | h <;> rcases hsp with h' | h' | h' <;> omega

/-- Two routing bands joined at their intermediate row. -/
structure OrderedRouting {n : ℕ} (source target : Fin n → ℕ) where
  /-- The first band routes rightward. -/
  upper : Fin n → Elbow
  /-- The second band routes leftward. -/
  lower : Fin n → Elbow
  /-- The upper band starts at the specified ports. -/
  source_eq (i) : (upper i).source = source i
  /-- The lower band ends at the specified ports. -/
  target_eq (i) : (lower i).target = target i
  /-- The bands meet at their intermediate ports. -/
  join_eq (i) : (upper i).target = (lower i).source
  /-- Both bands have the same height. -/
  upper_height (i) : (upper i).height = n + 1
  /-- Both bands have the same height. -/
  lower_height (i) : (lower i).height = n + 1
  /-- The upper paths are pairwise disjoint. -/
  upper_disjoint {i j} : i ≠ j → ∀ p, ¬((upper i).Contains p ∧ (upper j).Contains p)
  /-- The lower paths are pairwise disjoint. -/
  lower_disjoint {i j} : i ≠ j → ∀ p, ¬((lower i).Contains p ∧ (lower j).Contains p)

/-- The trace after placing the lower band immediately below the upper band. -/
@[expose] def OrderedRouting.Contains {n : ℕ} {source target : Fin n → ℕ}
    (r : OrderedRouting source target) (i : Fin n) (p : Point) : Prop :=
  (r.upper i).Contains p ∨
    (n + 1 ≤ p.2 ∧ (r.lower i).Contains (p.1, p.2 - (n + 1)))

/-- The whole path meets the first row at its source port. -/
theorem OrderedRouting.top_iff {n : ℕ} {source target : Fin n → ℕ}
    (r : OrderedRouting source target) (i : Fin n) (x : ℕ) :
    r.Contains i (x, 0) ↔ x = source i := by
  simp [OrderedRouting.Contains, Elbow.top_iff, r.source_eq]

/-- The whole path meets its last row at its target port. -/
theorem OrderedRouting.bottom_iff {n : ℕ} {source target : Fin n → ℕ}
    (r : OrderedRouting source target) (i : Fin n) (x : ℕ) :
    r.Contains i (x, 2 * (n + 1)) ↔ x = target i := by
  have hrow : ¬(r.upper i).Contains (x, 2 * (n + 1)) := fun hp => by
    have := r.upper_height i ▸ (r.upper i).row_le hp
    omega
  simp only [Contains, hrow, false_or]
  rw [show 2 * (n + 1) - (n + 1) = n + 1 by omega, ← r.lower_height i,
    Elbow.bottom_iff, r.target_eq]
  omega

/-- All path points lie between its endpoint rows. -/
theorem OrderedRouting.row_le {n : ℕ} {source target : Fin n → ℕ}
    (r : OrderedRouting source target) (i : Fin n) {p : Point} (hp : r.Contains i p) :
    p.2 ≤ 2 * (n + 1) := by
  rcases hp with hp | ⟨hy, hp⟩
  · have := (r.upper i).row_le hp
    rw [r.upper_height] at this
    omega
  · have := (r.lower i).row_le hp
    rw [r.lower_height] at this
    omega

private theorem OrderedRouting.upper_lower_disjoint {n : ℕ} {source target : Fin n → ℕ}
    (r : OrderedRouting source target) {i j : Fin n} (hij : i ≠ j) (p : Point)
    (hi : (r.upper i).Contains p)
    (hj : n + 1 ≤ p.2 ∧ (r.lower j).Contains (p.1, p.2 - (n + 1))) : False := by
  have hy := (r.upper i).row_le hi
  rw [r.upper_height] at hy
  have heq : p.2 = n + 1 := by omega
  have hj' : p.1 = (r.lower j).source := by
    simpa only [heq, Nat.sub_self, Elbow.top_iff] using hj.2
  have hu : (r.upper j).Contains p := by
    rw [← r.join_eq] at hj'
    cases p with
    | mk x y =>
      simp only at heq hj' ⊢
      subst y
      rw [← r.upper_height j, hj']
      exact (r.upper j).target_mem
  exact r.upper_disjoint hij p ⟨hi, hu⟩

/-- The joined routes remain pairwise disjoint, including at the joining row. -/
theorem OrderedRouting.disjoint {n : ℕ} {source target : Fin n → ℕ}
    (r : OrderedRouting source target) {i j : Fin n} (hij : i ≠ j) (p : Point) :
    ¬(r.Contains i p ∧ r.Contains j p) := by
  rintro ⟨hi, hj⟩
  rcases hi with hi | ⟨hiy, hi⟩ <;> rcases hj with hj | ⟨hjy, hj⟩
  · exact r.upper_disjoint hij p ⟨hi, hj⟩
  · exact r.upper_lower_disjoint hij p hi ⟨hjy, hj⟩
  · exact r.upper_lower_disjoint hij.symm p hj ⟨hiy, hi⟩
  · exact r.lower_disjoint hij (p.1, p.2 - (n + 1)) ⟨hi, hj⟩

/-- The sum of all endpoint columns, a bound for every endpoint. -/
private def portBound {n : ℕ} (source target : Fin n → ℕ) : ℕ :=
  (List.ofFn source ++ List.ofFn target).sum

private theorem source_le_portBound {n : ℕ} (source target : Fin n → ℕ) (i : Fin n) :
    source i ≤ portBound source target := by
  exact (List.le_sum_of_mem (show source i ∈ List.ofFn source from
    List.mem_ofFn.mpr ⟨i, rfl⟩)).trans (by simp [portBound])

private theorem target_le_portBound {n : ℕ} (source target : Fin n → ℕ) (i : Fin n) :
    target i ≤ portBound source target := by
  exact (List.le_sum_of_mem (show target i ∈ List.ofFn target from
    List.mem_ofFn.mpr ⟨i, rfl⟩)).trans (by simp [portBound])

/-- Connect two ordered rows by disjoint orthogonal routes, with total height `2 * (n + 1)`.
The intermediate columns lie to the right of all the specified ports. -/
def route {n : ℕ} (source target : Fin n → ℕ) (hs : StrictMono source)
    (ht : StrictMono target) : OrderedRouting source target where
  upper i := ⟨source i, portBound source target + i + 1, n - i, n + 1,
    by have := i.isLt; omega, by omega⟩
  lower i := ⟨portBound source target + i + 1, target i, i + 1, n + 1,
    by omega, by have := i.isLt; omega⟩
  source_eq _ := rfl
  target_eq _ := rfl
  join_eq _ := rfl
  upper_height _ := rfl
  lower_height _ := rfl
  upper_disjoint := by
    intro i j hij p hp
    rcases lt_or_gt_of_ne hij with h | h
    · exact disjoint_right _ _ (hs h) (by simp only; omega)
        (by have := source_le_portBound source target i; simp only; omega)
        (by have := source_le_portBound source target j; simp only; omega)
        (by have := i.isLt; have := j.isLt; simp only; omega) p hp
    · exact disjoint_right _ _ (hs h) (by simp only; omega)
        (by have := source_le_portBound source target j; simp only; omega)
        (by have := source_le_portBound source target i; simp only; omega)
        (by have := i.isLt; have := j.isLt; simp only; omega) p ⟨hp.2, hp.1⟩
  lower_disjoint := by
    intro i j hij p hp
    rcases lt_or_gt_of_ne hij with h | h
    · exact disjoint_left _ _ (by simp only; omega) (ht h)
        (by have := target_le_portBound source target i; simp only; omega)
        (by have := target_le_portBound source target j; simp only; omega)
        (by simp only; omega) p hp
    · exact disjoint_left _ _ (by simp only; omega) (ht h)
        (by have := target_le_portBound source target j; simp only; omega)
        (by have := target_le_portBound source target i; simp only; omega)
        (by simp only; omega) p ⟨hp.2, hp.1⟩

end Cslib.Complexity.NCL.GridRouting
