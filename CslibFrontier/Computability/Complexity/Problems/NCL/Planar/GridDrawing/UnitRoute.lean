/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridPath
public import CslibFrontier.Foundations.Geometry.Orthogonal.Neighborhood
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Simple unit routes inside grid paths

Subdivide each segment of a grid path into unit steps, concatenate the resulting walks, and
erase cycles using `SimpleGraph.Walk.toPath`. Every remaining lattice point belongs to the
original grid path, and both endpoints are preserved.

## Main definitions

* `GridDrawing.integerPoint`: include a nonnegative grid point in the integer lattice.
* `GridRouting.Path.unitRoute`: its route after cycle erasure.

## Main results

* `GridRouting.Path.unitRoute_trace`: every listed point lies on the original path.
* `GridRouting.Path.unitRoute_nodup`: cycle erasure gives distinct listed points.
* `GridRouting.Path.unitRoute_unit`: every consecutive segment has length one.
-/

public section

namespace Cslib.Complexity.NCL

namespace GridDrawing

/-- Include a point of the nonnegative grid in the integer lattice. -/
@[expose] def integerPoint (p : GridRouting.Point) : Orthogonal.Point := (p.1, p.2)

/-- The inclusion of the nonnegative grid is injective. -/
theorem integerPoint_injective : Function.Injective integerPoint := by
  intro p q h
  simpa only [integerPoint, Prod.mk.injEq, Nat.cast_inj, Prod.ext_iff] using h

/-- Lattice adjacency by a single horizontal or vertical unit step. -/
private def unitGraph : SimpleGraph Orthogonal.Point where
  Adj a b := Orthogonal.length a b = 1
  symm := ⟨by
    intro a b h
    simp only [Orthogonal.length] at h ⊢
    omega⟩
  loopless := ⟨by
    intro a h
    have hz : 0 = 1 := by
      simpa only [Orthogonal.length, sub_self, Int.natAbs_zero, Nat.zero_add] using h
    exact Nat.zero_ne_one hz⟩

private theorem chain_of_unit (r : Orthogonal.Route)
    (h : ∀ e ∈ r.consecutivePairs, Orthogonal.length e.1 e.2 = 1) :
    r.IsChain unitGraph.Adj := by
  induction r with
  | nil => exact .nil
  | cons a r ih =>
    cases r with
    | nil => exact .singleton _
    | cons b r =>
      refine List.isChain_cons_cons.2 ⟨h (a, b) (List.mem_cons_self), ?_⟩
      exact ih (fun e he => h e (List.mem_cons_of_mem _ he))

/-- Walk along the unit subdivision of one axis-aligned integer segment. -/
private def segmentUnitWalk (a b : Orthogonal.Point) (h : a.1 = b.1 ∨ a.2 = b.2) :
    unitGraph.Walk a b :=
  let r := Orthogonal.segmentWalk a b
  let hn : r ≠ [] := by
    intro he
    have hh := Orthogonal.segmentWalk_head a b
    change r.head? = some a at hh
    rw [he] at hh
    cases hh
  (SimpleGraph.Walk.ofSupport r hn
    (by exact chain_of_unit r (fun _ he => Orthogonal.segmentWalk_unit a b he))).copy
      (List.head_of_head?_eq_some (Orthogonal.segmentWalk_head a b))
      (List.getLast_of_getLast?_eq_some (Orthogonal.segmentWalk_last h))

/-- Segment subdivision has exactly the listed points of the cardinal segment walk. -/
private theorem support_segmentUnitWalk (a b : Orthogonal.Point) (h : a.1 = b.1 ∨ a.2 = b.2) :
    (segmentUnitWalk a b h).support = Orthogonal.segmentWalk a b := by
  simp only [segmentUnitWalk, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_ofSupport]

private theorem segmentWalk_trace (p q : GridRouting.Point)
    (h : p.1 = q.1 ∨ p.2 = q.2) (u : Orthogonal.Point)
    (hu : u ∈ Orthogonal.segmentWalk (integerPoint p) (integerPoint q)) :
    ∃ x : GridRouting.Point, integerPoint x = u ∧
      min p.1 q.1 ≤ x.1 ∧ x.1 ≤ max p.1 q.1 ∧
      min p.2 q.2 ≤ x.2 ∧ x.2 ≤ max p.2 q.2 := by
  have haxis : (integerPoint p).1 = (integerPoint q).1 ∨
      (integerPoint p).2 = (integerPoint q).2 :=
    h.imp (congrArg Int.ofNat) (congrArg Int.ofNat)
  have hm : Orthogonal.realPoint u ∈
      Orthogonal.support (Orthogonal.segmentWalk (integerPoint p) (integerPoint q)) :=
    .inl ⟨u, hu, rfl⟩
  rw [Orthogonal.support_segmentWalk haxis, Orthogonal.realPoint_mem_segment_iff haxis] at hm
  dsimp only [integerPoint] at hm
  refine ⟨(u.1.toNat, u.2.toNat), Prod.ext ?_ ?_, by dsimp only; omega⟩
  · dsimp only [integerPoint]
    omega
  · dsimp only [integerPoint]
    omega

/-- Every consecutive pair in the support of a unit-grid walk has Manhattan length one. -/
private theorem unit_walk_support {a b : Orthogonal.Point} (w : unitGraph.Walk a b) :
    ∀ e ∈ w.support.consecutivePairs, Orthogonal.length e.1 e.2 = 1 := by
  induction w with
  | nil =>
    intro e he
    exact False.elim (List.not_mem_nil he)
  | cons hab w ih =>
    cases w with
    | nil =>
      intro e he
      exact List.mem_singleton.1 he ▸ hab
    | cons _ _ => exact List.forall_mem_cons.2 ⟨hab, ih⟩

end GridDrawing

namespace GridRouting.Path

open GridDrawing

/-- Subdivide every segment into a unit-grid walk and concatenate at the common endpoints. -/
private def unitWalk {p q : Point} : Path p q → unitGraph.Walk (integerPoint p) (integerPoint q)
  | .horizontal x x' y => GridDrawing.segmentUnitWalk _ _ (.inr rfl)
  | .vertical x y y' _ => GridDrawing.segmentUnitWalk _ _ (.inl rfl)
  | .comp r s => r.unitWalk.append s.unitWalk

/-- Every lattice point of the subdivision is a point of the original grid path. -/
private theorem unitWalk_trace {p q : Point} (P : Path p q) (u : Orthogonal.Point)
    (hu : u ∈ P.unitWalk.support) : ∃ x, integerPoint x = u ∧ P.Contains x := by
  induction P with
  | horizontal x x' y =>
    rw [unitWalk, GridDrawing.support_segmentUnitWalk] at hu
    obtain ⟨v, hv, hm⟩ := segmentWalk_trace (x, y) (x', y) (.inr rfl) u hu
    exact ⟨v, hv, by dsimp only [Contains] at hm ⊢; omega⟩
  | vertical x y y' _ =>
    rw [unitWalk, GridDrawing.support_segmentUnitWalk] at hu
    obtain ⟨v, hv, hm⟩ := segmentWalk_trace (x, y) (x, y') (.inl rfl) u hu
    exact ⟨v, hv, by dsimp only [Contains] at hm ⊢; omega⟩
  | comp r s ihr ihs =>
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hu with hu | hu
    · obtain ⟨x, hx, hp⟩ := ihr hu
      exact ⟨x, hx, .inl hp⟩
    · obtain ⟨x, hx, hp⟩ := ihs hu
      exact ⟨x, hx, .inr hp⟩

/-- The unit route obtained by erasing cycles from the segment subdivision. -/
def unitRoute {p q : Point} (P : Path p q) : Orthogonal.Route :=
  (P.unitWalk.toPath : unitGraph.Walk (integerPoint p) (integerPoint q)).support

/-- Cycle erasure retains the prescribed first endpoint. -/
theorem unitRoute_head {p q : Point} (P : Path p q) :
    P.unitRoute.head? = some (integerPoint p) := by
  let w := (P.unitWalk.toPath : unitGraph.Walk (integerPoint p) (integerPoint q))
  exact (List.head?_eq_some_head w.support_ne_nil).trans (congrArg some w.head_support)

/-- Cycle erasure retains the prescribed final endpoint. -/
theorem unitRoute_last {p q : Point} (P : Path p q) :
    P.unitRoute.getLast? = some (integerPoint q) := by
  let w := (P.unitWalk.toPath : unitGraph.Walk (integerPoint p) (integerPoint q))
  exact (List.getLast?_eq_some_getLast w.support_ne_nil).trans (congrArg some w.getLast_support)

/-- The route lists distinct lattice points. -/
theorem unitRoute_nodup {p q : Point} (P : Path p q) : P.unitRoute.Nodup :=
  P.unitWalk.toPath.property.support_nodup

/-- Each consecutive route segment is a unit step. -/
theorem unitRoute_unit {p q : Point} (P : Path p q) :
    ∀ e ∈ P.unitRoute.consecutivePairs, Orthogonal.length e.1 e.2 = 1 :=
  unit_walk_support _

/-- Cycle erasure retains only points of the original grid path. -/
theorem unitRoute_trace {p q : Point} (P : Path p q) (u : Orthogonal.Point)
    (hu : u ∈ P.unitRoute) : ∃ x, integerPoint x = u ∧ P.Contains x :=
  P.unitWalk_trace u (P.unitWalk.support_toPath_subset_support hu)

/-- Membership at a nonnegative grid point implies membership in the original path trace. -/
theorem contains_of_mem_unitRoute {p q : Point} (P : Path p q) (x : Point)
    (hx : integerPoint x ∈ P.unitRoute) : P.Contains x := by
  obtain ⟨y, hy, hm⟩ := P.unitRoute_trace _ hx
  exact integerPoint_injective hy ▸ hm

end GridRouting.Path

end Cslib.Complexity.NCL
