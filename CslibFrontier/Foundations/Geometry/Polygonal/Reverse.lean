/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
public import Mathlib.Data.Fin.Rev
import Mathlib.Algebra.Order.Interval.Set.Instances
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Reversing indexed polygonal routes

Reversal retains the finite listed chain and reverses its point indices. It preserves
its entire continuous support and simplicity, including permitted closed-endpoint
identification. The actual segment parameter map is `(i.rev, 1-t)` for every real `t`.
Outgoing germs swap end tags without an extra sign.

## Main definitions

* `Cslib.Polygonal.Route.reverse`: reversal of the existing finite indexed route.

## Main results

* `Cslib.Polygonal.Route.eval_reverse`: actual affine parameter reversal.
* `Cslib.Polygonal.Route.position_reverse`: exact reversal of the global chain parameter.
* `Cslib.Polygonal.Route.endpoint_reverse`: endpoints swap their Boolean end tags.
* `Cslib.Polygonal.Route.germ_reverse`: actual outgoing germs swap their end tags.
* `Cslib.Polygonal.Route.reverse_reverse`: reversal is an involution.
* `Cslib.Polygonal.Route.support_reverse`: every actual support point is preserved.
* `Cslib.Polygonal.Route.IsSimple.reverse`: simplicity, with closed ends admitted, is preserved.
* `Cslib.Polygonal.Route.reverse_line`: reversal of a single segment is literally a single segment.

This graph-free API supplies source orientation for future reference detour placement.
The latter and global gluing/parity/HT/query completeness remain open under
[#3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Polygonal.Route

/-- Reverse all listed points, retaining the same number of bends and actual segments. -/
@[expose] def reverse (p : Route) : Route where
  bends := p.bends
  point := fun i => p.point i.rev

/-- Reversing twice gives the original finite route, not merely its support. -/
@[simp] theorem reverse_reverse (p : Route) : p.reverse.reverse = p := by
  cases p
  simp only [reverse, Fin.rev_rev]

/-- Reversal swaps endpoints with the opposite original end tag. -/
@[simp] theorem endpoint_reverse (p : Route) (b : Bool) :
    p.reverse.endpoint b = p.endpoint (!b) := by
  cases b
  · change p.point (0 : Fin (p.bends + 1 + 1)).rev = p.point (Fin.last (p.bends + 1))
    rw [Fin.rev_zero]
  · change p.point (Fin.last (p.bends + 1)).rev = p.point 0
    rw [Fin.rev_last]

/-- Outgoing germs swap their tags. Both definitions already point into the route,
so no extra negation is introduced, even at the two ends of a closed route. -/
@[simp] theorem germ_reverse (p : Route) (b : Bool) :
    p.reverse.germ b = p.germ (!b) := by
  cases b
  · change p.point (0 : Fin (p.bends + 1)).succ.rev -
      p.point (0 : Fin (p.bends + 1 + 1)).rev =
        p.point (Fin.last p.bends).castSucc - p.point (Fin.last (p.bends + 1))
    rw [Fin.rev_succ, Fin.rev_zero, Fin.rev_zero]
  · change p.point (Fin.last p.bends).castSucc.rev -
      p.point (Fin.last (p.bends + 1)).rev = p.point (0 : Fin (p.bends + 1)).succ - p.point 0
    rw [Fin.rev_castSucc, Fin.rev_last, Fin.rev_last]

/-- Every actual reversed segment is the original segment with complementary real time.
The equation holds for all real parameters, including outside the unit interval. -/
theorem eval_reverse (p : Route) (i : Fin p.reverse.segments) (t : ℝ) :
    p.reverse.eval i t = p.eval i.rev (1 - t) := by
  change Fin (p.bends + 1) at i
  change AffineMap.lineMap (p.point i.castSucc.rev) (p.point i.succ.rev) t =
    AffineMap.lineMap (p.point i.rev.castSucc) (p.point i.rev.succ) (1 - t)
  rw [Fin.rev_castSucc, Fin.rev_succ, AffineMap.lineMap_apply_one_sub]

/-- Global chain positions sum to the number of segments under the actual parameter map. -/
theorem position_reverse (p : Route) (i : Fin p.reverse.segments) (t : ℝ) :
    p.reverse.position i t = (p.segments : ℝ) - p.position i.rev (1 - t) := by
  change Fin (p.bends + 1) at i
  change (i.val : ℝ) + t = ((p.bends + 1 : ℕ) : ℝ) - ((i.rev.val : ℝ) + (1 - t))
  simp only [Nat.cast_add, Nat.cast_one]
  have h : (i.val : ℝ) + (i.rev.val : ℝ) = (p.bends : ℝ) := by
    exact_mod_cast Fin.add_rev_cast i
  linarith

private theorem atEnd_reverse (p : Route) (i : Fin p.reverse.segments) (t : ℝ) (b : Bool) :
    p.reverse.AtEnd i t b ↔ p.AtEnd i.rev (1 - t) (!b) := by
  change (p.reverse.position i t = if b then (p.segments : ℝ) else 0) ↔ _
  rw [position_reverse]
  cases b <;> simp only [AtEnd, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte] <;>
    constructor <;> intro h <;> linarith

/-- Reversal preserves the full continuum of actual support points. -/
@[simp] theorem support_reverse (p : Route) : p.reverse.support = p.support := by
  have sub (r : Route) : r.reverse.support ⊆ r.support := by
    intro z hz
    obtain ⟨i, t, ht, heq⟩ := (r.reverse.mem_support_iff z).mp hz
    exact (r.mem_support_iff z).mpr
      ⟨i.rev, 1 - t, Set.Icc.one_sub_mem ht, (eval_reverse r i t).symm.trans heq⟩
  exact Set.Subset.antisymm (sub p) (by simpa only [reverse_reverse] using sub p.reverse)

/-- Reversal preserves simplicity without excluding the permitted identification of the
two ends of a closed route. Both closing alternatives are swapped by the end-tag map. -/
theorem IsSimple.reverse {p : Route} (hp : p.IsSimple) : p.reverse.IsSimple := by
  intro i j s t hs ht heq
  have heq' : p.eval i.rev (1 - s) = p.eval j.rev (1 - t) := by
    simpa only [eval_reverse] using heq
  rcases hp i.rev j.rev (1 - s) (1 - t) (Set.Icc.one_sub_mem hs)
      (Set.Icc.one_sub_mem ht) heq' with h | ⟨h0, h1⟩ | ⟨h1, h0⟩
  · left
    rw [position_reverse, position_reverse, h]
  · right
    right
    exact ⟨(atEnd_reverse p i s true).mpr h0, (atEnd_reverse p j t false).mpr h1⟩
  · right
    left
    exact ⟨(atEnd_reverse p i s false).mpr h1, (atEnd_reverse p j t true).mpr h0⟩

/-- A reversed one-segment route is literally the one-segment route with swapped ends. -/
@[simp] theorem reverse_line (a b : ℂ) : (line a b).reverse = line b a := by
  unfold reverse line
  congr 1
  funext i
  fin_cases i <;> rfl

end Cslib.Polygonal.Route
