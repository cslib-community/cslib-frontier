/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Data.List.Defs
public import Mathlib.Basic.Real.Basic
import Aesop

/-!
# Finite orthogonal polygonal routes

The data are lists of integer points. Their geometric interpretation uses Mathlib's closed real
segments, including every real point between consecutive listed points, rather than only lattice
points. A singleton route has singleton support; an empty route has empty support.

## Main definitions

* `Cslib.Orthogonal.Point`, `Cslib.Orthogonal.Route`: finite integer-coordinate data.
* `Cslib.Orthogonal.support`: the continuous support of a polygonal route.
* `Cslib.Orthogonal.IsOrthogonal`: every consecutive segment is axis aligned and nondegenerate.
* `Cslib.Orthogonal.wireLength`: total Manhattan length.

## Main results

* `Cslib.Orthogonal.mem_horizontal`, `Cslib.Orthogonal.mem_vertical`: real segment membership
  characterized by coordinate intervals.
* `Cslib.Orthogonal.mem_support_pair`, `Cslib.Orthogonal.support_bounds_of_points`: continuous
  support of a single segment and coordinate bounding-box preservation.

## References

The finite-route definitions and proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal

/-- An integer grid point. -/
abbrev Point := ℤ × ℤ

/-- Explicit finite polygonal route data. -/
abbrev Route := List Point

/-- Inclusion of the integer grid into the real plane. -/
def realPoint (p : Point) : ℝ × ℝ := (p.1, p.2)

/-- The geometric inclusion does not identify distinct grid points. -/
theorem realPoint_injective : Function.Injective realPoint :=
  fun ⟨_, _⟩ ⟨_, _⟩ h => by simpa [realPoint] using h

/-- A closed real segment between two integer grid points. -/
def segment (a b : Point) : Set (ℝ × ℝ) := _root_.segment ℝ (realPoint a) (realPoint b)

/-- All real points on a finite polygonal route, including isolated listed points. -/
def support (r : Route) : Set (ℝ × ℝ) :=
  {p | (∃ a ∈ r, p = realPoint a) ∨ ∃ e ∈ r.consecutivePairs, p ∈ segment e.1 e.2}

/-- Splitting off the first segment agrees with the continuous polygonal support. -/
theorem support_cons_cons (a b : Point) (r : Route) :
    support (a :: b :: r) = segment a b ∪ support (b :: r) := by
  ext p
  simp only [support, Set.mem_ofPred_eq, List.mem_cons, List.consecutivePairs, List.tail_cons,
    List.zip_cons_cons, exists_eq_or_imp, Set.mem_union]
  have ha : realPoint a ∈ segment a b := left_mem_segment ℝ _ _
  aesop

/-- Every supported point of a route with at least two listed points belongs to one of its
consecutive segments. In this case separate degenerate pieces for listed points are redundant. -/
theorem mem_support_segment {r : Route} (hlen : 2 ≤ r.length) {p : ℝ × ℝ}
    (hp : p ∈ support r) : ∃ e ∈ r.consecutivePairs, p ∈ segment e.1 e.2 := by
  induction r with
  | nil => simp at hlen
  | cons a r ih =>
    rcases r with _ | ⟨b, _ | ⟨c, r⟩⟩
    · simp at hlen
    · rw [support_cons_cons] at hp
      refine ⟨(a, b), by simp [List.consecutivePairs], hp.elim id fun h => ?_⟩
      have hp' : p = realPoint b := by simpa [support, List.consecutivePairs] using h
      exact hp' ▸ right_mem_segment ℝ _ _
    · rw [support_cons_cons] at hp
      rcases hp with hp | hp
      · exact ⟨(a, b), by simp [List.consecutivePairs], hp⟩
      · obtain ⟨e, he, hp⟩ := ih (by simp) hp
        exact ⟨e, List.mem_cons_of_mem (a, b) he, hp⟩

/-- The continuous support of a two-point route `[a, b]` is the segment `segment a b`. -/
theorem mem_support_pair {a b : Point} {p : ℝ × ℝ} :
    p ∈ support [a, b] ↔ p ∈ segment a b := by
  rw [support_cons_cons]
  have hs : p ∈ support [b] ↔ p = realPoint b := by simp [support, List.consecutivePairs]
  exact (Set.mem_union _ _ _).trans ((or_congr_right hs).trans
    ⟨fun h => h.elim id (· ▸ _root_.right_mem_segment ℝ _ _), Or.inl⟩)

/-- The continuous support of a two-point route `[a, b]` equals `segment a b`. -/
theorem support_pair (a b : Point) : support [a, b] = segment a b :=
  Set.ext fun _ => mem_support_pair

/-- A proper axis-aligned segment; zero-length segments are excluded. -/
def AxisAligned (a b : Point) : Prop :=
  (a.1 = b.1 ∨ a.2 = b.2) ∧ a ≠ b

instance (a b : Point) : Decidable (AxisAligned a b) := inferInstanceAs (Decidable (_ ∧ _))

/-- Every consecutive segment is proper and axis aligned. -/
def IsOrthogonal (r : Route) : Prop := ∀ e ∈ r.consecutivePairs, AxisAligned e.1 e.2

/-- Orthogonality is decidable by checking the finitely many consecutive segments. -/
instance : DecidablePred IsOrthogonal :=
  fun r => inferInstanceAs (Decidable (∀ e ∈ r.consecutivePairs, AxisAligned e.1 e.2))

/-- Removing the initial listed point preserves proper orthogonality. -/
theorem IsOrthogonal.of_cons {a : Point} {r : Route} (h : IsOrthogonal (a :: r)) :
    IsOrthogonal r := by
  cases r with
  | nil => simp [IsOrthogonal, List.consecutivePairs]
  | cons b r =>
    intro e he
    exact h e (List.mem_cons_of_mem (a, b) he)

/-- Manhattan length of one segment. -/
def length (a b : Point) : ℕ := (b.1 - a.1).natAbs + (b.2 - a.2).natAbs

/-- A pair of lattice points one Manhattan unit apart forms a proper axis-aligned segment. -/
theorem axisAligned_of_length_eq_one {a b : Point} (h : length a b = 1) : AxisAligned a b := by
  rcases a, b with ⟨⟨ax, ay⟩, ⟨bx, by'⟩⟩
  simp only [length, AxisAligned, ne_eq, Prod.mk.injEq] at h ⊢
  omega

/-- Total Manhattan length of the consecutive segments. -/
def wireLength (r : Route) : ℕ := (r.consecutivePairs.map fun e => length e.1 e.2).sum

/-- A bounding rectangle controls the length of any one segment. -/
theorem length_le_box {a b : Point} {w h : ℕ}
    (ha : 0 ≤ a.1 ∧ a.1 ≤ w ∧ 0 ≤ a.2 ∧ a.2 ≤ h)
    (hb : 0 ≤ b.1 ∧ b.1 ≤ w ∧ 0 ≤ b.2 ∧ b.2 ≤ h) : length a b ≤ w + h := by
  unfold length
  omega

/-- Bounding all listed points bounds the total wire length by the number of segments times
the sum of the rectangle sides. -/
theorem wireLength_le_box {r : Route} {w h : ℕ}
    (hr : ∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ w ∧ 0 ≤ p.2 ∧ p.2 ≤ h) :
    wireLength r ≤ r.consecutivePairs.length * (w + h) := by
  calc wireLength r ≤ (r.consecutivePairs.map fun _ => w + h).sum :=
      List.sum_le_sum fun e he => length_le_box (hr e.1 (List.of_mem_zip he).1)
        (hr e.2 (List.mem_of_mem_tail (List.of_mem_zip he).2))
    _ = _ := by simp

/-- A strict transverse horizontal/vertical crossing at a real point. The strict inequalities
exclude endpoints and bends. -/
def Transverse (a b c d : Point) (p : ℝ × ℝ) : Prop :=
  (a.2 = b.2 ∧ c.1 = d.1 ∧ p = ((c.1 : ℝ), (a.2 : ℝ)) ∧
    min a.1 b.1 < c.1 ∧ c.1 < max a.1 b.1 ∧ min c.2 d.2 < a.2 ∧ a.2 < max c.2 d.2) ∨
  (a.1 = b.1 ∧ c.2 = d.2 ∧ p = ((a.1 : ℝ), (c.2 : ℝ)) ∧
    min c.1 d.1 < a.1 ∧ a.1 < max c.1 d.1 ∧ min a.2 b.2 < c.2 ∧ c.2 < max a.2 b.2)

/-- Every real segment lies in its coordinate bounding rectangle. -/
theorem mem_segment_bounds {a b : Point} {p : ℝ × ℝ} (hp : p ∈ segment a b) :
    p.1 ∈ Set.uIcc (a.1 : ℝ) (b.1 : ℝ) ∧
    p.2 ∈ Set.uIcc (a.2 : ℝ) (b.2 : ℝ) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hp
  constructor <;> rw [← segment_eq_uIcc] <;> exact ⟨s, t, hs, ht, hst, rfl⟩

/-- If every listed point of a route lies in `[x₀, x₁] × [y₀, y₁]`, then every point of its
continuous support lies in `[x₀, x₁] × [y₀, y₁]`. -/
theorem support_bounds_of_points {r : Route} {x₀ x₁ y₀ y₁ : ℤ}
    (h : ∀ q ∈ r, x₀ ≤ q.1 ∧ q.1 ≤ x₁ ∧ y₀ ≤ q.2 ∧ q.2 ≤ y₁)
    {p : ℝ × ℝ} (hp : p ∈ support r) :
    (x₀ : ℝ) ≤ p.1 ∧ p.1 ≤ x₁ ∧ (y₀ : ℝ) ≤ p.2 ∧ p.2 ≤ y₁ := by
  have cb (q : Point) (hq : q ∈ r) :
      (x₀ : ℝ) ≤ q.1 ∧ (q.1 : ℝ) ≤ x₁ ∧ (y₀ : ℝ) ≤ q.2 ∧ (q.2 : ℝ) ≤ y₁ := by
    exact_mod_cast h q hq
  rcases hp with ⟨q, hq, rfl⟩ | ⟨e, he, hp⟩
  · exact cb q hq
  · have ha := cb e.1 (List.of_mem_zip he).1
    have hb := cb e.2 (List.mem_of_mem_tail (List.of_mem_zip he).2)
    obtain ⟨hx, hy⟩ := mem_segment_bounds hp
    rw [Set.mem_uIcc] at hx hy
    exact ⟨hx.elim (ha.1.trans ·.1) (hb.1.trans ·.1),
      hx.elim (·.2.trans hb.2.1) (·.2.trans ha.2.1),
      hy.elim (ha.2.2.1.trans ·.1) (hb.2.2.1.trans ·.1),
      hy.elim (·.2.trans hb.2.2.2) (·.2.trans ha.2.2.2)⟩

/-- Horizontal real segment membership is a one-dimensional interval test. -/
theorem mem_horizontal {a b y : ℝ} {p : ℝ × ℝ} :
    p ∈ _root_.segment ℝ (a, y) (b, y) ↔ p.2 = y ∧ p.1 ∈ Set.uIcc a b := by
  rw [← Prod.image_mk_segment_left, segment_eq_uIcc]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩
  · rintro ⟨hy, hx⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩

/-- Vertical real segment membership is a one-dimensional interval test. -/
theorem mem_vertical {x a b : ℝ} {p : ℝ × ℝ} :
    p ∈ _root_.segment ℝ (x, a) (x, b) ↔ p.1 = x ∧ p.2 ∈ Set.uIcc a b := by
  rw [← Prod.image_mk_segment_right, segment_eq_uIcc]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨rfl, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨p.2, hy, Prod.ext hx.symm rfl⟩

/-- Integer points on an axis-aligned segment can be checked using integer inequalities. -/
theorem realPoint_mem_segment_iff {a b p : Point} (h : a.1 = b.1 ∨ a.2 = b.2) :
    realPoint p ∈ segment a b ↔
      min a.1 b.1 ≤ p.1 ∧ p.1 ≤ max a.1 b.1 ∧
      min a.2 b.2 ≤ p.2 ∧ p.2 ≤ max a.2 b.2 := by
  rcases a, b, p with ⟨⟨ax, ay⟩, ⟨bx, by'⟩, ⟨px, py⟩⟩
  dsimp only at h
  rcases h with rfl | rfl <;>
    simp only [segment, realPoint, mem_vertical, mem_horizontal, Set.mem_uIcc] <;>
    norm_cast <;> omega

/-- Integer-point membership in an orthogonal route is an entirely integer-arithmetic test,
while its meaning remains membership in the continuous real support. -/
theorem realPoint_mem_support_iff {r : Route} (hr : IsOrthogonal r) (p : Point) :
    realPoint p ∈ support r ↔ p ∈ r ∨ ∃ e ∈ r.consecutivePairs,
      min e.1.1 e.2.1 ≤ p.1 ∧ p.1 ≤ max e.1.1 e.2.1 ∧
      min e.1.2 e.2.2 ≤ p.2 ∧ p.2 ≤ max e.1.2 e.2.2 := by
  simp only [support, Set.mem_ofPred_eq]
  constructor
  · rintro (⟨a, ha, heq⟩ | ⟨e, he, hp⟩)
    · exact Or.inl (realPoint_injective heq ▸ ha)
    · exact Or.inr ⟨e, he, (realPoint_mem_segment_iff (hr e he).1).1 hp⟩
  · rintro (hp | ⟨e, he, hp⟩)
    · exact Or.inl ⟨p, hp, rfl⟩
    · exact Or.inr ⟨e, he, (realPoint_mem_segment_iff (hr e he).1).2 hp⟩

end Cslib.Orthogonal
