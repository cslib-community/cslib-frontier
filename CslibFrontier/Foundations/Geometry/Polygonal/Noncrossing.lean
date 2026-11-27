/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# Polygonal loops above ordered ports

A loop leaves the origin towards `(a,1)`, rises vertically, crosses horizontally at height
`2 + |a-b|`, returns to `(b,1)`, and closes at the origin. Distinct disjoint or strictly nested
port intervals give loops whose only common point is the origin. All statements quantify over
actual real parameters of the five segments. This is an original coordinate construction.
-/

public section

namespace Cslib.Polygonal

/-- A five-segment closed route with ordered real ports and a horizontal upper segment.
The two ports are kept in the given order, including when `b < a`. -/
@[expose] def portLoop (a b : ℝ) : Route where
  bends := 4
  point := ![0, ⟨a, 1⟩, ⟨a, 2 + |a - b|⟩, ⟨b, 2 + |a - b|⟩, ⟨b, 1⟩, 0]

/-- Both ends are the origin. -/
@[simp] theorem endpoint_portLoop (a b : ℝ) (c : Bool) : (portLoop a b).endpoint c = 0 := by
  cases c <;> rfl

/-- The two actual outgoing germs point to the two separately indexed ports. -/
@[simp] theorem germ_portLoop (a b : ℝ) (c : Bool) :
    (portLoop a b).germ c = if c then ⟨b, 1⟩ else ⟨a, 1⟩ := by
  cases c <;> simp [Route.germ, Route.start, Route.finish, portLoop, Route.segments,
    Fin.succ, Fin.last]

/-- Coordinates at every real parameter on each of the five actual segments. -/
theorem eval_portLoop (a b : ℝ) (i : Fin 5) (t : ℝ) :
    (portLoop a b).eval i t =
      (![⟨t * a, t⟩, ⟨a, 1 + t * (1 + |a - b|)⟩,
        ⟨(1 - t) * a + t * b, 2 + |a - b|⟩,
        ⟨b, 2 + |a - b| - t * (1 + |a - b|)⟩,
        ⟨(1 - t) * b, 1 - t⟩] : Fin 5 → ℂ) i := by
  fin_cases i <;>
    apply Complex.ext <;>
    simp [Route.eval, portLoop, AffineMap.lineMap_apply_module] <;> ring

private theorem portLoop_contact_forward {a b : ℝ} (hab : a ≠ b)
    (i j : Fin 5) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : (portLoop a b).eval i s = (portLoop a b).eval j t) (hij : i.val ≤ j.val) :
    (i.val : ℝ) + s = j.val + t ∨
      ((i.val : ℝ) + s = 0 ∧ (j.val : ℝ) + t = 5) := by
  rw [eval_portLoop a b i s, eval_portLoop a b j t] at heq
  have hx := congrArg Complex.re heq
  have hy := congrArg Complex.im heq
  have hfactor (u : ℝ) (h : u * (a - b) = 0) : u = 0 :=
    (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hab)
  have hheight (u : ℝ) (h : u * (1 + |a - b|) = 0) : u = 0 :=
    (mul_eq_zero.mp h).resolve_right (ne_of_gt (by positivity))
  have hsa := mul_nonneg hs.1 (abs_nonneg (a - b))
  have hta := mul_nonneg ht.1 (abs_nonneg (a - b))
  have hs'a := mul_nonneg (sub_nonneg.mpr hs.2) (abs_nonneg (a - b))
  have ht'a := mul_nonneg (sub_nonneg.mpr ht.2) (abs_nonneg (a - b))
  fin_cases i <;> fin_cases j <;> dsimp at hx hy hij ⊢ <;>
    norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, zero_add] <;>
    try omega
  · left; linarith
  · left; linarith [hs.2, ht.1, hta]
  · exfalso; linarith [hs.2, abs_nonneg (a - b)]
  · have hs1 : s = 1 := by linarith [hs.2, ht.2, ht'a]
    exact absurd (by simpa only [hs1, one_mul] using hx) hab
  · rw [← hy] at hx
    have hs0 := hfactor s (by linear_combination hx)
    exact Or.inr ⟨by linarith, by linarith⟩
  · have hst := hheight (s - t) (by linear_combination hy)
    left; linarith
  · have ht0 := hfactor t (by linear_combination hx)
    have hs1 := hheight (s - 1) (by linear_combination hy)
    left; linarith
  · exact False.elim (hab hx)
  · have ht0 : t = 0 := by linarith [hs.1, ht.1, hsa]
    exact absurd (by simpa only [ht0, sub_zero, one_mul] using hx) hab
  · have hst := hfactor (s - t) (by linear_combination -hx)
    left; linarith
  · have hs1 := hfactor (s - 1) (by linear_combination -hx)
    have ht0 := hheight t (by linear_combination hy)
    left; linarith
  · exfalso; linarith [ht.1, abs_nonneg (a - b)]
  · have hst := hheight (s - t) (by linear_combination -hy)
    left; linarith
  · left; linarith [hs.2, ht.1, hs'a]
  · left; linarith

/-- The five-segment loop is simple whenever its two ports are distinct. -/
theorem isSimple_portLoop {a b : ℝ} (hab : a ≠ b) : (portLoop a b).IsSimple := by
  intro i j s t hs ht heq
  by_cases hij : i.val ≤ j.val
  · exact (portLoop_contact_forward hab i j s t hs ht heq hij).imp id Or.inl
  · exact (portLoop_contact_forward hab j i t s ht hs heq.symm (by omega)).imp Eq.symm
      fun h => Or.inr ⟨h.2, h.1⟩

/-- Every point is either on a radial segment below the ports, or on the three-sided
upper arc. The latter lies in its bounding rectangle and on its two sides or its top. -/
theorem eval_portLoop_cases (a b : ℝ) (i : Fin 5) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    let z := (portLoop a b).eval i t
    (z.im ∈ Set.Icc 0 1 ∧ (z.re = z.im * a ∨ z.re = z.im * b)) ∨
      (1 ≤ z.im ∧ min a b ≤ z.re ∧ z.re ≤ max a b ∧ z.im ≤ 2 + |a - b| ∧
        (z.re = a ∨ z.re = b ∨ z.im = 2 + |a - b|)) := by
  dsimp only
  rw [eval_portLoop]
  have hta := mul_nonneg ht.1 (abs_nonneg (a - b))
  have ht'a := mul_nonneg (sub_nonneg.mpr ht.2) (abs_nonneg (a - b))
  fin_cases i <;> dsimp
  · exact Or.inl ⟨ht, Or.inl rfl⟩
  · exact Or.inr ⟨by linarith [ht.1, hta], min_le_left _ _, le_max_left _ _,
      by linarith [ht.2, ht'a], Or.inl rfl⟩
  · right
    refine ⟨by linarith [abs_nonneg (a - b)], ?_, ?_, le_rfl, Or.inr (Or.inr rfl)⟩
    · linarith [mul_nonneg ht.1 (sub_nonneg.mpr (min_le_right a b)),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (min_le_left a b))]
    · linarith [mul_nonneg ht.1 (sub_nonneg.mpr (le_max_right a b)),
        mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr (le_max_left a b))]
  · exact Or.inr ⟨by linarith [ht.2, ht'a], min_le_right _ _, le_max_right _ _,
      by linarith [ht.1, hta], Or.inr (Or.inl rfl)⟩
  · exact Or.inl ⟨⟨sub_nonneg.mpr ht.2, sub_le_self 1 ht.1⟩, Or.inr rfl⟩

private theorem radial_contact {a b : ℝ} (hab : a ≠ b) {z : ℂ}
    (ha : z.re = z.im * a) (hb : z.re = z.im * b) : z = 0 := by
  have him : z.im = 0 :=
    (mul_eq_zero.mp (by linear_combination hb - ha : z.im * (a - b) = 0)).resolve_right
      (sub_ne_zero.mpr hab)
  exact Complex.ext (by simpa [him] using ha) him

private theorem radial_upper_ne {a b c : ℝ} (hab : a ≠ b) (hac : a ≠ c) {z : ℂ}
    (hz : z.im ≤ 1) (hr : z.re = z.im * a)
    (hu : 1 ≤ z.im ∧ min b c ≤ z.re ∧ z.re ≤ max b c ∧ z.im ≤ 2 + |b - c| ∧
      (z.re = b ∨ z.re = c ∨ z.im = 2 + |b - c|)) : False := by
  have him : z.im = 1 := le_antisymm hz hu.1
  have hre : z.re = a := by simpa only [him, one_mul] using hr
  rcases hu.2.2.2.2 with hb | hc | hy
  · exact hab (hre.symm.trans hb)
  · exact hac (hre.symm.trans hc)
  · linarith [abs_nonneg (b - c)]

private theorem upper_nested_ne {a b c d : ℝ} {z : ℂ}
    (hl : min a b < min c d) (hu : max c d < max a b)
    (hz : 1 ≤ z.im ∧ min a b ≤ z.re ∧ z.re ≤ max a b ∧ z.im ≤ 2 + |a - b| ∧
      (z.re = a ∨ z.re = b ∨ z.im = 2 + |a - b|))
    (hw : 1 ≤ z.im ∧ min c d ≤ z.re ∧ z.re ≤ max c d ∧ z.im ≤ 2 + |c - d| ∧
      (z.re = c ∨ z.re = d ∨ z.im = 2 + |c - d|)) : False := by
  have hwidth : |c - d| < |a - b| := by
    rw [abs_sub_comm c d, ← max_sub_min_eq_abs c d,
      abs_sub_comm a b, ← max_sub_min_eq_abs a b]
    linarith
  rcases le_total a b with hab | hab
  · simp only [min_eq_left hab, max_eq_right hab] at hl hu
    rcases hz.2.2.2.2 with ha | hb | hy <;> linarith [hw.2.1, hw.2.2.1, hw.2.2.2.1]
  · simp only [min_eq_right hab, max_eq_left hab] at hl hu
    rcases hz.2.2.2.2 with ha | hb | hy <;> linarith [hw.2.1, hw.2.2.1, hw.2.2.2.1]

/-- Disjoint or strictly nested port intervals give loops meeting only at the origin.
The four port coordinates must be distinct, but neither their spacing nor the loop
orientations are prescribed. -/
theorem portLoop_contact_eq_zero {a b c d : ℝ}
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (horder : max a b < min c d ∨ max c d < min a b ∨
      (min a b < min c d ∧ max c d < max a b) ∨
      (min c d < min a b ∧ max a b < max c d))
    (i j : Fin 5) {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (heq : (portLoop a b).eval i s = (portLoop c d).eval j t) :
    (portLoop a b).eval i s = 0 := by
  have h := eval_portLoop_cases a b i hs
  have k := eval_portLoop_cases c d j ht
  rw [← heq] at k
  rcases h with ⟨hy, hr | hr⟩ | h
  · rcases k with ⟨_, hk | hk⟩ | k
    · exact radial_contact hac hr hk
    · exact radial_contact had hr hk
    · exact False.elim (radial_upper_ne hac had hy.2 hr k)
  · rcases k with ⟨_, hk | hk⟩ | k
    · exact radial_contact hbc hr hk
    · exact radial_contact hbd hr hk
    · exact False.elim (radial_upper_ne hbc hbd hy.2 hr k)
  · rcases k with ⟨hy, hk | hk⟩ | k
    · exact False.elim (radial_upper_ne hac.symm hbc.symm hy.2 hk h)
    · exact False.elim (radial_upper_ne had.symm hbd.symm hy.2 hk h)
    · exfalso
      rcases horder with hlt | hlt | ⟨hl, hu⟩ | ⟨hl, hu⟩
      · linarith [h.2.2.1, k.2.1]
      · linarith [k.2.2.1, h.2.1]
      · exact upper_nested_ne hl hu h k
      · exact upper_nested_ne hl hu k h

/-- Nonnegative ports bounded by `B` keep every segment in the same horizontal strip. -/
theorem re_eval_portLoop_mem {a b B : ℝ} (ha : a ∈ Set.Icc 0 B) (hb : b ∈ Set.Icc 0 B)
    (i : Fin 5) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ((portLoop a b).eval i t).re ∈ Set.Icc 0 B := by
  rcases eval_portLoop_cases a b i ht with ⟨hy, hx | hx⟩ | h
  · rw [hx]
    exact ⟨mul_nonneg hy.1 ha.1, (mul_le_of_le_one_left ha.1 hy.2).trans ha.2⟩
  · rw [hx]
    exact ⟨mul_nonneg hy.1 hb.1, (mul_le_of_le_one_left hb.1 hy.2).trans hb.2⟩
  · exact ⟨(le_min ha.1 hb.1).trans h.2.1,
      h.2.2.1.trans (max_le ha.2 hb.2)⟩

/-- Only the first and last global parameters of a simple port loop visit the origin. -/
theorem atEnd_of_eval_portLoop_eq_zero {a b : ℝ} (hab : a ≠ b) (i : Fin 5) {t : ℝ}
    (ht : t ∈ Set.Icc 0 1) (heq : (portLoop a b).eval i t = 0) :
    ∃ c, (portLoop a b).AtEnd i t c := by
  have h0 : (portLoop a b).eval i t = (portLoop a b).eval 0 0 :=
    heq.trans (AffineMap.lineMap_apply_zero (0 : ℂ) ⟨a, 1⟩).symm
  rcases isSimple_portLoop hab i 0 t 0 ht (by simp) h0 with h | ⟨h, _⟩ | ⟨h, _⟩
  · exact ⟨false, by simpa [Route.AtEnd, Route.position] using h⟩
  · exact ⟨false, h⟩
  · exact ⟨true, h⟩

end Cslib.Polygonal
