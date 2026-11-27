/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Orthogonal.Trim
import Mathlib.Tactic.NormNum

/-!
# Distinct exit directions at orthogonal drawing vertices

Two proper integer segments leaving the same vertex in the same cardinal direction overlap
at a nonintegral real point. Thus incidence routes whose contacts are graph vertices must
have distinct directions at any common initial vertex, including parallel listed incidences.

## Main results

* `nonGrid_contact_of_direction_eq`: a common direction forces a nonintegral intersection.
* `direction_ne_of_grid_contacts`: endpoint-only geometric contacts imply distinct exits.

## References

The elementary cardinal-ray separation and proofs are original.
-/

public section

namespace Cslib.Orthogonal


private theorem cutPoint_two_one_ne_even (a b v : Point) : cutPoint 2 1 a b ≠ 2 • v := by
  rcases a with ⟨ax, ay⟩
  rcases v with ⟨vx, vy⟩
  intro h
  rcases direction_unit (ax, ay) b with hd | hd | hd | hd <;>
    simp only [cutPoint, hd, one_smul, Prod.smul_mk, Int.nsmul_eq_mul,
      Prod.mk_add_mk, Prod.mk.injEq] at h <;> omega

/-- Equal cardinal directions force a common point that is not an integer grid point. -/
theorem nonGrid_contact_of_direction_eq {a b c : Point}
    (hab : AxisAligned a b) (hac : AxisAligned a c) (hd : direction a b = direction a c) :
    ∃ p ∈ segment a b, p ∈ segment a c ∧ ∀ v : Point, p ≠ realPoint v := by
  let q := cutPoint 2 1 a b
  let p : ℝ × ℝ := (1 / 2 : ℝ) • realPoint q
  have he : (2 : ℝ) • p = realPoint q := by
    dsimp only [p]
    rw [smul_smul]
    norm_num
  have hp_mem {x : Point} (hx : AxisAligned a x) (hdx : direction a b = direction a x) :
      p ∈ segment a x :=
    (mem_segment_nsmul_iff (by decide : 2 ≠ 0) a x p).1
      (by simpa only [Nat.cast_ofNat, he, q, cutPoint, hdx] using
        cutPoint_mem_segment hx (by decide))
  refine ⟨p, hp_mem hab rfl, hp_mem hac hd, fun v hv =>
    cutPoint_two_one_ne_even a b v (realPoint_injective ?_)⟩
  rw [← he, hv, realPoint_nsmul]; norm_num

/-- If common segment points must be integer graph vertices, two incidences cannot leave
their shared initial vertex in the same direction. -/
theorem direction_ne_of_grid_contacts {a b c : Point}
    (hab : AxisAligned a b) (hac : AxisAligned a c)
    (hc : ∀ p ∈ segment a b, p ∈ segment a c → ∃ v : Point, p = realPoint v) :
    direction a b ≠ direction a c := by
  intro hd
  obtain ⟨p, hp, hq, hng⟩ := nonGrid_contact_of_direction_eq hab hac hd
  exact (hc p hp hq).elim hng

end Cslib.Orthogonal
