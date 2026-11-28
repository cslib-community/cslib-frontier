/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.Route
import CslibFrontier.Foundations.Geometry.Polygonal.SegmentOrder
import Mathlib.Geometry.Euclidean.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Radial order on outward polygonal routes

A chord goes outward when the squared radial gain exceeds its squared length.
This endpoint test implies strict radial progress along the whole chord, and therefore
along a route made of outward chords. This is original geometric infrastructure.
-/

public section

namespace Cslib.Polygonal

open AffineMap
open scoped RealInnerProductSpace

private theorem norm_sq_lineMap_sub (z a b : ℂ) (t : ℝ) :
    ‖lineMap a b t - z‖ ^ 2 =
      (1 - t) * ‖a - z‖ ^ 2 + t * ‖b - z‖ ^ 2 - t * (1 - t) * ‖b - a‖ ^ 2 := by
  have hline (u : ℝ) :
      ‖lineMap a b u - z‖ ^ 2 =
        ‖b - a‖ ^ 2 * u * u + 2 * ⟪b - a, a - z⟫ * u + ‖a - z‖ ^ 2 := by
    simpa only [lineMap_apply, vadd_eq_add, vsub_eq_sub, dist_eq_norm,
      real_inner_self_eq_norm_sq, sq] using EuclideanGeometry.dist_smul_vadd_sq u (b - a) a z
  have hend := hline 1
  simp only [lineMap_apply_one, mul_one] at hend
  rw [hline]
  linear_combination -t * hend

/-- If the squared radial gain exceeds the squared chord length, the distance from the
center is strictly increasing on the entire chord, including its endpoints. -/
theorem strictMonoOn_norm_lineMap_sub {z a b : ℂ}
    (h : ‖b - a‖ ^ 2 < ‖b - z‖ ^ 2 - ‖a - z‖ ^ 2) :
    StrictMonoOn (fun t : ℝ => ‖lineMap a b t - z‖) (Set.Icc 0 1) := by
  intro s hs t ht hst
  apply (sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  have hterm : 0 <
      ‖b - z‖ ^ 2 - ‖a - z‖ ^ 2 - (1 - (s + t)) * ‖b - a‖ ^ 2 := by
    have hle : (1 - (s + t)) * ‖b - a‖ ^ 2 ≤ ‖b - a‖ ^ 2 := by
      nlinarith [mul_nonneg (add_nonneg hs.1 ht.1) (sq_nonneg ‖b - a‖)]
    linarith
  have hdiff : ‖lineMap a b t - z‖ ^ 2 - ‖lineMap a b s - z‖ ^ 2 =
      (t - s) * (‖b - z‖ ^ 2 - ‖a - z‖ ^ 2 - (1 - (s + t)) * ‖b - a‖ ^ 2) := by
    rw [norm_sq_lineMap_sub, norm_sq_lineMap_sub]
    ring
  exact sub_pos.mp (hdiff ▸ mul_pos (sub_pos.mpr hst) hterm)

/-- On a route whose chords all go outward, radii have the strict order of chain positions. -/
theorem Route.norm_eval_lt_iff_position_lt_of_outward (p : Route) (z : ℂ)
    (h : ∀ i : Fin p.segments, ‖p.point i.succ - p.point i.castSucc‖ ^ 2 <
      ‖p.point i.succ - z‖ ^ 2 - ‖p.point i.castSucc - z‖ ^ 2)
    (i j : Fin p.segments) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1) :
    ‖p.eval i s - z‖ < ‖p.eval j t - z‖ ↔ p.position i s < p.position j t :=
  p.eval_lt_iff_position_lt_of_strictMonoOn (fun x => ‖x - z‖)
    (fun k => strictMonoOn_norm_lineMap_sub (h k)) i j s t hs ht

/-- A route all of whose chords go outward is simple. -/
theorem Route.isSimple_of_outward (p : Route) (z : ℂ)
    (h : ∀ i : Fin p.segments, ‖p.point i.succ - p.point i.castSucc‖ ^ 2 <
      ‖p.point i.succ - z‖ ^ 2 - ‖p.point i.castSucc - z‖ ^ 2) : p.IsSimple :=
  Route.isSimple_of_strictMonoOn_eval (fun x => ‖x - z‖)
    (fun k => strictMonoOn_norm_lineMap_sub (h k))

end Cslib.Polygonal
