/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.FiniteAngleOrder
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Topology.Algebra.Affine

/-!
# Disjoint paths between concentric circles

Two clockwise enumerations of distinct ports determine matched continuous paths through
the annulus. The distance from the center grows linearly, while the arguments interpolate
between compatible real lifts. These paths supply continuous routing for a later polygonal
construction. On the closed unit interval they also have Lipschitz bounds for estimating
chord lengths. This is original finite geometry.
-/

public section

namespace Cslib.Polygonal

open AffineMap
open scoped NNReal

private theorem norm_mul_circle_exp_of_angle {x : ℂ} {a : ℝ}
    (ha : (a : Real.Angle) = x.arg) : (‖x‖ : ℂ) * (Circle.exp a : ℂ) = x := by
  have he : Circle.exp a = Circle.exp x.arg := congrArg Real.Angle.toCircle ha
  rw [he, Circle.coe_exp]
  exact Complex.norm_mul_exp_arg_mul_I x

private theorem lipschitzWith_coe_circle_exp :
    LipschitzWith 1 (fun t : ℝ => (Circle.exp t : ℂ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : (Circle.exp x : ℂ) - (Circle.exp y : ℂ) =
      ((Circle.exp (x - y) : ℂ) - 1) * (Circle.exp y : ℂ) := by
    rw [sub_mul, one_mul, ← Circle.coe_mul, ← Circle.exp_add, sub_add_cancel]
  rw [NNReal.coe_one, one_mul, dist_eq_norm, Real.dist_eq, ← Real.norm_eq_abs, he,
    norm_mul, Circle.norm_coe, mul_one, Circle.coe_exp, mul_comm _ Complex.I]
  exact Real.norm_exp_I_mul_ofReal_sub_one_le

/-- Match two clockwise lists of ports by continuous paths in their concentric annulus.
The direction order is specified using the last entry as a cut, as in
`Cslib.Polygonal.exists_reverse_ordered_angle_lift`. Each path's radius interpolates
linearly, and the paths are Lipschitz and jointly injective in the port index and time
on `[0,1]`. The Lipschitz bound is for each separate path. -/
theorem exists_annular_paths (n : ℕ) (z : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (p q : Fin (n + 1) → ℂ) (hp : ∀ i, ‖p i - z‖ = r) (hq : ∀ i, ‖q i - z‖ = R)
    (hp' : Function.Injective (fun i => ((p i - z).arg : Real.Angle)))
    (hq' : Function.Injective (fun i => ((q i - z).arg : Real.Angle)))
    (hpo : ∀ i j, i ≠ Fin.last n → j ≠ Fin.last n → i ≠ j →
      (sbtw ((p (Fin.last n) - z).arg : Real.Angle) ((p i - z).arg : Real.Angle)
        ((p j - z).arg : Real.Angle) ↔ j.val < i.val))
    (hqo : ∀ i j, i ≠ Fin.last n → j ≠ Fin.last n → i ≠ j →
      (sbtw ((q (Fin.last n) - z).arg : Real.Angle) ((q i - z).arg : Real.Angle)
        ((q j - z).arg : Real.Angle) ↔ j.val < i.val)) :
    ∃ γ : Fin (n + 1) → ℝ → ℂ, (∀ i, Continuous (γ i)) ∧
      (∀ i, ∃ K : ℝ≥0, LipschitzOnWith K (γ i) (Set.Icc 0 1)) ∧
      (∀ i, γ i 0 = p i) ∧ (∀ i, γ i 1 = q i) ∧
      (∀ i t, t ∈ Set.Icc 0 1 → ‖γ i t - z‖ = lineMap r R t) ∧
      Set.InjOn (fun x : Fin (n + 1) × ℝ => γ x.1 x.2) {x | x.2 ∈ Set.Icc 0 1} := by
  obtain ⟨a, P, hP, hPcoe, hPlt⟩ :=
    exists_reverse_ordered_angle_lift n (fun i => ((p i - z).arg : Real.Angle)) hp' hpo
  obtain ⟨b, Q, hQ, hQcoe, hQlt⟩ :=
    exists_reverse_ordered_angle_lift n (fun i => ((q i - z).arg : Real.Angle)) hq' hqo
  let angle (i : Fin (n + 1)) : ℝ → ℝ :=
    lineMap (P ((p i - z).arg : Real.Angle)) (Q ((q i - z).arg : Real.Angle))
  let γ (i : Fin (n + 1)) (t : ℝ) : ℂ :=
    z + (lineMap r R t : ℂ) * (Circle.exp (angle i t) : ℂ)
  have hradOrder : StrictMono (lineMap r R : ℝ → ℝ) := fun _ _ h =>
    (lineMap_lt_lineMap_iff_of_lt' hrR).mpr h
  have hrad (t : ℝ) (ht : t ∈ Set.Icc 0 1) : 0 < lineMap r R t :=
    hr.trans_le (by simpa only [lineMap_apply_zero] using hradOrder.monotone ht.1)
  have hnorm (i : Fin (n + 1)) (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
      ‖γ i t - z‖ = lineMap r R t := by
    dsimp only [γ]
    rw [add_sub_cancel_left, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (hrad t ht).le]
  refine ⟨γ, ?_, ?_, ?_, ?_, hnorm, ?_⟩
  · intro i
    exact continuous_const.add ((Complex.continuous_ofReal.comp lineMap_continuous).mul
      (continuous_subtype_val.comp (Circle.exp.continuous.comp lineMap_continuous)))
  · intro i
    let Ka := nndist (P ((p i - z).arg : Real.Angle)) (Q ((q i - z).arg : Real.Angle))
    let Kr := nndist r R
    have hangle : LipschitzWith Ka (angle i) := lipschitzWith_lineMap _ _
    have hc := lipschitzWith_coe_circle_exp.comp hangle
    refine ⟨Kr + R.toNNReal * Ka, LipschitzOnWith.of_dist_le_mul fun s _ t ht => ?_⟩
    have hR : 0 ≤ R := (hr.trans hrR).le
    have hrt : lineMap r R t ≤ R := by
      simpa only [lineMap_apply_one] using hradOrder.monotone ht.2
    have hrd : ‖(lineMap r R s : ℂ) - (lineMap r R t : ℂ)‖ ≤ (Kr : ℝ) * dist s t := by
      rw [← Complex.ofReal_sub, Complex.norm_real, ← dist_eq_norm]
      exact (lipschitzWith_lineMap (𝕜 := ℝ) r R).dist_le_mul s t
    have hcd : ‖(Circle.exp (angle i s) : ℂ) - (Circle.exp (angle i t) : ℂ)‖ ≤
        (Ka : ℝ) * dist s t := by
      simpa only [one_mul, Function.comp_apply, dist_eq_norm] using hc.dist_le_mul s t
    have hsplit : γ i s - γ i t =
        ((lineMap r R s : ℂ) - (lineMap r R t : ℂ)) * (Circle.exp (angle i s) : ℂ) +
          (lineMap r R t : ℂ) *
            ((Circle.exp (angle i s) : ℂ) - (Circle.exp (angle i t) : ℂ)) := by
      dsimp only [γ]
      ring
    rw [dist_eq_norm, hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Circle.norm_coe, mul_one, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (hrad t ht).le]
    calc
      _ ≤ (Kr : ℝ) * dist s t + R * ((Ka : ℝ) * dist s t) :=
        add_le_add hrd (mul_le_mul hrt hcd (norm_nonneg _) hR)
      _ = _ := by rw [NNReal.coe_add, NNReal.coe_mul, Real.coe_toNNReal _ hR]; ring
  · intro i
    dsimp only [γ, angle]
    rw [lineMap_apply_zero, lineMap_apply_zero, ← hp i,
      norm_mul_circle_exp_of_angle (hPcoe _)]
    abel
  · intro i
    dsimp only [γ, angle]
    rw [lineMap_apply_one, lineMap_apply_one, ← hq i,
      norm_mul_circle_exp_of_angle (hQcoe _)]
    abel
  · rintro ⟨i, s⟩ hs ⟨j, t⟩ ht he
    change s ∈ Set.Icc 0 1 at hs
    change t ∈ Set.Icc 0 1 at ht
    change γ i s = γ j t at he
    have hst : s = t := by
      have heq : lineMap r R s = lineMap r R t :=
        (hnorm i s hs).symm.trans ((congrArg (fun x : ℂ => ‖x - z‖) he).trans (hnorm j t ht))
      exact hradOrder.injective heq
    subst t
    have hcircle : Circle.exp (angle i s) = Circle.exp (angle j s) := by
      apply Subtype.ext
      exact mul_left_cancel₀ (by exact_mod_cast (hrad s hs).ne') (add_left_cancel he)
    have hin (k : Fin (n + 1)) : angle k s ∈
        Set.Ico (lineMap a b s) (lineMap a b s + 2 * Real.pi) := by
      refine ⟨(lineMap_strict_mono_endpoints (hP k).1 (hQ k).1 hs.1 hs.2).le, ?_⟩
      have h := lineMap_strict_mono_endpoints (hP k).2 (hQ k).2 hs.1 hs.2
      have heq : lineMap (a + 2 * Real.pi) (b + 2 * Real.pi) s =
          lineMap a b s + 2 * Real.pi := by
        simp only [lineMap_apply_ring]
        ring
      exact h.trans_eq heq
    have hangle : angle i s = angle j s :=
      Circle.exp_injOn_Ico (by linarith) (hin i) (hin j) hcircle
    have hlt {i j : Fin (n + 1)} (h : i < j) : angle j s < angle i s :=
      lineMap_strict_mono_endpoints ((hPlt j i).mpr h) ((hQlt j i).mpr h) hs.1 hs.2
    have hij : i = j := by
      rcases lt_trichotomy i j with h | h | h
      · exact ((hlt h).ne hangle.symm).elim
      · exact h
      · exact ((hlt h).ne hangle).elim
    exact Prod.ext hij rfl

end Cslib.Polygonal
