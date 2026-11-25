/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Geometry.Euclidean.Triangle

/-!
# Complete CAT(0) spaces: definitions

`Cslib.CompleteCAT0Space X` is the convention of the source formalization (`Nc.Cat.Core`): `X` is
complete, and any two points `x`, `v` have a midpoint `m` with the inequality of Bruhat and Tits
`|zm|² ≤ ½|zx|² + ½|zv|² − ¼|xv|²` for every `z` (the *CN inequality*). For geodesic spaces the CN
inequality is equivalent to the CAT(0) condition on comparison triangles
[BridsonHaefliger1999, II.1.9(1)(c), p. 163]; that equivalence is not formalized here, and the
class is used only through the CN inequality. Complete real inner product spaces are instances
(`Cslib.CompleteCAT0Space.ofInnerProductSpace`).

This file states the midpoint condition through the inequality that characterizes the point at
fraction `t` on a geodesic,
`|zb|² ≤ (1 − t)|zx|² + t|zv|² − t(1 − t)|xv|²` (`Cslib.CAT0.IsPointAt`), and the variance
inequality of barycenters (`Cslib.CAT0.IsBarycenter`). Both predicates make sense in every metric
space; the facts that need the CAT(0) inequality are in `Cslib.CAT0.Toolkit`.

The material comes from the formalization of *VP ≠ VNP over every field* [AnthropicVPVNP2026],
modules `Nc.Cat.Core` and `Nc.Cat.Prod`.

## Main definitions

* `Cslib.CAT0.IsPointAt x v t b`: `b` satisfies the inequality of the point at fraction `t`.
* `Cslib.CompleteCAT0Space X`: `X` is complete and any two points have a midpoint with the CN
  inequality (`t = 1/2`).
* `Cslib.CAT0.mid x v`: a chosen midpoint.
* `Cslib.CAT0.IsBarycenter w x b`: `b` satisfies the variance inequality of the weighted points.

## Main results

* `Cslib.CAT0.IsPointAt.dist_left`, `Cslib.CAT0.IsPointAt.dist_right`: the point at fraction `t`
  has distances `t|xv|` and `(1 − t)|xv|`; `Cslib.CAT0.IsPointAt.eq_of_dist`: it is the only
  point with these distances.
* `Cslib.CAT0.IsBarycenter.unique`: a barycenter of positive total weight is unique.
* `Cslib.completeCAT0Space_iff`: the class unfolded into completeness, the midpoint distances and
  the CN inequality.

## References

* [M. R. Bridson and A. Haefliger, *Metric Spaces of Non-Positive Curvature*][BridsonHaefliger1999]
* [Anthropic, *VP ≠ VNP over every field*, Lean formalization][AnthropicVPVNP2026]
-/

public section

namespace Cslib

namespace CAT0

variable {X : Type*} [MetricSpace X]

/-! ### Points at fraction `t` -/

/-- `b` satisfies the inequality of the point at fraction `t` between `x` and `v`:
`|zb|² ≤ (1 − t)|zx|² + t|zv|² − t(1 − t)|xv|²` for every `z`. -/
@[expose] def IsPointAt (x v : X) (t : ℝ) (b : X) : Prop :=
  ∀ z, dist z b ^ 2 ≤ (1 - t) * dist z x ^ 2 + t * dist z v ^ 2 - t * (1 - t) * dist x v ^ 2

theorem IsPointAt.symm {x v b : X} {t : ℝ} (h : IsPointAt x v t b) : IsPointAt v x (1 - t) b :=
  fun z => by rw [dist_comm v x]; linarith [h z]

theorem IsPointAt.dist_left {x v b : X} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (h : IsPointAt x v t b) : dist x b = t * dist x v := by
  have hx : dist x b ≤ t * dist x v := (pow_le_pow_iff_left₀ dist_nonneg (by positivity)
    two_ne_zero).1 (by nlinarith [h x, dist_self x])
  have hv : dist b v ≤ (1 - t) * dist x v := by
    refine (pow_le_pow_iff_left₀ dist_nonneg (mul_nonneg (sub_nonneg.2 h1) dist_nonneg)
      two_ne_zero).1 ?_
    have := h v
    rw [dist_self, dist_comm v x, dist_comm v b] at this; linarith
  linarith [dist_triangle x b v]

theorem IsPointAt.dist_right {x v b : X} {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (h : IsPointAt x v t b) : dist b v = (1 - t) * dist x v := by
  rw [dist_comm b v, h.symm.dist_left (by linarith) (by linarith), dist_comm v x]

/-- A point with the distances of the point at fraction `t` is that point. -/
theorem IsPointAt.eq_of_dist {x v b b' : X} {t : ℝ} (h : IsPointAt x v t b)
    (h2 : dist x b' = t * dist x v) (h3 : dist b' v = (1 - t) * dist x v) : b' = b := by
  have h4 := h b'
  rw [dist_comm b' x, h2, h3] at h4
  exact dist_eq_zero.1 ((sq_nonpos_iff _).1 (by linarith))

end CAT0

open CAT0 in
/-- A *complete CAT(0) space* in the convention of the source formalization (`Nc.Cat.Core`): a
complete metric space in which any two points have a midpoint with the CN inequality of Bruhat
and Tits, `|zm|² ≤ ½|zx|² + ½|zv|² − ¼|xv|²`. For geodesic spaces this is equivalent to the
comparison-triangle definition [BridsonHaefliger1999, II.1.9(1)(c)], which is not formalized
here. -/
class CompleteCAT0Space (X : Type*) [MetricSpace X] : Prop extends CompleteSpace X where
  exists_mid : ∀ x v : X, ∃ m : X, IsPointAt x v (1 / 2) m

namespace CAT0

variable {X : Type*} [MetricSpace X]

section mid

variable [CompleteCAT0Space X]

/-- A chosen midpoint of `x` and `v`. -/
noncomputable def mid (x v : X) : X := Classical.choose (CompleteCAT0Space.exists_mid x v)

theorem isPointAt_mid (x v : X) : IsPointAt x v (1 / 2) (mid x v) :=
  Classical.choose_spec (CompleteCAT0Space.exists_mid x v)

/-- The inequality of Bruhat and Tits. -/
theorem dist_mid_sq_le (x v z : X) :
    dist z (mid x v) ^ 2 ≤ (dist z x ^ 2 + dist z v ^ 2) / 2 - dist x v ^ 2 / 4 := by
  linarith [isPointAt_mid x v z]

theorem dist_mid_left (x v : X) : dist x (mid x v) = dist x v / 2 := by
  rw [(isPointAt_mid x v).dist_left (by norm_num) (by norm_num)]; ring

theorem dist_mid_right (x v : X) : dist (mid x v) v = dist x v / 2 := by
  rw [(isPointAt_mid x v).dist_right (by norm_num) (by norm_num)]; ring

end mid

/-- The class unfolded: `X` is complete, and any two points have a point at distance half their
distance from both with the CN inequality. This restates the bundled axiom only; it is not the
comparison-triangle definition. -/
theorem _root_.Cslib.completeCAT0Space_iff : CompleteCAT0Space X ↔ CompleteSpace X ∧ ∀ x v : X, ∃ m,
    dist x m = dist x v / 2 ∧ dist m v = dist x v / 2 ∧
      ∀ z, dist z m ^ 2 ≤ dist z x ^ 2 / 2 + dist z v ^ 2 / 2 - (dist x v / 2) ^ 2 :=
  ⟨fun h => ⟨h.toCompleteSpace, fun x v => ⟨mid x v, dist_mid_left x v, dist_mid_right x v,
    fun z => by linarith [dist_mid_sq_le x v z]⟩⟩,
    fun ⟨hc, h⟩ => { hc with exists_mid x v :=
      ⟨(h x v).choose, fun z => by linarith [(h x v).choose_spec.2.2 z]⟩ }⟩

/-! ### Barycenters -/

section bary

variable {ι : Type*} [Fintype ι]

/-- `b` is a barycenter of the points `x i` with weights `w i` (of any total weight): the
variance inequality `∑ wᵢ|bxᵢ|² + (∑ wᵢ)|yb|² ≤ ∑ wᵢ|yxᵢ|²` holds for every `y`. -/
@[expose] def IsBarycenter (w : ι → ℝ) (x : ι → X) (b : X) : Prop :=
  ∀ y, ∑ i, w i * dist b (x i) ^ 2 + (∑ i, w i) * dist y b ^ 2 ≤ ∑ i, w i * dist y (x i) ^ 2

theorem IsBarycenter.unique {w : ι → ℝ} {x : ι → X} {b b' : X} (hw : 0 < ∑ i, w i)
    (h : IsBarycenter w x b) (h' : IsBarycenter w x b') : b = b' := by
  have h1 := h b'
  rw [dist_comm] at h1
  exact dist_eq_zero.1 <| (sq_nonpos_iff _).1 <| nonpos_of_mul_nonpos_right (by linarith [h' b]) hw

/-- A surjective isometry maps barycenters to barycenters. -/
theorem IsBarycenter.map {Y : Type*} [MetricSpace Y] {w : ι → ℝ} {x : ι → X} {b : X}
    (h : IsBarycenter w x b) {f : X → Y} (hf : Isometry f) (hs : Function.Surjective f) :
    IsBarycenter w (fun i => f (x i)) (f b) := by
  intro y
  obtain ⟨x₀, rfl⟩ := hs y
  simpa only [hf.dist_eq] using h x₀

/-- Barycenters do not depend on the names of the points. -/
theorem IsBarycenter.comp_equiv {κ : Type*} [Fintype κ] {w : ι → ℝ} {x : ι → X} {b : X}
    (h : IsBarycenter w x b) (e : κ ≃ ι) : IsBarycenter (w ∘ e) (x ∘ e) b := by
  intro y
  simpa only [Function.comp_apply, e.sum_comp fun i => w i * dist b (x i) ^ 2, e.sum_comp w,
    e.sum_comp fun i => w i * dist y (x i) ^ 2] using h y

end bary

/-! ### Instances -/

/-- A complete real inner product space is a complete CAT(0) space: the affine midpoint satisfies
the CN inequality with equality, by Apollonius's identity. -/
instance _root_.Cslib.CompleteCAT0Space.ofInnerProductSpace {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] : CompleteCAT0Space E where
  exists_mid x v := ⟨midpoint ℝ x v, fun z => by
    have := EuclideanGeometry.dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq z x v
    linarith⟩

/-! ### Finite `ℓ²` products -/

/-- The squared distance in a finite `ℓ²` product of metric spaces is the sum of the squared
distances of the coordinates. (`PiLp.dist_sq_eq_of_L2` is the version for normed groups.) -/
theorem _root_.PiLp.dist_sq_eq_sum {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, PseudoMetricSpace (X i)] (f g : PiLp 2 X) :
    dist f g ^ 2 = ∑ i, dist (f i) (g i) ^ 2 := by
  rw [PiLp.dist_eq_sum (by norm_num), ENNReal.toReal_ofNat, ← Real.rpow_natCast,
    ← Real.rpow_mul (Finset.sum_nonneg fun i _ => by positivity)]
  norm_num

/-- A finite `ℓ²` product of CAT(0) spaces is CAT(0): the inequality of Bruhat and Tits adds up
over the coordinates. -/
instance _root_.Cslib.CompleteCAT0Space.piLp {ι : Type*} [Fintype ι] {X : ι → Type*}
    [∀ i, MetricSpace (X i)] [∀ i, CompleteCAT0Space (X i)] : CompleteCAT0Space (PiLp 2 X) where
  exists_mid x v := by
    refine ⟨WithLp.toLp 2 fun i => mid (x i) (v i), fun z => ?_⟩
    rw [PiLp.dist_sq_eq_sum, PiLp.dist_sq_eq_sum, PiLp.dist_sq_eq_sum,
      PiLp.dist_sq_eq_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun i _ => isPointAt_mid (x i) (v i) (z i)

end CAT0

end Cslib
