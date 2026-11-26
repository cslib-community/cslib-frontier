/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Planar Gaussian projections of three vectors in a spherical cap

Let `x` be a unit vector of a finite-dimensional real inner product space `E`, and let
`y₀, y₁, y₂ : E` be vectors of norm at most `1` lying in the spherical cap `κ ≤ ⟪yᵢ, x⟫`
(`0 < κ ≤ 1`). Draw two independent standard Gaussian vectors `(X₁, X₂)` from
`(stdGaussian E).prod (stdGaussian E)` and form the three planar projections
`zᵢ = (⟪yᵢ, X₁⟫, ⟪yᵢ, X₂⟫) ∈ ℝ²`. What is the probability that `(0, 0)` lies in the triangle
`conv(z₀, z₁, z₂)`?

1. **Orthonormal coordinates in `ℝ³`.** Embedding `E` isometrically into an ambient space with
   three spare orthogonal directions and running three steps of Gram–Schmidt produces an
   orthonormal triple `(e₀, e₁, e₂)` whose span contains `y₀, y₁, y₂`. Under `stdGaussian`, the
   projections onto any finite orthonormal family are independent `N(0, 1)` variables
   (`ProbabilityTheory.stdGaussian_map_inner_pi`).
2. **Cross-product cap inequality.** In the `(e₀, e₁, e₂)` coordinates, any convex combination
   `c = w₀ c₀ + w₁ c₁ + w₂ c₂` (`wᵢ ≥ 0`, `∑ wᵢ = 1`) has norm at most `1` and inner product at
   least `κ` with the normalized projection `v ∈ S²` of `x`. If `c · g₁ = c · g₂ = 0` for the two
   `N(0, I₃)` coordinate samples `g₁, g₂`, the vector triple product identity
   `c × (g₁ × g₂) = (c · g₂) g₁ - (c · g₁) g₂ = 0` forces `g₁ × g₂` to be parallel to `c`, so
   `κ ^ 2 * ‖g₁ × g₂‖ ^ 2 ≤ (v · (g₁ × g₂)) ^ 2`.
3. **Householder–Fubini evaluation (`1 - κ`).** A Householder reflection preserves `N(0, I₃)` and
   negates cross products up to reflection (`(H a) × (H b) = -H (a × b)`). Introducing an
   independent `X ~ N(0, I₃)` and swapping expectations via Fubini equates
   `Pr[κ ^ 2 ‖g₁ × g₂‖ ^ 2 ≤ (v · (g₁ × g₂)) ^ 2]` with the single-Gaussian double-cone
   probability `Pr[κ ^ 2 (X₀ ^ 2 + X₁ ^ 2 + X₂ ^ 2) ≤ X₀ ^ 2]`, which evaluates in cylindrical
   polar coordinates to `1 - κ`.

## Main results

* `ProbabilityTheory.stdGaussian_map_inner_pi`: projections of `stdGaussian E` onto a finite
  orthonormal family have law `Measure.pi (fun _ => gaussianReal 0 1)`.
* `ProbabilityTheory.measurableSet_convex_zero_three`: measurability of the event that `(0, 0)` is
  a convex combination of three continuous planar functions.
* `ProbabilityTheory.measureReal_stdGaussian_prod_convex_zero_le`: the planar origin-in-triangle
  probability is at most `1 - κ` under `(stdGaussian E).prod (stdGaussian E)`.
* `ProbabilityTheory.measureReal_pi_prod_convex_zero_le`: coordinatewise `Measure.pi`
  specialization.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace ProbabilityTheory

/-! ### Finite orthonormal families under `stdGaussian` -/

/-- **Projections onto a finite orthonormal family.** Under `stdGaussian E`, the inner products
with a family of pairwise orthogonal unit vectors `u : ι → E` are independent standard Gaussian
random variables. -/
theorem stdGaussian_map_inner_pi {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]
    {u : ι → E} (hu_norm : ∀ i, ‖u i‖ = 1) (hu_orth : Pairwise fun i j => ⟪u i, u j⟫ = 0) :
    (stdGaussian E).map (fun x i => ⟪u i, x⟫) = Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have hlaw : HasGaussianLaw (fun x => fun i : ι => innerSL ℝ (u i) x) (stdGaussian E) :=
    IsGaussian.hasGaussianLaw_id.map_fun (ContinuousLinearMap.pi fun i => innerSL ℝ (u i))
  have hind : iIndepFun (fun i x => ⟪u i, x⟫) (stdGaussian E) := by
    refine hlaw.iIndepFun_of_covariance_eq_zero fun i j hij => ?_
    have h := covarianceBilin_apply_eq_cov (μ := stdGaussian E) IsGaussian.memLp_two_id (u i) (u j)
    rw [covarianceBilin_stdGaussian, innerSL_apply_apply ℝ] at h
    exact h.symm.trans (hu_orth hij)
  rw [hind.map_fun_eq_pi_map fun _ => by fun_prop]
  congr with i
  have hn : ‖u i‖₊ = 1 := Subtype.ext (hu_norm i)
  rw [stdGaussian_map_inner, hn, one_pow]

/-! ### Closedness and measurability of the planar origin-in-triangle event -/

private abbrev convexZeroSet {Z : Type*} (f₀ f₁ f₂ : Z → ℝ × ℝ) : Set Z :=
  {z : Z | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
    w₀ * (f₀ z).1 + w₁ * (f₁ z).1 + w₂ * (f₂ z).1 = 0 ∧
    w₀ * (f₀ z).2 + w₁ * (f₁ z).2 + w₂ * (f₂ z).2 = 0}

/-- On any topological space `Z`, the set of `z` for which `(0, 0)` is a convex combination of
three continuous planar points `(f₀ z, f₁ z, f₂ z)` is closed, hence measurable. -/
theorem measurableSet_convex_zero_three {Z : Type*} [TopologicalSpace Z] [MeasurableSpace Z]
    [OpensMeasurableSpace Z] {f₀ f₁ f₂ : Z → ℝ × ℝ} (hf₀ : Continuous f₀) (hf₁ : Continuous f₁)
    (hf₂ : Continuous f₂) :
    MeasurableSet {z : Z | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
      w₀ * (f₀ z).1 + w₁ * (f₁ z).1 + w₂ * (f₂ z).1 = 0 ∧
      w₀ * (f₀ z).2 + w₁ * (f₁ z).2 + w₂ * (f₂ z).2 = 0} := by
  let K3 := Fin 3 → Icc (0 : ℝ) 1
  let closedRel : Set (Z × K3) :=
    {zw | (zw.2 0 : ℝ) + (zw.2 1 : ℝ) + (zw.2 2 : ℝ) = 1 ∧
      (zw.2 0 : ℝ) * (f₀ zw.1).1 + (zw.2 1 : ℝ) * (f₁ zw.1).1 + (zw.2 2 : ℝ) * (f₂ zw.1).1 = 0 ∧
      (zw.2 0 : ℝ) * (f₀ zw.1).2 + (zw.2 1 : ℝ) * (f₁ zw.1).2 + (zw.2 2 : ℝ) * (f₂ zw.1).2 = 0}
  have hclosedRel : IsClosed closedRel :=
    (isClosed_eq (by fun_prop) continuous_const).inter
      ((isClosed_eq (by fun_prop) continuous_const).inter
        (isClosed_eq (by fun_prop) continuous_const))
  have himg : convexZeroSet f₀ f₁ f₂ = Prod.fst '' closedRel := by
    ext z
    dsimp only [convexZeroSet, closedRel]
    simp only [mem_ofPred_eq, mem_image, Prod.exists]
    refine ⟨?_, ?_⟩
    · rintro ⟨w₀, w₁, w₂, hw₀, hw₁, hw₂, hsum, hx, hy⟩
      exact ⟨z, ![⟨w₀, hw₀, by linarith⟩, ⟨w₁, hw₁, by linarith⟩, ⟨w₂, hw₂, by linarith⟩],
        ⟨hsum, hx, hy⟩, rfl⟩
    · rintro ⟨_, w, ⟨hsum, hx, hy⟩, rfl⟩
      exact ⟨(w 0 : ℝ), (w 1 : ℝ), (w 2 : ℝ), (w 0).2.1, (w 1).2.1, (w 2).2.1, hsum, hx, hy⟩
  change MeasurableSet (convexZeroSet f₀ f₁ f₂)
  rw [himg]
  exact (isClosedMap_fst_of_compactSpace _ hclosedRel).measurableSet

/-! ### `ℝ³` cross products, Householder reflections, and Gaussian cones -/

section R3

private local instance : NullSingletonClass (gaussianReal 0 1) :=
  nullSingletonClass_gaussianReal one_ne_zero

private noncomputable abbrev P3Measure : Measure (Fin 3 → ℝ) :=
  Measure.pi fun _ : Fin 3 => gaussianReal 0 1

private def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

private def normSq3 (u : Fin 3 → ℝ) : ℝ := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2

private def cross3 (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

private noncomputable def unitVec3 (x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => (√(normSq3 x))⁻¹ * x i

private theorem dot3_comm (u v : Fin 3 → ℝ) : dot3 u v = dot3 v u := by
  dsimp [dot3]; ring

private theorem normSq3_nonneg (u : Fin 3 → ℝ) : 0 ≤ normSq3 u := by
  dsimp [normSq3]; positivity

private theorem normSq3_pos_of_ne_zero {x : Fin 3 → ℝ} (hx : x ≠ 0) : 0 < normSq3 x := by
  by_contra! hle
  apply hx
  dsimp [normSq3] at hle
  ext i
  fin_cases i <;>
    (dsimp; exact sq_eq_zero_iff.mp
      (by linarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]))

private theorem normSq3_unitVec3 {x : Fin 3 → ℝ} (hx : 0 < normSq3 x) :
    normSq3 (unitVec3 x) = 1 := by
  have hsq : (√(normSq3 x)) ^ 2 = normSq3 x := sq_sqrt hx.le
  dsimp [unitVec3, normSq3] at hsq hx ⊢
  have hne : √(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ≠ 0 := (sqrt_pos.mpr hx).ne'
  field_simp [hne]
  linarith only [hsq]

private theorem continuous_normSq3 : Continuous normSq3 := by
  unfold normSq3; fun_prop

private theorem continuous_cross3 :
    Continuous fun ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) => cross3 ab.1 ab.2 := by
  unfold cross3
  refine continuous_pi fun i => ?_
  fin_cases i <;> (dsimp; fun_prop)

private theorem cross3_cross3 (a b c : Fin 3 → ℝ) (i : Fin 3) :
    cross3 a (cross3 b c) i = dot3 a c * b i - dot3 a b * c i := by
  fin_cases i <;> (dsimp [cross3, dot3]; ring)

/-- Vector triple product consequence: if `c · a = 0` and `c · b = 0`, then
`‖c‖ ^ 2 * (v · (a × b)) ^ 2 = (c · v) ^ 2 * ‖a × b‖ ^ 2`. -/
private theorem mul_sq_dot3_cross3_eq {c v a b : Fin 3 → ℝ} (hca : dot3 c a = 0)
    (hcb : dot3 c b = 0) :
    normSq3 c * (dot3 v (cross3 a b)) ^ 2 = (dot3 c v) ^ 2 * normSq3 (cross3 a b) := by
  have hc0 (i : Fin 3) : cross3 c (cross3 a b) i = 0 := by
    rw [cross3_cross3, hcb, hca]; ring
  have hv (i : Fin 3) : dot3 v (cross3 a b) * c i = dot3 c v * cross3 a b i := by
    have h := cross3_cross3 v c (cross3 a b) i
    rw [show cross3 c (cross3 a b) = 0 from funext hc0,
      show cross3 v 0 i = 0 by fin_cases i <;> simp [cross3]] at h
    dsimp [dot3] at h ⊢; linarith
  calc normSq3 c * (dot3 v (cross3 a b)) ^ 2
      = ∑ i : Fin 3, (dot3 v (cross3 a b) * c i) ^ 2 := by
        rw [Fin.sum_univ_three]; dsimp [normSq3]; ring
    _ = ∑ i : Fin 3, (dot3 c v * cross3 a b i) ^ 2 := by simp_rw [hv]
    _ = (dot3 c v) ^ 2 * normSq3 (cross3 a b) := by
        rw [Fin.sum_univ_three]; dsimp [normSq3]; ring

/-- Denominator-free Householder vector mapping a unit vector `u` to `(±1, 0, 0)`. -/
private noncomputable def householderVec (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  if u 0 ≤ 0 then ![u 0 - 1, u 1, u 2] else ![u 0 + 1, u 1, u 2]

private theorem two_le_normSq3_householderVec {u : Fin 3 → ℝ} (hu : normSq3 u = 1) :
    2 ≤ normSq3 (householderVec u) := by
  dsimp [householderVec, normSq3] at hu ⊢
  split_ifs <;> (dsimp; linarith)

/-- Householder reflection across `householderVec u`. -/
private noncomputable def householder (u x : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let w := householderVec u
  fun i => x i - 2 / normSq3 w * dot3 w x * w i

private theorem dot3_householder {u : Fin 3 → ℝ} (hu : normSq3 u = 1) (x y : Fin 3 → ℝ) :
    dot3 (householder u x) (householder u y) = dot3 x y := by
  have hw : normSq3 (householderVec u) ≠ 0 := by linarith [two_le_normSq3_householderVec hu]
  dsimp [householder, normSq3, dot3] at hw ⊢
  field_simp [hw]
  ring

private theorem normSq3_householder {u : Fin 3 → ℝ} (hu : normSq3 u = 1) (y : Fin 3 → ℝ) :
    normSq3 (householder u y) = normSq3 y := by
  simpa [normSq3, dot3, sq] using dot3_householder hu y y

private theorem householder_involutive {u : Fin 3 → ℝ} (hu : normSq3 u = 1) (x : Fin 3 → ℝ) :
    householder u (householder u x) = x := by
  have hw : normSq3 (householderVec u) ≠ 0 := by linarith [two_le_normSq3_householderVec hu]
  ext i
  fin_cases i <;>
    (dsimp [householder, normSq3, dot3] at hw ⊢; field_simp [hw]; ring)

private theorem householder_eq_zero_iff {u : Fin 3 → ℝ} (hu : normSq3 u = 1) (y : Fin 3 → ℝ) :
    householder u y = 0 ↔ y = 0 := by
  have hz : householder u 0 = 0 := by ext i; fin_cases i <;> simp [householder, dot3]
  refine ⟨fun h => ?_, fun h => h ▸ hz⟩
  rw [← householder_involutive hu y, h, hz]

private theorem sq_householder_zero_eq_sq_dot3 {u : Fin 3 → ℝ} (hu : normSq3 u = 1)
    (y : Fin 3 → ℝ) : (householder u y 0) ^ 2 = (dot3 u y) ^ 2 := by
  dsimp [householder, householderVec]
  split_ifs with h0
  · have hN : normSq3 ![u 0 - 1, u 1, u 2] = 2 * (1 - u 0) := by
      dsimp [normSq3] at hu ⊢; linarith
    have h1 : 1 - u 0 ≠ 0 := by linarith
    rw [hN]; dsimp [dot3]; field_simp [h1]; ring
  · have hN : normSq3 ![u 0 + 1, u 1, u 2] = 2 * (1 + u 0) := by
      dsimp [normSq3] at hu ⊢; linarith
    have h1 : 1 + u 0 ≠ 0 := by linarith
    rw [hN]; dsimp [dot3]; field_simp [h1]; ring

private theorem cross3_householder {u : Fin 3 → ℝ} (hu : normSq3 u = 1) (a b : Fin 3 → ℝ) :
    cross3 (householder u a) (householder u b) = -householder u (cross3 a b) := by
  have hw : normSq3 (householderVec u) ≠ 0 := by linarith [two_le_normSq3_householderVec hu]
  ext i
  fin_cases i <;>
    (dsimp [cross3, householder, normSq3, dot3, Pi.neg_apply] at hw ⊢; field_simp [hw]; ring)

private theorem cone_iff_householder_unitVec3 {x : Fin 3 → ℝ} (hx : x ≠ 0) (y : Fin 3 → ℝ)
    (κ : ℝ) :
    κ ^ 2 * normSq3 x * normSq3 y ≤ (dot3 x y) ^ 2 ↔
      κ ^ 2 * normSq3 (householder (unitVec3 x) y) ≤ (householder (unitVec3 x) y 0) ^ 2 := by
  have hnx : 0 < normSq3 x := normSq3_pos_of_ne_zero hx
  have hux : normSq3 (unitVec3 x) = 1 := normSq3_unitVec3 hnx
  rw [normSq3_householder hux, sq_householder_zero_eq_sq_dot3 hux]
  have hdot : (dot3 (unitVec3 x) y) ^ 2 = (normSq3 x)⁻¹ * (dot3 x y) ^ 2 := by
    calc (dot3 (unitVec3 x) y) ^ 2
        = ((√(normSq3 x))⁻¹) ^ 2 * (dot3 x y) ^ 2 := by dsimp [unitVec3, dot3]; ring
      _ = (normSq3 x)⁻¹ * (dot3 x y) ^ 2 := by rw [inv_pow, sq_sqrt hnx.le]
  rw [hdot, inv_mul_eq_div, le_div_iff₀ hnx]
  exact ⟨fun h => by linarith only [h], fun h => by linarith only [h]⟩

private theorem measurePreserving_householder {u : Fin 3 → ℝ} (hu : normSq3 u = 1) :
    MeasurePreserving (householder u) P3Measure P3Measure := by
  let e (i : Fin 3) : Fin 3 → ℝ := Pi.single i 1
  let r (i : Fin 3) : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (householder u (e i))
  have hinner_lp (a b : Fin 3 → ℝ) : ⟪WithLp.toLp 2 a, WithLp.toLp 2 b⟫ = dot3 a b := by
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [star_trivial, dotProduct, Fin.sum_univ_three, dot3]
    ring
  have hsymm (i : Fin 3) (x : Fin 3 → ℝ) : householder u x i = ⟪r i, WithLp.toLp 2 x⟫ := by
    have he1 : dot3 (e i) (householder u x) = householder u x i := by
      fin_cases i <;> simp [dot3, e]
    rw [hinner_lp]
    have hdot' := dot3_householder hu (e i) (householder u x)
    rw [householder_involutive hu x, he1] at hdot'
    exact hdot'.symm
  have hr_norm (i : Fin 3) : ‖r i‖ = 1 := by
    rw [norm_eq_sqrt_real_inner, hinner_lp, dot3_householder hu (e i) (e i)]
    have he : dot3 (e i) (e i) = 1 := by fin_cases i <;> simp [dot3, e]
    simp [he]
  have hr_orth : Pairwise fun i j => ⟪r i, r j⟫ = 0 := by
    intro i j hij
    rw [hinner_lp, dot3_householder hu (e i) (e j)]
    fin_cases i <;> fin_cases j <;> simp_all [dot3, e]
  have hcomp : householder u = (fun y i => ⟪r i, y⟫) ∘ WithLp.toLp 2 := by
    funext x i; exact hsymm i x
  refine ⟨by unfold householder householderVec normSq3 dot3; fun_prop, ?_⟩
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
    (measurePreserving_toLp_pi_gaussianReal (Fin 3)).map_eq]
  exact stdGaussian_map_inner_pi hr_norm hr_orth

private theorem p3Measure_prod_cross3_eq_zero :
    (P3Measure.prod P3Measure) {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) | cross3 ab.1 ab.2 = 0} = 0 := by
  have hsub : {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) | cross3 ab.1 ab.2 = 0} ⊆
      {ab | ab.1 0 * ab.2 1 - ab.1 1 * ab.2 0 = 0} := fun ab hab => by
    simpa [cross3] using congrFun hab 2
  refine measure_mono_null hsub ?_
  rw [Measure.prod_apply (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [Measure.ae_eval_ne _ (0 : Fin 3) 0] with a ha0
  let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![-a 1, a 0, 0]
  have hw : w ≠ 0 := fun hzero => ha0 (by simpa [w] using congrArg (fun v => v.ofLp 1) hzero)
  let Sw : Set (EuclideanSpace ℝ (Fin 3)) := {y | ⟪w, y⟫ ∈ ({0} : Set ℝ)}
  have hSw : MeasurableSet Sw := (measurableSet_singleton 0).preimage (by fun_prop)
  have hset : {b : Fin 3 → ℝ | a 0 * b 1 - a 1 * b 0 = 0} = WithLp.toLp 2 ⁻¹' Sw := by
    ext b
    simp only [mem_ofPred_eq, mem_preimage, Sw, mem_singleton_iff,
      EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct, Fin.sum_univ_three, w]
    dsimp
    exact ⟨fun h => by linarith, fun h => by linarith⟩
  change P3Measure {b | a 0 * b 1 - a 1 * b 0 = 0} = 0
  rw [hset, ← Measure.map_apply (by fun_prop) hSw,
    (measurePreserving_toLp_pi_gaussianReal (Fin 3)).map_eq]
  exact le_antisymm ((stdGaussian_inner_mem_le hw (measurableSet_singleton 0)).trans (by simp))
    bot_le

/-- Planar standard Gaussian probability of the closed disk `{z | z.1 ^ 2 + z.2 ^ 2 ≤ a ^ 2}`
(`0 < a`). -/
private theorem measureReal_prod_gaussianReal_disk {a : ℝ} (ha : 0 < a) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).real
      {z : ℝ × ℝ | z.1 ^ 2 + z.2 ^ 2 ≤ a ^ 2} = 1 - exp (-(a ^ 2) / 2) := by
  let D : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 ≤ a ^ 2}
  have hDm : MeasurableSet D := measurableSet_le (by fun_prop) measurable_const
  let rad : ℝ → ℝ := fun r => (2 * π)⁻¹ * (r * exp (-(r ^ 2) / 2))
  have hdens : ∀ r φ,
      gaussianPDFReal 0 1 (r * cos φ) * gaussianPDFReal 0 1 (r * sin φ) =
        (2 * π)⁻¹ * exp (-(r ^ 2) / 2) := by
    intro r φ
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
    rw [mul_mul_mul_comm, ← mul_inv, mul_self_sqrt (by positivity), ← exp_add]
    congr 2
    linear_combination (-2⁻¹ * r ^ 2) * sin_sq_add_cos_sq φ
  rw [← integral_indicator_one hDm]
  change ∫ z, D.indicator (fun _ => (1 : ℝ)) z ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = _
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
  rw [integral_withDensity_eq_integral_toReal_smul]
  · rw [← Measure.volume_eq_prod, ← integral_comp_polarCoord_symm]
    have hcongr : ∫ p in polarCoord.target, p.1 •
        ((gaussianPDF 0 1 (polarCoord.symm p).1 * gaussianPDF 0 1 (polarCoord.symm p).2).toReal •
          D.indicator (fun _ => (1 : ℝ)) (polarCoord.symm p)) =
        ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
          (Iic a).indicator rad p.1 * (fun _ : ℝ => (1 : ℝ)) p.2 := by
      rw [polarCoord_target]
      refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
      have hD_iff : polarCoord.symm p ∈ D ↔ p.1 ≤ a := by
        simp only [D, polarCoord_symm_apply, mem_ofPred_eq]
        have hsq : (p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2 = p.1 ^ 2 := by
          linear_combination p.1 ^ 2 * sin_sq_add_cos_sq p.2
        rw [hsq]
        have hp1 : 0 < p.1 := hp.1
        exact ⟨fun h => le_of_sq_le_sq h ha.le, fun h => sq_le_sq' (by linarith) h⟩
      simp only [ENNReal.toReal_mul, toReal_gaussianPDF, polarCoord_symm_apply, hdens, smul_eq_mul,
        mul_one]
      by_cases hra : p.1 ≤ a
      · have hmem : (p.1 * cos p.2, p.1 * sin p.2) ∈ D := hD_iff.mpr hra
        simp only [indicator_of_mem hmem, indicator_of_mem (mem_Iic.mpr hra), rad]
        ring
      · have hnmem : (p.1 * cos p.2, p.1 * sin p.2) ∉ D := mt hD_iff.mp hra
        simp [hnmem, hra]
    rw [hcongr, Measure.volume_eq_prod,
      setIntegral_prod_mul (f := (Iic a).indicator rad) (g := fun _ : ℝ => (1 : ℝ))]
    have hang : ∫ _φ in Ioo (-π) π, (1 : ℝ) = 2 * π := by
      rw [setIntegral_const, smul_eq_mul, mul_one, Measure.real, Real.volume_Ioo,
        ENNReal.toReal_ofReal (by linarith [pi_pos])]
      ring
    rw [hang, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioi, ← intervalIntegral.integral_of_le ha.le]
    have hftc : ∫ r in (0 : ℝ)..a, rad r = (2 * π)⁻¹ * (1 - exp (-(a ^ 2) / 2)) := by
      dsimp [rad]
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hderiv : ∀ r ∈ uIcc 0 a,
          HasDerivAt (fun x : ℝ => -exp (-(x ^ 2) / 2)) (r * exp (-(r ^ 2) / 2)) r := by
        intro r _
        have h1 : HasDerivAt (fun x : ℝ => -(x ^ 2) / 2) (-r) r :=
          (((hasDerivAt_pow 2 r).neg).div_const 2).congr_deriv (by ring)
        exact (h1.exp.neg).congr_deriv (by ring)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((by fun_prop : Continuous fun r : ℝ => r * exp (-(r ^ 2) / 2)).intervalIntegrable 0 a)]
      simp only [sq, mul_zero, neg_zero, zero_div, exp_zero]
      ring
    rw [hftc]
    field_simp [pi_pos.ne']
  · exact ((measurable_gaussianPDF 0 1).comp measurable_fst).mul
      ((measurable_gaussianPDF 0 1).comp measurable_snd)
  · exact ae_of_all _ fun _ => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top

/-- Single 3D standard Gaussian double-cone probability:
`P3Measure.real {x | x ≠ 0 ∧ κ ^ 2 * normSq3 x ≤ (x 0) ^ 2} = 1 - κ` for `0 < κ ≤ 1`. -/
private theorem p3Measure_cone_eq {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    P3Measure.real {x : Fin 3 → ℝ | x ≠ 0 ∧ κ ^ 2 * normSq3 x ≤ (x 0) ^ 2} = 1 - κ := by
  let split3 : (Fin 3 → ℝ) → ℝ × (ℝ × ℝ) := fun x => (x 0, (x 1, x 2))
  have hmp : MeasurePreserving split3 P3Measure
      ((gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1))) := by
    have h := ((MeasurePreserving.id (gaussianReal 0 1)).prod
      (measurePreserving_finTwoArrow (gaussianReal 0 1))).comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin 3 => gaussianReal 0 1) 0)
    refine ⟨by unfold split3; fun_prop, ?_⟩
    simpa [split3, Function.comp_def, Fin.tail] using h.map_eq
  rcases eq_or_lt_of_le hκ1 with rfl | hκ_lt
  · have hsub : {x : Fin 3 → ℝ | x ≠ 0 ∧ (1 : ℝ) ^ 2 * normSq3 x ≤ (x 0) ^ 2} ⊆
        {x | x 1 = 0} := fun x ⟨_, hx⟩ => by
      dsimp [normSq3] at hx
      exact sq_eq_zero_iff.mp (by linarith [sq_nonneg (x 1), sq_nonneg (x 2)])
    rw [Measure.real, measure_mono_null hsub (Measure.pi_hyperplane _ 1 0)]
    simp
  · set c : ℝ := √(1 - κ ^ 2) / κ
    have h1_sub_pos : 0 < 1 - κ ^ 2 := by nlinarith
    have hc_pos : 0 < c := div_pos (sqrt_pos.mpr h1_sub_pos) hκ0
    have hc_sq : c ^ 2 = (1 - κ ^ 2) / κ ^ 2 := by
      dsimp [c]; rw [div_pow, sq_sqrt h1_sub_pos.le]
    let ConeP : Set (ℝ × (ℝ × ℝ)) :=
      {p | p.1 ≠ 0 ∧ p.2.1 ^ 2 + p.2.2 ^ 2 ≤ (c * |p.1|) ^ 2}
    have hConePm : MeasurableSet ConeP :=
      ((measurableSet_singleton 0).compl.preimage measurable_fst).inter
        (measurableSet_le (f := fun p : ℝ × (ℝ × ℝ) => p.2.1 ^ 2 + p.2.2 ^ 2)
          (g := fun p : ℝ × (ℝ × ℝ) => (c * |p.1|) ^ 2) (by fun_prop) (by fun_prop))
    have hpre : {x : Fin 3 → ℝ | x ≠ 0 ∧ κ ^ 2 * normSq3 x ≤ (x 0) ^ 2} = split3 ⁻¹' ConeP := by
      ext x
      have hκ2_pos : 0 < κ ^ 2 := pow_pos hκ0 2
      have hx0_of : x ≠ 0 → κ ^ 2 * normSq3 x ≤ (x 0) ^ 2 → x 0 ≠ 0 := fun hx hle h0 => by
        linarith [mul_pos hκ2_pos (normSq3_pos_of_ne_zero hx), show (x 0) ^ 2 = 0 by simp [h0]]
      simp only [mem_ofPred_eq, mem_preimage, ConeP, split3]
      rw [mul_pow, sq_abs, hc_sq, div_mul_eq_mul_div, le_div_iff₀ hκ2_pos]
      refine ⟨fun ⟨hx, hle⟩ => ⟨hx0_of hx hle, by dsimp [normSq3] at hle; linarith only [hle]⟩,
        fun ⟨hx0, hle⟩ => ⟨fun h => hx0 (by simp [h]), by dsimp [normSq3]; linarith only [hle]⟩⟩
    rw [hpre, hmp.measureReal_preimage hConePm.nullMeasurableSet]
    set μ2 := (gaussianReal 0 1).prod (gaussianReal 0 1)
    rw [← integral_indicator_one hConePm,
      integral_prod (ConeP.indicator 1) ((integrable_const (1 : ℝ)).indicator hConePm)]
    have hslice : ∀ᵐ x₀ ∂gaussianReal 0 1,
        (∫ z, ConeP.indicator 1 (x₀, z) ∂μ2) = 1 - exp (-((c * |x₀|) ^ 2) / 2) := by
      filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with x₀ hx₀
      change x₀ ≠ 0 at hx₀
      let D : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 ≤ (c * |x₀|) ^ 2}
      have hDm : MeasurableSet D := measurableSet_le (by fun_prop) measurable_const
      have hpre_x : Prod.mk x₀ ⁻¹' ConeP = D := by ext z; simp [ConeP, D, hx₀]
      change (∫ z, (Prod.mk x₀ ⁻¹' ConeP).indicator 1 z ∂μ2) = _
      rw [hpre_x, integral_indicator_one hDm]
      exact measureReal_prod_gaussianReal_disk (mul_pos hc_pos (abs_pos.mpr hx₀))
    rw [integral_congr_ae hslice]
    have hsub_int : ∫ x₀, (1 - exp (-((c * |x₀|) ^ 2) / 2)) ∂gaussianReal 0 1 =
        (∫ _x₀, (1 : ℝ) ∂gaussianReal 0 1) -
          ∫ x₀, exp (-((c * |x₀|) ^ 2) / 2) ∂gaussianReal 0 1 := by
      refine integral_sub (integrable_const 1)
        ((integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x₀ => ?_))
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
      linarith [sq_nonneg (c * |x₀|)]
    rw [hsub_int, integral_const, probReal_univ, one_smul]
    congr 1
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    let vκ : ℝ≥0 := Real.toNNReal (κ ^ 2)
    have hvκ_coe : (vκ : ℝ) = κ ^ 2 := Real.coe_toNNReal _ (sq_nonneg κ)
    have hvκ_ne : vκ ≠ 0 := fun h =>
      (pow_pos hκ0 2).ne' (hvκ_coe ▸ congrArg NNReal.toReal h)
    have hpdf_eq (x₀ : ℝ) :
        (gaussianPDF 0 1 x₀).toReal • exp (-((c * |x₀|) ^ 2) / 2) =
          κ * gaussianPDFReal 0 vκ x₀ := by
      rw [toReal_gaussianPDF, smul_eq_mul, mul_pow, sq_abs]
      simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one, hvκ_coe]
      rw [sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π), sqrt_sq hκ0.le, mul_inv]
      have hpre_fac : κ * ((√(2 * π))⁻¹ * κ⁻¹ * exp (-x₀ ^ 2 / (2 * κ ^ 2))) =
          (√(2 * π))⁻¹ * exp (-x₀ ^ 2 / (2 * κ ^ 2)) := by field_simp [hκ0.ne']
      rw [hpre_fac, mul_assoc, ← exp_add]
      congr 2
      rw [hc_sq]; field_simp [hκ0.ne']; ring
    simp_rw [hpdf_eq]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 hvκ_ne, mul_one]

/-- **Cross-product cap probability in `ℝ³` via Householder–Fubini.** -/
private theorem p3Measure_prod_cross3_cone_eq {v : Fin 3 → ℝ} (hv : normSq3 v = 1)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    (P3Measure.prod P3Measure).real
      {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
        κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 v (cross3 ab.1 ab.2)) ^ 2} = 1 - κ := by
  set M2 := P3Measure.prod P3Measure
  let A_full : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    {ab | κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 v (cross3 ab.1 ab.2)) ^ 2}
  let A_nz : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    {ab | cross3 ab.1 ab.2 ≠ 0 ∧
      κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 v (cross3 ab.1 ab.2)) ^ 2}
  have hfull_eq_nz : M2.real A_full = M2.real A_nz := by
    have hdiff : A_nz = A_full \ {ab | cross3 ab.1 ab.2 = 0} := by
      ext ab; simp only [A_full, A_nz, mem_sdiff, mem_ofPred_eq]; tauto
    rw [hdiff, Measure.real, Measure.real, measure_sdiff_null p3Measure_prod_cross3_eq_zero]
  rw [hfull_eq_nz]
  let A0 : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    {ab | cross3 ab.1 ab.2 ≠ 0 ∧
      κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (cross3 ab.1 ab.2 0) ^ 2}
  have hA0_m : MeasurableSet A0 :=
    (isClosed_singleton.preimage continuous_cross3).measurableSet.compl.inter
      (isClosed_le (continuous_const.mul (continuous_normSq3.comp continuous_cross3))
        (((continuous_apply 0).comp continuous_cross3).pow 2)).measurableSet
  have hnorm_neg (y : Fin 3 → ℝ) : normSq3 (-y) = normSq3 y := by
    dsimp [normSq3, Pi.neg_apply]; ring
  have hsq_neg (y : Fin 3 → ℝ) : ((-y) 0) ^ 2 = (y 0) ^ 2 := by
    dsimp [Pi.neg_apply]; ring
  have hpre_hh {u : Fin 3 → ℝ} (hu : normSq3 u = 1) (a b : Fin 3 → ℝ) :
      Prod.map (householder u) (householder u) (a, b) ∈ A0 ↔
        cross3 a b ≠ 0 ∧
          κ ^ 2 * normSq3 (householder u (cross3 a b)) ≤ (householder u (cross3 a b) 0) ^ 2 := by
    simp only [A0, Prod.map_apply, mem_ofPred_eq, cross3_householder hu, hnorm_neg, hsq_neg,
      ne_eq, neg_eq_zero, householder_eq_zero_iff hu]
  have hAnz_eq_A0 : M2.real A_nz = M2.real A0 := by
    have hpre : Prod.map (householder v) (householder v) ⁻¹' A0 = A_nz := by
      ext ⟨a, b⟩
      simp only [mem_preimage, hpre_hh hv, A_nz, mem_ofPred_eq, normSq3_householder hv,
        sq_householder_zero_eq_sq_dot3 hv]
    rw [← hpre, ((measurePreserving_householder hv).prod
      (measurePreserving_householder hv)).measureReal_preimage hA0_m.nullMeasurableSet]
  rw [hAnz_eq_A0]
  let Joint : Set (((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ)) :=
    {abx | cross3 abx.1.1 abx.1.2 ≠ 0 ∧ abx.2 ≠ 0 ∧
      κ ^ 2 * normSq3 abx.2 * normSq3 (cross3 abx.1.1 abx.1.2) ≤
        (dot3 abx.2 (cross3 abx.1.1 abx.1.2)) ^ 2}
  have hJoint_m : MeasurableSet Joint := by
    have hc1 : Continuous fun abx : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ) =>
        cross3 abx.1.1 abx.1.2 := continuous_cross3.comp continuous_fst
    have hdot2 : Continuous fun abx : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ) =>
        dot3 abx.2 (cross3 abx.1.1 abx.1.2) := by unfold dot3; fun_prop
    exact (isClosed_singleton.preimage hc1).measurableSet.compl.inter
      ((isClosed_singleton.preimage continuous_snd).measurableSet.compl.inter
        (isClosed_le ((continuous_const.mul (continuous_normSq3.comp continuous_snd)).mul
          (continuous_normSq3.comp hc1)) (hdot2.pow 2)).measurableSet)
  have hJoint_int : Integrable (Joint.indicator 1) (M2.prod P3Measure) :=
    (integrable_const (1 : ℝ)).indicator hJoint_m
  -- Slice 1: integrate over `ab` first for fixed `x ≠ 0`.
  have hslice_x : ∀ᵐ x ∂P3Measure,
      (∫ ab, Joint.indicator 1 (ab, x) ∂M2) = M2.real A0 := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : Fin 3 → ℝ))] with x hx0
    change x ≠ 0 at hx0
    have hux : normSq3 (unitVec3 x) = 1 := normSq3_unitVec3 (normSq3_pos_of_ne_zero hx0)
    have hpre_x : (fun ab => (ab, x)) ⁻¹' Joint =
        Prod.map (householder (unitVec3 x)) (householder (unitVec3 x)) ⁻¹' A0 := by
      ext ⟨a, b⟩
      simp only [mem_preimage, hpre_hh hux, Joint, mem_ofPred_eq,
        cone_iff_householder_unitVec3 hx0]
      exact ⟨fun ⟨h1, _, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, hx0, h2⟩⟩
    change (∫ ab, ((fun ab => (ab, x)) ⁻¹' Joint).indicator 1 ab ∂M2) = M2.real A0
    rw [hpre_x, integral_indicator_one
      (hA0_m.preimage ((measurePreserving_householder hux).measurable.prodMap
        (measurePreserving_householder hux).measurable)),
      ((measurePreserving_householder hux).prod
        (measurePreserving_householder hux)).measureReal_preimage hA0_m.nullMeasurableSet]
  -- Slice 2: integrate over `x` first for fixed `ab` with `cross3 ab.1 ab.2 ≠ 0`.
  have hslice_ab : ∀ᵐ ab ∂M2,
      (∫ x, Joint.indicator 1 (ab, x) ∂P3Measure) = 1 - κ := by
    filter_upwards [compl_mem_ae_iff.mpr p3Measure_prod_cross3_eq_zero] with ⟨a, b⟩ hc
    change cross3 a b ≠ 0 at hc
    set C := cross3 a b
    have huC : normSq3 (unitVec3 C) = 1 := normSq3_unitVec3 (normSq3_pos_of_ne_zero hc)
    let ConeX : Set (Fin 3 → ℝ) := {x | x ≠ 0 ∧ κ ^ 2 * normSq3 x ≤ (x 0) ^ 2}
    have hConeXm : MeasurableSet ConeX :=
      isClosed_singleton.measurableSet.compl.inter
        (isClosed_le (continuous_const.mul continuous_normSq3)
          ((continuous_apply 0).pow 2)).measurableSet
    have hpre_ab : Prod.mk (a, b) ⁻¹' Joint = householder (unitVec3 C) ⁻¹' ConeX := by
      ext x
      have hiff : κ ^ 2 * normSq3 x * normSq3 C ≤ (dot3 x C) ^ 2 ↔
          κ ^ 2 * normSq3 (householder (unitVec3 C) x) ≤ (householder (unitVec3 C) x 0) ^ 2 := by
        rw [dot3_comm, mul_right_comm, cone_iff_householder_unitVec3 hc]
      simp only [mem_preimage, Joint, ConeX, mem_ofPred_eq, ne_eq, householder_eq_zero_iff huC]
      change (C ≠ 0 ∧ x ≠ 0 ∧ κ ^ 2 * normSq3 x * normSq3 C ≤ (dot3 x C) ^ 2) ↔ _
      rw [hiff]
      exact ⟨fun ⟨_, h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨hc, h1, h2⟩⟩
    change (∫ x, (Prod.mk (a, b) ⁻¹' Joint).indicator 1 x ∂P3Measure) = 1 - κ
    rw [hpre_ab, integral_indicator_one
      (hConeXm.preimage (measurePreserving_householder huC).measurable),
      (measurePreserving_householder huC).measureReal_preimage hConeXm.nullMeasurableSet,
      p3Measure_cone_eq hκ0 hκ1]
  have hint1 : ∫ z, Joint.indicator 1 z ∂(M2.prod P3Measure) = M2.real A0 := by
    rw [integral_prod_symm _ hJoint_int, integral_congr_ae hslice_x,
      integral_const, probReal_univ, one_smul]
  have hint2 : ∫ z, Joint.indicator 1 z ∂(M2.prod P3Measure) = 1 - κ := by
    rw [integral_prod _ hJoint_int, integral_congr_ae hslice_ab,
      integral_const, probReal_univ, one_smul]
  exact hint1.symm.trans hint2

end R3

/-! ### Three-step Gram–Schmidt with three spare orthogonal coordinates -/

section GramSchmidt

private noncomputable def bSpare (d : ℕ) (j : Fin 3) : EuclideanSpace ℝ (Fin d ⊕ Fin 3) :=
  EuclideanSpace.single (Sum.inr j) 1

private theorem orthonormal_bSpare (d : ℕ) : Orthonormal ℝ (bSpare d) :=
  EuclideanSpace.orthonormal_single.comp Sum.inr Sum.inr_injective

private theorem exists_unit_perp_fin {d k : ℕ} (hk : k < 3)
    {e : Fin k → EuclideanSpace ℝ (Fin d ⊕ Fin 3)} (he : Orthonormal ℝ e)
    (v : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
    ∃ u : EuclideanSpace ℝ (Fin d ⊕ Fin 3),
      ‖u‖ = 1 ∧ (∀ i, ⟪e i, u⟫ = 0) ∧
        v = (∑ i : Fin k, ⟪e i, v⟫ • e i) + ⟪u, v⟫ • u := by
  let orth (w : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) := w - ∑ i : Fin k, ⟪e i, w⟫ • e i
  have horth_inner (w : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) (i : Fin k) : ⟪e i, orth w⟫ = 0 := by
    rw [inner_sub_right, he.inner_right_fintype, sub_self]
  have hunit {w : EuclideanSpace ℝ (Fin d ⊕ Fin 3)} (hw : orth w ≠ 0) :
      ‖‖orth w‖⁻¹ • orth w‖ = 1 ∧ ∀ i, ⟪e i, ‖orth w‖⁻¹ • orth w⟫ = 0 := by
    have hn : 0 < ‖orth w‖ := norm_pos_iff.mpr hw
    exact ⟨by rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne'],
      fun i => by rw [inner_smul_right, horth_inner, mul_zero]⟩
  by_cases hv : orth v ≠ 0
  · obtain ⟨hu_norm, hu_orth⟩ := hunit hv
    have hn : 0 < ‖orth v‖ := norm_pos_iff.mpr hv
    let u := ‖orth v‖⁻¹ • orth v
    refine ⟨u, hu_norm, hu_orth, ?_⟩
    have hv_eq : v = orth v + ∑ i : Fin k, ⟪e i, v⟫ • e i := (sub_add_cancel _ _).symm
    have hinner : ⟪u, v⟫ = ‖orth v‖⁻¹ * ‖orth v‖ ^ 2 := by
      rw [show ⟪u, v⟫ = ⟪u, orth v + ∑ i : Fin k, ⟪e i, v⟫ • e i⟫ by rw [← hv_eq],
        inner_add_right, inner_sum]
      have h0 : ∑ i : Fin k, ⟪u, ⟪e i, v⟫ • e i⟫ = 0 :=
        Finset.sum_eq_zero fun i _ => by
          rw [inner_smul_right, real_inner_comm (e i) u, hu_orth i, mul_zero]
      rw [h0, add_zero]
      dsimp [u]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [u]
    rw [hinner, smul_smul, show ‖orth v‖⁻¹ * ‖orth v‖ ^ 2 * ‖orth v‖⁻¹ = 1 by field_simp [hn.ne'],
      one_smul, add_sub_cancel]
  · push Not at hv
    have hv_eq : v = ∑ i : Fin k, ⟪e i, v⟫ • e i := sub_eq_zero.mp hv
    have hex : ∃ j : Fin 3, orth (bSpare d j) ≠ 0 := by
      by_contra! hall
      have hsq (j : Fin 3) : 1 = ∑ i : Fin k, ⟪bSpare d j, e i⟫ ^ 2 := by
        have hj : bSpare d j = ∑ i : Fin k, ⟪e i, bSpare d j⟫ • e i := sub_eq_zero.mp (hall j)
        have h1 : ⟪bSpare d j, bSpare d j⟫ = 1 := by
          rw [real_inner_self_eq_norm_sq, (orthonormal_bSpare d).1 j, one_pow]
        conv_lhs at h1 => rw [hj]
        rw [he.inner_sum] at h1
        simpa [sq, real_inner_comm (e _)] using h1.symm
      have h3 : (3 : ℝ) = ∑ i : Fin k, ∑ j : Fin 3, ⟪bSpare d j, e i⟫ ^ 2 := by
        rw [← Finset.sum_comm]; simp_rw [← hsq]; norm_num
      have hle : ∑ i : Fin k, ∑ j : Fin 3, ⟪bSpare d j, e i⟫ ^ 2 ≤ k := by
        calc ∑ i : Fin k, ∑ j : Fin 3, ⟪bSpare d j, e i⟫ ^ 2
            ≤ ∑ i : Fin k, ‖e i‖ ^ 2 := Finset.sum_le_sum fun i _ => by
              simpa using (orthonormal_bSpare d).sum_inner_products_le (e i) (s := Finset.univ)
          _ = k := by simp [he.1]
      have hkR : (k : ℝ) < 3 := by exact_mod_cast hk
      linarith
    obtain ⟨j, hj⟩ := hex
    obtain ⟨hu_norm, hu_orth⟩ := hunit hj
    let u := ‖orth (bSpare d j)‖⁻¹ • orth (bSpare d j)
    refine ⟨u, hu_norm, hu_orth, ?_⟩
    have huv : ⟪u, v⟫ = 0 := by
      rw [show ⟪u, v⟫ = ⟪u, ∑ i : Fin k, ⟪e i, v⟫ • e i⟫ by rw [← hv_eq], inner_sum]
      exact Finset.sum_eq_zero fun i _ => by
        rw [inner_smul_right, real_inner_comm (e i) u, hu_orth i, mul_zero]
    rw [huv, zero_smul, add_zero, ← hv_eq]

private theorem exists_orthonormal_fin3_span {d : ℕ}
    (v₀ v₁ v₂ : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
    ∃ e : Fin 3 → EuclideanSpace ℝ (Fin d ⊕ Fin 3),
      Orthonormal ℝ e ∧
        (v₀ = ∑ k : Fin 3, ⟪e k, v₀⟫ • e k) ∧
        (v₁ = ∑ k : Fin 3, ⟪e k, v₁⟫ • e k) ∧
        (v₂ = ∑ k : Fin 3, ⟪e k, v₂⟫ • e k) := by
  obtain ⟨e₀, he₀, -, hv₀⟩ := exists_unit_perp_fin (k := 0) (by omega)
    (Orthonormal.of_isEmpty Fin.elim0) v₀
  have horth₁ : Orthonormal ℝ ![e₀] := by simp [he₀]
  obtain ⟨e₁, he₁, h01, hv₁⟩ := exists_unit_perp_fin (k := 1) (by omega) horth₁ v₁
  have h10 : ⟪e₁, e₀⟫ = 0 := by simpa [real_inner_comm] using h01 0
  have horth₂ : Orthonormal ℝ ![e₁, e₀] := by
    rw [orthonormal_vecCons_iff]
    exact ⟨he₁, Fin.forall_fin_one.mpr h10, horth₁⟩
  obtain ⟨e₂, he₂, h12, hv₂⟩ := exists_unit_perp_fin (k := 2) (by omega) horth₂ v₂
  have h21 : ⟪e₂, e₁⟫ = 0 := by simpa [real_inner_comm] using h12 0
  have h20 : ⟪e₂, e₀⟫ = 0 := by simpa [real_inner_comm] using h12 1
  have horth₃ : Orthonormal ℝ ![e₂, e₁, e₀] := by
    rw [orthonormal_vecCons_iff]
    exact ⟨he₂, Fin.forall_fin_two.mpr ⟨h21, h20⟩, horth₂⟩
  refine ⟨![e₂, e₁, e₀], horth₃, ?_, ?_, ?_⟩
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_add] at hv₀
    rw [Fin.sum_univ_three]
    dsimp
    have h1 : ⟪e₁, v₀⟫ = 0 := by rw [hv₀, inner_smul_right, h10, mul_zero]
    have h2 : ⟪e₂, v₀⟫ = 0 := by rw [hv₀, inner_smul_right, h20, mul_zero]
    rw [h1, h2, zero_smul, zero_smul, zero_add, zero_add]
    exact hv₀
  · rw [Fin.sum_univ_one] at hv₁
    rw [Fin.sum_univ_three]
    dsimp at hv₁ ⊢
    have h2 : ⟪e₂, v₁⟫ = 0 := by
      rw [hv₁, inner_add_right, inner_smul_right, inner_smul_right, h20, h21, mul_zero, mul_zero,
        add_zero]
    rw [h2, zero_smul, zero_add, add_comm]
    exact hv₁
  · rw [Fin.sum_univ_two] at hv₂
    rw [Fin.sum_univ_three]
    dsimp at hv₂ ⊢
    abel_nf at hv₂ ⊢
    exact hv₂

end GramSchmidt

/-! ### Main planar Gaussian convex-hull theorem -/

/-- **Planar Gaussian projections of three vectors in a spherical cap.** Let `x` be a unit vector
of `E`, and let `y₀, y₁, y₂ : E` have norm at most `1` and inner product at least `κ` (`0 < κ ≤ 1`)
with `x`. Under two independent draws `(X₁, X₂) ~ (stdGaussian E).prod (stdGaussian E)`, `(0, 0)`
lies in the triangle `conv((⟪y₀, X₁⟫, ⟪y₀, X₂⟫), (⟪y₁, X₁⟫, ⟪y₁, X₂⟫), (⟪y₂, X₁⟫, ⟪y₂, X₂⟫))`
with probability at most `1 - κ`. -/
theorem measureReal_stdGaussian_prod_convex_zero_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {x y₀ y₁ y₂ : E} (hx : ‖x‖ = 1)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hy₀ : κ ≤ ⟪y₀, x⟫) (hy₁ : κ ≤ ⟪y₁, x⟫) (hy₂ : κ ≤ ⟪y₂, x⟫)
    (hnorm₀ : ‖y₀‖ ≤ 1) (hnorm₁ : ‖y₁‖ ≤ 1) (hnorm₂ : ‖y₂‖ ≤ 1) :
    ((stdGaussian E).prod (stdGaussian E)).real
      {p : E × E | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * ⟪y₀, p.1⟫ + w₁ * ⟪y₁, p.1⟫ + w₂ * ⟪y₂, p.1⟫ = 0 ∧
        w₀ * ⟪y₀, p.2⟫ + w₁ * ⟪y₁, p.2⟫ + w₂ * ⟪y₂, p.2⟫ = 0} ≤ 1 - κ := by
  let d := Module.finrank ℝ E
  let b : OrthonormalBasis (Fin d) ℝ E := stdOrthonormalBasis ℝ E
  let emb (z : E) : EuclideanSpace ℝ (Fin d ⊕ Fin 3) :=
    WithLp.toLp 2 (Sum.elim (fun i => ⟪b i, z⟫) 0)
  have hemb_inner (z₁ z₂ : E) : ⟪emb z₁, emb z₂⟫ = ⟪z₁, z₂⟫ := by
    dsimp only [emb]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [star_trivial, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
    calc ∑ i : Fin d, ⟪b i, z₂⟫ * ⟪b i, z₁⟫
        = ∑ i : Fin d, ⟪z₁, b i⟫ * ⟪b i, z₂⟫ :=
          Finset.sum_congr rfl fun i _ => by rw [real_inner_comm (b i) z₁, mul_comm]
      _ = ⟪z₁, z₂⟫ := b.sum_inner_mul_inner z₁ z₂
  let coordE (z : E) : Fin d → ℝ := fun i => ⟪b i, z⟫
  let coordF (w : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) : Fin d → ℝ :=
    fun i => ⟪EuclideanSpace.single (Sum.inl i) 1, w⟫
  have hmpE : MeasurePreserving coordE (stdGaussian E)
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
    ⟨by unfold coordE; fun_prop, stdGaussian_map_inner_pi b.orthonormal.1 b.orthonormal.2⟩
  have hmpF : MeasurePreserving coordF (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3)))
      (Measure.pi fun _ : Fin d => gaussianReal 0 1) := by
    have horth := EuclideanSpace.orthonormal_single
      (𝕜 := ℝ) (ι := Fin d ⊕ Fin 3) |>.comp Sum.inl Sum.inl_injective
    exact ⟨by unfold coordF; fun_prop, stdGaussian_map_inner_pi horth.1 horth.2⟩
  let fR (y : E) (ξ : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ × ℝ :=
    (∑ i, ⟪b i, y⟫ * ξ.1 i, ∑ i, ⟪b i, y⟫ * ξ.2 i)
  let ConvR : Set ((Fin d → ℝ) × (Fin d → ℝ)) := convexZeroSet (fR y₀) (fR y₁) (fR y₂)
  have hConvRm : MeasurableSet ConvR :=
    measurableSet_convex_zero_three (f₀ := fR y₀) (f₁ := fR y₁) (f₂ := fR y₂)
      (by unfold fR; fun_prop) (by unfold fR; fun_prop) (by unfold fR; fun_prop)
  have hinner_coordE (y z : E) : ⟪y, z⟫ = ∑ i : Fin d, ⟪b i, y⟫ * coordE z i := by
    simpa [coordE, real_inner_comm (b _)] using (b.sum_inner_mul_inner y z).symm
  have hinner_coordF (y : E) (w : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
      ⟪emb y, w⟫ = ∑ i : Fin d, ⟪b i, y⟫ * coordF w i := by
    dsimp only [emb, coordF]
    rw [EuclideanSpace.inner_toLp_toLp]
    simp only [star_trivial, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero, EuclideanSpace.inner_single_left,
      map_one, one_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  let fF (y : E) (q : EuclideanSpace ℝ (Fin d ⊕ Fin 3) × EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
      ℝ × ℝ := (⟪emb y, q.1⟫, ⟪emb y, q.2⟫)
  have hmeas_eq : ((stdGaussian E).prod (stdGaussian E)).real
      (convexZeroSet (fun p => (⟪y₀, p.1⟫, ⟪y₀, p.2⟫))
        (fun p => (⟪y₁, p.1⟫, ⟪y₁, p.2⟫)) (fun p => (⟪y₂, p.1⟫, ⟪y₂, p.2⟫))) =
      ((stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3)))).real
      (convexZeroSet (fF y₀) (fF y₁) (fF y₂)) := by
    have hpreE : Prod.map coordE coordE ⁻¹' ConvR =
        convexZeroSet (fun p => (⟪y₀, p.1⟫, ⟪y₀, p.2⟫))
          (fun p => (⟪y₁, p.1⟫, ⟪y₁, p.2⟫)) (fun p => (⟪y₂, p.1⟫, ⟪y₂, p.2⟫)) := by
      ext p; dsimp only [ConvR, convexZeroSet, fR]; simp [← hinner_coordE]
    have hpreF : Prod.map coordF coordF ⁻¹' ConvR = convexZeroSet (fF y₀) (fF y₁) (fF y₂) := by
      ext q; dsimp only [ConvR, convexZeroSet, fR, fF]; simp [← hinner_coordF]
    rw [← hpreE, ← hpreF, (hmpE.prod hmpE).measureReal_preimage hConvRm.nullMeasurableSet,
      (hmpF.prod hmpF).measureReal_preimage hConvRm.nullMeasurableSet]
  change ((stdGaussian E).prod (stdGaussian E)).real
    (convexZeroSet (fun p => (⟪y₀, p.1⟫, ⟪y₀, p.2⟫))
      (fun p => (⟪y₁, p.1⟫, ⟪y₁, p.2⟫)) (fun p => (⟪y₂, p.1⟫, ⟪y₂, p.2⟫))) ≤ 1 - κ
  rw [hmeas_eq]
  obtain ⟨e, he, hspan₀, hspan₁, hspan₂⟩ :=
    exists_orthonormal_fin3_span (emb y₀) (emb y₁) (emb y₂)
  let proj3 (w : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) : Fin 3 → ℝ := fun k => ⟪e k, w⟫
  have hnormSq_proj_le (z : E) (hz : ‖z‖ ≤ 1) : normSq3 (proj3 (emb z)) ≤ 1 := by
    have hbessel := he.sum_inner_products_le (emb z) (s := Finset.univ)
    rw [Fin.sum_univ_three] at hbessel
    simp only [Real.norm_eq_abs, sq_abs] at hbessel
    have hemb_sq : ‖emb z‖ ^ 2 ≤ 1 := by
      rw [← real_inner_self_eq_norm_sq, hemb_inner, real_inner_self_eq_norm_sq]
      exact pow_le_one₀ (norm_nonneg z) hz
    dsimp [normSq3, proj3]
    linarith only [hbessel, hemb_sq]
  let vx : Fin 3 → ℝ := proj3 (emb x)
  have hvx_le : normSq3 vx ≤ 1 := hnormSq_proj_le x hx.le
  let cy : Fin 3 → Fin 3 → ℝ := ![proj3 (emb y₀), proj3 (emb y₁), proj3 (emb y₂)]
  have hinner_proj (y : E) (hsp : emb y = ∑ k : Fin 3, ⟪e k, emb y⟫ • e k)
      (q : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
      ⟪emb y, q⟫ = dot3 (proj3 (emb y)) (proj3 q) := by
    conv_lhs => rw [hsp, Fin.sum_univ_three]
    simp [inner_add_left, real_inner_smul_left, dot3, proj3]
  have hdot_vx (y : E) (hsp : emb y = ∑ k : Fin 3, ⟪e k, emb y⟫ • e k) :
      dot3 (proj3 (emb y)) vx = ⟪y, x⟫ := by
    rw [← hemb_inner y x, hinner_proj y hsp (emb x)]
  have hcy0_vx : κ ≤ dot3 (cy 0) vx := by simpa [cy, hdot_vx y₀ hspan₀] using hy₀
  have hcy1_vx : κ ≤ dot3 (cy 1) vx := by simpa [cy, hdot_vx y₁ hspan₁] using hy₁
  have hcy2_vx : κ ≤ dot3 (cy 2) vx := by simpa [cy, hdot_vx y₂ hspan₂] using hy₂
  have hvx_pos : 0 < normSq3 vx := by
    have hid : normSq3 (cy 0) * normSq3 vx - (dot3 (cy 0) vx) ^ 2 =
        normSq3 (cross3 (cy 0) vx) := by dsimp [dot3, normSq3, cross3]; ring
    have h0 : normSq3 (cy 0) ≤ 1 := hnormSq_proj_le y₀ hnorm₀
    linarith [normSq3_nonneg (cross3 (cy 0) vx), pow_pos hκ0 2, sq_le_sq' (by linarith) hcy0_vx,
      mul_le_mul_of_nonneg_right h0 (normSq3_nonneg vx)]
  let vUnit : Fin 3 → ℝ := unitVec3 vx
  have hvUnit : normSq3 vUnit = 1 := normSq3_unitVec3 hvx_pos
  have hinv_ge_one : 1 ≤ (√(normSq3 vx))⁻¹ :=
    one_le_inv_iff₀.mpr ⟨sqrt_pos.mpr hvx_pos, sqrt_one ▸ sqrt_le_sqrt hvx_le⟩
  have hmp3_single : MeasurePreserving proj3
      (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))) P3Measure :=
    ⟨by unfold proj3; fun_prop, stdGaussian_map_inner_pi he.1 he.2⟩
  have hmp3 := hmp3_single.prod hmp3_single
  let Cone3 : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    {ab | κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 vUnit (cross3 ab.1 ab.2)) ^ 2}
  have hCone3m : MeasurableSet Cone3 :=
    (isClosed_le (continuous_const.mul (continuous_normSq3.comp continuous_cross3))
      (((by unfold dot3; fun_prop : Continuous (dot3 vUnit)).comp continuous_cross3).pow
        2)).measurableSet
  have hsub : convexZeroSet (fF y₀) (fF y₁) (fF y₂) ⊆ Prod.map proj3 proj3 ⁻¹' Cone3 := by
    rintro ⟨q₁, q₂⟩ ⟨w₀, w₁, w₂, hw₀, hw₁, hw₂, hsum, hq₁, hq₂⟩
    simp only [fF, mem_preimage, Prod.map_apply, Cone3, mem_ofPred_eq] at hq₁ hq₂ ⊢
    rw [hinner_proj y₀ hspan₀ q₁, hinner_proj y₁ hspan₁ q₁, hinner_proj y₂ hspan₂ q₁] at hq₁
    rw [hinner_proj y₀ hspan₀ q₂, hinner_proj y₁ hspan₁ q₂, hinner_proj y₂ hspan₂ q₂] at hq₂
    let c : Fin 3 → ℝ := fun k => w₀ * cy 0 k + w₁ * cy 1 k + w₂ * cy 2 k
    have hdot_c (u : Fin 3 → ℝ) :
        dot3 c u = w₀ * dot3 (cy 0) u + w₁ * dot3 (cy 1) u + w₂ * dot3 (cy 2) u := by
      dsimp [c, dot3]; ring
    have hca : dot3 c (proj3 q₁) = 0 := by rw [hdot_c]; exact hq₁
    have hcb : dot3 c (proj3 q₂) = 0 := by rw [hdot_c]; exact hq₂
    have hc_v : κ ≤ dot3 c vUnit := by
      have hcvx : κ ≤ dot3 c vx := by
        rw [hdot_c]
        nlinarith
      have hcu : dot3 c vUnit = (√(normSq3 vx))⁻¹ * dot3 c vx := by
        dsimp [vUnit, unitVec3, dot3]; ring
      nlinarith
    have hc_norm : normSq3 c ≤ 1 := by
      have h0 : normSq3 (cy 0) ≤ 1 := hnormSq_proj_le y₀ hnorm₀
      have h1 : normSq3 (cy 1) ≤ 1 := hnormSq_proj_le y₁ hnorm₁
      have h2 : normSq3 (cy 2) ≤ 1 := hnormSq_proj_le y₂ hnorm₂
      have hdiff : (w₀ + w₁ + w₂) * (w₀ * normSq3 (cy 0) + w₁ * normSq3 (cy 1) +
          w₂ * normSq3 (cy 2)) - normSq3 c =
          w₀ * w₁ * normSq3 (fun k => cy 0 k - cy 1 k) +
          w₁ * w₂ * normSq3 (fun k => cy 1 k - cy 2 k) +
          w₂ * w₀ * normSq3 (fun k => cy 2 k - cy 0 k) := by dsimp [c, normSq3]; ring
      rw [hsum, one_mul] at hdiff
      linarith [mul_nonneg (mul_nonneg hw₀ hw₁) (normSq3_nonneg (fun k => cy 0 k - cy 1 k)),
        mul_nonneg (mul_nonneg hw₁ hw₂) (normSq3_nonneg (fun k => cy 1 k - cy 2 k)),
        mul_nonneg (mul_nonneg hw₂ hw₀) (normSq3_nonneg (fun k => cy 2 k - cy 0 k)),
        mul_le_mul_of_nonneg_left h0 hw₀, mul_le_mul_of_nonneg_left h1 hw₁,
        mul_le_mul_of_nonneg_left h2 hw₂]
    have h1 := mul_le_mul_of_nonneg_right (sq_le_sq' (by linarith) hc_v)
      (normSq3_nonneg (cross3 (proj3 q₁) (proj3 q₂)))
    rw [← mul_sq_dot3_cross3_eq (v := vUnit) hca hcb] at h1
    linarith only [h1, mul_le_mul_of_nonneg_right hc_norm
      (sq_nonneg (dot3 vUnit (cross3 (proj3 q₁) (proj3 q₂))))]
  calc ((stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3)))).real
        (convexZeroSet (fF y₀) (fF y₁) (fF y₂))
      ≤ ((stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))).prod
          (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3)))).real
          (Prod.map proj3 proj3 ⁻¹' Cone3) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsub)
    _ = (P3Measure.prod P3Measure).real Cone3 :=
        hmp3.measureReal_preimage hCone3m.nullMeasurableSet
    _ = 1 - κ := p3Measure_prod_cross3_cone_eq hvUnit hκ0 hκ1

/-- Coordinatewise `Measure.pi` specialization of `measureReal_stdGaussian_prod_convex_zero_le`. -/
theorem measureReal_pi_prod_convex_zero_le {ι : Type*} [Fintype ι]
    {x y₀ y₁ y₂ : EuclideanSpace ℝ ι} (hx : ‖x‖ = 1)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1)
    (hy₀ : κ ≤ ⟪y₀, x⟫) (hy₁ : κ ≤ ⟪y₁, x⟫) (hy₂ : κ ≤ ⟪y₂, x⟫)
    (hnorm₀ : ‖y₀‖ ≤ 1) (hnorm₁ : ‖y₁‖ ≤ 1) (hnorm₂ : ‖y₂‖ ≤ 1) :
    ((Measure.pi fun _ : ι => gaussianReal 0 1).prod
        (Measure.pi fun _ : ι => gaussianReal 0 1)).real
      {ω : (ι → ℝ) × (ι → ℝ) | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * ⟪y₀, WithLp.toLp 2 ω.1⟫ + w₁ * ⟪y₁, WithLp.toLp 2 ω.1⟫ +
          w₂ * ⟪y₂, WithLp.toLp 2 ω.1⟫ = 0 ∧
        w₀ * ⟪y₀, WithLp.toLp 2 ω.2⟫ + w₁ * ⟪y₁, WithLp.toLp 2 ω.2⟫ +
          w₂ * ⟪y₂, WithLp.toLp 2 ω.2⟫ = 0} ≤ 1 - κ := by
  let fLp (y : EuclideanSpace ℝ ι) (p : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) : ℝ × ℝ :=
    (⟪y, p.1⟫, ⟪y, p.2⟫)
  have hSm : MeasurableSet (convexZeroSet (fLp y₀) (fLp y₁) (fLp y₂)) :=
    measurableSet_convex_zero_three (f₀ := fLp y₀) (f₁ := fLp y₁) (f₂ := fLp y₂)
      (by unfold fLp; fun_prop) (by unfold fLp; fun_prop) (by unfold fLp; fun_prop)
  have hmp := (measurePreserving_toLp_pi_gaussianReal ι).prod
    (measurePreserving_toLp_pi_gaussianReal ι)
  exact (hmp.measureReal_preimage hSm.nullMeasurableSet).trans_le
    (measureReal_stdGaussian_prod_convex_zero_le hx hκ0 hκ1 hy₀ hy₁ hy₂ hnorm₀ hnorm₁ hnorm₂)

end ProbabilityTheory
