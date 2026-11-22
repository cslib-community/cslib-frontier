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
  have himg : {z : Z | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
      w₀ * (f₀ z).1 + w₁ * (f₁ z).1 + w₂ * (f₂ z).1 = 0 ∧
      w₀ * (f₀ z).2 + w₁ * (f₁ z).2 + w₂ * (f₂ z).2 = 0} = Prod.fst '' closedRel := by
    ext z
    simp only [mem_ofPred_eq, mem_image, Prod.exists, closedRel]
    constructor
    · rintro ⟨w₀, w₁, w₂, hw₀, hw₁, hw₂, hsum, hx, hy⟩
      let w : K3 := ![⟨w₀, hw₀, by linarith⟩, ⟨w₁, hw₁, by linarith⟩, ⟨w₂, hw₂, by linarith⟩]
      exact ⟨z, w, ⟨hsum, hx, hy⟩, rfl⟩
    · rintro ⟨_, w, ⟨hsum, hx, hy⟩, rfl⟩
      exact ⟨(w 0 : ℝ), (w 1 : ℝ), (w 2 : ℝ), (w 0).2.1, (w 1).2.1, (w 2).2.1, hsum, hx, hy⟩
  rw [himg]
  exact (isClosedMap_fst_of_compactSpace _ hclosedRel).measurableSet

/-! ### `ℝ³` cross products, Householder reflections, and Gaussian cones -/

section R3

private noncomputable abbrev P3Measure : Measure (Fin 3 → ℝ) :=
  Measure.pi fun _ : Fin 3 => gaussianReal 0 1

private def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

private def normSq3 (u : Fin 3 → ℝ) : ℝ := u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2

private def cross3 (a b : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

private theorem normSq3_nonneg (u : Fin 3 → ℝ) : 0 ≤ normSq3 u := by
  dsimp [normSq3]; positivity

private theorem normSq3_pos_of_ne_zero {x : Fin 3 → ℝ} (hx : x ≠ 0) : 0 < normSq3 x := by
  by_contra hle
  have h0 : normSq3 x = 0 := le_antisymm (not_lt.mp hle) (normSq3_nonneg x)
  dsimp [normSq3] at h0
  have hs0 := sq_nonneg (x 0)
  have hs1 := sq_nonneg (x 1)
  have hs2 := sq_nonneg (x 2)
  have hx0 : x 0 = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith only [h0, hs1, hs2]) hs0)
  have hx1 : x 1 = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith only [h0, hs0, hs2]) hs1)
  have hx2 : x 2 = 0 := sq_eq_zero_iff.mp (le_antisymm (by linarith only [h0, hs0, hs1]) hs2)
  apply hx
  ext i; fin_cases i <;> assumption

private theorem normSq3_inv_sqrt_mul {x : Fin 3 → ℝ} (hx : 0 < normSq3 x) :
    normSq3 (fun i => (√(normSq3 x))⁻¹ * x i) = 1 := by
  have hsq : (√(normSq3 x)) ^ 2 = normSq3 x := sq_sqrt hx.le
  dsimp [normSq3] at hsq hx ⊢
  have hne : √(x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2) ≠ 0 := (sqrt_pos.mpr hx).ne'
  field_simp [hne]
  linarith only [hsq]

/-- Vector triple product consequence: if `c · a = 0` and `c · b = 0`, then
`‖c‖ ^ 2 * (v · (a × b)) ^ 2 = (c · v) ^ 2 * ‖a × b‖ ^ 2`. -/
private theorem mul_sq_dot3_cross3_eq {c v a b : Fin 3 → ℝ} (hca : dot3 c a = 0)
    (hcb : dot3 c b = 0) :
    normSq3 c * (dot3 v (cross3 a b)) ^ 2 = (dot3 c v) ^ 2 * normSq3 (cross3 a b) := by
  dsimp [normSq3, dot3, cross3] at hca hcb ⊢
  let C0 := a 1 * b 2 - a 2 * b 1
  let C1 := a 2 * b 0 - a 0 * b 2
  let C2 := a 0 * b 1 - a 1 * b 0
  change (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) * (v 0 * C0 + v 1 * C1 + v 2 * C2) ^ 2 =
    (c 0 * v 0 + c 1 * v 1 + c 2 * v 2) ^ 2 * (C0 ^ 2 + C1 ^ 2 + C2 ^ 2)
  have e01 : c 0 * C1 = c 1 * C0 := by
    have h : c 0 * C1 - c 1 * C0 = (c 0 * b 0 + c 1 * b 1 + c 2 * b 2) * a 2 -
        (c 0 * a 0 + c 1 * a 1 + c 2 * a 2) * b 2 := by dsimp [C0, C1]; ring
    rw [hca, hcb] at h
    linarith
  have e12 : c 1 * C2 = c 2 * C1 := by
    have h : c 1 * C2 - c 2 * C1 = (c 0 * b 0 + c 1 * b 1 + c 2 * b 2) * a 0 -
        (c 0 * a 0 + c 1 * a 1 + c 2 * a 2) * b 0 := by dsimp [C1, C2]; ring
    rw [hca, hcb] at h
    linarith
  have e20 : c 2 * C0 = c 0 * C2 := by
    have h : c 2 * C0 - c 0 * C2 = (c 0 * b 0 + c 1 * b 1 + c 2 * b 2) * a 1 -
        (c 0 * a 0 + c 1 * a 1 + c 2 * a 2) * b 1 := by dsimp [C2, C0]; ring
    rw [hca, hcb] at h
    linarith
  by_cases hc0 : c 0 ≠ 0
  · refine mul_left_cancel₀ (pow_ne_zero 2 hc0) ?_
    have h1 : c 0 ^ 2 * ((c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) * (v 0 * C0 + v 1 * C1 + v 2 * C2) ^ 2) =
        (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) *
          (v 0 * (c 0 * C0) + v 1 * (c 0 * C1) + v 2 * (c 0 * C2)) ^ 2 := by ring
    have h2 : c 0 ^ 2 * ((c 0 * v 0 + c 1 * v 1 + c 2 * v 2) ^ 2 * (C0 ^ 2 + C1 ^ 2 + C2 ^ 2)) =
        (c 0 * v 0 + c 1 * v 1 + c 2 * v 2) ^ 2 *
          ((c 0 * C0) ^ 2 + (c 0 * C1) ^ 2 + (c 0 * C2) ^ 2) := by ring
    rw [h1, h2, e01, e20.symm]
    ring
  · push Not at hc0
    by_cases hc1 : c 1 ≠ 0
    · refine mul_left_cancel₀ (pow_ne_zero 2 hc1) ?_
      have h1 : c 1 ^ 2 * ((c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) * (v 0 * C0 + v 1 * C1 + v 2 * C2) ^ 2) =
          (c 0 ^ 2 + c 1 ^ 2 + c 2 ^ 2) *
            (v 0 * (c 1 * C0) + v 1 * (c 1 * C1) + v 2 * (c 1 * C2)) ^ 2 := by ring
      have h2 : c 1 ^ 2 * ((c 0 * v 0 + c 1 * v 1 + c 2 * v 2) ^ 2 * (C0 ^ 2 + C1 ^ 2 + C2 ^ 2)) =
          (c 0 * v 0 + c 1 * v 1 + c 2 * v 2) ^ 2 *
            ((c 1 * C0) ^ 2 + (c 1 * C1) ^ 2 + (c 1 * C2) ^ 2) := by ring
      rw [h1, h2, e01.symm, e12]
      ring
    · push Not at hc1
      by_cases hc2 : c 2 ≠ 0
      · have hC0 : C0 = 0 := by
          rw [hc0, zero_mul] at e20; exact (mul_eq_zero.mp e20).resolve_left hc2
        have hC1 : C1 = 0 := by
          rw [hc1, zero_mul] at e12; exact (mul_eq_zero.mp e12.symm).resolve_left hc2
        rw [hc0, hc1, hC0, hC1]
        ring
      · push Not at hc2
        rw [hc0, hc1, hc2]
        ring

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

private theorem householder_involutive {u : Fin 3 → ℝ} (hu : normSq3 u = 1) (x : Fin 3 → ℝ) :
    householder u (householder u x) = x := by
  have hw : normSq3 (householderVec u) ≠ 0 := by linarith [two_le_normSq3_householderVec hu]
  ext i
  fin_cases i <;>
    (dsimp [householder, normSq3, dot3] at hw ⊢; field_simp [hw]; ring)

private theorem sq_householder_zero_eq_sq_dot3 {u : Fin 3 → ℝ} (hu : normSq3 u = 1)
    (y : Fin 3 → ℝ) : (householder u y 0) ^ 2 = (dot3 u y) ^ 2 := by
  dsimp [householder, householderVec]
  split_ifs with h0
  · have hN : normSq3 ![u 0 - 1, u 1, u 2] = 2 * (1 - u 0) := by
      dsimp [normSq3] at hu ⊢; linarith
    have h1 : 1 - u 0 ≠ 0 := by linarith
    rw [hN]
    dsimp [dot3]
    field_simp [h1]
    ring
  · have hN : normSq3 ![u 0 + 1, u 1, u 2] = 2 * (1 + u 0) := by
      dsimp [normSq3] at hu ⊢; linarith
    have h1 : 1 + u 0 ≠ 0 := by linarith
    rw [hN]
    dsimp [dot3]
    field_simp [h1]
    ring

private theorem cross3_householder {u : Fin 3 → ℝ} (hu : normSq3 u = 1) (a b : Fin 3 → ℝ) :
    cross3 (householder u a) (householder u b) = -householder u (cross3 a b) := by
  have hw : normSq3 (householderVec u) ≠ 0 := by linarith [two_le_normSq3_householderVec hu]
  ext i
  fin_cases i <;>
    (dsimp [cross3, householder, normSq3, dot3, Pi.neg_apply] at hw ⊢; field_simp [hw]; ring)

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

private theorem p3Measure_eval_eq_zero (i : Fin 3) : P3Measure {x : Fin 3 → ℝ | x i = 0} = 0 := by
  have hmap : (P3Measure.map fun x : Fin 3 → ℝ => x i) = gaussianReal 0 1 := by
    simpa using (measurePreserving_eval (fun _ : Fin 3 => gaussianReal 0 1) i).map_eq
  rw [show {x : Fin 3 → ℝ | x i = 0} = (fun x : Fin 3 → ℝ => x i) ⁻¹' {0} from rfl,
    ← Measure.map_apply (by fun_prop) (measurableSet_singleton 0), hmap]
  exact @measure_singleton _ _ (gaussianReal 0 1) (nullSingletonClass_gaussianReal one_ne_zero) 0

private theorem p3Measure_singleton_zero : P3Measure {0} = 0 := by
  have hsub : ({0} : Set (Fin 3 → ℝ)) ⊆ {x | x 0 = 0} :=
    fun x hx => by simp [mem_singleton_iff.mp hx]
  exact le_antisymm ((measure_mono hsub).trans (le_of_eq (p3Measure_eval_eq_zero 0))) bot_le

private theorem p3Measure_prod_cross3_eq_zero :
    (P3Measure.prod P3Measure) {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) | cross3 ab.1 ab.2 = 0} = 0 := by
  have hsub : {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) | cross3 ab.1 ab.2 = 0} ⊆
      {ab | ab.1 0 * ab.2 1 - ab.1 1 * ab.2 0 = 0} := by
    intro ab hab
    simpa [cross3] using congrFun hab 2
  refine le_antisymm ((measure_mono hsub).trans ?_) bot_le
  have hm : MeasurableSet {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
      ab.1 0 * ab.2 1 - ab.1 1 * ab.2 0 = 0} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  rw [Measure.prod_apply hm]
  have hae : (fun a : Fin 3 → ℝ => P3Measure {b | a 0 * b 1 - a 1 * b 0 = 0}) =ᵐ[P3Measure] 0 := by
    filter_upwards [compl_mem_ae_iff.mpr (p3Measure_eval_eq_zero 0)] with a ha0
    change a 0 ≠ 0 at ha0
    let w : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![-a 1, a 0, 0]
    have hw : w ≠ 0 := by
      intro hzero
      have h1 : w.ofLp 1 = 0 := by simp [hzero]
      exact ha0 (by simpa [w] using h1)
    let Sw : Set (EuclideanSpace ℝ (Fin 3)) := {y | ⟪w, y⟫ ∈ ({0} : Set ℝ)}
    have hSw : MeasurableSet Sw := (measurableSet_singleton 0).preimage (by fun_prop)
    have hset : {b : Fin 3 → ℝ | a 0 * b 1 - a 1 * b 0 = 0} = WithLp.toLp 2 ⁻¹' Sw := by
      ext b
      simp only [mem_ofPred_eq, mem_preimage, Sw, mem_singleton_iff,
        EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct, Fin.sum_univ_three, w]
      dsimp
      constructor <;> intro h <;> linarith
    change P3Measure {b | a 0 * b 1 - a 1 * b 0 = 0} = 0
    rw [hset, ← Measure.map_apply (by fun_prop) hSw,
      (measurePreserving_toLp_pi_gaussianReal (Fin 3)).map_eq]
    refine le_antisymm ((stdGaussian_inner_mem_le hw (measurableSet_singleton 0)).trans ?_) bot_le
    simp
  have hzero_int : ∫⁻ a, P3Measure {b | a 0 * b 1 - a 1 * b 0 = 0} ∂P3Measure = 0 := by
    calc ∫⁻ a, P3Measure {b | a 0 * b 1 - a 1 * b 0 = 0} ∂P3Measure
        = ∫⁻ _a, 0 ∂P3Measure := lintegral_congr_ae hae
      _ = 0 := by simp
  exact le_of_eq hzero_int

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
      have hr0 : 0 < p.1 := hp.1
      have hD_iff : polarCoord.symm p ∈ D ↔ p.1 ≤ a := by
        simp only [D, polarCoord_symm_apply, mem_ofPred_eq]
        have hsq : (p.1 * cos p.2) ^ 2 + (p.1 * sin p.2) ^ 2 = p.1 ^ 2 := by
          linear_combination p.1 ^ 2 * sin_sq_add_cos_sq p.2
        rw [hsq]
        exact ⟨fun h => le_of_sq_le_sq h ha.le, fun h => sq_le_sq' (by linarith only [hr0, ha]) h⟩
      simp only [ENNReal.toReal_mul, toReal_gaussianPDF, polarCoord_symm_apply, hdens, smul_eq_mul,
        mul_one]
      by_cases hra : p.1 ≤ a
      · have hmem : (p.1 * cos p.2, p.1 * sin p.2) ∈ D := hD_iff.mpr hra
        simp [hmem, hra, rad]
        ring
      · have hnmem : (p.1 * cos p.2, p.1 * sin p.2) ∉ D := fun h => hra (hD_iff.mp h)
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
      simp
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
    let u (i : Fin 3) : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single i 1
    have hu_norm (i : Fin 3) : ‖u i‖₊ = 1 := Subtype.ext (by simp [u])
    have hu_orth : Pairwise fun i j => ⟪u i, u j⟫ = 0 := by
      intro i j hij
      dsimp [u]
      rw [EuclideanSpace.inner_single_left]
      simp [hij.symm]
    have hlaw : HasGaussianLaw (fun y => fun i : Fin 3 => innerSL ℝ (u i) y)
        (stdGaussian (EuclideanSpace ℝ (Fin 3))) :=
      IsGaussian.hasGaussianLaw_id.map_fun (ContinuousLinearMap.pi fun i => innerSL ℝ (u i))
    have hind : iIndepFun (fun i y => ⟪u i, y⟫) (stdGaussian (EuclideanSpace ℝ (Fin 3))) := by
      refine hlaw.iIndepFun_of_covariance_eq_zero fun i j hij => ?_
      have h := covarianceBilin_apply_eq_cov
        (μ := stdGaussian (EuclideanSpace ℝ (Fin 3))) IsGaussian.memLp_two_id (u i) (u j)
      rw [covarianceBilin_stdGaussian, innerSL_apply_apply ℝ] at h
      exact h.symm.trans (hu_orth hij)
    have hind12 : IndepFun (fun y => (⟪u 1, y⟫, ⟪u 2, y⟫)) (fun y => ⟪u 0, y⟫)
        (stdGaussian (EuclideanSpace ℝ (Fin 3))) :=
      hind.indepFun_prodMk (fun _ => by fun_prop) 1 2 0 (by decide) (by decide)
    have hmap_std : (stdGaussian (EuclideanSpace ℝ (Fin 3))).map
        (fun y => (⟪u 0, y⟫, (⟪u 1, y⟫, ⟪u 2, y⟫))) =
        (gaussianReal 0 1).prod ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)).1 hind12.symm,
        stdGaussian_map_inner, stdGaussian_map_inner_prod (hu_orth (by decide : (1 : Fin 3) ≠ 2)),
        hu_norm 0, hu_norm 1, hu_norm 2]
      simp
    have hcomp : split3 = (fun y => (⟪u 0, y⟫, (⟪u 1, y⟫, ⟪u 2, y⟫))) ∘ WithLp.toLp 2 := by
      funext x
      simp [split3, u, EuclideanSpace.inner_single_left]
    refine ⟨by unfold split3; fun_prop, ?_⟩
    rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop),
      (measurePreserving_toLp_pi_gaussianReal (Fin 3)).map_eq, hmap_std]
  rcases eq_or_lt_of_le hκ1 with rfl | hκ_lt
  · -- Degenerate cap `κ = 1`: `x 1 = 0 ∧ x 2 = 0`, which has measure `0 = 1 - 1`.
    have hsub : {x : Fin 3 → ℝ | x ≠ 0 ∧ (1 : ℝ) ^ 2 * normSq3 x ≤ (x 0) ^ 2} ⊆
        {x | x 1 = 0} := by
      intro x ⟨_, hx⟩
      dsimp [normSq3] at hx
      have hs2 := sq_nonneg (x 2)
      have hs1 := sq_nonneg (x 1)
      have h1_le : x 1 ^ 2 ≤ 0 := by linarith only [hx, hs2]
      exact sq_eq_zero_iff.mp (le_antisymm h1_le hs1)
    have hzero : P3Measure {x : Fin 3 → ℝ | x ≠ 0 ∧ (1 : ℝ) ^ 2 * normSq3 x ≤ (x 0) ^ 2} = 0 :=
      le_antisymm ((measure_mono hsub).trans (le_of_eq (p3Measure_eval_eq_zero 1))) bot_le
    rw [Measure.real, hzero]
    simp
  · -- Nondegenerate cap `0 < κ < 1`: cylindrical integration via `split3`.
    set c : ℝ := √(1 - κ ^ 2) / κ
    have h1_sub_pos : 0 < 1 - κ ^ 2 := by
      have hsq : κ ^ 2 < 1 := by
        have := mul_lt_mul_of_pos_left hκ_lt hκ0
        have := hκ_lt
        nlinarith only [hκ0, hκ_lt]
      linarith only [hsq]
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
      simp only [mem_ofPred_eq, mem_preimage, ConeP, split3, normSq3]
      have hκ2_pos : 0 < κ ^ 2 := pow_pos hκ0 2
      constructor
      · rintro ⟨hx0, hle⟩
        have hx0_ne : x 0 ≠ 0 := by
          intro h0
          rw [h0] at hle
          have hs1 := sq_nonneg (x 1)
          have hs2 := sq_nonneg (x 2)
          have hprod : κ ^ 2 * (x 1 ^ 2 + x 2 ^ 2) ≤ 0 := by linarith only [hle]
          have hsum_le : x 1 ^ 2 + x 2 ^ 2 ≤ 0 :=
            nonpos_of_mul_nonpos_right hprod hκ2_pos
          have hx1 : x 1 = 0 :=
            sq_eq_zero_iff.mp (le_antisymm (by linarith only [hsum_le, hs2]) hs1)
          have hx2 : x 2 = 0 :=
            sq_eq_zero_iff.mp (le_antisymm (by linarith only [hsum_le, hs1]) hs2)
          apply hx0
          ext i
          fin_cases i
          · exact h0
          · exact hx1
          · exact hx2
        refine ⟨hx0_ne, ?_⟩
        rw [mul_pow, sq_abs, hc_sq, div_mul_eq_mul_div, le_div_iff₀ hκ2_pos]
        linarith only [hle]
      · rintro ⟨hx0_ne, hle⟩
        refine ⟨fun h => hx0_ne (by simp [h]), ?_⟩
        rw [mul_pow, sq_abs, hc_sq, div_mul_eq_mul_div, le_div_iff₀ hκ2_pos] at hle
        linarith only [hle]
    rw [hpre, hmp.measureReal_preimage hConePm.nullMeasurableSet]
    set μ2 := (gaussianReal 0 1).prod (gaussianReal 0 1)
    rw [← integral_indicator_one hConePm]
    have hf_int : Integrable (ConeP.indicator 1) ((gaussianReal 0 1).prod μ2) :=
      (integrable_const (1 : ℝ)).indicator hConePm
    rw [integral_prod _ hf_int]
    have hslice : ∀ᵐ x₀ ∂gaussianReal 0 1,
        (∫ z, ConeP.indicator 1 (x₀, z) ∂μ2) =
          1 - exp (-((c * |x₀|) ^ 2) / 2) := by
      have hg0 : gaussianReal 0 1 ({0} : Set ℝ) = 0 :=
        @measure_singleton _ _ (gaussianReal 0 1) (nullSingletonClass_gaussianReal one_ne_zero) 0
      filter_upwards [compl_mem_ae_iff.mpr hg0] with x₀ hx₀
      change x₀ ≠ 0 at hx₀
      have ha_pos : 0 < c * |x₀| := mul_pos hc_pos (abs_pos.mpr hx₀)
      let D : Set (ℝ × ℝ) := {z | z.1 ^ 2 + z.2 ^ 2 ≤ (c * |x₀|) ^ 2}
      have hDm : MeasurableSet D := measurableSet_le (by fun_prop) measurable_const
      have hind_eq : (fun z : ℝ × ℝ => ConeP.indicator (1 : (ℝ × (ℝ × ℝ)) → ℝ) (x₀, z)) =
          D.indicator 1 := by
        funext z
        by_cases hz : z ∈ D
        · have hmem : (x₀, z) ∈ ConeP := ⟨hx₀, hz⟩
          simp [hz, hmem]
        · have hnmem : (x₀, z) ∉ ConeP := fun h => hz h.2
          simp [hz, hnmem]
      rw [hind_eq, integral_indicator_one hDm]
      exact measureReal_prod_gaussianReal_disk ha_pos
    rw [integral_congr_ae hslice]
    have hsub_int : ∫ x₀, (1 - exp (-((c * |x₀|) ^ 2) / 2)) ∂gaussianReal 0 1 =
        (∫ _x₀, (1 : ℝ) ∂gaussianReal 0 1) -
          ∫ x₀, exp (-((c * |x₀|) ^ 2) / 2) ∂gaussianReal 0 1 := by
      refine integral_sub (integrable_const 1) ?_
      refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x₀ => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      have hsq0 := sq_nonneg (c * |x₀|)
      exact exp_le_one_iff.mpr (by linarith only [hsq0])
    rw [hsub_int, integral_const, probReal_univ, one_smul]
    congr 1
    rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
      integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
        (ae_of_all _ fun _ => gaussianPDF_lt_top)]
    let vκ : ℝ≥0 := Real.toNNReal (κ ^ 2)
    have hvκ_coe : (vκ : ℝ) = κ ^ 2 := Real.coe_toNNReal _ (sq_nonneg κ)
    have hvκ_ne : vκ ≠ 0 := by
      intro h
      have h0 : (vκ : ℝ) = 0 := congrArg NNReal.toReal h
      rw [hvκ_coe] at h0
      exact (pow_pos hκ0 2).ne' h0
    have hpdf_eq (x₀ : ℝ) :
        (gaussianPDF 0 1 x₀).toReal • exp (-((c * |x₀|) ^ 2) / 2) =
          κ * gaussianPDFReal 0 vκ x₀ := by
      rw [toReal_gaussianPDF, smul_eq_mul, mul_pow, sq_abs]
      simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one, hvκ_coe]
      have hsqrt_v : √(2 * π * κ ^ 2) = √(2 * π) * κ := by
        rw [sqrt_mul (by positivity), sqrt_sq hκ0.le]
      rw [hsqrt_v, mul_inv]
      have hpre_fac : κ * ((√(2 * π))⁻¹ * κ⁻¹ * exp (-x₀ ^ 2 / (2 * κ ^ 2))) =
          (√(2 * π))⁻¹ * exp (-x₀ ^ 2 / (2 * κ ^ 2)) := by
        field_simp [hκ0.ne']
      rw [hpre_fac, mul_assoc, ← exp_add]
      congr 2
      rw [hc_sq]
      field_simp [hκ0.ne']
      ring
    simp_rw [hpdf_eq]
    rw [integral_const_mul, integral_gaussianPDFReal_eq_one 0 hvκ_ne, mul_one]

/-- **Cross-product cap probability in `ℝ³` via Householder–Fubini.** -/
private theorem p3Measure_prod_cross3_cone_eq {v : Fin 3 → ℝ} (hv : normSq3 v = 1)
    {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) :
    (P3Measure.prod P3Measure).real
      {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
        κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 v (cross3 ab.1 ab.2)) ^ 2} = 1 - κ := by
  set M2 := P3Measure.prod P3Measure
  have hcont_cross : Continuous fun ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) => cross3 ab.1 ab.2 := by
    unfold cross3
    refine continuous_pi fun i => ?_
    fin_cases i <;> (dsimp; fun_prop)
  have hcont_normSq : Continuous normSq3 := by unfold normSq3; fun_prop
  have hcont_dot (w : Fin 3 → ℝ) : Continuous (dot3 w) := by unfold dot3; fun_prop
  let A_full : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    {ab | κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 v (cross3 ab.1 ab.2)) ^ 2}
  let A_nz : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    {ab | cross3 ab.1 ab.2 ≠ 0 ∧
      κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 v (cross3 ab.1 ab.2)) ^ 2}
  have hAnz_m : MeasurableSet A_nz := by
    have hm1 : MeasurableSet {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) | cross3 ab.1 ab.2 ≠ 0} :=
      (isClosed_singleton.preimage hcont_cross).measurableSet.compl
    have hm2 : MeasurableSet {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
        κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 v (cross3 ab.1 ab.2)) ^ 2} :=
      (isClosed_le (continuous_const.mul (hcont_normSq.comp hcont_cross))
        (((hcont_dot v).comp hcont_cross).pow 2)).measurableSet
    exact hm1.inter hm2
  have hdiff_null : M2 (A_full \ A_nz) = 0 := by
    refine le_antisymm ((measure_mono ?_).trans (le_of_eq p3Measure_prod_cross3_eq_zero)) bot_le
    intro ab ⟨_, hnot⟩
    by_contra hne
    exact hnot ⟨hne, ‹_›⟩
  have hfull_eq_nz : M2.real A_full = M2.real A_nz := by
    have hunion : A_full = A_nz ∪ (A_full \ A_nz) := by
      ext ab; simp only [A_full, A_nz, mem_union, mem_sdiff, mem_ofPred_eq]; tauto
    have h1 : M2 A_full ≤ M2 A_nz := by
      calc M2 A_full = M2 (A_nz ∪ (A_full \ A_nz)) := congrArg M2 hunion
        _ ≤ M2 A_nz + M2 (A_full \ A_nz) := measure_union_le _ _
        _ = M2 A_nz := by rw [hdiff_null, add_zero]
    have h2 : M2 A_nz ≤ M2 A_full := measure_mono fun _ h => h.2
    simp only [Measure.real, le_antisymm h1 h2]
  rw [hfull_eq_nz]
  let A0 : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    {ab | cross3 ab.1 ab.2 ≠ 0 ∧
      κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (cross3 ab.1 ab.2 0) ^ 2}
  have hA0_m : MeasurableSet A0 := by
    have hm1 : MeasurableSet {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) | cross3 ab.1 ab.2 ≠ 0} :=
      (isClosed_singleton.preimage hcont_cross).measurableSet.compl
    have hm2 : MeasurableSet {ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) |
        κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (cross3 ab.1 ab.2 0) ^ 2} :=
      (isClosed_le (continuous_const.mul (hcont_normSq.comp hcont_cross))
        (((continuous_apply 0).comp hcont_cross).pow 2)).measurableSet
    exact hm1.inter hm2
  have hv_mp : MeasurePreserving (Prod.map (householder v) (householder v)) M2 M2 :=
    (measurePreserving_householder hv).prod (measurePreserving_householder hv)
  have hhouse_zero (u : Fin 3 → ℝ) : householder u 0 = 0 := by
    ext i; fin_cases i <;> simp [householder, dot3]
  have hAnz_eq_A0 : M2.real A_nz = M2.real A0 := by
    have hpre : Prod.map (householder v) (householder v) ⁻¹' A0 = A_nz := by
      ext ⟨a, b⟩
      simp only [mem_preimage, Prod.map_apply, A0, A_nz, mem_ofPred_eq, cross3_householder hv]
      have hnorm_neg (y : Fin 3 → ℝ) : normSq3 (-y) = normSq3 y := by
        dsimp [normSq3, Pi.neg_apply]; ring
      have hsq_neg (y : Fin 3 → ℝ) : ((-y) 0) ^ 2 = (y 0) ^ 2 := by
        dsimp [Pi.neg_apply]; ring
      have hnorm_hh (y : Fin 3 → ℝ) : normSq3 (householder v y) = normSq3 y := by
        simpa [normSq3, dot3, sq] using dot3_householder hv y y
      rw [hnorm_neg, hnorm_hh, hsq_neg, sq_householder_zero_eq_sq_dot3 hv]
      have hne_iff : -householder v (cross3 a b) ≠ 0 ↔ cross3 a b ≠ 0 := by
        rw [neg_ne_zero]
        refine ⟨fun h h0 => h (by rw [h0, hhouse_zero]), fun h h0 => h ?_⟩
        rw [← householder_involutive hv (cross3 a b), h0, hhouse_zero]
      rw [hne_iff]
    rw [← hpre, hv_mp.measureReal_preimage hA0_m.nullMeasurableSet]
  rw [hAnz_eq_A0]
  let Joint : Set (((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ)) :=
    {abx | cross3 abx.1.1 abx.1.2 ≠ 0 ∧ abx.2 ≠ 0 ∧
      κ ^ 2 * normSq3 abx.2 * normSq3 (cross3 abx.1.1 abx.1.2) ≤
        (dot3 abx.2 (cross3 abx.1.1 abx.1.2)) ^ 2}
  have hJoint_m : MeasurableSet Joint := by
    have hc1 : Continuous fun abx : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ) =>
        cross3 abx.1.1 abx.1.2 := hcont_cross.comp continuous_fst
    have hm1 : MeasurableSet
        {abx : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ) | cross3 abx.1.1 abx.1.2 ≠ 0} :=
      (isClosed_singleton.preimage hc1).measurableSet.compl
    have hm2 : MeasurableSet
        {abx : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ) | abx.2 ≠ 0} :=
      (isClosed_singleton.preimage continuous_snd).measurableSet.compl
    have hm3 : MeasurableSet
        {abx : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ) |
          κ ^ 2 * normSq3 abx.2 * normSq3 (cross3 abx.1.1 abx.1.2) ≤
            (dot3 abx.2 (cross3 abx.1.1 abx.1.2)) ^ 2} := by
      have hdot2 : Continuous fun abx : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ) =>
          dot3 abx.2 (cross3 abx.1.1 abx.1.2) := by
        unfold dot3
        exact ((((continuous_apply 0).comp continuous_snd).mul
            ((continuous_apply 0).comp hc1)).add
          (((continuous_apply 1).comp continuous_snd).mul
            ((continuous_apply 1).comp hc1))).add
          (((continuous_apply 2).comp continuous_snd).mul
            ((continuous_apply 2).comp hc1))
      exact (isClosed_le
        ((continuous_const.mul (hcont_normSq.comp continuous_snd)).mul
          (hcont_normSq.comp hc1))
        (hdot2.pow 2)).measurableSet
    exact hm1.inter (hm2.inter hm3)
  have hJoint_int : Integrable (Joint.indicator 1) (M2.prod P3Measure) :=
    (integrable_const (1 : ℝ)).indicator hJoint_m
  -- Slice 1: integrate over `ab` first for fixed `x ≠ 0`.
  have hslice_x : ∀ᵐ x ∂P3Measure,
      (∫ ab, Joint.indicator 1 (ab, x) ∂M2) = M2.real A0 := by
    filter_upwards [compl_mem_ae_iff.mpr p3Measure_singleton_zero] with x hx0
    change x ≠ 0 at hx0
    have hnx_pos : 0 < normSq3 x := normSq3_pos_of_ne_zero hx0
    set s := (√(normSq3 x))⁻¹
    let ux : Fin 3 → ℝ := fun i => s * x i
    have hux : normSq3 ux = 1 := normSq3_inv_sqrt_mul hnx_pos
    have hind_x : (fun ab => Joint.indicator (1 : (((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ)) → ℝ)
          (ab, x)) =
        (Prod.map (householder ux) (householder ux) ⁻¹' A0).indicator
          (1 : ((Fin 3 → ℝ) × (Fin 3 → ℝ)) → ℝ) := by
      funext ⟨a, b⟩
      have hiff : ((a, b), x) ∈ Joint ↔
          Prod.map (householder ux) (householder ux) (a, b) ∈ A0 := by
        simp only [Joint, A0, mem_ofPred_eq, Prod.map_apply, cross3_householder hux]
        have hnorm_neg (y : Fin 3 → ℝ) : normSq3 (-y) = normSq3 y := by
          dsimp [normSq3, Pi.neg_apply]; ring
        have hsq_neg (y : Fin 3 → ℝ) : ((-y) 0) ^ 2 = (y 0) ^ 2 := by
          dsimp [Pi.neg_apply]; ring
        have hnorm_hh (y : Fin 3 → ℝ) : normSq3 (householder ux y) = normSq3 y := by
          simpa [normSq3, dot3, sq] using dot3_householder hux y y
        rw [hnorm_neg, hnorm_hh, hsq_neg, sq_householder_zero_eq_sq_dot3 hux]
        have hne_iff : -householder ux (cross3 a b) ≠ 0 ↔ cross3 a b ≠ 0 := by
          rw [neg_ne_zero]
          refine ⟨fun h h0 => h (by rw [h0, hhouse_zero]), fun h h0 => h ?_⟩
          rw [← householder_involutive hux (cross3 a b), h0, hhouse_zero]
        rw [hne_iff]
        have hdot_ux (y : Fin 3 → ℝ) : (dot3 ux y) ^ 2 = (normSq3 x)⁻¹ * (dot3 x y) ^ 2 := by
          dsimp [ux, dot3, s]
          have hsq : ((√(normSq3 x))⁻¹) ^ 2 = (normSq3 x)⁻¹ := by
            rw [inv_pow, sq_sqrt hnx_pos.le]
          calc (s * x 0 * y 0 + s * x 1 * y 1 + s * x 2 * y 2) ^ 2
              = s ^ 2 * (x 0 * y 0 + x 1 * y 1 + x 2 * y 2) ^ 2 := by ring
            _ = (normSq3 x)⁻¹ * (dot3 x y) ^ 2 := by rw [hsq]; rfl
        rw [hdot_ux]
        refine ⟨fun ⟨hc, _, hle⟩ => ⟨hc, ?_⟩, fun ⟨hc, hle⟩ => ⟨hc, hx0, ?_⟩⟩
        · have hmul := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hnx_pos.le)
          rwa [← mul_assoc, ← mul_assoc, mul_comm (normSq3 x)⁻¹, mul_assoc (κ ^ 2),
            inv_mul_cancel₀ hnx_pos.ne', mul_one] at hmul
        · have hmul := mul_le_mul_of_nonneg_left hle hnx_pos.le
          have hrhs : normSq3 x * ((normSq3 x)⁻¹ * (dot3 x (cross3 a b)) ^ 2) =
              (dot3 x (cross3 a b)) ^ 2 := by
            rw [← mul_assoc, mul_inv_cancel₀ hnx_pos.ne', one_mul]
          rw [hrhs] at hmul
          have hlhs : normSq3 x * (κ ^ 2 * normSq3 (cross3 a b)) =
              κ ^ 2 * normSq3 x * normSq3 (cross3 a b) := by ring
          rwa [hlhs] at hmul
      by_cases h : ((a, b), x) ∈ Joint
      · have h' : (a, b) ∈ Prod.map (householder ux) (householder ux) ⁻¹' A0 := hiff.mp h
        rw [indicator_of_mem h, indicator_of_mem h']
        rfl
      · have h' : (a, b) ∉ Prod.map (householder ux) (householder ux) ⁻¹' A0 := mt hiff.mpr h
        rw [indicator_of_notMem h, indicator_of_notMem h']
    rw [hind_x, integral_indicator_one
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
    have hnC_pos : 0 < normSq3 C := normSq3_pos_of_ne_zero hc
    set s := (√(normSq3 C))⁻¹
    let uC : Fin 3 → ℝ := fun i => s * C i
    have huC : normSq3 uC = 1 := normSq3_inv_sqrt_mul hnC_pos
    let ConeX : Set (Fin 3 → ℝ) := {x | x ≠ 0 ∧ κ ^ 2 * normSq3 x ≤ (x 0) ^ 2}
    have hConeXm : MeasurableSet ConeX := by
      have hm1 : MeasurableSet {x : Fin 3 → ℝ | x ≠ 0} := isClosed_singleton.measurableSet.compl
      have hm2 : MeasurableSet {x : Fin 3 → ℝ | κ ^ 2 * normSq3 x ≤ (x 0) ^ 2} :=
        (isClosed_le (continuous_const.mul hcont_normSq)
          ((continuous_apply 0).pow 2)).measurableSet
      exact hm1.inter hm2
    have hind_ab : (fun x => Joint.indicator (1 : (((Fin 3 → ℝ) × (Fin 3 → ℝ)) × (Fin 3 → ℝ)) → ℝ)
          ((a, b), x)) =
        (householder uC ⁻¹' ConeX).indicator (1 : (Fin 3 → ℝ) → ℝ) := by
      funext x
      have hiff : ((a, b), x) ∈ Joint ↔ householder uC x ∈ ConeX := by
        simp only [Joint, ConeX, mem_ofPred_eq]
        have hnorm_hh : normSq3 (householder uC x) = normSq3 x := by
          simpa [normSq3, dot3, sq] using dot3_householder huC x x
        rw [hnorm_hh, sq_householder_zero_eq_sq_dot3 huC x]
        have hne_x : householder uC x ≠ 0 ↔ x ≠ 0 := by
          refine ⟨fun h h0 => h (by rw [h0, hhouse_zero]), fun h h0 => h ?_⟩
          rw [← householder_involutive huC x, h0, hhouse_zero]
        rw [hne_x]
        have hdot_uC : (dot3 uC x) ^ 2 = (normSq3 C)⁻¹ * (dot3 x C) ^ 2 := by
          dsimp [uC, dot3, s]
          have hsq : ((√(normSq3 C))⁻¹) ^ 2 = (normSq3 C)⁻¹ := by
            rw [inv_pow, sq_sqrt hnC_pos.le]
          calc (s * C 0 * x 0 + s * C 1 * x 1 + s * C 2 * x 2) ^ 2
              = s ^ 2 * (x 0 * C 0 + x 1 * C 1 + x 2 * C 2) ^ 2 := by ring
            _ = (normSq3 C)⁻¹ * (dot3 x C) ^ 2 := by rw [hsq]; rfl
        rw [hdot_uC]
        refine ⟨fun ⟨_, hx0, hle⟩ => ⟨hx0, ?_⟩, fun ⟨hx0, hle⟩ => ⟨hc, hx0, ?_⟩⟩
        · have hmul := mul_le_mul_of_nonneg_left hle (inv_nonneg.mpr hnC_pos.le)
          have hlhs : (normSq3 C)⁻¹ * (κ ^ 2 * normSq3 x * normSq3 C) =
              κ ^ 2 * normSq3 x * (normSq3 C * (normSq3 C)⁻¹) := by ring
          rw [hlhs, mul_inv_cancel₀ hnC_pos.ne', mul_one] at hmul
          exact hmul
        · have hmul := mul_le_mul_of_nonneg_left hle hnC_pos.le
          have hrhs : normSq3 C * ((normSq3 C)⁻¹ * (dot3 x C) ^ 2) = (dot3 x C) ^ 2 := by
            rw [← mul_assoc, mul_inv_cancel₀ hnC_pos.ne', one_mul]
          have hlhs : normSq3 C * (κ ^ 2 * normSq3 x) = κ ^ 2 * normSq3 x * normSq3 C := by ring
          rwa [hlhs, hrhs] at hmul
      by_cases h : ((a, b), x) ∈ Joint
      · have h' : x ∈ householder uC ⁻¹' ConeX := hiff.mp h
        rw [indicator_of_mem h, indicator_of_mem h']
        rfl
      · have h' : x ∉ householder uC ⁻¹' ConeX := mt hiff.mpr h
        rw [indicator_of_notMem h, indicator_of_notMem h']
    rw [hind_ab, integral_indicator_one
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

private noncomputable def bSpare (d : ℕ) (k : Fin 3) : EuclideanSpace ℝ (Fin d ⊕ Fin 3) :=
  EuclideanSpace.single (Sum.inr k) 1

private theorem norm_bSpare (d : ℕ) (k : Fin 3) : ‖bSpare d k‖ = 1 := by
  simp [bSpare]

private theorem inner_bSpare (d : ℕ) (j k : Fin 3) :
    ⟪bSpare d j, bSpare d k⟫ = if j = k then 1 else 0 := by
  dsimp [bSpare]
  rw [EuclideanSpace.inner_single_left]
  by_cases h : j = k
  · subst h; simp
  · simp [h]

private theorem exists_unit_span_one {d : ℕ} (v₀ : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
    ∃ e₀ : EuclideanSpace ℝ (Fin d ⊕ Fin 3), ‖e₀‖ = 1 ∧ v₀ = ⟪e₀, v₀⟫ • e₀ := by
  by_cases hv : v₀ = 0
  · exact ⟨bSpare d 0, norm_bSpare d 0, by simp [hv]⟩
  · have hn : 0 < ‖v₀‖ := norm_pos_iff.mpr hv
    refine ⟨‖v₀‖⁻¹ • v₀, ?_, ?_⟩
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    · rw [real_inner_smul_left, real_inner_self_eq_norm_sq, smul_smul]
      have hc : ‖v₀‖⁻¹ * ‖v₀‖ ^ 2 * ‖v₀‖⁻¹ = 1 := by field_simp [hn.ne']
      rw [hc, one_smul]

private theorem exists_unit_perp_one {d : ℕ} (e₀ v₁ : EuclideanSpace ℝ (Fin d ⊕ Fin 3))
    (he₀ : ‖e₀‖ = 1) :
    ∃ e₁ : EuclideanSpace ℝ (Fin d ⊕ Fin 3),
      ‖e₁‖ = 1 ∧ ⟪e₀, e₁⟫ = 0 ∧ v₁ = ⟪e₀, v₁⟫ • e₀ + ⟪e₁, v₁⟫ • e₁ := by
  set u := v₁ - ⟪e₀, v₁⟫ • e₀
  have heu : ⟪e₀, u⟫ = 0 := by
    simp [u, inner_sub_right, inner_smul_right, he₀]
  by_cases hu : u ≠ 0
  · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let e₁ := ‖u‖⁻¹ • u
    have he₁_norm : ‖e₁‖ = 1 := by
      dsimp [e₁]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have he₁_orth : ⟪e₀, e₁⟫ = 0 := by
      dsimp [e₁]; rw [inner_smul_right, heu, mul_zero]
    have he₁_v : ⟪e₁, v₁⟫ • e₁ = u := by
      have hv_eq : v₁ = u + ⟪e₀, v₁⟫ • e₀ := by dsimp [u]; abel
      rw [hv_eq, inner_add_right, inner_smul_right, real_inner_comm e₀ e₁, he₁_orth, mul_zero,
        add_zero]
      dsimp [e₁]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, smul_smul]
      have hc : ‖u‖⁻¹ * ‖u‖ ^ 2 * ‖u‖⁻¹ = 1 := by field_simp [hn.ne']
      rw [hc, one_smul]
    exact ⟨e₁, he₁_norm, he₁_orth, by rw [he₁_v]; dsimp [u]; abel⟩
  · push Not at hu
    have hv₁_eq : v₁ = ⟪e₀, v₁⟫ • e₀ := sub_eq_zero.mp hu
    set u' := bSpare d 0 - ⟪e₀, bSpare d 0⟫ • e₀
    by_cases hu' : u' ≠ 0
    · have hn : 0 < ‖u'‖ := norm_pos_iff.mpr hu'
      let e₁ := ‖u'‖⁻¹ • u'
      have he₁_norm : ‖e₁‖ = 1 := by
        dsimp [e₁]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
      have he₁_orth : ⟪e₀, e₁⟫ = 0 := by
        dsimp [e₁, u']
        rw [inner_smul_right, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, he₀]
        ring
      have he1v : ⟪e₁, v₁⟫ = 0 := by
        rw [hv₁_eq, inner_smul_right, real_inner_comm e₀ e₁, he₁_orth, mul_zero]
      exact ⟨e₁, he₁_norm, he₁_orth, by rw [he1v, zero_smul, add_zero, ← hv₁_eq]⟩
    · push Not at hu'
      have hb0 : bSpare d 0 = ⟪e₀, bSpare d 0⟫ • e₀ := sub_eq_zero.mp hu'
      have hc_ne : ⟪e₀, bSpare d 0⟫ ≠ 0 := by
        intro hc0
        have hnorm := norm_bSpare d 0
        rw [hb0, hc0, zero_smul, norm_zero] at hnorm
        norm_num at hnorm
      have horth1 : ⟪e₀, bSpare d 1⟫ = 0 := by
        have h01 : ⟪bSpare d 0, bSpare d 1⟫ = 0 := by rw [inner_bSpare]; simp
        rw [hb0, real_inner_smul_left] at h01
        exact (mul_eq_zero.mp h01).resolve_left hc_ne
      have hb1v : ⟪bSpare d 1, v₁⟫ = 0 := by
        rw [hv₁_eq, inner_smul_right, real_inner_comm e₀ (bSpare d 1), horth1, mul_zero]
      exact ⟨bSpare d 1, norm_bSpare d 1, horth1, by rw [hb1v, zero_smul, add_zero, ← hv₁_eq]⟩

private theorem exists_unit_perp_two {d : ℕ} (e₀ e₁ v₂ : EuclideanSpace ℝ (Fin d ⊕ Fin 3))
    (he₀ : ‖e₀‖ = 1) (he₁ : ‖e₁‖ = 1) (h01 : ⟪e₀, e₁⟫ = 0) :
    ∃ e₂ : EuclideanSpace ℝ (Fin d ⊕ Fin 3),
      ‖e₂‖ = 1 ∧ ⟪e₀, e₂⟫ = 0 ∧ ⟪e₁, e₂⟫ = 0 ∧
        v₂ = ⟪e₀, v₂⟫ • e₀ + ⟪e₁, v₂⟫ • e₁ + ⟪e₂, v₂⟫ • e₂ := by
  set u := v₂ - ⟪e₀, v₂⟫ • e₀ - ⟪e₁, v₂⟫ • e₁
  have he0u : ⟪e₀, u⟫ = 0 := by
    simp [u, inner_sub_right, inner_smul_right, he₀, h01]
  have he1u : ⟪e₁, u⟫ = 0 := by
    simp [u, inner_sub_right, inner_smul_right, he₁, real_inner_comm e₀ e₁, h01]
  by_cases hu : u ≠ 0
  · have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu
    let e₂ := ‖u‖⁻¹ • u
    have he2_norm : ‖e₂‖ = 1 := by
      dsimp [e₂]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have he02 : ⟪e₀, e₂⟫ = 0 := by dsimp [e₂]; rw [inner_smul_right, he0u, mul_zero]
    have he12 : ⟪e₁, e₂⟫ = 0 := by dsimp [e₂]; rw [inner_smul_right, he1u, mul_zero]
    have he2_v : ⟪e₂, v₂⟫ • e₂ = u := by
      have hv_eq : v₂ = u + ⟪e₀, v₂⟫ • e₀ + ⟪e₁, v₂⟫ • e₁ := by dsimp [u]; abel
      rw [hv_eq, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
        real_inner_comm e₀ e₂, he02, real_inner_comm e₁ e₂, he12, mul_zero, mul_zero, add_zero,
        add_zero]
      dsimp [e₂]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq, smul_smul]
      have hc : ‖u‖⁻¹ * ‖u‖ ^ 2 * ‖u‖⁻¹ = 1 := by field_simp [hn.ne']
      rw [hc, one_smul]
    exact ⟨e₂, he2_norm, he02, he12, by rw [he2_v]; dsimp [u]; abel⟩
  · push Not at hu
    have hv₂_eq : v₂ = ⟪e₀, v₂⟫ • e₀ + ⟪e₁, v₂⟫ • e₁ := by
      rw [← sub_eq_zero.mp hu]; abel
    let uk (k : Fin 3) := bSpare d k - ⟪e₀, bSpare d k⟫ • e₀ - ⟪e₁, bSpare d k⟫ • e₁
    have hex_k : ∃ k : Fin 3, uk k ≠ 0 := by
      by_contra! hall
      have h10 : ⟪e₁, e₀⟫ = 0 := by rw [real_inner_comm, h01]
      have h00 : ⟪e₀, e₀⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he₀, one_pow]
      have h11 : ⟪e₁, e₁⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he₁, one_pow]
      have hsq_k (k : Fin 3) : 1 = ⟪e₀, bSpare d k⟫ ^ 2 + ⟪e₁, bSpare d k⟫ ^ 2 := by
        have hk : bSpare d k = ⟪e₀, bSpare d k⟫ • e₀ + ⟪e₁, bSpare d k⟫ • e₁ := by
          have h0 := hall k
          dsimp [uk] at h0
          calc bSpare d k = (bSpare d k - ⟪e₀, bSpare d k⟫ • e₀ - ⟪e₁, bSpare d k⟫ • e₁) +
                ⟪e₀, bSpare d k⟫ • e₀ + ⟪e₁, bSpare d k⟫ • e₁ := by abel
            _ = ⟪e₀, bSpare d k⟫ • e₀ + ⟪e₁, bSpare d k⟫ • e₁ := by rw [h0, zero_add]
        have h1 : ⟪bSpare d k, bSpare d k⟫ = 1 := by
          rw [real_inner_self_eq_norm_sq, norm_bSpare, one_pow]
        rw [hk] at h1
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
          h00, h11, h01, h10] at h1
        linarith
      have hbessel (w : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
          ∑ k : Fin 3, ⟪w, bSpare d k⟫ ^ 2 ≤ ‖w‖ ^ 2 := by
        have hinner (k : Fin 3) : ⟪w, bSpare d k⟫ = w.ofLp (Sum.inr k) := by
          simp [bSpare, EuclideanSpace.inner_single_right]
        simp_rw [hinner]
        rw [EuclideanSpace.norm_sq_eq]
        simp only [Real.norm_eq_abs, sq_abs, Fintype.sum_sum_type]
        have hnonneg : 0 ≤ ∑ i : Fin d, w.ofLp (Sum.inl i) ^ 2 :=
          Finset.sum_nonneg fun _ _ => sq_nonneg _
        linarith
      have hsum3 : (3 : ℝ) = ∑ k : Fin 3, (⟪e₀, bSpare d k⟫ ^ 2 + ⟪e₁, bSpare d k⟫ ^ 2) := by
        simp_rw [← hsq_k]; norm_num
      rw [Finset.sum_add_distrib] at hsum3
      have hb0 := hbessel e₀
      have hb1 := hbessel e₁
      rw [he₀, one_pow] at hb0
      rw [he₁, one_pow] at hb1
      linarith
    obtain ⟨k, hk⟩ := hex_k
    have hn : 0 < ‖uk k‖ := norm_pos_iff.mpr hk
    let e₂ := ‖uk k‖⁻¹ • uk k
    have he2_norm : ‖e₂‖ = 1 := by
      dsimp [e₂]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have he02 : ⟪e₀, e₂⟫ = 0 := by
      dsimp [e₂, uk]
      rw [inner_smul_right, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, he₀, h01]
      ring
    have he12 : ⟪e₁, e₂⟫ = 0 := by
      dsimp [e₂, uk]
      rw [inner_smul_right, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right,
        real_inner_self_eq_norm_sq, he₁, real_inner_comm e₀ e₁, h01]
      ring
    refine ⟨e₂, he2_norm, he02, he12, ?_⟩
    have he2v : ⟪e₂, v₂⟫ = 0 := by
      rw [hv₂_eq, inner_add_right, inner_smul_right, inner_smul_right,
        real_inner_comm e₀ e₂, he02, real_inner_comm e₁ e₂, he12]
      ring
    rw [he2v, zero_smul, add_zero, ← hv₂_eq]

private theorem exists_orthonormal_fin3_span {d : ℕ}
    (v₀ v₁ v₂ : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
    ∃ e : Fin 3 → EuclideanSpace ℝ (Fin d ⊕ Fin 3),
      (∀ k, ‖e k‖ = 1) ∧ Pairwise (fun j k => ⟪e j, e k⟫ = 0) ∧
        (v₀ = ∑ k : Fin 3, ⟪e k, v₀⟫ • e k) ∧
        (v₁ = ∑ k : Fin 3, ⟪e k, v₁⟫ • e k) ∧
        (v₂ = ∑ k : Fin 3, ⟪e k, v₂⟫ • e k) := by
  obtain ⟨e₀, he₀, hv₀⟩ := exists_unit_span_one v₀
  obtain ⟨e₁, he₁, h01, hv₁⟩ := exists_unit_perp_one e₀ v₁ he₀
  obtain ⟨e₂, he₂, h02, h12, hv₂⟩ := exists_unit_perp_two e₀ e₁ v₂ he₀ he₁ h01
  let e : Fin 3 → EuclideanSpace ℝ (Fin d ⊕ Fin 3) := ![e₀, e₁, e₂]
  refine ⟨e, ?_, ?_, ?_, ?_, ?_⟩
  · intro k; fin_cases k <;> assumption
  · intro j k hjk
    fin_cases j <;> fin_cases k
    · exact absurd rfl hjk
    · exact h01
    · exact h02
    · exact real_inner_comm e₀ e₁ ▸ h01
    · exact absurd rfl hjk
    · exact h12
    · exact real_inner_comm e₀ e₂ ▸ h02
    · exact real_inner_comm e₁ e₂ ▸ h12
    · exact absurd rfl hjk
  · rw [Fin.sum_univ_three]
    dsimp [e]
    have h1 : ⟪e₁, v₀⟫ = 0 := by
      rw [hv₀, inner_smul_right, real_inner_comm e₀ e₁, h01, mul_zero]
    have h2 : ⟪e₂, v₀⟫ = 0 := by
      rw [hv₀, inner_smul_right, real_inner_comm e₀ e₂, h02, mul_zero]
    rw [h1, h2, zero_smul, zero_smul, add_zero, add_zero]
    exact hv₀
  · rw [Fin.sum_univ_three]
    dsimp [e]
    have h2 : ⟪e₂, v₁⟫ = 0 := by
      rw [hv₁, inner_add_right, inner_smul_right, inner_smul_right, real_inner_comm e₀ e₂, h02,
        real_inner_comm e₁ e₂, h12, mul_zero, mul_zero, add_zero]
    rw [h2, zero_smul, add_zero]
    exact hv₁
  · rw [Fin.sum_univ_three]
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
  have hmapE : (stdGaussian E).map coordE = Measure.pi fun _ : Fin d => gaussianReal 0 1 :=
    stdGaussian_map_inner_pi b.orthonormal.1 b.orthonormal.2
  have hmapF : (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))).map coordF =
      Measure.pi fun _ : Fin d => gaussianReal 0 1 := by
    refine stdGaussian_map_inner_pi (fun i => by simp) fun i j hij => ?_
    dsimp only
    rw [EuclideanSpace.inner_single_left]
    have hne : (Sum.inl j : Fin d ⊕ Fin 3) ≠ Sum.inl i := fun h => hij (Sum.inl.inj h).symm
    simp [hne]
  let fR (y : E) (ξ : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ × ℝ :=
    (∑ i, ⟪b i, y⟫ * ξ.1 i, ∑ i, ⟪b i, y⟫ * ξ.2 i)
  let ConvR : Set ((Fin d → ℝ) × (Fin d → ℝ)) :=
    {ξ | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
      w₀ * (fR y₀ ξ).1 + w₁ * (fR y₁ ξ).1 + w₂ * (fR y₂ ξ).1 = 0 ∧
      w₀ * (fR y₀ ξ).2 + w₁ * (fR y₁ ξ).2 + w₂ * (fR y₂ ξ).2 = 0}
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
  have hmeas_eq : ((stdGaussian E).prod (stdGaussian E)).real
      {p : E × E | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * ⟪y₀, p.1⟫ + w₁ * ⟪y₁, p.1⟫ + w₂ * ⟪y₂, p.1⟫ = 0 ∧
        w₀ * ⟪y₀, p.2⟫ + w₁ * ⟪y₁, p.2⟫ + w₂ * ⟪y₂, p.2⟫ = 0} =
      ((stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3)))).real
      {q | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * ⟪emb y₀, q.1⟫ + w₁ * ⟪emb y₁, q.1⟫ + w₂ * ⟪emb y₂, q.1⟫ = 0 ∧
        w₀ * ⟪emb y₀, q.2⟫ + w₁ * ⟪emb y₁, q.2⟫ + w₂ * ⟪emb y₂, q.2⟫ = 0} := by
    have hpreE : Prod.map coordE coordE ⁻¹' ConvR =
        {p : E × E | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
          w₀ * ⟪y₀, p.1⟫ + w₁ * ⟪y₁, p.1⟫ + w₂ * ⟪y₂, p.1⟫ = 0 ∧
          w₀ * ⟪y₀, p.2⟫ + w₁ * ⟪y₁, p.2⟫ + w₂ * ⟪y₂, p.2⟫ = 0} := by
      ext p; simp [ConvR, fR, ← hinner_coordE]
    have hpreF : Prod.map coordF coordF ⁻¹' ConvR =
        {q | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
          w₀ * ⟪emb y₀, q.1⟫ + w₁ * ⟪emb y₁, q.1⟫ + w₂ * ⟪emb y₂, q.1⟫ = 0 ∧
          w₀ * ⟪emb y₀, q.2⟫ + w₁ * ⟪emb y₁, q.2⟫ + w₂ * ⟪emb y₂, q.2⟫ = 0} := by
      ext q; simp [ConvR, fR, ← hinner_coordF]
    have hmpE1 : MeasurePreserving coordE (stdGaussian E)
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
      ⟨by unfold coordE; fun_prop, hmapE⟩
    have hmpF1 : MeasurePreserving coordF (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3)))
        (Measure.pi fun _ : Fin d => gaussianReal 0 1) :=
      ⟨by unfold coordF; fun_prop, hmapF⟩
    rw [← hpreE, ← hpreF, (hmpE1.prod hmpE1).measureReal_preimage hConvRm.nullMeasurableSet,
      (hmpF1.prod hmpF1).measureReal_preimage hConvRm.nullMeasurableSet]
  rw [hmeas_eq]
  obtain ⟨e, he_norm, he_orth, hspan₀, hspan₁, hspan₂⟩ :=
    exists_orthonormal_fin3_span (emb y₀) (emb y₁) (emb y₂)
  let vx : Fin 3 → ℝ := fun k => ⟪e k, emb x⟫
  have hvx_le : normSq3 vx ≤ 1 := by
    let rem : EuclideanSpace ℝ (Fin d ⊕ Fin 3) := emb x - (vx 0 • e 0 + vx 1 • e 1 + vx 2 • e 2)
    have hrem : 0 ≤ ⟪rem, rem⟫ := real_inner_self_nonneg
    have hexp : ⟪rem, rem⟫ = 1 - normSq3 vx := by
      have hx1 : ⟪emb x, emb x⟫ = 1 := by rw [hemb_inner, real_inner_self_eq_norm_sq, hx, one_pow]
      have h00 : ⟪e 0, e 0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he_norm 0, one_pow]
      have h11 : ⟪e 1, e 1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he_norm 1, one_pow]
      have h22 : ⟪e 2, e 2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he_norm 2, one_pow]
      have h01 := he_orth (by decide : (0 : Fin 3) ≠ 1)
      have h02 := he_orth (by decide : (0 : Fin 3) ≠ 2)
      have h12 := he_orth (by decide : (1 : Fin 3) ≠ 2)
      have h10 : ⟪e 1, e 0⟫ = 0 := real_inner_comm (e 0) (e 1) ▸ h01
      have h20 : ⟪e 2, e 0⟫ = 0 := real_inner_comm (e 0) (e 2) ▸ h02
      have h21 : ⟪e 2, e 1⟫ = 0 := real_inner_comm (e 1) (e 2) ▸ h12
      have hx0 : ⟪emb x, e 0⟫ = vx 0 := real_inner_comm (e 0) (emb x)
      have hx1' : ⟪emb x, e 1⟫ = vx 1 := real_inner_comm (e 1) (emb x)
      have hx2 : ⟪emb x, e 2⟫ = vx 2 := real_inner_comm (e 2) (emb x)
      dsimp [rem, normSq3]
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
        real_inner_smul_left, inner_smul_right, hx1, h00, h11, h22, h01, h02, h12, h10, h20, h21,
        hx0, hx1', hx2]
      dsimp [vx]
      ring
    linarith only [hrem, hexp]
  let cy (m : Fin 3) : Fin 3 → ℝ :=
    match m with
    | 0 => fun k => ⟪e k, emb y₀⟫
    | 1 => fun k => ⟪e k, emb y₁⟫
    | 2 => fun k => ⟪e k, emb y₂⟫
  have hdot_vx (y : E) (hsp : emb y = ∑ k : Fin 3, ⟪e k, emb y⟫ • e k) :
      dot3 (fun k => ⟪e k, emb y⟫) vx = ⟪y, x⟫ := by
    rw [← hemb_inner y x]
    conv_rhs => rw [hsp]
    rw [Fin.sum_univ_three]
    simp only [inner_add_left, real_inner_smul_left, dot3, vx]
  have hcy0_vx : κ ≤ dot3 (cy 0) vx := by simpa [cy, hdot_vx y₀ hspan₀] using hy₀
  have hcy1_vx : κ ≤ dot3 (cy 1) vx := by simpa [cy, hdot_vx y₁ hspan₁] using hy₁
  have hcy2_vx : κ ≤ dot3 (cy 2) vx := by simpa [cy, hdot_vx y₂ hspan₂] using hy₂
  have hnorm_cy (y : E) (hsp : emb y = ∑ k : Fin 3, ⟪e k, emb y⟫ • e k) (hn : ‖y‖ ≤ 1) :
      normSq3 (fun k => ⟪e k, emb y⟫) ≤ 1 := by
    have h1 : ⟪emb y, emb y⟫ ≤ 1 := by
      rw [hemb_inner, real_inner_self_eq_norm_sq]
      exact pow_le_one₀ (norm_nonneg y) hn
    have h00 : ⟪e 0, e 0⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he_norm 0, one_pow]
    have h11 : ⟪e 1, e 1⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he_norm 1, one_pow]
    have h22 : ⟪e 2, e 2⟫ = 1 := by rw [real_inner_self_eq_norm_sq, he_norm 2, one_pow]
    have h01 := he_orth (by decide : (0 : Fin 3) ≠ 1)
    have h02 := he_orth (by decide : (0 : Fin 3) ≠ 2)
    have h12 := he_orth (by decide : (1 : Fin 3) ≠ 2)
    have h10 : ⟪e 1, e 0⟫ = 0 := real_inner_comm (e 0) (e 1) ▸ h01
    have h20 : ⟪e 2, e 0⟫ = 0 := real_inner_comm (e 0) (e 2) ▸ h02
    have h21 : ⟪e 2, e 1⟫ = 0 := real_inner_comm (e 1) (e 2) ▸ h12
    conv at h1 => lhs; rw [hsp, Fin.sum_univ_three]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
      h00, h11, h22, h01, h02, h12, h10, h20, h21] at h1
    dsimp [normSq3]
    linarith only [h1]
  have hvx_pos : 0 < normSq3 vx := by
    have hcs : (dot3 (cy 0) vx) ^ 2 ≤ normSq3 (cy 0) * normSq3 vx := by
      have hid : normSq3 (cy 0) * normSq3 vx - (dot3 (cy 0) vx) ^ 2 =
          (cy 0 0 * vx 1 - cy 0 1 * vx 0) ^ 2 +
          (cy 0 1 * vx 2 - cy 0 2 * vx 1) ^ 2 +
          (cy 0 2 * vx 0 - cy 0 0 * vx 2) ^ 2 := by dsimp [dot3, normSq3]; ring
      have hnn : 0 ≤ (cy 0 0 * vx 1 - cy 0 1 * vx 0) ^ 2 +
          (cy 0 1 * vx 2 - cy 0 2 * vx 1) ^ 2 +
          (cy 0 2 * vx 0 - cy 0 0 * vx 2) ^ 2 := by positivity
      linarith only [hid, hnn]
    have hcy0_le : normSq3 (cy 0) ≤ 1 := hnorm_cy y₀ hspan₀ hnorm₀
    have hκ_sq : 0 < κ ^ 2 := pow_pos hκ0 2
    have hle1 : κ ^ 2 ≤ (dot3 (cy 0) vx) ^ 2 := sq_le_sq' (by linarith only [hκ0, hcy0_vx]) hcy0_vx
    have hle2 : normSq3 (cy 0) * normSq3 vx ≤ 1 * normSq3 vx :=
      mul_le_mul_of_nonneg_right hcy0_le (normSq3_nonneg vx)
    linarith only [hκ_sq, hle1, hcs, hle2]
  let vUnit : Fin 3 → ℝ := fun k => (√(normSq3 vx))⁻¹ * vx k
  have hvUnit : normSq3 vUnit = 1 := normSq3_inv_sqrt_mul hvx_pos
  have hsqrt_vx_le_one : √(normSq3 vx) ≤ 1 := by
    rw [← sqrt_one]; exact sqrt_le_sqrt hvx_le
  have hinv_ge_one : 1 ≤ (√(normSq3 vx))⁻¹ :=
    one_le_inv_iff₀.mpr ⟨sqrt_pos.mpr hvx_pos, hsqrt_vx_le_one⟩
  let proj3 (w : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) : Fin 3 → ℝ := fun k => ⟪e k, w⟫
  have hmp3_single : MeasurePreserving proj3
      (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))) P3Measure :=
    ⟨by unfold proj3; fun_prop, stdGaussian_map_inner_pi he_norm he_orth⟩
  have hmp3 : MeasurePreserving (Prod.map proj3 proj3)
      ((stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3)))) (P3Measure.prod P3Measure) :=
    hmp3_single.prod hmp3_single
  let Cone3 : Set ((Fin 3 → ℝ) × (Fin 3 → ℝ)) :=
    {ab | κ ^ 2 * normSq3 (cross3 ab.1 ab.2) ≤ (dot3 vUnit (cross3 ab.1 ab.2)) ^ 2}
  have hCone3m : MeasurableSet Cone3 := by
    have hcc : Continuous fun ab : (Fin 3 → ℝ) × (Fin 3 → ℝ) => cross3 ab.1 ab.2 := by
      unfold cross3
      refine continuous_pi fun i => ?_
      fin_cases i <;> (dsimp; fun_prop)
    exact (isClosed_le
      (continuous_const.mul ((by unfold normSq3; fun_prop : Continuous normSq3).comp hcc))
      (((by unfold dot3; fun_prop : Continuous (dot3 vUnit)).comp hcc).pow 2)).measurableSet
  have hsub : {q : EuclideanSpace ℝ (Fin d ⊕ Fin 3) × EuclideanSpace ℝ (Fin d ⊕ Fin 3) |
      ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * ⟪emb y₀, q.1⟫ + w₁ * ⟪emb y₁, q.1⟫ + w₂ * ⟪emb y₂, q.1⟫ = 0 ∧
        w₀ * ⟪emb y₀, q.2⟫ + w₁ * ⟪emb y₁, q.2⟫ + w₂ * ⟪emb y₂, q.2⟫ = 0} ⊆
      Prod.map proj3 proj3 ⁻¹' Cone3 := by
    rintro ⟨q₁, q₂⟩ ⟨w₀, w₁, w₂, hw₀, hw₁, hw₂, hsum, hq₁, hq₂⟩
    simp only [mem_preimage, Prod.map_apply, Cone3, mem_ofPred_eq]
    have hinner_proj (y : E) (hsp : emb y = ∑ k : Fin 3, ⟪e k, emb y⟫ • e k)
        (q : EuclideanSpace ℝ (Fin d ⊕ Fin 3)) :
        ⟪emb y, q⟫ = dot3 (fun k => ⟪e k, emb y⟫) (proj3 q) := by
      conv_lhs => rw [hsp, Fin.sum_univ_three]
      simp [inner_add_left, real_inner_smul_left, dot3, proj3]
    rw [hinner_proj y₀ hspan₀ q₁, hinner_proj y₁ hspan₁ q₁, hinner_proj y₂ hspan₂ q₁] at hq₁
    rw [hinner_proj y₀ hspan₀ q₂, hinner_proj y₁ hspan₁ q₂, hinner_proj y₂ hspan₂ q₂] at hq₂
    let c : Fin 3 → ℝ := fun k => w₀ * cy 0 k + w₁ * cy 1 k + w₂ * cy 2 k
    have hca : dot3 c (proj3 q₁) = 0 := by
      have hid : dot3 c (proj3 q₁) = w₀ * dot3 (cy 0) (proj3 q₁) + w₁ * dot3 (cy 1) (proj3 q₁) +
          w₂ * dot3 (cy 2) (proj3 q₁) := by dsimp [c, dot3]; ring
      change w₀ * dot3 (cy 0) (proj3 q₁) + w₁ * dot3 (cy 1) (proj3 q₁) +
        w₂ * dot3 (cy 2) (proj3 q₁) = 0 at hq₁
      linarith only [hid, hq₁]
    have hcb : dot3 c (proj3 q₂) = 0 := by
      have hid : dot3 c (proj3 q₂) = w₀ * dot3 (cy 0) (proj3 q₂) + w₁ * dot3 (cy 1) (proj3 q₂) +
          w₂ * dot3 (cy 2) (proj3 q₂) := by dsimp [c, dot3]; ring
      change w₀ * dot3 (cy 0) (proj3 q₂) + w₁ * dot3 (cy 1) (proj3 q₂) +
        w₂ * dot3 (cy 2) (proj3 q₂) = 0 at hq₂
      linarith only [hid, hq₂]
    have hc_v : κ ≤ dot3 c vUnit := by
      have hcvx : κ ≤ dot3 c vx := by
        have hid : dot3 c vx = w₀ * dot3 (cy 0) vx + w₁ * dot3 (cy 1) vx + w₂ * dot3 (cy 2) vx := by
          dsimp [c, dot3]; ring
        have hm0 := mul_le_mul_of_nonneg_left hcy0_vx hw₀
        have hm1 := mul_le_mul_of_nonneg_left hcy1_vx hw₁
        have hm2 := mul_le_mul_of_nonneg_left hcy2_vx hw₂
        have hsum_κ : (w₀ + w₁ + w₂) * κ = κ := by rw [hsum, one_mul]
        have hexp_κ : (w₀ + w₁ + w₂) * κ = w₀ * κ + w₁ * κ + w₂ * κ := by ring
        linarith only [hid, hm0, hm1, hm2, hsum_κ, hexp_κ]
      have hcu : dot3 c vUnit = (√(normSq3 vx))⁻¹ * dot3 c vx := by
        dsimp [vUnit, dot3]; ring
      have hpos_cvx : 0 ≤ dot3 c vx := le_trans hκ0.le hcvx
      have hm := mul_le_mul hinv_ge_one hcvx hκ0.le (le_trans zero_le_one hinv_ge_one)
      linarith only [hcu, hm]
    have hc_norm : normSq3 c ≤ 1 := by
      have h0 : normSq3 (cy 0) ≤ 1 := hnorm_cy y₀ hspan₀ hnorm₀
      have h1 : normSq3 (cy 1) ≤ 1 := hnorm_cy y₁ hspan₁ hnorm₁
      have h2 : normSq3 (cy 2) ≤ 1 := hnorm_cy y₂ hspan₂ hnorm₂
      have hjensen : normSq3 c ≤ w₀ * normSq3 (cy 0) + w₁ * normSq3 (cy 1) +
          w₂ * normSq3 (cy 2) := by
        have hdiff : (w₀ + w₁ + w₂) * (w₀ * normSq3 (cy 0) + w₁ * normSq3 (cy 1) +
            w₂ * normSq3 (cy 2)) - normSq3 c =
            w₀ * w₁ * normSq3 (fun k => cy 0 k - cy 1 k) +
            w₁ * w₂ * normSq3 (fun k => cy 1 k - cy 2 k) +
            w₂ * w₀ * normSq3 (fun k => cy 2 k - cy 0 k) := by
          dsimp [c, normSq3]; ring
        have hrhs : 0 ≤ w₀ * w₁ * normSq3 (fun k => cy 0 k - cy 1 k) +
            w₁ * w₂ * normSq3 (fun k => cy 1 k - cy 2 k) +
            w₂ * w₀ * normSq3 (fun k => cy 2 k - cy 0 k) :=
          add_nonneg (add_nonneg
            (mul_nonneg (mul_nonneg hw₀ hw₁) (normSq3_nonneg _))
            (mul_nonneg (mul_nonneg hw₁ hw₂) (normSq3_nonneg _)))
            (mul_nonneg (mul_nonneg hw₂ hw₀) (normSq3_nonneg _))
        rw [hsum, one_mul] at hdiff
        linarith only [hdiff, hrhs]
      have hm0 := mul_le_mul_of_nonneg_left h0 hw₀
      have hm1 := mul_le_mul_of_nonneg_left h1 hw₁
      have hm2 := mul_le_mul_of_nonneg_left h2 hw₂
      linarith only [hjensen, hm0, hm1, hm2, hsum]
    have hid := mul_sq_dot3_cross3_eq (v := vUnit) hca hcb
    have hcv_sq : κ ^ 2 ≤ (dot3 c vUnit) ^ 2 := sq_le_sq' (by linarith only [hκ0, hc_v]) hc_v
    have h1 : κ ^ 2 * normSq3 (cross3 (proj3 q₁) (proj3 q₂)) ≤
        (dot3 c vUnit) ^ 2 * normSq3 (cross3 (proj3 q₁) (proj3 q₂)) :=
      mul_le_mul_of_nonneg_right hcv_sq (normSq3_nonneg _)
    rw [← hid] at h1
    have h2 : normSq3 c * (dot3 vUnit (cross3 (proj3 q₁) (proj3 q₂))) ^ 2 ≤
        1 * (dot3 vUnit (cross3 (proj3 q₁) (proj3 q₂))) ^ 2 :=
      mul_le_mul_of_nonneg_right hc_norm (sq_nonneg _)
    linarith only [h1, h2]
  calc ((stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin d ⊕ Fin 3)))).real
        {q | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
          w₀ * ⟪emb y₀, q.1⟫ + w₁ * ⟪emb y₁, q.1⟫ + w₂ * ⟪emb y₂, q.1⟫ = 0 ∧
          w₀ * ⟪emb y₀, q.2⟫ + w₁ * ⟪emb y₁, q.2⟫ + w₂ * ⟪emb y₂, q.2⟫ = 0}
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
  let S : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ ι) :=
    {p | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
      w₀ * (fLp y₀ p).1 + w₁ * (fLp y₁ p).1 + w₂ * (fLp y₂ p).1 = 0 ∧
      w₀ * (fLp y₀ p).2 + w₁ * (fLp y₁ p).2 + w₂ * (fLp y₂ p).2 = 0}
  have hSm : MeasurableSet S :=
    measurableSet_convex_zero_three (f₀ := fLp y₀) (f₁ := fLp y₁) (f₂ := fLp y₂)
      (by unfold fLp; fun_prop) (by unfold fLp; fun_prop) (by unfold fLp; fun_prop)
  have hmp := (measurePreserving_toLp_pi_gaussianReal ι).prod
    (measurePreserving_toLp_pi_gaussianReal ι)
  have hpre : Prod.map (WithLp.toLp 2) (WithLp.toLp 2) ⁻¹' S =
      {ω : (ι → ℝ) × (ι → ℝ) | ∃ w₀ w₁ w₂ : ℝ, 0 ≤ w₀ ∧ 0 ≤ w₁ ∧ 0 ≤ w₂ ∧ w₀ + w₁ + w₂ = 1 ∧
        w₀ * ⟪y₀, WithLp.toLp 2 ω.1⟫ + w₁ * ⟪y₁, WithLp.toLp 2 ω.1⟫ +
          w₂ * ⟪y₂, WithLp.toLp 2 ω.1⟫ = 0 ∧
        w₀ * ⟪y₀, WithLp.toLp 2 ω.2⟫ + w₁ * ⟪y₁, WithLp.toLp 2 ω.2⟫ +
          w₂ * ⟪y₂, WithLp.toLp 2 ω.2⟫ = 0} := rfl
  rw [← hpre, hmp.measureReal_preimage hSm.nullMeasurableSet]
  exact measureReal_stdGaussian_prod_convex_zero_le hx hκ0 hκ1 hy₀ hy₁ hy₂ hnorm₀ hnorm₁ hnorm₂

end ProbabilityTheory
