/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Probability/Distributions/Gaussian/`
-- `Slepian.lean`)

public import CslibFrontier.Foundations.Probability.Gaussian.CDF
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.QuadrantDeriv
import CslibFrontier.Foundations.Probability.Gaussian.Real
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard
import CslibFrontier.Foundations.Probability.Gaussian.Stein
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.Order.Real

/-!
# Slepian's orthant inequality and equicorrelated Gaussian straddling bounds

Let `u₁, …, u_k` and `v₁, …, v_k` be families of unit vectors in Euclidean spaces such that
`⟪v_i, v_j⟫ ≤ ⟪u_i, u_j⟫` for all `i ≠ j`. **Slepian's orthant inequality** [LedouxTalagrand1991,
Corollary 3.12] [Vershynin2018, Section 7.2] states that standard Gaussian projections onto the
more positively correlated family are at least as likely to lie simultaneously in any lower
orthant `{x | ∀ i, x_i ≤ t_i}` (`le_measureReal_forall_inner_le_of_le_inner`), and by negation
also in any upper orthant `{x | ∀ i, t_i ≤ x_i}`. Consequently, `u₁, …, u_k` straddle a scalar
threshold `t` with probability at most that of `v₁, …, v_k`.

Comparing a family whose pairwise inner products are all at least `ρ ∈ (0, 1)` against `k`
equicorrelated unit vectors `Z_i = √ρ W_0 + √(1 - ρ) W_i`, and differentiating the conditional
non-straddling integral in `t` via bivariate Gaussian density symmetry
(`ProbabilityTheory.gaussianPDFReal_mul_gaussianPDFReal_comm`), shows that the equicorrelated
straddling probability is maximized at threshold `t = 0` (`measureReal_straddlesOn_le_equicorr`):

`equicorrStraddle k ρ = 1 - ∫ z, φ(z) (Φ(-√ρ z / √(1 - ρ)) ^ k + (1 - Φ(-√ρ z / √(1 - ρ))) ^ k)`.

For `k = 3`, a non-zero triple straddles `0` if and only if `4` of its `6` ordered pairs differ in
sign, so Sheppard's formula [Sheppard1899] gives `equicorrStraddle 3 ρ = (3 / (2π)) arccos ρ`
(`equicorrStraddle_three`), which in turn evaluates the quadratic centered-cdf moment
`∫_{z > 0} φ(z) (Φ(γ z) - 1/2) ^ 2` in closed form (`two_mul_integral_Ioi_cdf_sub_half_sq`).
Together with alternating Taylor bounds for `exp (-u)` and Gordon's rational Mill's-ratio tail
lower bound `(B / (B² + 1)) φ(B) ≤ 1 - Φ(B)` (`div_sq_add_one_mul_gaussianPDFReal_le`, proved
self-contained here; cf. [Vershynin2018, Proposition 2.1.2], which records the weaker
`(1 / B - 1 / B³) φ(B)` bound for `B > 1`), this yields rational upper bounds on
`equicorrStraddle k ρ` for `k ∈ {4, 5, 6, 7}` (`equicorrStraddle_le_of_poly`).

## Main definitions

* `ProbabilityTheory.equicorrStraddle`: the threshold-`0` straddling probability of `k`
  equicorrelated standard Gaussians with pairwise correlation `ρ`.
* `ProbabilityTheory.qPolyMul`, `ProbabilityTheory.qPolyPow`, `ProbabilityTheory.qIntOdd`,
  `ProbabilityTheory.qEquicorrUpperCert`: rational polynomial arithmetic for certifying even-power
  Gaussian cdf integrals.

## Main results

* `ProbabilityTheory.le_measureReal_forall_inner_le_of_le_inner`: Slepian's orthant comparison.
* `ProbabilityTheory.measureReal_straddlesOn_le_equicorr`: straddling probability bound by
  `equicorrStraddle s.card ρ` uniformly over all thresholds `t : ℝ`.
* `ProbabilityTheory.continuousAt_equicorrStraddle`: continuity of `equicorrStraddle k` on
  `(0, 1)`.
* `ProbabilityTheory.equicorrStraddle_three`: `equicorrStraddle 3 ρ = 3 / (2 * π) * arccos ρ`.
* `ProbabilityTheory.equicorrStraddle_le_of_poly`: rational polynomial + tail upper bound on
  `equicorrStraddle k ρ` for `k ∈ {4, 5, 6, 7}`.

## References

* [M. Ledoux, M. Talagrand, *Probability in Banach Spaces*][LedouxTalagrand1991]
* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018]
* [W. F. Sheppard, *On the application of the theory of error to cases of normal distribution
  and normal correlation*][Sheppard1899]
* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

open MeasureTheory Real Set Filter
open scoped NNReal ENNReal RealInnerProductSpace Interval

namespace ProbabilityTheory

local notation "Φ" => cdf (gaussianReal 0 1)
local notation "φ" => gaussianPDFReal 0 1

/-! ### Multivariate Gaussian integration by parts and Slepian's orthant inequality -/

section OrthantComparison

/-- Coordinatewise Stein integration by parts under the standard product Gaussian measure:
`E[z_i g(z)] = E[∂_i g(z)]`. -/
private theorem integral_mul_pi_gaussianReal {α : Type*} [Fintype α] [DecidableEq α] (i : α)
    {g g' : (α → ℝ) → ℝ}
    (hg : ∀ z, HasDerivAt (fun x => g (Function.update z i x)) (g' z) (z i))
    (hgi : Integrable g (Measure.pi fun _ : α => gaussianReal 0 1))
    (hzg : Integrable (fun z => z i * g z) (Measure.pi fun _ : α => gaussianReal 0 1))
    (hg' : Integrable g' (Measure.pi fun _ : α => gaussianReal 0 1)) :
    ∫ z, z i * g z ∂Measure.pi (fun _ : α => gaussianReal 0 1) =
      ∫ z, g' z ∂Measure.pi (fun _ : α => gaussianReal 0 1) := by
  rw [← integral_integral_update _ hzg i, ← integral_integral_update _ hg' i]
  refine integral_congr_ae ?_
  filter_upwards [ae_integrable_update _ hgi i, ae_integrable_update _ hzg i,
    ae_integrable_update _ hg' i] with z h₁ h₂ h₃
  have hd : ∀ x, HasDerivAt (fun t => g (Function.update z i t))
      (g' (Function.update z i x)) x := fun x => by
    simpa only [Function.update_idem, Function.update_self] using hg (Function.update z i x)
  have hsub : Integrable (fun x => (x - 0) * g (Function.update z i x)) (gaussianReal 0 1) :=
    h₂.congr (ae_of_all _ fun x => by simp)
  have hstein := integral_sub_mul_gaussianReal (μ := 0) (v := 1) hd h₁ hsub h₃
  have hstein' : ∫ x, x * g (Function.update z i x) ∂gaussianReal 0 1 =
      ∫ x, g' (Function.update z i x) ∂gaussianReal 0 1 := by
    simpa only [sub_zero, NNReal.coe_one, one_mul] using hstein
  calc ∫ x, Function.update z i x i * g (Function.update z i x) ∂gaussianReal 0 1
      = ∫ x, x * g (Function.update z i x) ∂gaussianReal 0 1 := by
        simp_rw [Function.update_self]
    _ = ∫ x, g' (Function.update z i x) ∂gaussianReal 0 1 := hstein'

private theorem abs_gaussianPDFReal_le_one (x : ℝ) : |φ x| ≤ 1 := by
  rw [abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x), gaussianPDFReal_def]
  simp only [sub_zero, NNReal.coe_one, mul_one]
  have h2pi : (0 : ℝ) ≤ 2 * π := mul_nonneg zero_le_two pi_pos.le
  have h1 : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀
    ((le_sqrt zero_le_one h2pi).mpr (by linarith [two_le_pi]))
  have h2 : exp (-x ^ 2 / 2) ≤ 1 :=
    exp_le_one_iff.mpr (by rw [neg_div]; exact neg_nonpos.mpr (by positivity))
  nlinarith [exp_nonneg (-x ^ 2 / 2)]

private theorem prod_cdf_nonneg {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    0 ≤ ∏ i ∈ s, Φ (f i) :=
  Finset.prod_nonneg fun i _ => cdf_nonneg (gaussianReal 0 1) (f i)

private theorem prod_cdf_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ∏ i ∈ s, Φ (f i) ≤ 1 := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [Finset.prod_cons]
    exact (mul_le_of_le_one_left (prod_cdf_nonneg s f)
      (cdf_le_one (gaussianReal 0 1) (f a))).trans ih

private theorem abs_prod_cdf_le_one {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    |∏ i ∈ s, Φ (f i)| ≤ 1 := by
  rw [abs_of_nonneg (prod_cdf_nonneg s f)]
  exact prod_cdf_le_one s f

private theorem integrable_abs_coord {α : Type*} [Fintype α] (γ : α) :
    Integrable (fun ω : α → ℝ => |ω γ|) (Measure.pi fun _ : α => gaussianReal 0 1) := by
  have hpres : MeasurePreserving (Function.eval γ)
      (Measure.pi fun _ : α => gaussianReal 0 1) (gaussianReal 0 1) :=
    measurePreserving_eval (fun _ : α => gaussianReal 0 1) γ
  have h1 : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) := by
    have hp : Integrable (fun x : ℝ => x ^ 1) (gaussianReal 0 1) :=
      integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x) (by simp) 1
    simpa only [pow_one, Real.norm_eq_abs] using hp.norm
  exact hpres.integrable_comp_of_integrable h1

private theorem ae_inner_ne {V : Type*} [Fintype V] {u : EuclideanSpace ℝ V} (hu : u ≠ 0)
    (c : ℝ) : ∀ᵐ ω ∂Measure.pi (fun _ : V => gaussianReal 0 1),
      ⟪u, WithLp.toLp 2 ω⟫ ≠ c := by
  rw [ae_iff, ← measureReal_eq_zero_iff]
  have heq := measureReal_pi_gaussianReal_eq
    (s := {x : EuclideanSpace ℝ V | ⟪u, x⟫ ∈ ({c} : Set ℝ)})
    ((by fun_prop : Measurable fun x : EuclideanSpace ℝ V => ⟪u, x⟫) (measurableSet_singleton c))
  have hset : {ω : V → ℝ | ¬⟪u, WithLp.toLp 2 ω⟫ ≠ c} =
      {ω | WithLp.toLp 2 ω ∈ {x : EuclideanSpace ℝ V | ⟪u, x⟫ ∈ ({c} : Set ℝ)}} := by
    ext ω; simp
  rw [hset, heq, measureReal_def,
    nonpos_iff_eq_zero.1 ((stdGaussian_inner_mem_le hu (measurableSet_singleton c)).trans
      (by simp)),
    ENNReal.toReal_zero]

/-- Smooth mollified orthant comparison at smoothing scale `s > 0` via Kahane's interpolation. -/
private theorem mollified_orthant_le {V V' κ : Type*} [Fintype V] [Fintype V'] [Fintype κ]
    {u : κ → EuclideanSpace ℝ V} {v : κ → EuclideanSpace ℝ V'}
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (huv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ ⟪u i, u j⟫) (t : κ → ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ ω, ∏ i, Φ (s * (t i - ⟪v i, WithLp.toLp 2 (ω ∘ Sum.inl)⟫))
        ∂Measure.pi (fun _ : V' ⊕ V => gaussianReal 0 1) ≤
      ∫ ω, ∏ i, Φ (s * (t i - ⟪u i, WithLp.toLp 2 (ω ∘ Sum.inr)⟫))
        ∂Measure.pi (fun _ : V' ⊕ V => gaussianReal 0 1) := by
  classical
  set α := V' ⊕ V
  set P := Measure.pi fun _ : α => gaussianReal 0 1
  let bCoeff : κ → ℝ → α → ℝ := fun i τ γ =>
    match γ with
    | .inl b => cos τ * v i b
    | .inr a => sin τ * u i a
  let aCoeff : κ → ℝ → α → ℝ := fun i τ γ =>
    match γ with
    | .inl b => -sin τ * v i b
    | .inr a => cos τ * u i a
  let W : κ → ℝ → (α → ℝ) → ℝ := fun i τ ω => ∑ γ, bCoeff i τ γ * ω γ
  let W' : κ → ℝ → (α → ℝ) → ℝ := fun i τ ω => ∑ γ, aCoeff i τ γ * ω γ
  have hW0 (i : κ) (ω : α → ℝ) : W i 0 ω = ⟪v i, WithLp.toLp 2 (ω ∘ Sum.inl)⟫ := by
    simp only [W, α, Fintype.sum_sum_type, bCoeff, cos_zero, one_mul, sin_zero, zero_mul,
      Finset.sum_const_zero, add_zero, PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Function.comp_apply]
    exact Finset.sum_congr rfl fun b _ => mul_comm (v i b) (ω (.inl b))
  have hWpi (i : κ) (ω : α → ℝ) : W i (π / 2) ω = ⟪u i, WithLp.toLp 2 (ω ∘ Sum.inr)⟫ := by
    simp only [W, α, Fintype.sum_sum_type, bCoeff, cos_pi_div_two, zero_mul,
      Finset.sum_const_zero, zero_add, sin_pi_div_two, one_mul, PiLp.inner_apply,
      RCLike.inner_apply, conj_trivial, Function.comp_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm (u i a) (ω (.inr a))
  have hdot_diag (i : κ) (τ : ℝ) : ∑ γ, aCoeff i τ γ * bCoeff i τ γ = 0 := by
    have hv2 : ∑ b : V', (v i b) ^ 2 = 1 := by
      have h := congrArg (· ^ 2) (hv i)
      simpa [EuclideanSpace.norm_eq, sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using h
    have hu2 : ∑ a : V, (u i a) ^ 2 = 1 := by
      have h := congrArg (· ^ 2) (hu i)
      simpa [EuclideanSpace.norm_eq, sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] using h
    calc ∑ γ : α, aCoeff i τ γ * bCoeff i τ γ
        = (-sin τ * cos τ) * ∑ b : V', (v i b) ^ 2 +
            (cos τ * sin τ) * ∑ a : V, (u i a) ^ 2 := by
          rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;>
            simp only [aCoeff, bCoeff] <;> ring
      _ = 0 := by rw [hv2, hu2]; ring
  have hdot_off {i j : κ} (hij : i ≠ j) (τ : ℝ) :
      ∑ γ, aCoeff i τ γ * bCoeff j τ γ = sin τ * cos τ * (⟪u i, u j⟫ - ⟪v i, v j⟫) := by
    calc ∑ γ : α, aCoeff i τ γ * bCoeff j τ γ
        = (-sin τ * cos τ) * ∑ b : V', v j b * v i b +
            (cos τ * sin τ) * ∑ a : V, u j a * u i a := by
          rw [Fintype.sum_sum_type, Finset.mul_sum, Finset.mul_sum]
          congr 1 <;> refine Finset.sum_congr rfl fun _ _ => ?_ <;>
            simp only [aCoeff, bCoeff] <;> ring
      _ = sin τ * cos τ * (⟪u i, u j⟫ - ⟪v i, v j⟫) := by
          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
          ring
  have habs_a (i : κ) (τ : ℝ) (γ : α) : |aCoeff i τ γ| ≤ 1 := by
    cases γ with
    | inl b =>
      have hb : |v i b| ≤ 1 := (PiLp.norm_apply_le (v i) b).trans_eq (hv i)
      calc |-sin τ * v i b| = |sin τ| * |v i b| := by rw [abs_mul, abs_neg]
        _ ≤ 1 * 1 := mul_le_mul (abs_sin_le_one τ) hb (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    | inr a =>
      have ha : |u i a| ≤ 1 := (PiLp.norm_apply_le (u i) a).trans_eq (hu i)
      calc |cos τ * u i a| = |cos τ| * |u i a| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (abs_cos_le_one τ) ha (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  have habs_b (i : κ) (τ : ℝ) (γ : α) : |bCoeff i τ γ| ≤ 1 := by
    cases γ with
    | inl b =>
      have hb : |v i b| ≤ 1 := (PiLp.norm_apply_le (v i) b).trans_eq (hv i)
      calc |cos τ * v i b| = |cos τ| * |v i b| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (abs_cos_le_one τ) hb (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    | inr a =>
      have ha : |u i a| ≤ 1 := (PiLp.norm_apply_le (u i) a).trans_eq (hu i)
      calc |sin τ * u i a| = |sin τ| * |u i a| := abs_mul _ _
        _ ≤ 1 * 1 := mul_le_mul (abs_sin_le_one τ) ha (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
  let F : ℝ → (α → ℝ) → ℝ := fun τ ω => ∏ i, Φ (s * (t i - W i τ ω))
  let F' : ℝ → (α → ℝ) → ℝ := fun τ ω =>
    ∑ i, (-s * W' i τ ω * φ (s * (t i - W i τ ω))) *
      ∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))
  let Ψ : ℝ → ℝ := fun τ => ∫ ω, F τ ω ∂P
  have hW_cont (i : κ) (τ : ℝ) : Continuous (W i τ) :=
    continuous_finsetSum _ fun γ _ => continuous_const.mul (continuous_apply γ)
  have hW'_cont (i : κ) (τ : ℝ) : Continuous (W' i τ) :=
    continuous_finsetSum _ fun γ _ => continuous_const.mul (continuous_apply γ)
  have hF_meas (τ : ℝ) : AEStronglyMeasurable (F τ) P :=
    (continuous_finsetProd _ fun i _ => (continuous_cdf_gaussianReal 0 one_ne_zero).comp
      (continuous_const.mul (continuous_const.sub (hW_cont i τ)))).aestronglyMeasurable
  have hF_int (τ : ℝ) : Integrable (F τ) P :=
    Integrable.mono' (integrable_const (1 : ℝ)) (hF_meas τ)
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).trans_le (abs_prod_cdf_le_one _ _))
  have hderiv_F (ω : α → ℝ) (τ : ℝ) : HasDerivAt (fun r => F r ω) (F' τ ω) τ := by
    have hWi (i : κ) : HasDerivAt (fun r => W i r ω) (W' i τ ω) τ := by
      refine HasDerivAt.fun_sum (u := Finset.univ)
        (A := fun γ r => bCoeff i r γ * ω γ)
        (A' := fun γ => aCoeff i τ γ * ω γ) fun γ _ => ?_
      cases γ with
      | inl b =>
        exact (((hasDerivAt_cos τ).mul_const (v i b)).mul_const (ω (.inl b))).congr_deriv
          (by simp [aCoeff])
      | inr a =>
        exact (((hasDerivAt_sin τ).mul_const (u i a)).mul_const (ω (.inr a))).congr_deriv
          (by simp [aCoeff])
    have hΦi (i : κ) : HasDerivAt (fun r => Φ (s * (t i - W i r ω)))
        (-s * W' i τ ω * φ (s * (t i - W i τ ω))) τ := by
      have h := (hasDerivAt_cdf_gaussianReal 0 one_ne_zero (s * (t i - W i τ ω))).comp τ
        (((hasDerivAt_const τ (t i)).sub (hWi i)).const_mul s)
      exact h.congr_deriv (by ring)
    refine (HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun i r => Φ (s * (t i - W i r ω))) (fun i _ => hΦi i)).congr_deriv ?_
    simp only [F', smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  let boundF' : (α → ℝ) → ℝ := fun ω => (Fintype.card κ : ℝ) * s * ∑ γ : α, |ω γ|
  have hbound_int : Integrable boundF' P :=
    (integrable_finsetSum _ fun γ _ => integrable_abs_coord γ).const_mul _
  have hF'_le (τ : ℝ) (ω : α → ℝ) : ‖F' τ ω‖ ≤ boundF' ω := by
    rw [Real.norm_eq_abs]
    calc |F' τ ω|
        ≤ ∑ i : κ, |(-s * W' i τ ω * φ (s * (t i - W i τ ω))) *
            ∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : κ, s * ∑ γ : α, |ω γ| := by
          refine Finset.sum_le_sum fun i _ => ?_
          have hprod := abs_prod_cdf_le_one (Finset.univ.erase i) (fun j => s * (t j - W j τ ω))
          have hW'_le : |W' i τ ω| ≤ ∑ γ : α, |ω γ| :=
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun γ _ => by
              rw [abs_mul]
              exact mul_le_of_le_one_left (abs_nonneg _) (habs_a i τ γ))
          rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hs]
          calc s * |W' i τ ω| * |φ (s * (t i - W i τ ω))| *
                |∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))|
              ≤ s * (∑ γ : α, |ω γ|) * 1 * 1 := by
                gcongr
                exact abs_gaussianPDFReal_le_one _
            _ = s * ∑ γ : α, |ω γ| := by ring
      _ = boundF' ω := by simp [boundF', Finset.sum_const, nsmul_eq_mul, mul_assoc]
  have hF'_meas (τ : ℝ) : AEStronglyMeasurable (F' τ) P := by
    refine (continuous_finsetSum _ fun i _ => ?_).aestronglyMeasurable
    exact ((continuous_const.mul (hW'_cont i τ)).mul
      ((continuous_gaussianPDFReal 0 1).comp
        (continuous_const.mul (continuous_const.sub (hW_cont i τ))))).mul
      (continuous_finsetProd _ fun j _ => (continuous_cdf_gaussianReal 0 one_ne_zero).comp
        (continuous_const.mul (continuous_const.sub (hW_cont j τ))))
  have hΨ_deriv (τ : ℝ) : HasDerivAt Ψ (∫ ω, F' τ ω ∂P) τ :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds τ one_pos)
      (Eventually.of_forall hF_meas) (hF_int τ) (hF'_meas τ)
      (ae_of_all _ fun ω r _ => hF'_le r ω) hbound_int
      (ae_of_all _ fun ω r _ => hderiv_F ω r)).2
  have hΨ_nonneg : ∀ τ ∈ Ioo 0 (π / 2), 0 ≤ deriv Ψ τ := by
    intro τ hτ
    rw [(hΨ_deriv τ).deriv]
    have h2pi_le : τ ≤ π := hτ.2.le.trans (by linarith [pi_pos])
    have hsin : 0 ≤ sin τ := sin_nonneg_of_nonneg_of_le_pi hτ.1.le h2pi_le
    have hcos : 0 ≤ cos τ := cos_nonneg_of_mem_Icc ⟨by linarith [hτ.1, pi_pos], hτ.2.le⟩
    let G_i : κ → (α → ℝ) → ℝ := fun i ω =>
      φ (s * (t i - W i τ ω)) * ∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))
    have hF'_eq (ω : α → ℝ) :
        F' τ ω = ∑ i : κ, ∑ γ : α, (-s * aCoeff i τ γ) * (ω γ * G_i i ω) := by
      simp only [F', W', G_i]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun γ _ => ?_
      ring
    have hGi_cont (i : κ) : Continuous (G_i i) :=
      ((continuous_gaussianPDFReal 0 1).comp
        (continuous_const.mul (continuous_const.sub (hW_cont i τ)))).mul
        (continuous_finsetProd _ fun j _ => (continuous_cdf_gaussianReal 0 one_ne_zero).comp
          (continuous_const.mul (continuous_const.sub (hW_cont j τ))))
    have hGi_le_one (i : κ) (ω : α → ℝ) : |G_i i ω| ≤ 1 := by
      rw [abs_mul]
      calc |φ (s * (t i - W i τ ω))| * |∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))|
          ≤ 1 * 1 := mul_le_mul (abs_gaussianPDFReal_le_one _)
            (abs_prod_cdf_le_one _ _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hGi_int (i : κ) : Integrable (G_i i) P :=
      Integrable.mono' (integrable_const 1) (hGi_cont i).aestronglyMeasurable
        (ae_of_all _ fun ω => (Real.norm_eq_abs _).trans_le (hGi_le_one i ω))
    have hzGi_int (i : κ) (γ : α) : Integrable (fun ω => ω γ * G_i i ω) P :=
      Integrable.mono' (integrable_abs_coord γ)
        ((continuous_apply γ).mul (hGi_cont i)).aestronglyMeasurable
        (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_of_le_one_right (abs_nonneg _) (hGi_le_one i ω))
    let dG : κ → α → (α → ℝ) → ℝ := fun i γ ω =>
      (s ^ 2 * (t i - W i τ ω) * bCoeff i τ γ * φ (s * (t i - W i τ ω))) *
        (∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))) +
      φ (s * (t i - W i τ ω)) *
        ∑ j ∈ Finset.univ.erase i, (-s * bCoeff j τ γ * φ (s * (t j - W j τ ω))) *
          ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))
    have hdG_deriv (i : κ) (γ : α) (ω : α → ℝ) :
        HasDerivAt (fun x => G_i i (Function.update ω γ x)) (dG i γ ω) (ω γ) := by
      have hW_upd (k : κ) :
          HasDerivAt (fun x => W k τ (Function.update ω γ x)) (bCoeff k τ γ) (ω γ) := by
        have heq : (fun x => W k τ (Function.update ω γ x)) =
            fun x => bCoeff k τ γ * x + ∑ δ ∈ Finset.univ.erase γ, bCoeff k τ δ * ω δ := by
          funext x
          simp only [W, ← Finset.add_sum_erase _ _ (Finset.mem_univ γ), Function.update_self]
          congr 1
          refine Finset.sum_congr rfl fun δ hδ => ?_
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hδ)]
        rw [heq]
        have hid : HasDerivAt (fun x : ℝ => bCoeff k τ γ * x) (bCoeff k τ γ * 1) (ω γ) :=
          (hasDerivAt_id' (ω γ)).const_mul (bCoeff k τ γ)
        exact (hid.add_const _).congr_deriv (mul_one _)
      have hφ_upd : HasDerivAt (fun x => φ (s * (t i - W i τ (Function.update ω γ x))))
          (s ^ 2 * (t i - W i τ ω) * bCoeff i τ γ * φ (s * (t i - W i τ ω))) (ω γ) := by
        have harg : HasDerivAt (fun x => s * (t i - W i τ (Function.update ω γ x)))
            (s * (0 - bCoeff i τ γ)) (ω γ) :=
          ((hasDerivAt_const (ω γ) (t i)).sub (hW_upd i)).const_mul s
        have hbase : HasDerivAt φ
            (-((s * (t i - W i τ ω) - 0) / (1 : ℝ≥0)) * φ (s * (t i - W i τ ω)))
            (s * (t i - W i τ (Function.update ω γ (ω γ)))) := by
          rw [Function.update_eq_self]
          exact hasDerivAt_gaussianPDFReal 0 1 (s * (t i - W i τ ω))
        have h1 := hbase.comp (ω γ) harg
        simp only [sub_zero, NNReal.coe_one, div_one] at h1
        exact h1.congr_deriv (by ring)
      have hΦ_upd (j : κ) : HasDerivAt (fun x => Φ (s * (t j - W j τ (Function.update ω γ x))))
          (-s * bCoeff j τ γ * φ (s * (t j - W j τ ω))) (ω γ) := by
        have harg : HasDerivAt (fun x => s * (t j - W j τ (Function.update ω γ x)))
            (s * (0 - bCoeff j τ γ)) (ω γ) :=
          ((hasDerivAt_const (ω γ) (t j)).sub (hW_upd j)).const_mul s
        have hbase : HasDerivAt Φ (φ (s * (t j - W j τ ω)))
            (s * (t j - W j τ (Function.update ω γ (ω γ)))) := by
          rw [Function.update_eq_self]
          exact hasDerivAt_cdf_gaussianReal 0 one_ne_zero (s * (t j - W j τ ω))
        have h1 := hbase.comp (ω γ) harg
        exact h1.congr_deriv (by ring)
      have hprod_upd : HasDerivAt
          (fun x => ∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ (Function.update ω γ x))))
          (∑ j ∈ Finset.univ.erase i, (-s * bCoeff j τ γ * φ (s * (t j - W j τ ω))) *
            ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))) (ω γ) := by
        refine (HasDerivAt.fun_finsetProd (u := Finset.univ.erase i)
          (f := fun j x => Φ (s * (t j - W j τ (Function.update ω γ x))))
          (fun j _ => hΦ_upd j)).congr_deriv ?_
        simp only [Function.update_eq_self, smul_eq_mul]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      exact (hφ_upd.mul hprod_upd).congr_deriv (by simp only [dG, Function.update_eq_self])
    have hdG_int (i : κ) (γ : α) : Integrable (dG i γ) P := by
      have hcont : Continuous (dG i γ) := by
        refine Continuous.add ?_ ?_
        · exact ((((continuous_const.mul (continuous_const.sub (hW_cont i τ))).mul
            continuous_const).mul ((continuous_gaussianPDFReal 0 1).comp
            (continuous_const.mul (continuous_const.sub (hW_cont i τ))))).mul
            (continuous_finsetProd _ fun j _ => (continuous_cdf_gaussianReal 0 one_ne_zero).comp
              (continuous_const.mul (continuous_const.sub (hW_cont j τ)))))
        · exact ((continuous_gaussianPDFReal 0 1).comp
            (continuous_const.mul (continuous_const.sub (hW_cont i τ)))).mul
            (continuous_finsetSum _ fun j _ => (continuous_const.mul
              ((continuous_gaussianPDFReal 0 1).comp
                (continuous_const.mul (continuous_const.sub (hW_cont j τ))))).mul
              (continuous_finsetProd _ fun l _ => (continuous_cdf_gaussianReal 0 one_ne_zero).comp
                (continuous_const.mul (continuous_const.sub (hW_cont l τ)))))
      let dom : (α → ℝ) → ℝ := fun ω =>
        s ^ 2 * (|t i| + ∑ δ : α, |ω δ|) + (Fintype.card κ : ℝ) * s
      have hdom : Integrable dom P :=
        (((integrable_const |t i|).add
          (integrable_finsetSum _ fun δ _ => integrable_abs_coord δ)).const_mul (s ^ 2)).add
          (integrable_const _)
      refine Integrable.mono' hdom hcont.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
      rw [Real.norm_eq_abs]
      have hW_le : |t i - W i τ ω| ≤ |t i| + ∑ δ : α, |ω δ| := by
        refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun δ _ => by
          rw [abs_mul]
          exact mul_le_of_le_one_left (abs_nonneg _) (habs_b i τ δ))
      have hp1 := abs_prod_cdf_le_one (Finset.univ.erase i) (fun j => s * (t j - W j τ ω))
      have hterm1 : |(s ^ 2 * (t i - W i τ ω) * bCoeff i τ γ * φ (s * (t i - W i τ ω))) *
          ∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))| ≤
          s ^ 2 * (|t i| + ∑ δ : α, |ω δ|) := by
        rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (sq_pos_of_pos hs)]
        calc s ^ 2 * |t i - W i τ ω| * |bCoeff i τ γ| * |φ (s * (t i - W i τ ω))| *
              |∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))|
            ≤ s ^ 2 * (|t i| + ∑ δ : α, |ω δ|) * 1 * 1 * 1 := by
              gcongr
              · exact habs_b i τ γ
              · exact abs_gaussianPDFReal_le_one _
          _ = s ^ 2 * (|t i| + ∑ δ : α, |ω δ|) := by ring
      have hterm2 : |φ (s * (t i - W i τ ω)) *
          ∑ j ∈ Finset.univ.erase i, (-s * bCoeff j τ γ * φ (s * (t j - W j τ ω))) *
            ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))| ≤
          (Fintype.card κ : ℝ) * s := by
        rw [abs_mul]
        calc |φ (s * (t i - W i τ ω))| *
              |∑ j ∈ Finset.univ.erase i, (-s * bCoeff j τ γ * φ (s * (t j - W j τ ω))) *
                ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))|
            ≤ 1 * ∑ j ∈ Finset.univ.erase i, s := by
              refine mul_le_mul (abs_gaussianPDFReal_le_one _)
                ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_))
                (abs_nonneg _) zero_le_one
              rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos hs]
              have hp2 := abs_prod_cdf_le_one ((Finset.univ.erase i).erase j)
                (fun l => s * (t l - W l τ ω))
              calc s * |bCoeff j τ γ| * |φ (s * (t j - W j τ ω))| *
                    |∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))|
                  ≤ s * 1 * 1 * 1 := by
                    gcongr
                    · exact habs_b j τ γ
                    · exact abs_gaussianPDFReal_le_one _
                _ = s := by ring
          _ ≤ (Fintype.card κ : ℝ) * s := by
              rw [one_mul, Finset.sum_const, nsmul_eq_mul]
              exact mul_le_mul_of_nonneg_right
                (Nat.cast_le.mpr (Finset.card_le_univ _)) hs.le
      exact (abs_add_le _ _).trans (add_le_add hterm1 hterm2)
    have hstep (i : κ) :
        ∫ ω, (∑ γ : α, (-s * aCoeff i τ γ) * (ω γ * G_i i ω)) ∂P =
          ∫ ω, (∑ j ∈ Finset.univ.erase i,
            s ^ 2 * (sin τ * cos τ * (⟪u i, u j⟫ - ⟪v i, v j⟫)) *
              φ (s * (t i - W i τ ω)) * φ (s * (t j - W j τ ω)) *
              ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))) ∂P := by
      rw [integral_finsetSum _ fun γ _ => (hzGi_int i γ).const_mul _]
      have hstein_γ (γ : α) :
          ∫ ω, (-s * aCoeff i τ γ) * (ω γ * G_i i ω) ∂P =
            ∫ ω, (-s * aCoeff i τ γ) * dG i γ ω ∂P := by
        rw [integral_const_mul, integral_const_mul,
          integral_mul_pi_gaussianReal γ (hdG_deriv i γ) (hGi_int i) (hzGi_int i γ) (hdG_int i γ)]
      simp_rw [hstein_γ]
      rw [← integral_finsetSum _ fun γ _ => (hdG_int i γ).const_mul _]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      have hpt1 : ∑ γ : α, (-s * aCoeff i τ γ) *
          ((s ^ 2 * (t i - W i τ ω) * bCoeff i τ γ * φ (s * (t i - W i τ ω))) *
            ∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))) =
          (-s ^ 3 * (t i - W i τ ω) * φ (s * (t i - W i τ ω)) *
            ∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))) *
            (∑ γ : α, aCoeff i τ γ * bCoeff i τ γ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun γ _ => by ring
      have hpt2 : ∑ γ : α, (-s * aCoeff i τ γ) *
          (φ (s * (t i - W i τ ω)) *
            ∑ j ∈ Finset.univ.erase i, (-s * bCoeff j τ γ * φ (s * (t j - W j τ ω))) *
              ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))) =
          ∑ j ∈ Finset.univ.erase i,
            (s ^ 2 * φ (s * (t i - W i τ ω)) * φ (s * (t j - W j τ ω)) *
              ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))) *
              (∑ γ : α, aCoeff i τ γ * bCoeff j τ γ) := by
        have hexp (γ : α) : (-s * aCoeff i τ γ) *
            (φ (s * (t i - W i τ ω)) *
              ∑ j ∈ Finset.univ.erase i, (-s * bCoeff j τ γ * φ (s * (t j - W j τ ω))) *
                ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))) =
            ∑ j ∈ Finset.univ.erase i,
              (s ^ 2 * φ (s * (t i - W i τ ω)) * φ (s * (t j - W j τ ω)) *
                ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))) *
                (aCoeff i τ γ * bCoeff j τ γ) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
        simp_rw [hexp]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => (Finset.mul_sum _ _ _).symm
      have hpt : ∑ γ : α, (-s * aCoeff i τ γ) * dG i γ ω =
          (-s ^ 3 * (t i - W i τ ω) * φ (s * (t i - W i τ ω)) *
            ∏ j ∈ Finset.univ.erase i, Φ (s * (t j - W j τ ω))) *
            (∑ γ : α, aCoeff i τ γ * bCoeff i τ γ) +
          ∑ j ∈ Finset.univ.erase i,
            (s ^ 2 * φ (s * (t i - W i τ ω)) * φ (s * (t j - W j τ ω)) *
              ∏ l ∈ (Finset.univ.erase i).erase j, Φ (s * (t l - W l τ ω))) *
              (∑ γ : α, aCoeff i τ γ * bCoeff j τ γ) := by
        simp only [dG, mul_add, Finset.sum_add_distrib, hpt1, hpt2]
      dsimp only
      rw [hpt, hdot_diag i τ, mul_zero, zero_add]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hdot_off (Finset.ne_of_mem_erase hj).symm τ]
      ring
    rw [integral_congr_ae (ae_of_all _ hF'_eq),
      integral_finsetSum _ fun i _ =>
        integrable_finsetSum _ fun γ _ => (hzGi_int i γ).const_mul _]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [hstep i]
    refine integral_nonneg fun ω => Finset.sum_nonneg fun j hj => ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hdiff : 0 ≤ ⟪u i, u j⟫ - ⟪v i, v j⟫ := sub_nonneg.mpr (huv i j hij)
    have hφi := gaussianPDFReal_nonneg 0 1 (s * (t i - W i τ ω))
    have hφj := gaussianPDFReal_nonneg 0 1 (s * (t j - W j τ ω))
    have hpr := prod_cdf_nonneg ((Finset.univ.erase i).erase j) (fun l => s * (t l - W l τ ω))
    positivity
  have hmono : MonotoneOn Ψ (Icc 0 (π / 2)) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 (π / 2))
      (fun τ _ => (hΨ_deriv τ).continuousAt.continuousWithinAt)
      (fun τ _ => (hΨ_deriv τ).differentiableAt.differentiableWithinAt)
      (fun τ hτ => by rw [interior_Icc] at hτ; exact hΨ_nonneg τ hτ)
  have hle := hmono ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩ (by positivity)
  simpa only [Ψ, F, hW0, hWpi] using hle

/-- Pointwise convergence of the smooth orthant mollifier outside hyperplanes `{⟪u i, ω⟫ = t i}`. -/
private theorem tendsto_mollified_orthant {V κ : Type*} [Fintype V] [Fintype κ]
    (u : κ → EuclideanSpace ℝ V) (hu : ∀ i, u i ≠ 0) (t : κ → ℝ) :
    Tendsto (fun m : ℕ => ∫ ω, ∏ i, Φ (((m : ℝ) + 1) * (t i - ⟪u i, WithLp.toLp 2 ω⟫))
        ∂Measure.pi (fun _ : V => gaussianReal 0 1))
      atTop
      (nhds ((Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | ∀ i, ⟪u i, WithLp.toLp 2 ω⟫ ≤ t i})) := by
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set S : Set (V → ℝ) := {ω | ∀ i, ⟪u i, WithLp.toLp 2 ω⟫ ≤ t i}
  have hSm : MeasurableSet S := by
    have : S = ⋂ i : κ, {ω | ⟪u i, WithLp.toLp 2 ω⟫ ≤ t i} := by ext ω; simp [S]
    rw [this]
    exact MeasurableSet.iInter fun i => measurableSet_le (by fun_prop) measurable_const
  rw [← integral_indicator_one hSm]
  have hae : ∀ᵐ ω ∂P, ∀ i : κ, ⟪u i, WithLp.toLp 2 ω⟫ ≠ t i :=
    eventually_all.mpr fun i => ae_inner_ne (hu i) (t i)
  refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun m => ?_)
    (integrable_const (1 : ℝ)) (fun m => ae_of_all _ fun ω => ?_) ?_
  · refine (continuous_finsetProd _ fun i _ =>
      (continuous_cdf_gaussianReal 0 one_ne_zero).comp
        (continuous_const.mul (continuous_const.sub (by fun_prop)))).aestronglyMeasurable
  · exact (Real.norm_eq_abs _).trans_le (abs_prod_cdf_le_one _ _)
  · refine hae.mono fun ω hne => ?_
    by_cases hω : ω ∈ S
    · rw [indicator_of_mem hω, Pi.one_apply]
      have h1 : ∀ i ∈ (Finset.univ : Finset κ),
          Tendsto (fun m : ℕ => Φ (((m : ℝ) + 1) * (t i - ⟪u i, WithLp.toLp 2 ω⟫)))
            atTop (nhds 1) := by
        intro i _
        have hpos : 0 < t i - ⟪u i, WithLp.toLp 2 ω⟫ :=
          sub_pos.mpr (lt_of_le_of_ne (hω i) (hne i))
        exact (tendsto_cdf_atTop (gaussianReal 0 1)).comp
          ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hpos)
      simpa using tendsto_finsetProd Finset.univ h1
    · rw [indicator_of_notMem hω]
      simp only [S, mem_ofPred_eq, not_forall, not_le] at hω
      obtain ⟨i₀, hi₀⟩ := hω
      have hneg : t i₀ - ⟪u i₀, WithLp.toLp 2 ω⟫ < 0 := sub_neg.mpr hi₀
      have h0 : Tendsto (fun m : ℕ => Φ (((m : ℝ) + 1) * (t i₀ - ⟪u i₀, WithLp.toLp 2 ω⟫)))
          atTop (nhds 0) :=
        (tendsto_cdf_atBot (gaussianReal 0 1)).comp
          ((tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const_of_neg hneg)
      refine squeeze_zero (fun m => prod_cdf_nonneg _ _) (fun m => ?_) h0
      classical
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
      exact mul_le_of_le_one_right (cdf_nonneg _ _) (prod_cdf_le_one _ _)

private theorem integral_mollified_orthant_comp {W V₀ κ : Type*} [Fintype W] [Fintype V₀]
    [Fintype κ] (w : κ → EuclideanSpace ℝ V₀) (t : κ → ℝ) (proj : (W → ℝ) → (V₀ → ℝ))
    (hmp : MeasurePreserving proj (Measure.pi fun _ : W => gaussianReal 0 1)
      (Measure.pi fun _ : V₀ => gaussianReal 0 1)) (m : ℕ) :
    ∫ ω, ∏ i, Φ (((m : ℝ) + 1) * (t i - ⟪w i, WithLp.toLp 2 (proj ω)⟫))
        ∂Measure.pi (fun _ : W => gaussianReal 0 1) =
      ∫ ω₀, ∏ i, Φ (((m : ℝ) + 1) * (t i - ⟪w i, WithLp.toLp 2 ω₀⟫))
        ∂Measure.pi (fun _ : V₀ => gaussianReal 0 1) := by
  have hcont : Continuous fun ω₀ : V₀ → ℝ =>
      ∏ i, Φ (((m : ℝ) + 1) * (t i - ⟪w i, WithLp.toLp 2 ω₀⟫)) :=
    continuous_finsetProd _ fun i _ => (continuous_cdf_gaussianReal 0 one_ne_zero).comp
      (continuous_const.mul (continuous_const.sub (by fun_prop)))
  have hmeas : AEStronglyMeasurable
      (fun ω₀ : V₀ → ℝ => ∏ i, Φ (((m : ℝ) + 1) * (t i - ⟪w i, WithLp.toLp 2 ω₀⟫)))
      (Measure.map proj (Measure.pi fun _ : W => gaussianReal 0 1)) := by
    rw [hmp.map_eq]; exact hcont.aestronglyMeasurable
  exact (integral_map hmp.measurable.aemeasurable hmeas).symm.trans (by rw [hmp.map_eq])

/-- **Slepian's orthant inequality** [LedouxTalagrand1991, Corollary 3.12]
[Vershynin2018, Section 7.2]: if `u` and `v` are finite families of unit vectors with
`⟪v i, v j⟫ ≤ ⟪u i, u j⟫` for all `i ≠ j`, then standard Gaussian projections onto `u` are at
least as likely to lie simultaneously in any lower orthant `{x | ∀ i, x i ≤ t i}`. -/
theorem le_measureReal_forall_inner_le_of_le_inner {V V' κ : Type*} [Fintype V] [Fintype V']
    [Finite κ] {u : κ → EuclideanSpace ℝ V} {v : κ → EuclideanSpace ℝ V'}
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (huv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ ⟪u i, u j⟫) (t : κ → ℝ) :
    (Measure.pi fun _ : V' => gaussianReal 0 1).real {ω' | ∀ i, ⟪v i, WithLp.toLp 2 ω'⟫ ≤ t i} ≤
      (Measure.pi fun _ : V => gaussianReal 0 1).real {ω | ∀ i, ⟪u i, WithLp.toLp 2 ω⟫ ≤ t i} := by
  let _ := Fintype.ofFinite κ
  have hu0 (i : κ) : u i ≠ 0 := fun h => by have := hu i; simp [h] at this
  have hv0 (i : κ) : v i ≠ 0 := fun h => by have := hv i; simp [h] at this
  have hmp_l : MeasurePreserving (fun ω : V' ⊕ V → ℝ => ω ∘ Sum.inl)
      (Measure.pi fun _ : V' ⊕ V => gaussianReal 0 1)
      (Measure.pi fun _ : V' => gaussianReal 0 1) :=
    measurePreserving_fst.comp (measurePreserving_sumPiEquivProdPi _)
  have hmp_r : MeasurePreserving (fun ω : V' ⊕ V → ℝ => ω ∘ Sum.inr)
      (Measure.pi fun _ : V' ⊕ V => gaussianReal 0 1)
      (Measure.pi fun _ : V => gaussianReal 0 1) :=
    measurePreserving_snd.comp (measurePreserving_sumPiEquivProdPi _)
  exact le_of_tendsto_of_tendsto (tendsto_mollified_orthant v hv0 t)
    (tendsto_mollified_orthant u hu0 t) (Eventually.of_forall fun m => by
      dsimp only
      rw [← integral_mollified_orthant_comp v t _ hmp_l m,
        ← integral_mollified_orthant_comp u t _ hmp_r m]
      exact mollified_orthant_le hu hv huv t (by positivity))

/-- Upper-orthant form of Slepian's inequality (`{∀ i, t i ≤ ⟪u i, ω⟫}`), deduced from
`le_measureReal_forall_inner_le_of_le_inner` by negating both families of unit vectors. -/
theorem le_measureReal_forall_le_inner_of_le_inner {V V' κ : Type*} [Fintype V] [Fintype V']
    [Finite κ] {u : κ → EuclideanSpace ℝ V} {v : κ → EuclideanSpace ℝ V'}
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ i, ‖v i‖ = 1)
    (huv : ∀ i j, i ≠ j → ⟪v i, v j⟫ ≤ ⟪u i, u j⟫) (t : κ → ℝ) :
    (Measure.pi fun _ : V' => gaussianReal 0 1).real {ω' | ∀ i, t i ≤ ⟪v i, WithLp.toLp 2 ω'⟫} ≤
      (Measure.pi fun _ : V => gaussianReal 0 1).real {ω | ∀ i, t i ≤ ⟪u i, WithLp.toLp 2 ω⟫} := by
  have h := le_measureReal_forall_inner_le_of_le_inner
    (u := fun i => -u i) (v := fun i => -v i)
    (fun i => by rw [norm_neg, hu i]) (fun i => by rw [norm_neg, hv i])
    (fun i j hij => by rw [inner_neg_left, inner_neg_right, neg_neg,
      inner_neg_left, inner_neg_right, neg_neg]; exact huv i j hij)
    (fun i => -t i)
  simpa only [inner_neg_left, neg_le_neg_iff] using h

end OrthantComparison

/-! ### Equicorrelated Gaussian straddling and threshold-`0` maximization -/

section Equicorrelated

/-- Conditional non-straddling probability integral for `k` equicorrelated standard Gaussians with
pairwise correlation `ρ` at threshold `t`. -/
private noncomputable def equicorrNonStraddle (k : ℕ) (ρ t : ℝ) : ℝ :=
  ∫ z, φ z * (Φ ((t - √ρ * z) / √(1 - ρ)) ^ k + (1 - Φ ((t - √ρ * z) / √(1 - ρ))) ^ k)

/-- The probability that `k` equicorrelated standard Gaussians with pairwise correlation `ρ`
straddle threshold `0` (their maximum straddling probability across all thresholds `t : ℝ`). -/
noncomputable def equicorrStraddle (k : ℕ) (ρ : ℝ) : ℝ :=
  if k ≤ 1 then 0 else 1 - equicorrNonStraddle k ρ 0

/-- Equicorrelated unit vectors in `EuclideanSpace ℝ (Unit ⊕ α)` realizing pairwise inner product
`ρ ∈ [0, 1]`. -/
private noncomputable def equicorrVec {α : Type*} [DecidableEq α] (ρ : ℝ) (i : α) :
    EuclideanSpace ℝ (Unit ⊕ α) :=
  WithLp.toLp 2 fun
    | .inl () => √ρ
    | .inr j => if i = j then √(1 - ρ) else 0

private theorem norm_equicorrVec {α : Type*} [Fintype α] [DecidableEq α] {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (i : α) : ‖equicorrVec ρ i‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ x : Unit ⊕ α, ‖equicorrVec ρ i x‖ ^ 2 = 1 := by
    rw [Fintype.sum_sum_type, Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton]
    simp only [equicorrVec, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, sq_sqrt hρ0]
    have hrest : ∑ j : α, (if i = j then √(1 - ρ) else 0) ^ 2 = 1 - ρ := by
      rw [Finset.sum_eq_single i]
      · simp [sq_sqrt (sub_nonneg.mpr hρ1)]
      · intro j _ hji
        simp [Ne.symm hji]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    linarith
  rw [hsum, sqrt_one]

private theorem inner_equicorrVec_of_ne {α : Type*} [Fintype α] [DecidableEq α] {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) {i j : α} (hij : i ≠ j) :
    ⟪equicorrVec ρ i, equicorrVec ρ j⟫ = ρ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_sum_type,
    Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton, equicorrVec]
  have hrest : ∑ l : α, (if j = l then √(1 - ρ) else 0) * (if i = l then √(1 - ρ) else 0) = 0 := by
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hjl : j = l
    · subst hjl
      simp [hij]
    · simp [hjl]
  rw [hrest, add_zero, mul_self_sqrt hρ0]

/-- Straddling complement identity for a nonempty finite family of unit projections. -/
private theorem measureReal_straddlesOn_eq_one_sub {V κ : Type*} [Fintype V] {s : Finset κ}
    (hs : s.Nonempty) (u : κ → EuclideanSpace ℝ V) (hu : ∀ i ∈ s, ‖u i‖ = 1) (t : ℝ) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | (∃ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ < t) ∧ (∃ i ∈ s, t ≤ ⟪u i, WithLp.toLp 2 ω⟫)} =
      1 - (Measure.pi fun _ : V => gaussianReal 0 1).real
            {ω | ∀ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ ≤ t} -
          (Measure.pi fun _ : V => gaussianReal 0 1).real
            {ω | ∀ i ∈ s, t ≤ ⟪u i, WithLp.toLp 2 ω⟫} := by
  set P := Measure.pi fun _ : V => gaussianReal 0 1
  set A := {ω : V → ℝ | (∃ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ < t) ∧
    (∃ i ∈ s, t ≤ ⟪u i, WithLp.toLp 2 ω⟫)}
  set B := {ω : V → ℝ | ∀ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ < t}
  set B' := {ω : V → ℝ | ∀ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ ≤ t}
  set C := {ω : V → ℝ | ∀ i ∈ s, t ≤ ⟪u i, WithLp.toLp 2 ω⟫}
  have hAm : MeasurableSet A := by
    have : A = (⋃ i ∈ s, {ω | ⟪u i, WithLp.toLp 2 ω⟫ < t}) ∩
        (⋃ i ∈ s, {ω | t ≤ ⟪u i, WithLp.toLp 2 ω⟫}) := by
      ext ω; simp [A]
    rw [this]
    exact (s.measurableSet_biUnion fun i _ => measurableSet_lt (by fun_prop) measurable_const).inter
      (s.measurableSet_biUnion fun i _ => measurableSet_le measurable_const (by fun_prop))
  have hCm : MeasurableSet C := by
    have : C = ⋂ i ∈ s, {ω | t ≤ ⟪u i, WithLp.toLp 2 ω⟫} := by ext ω; simp [C]
    rw [this]
    exact s.measurableSet_biInter fun i _ => measurableSet_le measurable_const (by fun_prop)
  have hcompl : Aᶜ = B ∪ C := by
    ext ω
    simp only [A, B, C, mem_compl_iff, mem_ofPred_eq, mem_union]
    constructor
    · intro h
      by_cases hlt : ∃ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ < t
      · exact Or.inl fun i hi => lt_of_not_ge fun hge => h ⟨hlt, ⟨i, hi, hge⟩⟩
      · exact Or.inr fun i hi => not_lt.mp fun hlt' => hlt ⟨i, hi, hlt'⟩
    · rintro (hB | hC) ⟨⟨i, hi, hlt⟩, ⟨j, hj, hge⟩⟩
      · exact (hB j hj).not_ge hge
      · exact hlt.not_ge (hC i hi)
  obtain ⟨i₀, hi₀⟩ := hs
  have hdisj : Disjoint B C := Set.disjoint_left.mpr fun ω h1 h2 => (h1 i₀ hi₀).not_ge (h2 i₀ hi₀)
  have hBB' : P.real B = P.real B' := by
    have hae : ∀ᵐ ω ∂P, ∀ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ ≠ t := by
      rw [eventually_all_finset]
      intro i hi
      exact ae_inner_ne (fun h0 => by have := hu i hi; simp [h0] at this) t
    refine measureReal_congr (eventuallyEqSet_iff.2 (hae.mono fun ω hne => ?_))
    simp only [B, B', mem_ofPred_eq]
    exact forall₂_congr fun i hi => lt_iff_le_and_ne.trans (and_iff_left (hne i hi))
  have hprob := probReal_compl_eq_one_sub (μ := P) hAm
  rw [hcompl, measureReal_union hdisj hCm, hBB'] at hprob
  linarith

/-- Exact conditioning identity for the equicorrelated lower and upper orthants. -/
private theorem equicorr_orthants_eq {α : Type*} [Fintype α] [DecidableEq α] {ρ : ℝ}
    (hρ1 : ρ < 1) (t : ℝ) :
    (Measure.pi fun _ : Unit ⊕ α => gaussianReal 0 1).real
        {ω | ∀ i : α, ⟪equicorrVec ρ i, WithLp.toLp 2 ω⟫ ≤ t} +
      (Measure.pi fun _ : Unit ⊕ α => gaussianReal 0 1).real
        {ω | ∀ i : α, t ≤ ⟪equicorrVec ρ i, WithLp.toLp 2 ω⟫} =
      equicorrNonStraddle (Fintype.card α) ρ t := by
  set s := √(1 - ρ)
  have hs : 0 < s := sqrt_pos.mpr (sub_pos.mpr hρ1)
  have hmp1 := measurePreserving_sumPiEquivProdPi (fun _ : Unit ⊕ α => gaussianReal 0 1)
  have hmp0 : MeasurePreserving (Prod.map (Function.eval ()) id)
      ((Measure.pi fun _ : Unit => gaussianReal 0 1).prod
        (Measure.pi fun _ : α => gaussianReal 0 1))
      ((gaussianReal 0 1).prod (Measure.pi fun _ : α => gaussianReal 0 1)) :=
    (measurePreserving_eval (fun _ : Unit => gaussianReal 0 1) ()).prod (MeasurePreserving.id _)
  let proj : (Unit ⊕ α → ℝ) → ℝ × (α → ℝ) :=
    Prod.map (Function.eval ()) id ∘ MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ α => ℝ)
  have hmp : MeasurePreserving proj
      (Measure.pi fun _ : Unit ⊕ α => gaussianReal 0 1)
      ((gaussianReal 0 1).prod (Measure.pi fun _ : α => gaussianReal 0 1)) :=
    hmp0.comp hmp1
  have hproj (ω : Unit ⊕ α → ℝ) : proj ω = (ω (.inl ()), ω ∘ Sum.inr) := rfl
  have hinner (ω : Unit ⊕ α → ℝ) (i : α) :
      ⟪equicorrVec ρ i, WithLp.toLp 2 ω⟫ = √ρ * ω (.inl ()) + s * ω (.inr i) := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fintype.sum_sum_type,
      Finset.univ_unique, PUnit.default_eq_unit, Finset.sum_singleton, equicorrVec, s]
    rw [Finset.sum_eq_single i]
    · simp [mul_comm]
    · intro j _ hji
      simp [Ne.symm hji]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have horth (S : Set (ℝ × (α → ℝ))) (hSm : MeasurableSet S) (f : ℝ → ℝ)
      (hf0 : ∀ z, 0 ≤ f z) (hfc : Continuous f)
      (hslice : ∀ z, (Measure.pi fun _ : α => gaussianReal 0 1) (Prod.mk z ⁻¹' S) =
        ENNReal.ofReal (f z ^ Fintype.card α)) :
      (Measure.pi fun _ : Unit ⊕ α => gaussianReal 0 1).real (proj ⁻¹' S) =
        ∫ z, φ z * f z ^ Fintype.card α := by
    rw [← map_measureReal_apply hmp.measurable hSm, hmp.map_eq, measureReal_def,
      Measure.prod_apply hSm]
    simp_rw [hslice]
    rw [← integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun z => pow_nonneg (hf0 z) _)
      (hfc.pow _).aestronglyMeasurable,
      integral_gaussianReal_eq_integral_smul one_ne_zero]
    simp only [smul_eq_mul]
  have hlower :
      (Measure.pi fun _ : Unit ⊕ α => gaussianReal 0 1).real
        {ω | ∀ i : α, ⟪equicorrVec ρ i, WithLp.toLp 2 ω⟫ ≤ t} =
      ∫ z, φ z * Φ ((t - √ρ * z) / s) ^ Fintype.card α := by
    let S₁ : Set (ℝ × (α → ℝ)) := {p | ∀ i : α, p.2 i ≤ (t - √ρ * p.1) / s}
    have hS₁m : MeasurableSet S₁ := by
      have : S₁ = ⋂ i : α, {p : ℝ × (α → ℝ) | p.2 i ≤ (t - √ρ * p.1) / s} := by ext p; simp [S₁]
      rw [this]
      exact MeasurableSet.iInter fun i => measurableSet_le
        ((measurable_pi_apply i).comp measurable_snd)
        (((measurable_const.sub (measurable_const.mul measurable_fst)).div_const s))
    have hpre : {ω : Unit ⊕ α → ℝ | ∀ i : α, ⟪equicorrVec ρ i, WithLp.toLp 2 ω⟫ ≤ t} =
        proj ⁻¹' S₁ := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, hproj, S₁, Function.comp_apply, hinner,
        le_div_iff₀ hs]
      exact forall_congr' fun i =>
        ⟨fun h => by linarith [mul_comm s (ω (.inr i))],
          fun h => by linarith [mul_comm s (ω (.inr i))]⟩
    rw [hpre]
    refine horth S₁ hS₁m (fun z => Φ ((t - √ρ * z) / s)) (fun z => cdf_nonneg _ _)
      ((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)) fun z => ?_
    have heq : Prod.mk z ⁻¹' S₁ = Set.pi Set.univ fun _ : α => Iic ((t - √ρ * z) / s) := by
      ext w; simp [S₁, Pi.le_def]
    rw [heq, Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, ← ofReal_cdf,
      ENNReal.ofReal_pow (cdf_nonneg _ _)]
  have hupper :
      (Measure.pi fun _ : Unit ⊕ α => gaussianReal 0 1).real
        {ω | ∀ i : α, t ≤ ⟪equicorrVec ρ i, WithLp.toLp 2 ω⟫} =
      ∫ z, φ z * (1 - Φ ((t - √ρ * z) / s)) ^ Fintype.card α := by
    let S₂ : Set (ℝ × (α → ℝ)) := {p | ∀ i : α, (t - √ρ * p.1) / s ≤ p.2 i}
    have hS₂m : MeasurableSet S₂ := by
      have : S₂ = ⋂ i : α, {p : ℝ × (α → ℝ) | (t - √ρ * p.1) / s ≤ p.2 i} := by ext p; simp [S₂]
      rw [this]
      exact MeasurableSet.iInter fun i => measurableSet_le
        (((measurable_const.sub (measurable_const.mul measurable_fst)).div_const s))
        ((measurable_pi_apply i).comp measurable_snd)
    have hpre : {ω : Unit ⊕ α → ℝ | ∀ i : α, t ≤ ⟪equicorrVec ρ i, WithLp.toLp 2 ω⟫} =
        proj ⁻¹' S₂ := by
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, hproj, S₂, Function.comp_apply, hinner,
        div_le_iff₀ hs]
      exact forall_congr' fun i =>
        ⟨fun h => by linarith [mul_comm s (ω (.inr i))],
          fun h => by linarith [mul_comm s (ω (.inr i))]⟩
    rw [hpre]
    refine horth S₂ hS₂m (fun z => 1 - Φ ((t - √ρ * z) / s))
      (fun z => sub_nonneg.mpr (cdf_le_one _ _))
      (continuous_const.sub ((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)))
      fun z => ?_
    have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
    have heq : Prod.mk z ⁻¹' S₂ = Set.pi Set.univ fun _ : α => Ici ((t - √ρ * z) / s) := by
      ext w; simp [S₂, Pi.le_def]
    have h1d (a : ℝ) : gaussianReal 0 1 (Ici a) = ENNReal.ofReal (1 - Φ a) := by
      have hreal : (gaussianReal 0 1).real (Ici a) = 1 - Φ a := by
        rw [← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio,
          measureReal_congr Iio_ae_eq_Iic, cdf_eq_real]
      rw [← ofReal_measureReal (s := Ici a), hreal]
    rw [heq, Measure.pi_pi]
    simp only [Finset.prod_const, Finset.card_univ, h1d,
      ENNReal.ofReal_pow (sub_nonneg.mpr (cdf_le_one _ _))]
  rw [hlower, hupper, equicorrNonStraddle, ← integral_add]
  · refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [s, mul_add]
  · refine (integrable_gaussianPDFReal 0 1).mul_bdd
      (((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)).pow _).aestronglyMeasurable
      (c := 1) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (cdf_nonneg _ _) _)]
    exact pow_le_one₀ (cdf_nonneg _ _) (cdf_le_one _ _)
  · refine (integrable_gaussianPDFReal 0 1).mul_bdd
      ((continuous_const.sub ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
        (by fun_prop))).pow _).aestronglyMeasurable
      (c := 1) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) _)]
    exact pow_le_one₀ (sub_nonneg.mpr (cdf_le_one _ _)) (sub_le_self _ (cdf_nonneg _ _))

/-- Threshold `t = 0` minimizes `equicorrNonStraddle k ρ t` over all `t : ℝ` for `k ≥ 1` and
`0 ≤ ρ < 1`. -/
private theorem equicorrNonStraddle_zero_le {k : ℕ} (hk : 1 ≤ k) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ < 1) (t : ℝ) :
    equicorrNonStraddle k ρ 0 ≤ equicorrNonStraddle k ρ t := by
  rcases eq_or_lt_of_le hρ0 with rfl | hρ_pos
  · have h0 (u : ℝ) : equicorrNonStraddle k 0 u = Φ u ^ k + (1 - Φ u) ^ k := by
      simp only [equicorrNonStraddle, sqrt_zero, zero_mul, sub_zero, sqrt_one, div_one,
        integral_mul_const, integral_gaussianPDFReal_eq_one 0 one_ne_zero, one_mul]
    rw [h0 0, h0 t, cdf_gaussianReal_zero_zero one_ne_zero]
    have hconv : ConvexOn ℝ (Ici (0 : ℝ)) (fun x : ℝ => x ^ k) := convexOn_pow k
    have hconv2 := hconv.2
    have hmid := hconv2 (mem_Ici.mpr (cdf_nonneg (gaussianReal 0 1) t))
      (mem_Ici.mpr (sub_nonneg.mpr (cdf_le_one (gaussianReal 0 1) t)))
      (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2⁻¹ : ℝ) + 2⁻¹ = 1)
    simp only [smul_eq_mul] at hmid
    have hhalf : 2⁻¹ * Φ t + 2⁻¹ * (1 - Φ t) = (2⁻¹ : ℝ) := by ring
    have h12 : (1 : ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
    rw [hhalf] at hmid
    rw [h12]
    linarith
  set c := √ρ
  set s := √(1 - ρ)
  have hc : 0 < c := sqrt_pos.mpr hρ_pos
  have hs : 0 < s := sqrt_pos.mpr (sub_pos.mpr hρ1)
  have heven (u : ℝ) : equicorrNonStraddle k ρ (-u) = equicorrNonStraddle k ρ u := by
    simp only [equicorrNonStraddle]
    rw [← integral_neg_eq_self (fun z => φ z *
      (Φ ((-u - √ρ * z) / √(1 - ρ)) ^ k + (1 - Φ ((-u - √ρ * z) / √(1 - ρ))) ^ k))]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    have hφneg : φ (-z) = φ z := by simp [gaussianPDFReal_def]
    have harg : (-u - √ρ * -z) / √(1 - ρ) = -((u - √ρ * z) / √(1 - ρ)) := by ring
    rw [hφneg, harg, cdf_gaussianReal_neg one_ne_zero]
    ring
  wlog ht : 0 ≤ t generalizing t
  · rw [← heven t]
    exact this (-t) (by linarith)
  let G : ℝ → ℝ := equicorrNonStraddle k ρ
  let g : ℝ → ℝ → ℝ := fun u z =>
    φ z * (Φ ((u - c * z) / s) ^ k + (1 - Φ ((u - c * z) / s)) ^ k)
  let g' : ℝ → ℝ → ℝ := fun u z =>
    φ z * ((k : ℝ) / s * φ ((u - c * z) / s) *
      (Φ ((u - c * z) / s) ^ (k - 1) - (1 - Φ ((u - c * z) / s)) ^ (k - 1)))
  have hg_meas (u : ℝ) : AEStronglyMeasurable (g u) volume := by
    refine Continuous.aestronglyMeasurable ?_
    exact (continuous_gaussianPDFReal 0 1).mul
      ((((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)).pow k).add
        ((continuous_const.sub ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
          (by fun_prop))).pow k))
  have hg_int (u : ℝ) : Integrable (g u) volume := by
    refine (integrable_gaussianPDFReal 0 1).mul_bdd
      (((((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)).pow k).add
        ((continuous_const.sub ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
          (by fun_prop))).pow k)).aestronglyMeasurable)
      (c := 2) (ae_of_all _ fun z => ?_)
    have h1 : 0 ≤ Φ ((u - c * z) / s) ^ k := pow_nonneg (cdf_nonneg _ _) _
    have h2 : 0 ≤ (1 - Φ ((u - c * z) / s)) ^ k :=
      pow_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) _
    rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg h1 h2)]
    have hp1 : Φ ((u - c * z) / s) ^ k ≤ 1 :=
      pow_le_one₀ (cdf_nonneg (gaussianReal 0 1) _) (cdf_le_one (gaussianReal 0 1) _)
    have hp2 : (1 - Φ ((u - c * z) / s)) ^ k ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr (cdf_le_one (gaussianReal 0 1) _))
        (sub_le_self 1 (cdf_nonneg (gaussianReal 0 1) _))
    linarith
  have hg'_meas (u : ℝ) : AEStronglyMeasurable (g' u) volume := by
    refine Continuous.aestronglyMeasurable ?_
    exact (continuous_gaussianPDFReal 0 1).mul
      ((continuous_const.mul ((continuous_gaussianPDFReal 0 1).comp (by fun_prop))).mul
        ((((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)).pow (k - 1)).sub
          ((continuous_const.sub ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
            (by fun_prop))).pow (k - 1))))
  have hg_deriv (z u : ℝ) : HasDerivAt (fun v => g v z) (g' u z) u := by
    have hlin : HasDerivAt (fun v : ℝ => (v - c * z) / s) (1 / s) u :=
      ((hasDerivAt_id' u).sub_const (c * z)).div_const s
    have hΦ : HasDerivAt (fun v => Φ ((v - c * z) / s))
        (φ ((u - c * z) / s) * (1 / s)) u :=
      (hasDerivAt_cdf_gaussianReal 0 one_ne_zero ((u - c * z) / s)).comp u hlin
    have h1 : HasDerivAt (fun v => Φ ((v - c * z) / s) ^ k)
        ((k : ℝ) * Φ ((u - c * z) / s) ^ (k - 1) * (φ ((u - c * z) / s) * (1 / s))) u :=
      hΦ.pow k
    have h2 : HasDerivAt (fun v => (1 - Φ ((v - c * z) / s)) ^ k)
        ((k : ℝ) * (1 - Φ ((u - c * z) / s)) ^ (k - 1) *
          (-(φ ((u - c * z) / s) * (1 / s)))) u :=
      (hΦ.const_sub (1 : ℝ)).pow k
    exact ((h1.add h2).const_mul (φ z)).congr_deriv (by simp only [g']; ring)
  let dom : ℝ → ℝ := fun z => (2 * (k : ℝ) / s) * φ z
  have hdom : Integrable dom volume := (integrable_gaussianPDFReal 0 1).const_mul _
  have hg'_le (z u : ℝ) : ‖g' u z‖ ≤ dom z := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (gaussianPDFReal_nonneg 0 1 z), abs_of_nonneg (by positivity : 0 ≤ (k : ℝ) / s)]
    have hsub : |Φ ((u - c * z) / s) ^ (k - 1) - (1 - Φ ((u - c * z) / s)) ^ (k - 1)| ≤ 2 := by
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (pow_nonneg (cdf_nonneg _ _) _),
        abs_of_nonneg (pow_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) _)]
      have hp1 : Φ ((u - c * z) / s) ^ (k - 1) ≤ 1 :=
        pow_le_one₀ (cdf_nonneg (gaussianReal 0 1) _) (cdf_le_one (gaussianReal 0 1) _)
      have hp2 : (1 - Φ ((u - c * z) / s)) ^ (k - 1) ≤ 1 :=
        pow_le_one₀ (sub_nonneg.mpr (cdf_le_one (gaussianReal 0 1) _))
          (sub_le_self 1 (cdf_nonneg (gaussianReal 0 1) _))
      linarith
    calc φ z * ((k : ℝ) / s * |φ ((u - c * z) / s)| *
          |Φ ((u - c * z) / s) ^ (k - 1) - (1 - Φ ((u - c * z) / s)) ^ (k - 1)|)
        ≤ φ z * ((k : ℝ) / s * 1 * 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (gaussianPDFReal_nonneg 0 1 z)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (abs_gaussianPDFReal_le_one _) (by positivity))
            hsub (abs_nonneg _) (by positivity)
      _ = dom z := by simp only [dom]; ring
  have hG_deriv (u : ℝ) : HasDerivAt G (∫ z, g' u z) u :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds u one_pos)
      (Eventually.of_forall hg_meas) (hg_int u) (hg'_meas u)
      (ae_of_all _ fun z v _ => hg'_le z v) hdom
      (ae_of_all _ fun z v _ => hg_deriv z v)).2
  have hG'_nonneg : ∀ u ∈ Ioo 0 t, 0 ≤ deriv G u := by
    intro u hu_mem
    rw [(hG_deriv u).deriv]
    have hc_abs : |c| < 1 := by
      rw [abs_of_pos hc]
      simpa using sqrt_lt_sqrt hρ0 hρ1
    have hs_eq : √(1 - c ^ 2) = s := by simp [c, s, sq_sqrt hρ0]
    let H : ℝ → ℝ := fun y =>
      φ y * (Φ (s * u - c * y) ^ (k - 1) - Φ (-s * u + c * y) ^ (k - 1))
    have hrew (z : ℝ) : g' u z = (k : ℝ) / s * φ u * H ((z - c * u) / s) := by
      have hsym := gaussianPDFReal_mul_gaussianPDFReal_comm hc_abs z u
      rw [hs_eq] at hsym
      have hc2 : c ^ 2 + s ^ 2 = 1 := by simp [c, s, sq_sqrt hρ0, sq_sqrt (sub_nonneg.mpr hρ1.le)]
      have harg1 : (u - c * z) / s = s * u - c * ((z - c * u) / s) := by
        calc (u - c * z) / s = (u * (c ^ 2 + s ^ 2) - c * z) / s := by rw [hc2, mul_one]
          _ = (s ^ 2 * u - c * (z - c * u)) / s := by ring
          _ = s * u - c * ((z - c * u) / s) := by field_simp [hs.ne']
      have harg2 : 1 - Φ ((u - c * z) / s) = Φ (-s * u + c * ((z - c * u) / s)) := by
        rw [harg1, ← cdf_gaussianReal_neg one_ne_zero]
        exact congrArg Φ (by ring)
      simp only [g', H, ← harg2, ← harg1]
      linear_combination ((k : ℝ) / s *
        (Φ ((u - c * z) / s) ^ (k - 1) - (1 - Φ ((u - c * z) / s)) ^ (k - 1))) * hsym
    have hH_int : Integrable H volume := by
      have hH_cont : Continuous fun y =>
          Φ (s * u - c * y) ^ (k - 1) - Φ (-s * u + c * y) ^ (k - 1) :=
        (((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)).pow (k - 1)).sub
          (((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)).pow (k - 1))
      refine (integrable_gaussianPDFReal 0 1).mul_bdd hH_cont.aestronglyMeasurable
        (c := 2) (ae_of_all _ fun y => ?_)
      rw [Real.norm_eq_abs]
      refine (abs_sub _ _).trans ?_
      rw [abs_of_nonneg (pow_nonneg (cdf_nonneg _ _) _),
        abs_of_nonneg (pow_nonneg (cdf_nonneg _ _) _)]
      have hp1 : Φ (s * u - c * y) ^ (k - 1) ≤ 1 :=
        pow_le_one₀ (cdf_nonneg (gaussianReal 0 1) _) (cdf_le_one (gaussianReal 0 1) _)
      have hp2 : Φ (-s * u + c * y) ^ (k - 1) ≤ 1 :=
        pow_le_one₀ (cdf_nonneg (gaussianReal 0 1) _) (cdf_le_one (gaussianReal 0 1) _)
      linarith
    have hchg : ∫ z, H ((z - c * u) / s) = s * ∫ y, H y := by
      have heq : (fun z => H ((z - c * u) / s)) = fun z => H (s⁻¹ * (z + -(c * u))) := by
        funext z; congr 1; ring
      rw [heq, integral_add_right_eq_self (fun z => H (s⁻¹ * z)) (-(c * u)),
        Measure.integral_comp_inv_mul_left H s, abs_of_pos hs, smul_eq_mul]
    have hsym_int : 2 * ∫ y, H y = ∫ y, (H y + H (-y)) := by
      rw [two_mul, integral_add hH_int (hH_int.comp_neg), integral_neg_eq_self H]
    have hsum_nonneg : 0 ≤ ∫ y, (H y + H (-y)) := by
      refine integral_nonneg fun y => ?_
      have hφneg : φ (-y) = φ y := by simp [gaussianPDFReal_def]
      have ha1 : s * u - c * -y = s * u + c * y := by ring
      have ha2 : -s * u + c * -y = -s * u - c * y := by ring
      have hpt : H y + H (-y) = φ y *
          ((Φ (s * u - c * y) ^ (k - 1) - Φ (-s * u - c * y) ^ (k - 1)) +
           (Φ (s * u + c * y) ^ (k - 1) - Φ (-s * u + c * y) ^ (k - 1))) := by
        simp only [H, hφneg, ha1, ha2]
        ring
      rw [hpt]
      have hsu : 0 ≤ s * u := mul_nonneg hs.le hu_mem.1.le
      have hm1 : Φ (-s * u - c * y) ^ (k - 1) ≤ Φ (s * u - c * y) ^ (k - 1) :=
        pow_le_pow_left₀ (cdf_nonneg _ _)
          ((strictMono_cdf_gaussianReal 0 one_ne_zero).monotone (by linarith)) (k - 1)
      have hm2 : Φ (-s * u + c * y) ^ (k - 1) ≤ Φ (s * u + c * y) ^ (k - 1) :=
        pow_le_pow_left₀ (cdf_nonneg _ _)
          ((strictMono_cdf_gaussianReal 0 one_ne_zero).monotone (by linarith)) (k - 1)
      exact mul_nonneg (gaussianPDFReal_nonneg 0 1 y) (by linarith)
    have hHint : 0 ≤ ∫ y, H y := by linarith [hsym_int, hsum_nonneg]
    rw [integral_congr_ae (ae_of_all _ hrew), integral_const_mul, hchg]
    have hφu := gaussianPDFReal_nonneg 0 1 u
    positivity
  rcases eq_or_lt_of_le ht with rfl | ht_pos
  · exact le_rfl
  · have hmono : MonotoneOn G (Icc 0 t) :=
      monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
        (fun u _ => (hG_deriv u).continuousAt.continuousWithinAt)
        (fun u _ => (hG_deriv u).differentiableAt.differentiableWithinAt)
        (fun u hu_mem => by rw [interior_Icc] at hu_mem; exact hG'_nonneg u hu_mem)
    exact hmono ⟨le_rfl, ht_pos.le⟩ ⟨ht_pos.le, le_rfl⟩ ht_pos.le

/-- **Slepian straddling bound across all thresholds.** Let `s` be a finite index set with
`2 ≤ s.card`, and let `u : κ → EuclideanSpace ℝ V` be unit vectors on `s` whose distinct pairwise
inner products are all at least `ρ ∈ [0, 1)`. Then for every threshold `t : ℝ`, the projections
`⟪u i, ω⟫` (`i ∈ s`) straddle `t` with probability at most `equicorrStraddle s.card ρ`. -/
theorem measureReal_straddlesOn_le_equicorr {V κ : Type*} [Fintype V] {s : Finset κ}
    (hs : 2 ≤ s.card) {u : κ → EuclideanSpace ℝ V} (hu : ∀ i ∈ s, ‖u i‖ = 1) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ρ ≤ ⟪u i, u j⟫) (t : ℝ) :
    (Measure.pi fun _ : V => gaussianReal 0 1).real
        {ω | (∃ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ < t) ∧
          (∃ i ∈ s, t ≤ ⟪u i, WithLp.toLp 2 ω⟫)} ≤
      equicorrStraddle s.card ρ := by
  classical
  have hs_ne : s.Nonempty := Finset.card_pos.mp (by omega)
  let uSub : s → EuclideanSpace ℝ V := fun i => u i.1
  let vSub : s → EuclideanSpace ℝ (Unit ⊕ s) := equicorrVec ρ
  have huSub (i : s) : ‖uSub i‖ = 1 := hu i.1 i.2
  have hvSub (i : s) : ‖vSub i‖ = 1 := norm_equicorrVec hρ0 hρ1.le i
  have hpSub (i j : s) (hij : i ≠ j) : ⟪vSub i, vSub j⟫ ≤ ⟪uSub i, uSub j⟫ := by
    rw [inner_equicorrVec_of_ne hρ0 hij]
    exact hpair i.1 i.2 j.1 j.2 (Subtype.coe_ne_coe.mpr hij)
  have hlow := le_measureReal_forall_inner_le_of_le_inner huSub hvSub hpSub (fun _ => t)
  have hhigh := le_measureReal_forall_le_inner_of_le_inner huSub hvSub hpSub (fun _ => t)
  have hrewrite_low :
      {ω : V → ℝ | ∀ i ∈ s, ⟪u i, WithLp.toLp 2 ω⟫ ≤ t} =
        {ω | ∀ i : s, ⟪uSub i, WithLp.toLp 2 ω⟫ ≤ t} := by
    ext ω; simp [uSub]
  have hrewrite_high :
      {ω : V → ℝ | ∀ i ∈ s, t ≤ ⟪u i, WithLp.toLp 2 ω⟫} =
        {ω | ∀ i : s, t ≤ ⟪uSub i, WithLp.toLp 2 ω⟫} := by
    ext ω; simp [uSub]
  rw [measureReal_straddlesOn_eq_one_sub hs_ne u hu t, hrewrite_low, hrewrite_high]
  have heq := equicorr_orthants_eq (α := s) hρ1 t
  rw [Fintype.card_coe] at heq
  have hzero := equicorrNonStraddle_zero_le (k := s.card) (by omega) hρ0 hρ1 t
  have hdef : equicorrStraddle s.card ρ = 1 - equicorrNonStraddle s.card ρ 0 := by
    simp [equicorrStraddle, show ¬ s.card ≤ 1 by omega]
  linarith

/-- Continuity of `equicorrStraddle k` at every correlation `ρ₀ ∈ (0, 1)`. -/
theorem continuousAt_equicorrStraddle (k : ℕ) {ρ₀ : ℝ} (hρ0 : 0 < ρ₀) (hρ1 : ρ₀ < 1) :
    ContinuousAt (equicorrStraddle k) ρ₀ := by
  by_cases hk : k ≤ 1
  · have hconst : equicorrStraddle k = fun _ => 0 := funext fun ρ => by simp [equicorrStraddle, hk]
    rw [hconst]
    exact continuousAt_const
  have hfun : equicorrStraddle k = fun ρ => 1 - equicorrNonStraddle k ρ 0 :=
    funext fun ρ => by simp [equicorrStraddle, hk]
  rw [hfun]
  refine continuousAt_const.sub ?_
  refine continuousAt_of_dominated (bound := fun z => 2 * φ z)
    (Eventually.of_forall fun ρ => ?_)
    (Eventually.of_forall fun ρ => ae_of_all _ fun z => ?_)
    ((integrable_gaussianPDFReal 0 1).const_mul 2)
    (ae_of_all _ fun z => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    exact (continuous_gaussianPDFReal 0 1).mul
      ((((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)).pow k).add
        ((continuous_const.sub ((continuous_cdf_gaussianReal 0 one_ne_zero).comp
          (by fun_prop))).pow k))
  · have h1 : 0 ≤ Φ ((0 - √ρ * z) / √(1 - ρ)) ^ k := pow_nonneg (cdf_nonneg _ _) _
    have h2 : 0 ≤ (1 - Φ ((0 - √ρ * z) / √(1 - ρ))) ^ k :=
      pow_nonneg (sub_nonneg.mpr (cdf_le_one _ _)) _
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 z),
      abs_of_nonneg (add_nonneg h1 h2)]
    have hp1 : Φ ((0 - √ρ * z) / √(1 - ρ)) ^ k ≤ 1 :=
      pow_le_one₀ (cdf_nonneg (gaussianReal 0 1) _) (cdf_le_one (gaussianReal 0 1) _)
    have hp2 : (1 - Φ ((0 - √ρ * z) / √(1 - ρ))) ^ k ≤ 1 :=
      pow_le_one₀ (sub_nonneg.mpr (cdf_le_one (gaussianReal 0 1) _))
        (sub_le_self 1 (cdf_nonneg (gaussianReal 0 1) _))
    have hb : Φ ((0 - √ρ * z) / √(1 - ρ)) ^ k + (1 - Φ ((0 - √ρ * z) / √(1 - ρ))) ^ k ≤ 2 := by
      linarith
    nlinarith [gaussianPDFReal_nonneg 0 1 z]
  · have hden : √(1 - ρ₀) ≠ 0 := (sqrt_pos.mpr (sub_pos.mpr hρ1)).ne'
    have harg : ContinuousAt (fun ρ => (0 - √ρ * z) / √(1 - ρ)) ρ₀ :=
      (continuousAt_const.sub (continuous_sqrt.continuousAt.mul continuousAt_const)).div
        (continuous_sqrt.continuousAt.comp (continuousAt_const.sub continuousAt_id)) hden
    have hΦ : ContinuousAt (fun ρ => Φ ((0 - √ρ * z) / √(1 - ρ))) ρ₀ :=
      (continuous_cdf_gaussianReal 0 one_ne_zero).continuousAt.comp harg
    exact continuousAt_const.mul ((hΦ.pow k).add ((continuousAt_const.sub hΦ).pow k))

end Equicorrelated

/-! ### Exact `k = 3` identity and rational Taylor–Gordon upper bounds -/

section Bounds

open Classical in
/-- Pure real identity for three nonzero numbers: `4` times the indicator that they straddle `0`
equals the number of ordered distinct pairs separated by `0`. -/
private theorem four_mul_straddlesOn_fin_three {x : Fin 3 → ℝ} (hx : ∀ i, x i ≠ 0) :
    (4 : ℝ) * (if (∃ i, x i < 0) ∧ (∃ i, 0 ≤ x i) then 1 else 0) =
      ∑ p ∈ (Finset.univ : Finset (Fin 3)).offDiag,
        if (0 : ℝ) ∈ Ι (x p.1) (x p.2) then 1 else 0 := by
  have hsum : ∑ p ∈ (Finset.univ : Finset (Fin 3)).offDiag,
      (if (0 : ℝ) ∈ Ι (x p.1) (x p.2) then (1 : ℝ) else 0) =
      (if (0 : ℝ) ∈ Ι (x 0) (x 1) then 1 else 0) +
      (if (0 : ℝ) ∈ Ι (x 0) (x 2) then 1 else 0) +
      (if (0 : ℝ) ∈ Ι (x 1) (x 0) then 1 else 0) +
      (if (0 : ℝ) ∈ Ι (x 1) (x 2) then 1 else 0) +
      (if (0 : ℝ) ∈ Ι (x 2) (x 0) then 1 else 0) +
      (if (0 : ℝ) ∈ Ι (x 2) (x 1) then 1 else 0) := by
    have hoff : (Finset.univ : Finset (Fin 3)).offDiag =
        {(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)} := by decide
    rw [hoff]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton]
    ring
  rw [hsum]
  have hstrad : ((∃ i, x i < 0) ∧ (∃ i, 0 ≤ x i)) ↔
      (x 0 < 0 ∨ x 1 < 0 ∨ x 2 < 0) ∧ (0 ≤ x 0 ∨ 0 ≤ x 1 ∨ 0 ≤ x 2) := by
    constructor
    · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
      exact ⟨by fin_cases i <;> simp_all, by fin_cases j <;> simp_all⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · rcases h1 with h | h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
      · rcases h2 with h | h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
        · exact ⟨2, h⟩
  have neg_neg {a b : ℝ} (ha : a < 0) (hb : b < 0) :
      (if (0 : ℝ) ∈ Ι a b then (1 : ℝ) else 0) = 0 := by
    have h : (0 : ℝ) ∉ Ι a b := by rw [mem_uIoc]; rintro (⟨_, h2⟩ | ⟨_, h2⟩) <;> linarith
    simp [h]
  have pos_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
      (if (0 : ℝ) ∈ Ι a b then (1 : ℝ) else 0) = 0 := by
    have h : (0 : ℝ) ∉ Ι a b := by rw [mem_uIoc]; rintro (⟨h1, _⟩ | ⟨h1, _⟩) <;> linarith
    simp [h]
  have neg_pos {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
      (if (0 : ℝ) ∈ Ι a b then (1 : ℝ) else 0) = 1 := by
    have h : (0 : ℝ) ∈ Ι a b := mem_uIoc.mpr (Or.inl ⟨ha, hb.le⟩)
    simp [h]
  have pos_neg {a b : ℝ} (ha : 0 < a) (hb : b < 0) :
      (if (0 : ℝ) ∈ Ι a b then (1 : ℝ) else 0) = 1 := by
    rw [uIoc_comm, neg_pos hb ha]
  have ite_true_s (h : (∃ i, x i < 0) ∧ (∃ i, 0 ≤ x i)) :
      (if (∃ i, x i < 0) ∧ (∃ i, 0 ≤ x i) then (1 : ℝ) else 0) = 1 := by simp [h]
  have ite_false_s (h : ¬ ((∃ i, x i < 0) ∧ (∃ i, 0 ≤ x i))) :
      (if (∃ i, x i < 0) ∧ (∃ i, 0 ≤ x i) then (1 : ℝ) else 0) = 0 := by simp [h]
  rcases lt_or_gt_of_ne (hx 0) with h0 | h0 <;>
    rcases lt_or_gt_of_ne (hx 1) with h1 | h1 <;>
    rcases lt_or_gt_of_ne (hx 2) with h2 | h2
  · rw [neg_neg h0 h1, neg_neg h0 h2, neg_neg h1 h0, neg_neg h1 h2, neg_neg h2 h0, neg_neg h2 h1,
      ite_false_s (fun h => by rcases (hstrad.mp h).2 with h' | h' | h' <;> linarith)]
    norm_num
  · rw [neg_pos h0 h2, pos_neg h2 h0, neg_pos h1 h2, pos_neg h2 h1, neg_neg h0 h1, neg_neg h1 h0,
      ite_true_s (hstrad.mpr ⟨Or.inl h0, Or.inr (Or.inr h2.le)⟩)]
    norm_num
  · rw [neg_pos h0 h1, pos_neg h1 h0, pos_neg h1 h2, neg_pos h2 h1, neg_neg h0 h2, neg_neg h2 h0,
      ite_true_s (hstrad.mpr ⟨Or.inl h0, Or.inr (Or.inl h1.le)⟩)]
    norm_num
  · rw [neg_pos h0 h1, pos_neg h1 h0, neg_pos h0 h2, pos_neg h2 h0, pos_pos h1 h2, pos_pos h2 h1,
      ite_true_s (hstrad.mpr ⟨Or.inl h0, Or.inr (Or.inl h1.le)⟩)]
    norm_num
  · rw [pos_neg h0 h1, neg_pos h1 h0, pos_neg h0 h2, neg_pos h2 h0, neg_neg h1 h2, neg_neg h2 h1,
      ite_true_s (hstrad.mpr ⟨Or.inr (Or.inl h1), Or.inl h0.le⟩)]
    norm_num
  · rw [pos_neg h0 h1, neg_pos h1 h0, neg_pos h1 h2, pos_neg h2 h1, pos_pos h0 h2, pos_pos h2 h0,
      ite_true_s (hstrad.mpr ⟨Or.inr (Or.inl h1), Or.inl h0.le⟩)]
    norm_num
  · rw [pos_pos h0 h1, pos_pos h1 h0, pos_neg h0 h2, neg_pos h2 h0, pos_neg h1 h2, neg_pos h2 h1,
      ite_true_s (hstrad.mpr ⟨Or.inr (Or.inr h2), Or.inl h0.le⟩)]
    norm_num
  · rw [pos_pos h0 h1, pos_pos h1 h0, pos_pos h0 h2, pos_pos h2 h0, pos_pos h1 h2, pos_pos h2 h1,
      ite_false_s (fun h => by rcases (hstrad.mp h).1 with h' | h' | h' <;> linarith)]
    norm_num

/-- Exact `k = 3` identity: `equicorrStraddle 3 ρ = (3 / (2π)) arccos ρ` for `ρ ∈ [0, 1)`. -/
theorem equicorrStraddle_three {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    equicorrStraddle 3 ρ = 3 / (2 * π) * arccos ρ := by
  set P := Measure.pi fun _ : Unit ⊕ Fin 3 => gaussianReal 0 1
  set s : Finset (Fin 3) := Finset.univ
  let v : Fin 3 → EuclideanSpace ℝ (Unit ⊕ Fin 3) := equicorrVec ρ
  have hv (i : Fin 3) : ‖v i‖ = 1 := norm_equicorrVec hρ0 hρ1.le i
  have hstrad : P.real {ω | (∃ i ∈ s, ⟪v i, WithLp.toLp 2 ω⟫ < 0) ∧
      (∃ i ∈ s, 0 ≤ ⟪v i, WithLp.toLp 2 ω⟫)} =
      equicorrStraddle 3 ρ := by
    have hcomp := measureReal_straddlesOn_eq_one_sub (Finset.univ_nonempty (α := Fin 3))
      v (fun i _ => hv i) 0
    have heq := equicorr_orthants_eq (α := Fin 3) hρ1 0
    rw [Fintype.card_fin] at heq
    have hdef : equicorrStraddle 3 ρ = 1 - equicorrNonStraddle 3 ρ 0 := by
      simp [equicorrStraddle]
    simp only [s, Finset.mem_univ, true_and, forall_true_left] at hcomp ⊢
    linarith
  set A := {ω : Unit ⊕ Fin 3 → ℝ | (∃ i ∈ s, ⟪v i, WithLp.toLp 2 ω⟫ < 0) ∧
    (∃ i ∈ s, 0 ≤ ⟪v i, WithLp.toLp 2 ω⟫)}
  let B : Fin 3 × Fin 3 → Set (Unit ⊕ Fin 3 → ℝ) := fun p =>
    {ω | (0 : ℝ) ∈ Ι ⟪v p.1, WithLp.toLp 2 ω⟫ ⟪v p.2, WithLp.toLp 2 ω⟫}
  have hAm : MeasurableSet A := by
    have : A = (⋃ i ∈ s, {ω | ⟪v i, WithLp.toLp 2 ω⟫ < 0}) ∩
        (⋃ i ∈ s, {ω | 0 ≤ ⟪v i, WithLp.toLp 2 ω⟫}) := by
      ext ω; simp [A]
    rw [this]
    exact (s.measurableSet_biUnion fun i _ => measurableSet_lt (by fun_prop) measurable_const).inter
      (s.measurableSet_biUnion fun i _ => measurableSet_le measurable_const (by fun_prop))
  have hBm (p : Fin 3 × Fin 3) : MeasurableSet (B p) :=
    measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) 0
  have hae : ∀ᵐ ω ∂P, ∀ i : Fin 3, ⟪v i, WithLp.toLp 2 ω⟫ ≠ 0 :=
    eventually_all.mpr fun i => ae_inner_ne (fun h0 => by have := hv i; simp [h0] at this) 0
  have hpt : ∀ᵐ ω ∂P, 4 * A.indicator (1 : (Unit ⊕ Fin 3 → ℝ) → ℝ) ω =
      ∑ p ∈ s.offDiag, (B p).indicator (fun _ => (1 : ℝ)) ω := by
    classical
    refine hae.mono fun ω hne => ?_
    simpa only [indicator_apply, Pi.one_apply, A, B, s, Finset.mem_univ, true_and,
      mem_ofPred_eq] using
      four_mul_straddlesOn_fin_three (x := fun i => ⟪v i, WithLp.toLp 2 ω⟫) hne
  have hint_eq : 4 * P.real A = ∑ p ∈ s.offDiag, P.real (B p) := by
    rw [← integral_indicator_one hAm, ← integral_const_mul,
      integral_congr_ae hpt,
      integral_finsetSum s.offDiag (f := fun p ω => (B p).indicator (fun _ => (1 : ℝ)) ω)
        fun p _ => (integrable_const (1 : ℝ)).indicator (hBm p)]
    exact Finset.sum_congr rfl fun p _ => integral_indicator_one (hBm p)
  have hpair_eq (p : Fin 3 × Fin 3) (hp : p ∈ s.offDiag) : P.real (B p) = arccos ρ / π := by
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    have h1 := measureReal_pi_gaussianReal_eq
      (s := {x : EuclideanSpace ℝ (Unit ⊕ Fin 3) | (0 : ℝ) ∈ Ι ⟪v p.1, x⟫ ⟪v p.2, x⟫})
      (measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) 0)
    exact h1.trans ((measureReal_stdGaussian_zero_mem_uIoc_eq_arccos (hv p.1) (hv p.2)).trans
      (by rw [inner_equicorrVec_of_ne hρ0 hne]))
  have hsum : ∑ p ∈ s.offDiag, P.real (B p) = 6 * (arccos ρ / π) := by
    rw [Finset.sum_congr rfl hpair_eq, Finset.sum_const,
      show s.offDiag.card = 6 by decide, nsmul_eq_mul]
    norm_num
  have hrew : 6 * (arccos ρ / π) = 4 * (3 / (2 * π) * arccos ρ) := by ring
  rw [← hstrad]
  change P.real A = _
  linarith

private theorem integrable_gaussianPDFReal_mul_cdf_sub_half_pow (γ : ℝ) (d : ℕ) :
    Integrable (fun z => φ z * (Φ (γ * z) - 1 / 2) ^ d) volume := by
  refine (integrable_gaussianPDFReal 0 1).mul_bdd
    ((((continuous_cdf_gaussianReal 0 one_ne_zero).comp (by fun_prop)).sub
      continuous_const).pow d).aestronglyMeasurable
    (c := 1) (ae_of_all _ fun z => ?_)
  have habs : |Φ (γ * z) - 1 / 2| ≤ 1 := by
    rw [abs_le]
    have h0 := cdf_nonneg (gaussianReal 0 1) (γ * z)
    have h1 := cdf_le_one (gaussianReal 0 1) (γ * z)
    exact ⟨by linarith, by linarith⟩
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_one₀ (abs_nonneg _) habs

private theorem integral_gaussianPDFReal_mul_cdf_sub_half_pow_even (γ : ℝ) {d : ℕ}
    (hd : Even d) :
    ∫ z, φ z * (Φ (γ * z) - 1 / 2) ^ d =
      2 * ∫ z in Ioi (0 : ℝ), φ z * (Φ (γ * z) - 1 / 2) ^ d := by
  have hae_set : (Iic (0 : ℝ) : Set ℝ) =ᵐ[volume] Iio 0 := by
    rw [eventuallyEqSet_iff, ae_iff]
    have hsub : {x : ℝ | ¬(x ∈ Iic (0 : ℝ) ↔ x ∈ Iio (0 : ℝ))} ⊆ {(0 : ℝ)} := by
      intro x hx
      simp only [mem_ofPred_eq, mem_Iic, mem_Iio, mem_singleton_iff] at hx ⊢
      exact le_antisymm (by by_contra h; exact hx (iff_of_false h (by linarith)))
        (by by_contra h; have hgt := lt_of_not_ge h; exact hx (iff_of_true hgt.le hgt))
    exact measure_mono_null hsub Real.volume_singleton
  have hψ_int := integrable_gaussianPDFReal_mul_cdf_sub_half_pow γ d
  rw [← integral_add_compl measurableSet_Ioi hψ_int, compl_Ioi,
    setIntegral_congr_set hae_set]
  have hind : ∫ z, (Iio (0 : ℝ)).indicator (fun z => φ z * (Φ (γ * z) - 1 / 2) ^ d) z =
      ∫ z, (Ioi (0 : ℝ)).indicator (fun z => φ z * (Φ (γ * z) - 1 / 2) ^ d) z := by
    rw [← integral_neg_eq_self
      (fun z => (Ioi (0 : ℝ)).indicator (fun z => φ z * (Φ (γ * z) - 1 / 2) ^ d) z)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rcases lt_trichotomy z 0 with hz | rfl | hz
    · rw [indicator_of_mem (mem_Iio.mpr hz), indicator_of_mem (mem_Ioi.mpr (neg_pos.mpr hz))]
      have hφ : φ (-z) = φ z := by simp [gaussianPDFReal_def]
      have hψ : Φ (γ * -z) - 1 / 2 = -(Φ (γ * z) - 1 / 2) := by
        rw [mul_neg, cdf_gaussianReal_neg one_ne_zero]; ring
      rw [hφ, hψ, Even.neg_pow hd]
    · rw [indicator_of_notMem (by simp), neg_zero, indicator_of_notMem (by simp)]
    · rw [indicator_of_notMem (not_lt.mpr hz.le),
        indicator_of_notMem (not_lt.mpr (neg_nonpos.mpr hz.le))]
  rw [integral_indicator measurableSet_Iio, integral_indicator measurableSet_Ioi] at hind
  linarith

/-- Closed-form quadratic moment of the centered Gaussian cdf from `equicorrStraddle_three`:
`2 * ∫_{z > 0} φ(z) (Φ(γ z) - 1/2) ^ 2 = 1/4 - arccos ρ / (2π)` where `γ = √ρ / √(1 - ρ)`. -/
private theorem two_mul_integral_Ioi_cdf_sub_half_sq {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    2 * ∫ z in Ioi (0 : ℝ), φ z * (Φ (√ρ / √(1 - ρ) * z) - 1 / 2) ^ 2 =
      1 / 4 - arccos ρ / (2 * π) := by
  set γ := √ρ / √(1 - ρ)
  have h3 := equicorrStraddle_three hρ0 hρ1
  simp only [equicorrStraddle, show ¬ (3 : ℕ) ≤ 1 by decide, ↓reduceIte,
    equicorrNonStraddle] at h3
  have hpt (z : ℝ) :
      φ z * (Φ ((0 - √ρ * z) / √(1 - ρ)) ^ 3 + (1 - Φ ((0 - √ρ * z) / √(1 - ρ))) ^ 3) =
        1 / 4 * φ z + 3 * (φ z * (Φ (γ * z) - 1 / 2) ^ 2) := by
    have harg : (0 - √ρ * z) / √(1 - ρ) = -(γ * z) := by simp only [γ]; ring
    rw [harg, cdf_gaussianReal_neg one_ne_zero]
    ring
  have hψ_int := integrable_gaussianPDFReal_mul_cdf_sub_half_pow γ 2
  have heven := integral_gaussianPDFReal_mul_cdf_sub_half_pow_even γ (d := 2) ⟨1, rfl⟩
  rw [integral_congr_ae (ae_of_all _ hpt),
    integral_add ((integrable_gaussianPDFReal 0 1).const_mul _) (hψ_int.const_mul 3),
    integral_const_mul, integral_const_mul, integral_gaussianPDFReal_eq_one 0 one_ne_zero,
    mul_one, heven] at h3
  have hrew : 3 / (2 * π) * arccos ρ = 3 * (arccos ρ / (2 * π)) := by ring
  linarith

/-- Alternating Taylor bounds for `exp (-u)` on `u ≥ 0`: even truncations overestimate `exp (-u)`
and odd truncations underestimate `exp (-u)`. -/
private theorem exp_neg_taylor_even_odd (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (Even n → exp (-u) ≤ ∑ j ∈ Finset.range (n + 1), (-u) ^ j / (j.factorial : ℝ)) ∧
    (Odd n → ∑ j ∈ Finset.range (n + 1), (-u) ^ j / (j.factorial : ℝ) ≤ exp (-u)) := by
  induction n generalizing u with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one]
    exact exp_le_one_iff.mpr (by linarith)
  | succ n ih =>
    let E : ℕ → ℝ → ℝ := fun m x => exp (-x) - ∑ j ∈ Finset.range (m + 1), (-x) ^ j / j.factorial
    have hE0 (m : ℕ) : E m 0 = 0 := by
      simp [E, Finset.sum_range_succ']
    have hE_deriv (x : ℝ) : HasDerivAt (E (n + 1)) (-E n x) x := by
      have hexp : HasDerivAt (fun y => exp (-y)) (-exp (-x)) x := by
        simpa using (hasDerivAt_neg x).exp
      have hsum : HasDerivAt (fun y => ∑ j ∈ Finset.range (n + 2), (-y) ^ j / (j.factorial : ℝ))
          (-∑ j ∈ Finset.range (n + 1), (-x) ^ j / (j.factorial : ℝ)) x := by
        have h1 : ∀ y : ℝ, ∑ j ∈ Finset.range (n + 2), (-y) ^ j / (j.factorial : ℝ) =
            1 + ∑ j ∈ Finset.range (n + 1), (-y) ^ (j + 1) / ((j + 1).factorial : ℝ) :=
          fun y => by simp only [Finset.sum_range_succ', pow_zero, Nat.factorial_zero, Nat.cast_one,
            div_one, add_comm]
        simp_rw [h1]
        refine ((hasDerivAt_const x (1 : ℝ)).add
          (HasDerivAt.fun_sum
            (A := fun j y => (-y) ^ (j + 1) / ((j + 1).factorial : ℝ))
            (A' := fun j => -((-x) ^ j / (j.factorial : ℝ))) fun j _ => ?_)).congr_deriv ?_
        · refine (((hasDerivAt_neg x).pow (j + 1)).div_const ((j + 1).factorial : ℝ)).congr_deriv ?_
          rw [Nat.factorial_succ, Nat.cast_mul]
          have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          field_simp [hne]
        · rw [zero_add, ← Finset.sum_neg_distrib]
      exact (hexp.sub hsum).congr_deriv (by simp only [E]; ring)
    rcases Nat.even_or_odd n with hn | hn
    · refine ⟨fun h => absurd h (Nat.not_even_iff_odd.mpr (Even.add_one hn)), fun _ => ?_⟩
      have hmono : MonotoneOn (E (n + 1)) (Icc 0 u) :=
        monotoneOn_of_deriv_nonneg (convex_Icc 0 u)
          (fun x _ => (hE_deriv x).continuousAt.continuousWithinAt)
          (fun x _ => (hE_deriv x).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [interior_Icc] at hx
            rw [(hE_deriv x).deriv]
            have hle := (ih hx.1.le).1 hn
            simp only [E]
            linarith)
      have hge := hmono ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu
      rw [hE0 (n + 1)] at hge
      simp only [E] at hge
      linarith
    · refine ⟨fun _ => ?_, fun h => absurd h (Nat.not_odd_iff_even.mpr (Odd.add_one hn))⟩
      have hanti : AntitoneOn (E (n + 1)) (Icc 0 u) :=
        antitoneOn_of_deriv_nonpos (convex_Icc 0 u)
          (fun x _ => (hE_deriv x).continuousAt.continuousWithinAt)
          (fun x _ => (hE_deriv x).differentiableAt.differentiableWithinAt)
          (fun x hx => by
            rw [interior_Icc] at hx
            rw [(hE_deriv x).deriv]
            have hge := (ih hx.1.le).2 hn
            simp only [E]
            linarith)
      have hle := hanti ⟨le_rfl, hu⟩ ⟨hu, le_rfl⟩ hu
      rw [hE0 (n + 1)] at hle
      simp only [E] at hle
      linarith

/-- Odd Taylor lower bound for `exp (-u)` on `u ≥ 0`. -/
theorem sum_odd_taylor_le_exp_neg (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    ∑ j ∈ Finset.range (2 * m + 2), (-u) ^ j / (j.factorial : ℝ) ≤ exp (-u) :=
  (exp_neg_taylor_even_odd (2 * m + 1) hu).2 ⟨m, rfl⟩

/-- Gordon's rational Mill's-ratio lower bound for the standard Gaussian tail: for every `B : ℝ`,
`(B / (B² + 1)) φ(B) ≤ 1 - Φ(B)` (proved self-contained by monotonicity; cf.
[Vershynin2018, Proposition 2.1.2], which records the weaker `(1 / B - 1 / B³) φ(B)` lower bound
for `B > 1`). -/
theorem div_sq_add_one_mul_gaussianPDFReal_le (B : ℝ) :
    B / (B ^ 2 + 1) * φ B ≤ 1 - Φ B := by
  let g : ℝ → ℝ := fun x => (1 - Φ x) - x / (x ^ 2 + 1) * φ x
  have hg_deriv (x : ℝ) :
      HasDerivAt g (-(2 / (x ^ 2 + 1) ^ 2 * φ x)) x := by
    have hd1 : HasDerivAt (fun y => 1 - Φ y) (-φ x) x :=
      (hasDerivAt_cdf_gaussianReal 0 one_ne_zero x).const_sub (1 : ℝ)
    have hden : x ^ 2 + 1 ≠ 0 := by positivity
    have hd_sq : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x :=
      ((hasDerivAt_pow 2 x).add_const 1).congr_deriv (by ring)
    have hd_rat : HasDerivAt (fun y : ℝ => y / (y ^ 2 + 1))
        ((1 * (x ^ 2 + 1) - x * (2 * x)) / (x ^ 2 + 1) ^ 2) x :=
      (hasDerivAt_id' x).div hd_sq hden
    have hd_φ : HasDerivAt φ (-x * φ x) x := by
      simpa [sub_zero, NNReal.coe_one, div_one] using hasDerivAt_gaussianPDFReal 0 1 x
    refine (hd1.sub (hd_rat.mul hd_φ)).congr_deriv ?_
    field_simp [hden]
    ring
  have hanti : AntitoneOn g (Ici B) :=
    antitoneOn_of_deriv_nonpos (convex_Ici B)
      (fun x _ => (hg_deriv x).continuousAt.continuousWithinAt)
      (fun x _ => (hg_deriv x).differentiableAt.differentiableWithinAt)
      (fun x _ => by
        rw [(hg_deriv x).deriv, neg_nonpos]
        exact mul_nonneg (by positivity) (gaussianPDFReal_nonneg 0 1 x))
  have hlim : Tendsto g atTop (nhds 0) := by
    have h1 : Tendsto (fun x => 1 - Φ x) atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_cdf_atTop (gaussianReal 0 1))
    have h2 : Tendsto (fun x => x / (x ^ 2 + 1) * φ x) atTop (nhds 0) := by
      refine squeeze_zero_norm' (a := fun x => φ x) ?_ ?_
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
        have hrat : x / (x ^ 2 + 1) ≤ 1 :=
          (div_le_one (by positivity)).mpr (by nlinarith [sq_nonneg (x - 1)])
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity),
          abs_of_nonneg (gaussianPDFReal_nonneg 0 1 x)]
        exact mul_le_of_le_one_left (gaussianPDFReal_nonneg 0 1 x) hrat
      · simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one]
        simpa using tendsto_const_nhds.mul
          (tendsto_exp_atBot.comp ((tendsto_neg_atTop_atBot.comp
            (tendsto_pow_atTop (by norm_num : 2 ≠ 0))).atBot_div_const two_pos))
    simpa [g] using h1.sub h2
  have hgB : 0 ≤ g B := le_of_tendsto hlim
    ((eventually_ge_atTop B).mono fun x hx => hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx)
  simp only [g] at hgB
  linarith

/-! ### Rational polynomial arithmetic for certifying `equicorrStraddle` -/

/-- Coefficientwise addition of `ℚ` polynomial lists. -/
@[expose] def qPolyAdd : List ℚ → List ℚ → List ℚ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: qPolyAdd p q

/-- Scalar multiplication of a `ℚ` polynomial list. -/
@[expose] def qPolyScale (c : ℚ) : List ℚ → List ℚ :=
  List.map (c * ·)

/-- Convolution product of `ℚ` polynomial lists. -/
@[expose] def qPolyMul : List ℚ → List ℚ → List ℚ
  | [], _ => []
  | c :: cs, q => qPolyAdd (qPolyScale c q) (0 :: qPolyMul cs q)

/-- Iterated power of a `ℚ` polynomial list. -/
@[expose] def qPolyPow (p : List ℚ) : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => qPolyMul p (qPolyPow p n)

/-- Evaluate a `ℚ` polynomial list at `u : ℚ`. -/
@[expose] def qEval (p : List ℚ) (u : ℚ) : ℚ :=
  match p with
  | [] => 0
  | c :: cs => c + u * qEval cs u

/-- Evaluate a `ℚ` polynomial list in `x ^ 2` over `ℝ`. -/
private def rEvalEven : List ℚ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => (c : ℝ) + x ^ 2 * rEvalEven cs x

/-- Exact rational value of `∫_0^B z ^ d * rEvalEven p z dz`. -/
@[expose] def qIntOdd : List ℚ → ℕ → ℚ → ℚ
  | [], _, _ => 0
  | c :: cs, d, B => c * B ^ (d + 1) / (d + 1) + qIntOdd cs (d + 2) B

/-- Odd Taylor polynomial of `exp (-u)` of degree `2 * m + 1` scaled at `u = a * x ^ 2`:
coefficient `j` is `(-a) ^ j / j!`. -/
@[expose] def qExpOddPoly (m : ℕ) (a : ℚ) : List ℚ :=
  (List.range (2 * m + 2)).map fun j : ℕ => (-a) ^ j / (j.factorial : ℚ)

/-- Inner polynomial `Q(x^2)` such that `x * rEvalEven (qInnerPoly m γ) x` underestimates
`∫_0^{γ x} exp(-t^2/2) dt`: coefficient `j` is `γ * (-γ^2 / 2)^j / (j! * (2j + 1))`. -/
@[expose] def qInnerPoly (m : ℕ) (γ : ℚ) : List ℚ :=
  (List.range (2 * m + 2)).map fun j : ℕ =>
    γ * (-(γ ^ 2 / 2)) ^ j / ((j.factorial : ℚ) * (2 * j + 1))

private theorem rEvalEven_qEval (p : List ℚ) (x : ℚ) :
    rEvalEven p (x : ℝ) = (qEval p (x ^ 2) : ℝ) := by
  induction p with
  | nil => simp [rEvalEven, qEval]
  | cons c cs ih =>
    simp only [rEvalEven, qEval, Rat.cast_add, Rat.cast_mul, Rat.cast_pow, ih]

private theorem rEvalEven_add (p q : List ℚ) (x : ℝ) :
    rEvalEven (qPolyAdd p q) x = rEvalEven p x + rEvalEven q x := by
  induction p generalizing q with
  | nil => simp [qPolyAdd, rEvalEven]
  | cons a p ih =>
    cases q with
    | nil => simp [qPolyAdd, rEvalEven]
    | cons b q =>
      simp only [qPolyAdd, rEvalEven, Rat.cast_add, ih]
      ring

private theorem rEvalEven_scale (c : ℚ) (p : List ℚ) (x : ℝ) :
    rEvalEven (qPolyScale c p) x = (c : ℝ) * rEvalEven p x := by
  induction p with
  | nil => simp [qPolyScale, rEvalEven]
  | cons a p ih =>
    have hcons : qPolyScale c (a :: p) = (c * a) :: qPolyScale c p := rfl
    rw [hcons]
    simp only [rEvalEven, Rat.cast_mul, ih]
    ring

private theorem rEvalEven_mul (p q : List ℚ) (x : ℝ) :
    rEvalEven (qPolyMul p q) x = rEvalEven p x * rEvalEven q x := by
  induction p with
  | nil => simp [qPolyMul, rEvalEven]
  | cons c cs ih =>
    simp only [qPolyMul, rEvalEven_add, rEvalEven_scale, rEvalEven, Rat.cast_zero, zero_add, ih]
    ring

private theorem rEvalEven_pow (p : List ℚ) (n : ℕ) (x : ℝ) :
    rEvalEven (qPolyPow p n) x = rEvalEven p x ^ n := by
  induction n with
  | zero => simp [qPolyPow, rEvalEven]
  | succ n ih => simp [qPolyPow, rEvalEven_mul, ih, pow_succ']

private theorem continuous_rEvalEven (p : List ℚ) : Continuous (rEvalEven p) := by
  induction p with
  | nil => exact continuous_const
  | cons c cs ih => exact continuous_const.add ((continuous_pow 2).mul ih)

private theorem intervalIntegral_pow_mul_rEvalEven (p : List ℚ) (d : ℕ) (B : ℚ) :
    ∫ z in (0 : ℝ)..(B : ℝ), z ^ d * rEvalEven p z = (qIntOdd p d B : ℝ) := by
  induction p generalizing d with
  | nil => simp [rEvalEven, qIntOdd]
  | cons c cs ih =>
    have hpt (z : ℝ) : z ^ d * rEvalEven (c :: cs) z =
        (c : ℝ) * z ^ d + z ^ (d + 2) * rEvalEven cs z := by
      simp only [rEvalEven]
      ring
    simp_rw [hpt]
    have hi1 : IntervalIntegrable (fun z : ℝ => (c : ℝ) * z ^ d) volume 0 (B : ℝ) :=
      ((continuous_pow d).const_mul _).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun z : ℝ => z ^ (d + 2) * rEvalEven cs z) volume 0 (B : ℝ) :=
      ((continuous_pow (d + 2)).mul (continuous_rEvalEven cs)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2,
      intervalIntegral.integral_const_mul, integral_pow, ih (d + 2)]
    simp only [qIntOdd, zero_pow (Nat.succ_ne_zero d), sub_zero, Rat.cast_add, Rat.cast_div,
      Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
    ring

private theorem rEvalEven_list_map_range (n : ℕ) (f : ℕ → ℚ) (x : ℝ) :
    rEvalEven ((List.range n).map f) x = ∑ j ∈ Finset.range n, (f j : ℝ) * x ^ (2 * j) := by
  induction n generalizing f with
  | zero => simp [rEvalEven]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, rEvalEven,
      ih (f ∘ Nat.succ), Finset.sum_range_succ']
    simp only [Function.comp_apply, mul_zero, pow_zero, mul_one]
    rw [add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 * (j + 1) = 2 + 2 * j by ring, pow_add]
    ring

private theorem rEvalEven_qExpOddPoly_le_exp (m : ℕ) {a : ℚ} (ha : 0 ≤ a) (x : ℝ) :
    rEvalEven (qExpOddPoly m a) x ≤ exp (-(a : ℝ) * x ^ 2) := by
  rw [qExpOddPoly, rEvalEven_list_map_range]
  have hu : 0 ≤ (a : ℝ) * x ^ 2 := mul_nonneg (Rat.cast_nonneg.mpr ha) (sq_nonneg x)
  have h := sum_odd_taylor_le_exp_neg m hu
  have heq : ∑ j ∈ Finset.range (2 * m + 2), (-((a : ℝ) * x ^ 2)) ^ j / (j.factorial : ℝ) =
      ∑ j ∈ Finset.range (2 * m + 2), (((-a) ^ j / (j.factorial : ℚ) : ℚ) : ℝ) * x ^ (2 * j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [show -((a : ℝ) * x ^ 2) = (-(a : ℝ)) * x ^ 2 by ring, mul_pow, ← pow_mul]
    ring
  simpa only [neg_mul, heq] using h

private theorem antitoneOn_rEvalEven_qExpOddPoly (m : ℕ) {a : ℚ} (ha : 0 ≤ a) :
    AntitoneOn (rEvalEven (qExpOddPoly m a)) (Ici 0) := by
  let P := rEvalEven (qExpOddPoly m a)
  have hderiv (x : ℝ) : HasDerivAt P
      (-2 * (a : ℝ) * x * ∑ j ∈ Finset.range (2 * m + 1),
        (-((a : ℝ) * x ^ 2)) ^ j / (j.factorial : ℝ)) x := by
    have hfun : P = fun y => ∑ j ∈ Finset.range (2 * m + 2),
        (((-a) ^ j / (j.factorial : ℚ) : ℚ) : ℝ) * y ^ (2 * j) := by
      funext y; exact rEvalEven_list_map_range (2 * m + 2) _ y
    rw [hfun]
    have h1 : ∀ y : ℝ, ∑ j ∈ Finset.range (2 * m + 2),
        (((-a) ^ j / (j.factorial : ℚ) : ℚ) : ℝ) * y ^ (2 * j) =
        1 + ∑ j ∈ Finset.range (2 * m + 1),
          (((-a) ^ (j + 1) / ((j + 1).factorial : ℚ) : ℚ) : ℝ) * y ^ (2 * (j + 1)) :=
      fun y => by
        rw [Finset.sum_range_succ']
        simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, Rat.cast_one, mul_zero,
          one_mul, add_comm]
    simp_rw [h1]
    refine ((hasDerivAt_const x (1 : ℝ)).add
      (HasDerivAt.fun_sum
        (A := fun j y => (((-a) ^ (j + 1) / ((j + 1).factorial : ℚ) : ℚ) : ℝ) * y ^ (2 * (j + 1)))
        (A' := fun j => -2 * (a : ℝ) * x * ((-((a : ℝ) * x ^ 2)) ^ j / (j.factorial : ℝ)))
        fun j _ => ?_)).congr_deriv ?_
    · refine ((hasDerivAt_pow (2 * (j + 1)) x).const_mul _).congr_deriv ?_
      rw [Nat.factorial_succ]
      push_cast
      have hne : ((j : ℝ) + 1) ≠ 0 := by positivity
      have hexp : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
      rw [hexp, show 2 * j + 1 = 1 + 2 * j by omega, pow_add x 1 (2 * j), pow_one,
        pow_mul x 2 j, show -((a : ℝ) * x ^ 2) = (-(a : ℝ)) * x ^ 2 by ring, mul_pow]
      field_simp [hne]
      ring
    · rw [zero_add, Finset.mul_sum]
  exact antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt)
    (fun x _ => (hderiv x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Ici] at hx
      rw [(hderiv x).deriv]
      have hx0 : 0 ≤ x := hx.le
      have ha0 : 0 ≤ (a : ℝ) := Rat.cast_nonneg.mpr ha
      have heven :=
        (exp_neg_taylor_even_odd (2 * m) (mul_nonneg ha0 (sq_nonneg x))).1 ⟨m, two_mul m⟩
      have hsum_pos : 0 ≤ ∑ j ∈ Finset.range (2 * m + 1),
          (-((a : ℝ) * x ^ 2)) ^ j / (j.factorial : ℝ) :=
        (exp_pos _).le.trans heven
      have hprod_nn : 0 ≤ (a : ℝ) * x * ∑ j ∈ Finset.range (2 * m + 1),
          (-((a : ℝ) * x ^ 2)) ^ j / (j.factorial : ℝ) :=
        mul_nonneg (mul_nonneg ha0 hx0) hsum_pos
      linarith)

private theorem inner_poly_eq_intervalIntegral (m : ℕ) (γ : ℚ) (z : ℝ) :
    z * rEvalEven (qInnerPoly m γ) z =
      ∫ t in (0 : ℝ)..((γ : ℝ) * z),
        ∑ j ∈ Finset.range (2 * m + 2), (-(t ^ 2 / 2)) ^ j / (j.factorial : ℝ) := by
  have hint_j (j : ℕ) : IntervalIntegrable
      (fun t : ℝ => (-(t ^ 2 / 2)) ^ j / (j.factorial : ℝ)) volume 0 ((γ : ℝ) * z) :=
    (by fun_prop : Continuous fun t : ℝ =>
      (-(t ^ 2 / 2)) ^ j / (j.factorial : ℝ)).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum fun j _ => hint_j j,
    qInnerPoly, rEvalEven_list_map_range, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hrew : (fun t : ℝ => (-(t ^ 2 / 2)) ^ j / (j.factorial : ℝ)) =
      fun t => ((-((1 : ℝ) / 2)) ^ j / (j.factorial : ℝ)) * t ^ (2 * j) := by
    funext t
    rw [show -(t ^ 2 / 2) = -((1 : ℝ) / 2) * t ^ 2 by ring, mul_pow, ← pow_mul]
    ring
  rw [hrew, intervalIntegral.integral_const_mul, integral_pow,
    zero_pow (Nat.succ_ne_zero (2 * j)), sub_zero]
  push_cast
  have hne1 : (j.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
  have hne2 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  rw [show 2 * j + 1 = 1 + 2 * j by omega, pow_add ((γ : ℝ) * z) 1 (2 * j), pow_one, mul_pow,
    pow_mul ((γ : ℝ)) 2 j]
  field_simp [hne1, hne2]
  ring

private theorem inner_poly_le_sqrt_two_pi_mul_psi (m : ℕ) {γ : ℚ} (hγ : 0 ≤ γ) {z : ℝ}
    (hz : 0 ≤ z) :
    z * rEvalEven (qInnerPoly m γ) z ≤ √(2 * π) * (Φ ((γ : ℝ) * z) - 1 / 2) := by
  have hγR : 0 ≤ (γ : ℝ) := Rat.cast_nonneg.mpr hγ
  have hgz : 0 ≤ (γ : ℝ) * z := mul_nonneg hγR hz
  have hpsi : √(2 * π) * (Φ ((γ : ℝ) * z) - 1 / 2) =
      ∫ t in (0 : ℝ)..((γ : ℝ) * z), exp (-t ^ 2 / 2) := by
    have h12 : (1 : ℝ) / 2 = Φ 0 := by
      rw [cdf_gaussianReal_zero_zero one_ne_zero]; norm_num
    rw [h12, cdf_gaussianReal_eq_integral _ one_ne_zero,
      cdf_gaussianReal_eq_integral _ one_ne_zero]
    have hdiff : (∫ y in Iic ((γ : ℝ) * z), φ y) - ∫ y in Iic (0 : ℝ), φ y =
        ∫ y in Ioc (0 : ℝ) ((γ : ℝ) * z), φ y := by
      have hunion : Iic ((γ : ℝ) * z) = Iic 0 ∪ Ioc 0 ((γ : ℝ) * z) :=
        (Iic_union_Ioc_eq_Iic hgz).symm
      rw [hunion, setIntegral_union (Iic_disjoint_Ioc le_rfl) measurableSet_Ioc
        (integrable_gaussianPDFReal 0 1).integrableOn
        (integrable_gaussianPDFReal 0 1).integrableOn]
      ring
    have hs_ne : √(2 * π) ≠ 0 := (sqrt_pos.mpr (mul_pos two_pos pi_pos)).ne'
    rw [hdiff, ← intervalIntegral.integral_of_le hgz]
    simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one,
      intervalIntegral.integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hs_ne, one_mul]
  rw [hpsi, inner_poly_eq_intervalIntegral]
  refine intervalIntegral.integral_mono_on hgz ?_
    ((continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)
    (fun t _ => by
      simpa [neg_div] using sum_odd_taylor_le_exp_neg m (by positivity : 0 ≤ t ^ 2 / 2))
  exact (by fun_prop : Continuous fun t : ℝ =>
    ∑ j ∈ Finset.range (2 * m + 2), (-(t ^ 2 / 2)) ^ j / (j.factorial : ℝ)).intervalIntegrable _ _

private theorem nonneg_and_monotoneOn_inner {m : ℕ} {γ B : ℚ} (hγ : 0 ≤ γ) (hB : 0 ≤ B)
    (hpos : 0 ≤ qEval (qExpOddPoly m (γ ^ 2 / 2)) (B ^ 2)) :
    (∀ z ∈ Icc (0 : ℝ) B, 0 ≤ z * rEvalEven (qInnerPoly m γ) z) ∧
    ∀ z ∈ Icc (0 : ℝ) B, (B : ℝ) * rEvalEven (qInnerPoly m γ) B ≤
      √(2 * π) * (Φ ((γ : ℝ) * B) - 1 / 2) := by
  refine ⟨fun z hz => ?_,
    fun _ _ => inner_poly_le_sqrt_two_pi_mul_psi m hγ (Rat.cast_nonneg.mpr hB)⟩
  have hγR : 0 ≤ (γ : ℝ) := Rat.cast_nonneg.mpr hγ
  have hgz : 0 ≤ (γ : ℝ) * z := mul_nonneg hγR hz.1
  rw [inner_poly_eq_intervalIntegral]
  refine intervalIntegral.integral_nonneg hgz fun t ht => ?_
  have ht_le : t ≤ (γ : ℝ) * B := ht.2.trans (mul_le_mul_of_nonneg_left hz.2 hγR)
  have hanti := antitoneOn_rEvalEven_qExpOddPoly m (a := 1 / 2) (by norm_num)
    (mem_Ici.mpr ht.1) (mem_Ici.mpr (mul_nonneg hγR (Rat.cast_nonneg.mpr hB))) ht_le
  have hrew_t : rEvalEven (qExpOddPoly m (1 / 2)) t =
      ∑ j ∈ Finset.range (2 * m + 2), (-(t ^ 2 / 2)) ^ j / (j.factorial : ℝ) := by
    rw [qExpOddPoly, rEvalEven_list_map_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [show -(t ^ 2 / 2) = -((1 : ℝ) / 2) * t ^ 2 by ring, mul_pow, ← pow_mul]
    ring
  have hrew_B : rEvalEven (qExpOddPoly m (1 / 2)) ((γ : ℝ) * B) =
      (qEval (qExpOddPoly m (γ ^ 2 / 2)) (B ^ 2) : ℝ) := by
    rw [← rEvalEven_qEval (qExpOddPoly m (γ ^ 2 / 2)) B, qExpOddPoly, qExpOddPoly,
      rEvalEven_list_map_range, rEvalEven_list_map_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [mul_pow, pow_mul (γ : ℝ) 2 j, ← mul_assoc, ← mul_div_right_comm, ← mul_pow]
    congr 2
    ring
  rw [← hrew_t]
  exact (Rat.cast_nonneg.mpr hpos).trans (hrew_B ▸ hanti)

/-- Rational lower bound on the even centered-cdf moment
`2 * ∫_{z > 0} φ(z) (Φ(γ z) - 1/2) ^ d`. -/
@[expose] def qMomentLower (d m_in m_out S_out : ℕ) (γ_lo B s_hi : ℚ) : ℚ :=
  let p_out := qPolyPow (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) S_out
  let q_in := qInnerPoly m_in γ_lo
  let QB := B * qEval q_in (B ^ 2)
  let pB := qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2) ^ S_out
  2 * (qIntOdd (qPolyMul p_out (qPolyPow q_in d)) d B / s_hi ^ (d + 1) +
    (QB ^ d / s_hi ^ d) * ((B / (B ^ 2 + 1)) * (pB / s_hi)))

/-- Lower bound on `2 * ∫_{z > 0} φ(z) (Φ(γ_real * z) - 1/2) ^ d` via rational polynomial
integration on `[0, B]` plus Mill's / Gordon's tail bound on `[B, ∞)`. -/
private theorem le_two_mul_integral_Ioi_cdf_sub_half_pow {d m_in m_out S_out : ℕ}
    (hS : 1 ≤ S_out)
    {γ_lo B s_hi : ℚ} {γ_real : ℝ}
    (hγ0 : 0 ≤ γ_lo) (hγ : (γ_lo : ℝ) ≤ γ_real) (hB : 0 < B)
    (hs_hi : √(2 * π) ≤ (s_hi : ℝ))
    (hin_pos : 0 ≤ qEval (qExpOddPoly m_in (γ_lo ^ 2 / 2)) (B ^ 2))
    (hout_pos : 0 ≤ qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2)) :
    (qMomentLower d m_in m_out S_out γ_lo B s_hi : ℝ) ≤
      2 * ∫ z in Ioi (0 : ℝ), φ z * (Φ (γ_real * z) - 1 / 2) ^ d := by
  unfold qMomentLower
  dsimp only
  set p_out := qPolyPow (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) S_out
  set q_in := qInnerPoly m_in γ_lo
  set QB := B * qEval q_in (B ^ 2)
  set pB := qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2) ^ S_out
  have hBR : 0 < (B : ℝ) := Rat.cast_pos.mpr hB
  have hs_pos : 0 < √(2 * π) := sqrt_pos.mpr (mul_pos two_pos pi_pos)
  have hs_hi_pos : 0 < (s_hi : ℝ) := hs_pos.trans_le hs_hi
  let ψ : ℝ → ℝ := fun z => Φ (γ_real * z) - 1 / 2
  have h_int : Integrable (fun z => φ z * ψ z ^ d) volume :=
    integrable_gaussianPDFReal_mul_cdf_sub_half_pow γ_real d
  have hunion : Ioi (0 : ℝ) = Ioc 0 (B : ℝ) ∪ Ioi (B : ℝ) := (Ioc_union_Ioi_eq_Ioi hBR.le).symm
  rw [hunion, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    h_int.integrableOn h_int.integrableOn]
  have hmain : ((qIntOdd (qPolyMul p_out (qPolyPow q_in d)) d B / s_hi ^ (d + 1) : ℚ) : ℝ) ≤
      ∫ z in Ioc (0 : ℝ) (B : ℝ), φ z * ψ z ^ d := by
    rw [← intervalIntegral.integral_of_le hBR.le]
    have hpoly_int := intervalIntegral_pow_mul_rEvalEven (qPolyMul p_out (qPolyPow q_in d)) d B
    have hnn_in := (nonneg_and_monotoneOn_inner hγ0 hB.le hin_pos).1
    have hpt_main : ∀ z ∈ Icc (0 : ℝ) B,
        (z ^ d * rEvalEven (qPolyMul p_out (qPolyPow q_in d)) z) / (s_hi : ℝ) ^ (d + 1) ≤
          φ z * ψ z ^ d := by
      intro z hz
      have hbase_nn : 0 ≤ rEvalEven (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) z := by
        have hanti := antitoneOn_rEvalEven_qExpOddPoly m_out
          (a := 1 / (2 * (S_out : ℚ))) (by positivity)
          (mem_Ici.mpr hz.1) (mem_Ici.mpr hBR.le) hz.2
        rw [rEvalEven_qEval] at hanti
        exact (Rat.cast_nonneg.mpr hout_pos).trans hanti
      have hbase_le : rEvalEven (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) z ≤
          exp (-z ^ 2 / (2 * (S_out : ℝ))) := by
        have h := rEvalEven_qExpOddPoly_le_exp m_out
          (a := 1 / (2 * (S_out : ℚ))) (by positivity) z
        convert h using 2
        push_cast
        ring
      have hp_out_le : rEvalEven p_out z ≤ exp (-z ^ 2 / 2) := by
        rw [rEvalEven_pow]
        calc rEvalEven (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) z ^ S_out
            ≤ exp (-z ^ 2 / (2 * (S_out : ℝ))) ^ S_out := pow_le_pow_left₀ hbase_nn hbase_le S_out
          _ = exp (-z ^ 2 / 2) := by
              rw [← exp_nat_mul]
              congr 1
              have hSne : (S_out : ℝ) ≠ 0 := by positivity
              field_simp [hSne]
      have hp_out_nn : 0 ≤ rEvalEven p_out z := by
        rw [rEvalEven_pow]; exact pow_nonneg hbase_nn S_out
      have hq_le : z * rEvalEven q_in z ≤ √(2 * π) * ψ z := by
        refine (inner_poly_le_sqrt_two_pi_mul_psi m_in hγ0 hz.1).trans
          (mul_le_mul_of_nonneg_left ?_ hs_pos.le)
        exact sub_le_sub_right
          ((strictMono_cdf_gaussianReal 0 one_ne_zero).monotone
            (mul_le_mul_of_nonneg_right hγ hz.1)) _
      have hqd_le : z ^ d * rEvalEven (qPolyPow q_in d) z ≤ (√(2 * π) * ψ z) ^ d := by
        rw [rEvalEven_pow, ← mul_pow]
        exact pow_le_pow_left₀ (hnn_in z hz) hq_le d
      have hprod_nn : 0 ≤ z ^ d * rEvalEven (qPolyMul p_out (qPolyPow q_in d)) z := by
        rw [rEvalEven_mul, ← mul_assoc, mul_comm (z ^ d), mul_assoc, rEvalEven_pow q_in d z,
          ← mul_pow]
        exact mul_nonneg hp_out_nn (pow_nonneg (hnn_in z hz) d)
      calc (z ^ d * rEvalEven (qPolyMul p_out (qPolyPow q_in d)) z) / (s_hi : ℝ) ^ (d + 1)
          ≤ (z ^ d * rEvalEven (qPolyMul p_out (qPolyPow q_in d)) z) / √(2 * π) ^ (d + 1) :=
            div_le_div_of_nonneg_left hprod_nn (pow_pos hs_pos _)
              (pow_le_pow_left₀ hs_pos.le hs_hi (d + 1))
        _ = (rEvalEven p_out z * (z ^ d * rEvalEven (qPolyPow q_in d) z)) /
              (√(2 * π) * √(2 * π) ^ d) := by
            rw [rEvalEven_mul, pow_succ']; ring
        _ ≤ (exp (-z ^ 2 / 2) * (√(2 * π) * ψ z) ^ d) / (√(2 * π) * √(2 * π) ^ d) := by
            refine div_le_div_of_nonneg_right ?_ (by positivity)
            exact mul_le_mul hp_out_le hqd_le (by
              rw [rEvalEven_pow, ← mul_pow]; exact pow_nonneg (hnn_in z hz) d) (exp_pos _).le
        _ = φ z * ψ z ^ d := by
            rw [mul_pow, gaussianPDFReal_def]
            simp only [sub_zero, NNReal.coe_one, mul_one]
            have h1 : √(2 * π) ≠ 0 := hs_pos.ne'
            have h2 : √(2 * π) ^ d ≠ 0 := pow_ne_zero d h1
            field_simp [h1, h2]
    have hlhs_int : IntervalIntegrable
        (fun z : ℝ => (z ^ d * rEvalEven (qPolyMul p_out (qPolyPow q_in d)) z) /
          (s_hi : ℝ) ^ (d + 1))
        volume 0 (B : ℝ) := by
      have hc : Continuous fun z : ℝ =>
          (z ^ d * rEvalEven (qPolyMul p_out (qPolyPow q_in d)) z) / (s_hi : ℝ) ^ (d + 1) :=
        ((continuous_pow d).mul (continuous_rEvalEven _)).div_const _
      exact hc.intervalIntegrable _ _
    have hint_le := intervalIntegral.integral_mono_on hBR.le hlhs_int
      h_int.intervalIntegrable (fun z hz => hpt_main z hz)
    rw [intervalIntegral.integral_div, hpoly_int] at hint_le
    simpa only [Rat.cast_div, Rat.cast_pow] using hint_le
  have htail : (((QB ^ d / s_hi ^ d) * ((B / (B ^ 2 + 1)) * (pB / s_hi)) : ℚ) : ℝ) ≤
      ∫ z in Ioi (B : ℝ), φ z * ψ z ^ d := by
    have hQB_nn : 0 ≤ (QB : ℝ) := by
      have h1 := (nonneg_and_monotoneOn_inner hγ0 hB.le hin_pos).1 (B : ℝ) ⟨hBR.le, le_rfl⟩
      simpa only [QB, rEvalEven_qEval, Rat.cast_mul] using h1
    have hQB_le : (QB : ℝ) / (s_hi : ℝ) ≤ ψ (B : ℝ) := by
      have h1 := (nonneg_and_monotoneOn_inner hγ0 hB.le hin_pos).2 (B : ℝ) ⟨hBR.le, le_rfl⟩
      rw [rEvalEven_qEval] at h1
      calc (QB : ℝ) / (s_hi : ℝ) ≤ (QB : ℝ) / √(2 * π) :=
            div_le_div_of_nonneg_left hQB_nn hs_pos hs_hi
        _ ≤ Φ ((γ_lo : ℝ) * B) - 1 / 2 := by
            rw [div_le_iff₀ hs_pos]
            simpa only [QB, Rat.cast_mul, mul_comm] using h1
        _ ≤ ψ (B : ℝ) := sub_le_sub_right
            ((strictMono_cdf_gaussianReal 0 one_ne_zero).monotone
              (mul_le_mul_of_nonneg_right hγ hBR.le)) _
    have hpB_le : (pB : ℝ) / (s_hi : ℝ) ≤ φ (B : ℝ) := by
      have hbase_le : (qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2) : ℝ) ≤
          exp (-(B : ℝ) ^ 2 / (2 * (S_out : ℝ))) := by
        rw [← rEvalEven_qEval]
        convert rEvalEven_qExpOddPoly_le_exp m_out
          (a := 1 / (2 * (S_out : ℚ))) (by positivity) (B : ℝ) using 2
        push_cast; ring
      have hpB_exp : (pB : ℝ) ≤ exp (-(B : ℝ) ^ 2 / 2) := by
        simp only [pB, Rat.cast_pow]
        calc (qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2) : ℝ) ^ S_out
            ≤ exp (-(B : ℝ) ^ 2 / (2 * (S_out : ℝ))) ^ S_out :=
              pow_le_pow_left₀ (Rat.cast_nonneg.mpr hout_pos) hbase_le S_out
          _ = exp (-(B : ℝ) ^ 2 / 2) := by
              rw [← exp_nat_mul]
              congr 1
              have hSne : (S_out : ℝ) ≠ 0 := by positivity
              field_simp [hSne]
      have hpB_nn : 0 ≤ (pB : ℝ) := by
        simp only [pB, Rat.cast_pow]; exact pow_nonneg (Rat.cast_nonneg.mpr hout_pos) S_out
      calc (pB : ℝ) / (s_hi : ℝ) ≤ (pB : ℝ) / √(2 * π) :=
            div_le_div_of_nonneg_left hpB_nn hs_pos hs_hi
        _ ≤ exp (-(B : ℝ) ^ 2 / 2) / √(2 * π) :=
            div_le_div_of_nonneg_right hpB_exp hs_pos.le
        _ = φ (B : ℝ) := by
            simp only [gaussianPDFReal_def, sub_zero, NNReal.coe_one, mul_one, div_eq_inv_mul]
    have hgordon : ((B / (B ^ 2 + 1) * (pB / s_hi) : ℚ) : ℝ) ≤ ∫ z in Ioi (B : ℝ), φ z := by
      have htail_eq : ∫ z in Ioi (B : ℝ), φ z = 1 - Φ (B : ℝ) := by
        rw [← integral_gaussianPDFReal_eq_one 0 one_ne_zero,
          ← integral_add_compl measurableSet_Iic (integrable_gaussianPDFReal 0 1), compl_Iic,
          cdf_gaussianReal_eq_integral 0 one_ne_zero]
        ring
      rw [htail_eq]
      push_cast
      refine (mul_le_mul_of_nonneg_left hpB_le (by positivity)).trans
        (div_sq_add_one_mul_gaussianPDFReal_le (B : ℝ))
    have hpt_tail : ∀ z ∈ Ioi (B : ℝ),
        ((QB : ℝ) / (s_hi : ℝ)) ^ d * φ z ≤ φ z * ψ z ^ d := by
      intro z hz
      rw [mul_comm _ (φ z)]
      refine mul_le_mul_of_nonneg_left ?_ (gaussianPDFReal_nonneg 0 1 z)
      have hψ_z : ψ (B : ℝ) ≤ ψ z :=
        sub_le_sub_right ((strictMono_cdf_gaussianReal 0 one_ne_zero).monotone
          (mul_le_mul_of_nonneg_left (mem_Ioi.mp hz).le
            ((Rat.cast_nonneg.mpr hγ0).trans hγ))) _
      exact pow_le_pow_left₀ (by positivity) (hQB_le.trans hψ_z) d
    have hint_tail := setIntegral_mono_on
      (((integrable_gaussianPDFReal 0 1).const_mul _).integrableOn)
      h_int.integrableOn measurableSet_Ioi hpt_tail
    rw [integral_const_mul] at hint_tail
    refine le_trans ?_ hint_tail
    have h1 : (((QB ^ d / s_hi ^ d) * ((B / (B ^ 2 + 1)) * (pB / s_hi)) : ℚ) : ℝ) =
        ((QB : ℝ) / (s_hi : ℝ)) ^ d * (((B / (B ^ 2 + 1)) * (pB / s_hi) : ℚ) : ℝ) := by
      push_cast; rw [div_pow]
    rw [h1]
    exact mul_le_mul_of_nonneg_left hgordon (pow_nonneg (div_nonneg hQB_nn hs_hi_pos.le) d)
  push_cast at hmain htail ⊢
  linarith

/-- Rational upper-bound certificate for `equicorrStraddle k ρ` (`k ∈ {4, 5, 6, 7}`). -/
@[expose] def qEquicorrUpperCert (k m_in m_out S_out : ℕ) (arc_ub γ_lo B s_hi : ℚ) : ℚ :=
  let I2 := 1 / 4 - arc_ub / 2
  let I4 := qMomentLower 4 m_in m_out S_out γ_lo B s_hi
  let I6 := if 6 ≤ k then qMomentLower 6 m_in m_out S_out γ_lo B s_hi else 0
  1 - (1 / 2 ^ (k - 1) +
    2 * (k.choose 2 : ℚ) / 2 ^ (k - 2) * I2 +
    2 * (k.choose 4 : ℚ) / 2 ^ (k - 4) * I4 +
    (if 6 ≤ k then 2 * (k.choose 6 : ℚ) / 2 ^ (k - 6) * I6 else 0))

/-- **Master rational upper bound on `equicorrStraddle k ρ` for `k ∈ {4, 5, 6, 7}`.** -/
theorem equicorrStraddle_le_of_poly {k m_in m_out S_out : ℕ}
    (hk4 : 4 ≤ k) (hk7 : k ≤ 7) (hS : 1 ≤ S_out)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    {arc_ub γ_lo B s_hi : ℚ}
    (harc : arccos ρ / π ≤ (arc_ub : ℝ))
    (hγ0 : 0 ≤ γ_lo) (hγ : (γ_lo : ℝ) ^ 2 * (1 - ρ) ≤ ρ)
    (hB : 0 < B)
    (hs_hi0 : 0 ≤ s_hi) (hs_hi : 2 * π ≤ (s_hi : ℝ) ^ 2)
    (hin_pos : 0 ≤ qEval (qExpOddPoly m_in (γ_lo ^ 2 / 2)) (B ^ 2))
    (hout_pos : 0 ≤ qEval (qExpOddPoly m_out (1 / (2 * (S_out : ℚ)))) (B ^ 2)) :
    equicorrStraddle k ρ ≤ (qEquicorrUpperCert k m_in m_out S_out arc_ub γ_lo B s_hi : ℝ) := by
  have hγ_le : (γ_lo : ℝ) ≤ √ρ / √(1 - ρ) := by
    have hden : 0 < √(1 - ρ) := sqrt_pos.mpr (sub_pos.mpr hρ1)
    rw [le_div_iff₀ hden]
    have hnn : 0 ≤ (γ_lo : ℝ) * √(1 - ρ) :=
      mul_nonneg (Rat.cast_nonneg.mpr hγ0) hden.le
    rw [← sq_le_sq₀ hnn (sqrt_nonneg ρ), mul_pow, sq_sqrt (sub_nonneg.mpr hρ1.le),
      sq_sqrt hρ0.le]
    exact hγ
  have hs_le : √(2 * π) ≤ (s_hi : ℝ) := by
    rw [← sq_le_sq₀ (sqrt_nonneg _) (Rat.cast_nonneg.mpr hs_hi0),
      sq_sqrt (mul_nonneg zero_le_two pi_pos.le)]
    exact hs_hi
  set γ := √ρ / √(1 - ρ)
  let ψ : ℝ → ℝ := fun z => Φ (γ * z) - 1 / 2
  have hψ_int (d : ℕ) : Integrable (fun z => φ z * ψ z ^ d) volume :=
    integrable_gaussianPDFReal_mul_cdf_sub_half_pow γ d
  have hI2 : (1 / 4 - (arc_ub : ℝ) / 2) ≤ ∫ z, φ z * ψ z ^ 2 := by
    change (1 / 4 - (arc_ub : ℝ) / 2) ≤ ∫ z, φ z * (Φ (γ * z) - 1 / 2) ^ 2
    rw [integral_gaussianPDFReal_mul_cdf_sub_half_pow_even γ (d := 2) ⟨1, rfl⟩,
      two_mul_integral_Ioi_cdf_sub_half_sq hρ0.le hρ1]
    have : arccos ρ / (2 * π) = (arccos ρ / π) / 2 := by ring
    linarith
  have hI4 : (qMomentLower 4 m_in m_out S_out γ_lo B s_hi : ℝ) ≤ ∫ z, φ z * ψ z ^ 4 :=
    (le_two_mul_integral_Ioi_cdf_sub_half_pow (d := 4) hS
      hγ0 hγ_le hB hs_le hin_pos hout_pos).trans_eq
      (integral_gaussianPDFReal_mul_cdf_sub_half_pow_even γ (d := 4) ⟨2, rfl⟩).symm
  have hI6 : (qMomentLower 6 m_in m_out S_out γ_lo B s_hi : ℝ) ≤ ∫ z, φ z * ψ z ^ 6 :=
    (le_two_mul_integral_Ioi_cdf_sub_half_pow (d := 6) hS
      hγ0 hγ_le hB hs_le hin_pos hout_pos).trans_eq
      (integral_gaussianPDFReal_mul_cdf_sub_half_pow_even γ (d := 6) ⟨3, rfl⟩).symm
  have hlin4 (c0 c2 c4 c6 : ℝ) :
      ∫ z, (c0 * φ z + c2 * (φ z * ψ z ^ 2) + c4 * (φ z * ψ z ^ 4) + c6 * (φ z * ψ z ^ 6)) =
        c0 + c2 * (∫ z, φ z * ψ z ^ 2) + c4 * (∫ z, φ z * ψ z ^ 4) +
          c6 * (∫ z, φ z * ψ z ^ 6) := by
    have hi0 : Integrable (fun z => c0 * φ z) volume :=
      (integrable_gaussianPDFReal 0 1).const_mul c0
    have hi2 : Integrable (fun z => c2 * (φ z * ψ z ^ 2)) volume := (hψ_int 2).const_mul c2
    have hi4 : Integrable (fun z => c4 * (φ z * ψ z ^ 4)) volume := (hψ_int 4).const_mul c4
    have hi6 : Integrable (fun z => c6 * (φ z * ψ z ^ 6)) volume := (hψ_int 6).const_mul c6
    have hi02 : Integrable (fun z => c0 * φ z + c2 * (φ z * ψ z ^ 2)) volume := hi0.add hi2
    have hi024 :
        Integrable (fun z => c0 * φ z + c2 * (φ z * ψ z ^ 2) + c4 * (φ z * ψ z ^ 4)) volume :=
      hi02.add hi4
    rw [integral_add hi024 hi6, integral_add hi02 hi4, integral_add hi0 hi2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
      integral_gaussianPDFReal_eq_one 0 one_ne_zero, mul_one]
  have hdef : equicorrStraddle k ρ = 1 - equicorrNonStraddle k ρ 0 := by
    simp [equicorrStraddle, show ¬ k ≤ 1 by omega]
  rw [hdef]
  have harg (z : ℝ) :
      Φ ((0 - √ρ * z) / √(1 - ρ)) ^ k + (1 - Φ ((0 - √ρ * z) / √(1 - ρ))) ^ k =
        (1 / 2 - ψ z) ^ k + (1 / 2 + ψ z) ^ k := by
    have h1 : (0 - √ρ * z) / √(1 - ρ) = -(γ * z) := by simp only [γ]; ring
    rw [h1, cdf_gaussianReal_neg one_ne_zero]
    simp only [ψ]
    ring
  set j4 : ℝ := (qMomentLower 4 m_in m_out S_out γ_lo B s_hi : ℝ)
  set j6 : ℝ := (qMomentLower 6 m_in m_out S_out γ_lo B s_hi : ℝ)
  set m2 : ℝ := ∫ z, φ z * ψ z ^ 2
  set m4 : ℝ := ∫ z, φ z * ψ z ^ 4
  set m6 : ℝ := ∫ z, φ z * ψ z ^ 6
  interval_cases k
  · have hpt (z : ℝ) : φ z * ((1 / 2 - ψ z) ^ 4 + (1 / 2 + ψ z) ^ 4) =
        1 / 8 * φ z + 3 * (φ z * ψ z ^ 2) + 2 * (φ z * ψ z ^ 4) + 0 * (φ z * ψ z ^ 6) := by ring
    have heq : equicorrNonStraddle 4 ρ 0 = 1 / 8 + 3 * m2 + 2 * m4 + 0 * m6 := by
      simp only [equicorrNonStraddle, harg, m2, m4, m6]
      rw [integral_congr_ae (ae_of_all _ hpt), hlin4]
    have hcert : (qEquicorrUpperCert 4 m_in m_out S_out arc_ub γ_lo B s_hi : ℝ) =
        1 - (1 / 8 + 3 * (1 / 4 - (arc_ub : ℝ) / 2) + 2 * j4) := by
      simp only [qEquicorrUpperCert, show ¬ (6 ≤ 4) by decide, ↓reduceIte,
        show Nat.choose 4 2 = 6 by decide, show Nat.choose 4 4 = 1 by decide]
      push_cast [j4]
      ring
    rw [heq, hcert]
    linarith
  · have hpt (z : ℝ) : φ z * ((1 / 2 - ψ z) ^ 5 + (1 / 2 + ψ z) ^ 5) =
        1 / 16 * φ z + 5 / 2 * (φ z * ψ z ^ 2) + 5 * (φ z * ψ z ^ 4) + 0 * (φ z * ψ z ^ 6) := by
      ring
    have heq : equicorrNonStraddle 5 ρ 0 = 1 / 16 + 5 / 2 * m2 + 5 * m4 + 0 * m6 := by
      simp only [equicorrNonStraddle, harg, m2, m4, m6]
      rw [integral_congr_ae (ae_of_all _ hpt), hlin4]
    have hcert : (qEquicorrUpperCert 5 m_in m_out S_out arc_ub γ_lo B s_hi : ℝ) =
        1 - (1 / 16 + 5 / 2 * (1 / 4 - (arc_ub : ℝ) / 2) + 5 * j4) := by
      simp only [qEquicorrUpperCert, show ¬ (6 ≤ 5) by decide, ↓reduceIte,
        show Nat.choose 5 2 = 10 by decide, show Nat.choose 5 4 = 5 by decide]
      push_cast [j4]
      ring
    rw [heq, hcert]
    linarith
  · have hpt (z : ℝ) : φ z * ((1 / 2 - ψ z) ^ 6 + (1 / 2 + ψ z) ^ 6) =
        1 / 32 * φ z + 15 / 8 * (φ z * ψ z ^ 2) + 15 / 2 * (φ z * ψ z ^ 4) +
          2 * (φ z * ψ z ^ 6) := by ring
    have heq : equicorrNonStraddle 6 ρ 0 = 1 / 32 + 15 / 8 * m2 + 15 / 2 * m4 + 2 * m6 := by
      simp only [equicorrNonStraddle, harg, m2, m4, m6]
      rw [integral_congr_ae (ae_of_all _ hpt), hlin4]
    have hcert : (qEquicorrUpperCert 6 m_in m_out S_out arc_ub γ_lo B s_hi : ℝ) =
        1 - (1 / 32 + 15 / 8 * (1 / 4 - (arc_ub : ℝ) / 2) + 15 / 2 * j4 + 2 * j6) := by
      simp only [qEquicorrUpperCert, show (6 ≤ 6) by decide, ↓reduceIte,
        show Nat.choose 6 2 = 15 by decide, show Nat.choose 6 4 = 15 by decide,
        show Nat.choose 6 6 = 1 by decide]
      push_cast [j4, j6]
      ring
    rw [heq, hcert]
    linarith
  · have hpt (z : ℝ) : φ z * ((1 / 2 - ψ z) ^ 7 + (1 / 2 + ψ z) ^ 7) =
        1 / 64 * φ z + 21 / 16 * (φ z * ψ z ^ 2) + 35 / 4 * (φ z * ψ z ^ 4) +
          7 * (φ z * ψ z ^ 6) := by ring
    have heq : equicorrNonStraddle 7 ρ 0 = 1 / 64 + 21 / 16 * m2 + 35 / 4 * m4 + 7 * m6 := by
      simp only [equicorrNonStraddle, harg, m2, m4, m6]
      rw [integral_congr_ae (ae_of_all _ hpt), hlin4]
    have hcert : (qEquicorrUpperCert 7 m_in m_out S_out arc_ub γ_lo B s_hi : ℝ) =
        1 - (1 / 64 + 21 / 16 * (1 / 4 - (arc_ub : ℝ) / 2) + 35 / 4 * j4 + 7 * j6) := by
      simp only [qEquicorrUpperCert, show (6 ≤ 7) by decide, ↓reduceIte,
        show Nat.choose 7 2 = 21 by decide, show Nat.choose 7 4 = 35 by decide,
        show Nat.choose 7 6 = 7 by decide]
      push_cast [j4, j6]
      ring
    rw [heq, hcert]
    linarith

end Bounds

end ProbabilityTheory
