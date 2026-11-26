/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
-- `import all`: reads private `dot2`, `det2`, `neg2`, `rot120` from `PlanarGeometry`.
import all CslibFrontier.Computability.Circuit.Frontier.TensorRank.ThreeWayCut.PlanarGeometry
import CslibFrontier.Foundations.Probability.Gaussian.ConvexCap
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.OffMedian
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Measure-preserving maps and null sets on the planar Gaussian block sample

Internal `2`D Gaussian + `3`-way tie-breaker sample space (`BlockSample`, `gauss2`, `gaussTie`,
`blockMeasure`), orthogonal/cyclic measure-preserving symmetries (`measurePreserving_rotSample`,
`measurePreserving_negSample`), and collinearity / tie-equality null-set lemmas.
-/

-- This proof-only companion is intentionally private; sibling ThreeWayCut modules use import all.
set_option linter.privateModule false

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace

namespace Cslib.Circuits.Frontier.TensorRank

/-- Per-block sample: two Gaussian coordinates for `2`D edge scores plus three Gaussian
tie-breakers. -/
private abbrev BlockSample := (ℝ × ℝ) × (Fin 3 → ℝ)

private noncomputable def gauss2 : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

private noncomputable def gaussTie : Measure (Fin 3 → ℝ) :=
  Measure.pi fun _ : Fin 3 => gaussianReal 0 1

private noncomputable def blockMeasure : Measure BlockSample :=
  gauss2.prod gaussTie

private instance instIsProbabilityMeasure_gauss2 : IsProbabilityMeasure gauss2 := by
  unfold gauss2; infer_instance

private instance instIsProbabilityMeasure_gaussTie : IsProbabilityMeasure gaussTie := by
  unfold gaussTie; infer_instance

private instance instIsProbabilityMeasure_blockMeasure :
    IsProbabilityMeasure blockMeasure := by
  unfold blockMeasure; infer_instance

/-- Any unit linear functional `(a, b)` on `gauss2` has law `gaussianReal 0 1`. -/
private theorem measurePreserving_dot2_unit {u : ℝ × ℝ} (hu : u.1 ^ 2 + u.2 ^ 2 = 1) :
    MeasurePreserving (dot2 u) gauss2 (gaussianReal 0 1) := by
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 ![u.1, u.2]
  have hv_nn : ‖v‖₊ ^ 2 = 1 :=
    Subtype.ext (by simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, v, hu])
  have hmp3 : MeasurePreserving (fun x : EuclideanSpace ℝ (Fin 2) => ⟪v, x⟫)
      (stdGaussian (EuclideanSpace ℝ (Fin 2))) (gaussianReal 0 1) :=
    ⟨by fun_prop, by rw [stdGaussian_map_inner, hv_nn]⟩
  unfold gauss2
  convert ((hmp3.comp (measurePreserving_toLp_pi_gaussianReal (Fin 2))).comp
    (measurePreserving_finTwoArrow (gaussianReal 0 1)).symm) using 1
  funext p
  simp only [Function.comp_apply, PiLp.inner_apply, Fin.sum_univ_two, v,
    Matrix.cons_val_zero, Matrix.cons_val_one, RCLike.inner_apply, conj_trivial]
  change u.1 * p.1 + u.2 * p.2 = p.1 * u.1 + p.2 * u.2
  ring

/-- Any orthogonal `2 × 2` map given by two orthogonal unit vectors preserves `gauss2`. -/
private theorem measurePreserving_ortho2 {u₀ u₁ : ℝ × ℝ}
    (h₀ : u₀.1 ^ 2 + u₀.2 ^ 2 = 1) (h₁ : u₁.1 ^ 2 + u₁.2 ^ 2 = 1)
    (horth : u₀.1 * u₁.1 + u₀.2 * u₁.2 = 0) :
    MeasurePreserving (fun p : ℝ × ℝ => (dot2 u₀ p, dot2 u₁ p)) gauss2 gauss2 := by
  let v : Fin 2 → EuclideanSpace ℝ (Fin 2) :=
    ![WithLp.toLp 2 ![u₀.1, u₀.2], WithLp.toLp 2 ![u₁.1, u₁.2] ]
  have hv_norm (i : Fin 2) : ‖v i‖ = 1 := by
    fin_cases i <;> simp [EuclideanSpace.norm_eq, Fin.sum_univ_two, v, h₀, h₁]
  have hv_orth : Pairwise fun i j : Fin 2 => ⟪v i, v j⟫ = 0 := fun i j hij => by
    fin_cases i <;> fin_cases j <;> try exact absurd rfl hij
    all_goals
      simp only [PiLp.inner_apply, Fin.sum_univ_two, RCLike.inner_apply, conj_trivial]
      dsimp [v]
      linarith only [horth]
  have hmp3 : MeasurePreserving (fun x (i : Fin 2) => ⟪v i, x⟫)
      (stdGaussian (EuclideanSpace ℝ (Fin 2))) (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) :=
    ⟨by fun_prop, stdGaussian_map_inner_pi hv_norm hv_orth⟩
  unfold gauss2
  convert (measurePreserving_finTwoArrow (gaussianReal 0 1)).comp
    ((hmp3.comp (measurePreserving_toLp_pi_gaussianReal (Fin 2))).comp
      (measurePreserving_finTwoArrow (gaussianReal 0 1)).symm) using 1
  funext p
  ext <;> simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply, PiLp.inner_apply,
      Fin.sum_univ_two, v, Matrix.cons_val_zero, Matrix.cons_val_one,
      RCLike.inner_apply, conj_trivial]
  exacts [(by ring : u₀.1 * p.1 + u₀.2 * p.2 = p.1 * u₀.1 + p.2 * u₀.2),
    (by ring : u₁.1 * p.1 + u₁.2 * p.2 = p.1 * u₁.1 + p.2 * u₁.2)]

private theorem measurePreserving_rot120 : MeasurePreserving rot120 gauss2 gauss2 := by
  convert measurePreserving_ortho2 (u₀ := (-1 / 2, -√3 / 2)) (u₁ := (√3 / 2, -1 / 2))
    (by ring_nf; rw [sq_sqrt (by norm_num)]; norm_num)
    (by ring_nf; rw [sq_sqrt (by norm_num)]; norm_num)
    (by ring) using 1
  funext p
  ext <;> (dsimp [rot120, dot2]; ring)

private theorem measurePreserving_neg2 : MeasurePreserving neg2 gauss2 gauss2 := by
  convert measurePreserving_ortho2 (u₀ := (-1, 0)) (u₁ := (0, -1))
    (by norm_num) (by norm_num) (by norm_num) using 1
  funext p
  ext <;> (dsimp [neg2, dot2]; ring)

/-- Cyclic shift `τ ↦ (c ↦ τ (c + 2))` on `Fin 3 → ℝ` preserves `gaussTie`. -/
private def shiftTie (τ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun c => τ (c + 2)

private theorem shiftTie_add_one (τ : Fin 3 → ℝ) (c : Fin 3) :
    shiftTie τ (c + 1) = τ c := by
  exact congrArg τ (by fin_cases c <;> decide)

private theorem measurePreserving_shiftTie :
    MeasurePreserving shiftTie gaussTie gaussTie := by
  exact (measurePreserving_piCongrLeft (α := fun _ : Fin 3 => ℝ)
    (fun _ : Fin 3 => gaussianReal 0 1)
    { toFun := fun c => c + 2
      invFun := fun c => c + 1
      left_inv := fun c => by fin_cases c <;> decide
      right_inv := fun c => by fin_cases c <;> decide }).symm

private noncomputable def rotSample (s : BlockSample) : BlockSample :=
  (rot120 s.1, shiftTie s.2)

private def negSample (s : BlockSample) : BlockSample :=
  (neg2 s.1, s.2)

private theorem measurePreserving_rotSample :
    MeasurePreserving rotSample blockMeasure blockMeasure :=
  measurePreserving_rot120.prod measurePreserving_shiftTie

private theorem measurePreserving_negSample :
    MeasurePreserving negSample blockMeasure blockMeasure :=
  measurePreserving_neg2.prod (MeasurePreserving.id gaussTie)

/-- Under `gaussTie`, two distinct coordinates agree with probability zero. -/
private theorem gaussTie_not_injective_zero :
    gaussTie.real {τ : Fin 3 → ℝ | ¬Function.Injective τ} = 0 := by
  have hpair (c₁ c₂ : Fin 3) (hne : c₁ ≠ c₂) :
      gaussTie.real {τ : Fin 3 → ℝ | τ c₁ = τ c₂} = 0 := by
    let e₁ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single c₁ 1
    let e₂ : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single c₂ 1
    let u : EuclideanSpace ℝ (Fin 3) := (1 / √2 : ℝ) • (e₁ - e₂)
    have hon := EuclideanSpace.orthonormal_single (𝕜 := ℝ) (ι := Fin 3)
    have hu : ‖u‖ = 1 := by
      have hsub_sq : ‖e₁ - e₂‖ ^ 2 = 2 := by
        rw [@norm_sub_sq_real (EuclideanSpace ℝ (Fin 3)) _ _ e₁ e₂, hon.1 c₁, hon.1 c₂, hon.2 hne]
        norm_num
      rw [norm_smul, ← sqrt_sq (norm_nonneg (e₁ - e₂)), hsub_sq,
        Real.norm_of_nonneg (by positivity)]
      exact one_div_mul_cancel (by positivity)
    have hsub : {τ : Fin 3 → ℝ | τ c₁ = τ c₂} ⊆
        {τ : Fin 3 → ℝ | ⟪u, WithLp.toLp 2 τ⟫ = 0} := fun τ (hτ : τ c₁ = τ c₂) => by
      simp [u, e₁, e₂, real_inner_smul_left, inner_sub_left, EuclideanSpace.inner_single_left, hτ]
    exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (measure_mono_null hsub
      ((measureReal_eq_zero_iff (measure_ne_top _ _)).mp
        (measureReal_pi_gaussianReal_inner_eq_zero hu)))
  have hcov : {τ : Fin 3 → ℝ | ¬Function.Injective τ} ⊆
      {τ | τ 0 = τ 1} ∪ ({τ | τ 1 = τ 2} ∪ {τ | τ 2 = τ 0}) := fun τ hτ => by
    obtain ⟨c₁, c₂, heq, hne⟩ := Function.not_injective_iff.mp hτ
    fin_cases c₁ <;> fin_cases c₂ <;> simp only [mem_union, mem_ofPred_eq] <;> grind
  have h (c₁ c₂ : Fin 3) (hne : c₁ ≠ c₂) :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).mp (hpair c₁ c₂ hne)
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (measure_mono_null hcov
    (measure_union_null (h 0 1 (by decide))
      (measure_union_null (h 1 2 (by decide)) (h 2 0 (by decide)))))

/-- Under two independent copies of `gauss2`, `{((a₀, a₁), (b₀, b₁)) | a₀ * b₁ = b₀ * a₁}` has
measure zero. -/
private theorem gauss2_prod_det_eq_zero :
    (gauss2.prod gauss2) {p : (ℝ × ℝ) × (ℝ × ℝ) | p.1.1 * p.2.2 - p.1.2 * p.2.1 = 0} = 0 := by
  have := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | p.1.1 * p.2.2 - p.1.2 * p.2.1 = 0}
  have hSm : MeasurableSet S :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [Measure.prod_apply hSm]
  have ha0 : gauss2 {a : ℝ × ℝ | a.1 = 0} = 0 := by
    have hset : {a : ℝ × ℝ | a.1 = 0} = ({0} : Set ℝ) ×ˢ univ := Set.ext fun _ => by simp
    rw [hset, gauss2, Measure.prod_prod, measure_singleton, zero_mul]
  refine (lintegral_eq_zero_iff (measurable_measure_prodMk_left hSm)).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr ha0] with a (ha : a.1 ≠ 0)
  have hpre_m : MeasurableSet (Prod.mk a ⁻¹' S) := hSm.preimage (by fun_prop)
  rw [gauss2, Measure.prod_apply hpre_m]
  refine (lintegral_eq_zero_iff (measurable_measure_prodMk_left hpre_m)).mpr
    (Filter.Eventually.of_forall fun b₀ =>
      measure_mono_null (fun b₁ hb₁ => ?_) (measure_singleton (a.2 * b₀ / a.1)))
  simp only [mem_preimage, S, mem_ofPred_eq, mem_singleton_iff] at hb₁ ⊢
  rw [eq_div_iff ha]
  linarith only [hb₁]

/-- For distinct unit vectors `y₁ ≠ y₂` with `-1 < ⟪y₁, y₂⟫`, the `2`D Gaussian projections
`(⟪y_i, g₁⟫, ⟪y_i, g₂⟫)` are collinear (`det2 = 0`) with probability zero. -/
private theorem measureReal_pi_prod_det2_eq_zero {ι : Type*} [Fintype ι]
    {y₁ y₂ : EuclideanSpace ℝ ι} (hy₁ : ‖y₁‖ = 1) (hy₂ : ‖y₂‖ = 1)
    (hρ_gt : -1 < ⟪y₁, y₂⟫) (hne : y₁ ≠ y₂) :
    ((Measure.pi fun _ : ι => gaussianReal 0 1).prod
        (Measure.pi fun _ : ι => gaussianReal 0 1)).real
      {g : (ι → ℝ) × (ι → ℝ) |
        det2 (⟪y₁, WithLp.toLp 2 g.1⟫, ⟪y₁, WithLp.toLp 2 g.2⟫)
          (⟪y₂, WithLp.toLp 2 g.1⟫, ⟪y₂, WithLp.toLp 2 g.2⟫) = 0} = 0 := by
  set ρ := ⟪y₁, y₂⟫
  have hρ_lt : ρ < 1 := by
    have hpos : 0 < ‖y₂ - y₁‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm))
    rw [norm_sub_sq_real, hy₂, hy₁, real_inner_comm] at hpos
    linarith only [hpos]
  set w := y₂ - ρ • y₁
  have hw_sq : ‖w‖ ^ 2 = 1 - ρ ^ 2 := by
    dsimp [w]
    rw [norm_sub_sq_real, hy₂, norm_smul, Real.norm_eq_abs, hy₁, mul_one, sq_abs,
      real_inner_smul_right, real_inner_comm]
    ring
  have hw_pos : 0 < ‖w‖ := (norm_nonneg w).lt_of_ne' fun h0 => by
    rw [h0] at hw_sq
    nlinarith only [hρ_gt, hρ_lt, hw_sq]
  let u₂ : EuclideanSpace ℝ ι := ‖w‖⁻¹ • w
  have hu₂_norm : ‖u₂‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw_pos.ne']
  have hy₁u₂ : ⟪y₁, u₂⟫ = 0 := by
    simp [u₂, w, ρ, real_inner_smul_right, inner_sub_right, hy₁]
  have hy₂_decomp (x : EuclideanSpace ℝ ι) :
      ⟪y₂, x⟫ = ρ * ⟪y₁, x⟫ + ‖w‖ * ⟪u₂, x⟫ := by
    have hw_eq : y₂ = ρ • y₁ + ‖w‖ • u₂ := by simp [u₂, w, smul_smul, hw_pos.ne']
    conv_lhs => rw [hw_eq]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  let u : Fin 2 → EuclideanSpace ℝ ι := ![y₁, u₂]
  have hu_norm (i : Fin 2) : ‖u i‖ = 1 := by
    fin_cases i <;> simp [u, hy₁, hu₂_norm]
  have hu_orth : Pairwise fun i j : Fin 2 => ⟪u i, u j⟫ = 0 := fun i j hij => by
    clear * - u hy₁u₂ hij
    fin_cases i <;> fin_cases j <;> simp [u, hy₁u₂, real_inner_comm y₁ u₂] at hij ⊢
  let proj (x : EuclideanSpace ℝ ι) : ℝ × ℝ := (⟪y₁, x⟫, ⟪u₂, x⟫)
  have hmp_single : MeasurePreserving proj (stdGaussian (EuclideanSpace ℝ ι)) gauss2 := by
    unfold gauss2
    convert (measurePreserving_finTwoArrow (gaussianReal 0 1)).comp
      (MeasurePreserving.mk (by fun_prop) (stdGaussian_map_inner_pi hu_norm hu_orth)) using 1
    ext x <;> simp [proj, u]
  have hmp_all := (hmp_single.prod hmp_single).comp
    ((measurePreserving_toLp_pi_gaussianReal ι).prod (measurePreserving_toLp_pi_gaussianReal ι))
  set S : Set ((ℝ × ℝ) × (ℝ × ℝ)) := {p | p.1.1 * p.2.2 - p.1.2 * p.2.1 = 0}
  have hSm : MeasurableSet S :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  have hsub : {g : (ι → ℝ) × (ι → ℝ) |
      det2 (⟪y₁, WithLp.toLp 2 g.1⟫, ⟪y₁, WithLp.toLp 2 g.2⟫)
        (⟪y₂, WithLp.toLp 2 g.1⟫, ⟪y₂, WithLp.toLp 2 g.2⟫) = 0} ⊆
      (Prod.map proj proj ∘ Prod.map (WithLp.toLp 2) (WithLp.toLp 2)) ⁻¹' S := by
    intro g hg
    simp only [mem_ofPred_eq, mem_preimage, Function.comp_apply, proj, S] at hg ⊢
    rw [hy₂_decomp, hy₂_decomp] at hg
    refine (mul_eq_zero.mp ?_).resolve_left hw_pos.ne'
    dsimp only [det2, Prod.map] at hg ⊢
    linear_combination hg
  exact (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr (measure_mono_null hsub
    ((hmp_all.measure_preimage hSm.nullMeasurableSet).trans gauss2_prod_det_eq_zero))


end Cslib.Circuits.Frontier.TensorRank
