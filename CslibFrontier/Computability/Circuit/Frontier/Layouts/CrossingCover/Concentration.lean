/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.GaussianComparison
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.CrossingCover.Interpolation
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Cubic
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Efron–Stein concentration and threshold-grid crossing-cover reduction

This module proves the bounded-difference variance inequality (Efron–Stein) for finite products of
probability measures and applies it to reduce the cubic cutwidth of a graph `G` to the expected
crossing-cover size at real thresholds under any unit-variance Gaussian score family with locally
bounded coordinate influence.

## Main results

* `Cslib.Circuits.Frontier.CrossingCover.integral_sq_sub_mean_le_of_boundedDiff`:
  **Efron–Stein variance inequality** for bounded measurable functions on a finite product space
  `Measure.pi μ`: if changing coordinate `i` alters `f` by at most `c i`, then
  `∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P ≤ ∑ i, c i ^ 2`.
* `Cslib.Circuits.Frontier.CrossingCover.measureReal_ge_mean_add_le_of_boundedDiff`:
  corresponding one-sided Chebyshev deviation bound.
* `Cslib.Circuits.Frontier.CrossingCover.exists_width_le_of_expected_crossingCover`:
  generic Gaussian concentration + interpolation step turning a uniform threshold expectation bound
  `∫ g, crossingCover G (thresholdVec (row · ⬝ᵥ g) t) ≤ γ * |V|` into a layout of width at most
  `(γ + ξ) * |V|`, for every sufficiently large cubic graph. Its proof uses a deterministic
  sandwich relating every prefix of a score-sorted vertex ordering to either a tail set (`< -T` or
  `≥ T`) or a single grid threshold plus the enclosing window, with no distinctness assumption on
  the scores.
-/

public section

namespace Cslib.Circuits.Frontier.CrossingCover

open Finset MeasureTheory ProbabilityTheory Real Set

section EfronStein

/-- **Efron–Stein variance inequality on `Fin n`.** For a product of probability measures on
`∀ i : Fin n, α i`, any bounded measurable function `f` satisfying the coordinate-wise bounded
difference `|f (Function.update x i u) - f x| ≤ c i` has variance bounded by `∑ i, c i ^ 2`. -/
private theorem efronStein_fin :
    ∀ (n : ℕ) (α : Fin n → Type*) [∀ i, MeasurableSpace (α i)]
      (μ : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (μ i)]
      (f : (∀ i, α i) → ℝ), Measurable f →
      ∀ (M : ℝ), (∀ x, |f x| ≤ M) → ∀ (c : Fin n → ℝ),
      (∀ i, 0 ≤ c i) →
      (∀ (i : Fin n) (x : ∀ j, α j) (u : α i),
        |f (Function.update x i u) - f x| ≤ c i) →
      let P : Measure (∀ i, α i) := Measure.pi μ
      ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P ≤ ∑ i : Fin n, c i ^ 2 := by
  intro n
  induction n with
  | zero =>
    intro α _ μ _ f _ M _ c _ _ P
    have heq : ∀ x y : ∀ i : Fin 0, α i, x = y := fun x y => funext fun i => i.elim0
    have hconst : ∀ x, f x = ∫ y, f y ∂P := fun x => by
      have hf_eq : (fun y => f y) = fun _ => f x := funext fun y => congrArg f (heq y x)
      rw [hf_eq, integral_const, probReal_univ, one_smul]
    have hzero : (fun x => (f x - ∫ y, f y ∂P) ^ 2) = fun _ => (0 : ℝ) :=
      funext fun x => by rw [← hconst x, sub_self, zero_pow two_ne_zero]
    rw [hzero, integral_zero]; simp
  | succ n ih =>
    intro α _ μ _ f hf_meas M hM c hc_nonneg hdiff P
    let P₀ : Measure (α 0) := μ 0
    let Pn : Measure (∀ j : Fin n, α j.succ) := Measure.pi fun j => μ j.succ
    let e := MeasurableEquiv.piFinSuccAbove α 0
    have hmp : MeasurePreserving e P (P₀.prod Pn) :=
      MeasureTheory.measurePreserving_piFinSuccAbove μ 0
    let fp : α 0 × (∀ j : Fin n, α j.succ) → ℝ := fun p => f (e.symm p)
    have hfp_meas : Measurable fp := hf_meas.comp e.symm.measurable
    have hfp_bd : ∀ p, |fp p| ≤ M := fun p => hM (e.symm p)
    have hfp_int : Integrable fp (P₀.prod Pn) :=
      Integrable.of_bound hfp_meas.aestronglyMeasurable M (ae_of_all _ hfp_bd)
    let g : (∀ j : Fin n, α j.succ) → ℝ := fun y => ∫ t, fp (t, y) ∂P₀
    have hg_meas : Measurable g :=
      (StronglyMeasurable.integral_prod_left hfp_meas.stronglyMeasurable).measurable
    have hg_bd : ∀ y, |g y| ≤ M := fun y => by
      have hm_t : Measurable fun t : α 0 => fp (t, y) :=
        hfp_meas.comp (measurable_id.prodMk measurable_const)
      calc |∫ t, fp (t, y) ∂P₀| ≤ ∫ t, |fp (t, y)| ∂P₀ := abs_integral_le_integral_abs
        _ ≤ ∫ _t, M ∂P₀ := integral_mono
            (Integrable.of_bound hm_t.norm.aestronglyMeasurable M
              (ae_of_all _ fun t => by simpa [Real.norm_eq_abs] using hfp_bd (t, y)))
            (integrable_const M) (fun t => hfp_bd (t, y))
        _ = M := by simp [P₀]
    have hmean_eq : ∫ x, f x ∂P = ∫ y, g y ∂Pn := by
      have h1 : ∫ x, f x ∂P = ∫ p, fp p ∂(P₀.prod Pn) := by
        have hfg : (fun x => f x) = fun x => fp (e x) :=
          funext fun x => congrArg f (e.symm_apply_apply x).symm
        rw [hfg]
        exact hmp.integral_comp e.measurableEmbedding fp
      rw [h1, integral_prod_symm fp hfp_int]
    set m : ℝ := ∫ y, g y ∂Pn
    have hvar_eq : ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P =
        ∫ y, (∫ t, (fp (t, y) - g y) ^ 2 ∂P₀) ∂Pn + ∫ y, (g y - m) ^ 2 ∂Pn := by
      rw [hmean_eq]
      have h1 : ∫ x, (f x - m) ^ 2 ∂P = ∫ p, (fp p - m) ^ 2 ∂(P₀.prod Pn) := by
        have hfg : (fun x => (f x - m) ^ 2) = fun x => (fp (e x) - m) ^ 2 :=
          funext fun x => by simp only [fp, e.symm_apply_apply]
        rw [hfg]
        exact hmp.integral_comp e.measurableEmbedding (fun p => (fp p - m) ^ 2)
      have hsq_int : Integrable (fun p => (fp p - m) ^ 2) (P₀.prod Pn) :=
        Integrable.of_bound ((hfp_meas.sub measurable_const).pow_const 2).aestronglyMeasurable
          ((M + |m|) ^ 2) (ae_of_all _ fun p => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
            have hle : |fp p - m| ≤ M + |m| :=
              (abs_sub _ _).trans (add_le_add (hfp_bd p) le_rfl)
            exact pow_le_pow_left₀ (abs_nonneg _) hle 2)
      rw [h1, integral_prod_symm _ hsq_int]
      have hinner : ∀ y, ∫ t, (fp (t, y) - m) ^ 2 ∂P₀ =
          (∫ t, (fp (t, y) - g y) ^ 2 ∂P₀) + (g y - m) ^ 2 := fun y => by
        have hdecomp : ∀ t, (fp (t, y) - m) ^ 2 =
            (fp (t, y) - g y) ^ 2 + 2 * (g y - m) * (fp (t, y) - g y) + (g y - m) ^ 2 :=
          fun t => by ring
        simp_rw [hdecomp]
        have hi1 : Integrable (fun t => fp (t, y)) P₀ :=
          Integrable.of_bound
            (hfp_meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
            M (ae_of_all _ fun t => hfp_bd (t, y))
        have hi_sq : Integrable (fun t => (fp (t, y) - g y) ^ 2) P₀ :=
          Integrable.of_bound
            (((hfp_meas.comp (measurable_id.prodMk measurable_const)).sub
              measurable_const).pow_const 2).aestronglyMeasurable
            ((M + |g y|) ^ 2) (ae_of_all _ fun t => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _)
                ((abs_sub (fp (t, y)) (g y)).trans (add_le_add (hfp_bd (t, y)) le_rfl)) 2)
        have hi_lin : Integrable (fun t => 2 * (g y - m) * (fp (t, y) - g y)) P₀ :=
          (hi1.sub (integrable_const (g y))).const_mul _
        have hsum := integral_add (hi_sq.add hi_lin) (integrable_const ((g y - m) ^ 2))
        simp only [Pi.add_apply] at hsum
        rw [hsum, integral_add hi_sq hi_lin, integral_const_mul,
          integral_sub hi1 (integrable_const (g y))]
        simp [P₀, g]
      simp_rw [hinner]
      have hsub_sm : StronglyMeasurable fun p : α 0 × (∀ j : Fin n, α j.succ) =>
          (fp p - g p.2) ^ 2 :=
        ((hfp_meas.sub (hg_meas.comp measurable_snd)).pow_const 2).stronglyMeasurable
      have hint1 : Integrable (fun y => ∫ t, (fp (t, y) - g y) ^ 2 ∂P₀) Pn := by
        refine Integrable.of_bound
          (StronglyMeasurable.integral_prod_left hsub_sm).aestronglyMeasurable
          ((2 * M) ^ 2) (ae_of_all _ fun y => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => sq_nonneg _)]
        have his : Integrable (fun t => (fp (t, y) - g y) ^ 2) P₀ :=
          Integrable.of_bound
            (((hfp_meas.comp (measurable_id.prodMk measurable_const)).sub
              measurable_const).pow_const 2).aestronglyMeasurable
            ((2 * M) ^ 2) (ae_of_all _ fun t => by
              rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
              have hle : |fp (t, y) - g y| ≤ 2 * M :=
                (abs_sub _ _).trans (by linarith [hfp_bd (t, y), hg_bd y])
              exact pow_le_pow_left₀ (abs_nonneg _) hle 2)
        calc ∫ t, (fp (t, y) - g y) ^ 2 ∂P₀
            ≤ ∫ _t, (2 * M) ^ 2 ∂P₀ := integral_mono his (integrable_const _) fun t => by
                rw [← sq_abs]
                have hle : |fp (t, y) - g y| ≤ 2 * M :=
                  (abs_sub _ _).trans (by linarith [hfp_bd (t, y), hg_bd y])
                exact pow_le_pow_left₀ (abs_nonneg _) hle 2
          _ = (2 * M) ^ 2 := by simp [P₀]
      have hint2 : Integrable (fun y => (g y - m) ^ 2) Pn :=
        Integrable.of_bound ((hg_meas.sub measurable_const).pow_const 2).aestronglyMeasurable
          ((M + |m|) ^ 2) (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _)
              ((abs_sub _ _).trans (add_le_add (hg_bd y) le_rfl)) 2)
      exact integral_add hint1 hint2
    have hfirst_le : ∫ y, (∫ t, (fp (t, y) - g y) ^ 2 ∂P₀) ∂Pn ≤ c 0 ^ 2 := by
      have hpt : ∀ y t, |fp (t, y) - g y| ≤ c 0 := fun y t => by
        have hsub : fp (t, y) - g y = ∫ s, (fp (t, y) - fp (s, y)) ∂P₀ := by
          have hi : Integrable (fun s => fp (s, y)) P₀ :=
            Integrable.of_bound
              (hfp_meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
              M (ae_of_all _ fun s => hfp_bd (s, y))
          rw [integral_sub (integrable_const _) hi]; simp [P₀, g]
        rw [hsub]
        have hpair : ∀ s, |fp (t, y) - fp (s, y)| ≤ c 0 := fun s => by
          have heq : e.symm (t, y) = Function.update (e.symm (s, y)) 0 t := by
            ext i
            refine Fin.cases ?_ (fun j => ?_) i
            · change (Fin.cons t y : ∀ k, α k) 0 = _
              simp
            · change (Fin.cons t y : ∀ k, α k) j.succ =
                Function.update (Fin.cons s y : ∀ k, α k) 0 t j.succ
              rw [Function.update_of_ne (Fin.succ_ne_zero j)]
              simp
          calc |fp (t, y) - fp (s, y)|
              = |f (Function.update (e.symm (s, y)) 0 t) - f (e.symm (s, y))| := by
                dsimp only [fp]; exact congrArg (fun z => |f z - f (e.symm (s, y))|) heq
            _ ≤ c 0 := hdiff 0 (e.symm (s, y)) t
        have hint_d : Integrable (fun s => |fp (t, y) - fp (s, y)|) P₀ :=
          Integrable.of_bound
            ((measurable_const.sub
              (hfp_meas.comp (measurable_id.prodMk measurable_const))).norm).aestronglyMeasurable
            (c 0) (ae_of_all _ fun s => by simpa [Real.norm_eq_abs] using hpair s)
        calc |∫ s, (fp (t, y) - fp (s, y)) ∂P₀|
            ≤ ∫ s, |fp (t, y) - fp (s, y)| ∂P₀ := abs_integral_le_integral_abs
          _ ≤ ∫ _s, c 0 ∂P₀ := integral_mono hint_d (integrable_const _) hpair
          _ = c 0 := by simp [P₀]
      have hinner_le : ∀ y, ∫ t, (fp (t, y) - g y) ^ 2 ∂P₀ ≤ c 0 ^ 2 := fun y => by
        have hi : Integrable (fun t => (fp (t, y) - g y) ^ 2) P₀ :=
          Integrable.of_bound
            (((hfp_meas.comp (measurable_id.prodMk measurable_const)).sub
              measurable_const).pow_const 2).aestronglyMeasurable
            (c 0 ^ 2) (ae_of_all _ fun t => by
              rw [Real.norm_eq_abs, abs_sq]
              exact sq_le_sq.mpr (by rw [abs_of_nonneg (hc_nonneg 0)]; exact hpt y t))
        calc ∫ t, (fp (t, y) - g y) ^ 2 ∂P₀
            ≤ ∫ _t, c 0 ^ 2 ∂P₀ := integral_mono hi (integrable_const _) fun t => by
                have := hpt y t
                nlinarith [sq_abs (fp (t, y) - g y), abs_nonneg (fp (t, y) - g y), hc_nonneg 0]
          _ = c 0 ^ 2 := by simp [P₀]
      have hsub_sm2 : StronglyMeasurable fun p : α 0 × (∀ j : Fin n, α j.succ) =>
          (fp p - g p.2) ^ 2 :=
        ((hfp_meas.sub (hg_meas.comp measurable_snd)).pow_const 2).stronglyMeasurable
      have hint_outer : Integrable (fun y => ∫ t, (fp (t, y) - g y) ^ 2 ∂P₀) Pn :=
        Integrable.of_bound
          (StronglyMeasurable.integral_prod_left hsub_sm2).aestronglyMeasurable
          (c 0 ^ 2) (ae_of_all _ fun y => by
            rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun t => sq_nonneg _)]
            exact hinner_le y)
      calc ∫ y, (∫ t, (fp (t, y) - g y) ^ 2 ∂P₀) ∂Pn
          ≤ ∫ _y, c 0 ^ 2 ∂Pn := integral_mono hint_outer (integrable_const _) hinner_le
        _ = c 0 ^ 2 := by simp [Pn]
    have hg_diff : ∀ (k : Fin n) (y : ∀ j : Fin n, α j.succ) (u : α k.succ),
        |g (Function.update y k u) - g y| ≤ c k.succ := fun k y u => by
      have hi1 : Integrable (fun t => fp (t, Function.update y k u)) P₀ :=
        Integrable.of_bound
          (hfp_meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
          M (ae_of_all _ fun t => hfp_bd (t, _))
      have hi2 : Integrable (fun t => fp (t, y)) P₀ :=
        Integrable.of_bound
          (hfp_meas.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
          M (ae_of_all _ fun t => hfp_bd (t, y))
      have hsub : g (Function.update y k u) - g y =
          ∫ t, (fp (t, Function.update y k u) - fp (t, y)) ∂P₀ :=
        (integral_sub hi1 hi2).symm
      rw [hsub]
      have hpt : ∀ t, |fp (t, Function.update y k u) - fp (t, y)| ≤ c k.succ := fun t => by
        have heq : e.symm (t, Function.update y k u) =
            Function.update (e.symm (t, y)) k.succ u := by
          ext i
          refine Fin.cases ?_ (fun j => ?_) i
          · change (Fin.cons t (Function.update y k u) : ∀ m, α m) 0 =
              Function.update (Fin.cons t y : ∀ m, α m) k.succ u 0
            rw [Function.update_of_ne (Fin.succ_ne_zero k).symm]
            simp
          · change (Fin.cons t (Function.update y k u) : ∀ m, α m) j.succ =
              Function.update (Fin.cons t y : ∀ m, α m) k.succ u j.succ
            by_cases hjk : j = k
            · subst hjk; simp
            · have hne : j.succ ≠ k.succ := fun h => hjk (Fin.succ_inj.mp h)
              rw [Fin.cons_succ, Function.update_of_ne hjk, Function.update_of_ne hne,
                Fin.cons_succ]
        calc |fp (t, Function.update y k u) - fp (t, y)|
            = |f (Function.update (e.symm (t, y)) k.succ u) - f (e.symm (t, y))| := by
              dsimp only [fp]; exact congrArg (fun z => |f z - f (e.symm (t, y))|) heq
          _ ≤ c k.succ := hdiff k.succ (e.symm (t, y)) u
      calc |∫ t, (fp (t, Function.update y k u) - fp (t, y)) ∂P₀|
          ≤ ∫ t, |fp (t, Function.update y k u) - fp (t, y)| ∂P₀ := abs_integral_le_integral_abs
        _ ≤ ∫ _t, c k.succ ∂P₀ := integral_mono ((hi1.sub hi2).abs) (integrable_const _) hpt
        _ = c k.succ := by simp [P₀]
    have hsec_le := ih (fun j => α j.succ) (fun j => μ j.succ) g hg_meas M hg_bd
      (fun j => c j.succ) (fun j => hc_nonneg j.succ) hg_diff
    rw [hvar_eq, Fin.sum_univ_succ]
    linarith

/-- **Efron–Stein bounded-difference variance inequality.** Under any finite product of probability
measures on `κ → ℝ` (in particular, `piGauss κ`), a bounded measurable function `f : (κ → ℝ) → ℝ`
whose coordinate perturbations satisfy `|f (update x k u) - f x| ≤ c k` has variance at most
`∑ k, c k ^ 2`. -/
theorem integral_sq_sub_mean_le_of_boundedDiff {κ : Type*} [Fintype κ]
    (μ : κ → Measure ℝ) [∀ k, IsProbabilityMeasure (μ k)]
    {f : (κ → ℝ) → ℝ} (hf_meas : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) {c : κ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (hdiff : ∀ (k : κ) (x : κ → ℝ) (u : ℝ),
      open Classical in |f (Function.update x k u) - f x| ≤ c k) :
    let P : Measure (κ → ℝ) := Measure.pi μ
    ∫ x, (f x - ∫ y, f y ∂P) ^ 2 ∂P ≤ ∑ k : κ, c k ^ 2 := by
  classical
  let eqv : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let σ : MeasurableEquiv (Fin (Fintype.card κ) → ℝ) (κ → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ => ℝ) eqv
  have hmp : MeasurePreserving σ (Measure.pi fun i => μ (eqv i)) (Measure.pi μ) :=
    MeasureTheory.measurePreserving_piCongrLeft (fun k => μ k) eqv
  let f' : (Fin (Fintype.card κ) → ℝ) → ℝ := f ∘ σ
  have hf'_meas : Measurable f' := hf_meas.comp σ.measurable
  have hf'_mean : ∫ y, f' y ∂(Measure.pi fun i => μ (eqv i)) = ∫ y, f y ∂(Measure.pi μ) :=
    hmp.integral_comp σ.measurableEmbedding f
  have hbd : ∀ x, |f' x| ≤ M := fun x => hM (σ x)
  have hdiff' : ∀ (i : Fin (Fintype.card κ)) (x : Fin (Fintype.card κ) → ℝ) (u : ℝ),
      |f' (Function.update x i u) - f' x| ≤ c (eqv i) := fun i x u => by
    have heq : σ (Function.update x i u) = Function.update (σ x) (eqv i) u := by
      apply σ.symm.injective
      ext j
      rw [σ.symm_apply_apply]
      change Function.update x i u j = Function.update (σ x) (eqv i) u (eqv j)
      by_cases hji : j = i
      · subst hji; simp
      · have hne : eqv j ≠ eqv i := fun h => hji (eqv.injective h)
        rw [Function.update_of_ne hji, Function.update_of_ne hne]
        exact (congrFun (σ.symm_apply_apply x) j).symm
    simpa [f', heq] using hdiff (eqv i) (σ x) u
  have hvar := efronStein_fin (Fintype.card κ) (fun _ => ℝ) (fun i => μ (eqv i)) f' hf'_meas
    M hbd (fun i => c (eqv i)) (fun i => hc (eqv i)) hdiff'
  have hvar_eq : ∫ x, (f' x - ∫ y, f' y ∂(Measure.pi fun i => μ (eqv i))) ^ 2
      ∂(Measure.pi fun i => μ (eqv i)) =
      ∫ x, (f x - ∫ y, f y ∂(Measure.pi μ)) ^ 2 ∂(Measure.pi μ) := by
    rw [hf'_mean]
    exact hmp.integral_comp σ.measurableEmbedding
      (fun z => (f z - ∫ y, f y ∂(Measure.pi μ)) ^ 2)
  have hsum_eq : ∑ i : Fin (Fintype.card κ), c (eqv i) ^ 2 = ∑ k : κ, c k ^ 2 :=
    Fintype.sum_equiv eqv _ _ fun _ => rfl
  linarith [hvar, hvar_eq, hsum_eq]

/-- **One-sided Chebyshev bound from Efron–Stein.** Under `piGauss κ`, if `f` is bounded measurable
with coordinate perturbations `|f (update x k u) - f x| ≤ c k`, then for every `a > 0`,
`P {x | E[f] + a ≤ f x} ≤ (∑ k, c k ^ 2) / a ^ 2`. -/
theorem measureReal_ge_mean_add_le_of_boundedDiff {κ : Type*} [Fintype κ]
    {f : (κ → ℝ) → ℝ} (hf_meas : Measurable f)
    {M : ℝ} (hM : ∀ x, |f x| ≤ M) {c : κ → ℝ} (hc : ∀ k, 0 ≤ c k)
    (hdiff : ∀ (k : κ) (x : κ → ℝ) (u : ℝ),
      open Classical in |f (Function.update x k u) - f x| ≤ c k)
    {a : ℝ} (ha : 0 < a) :
    (piGauss κ).real {x | (∫ y, f y ∂(piGauss κ)) + a ≤ f x} ≤ (∑ k : κ, c k ^ 2) / a ^ 2 := by
  classical
  set P := piGauss κ
  set m := ∫ y, f y ∂P
  let g : (κ → ℝ) → ℝ := fun x => (f x - m) ^ 2
  have hg_int : Integrable g P :=
    Integrable.of_bound ((hf_meas.sub measurable_const).pow_const 2).aestronglyMeasurable
      ((M + |m|) ^ 2) (ae_of_all _ fun x => by
        change ‖(f x - m) ^ 2‖ ≤ (M + |m|) ^ 2
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((abs_sub _ _).trans (add_le_add (hM x) le_rfl)) 2)
  have hsub : {x | m + a ≤ f x} ⊆ {x | a ^ 2 ≤ g x} := fun x hx => by
    have hfm : a ≤ f x - m := by
      have : m + a ≤ f x := hx; linarith
    change a ^ 2 ≤ (f x - m) ^ 2
    exact pow_le_pow_left₀ ha.le hfm 2
  have hmeas_le : P.real {x | m + a ≤ f x} ≤ P.real {x | a ^ 2 ≤ g x} :=
    measureReal_mono hsub
  have hmarkov : a ^ 2 * P.real {x | a ^ 2 ≤ g x} ≤ ∫ x, g x ∂P :=
    mul_meas_ge_le_integral_of_nonneg (ae_of_all _ fun x => sq_nonneg (f x - m)) hg_int (a ^ 2)
  have hvar := integral_sq_sub_mean_le_of_boundedDiff (fun _ : κ => gaussianReal 0 1)
    hf_meas hM hc hdiff
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  rw [le_div_iff₀ ha2]
  calc P.real {x | m + a ≤ f x} * a ^ 2
      = a ^ 2 * P.real {x | m + a ≤ f x} := mul_comm _ _
    _ ≤ a ^ 2 * P.real {x | a ^ 2 ≤ g x} := mul_le_mul_of_nonneg_left hmeas_le ha2.le
    _ ≤ ∫ x, g x ∂P := hmarkov
    _ ≤ ∑ k : κ, c k ^ 2 := hvar

end EfronStein

section GridReduction

/-- **Prefix crossing cover controlled by a uniform threshold grid (no distinctness needed).**
Let `G` be a finite multigraph and `s : V → ℝ` any real vertex scoring. Take a nodup list
`vs : List V` listing `V` in non-decreasing order of `s`. For any grid `-T = t_0 < ... < t_K = T`
with step `δ = 2 * T / K` (`T > 0`, `K > 0`), *every* prefix bipartition
`v ↦ decide (v ∈ vs.take i)` satisfies

* `crossingCover G b_i ≤ max (|left tail|, |right tail|, max_k (crossingCover G (s < t_k) + |W_k|))`

even when vertices tie in score! -/
private theorem prefix_crossingCover_le_grid {V E : Type*} [Fintype V] [Finite E] [DecidableEq V]
    (G : Multigraph V E) (s : V → ℝ) (vs : List V) (hvs_mem : ∀ v : V, v ∈ vs)
    (hsort : vs.Pairwise fun u v => s u ≤ s v)
    {T : ℝ} (hT : 0 < T) {K : ℕ} (hK : 0 < K) (M : ℕ)
    (hL : (univ.filter fun v => s v < -T).card ≤ M)
    (hR : (univ.filter fun v => T ≤ s v).card ≤ M)
    (hGrid : ∀ k : Fin K,
      let tk : ℝ := -T + (k.val : ℝ) * (2 * T / K)
      let tk1 : ℝ := -T + ((k.val : ℝ) + 1) * (2 * T / K)
      crossingCover G (thresholdVec s tk) +
        (univ.filter fun v => tk ≤ s v ∧ s v < tk1).card ≤ M) :
    ∀ i ≤ vs.length, crossingCover G (fun v => decide (v ∈ vs.take i)) ≤ M := by
  classical
  have := Fintype.ofFinite E
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0; simp [crossingCover_const]
  · by_cases hin : i = vs.length
    · subst hin
      have htop : (fun v => decide (v ∈ vs.take vs.length)) = fun _ => true := by
        ext v; simp [hvs_mem v]
      rw [htop, crossingCover_const]; exact Nat.zero_le M
    · have him : i - 1 < vs.length := by omega
      set pivot := s vs[i - 1]
      have hle_piv : ∀ v ∈ vs.take i, s v ≤ pivot := fun v hv => by
        obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hv
        have halt : a < i := by rw [List.length_take] at ha; omega
        rw [List.getElem_take]
        by_cases hae : a = i - 1
        · subst hae; exact le_rfl
        · exact (List.pairwise_iff_getElem.mp hsort) a (i - 1) (by omega) him (by omega)
      have hge_piv : ∀ v, v ∉ vs.take i → pivot ≤ s v := fun v hv => by
        obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem (hvs_mem v)
        have ha_ge : i ≤ a := by
          by_contra hlt; push Not at hlt
          have hmem : a < (vs.take i).length := by rw [List.length_take]; omega
          have hm := List.getElem_mem hmem
          rw [List.getElem_take] at hm
          exact hv hm
        exact (List.pairwise_iff_getElem.mp hsort) (i - 1) a him ha (by omega)
      set b : V → Bool := fun v => decide (v ∈ vs.take i)
      by_cases hlow : pivot < -T
      · have hdiff : (univ.filter fun v => false ≠ b v).card ≤
            (univ.filter fun v => s v < -T).card :=
          card_le_card fun v hv => by
            have hbv : v ∈ vs.take i := by
              have h := (mem_filter.mp hv).2
              by_contra hn; exact h (by simp [b, hn])
            exact mem_filter.mpr ⟨mem_univ v, lt_of_le_of_lt (hle_piv v hbv) hlow⟩
        have hstep := crossingCover_sub_le_hamming G (fun _ => false) b
        rw [crossingCover_const] at hstep
        omega
      · push Not at hlow
        by_cases hhi : T ≤ pivot
        · have hdiff : (univ.filter fun v => true ≠ b v).card ≤
              (univ.filter fun v => T ≤ s v).card :=
            card_le_card fun v hv => by
              have hbv : v ∉ vs.take i := by
                have h := (mem_filter.mp hv).2
                intro hm; exact h (by simp [b, hm])
              exact mem_filter.mpr ⟨mem_univ v, hhi.trans (hge_piv v hbv)⟩
          have hstep := crossingCover_sub_le_hamming G (fun _ => true) b
          rw [crossingCover_const] at hstep
          omega
        · push Not at hhi
          have hδpos : 0 < (2 * T / K : ℝ) := by positivity
          set q : ℝ := (pivot + T) / (2 * T / K)
          have hq0 : 0 ≤ q := div_nonneg (by linarith) hδpos.le
          have hqK : q < (K : ℝ) := by
            rw [div_lt_iff₀ hδpos]
            have hKpos : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
            have hprod : (K : ℝ) * (2 * T / K) = 2 * T := by field_simp
            linarith
          let kNat : ℕ := Nat.floor q
          have hklt : kNat < K := by
            have : (kNat : ℝ) ≤ q := Nat.floor_le hq0
            exact_mod_cast (this.trans_lt hqK)
          let k : Fin K := ⟨kNat, hklt⟩
          let tk : ℝ := -T + (k.val : ℝ) * (2 * T / K)
          let tk1 : ℝ := -T + ((k.val : ℝ) + 1) * (2 * T / K)
          have htk_le : tk ≤ pivot := by
            have hfl : (kNat : ℝ) ≤ q := Nat.floor_le hq0
            have := (mul_le_mul_of_nonneg_right hfl hδpos.le)
            have hmul : q * (2 * T / K) = pivot + T := div_mul_cancel₀ _ hδpos.ne'
            linarith
          have hpiv_lt : pivot < tk1 := by
            have hfl : q < (kNat : ℝ) + 1 := Nat.lt_floor_add_one q
            have := mul_lt_mul_of_pos_right hfl hδpos
            have hmul : q * (2 * T / K) = pivot + T := div_mul_cancel₀ _ hδpos.ne'
            linarith
          have hdiff : (univ.filter fun v => thresholdVec s tk v ≠ b v).card ≤
              (univ.filter fun v => tk ≤ s v ∧ s v < tk1).card := by
            refine card_le_card fun v hv => mem_filter.mpr ⟨mem_univ v, ?_⟩
            have hne := (mem_filter.mp hv).2
            by_cases hm : v ∈ vs.take i
            · have hb : b v = true := by simp [b, hm]
              have htv : thresholdVec s tk v = false := by
                cases h : thresholdVec s tk v <;> simp_all
              have hge_tk : tk ≤ s v := by
                by_contra hlt; push Not at hlt
                exact absurd ((thresholdVec_apply_eq_true s tk v).mpr hlt) (by rw [htv]; decide)
              exact ⟨hge_tk, lt_of_le_of_lt (hle_piv v hm) hpiv_lt⟩
            · have hb : b v = false := by simp [b, hm]
              have htv : thresholdVec s tk v = true := by
                cases h : thresholdVec s tk v <;> simp_all
              have hlt_tk : s v < tk := (thresholdVec_apply_eq_true s tk v).mp htv
              exfalso; linarith [hge_piv v hm]
          have hstep := crossingCover_sub_le_hamming G (thresholdVec s tk) b
          have hg := hGrid k
          have htk_eq : (univ.filter fun v => tk ≤ s v ∧ s v < tk1).card =
              (univ.filter fun v =>
                -T + (k.val : ℝ) * (2 * T / K) ≤ s v ∧
                  s v < -T + ((k.val : ℝ) + 1) * (2 * T / K)).card := by
            congr 1
          exact hstep.trans ((Nat.add_le_add_left (hdiff.trans_eq htk_eq) _).trans hg)

end GridReduction

section MainReduction

private lemma measurable_score_fun {V κ : Type*} [Fintype κ] (row : V → κ → ℝ) (v : V) :
    Measurable fun g : κ → ℝ => ∑ k : κ, row v k * g k := by
  refine Finset.measurable_sum univ fun k _ => ?_
  exact measurable_const.mul (measurable_pi_apply k)

private lemma gaussianReal_dotProduct_law {κ : Type*} [Fintype κ]
    (a : κ → ℝ) (ha : ∑ k : κ, a k ^ 2 = 1) :
    (piGauss κ).map (fun g : κ → ℝ => ∑ k : κ, a k * g k) = gaussianReal 0 1 := by
  have hnorm : ‖WithLp.toLp 2 a‖₊ ^ 2 = 1 := by
    apply NNReal.coe_injective
    push_cast
    rw [EuclideanSpace.norm_sq_eq]
    simpa [Real.norm_eq_abs, sq_abs] using ha
  have hmap := pi_gaussianReal_map_dotProduct a
  change (piGauss κ).map (fun g : κ → ℝ => ∑ k : κ, a k * g k) = _
  simpa [dotProduct, piGauss, hnorm] using hmap

/-- For any finite multigraph `G` and score matrix `row : V → κ → ℝ` of unit rows whose squared
support cardinalities satisfy `∑ k, |{v | row v k ≠ 0}| ^ 2 ≤ C * |V|`, if the expected
crossing cover at *every* threshold `t : ℝ` is at most `γ * |V|`, then for every `ξ > 0` and large
enough `|V|`, `G` admits a vertex layout of width at most `(γ + ξ) * |V|`. -/
theorem exists_width_le_of_expected_crossingCover
    {V E κ : Type*} [Fintype V] [Finite E] [Fintype κ]
    (G : Multigraph V E) (h3 : ∀ v : V, (G.incidenceSet v).ncard = 3)
    (row : V → κ → ℝ) (hunit : ∀ v : V, ∑ k : κ, row v k ^ 2 = 1)
    {C γ ξ : ℝ} (hγ : 0 ≤ γ) (hξ : 0 < ξ)
    (hsupport : open Classical in
      ∑ k : κ, ((Finset.univ.filter fun v : V => row v k ≠ 0).card : ℝ) ^ 2 ≤
        C * (Nat.card V : ℝ))
    (hexp : ∀ t : ℝ,
      ∫ g : κ → ℝ,
        (crossingCover G (thresholdVec (fun v => ∑ k, row v k * g k) t) : ℝ) ∂(piGauss κ) ≤
        γ * (Nat.card V : ℝ))
    {T : ℝ} (hT : 0 < T) (hT_bd : 1 / T ^ 2 ≤ ξ / 4)
    {K : ℕ} (hK : 0 < K) (hK_bd : (2 * T / K) / √(2 * π) ≤ ξ / 4)
    (hN_prob : (2 * (K : ℝ) + 2) * C / (ξ / 8) ^ 2 < (Nat.card V : ℝ))
    (hN_six : (6 : ℝ) ≤ (ξ / 4) * (Nat.card V : ℝ)) :
    ∃ lay : Layout V, (G.width lay : ℝ) ≤ (γ + ξ) * (Nat.card V : ℝ) := by
  classical
  have := Fintype.ofFinite E
  let n : ℕ := Fintype.card V
  have hn_eq : (Nat.card V : ℝ) = (n : ℝ) := by simp [n, Nat.card_eq_fintype_card]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    have h6 : (6 : ℝ) ≤ (ξ / 4) * (n : ℝ) := by rw [← hn_eq]; exact hN_six
    have hpos : 0 < (ξ / 4) * (n : ℝ) := by linarith
    exact pos_of_mul_pos_right hpos (by positivity)
  let score (g : κ → ℝ) (v : V) : ℝ := ∑ k : κ, row v k * g k
  let c (k : κ) : ℝ := ((univ.filter fun v : V => row v k ≠ 0).card : ℝ)
  have hc_nonneg : ∀ k, 0 ≤ c k := fun k => Nat.cast_nonneg _
  have hc_sum : ∑ k : κ, c k ^ 2 ≤ C * (n : ℝ) := by
    rw [← hn_eq]; simpa only [c] using hsupport
  have hscore_diff : ∀ (k : κ) (g : κ → ℝ) (u : ℝ) (v : V),
      score (Function.update g k u) v ≠ score g v → row v k ≠ 0 := by
    intro k g u v hne hzero
    apply hne
    refine sum_congr rfl fun j _ => ?_
    by_cases hjk : j = k
    · subst hjk; simp [hzero]
    · rw [Function.update_of_ne hjk]
  have hcard_change : ∀ (P : ℝ → Prop) (k : κ) (g : κ → ℝ) (u : ℝ),
      |((univ.filter fun v : V => P (score (Function.update g k u) v)).card : ℝ) -
        ((univ.filter fun v : V => P (score g v)).card : ℝ)| ≤ c k := by
    intro P k g u
    let S₁ := univ.filter fun v : V => P (score (Function.update g k u) v)
    let S₂ := univ.filter fun v : V => P (score g v)
    let D := univ.filter fun v : V => row v k ≠ 0
    have h12 : S₁ ⊆ S₂ ∪ D := fun v hv => by
      by_cases hrow : row v k = 0
      · refine mem_union_left D (mem_filter.mpr ⟨mem_univ v, ?_⟩)
        have hsame : score (Function.update g k u) v = score g v := by
          by_contra hne; exact hscore_diff k g u v hne hrow
        rw [← hsame]; exact (mem_filter.mp hv).2
      · exact mem_union_right S₂ (mem_filter.mpr ⟨mem_univ v, hrow⟩)
    have h21 : S₂ ⊆ S₁ ∪ D := fun v hv => by
      by_cases hrow : row v k = 0
      · refine mem_union_left D (mem_filter.mpr ⟨mem_univ v, ?_⟩)
        have hsame : score (Function.update g k u) v = score g v := by
          by_contra hne; exact hscore_diff k g u v hne hrow
        rw [hsame]; exact (mem_filter.mp hv).2
      · exact mem_union_right S₁ (mem_filter.mpr ⟨mem_univ v, hrow⟩)
    have c1 : S₁.card ≤ S₂.card + D.card :=
      (Finset.card_le_card h12).trans (Finset.card_union_le S₂ D)
    have c2 : S₂.card ≤ S₁.card + D.card :=
      (Finset.card_le_card h21).trans (Finset.card_union_le S₁ D)
    rw [abs_le]
    have c1r : (S₁.card : ℝ) ≤ (S₂.card : ℝ) + (D.card : ℝ) := by exact_mod_cast c1
    have c2r : (S₂.card : ℝ) ≤ (S₁.card : ℝ) + (D.card : ℝ) := by exact_mod_cast c2
    constructor <;> linarith
  have hcc_diff : ∀ (t : ℝ) (k : κ) (g : κ → ℝ) (u : ℝ),
      |(crossingCover G (thresholdVec (score (Function.update g k u)) t) : ℝ) -
        (crossingCover G (thresholdVec (score g) t) : ℝ)| ≤ c k := by
    intro t k g u
    let b₁ := thresholdVec (score (Function.update g k u)) t
    let b₂ := thresholdVec (score g) t
    have hsub : (univ.filter fun v : V => b₁ v ≠ b₂ v) ⊆
        univ.filter fun v : V => row v k ≠ 0 := fun v hv =>
      mem_filter.mpr ⟨mem_univ v, fun hrow => by
        have hne := (mem_filter.mp hv).2
        apply hne
        have hsame : score (Function.update g k u) v = score g v := by
          by_contra hne'; exact hscore_diff k g u v hne' hrow
        simp [b₁, b₂, thresholdVec, hsame]⟩
    have hham : (univ.filter fun v : V => b₁ v ≠ b₂ v).card ≤
        (univ.filter fun v : V => row v k ≠ 0).card := Finset.card_le_card hsub
    have h1 := crossingCover_sub_le_hamming G b₁ b₂
    have h2 := crossingCover_sub_le_hamming G b₂ b₁
    have hsym : (univ.filter fun v : V => b₂ v ≠ b₁ v).card =
        (univ.filter fun v : V => b₁ v ≠ b₂ v).card := by
      congr 1; ext v; simp [ne_comm]
    rw [hsym] at h2
    rw [abs_le]
    have h1' : (crossingCover G b₂ : ℝ) ≤ (crossingCover G b₁ : ℝ) +
        ((univ.filter fun v : V => row v k ≠ 0).card : ℝ) := by
      exact_mod_cast h1.trans (Nat.add_le_add_left hham _)
    have h2' : (crossingCover G b₁ : ℝ) ≤ (crossingCover G b₂ : ℝ) +
        ((univ.filter fun v : V => row v k ≠ 0).card : ℝ) := by
      exact_mod_cast h2.trans (Nat.add_le_add_left hham _)
    change -(c k) ≤ _ ∧ _ ≤ c k
    dsimp [c]
    constructor <;> linarith
  -- Deviation threshold `a = (ξ / 8) * n`.
  set a : ℝ := (ξ / 8) * (n : ℝ)
  have ha_pos : 0 < a := by positivity
  -- Measurability of threshold/window counts and crossing covers.
  let countSet (S : Set ℝ) (g : κ → ℝ) : ℝ :=
    (@Finset.filter V (fun v => score g v ∈ S) (Classical.decPred _) univ).card
  have hmeas_count : ∀ (S : Set ℝ), MeasurableSet S → Measurable (countSet S) := by
    intro S hS
    have hsum : countSet S =
        fun g => ∑ v : V, S.indicator (fun _ => (1 : ℝ)) (score g v) := by
      ext g
      dsimp only [countSet]
      rw [card_filter, Nat.cast_sum]
      refine sum_congr rfl fun v _ => ?_
      by_cases hv : score g v ∈ S <;> simp [hv]
    rw [hsum]
    exact Finset.measurable_sum univ fun v _ =>
      (measurable_const.indicator hS).comp (measurable_score_fun row v)
  have hmeas_cc : ∀ t : ℝ,
      Measurable fun g : κ → ℝ => (crossingCover G (thresholdVec (score g) t) : ℝ) := by
    intro t
    have hfin : Measurable fun b : V → Bool => (crossingCover G b : ℝ) := measurable_of_finite _
    have hsc : Measurable fun g : κ → ℝ => score g :=
      measurable_pi_iff.mpr fun v => measurable_score_fun row v
    exact hfin.comp (measurable_thresholdVec hsc (fun _ => t) measurable_const)
  -- Construct `fL`, `fR`, `fW k`, `fC k`.
  let fL : (κ → ℝ) → ℝ := countSet (Iio (-T))
  let fR : (κ → ℝ) → ℝ := countSet (Ici T)
  let grid (k : ℕ) : ℝ := -T + (k : ℝ) * (2 * T / K)
  let fW (k : Fin K) : (κ → ℝ) → ℝ := countSet (Ico (grid k.val) (grid (k.val + 1)))
  let fC (k : Fin K) (g : κ → ℝ) : ℝ :=
    (crossingCover G (thresholdVec (score g) (grid k.val)) : ℝ)
  have hbd_count : ∀ (S : Set ℝ) (g : κ → ℝ), |countSet S g| ≤ (n : ℝ) := fun S g => by
    dsimp only [countSet]
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast card_filter_le univ (fun v => score g v ∈ S)
  have hdiff_count : ∀ (S : Set ℝ) (k : κ) (g : κ → ℝ) (u : ℝ),
      |countSet S (Function.update g k u) - countSet S g| ≤ c k := fun S k g u => by
    have h := hcard_change (· ∈ S) k g u
    convert h using 2
  have hbd_cc : ∀ (t : ℝ) (g : κ → ℝ),
      |(crossingCover G (thresholdVec (score g) t) : ℝ)| ≤ (n : ℝ) := fun t g => by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have hle : crossingCover G (thresholdVec (score g) t) ≤ (univ : Finset V).card :=
      crossingCover_le_card G fun _ _ => Or.inl (mem_univ _)
    exact_mod_cast hle
  -- Chebyshev bad-event sets.
  let mL : ℝ := ∫ g, fL g ∂(piGauss κ)
  let mR : ℝ := ∫ g, fR g ∂(piGauss κ)
  let mW (k : Fin K) : ℝ := ∫ g, fW k g ∂(piGauss κ)
  let mC (k : Fin K) : ℝ := ∫ g, fC k g ∂(piGauss κ)
  let badL : Set (κ → ℝ) := {g | mL + a ≤ fL g}
  let badR : Set (κ → ℝ) := {g | mR + a ≤ fR g}
  let badW (k : Fin K) : Set (κ → ℝ) := {g | mW k + a ≤ fW k g}
  let badC (k : Fin K) : Set (κ → ℝ) := {g | mC k + a ≤ fC k g}
  let pBad : ℝ := C * (n : ℝ) / a ^ 2
  have hmeasL : (piGauss κ).real badL ≤ pBad :=
    (measureReal_ge_mean_add_le_of_boundedDiff (hmeas_count _ measurableSet_Iio)
      (hbd_count _) hc_nonneg (hdiff_count _) ha_pos).trans
      (div_le_div_of_nonneg_right hc_sum (sq_nonneg a))
  have hmeasR : (piGauss κ).real badR ≤ pBad :=
    (measureReal_ge_mean_add_le_of_boundedDiff (hmeas_count _ measurableSet_Ici)
      (hbd_count _) hc_nonneg (hdiff_count _) ha_pos).trans
      (div_le_div_of_nonneg_right hc_sum (sq_nonneg a))
  have hmeasW : ∀ k : Fin K, (piGauss κ).real (badW k) ≤ pBad := fun k =>
    (measureReal_ge_mean_add_le_of_boundedDiff (hmeas_count _ measurableSet_Ico)
      (hbd_count _) hc_nonneg (hdiff_count _) ha_pos).trans
      (div_le_div_of_nonneg_right hc_sum (sq_nonneg a))
  have hmeasC : ∀ k : Fin K, (piGauss κ).real (badC k) ≤ pBad := fun k => by
    refine (measureReal_ge_mean_add_le_of_boundedDiff
      (hmeas_cc (grid k.val)) (hbd_cc (grid k.val)) hc_nonneg
      (hcc_diff (grid k.val)) ha_pos).trans ?_
    exact div_le_div_of_nonneg_right hc_sum (sq_nonneg a)
  let badAll : Set (κ → ℝ) :=
    badL ∪ badR ∪ (⋃ k : Fin K, badW k) ∪ (⋃ k : Fin K, badC k)
  have hp_lt_one : (piGauss κ).real badAll < 1 := by
    have hsub1 : (piGauss κ).real badAll ≤
        (piGauss κ).real badL + (piGauss κ).real badR +
          (∑ k : Fin K, (piGauss κ).real (badW k)) +
          (∑ k : Fin K, (piGauss κ).real (badC k)) := by
      calc (piGauss κ).real badAll
          ≤ (piGauss κ).real (badL ∪ badR ∪ ⋃ k, badW k) +
              (piGauss κ).real (⋃ k, badC k) := measureReal_union_le _ _
        _ ≤ (piGauss κ).real (badL ∪ badR) + (piGauss κ).real (⋃ k, badW k) +
              (piGauss κ).real (⋃ k, badC k) :=
            add_le_add (measureReal_union_le _ _) le_rfl
        _ ≤ (piGauss κ).real badL + (piGauss κ).real badR +
              (∑ k : Fin K, (piGauss κ).real (badW k)) +
              (∑ k : Fin K, (piGauss κ).real (badC k)) := by
            gcongr
            · exact measureReal_union_le _ _
            · exact measureReal_iUnion_fintype_le _
            · exact measureReal_iUnion_fintype_le _
    have hsum_bd : (piGauss κ).real badL + (piGauss κ).real badR +
        (∑ k : Fin K, (piGauss κ).real (badW k)) +
        (∑ k : Fin K, (piGauss κ).real (badC k)) ≤ (2 * (K : ℝ) + 2) * pBad := by
      have hWsum : ∑ k : Fin K, (piGauss κ).real (badW k) ≤ (K : ℝ) * pBad :=
        (sum_le_sum fun k _ => hmeasW k).trans (by simp [sum_const, nsmul_eq_mul])
      have hCsum : ∑ k : Fin K, (piGauss κ).real (badC k) ≤ (K : ℝ) * pBad :=
        (sum_le_sum fun k _ => hmeasC k).trans (by simp [sum_const, nsmul_eq_mul])
      linarith
    have htot_lt : (2 * (K : ℝ) + 2) * pBad < 1 := by
      have hval : (2 * (K : ℝ) + 2) * pBad =
          ((2 * (K : ℝ) + 2) * C / (ξ / 8) ^ 2) / (n : ℝ) := by
        simp only [pBad, a]; field_simp
      rw [hval, div_lt_one hn_pos]
      rwa [← hn_eq]
    exact (hsub1.trans hsum_bd).trans_lt htot_lt
  have hne : (badAllᶜ : Set (κ → ℝ)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at hempty
    have h1 : (piGauss κ).real badAll = 1 := by rw [hempty, probReal_univ]
    linarith
  obtain ⟨g, hg⟩ := hne
  have hgL : fL g < mL + a := lt_of_not_ge fun h => hg (Or.inl (Or.inl (Or.inl h)))
  have hgR : fR g < mR + a := lt_of_not_ge fun h => hg (Or.inl (Or.inl (Or.inr h)))
  have hgW : ∀ k : Fin K, fW k g < mW k + a := fun k =>
    lt_of_not_ge fun h => hg (Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨k, h⟩)))
  have hgC : ∀ k : Fin K, fC k g < mC k + a := fun k =>
    lt_of_not_ge fun h => hg (Or.inr (Set.mem_iUnion.mpr ⟨k, h⟩))
  -- Mean upper bounds from 1D standard Gaussian marginals.
  have hm_law : ∀ (S : Set ℝ) (hS : MeasurableSet S),
      ∫ x, countSet S x ∂(piGauss κ) = (n : ℝ) * (gaussianReal 0 1).real S := fun S hS => by
    have hsum : countSet S = fun x => ∑ v : V, S.indicator (fun _ => (1 : ℝ)) (score x v) := by
      ext x; dsimp only [countSet]; rw [card_filter, Nat.cast_sum]
      refine sum_congr rfl fun v _ => by by_cases hv : score x v ∈ S <;> simp [hv]
    have hint_v : ∀ v : V, Integrable (fun x : κ → ℝ =>
        S.indicator (fun _ => (1 : ℝ)) (score x v)) (piGauss κ) := fun v =>
      Integrable.of_bound
        ((measurable_const.indicator hS).comp (measurable_score_fun row v)).aestronglyMeasurable
        1 (ae_of_all _ fun x => by by_cases hv : score x v ∈ S <;> simp [hv])
    have hint_sum : ∀ T : Finset V,
        ∫ x, ∑ v ∈ T, S.indicator (fun _ => (1 : ℝ)) (score x v) ∂(piGauss κ) =
          ∑ v ∈ T, ∫ x, S.indicator (fun _ => (1 : ℝ)) (score x v) ∂(piGauss κ) := by
      intro T
      induction T using Finset.induction_on with
      | empty => simp
      | insert a s ha ih =>
        have his : Integrable (fun x => ∑ v ∈ s, S.indicator (fun _ => (1 : ℝ)) (score x v))
            (piGauss κ) := by
          clear ih ha
          induction s using Finset.induction_on with
          | empty => exact integrable_zero _ _ _
          | insert b t hb ih' =>
            simp_rw [sum_insert hb]; exact (hint_v b).add ih'
        simp_rw [sum_insert ha]
        rw [integral_add (hint_v a) his, ih]
    rw [hsum, hint_sum univ]
    have hterm : ∀ v : V,
        ∫ x, S.indicator (fun _ => (1 : ℝ)) (score x v) ∂(piGauss κ) =
          (gaussianReal 0 1).real S := fun v => by
      have hcomp : (fun x => S.indicator (fun _ => (1 : ℝ)) (score x v)) =
          ((fun x => score x v) ⁻¹' S).indicator (fun _ => (1 : ℝ)) := by
        ext x; by_cases hx : score x v ∈ S <;> simp [hx]
      rw [hcomp, integral_indicator ((measurable_score_fun row v) hS), integral_const,
        smul_eq_mul, mul_one, measureReal_restrict_apply_univ]
      have hmap := gaussianReal_dotProduct_law (row v) (hunit v)
      rw [measureReal_def, measureReal_def, ← hmap,
        Measure.map_apply (measurable_score_fun row v) hS]
    simp [hterm, sum_const, nsmul_eq_mul, n]
  have hmL_le : mL ≤ (1 / T ^ 2) * (n : ℝ) := by
    have hlaw := hm_law (Iio (-T)) measurableSet_Iio
    have htail : (gaussianReal 0 1).real (Iio (-T)) ≤ 1 / T ^ 2 := by
      have hsub : Iio (-T) ⊆ {x : ℝ | T ≤ |x - 0|} := fun x hx => by
        simp only [Set.mem_Iio] at hx
        change T ≤ |x - 0|; rw [sub_zero, le_abs]
        right; linarith
      have hm := (measure_mono hsub).trans (gaussianReal_meas_ge_le 0 1 hT)
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by simpa using hm)
    have hmeq : mL = (n : ℝ) * (gaussianReal 0 1).real (Iio (-T)) := hlaw
    nlinarith [hn_pos]
  have hmR_le : mR ≤ (1 / T ^ 2) * (n : ℝ) := by
    have hlaw := hm_law (Ici T) measurableSet_Ici
    have htail : (gaussianReal 0 1).real (Ici T) ≤ 1 / T ^ 2 := by
      have hsub : Ici T ⊆ {x : ℝ | T ≤ |x - 0|} := fun x hx => by
        simp only [Set.mem_Ici] at hx
        change T ≤ |x - 0|; rw [sub_zero, le_abs]
        left; exact hx
      have hm := (measure_mono hsub).trans (gaussianReal_meas_ge_le 0 1 hT)
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal (by positivity) (by simpa using hm)
    have hmeq : mR = (n : ℝ) * (gaussianReal 0 1).real (Ici T) := hlaw
    nlinarith [hn_pos]
  have hmW_le : ∀ k : Fin K, mW k ≤ ((2 * T / K) / √(2 * π)) * (n : ℝ) := fun k => by
    have hlaw := hm_law (Ico (grid k.val) (grid (k.val + 1))) measurableSet_Ico
    have hstep : grid (k.val + 1) - grid k.val = 2 * T / K := by
      simp only [grid, Nat.cast_add, Nat.cast_one]; ring
    have hwin : (gaussianReal 0 1).real (Ico (grid k.val) (grid (k.val + 1))) ≤
        (2 * T / K) / √(2 * π) := by
      rw [measureReal_def]
      refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
      refine (gaussianReal_le_ofReal_mul_volume 0 one_ne_zero _).trans ?_
      rw [Real.volume_Ico, hstep, NNReal.coe_one, mul_one,
        ← ENNReal.ofReal_mul (by positivity), inv_mul_eq_div]
    have hmeq : mW k = (n : ℝ) *
        (gaussianReal 0 1).real (Ico (grid k.val) (grid (k.val + 1))) := hlaw
    nlinarith [hn_pos]
  have hmC_le : ∀ k : Fin K, mC k ≤ γ * (n : ℝ) := fun k => by
    have h := hexp (grid k.val)
    rw [hn_eq] at h; exact h
  let B : ℝ := (γ + 3 * ξ / 4) * (n : ℝ)
  have hB_nonneg : 0 ≤ B := by positivity
  let M : ℕ := Nat.floor B
  have hM_real : (M : ℝ) ≤ B := Nat.floor_le hB_nonneg
  have hγn : 0 ≤ γ * (n : ℝ) := mul_nonneg hγ hn_pos.le
  have hT_bd_n : (1 / T ^ 2) * (n : ℝ) ≤ (ξ / 4) * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hT_bd hn_pos.le
  have hM_L : (univ.filter fun v => score g v < -T).card ≤ M := by
    refine Nat.le_floor ?_
    have heq : ((univ.filter fun v => score g v < -T).card : ℝ) = fL g :=
      congrArg (fun c : ℕ => (c : ℝ)) (congrArg Finset.card (by ext v; simp))
    rw [heq]
    linarith [hgL, hmL_le, hT_bd_n, hγn, show a = (ξ / 8) * n from rfl,
      show B = (γ + 3 * ξ / 4) * n from rfl]
  have hM_R : (univ.filter fun v => T ≤ score g v).card ≤ M := by
    refine Nat.le_floor ?_
    have heq : ((univ.filter fun v => T ≤ score g v).card : ℝ) = fR g :=
      congrArg (fun c : ℕ => (c : ℝ)) (congrArg Finset.card (by ext v; simp))
    rw [heq]
    linarith [hgR, hmR_le, hT_bd_n, hγn, show a = (ξ / 8) * n from rfl,
      show B = (γ + 3 * ξ / 4) * n from rfl]
  have hM_grid : ∀ k : Fin K,
      let tk : ℝ := -T + (k.val : ℝ) * (2 * T / K)
      let tk1 : ℝ := -T + ((k.val : ℝ) + 1) * (2 * T / K)
      crossingCover G (thresholdVec (score g) tk) +
        (univ.filter fun v => tk ≤ score g v ∧ score g v < tk1).card ≤ M := by
    intro k tk tk1
    refine Nat.le_floor ?_
    push_cast
    have h1 := hgC k
    have h2 := hmC_le k
    have h3' := hgW k
    have h4 := hmW_le k
    have h5 : (2 * T / K) / √(2 * π) * (n : ℝ) ≤ (ξ / 4) * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hK_bd hn_pos.le
    have h6 : grid (k.val + 1) = tk1 := by
      simp only [grid, tk1, Nat.cast_add, Nat.cast_one]
    have h7 : grid k.val = tk := rfl
    have heqC : (crossingCover G (thresholdVec (score g) tk) : ℝ) = fC k g := rfl
    have heqW : ((univ.filter fun v => tk ≤ score g v ∧ score g v < tk1).card : ℝ) = fW k g :=
      congrArg (fun m : ℕ => (m : ℝ)) (congrArg Finset.card (by
        ext v; simp only [mem_filter, h6, h7, Set.mem_Ico]))
    dsimp [B]
    have ha_eq : a = (ξ / 8) * (n : ℝ) := rfl
    linarith [h1, h2, h3', h4, h5, heqC, heqW, ha_eq]
  let leq : V → V → Bool := fun u v => decide (score g u ≤ score g v)
  let vs : List V := (univ : Finset V).toList.mergeSort leq
  have hvs_mem : ∀ v : V, v ∈ vs := fun v =>
    (List.mem_mergeSort).mpr (mem_toList.mpr (mem_univ v))
  have hvs_sort : vs.Pairwise fun u v => score g u ≤ score g v := by
    have hp := List.pairwise_mergeSort (l := (univ : Finset V).toList) (le := leq)
      (fun a b c hab hbc => by
        simp only [leq, decide_eq_true_eq] at hab hbc ⊢; exact hab.trans hbc)
      (fun a b => by
        simp only [leq, Bool.or_eq_true, decide_eq_true_eq]; exact le_total _ _)
    exact hp.imp fun h => by simpa [leq] using h
  have hpref := prefix_crossingCover_le_grid G (score g) vs hvs_mem hvs_sort hT hK M
    hM_L hM_R hM_grid
  obtain ⟨lay, hlay⟩ := exists_width_le_max_crossingCover G h3 vs hvs_mem M hpref
  refine ⟨lay, hlay.trans ?_⟩
  rw [hn_eq] at hN_six ⊢
  dsimp [B] at hM_real
  linarith [hM_real, hN_six]

end MainReduction

end Cslib.Circuits.Frontier.CrossingCover
