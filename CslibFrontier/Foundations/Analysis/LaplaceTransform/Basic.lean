/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, a new file `Mathlib/Analysis/LaplaceTransform.lean`)

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# The one-sided Laplace transform

For `f : ℝ → E` with values in a complex normed space, the one-sided **Laplace transform** is
`laplace f s = ∫ t in Ioi 0, exp (-s t) • f t` for `s : ℂ` (`laplace`). It converges at `s`
(`LaplaceConvergent f s`) when this integrand is integrable on `(0, ∞)`, i.e. when the integral
converges absolutely; at other `s` the Bochner integral, and so `laplace f s`, is `0`. Only the
values of `f` on `(0, ∞)` are used; the value `f 0` plays a role only in the derivative rule
(`CslibFrontier/Foundations/Analysis/LaplaceTransform/Deriv.lean`).

The names and statement shapes follow the open Mathlib PR mathlib4#40582 (`laplace`,
`LaplaceConvergent`, `laplaceConvergent_of_isBigO_exp`, `laplace_cexp_smul`), so that these
definitions can be replaced by Mathlib's if it lands; nothing is copied from it.

## Holomorphy

If `f` is a.e.-strongly measurable on `(0, ∞)` (for instance locally integrable on `[0, ∞)`) and
of exponential order `σ`, i.e. `‖f t‖ ≤ M exp (σ t)` for `t > 0`, then `laplace f` converges on the
open half-plane `re s > σ` (`laplaceConvergent_of_norm_le_exp`) and is holomorphic there
(`differentiableOn_laplace`), with derivative `-laplace (t • f)` (`hasDerivAt_laplace`).

The proof differentiates under the integral sign with Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_deriv_le`, dominating `t exp (-s t) f t` on a small disc
around `s` by `exp (-ε t)` for some `ε > 0`. Two alternatives were rejected. The substitution
`t = -log x` turns `laplace f s` into the Mellin transform of `x ↦ f (-log x)` at `s`, but the
holomorphy theorem of `Mathlib.Analysis.MellinTransform` is stated with `IsBigO` hypotheses at `0`
and `∞` on `(0, ∞)`, and transporting the exponential-order bound, local integrability and the
derivative through the change of variables costs more than the direct proof.
`CslibFrontier.Foundations.Analysis.Calculus.ParametricIntegralExp` requires integrability of
`exp (c ‖φ t‖) ‖g t‖` for *every* `c`, which fails for every nonzero function of exponential
order here, so it does not apply.

## Main definitions

* `LaplaceConvergent f s`: `t ↦ exp (-s t) • f t` is integrable on `(0, ∞)`.
* `laplace f s = ∫ t in Ioi 0, exp (-s t) • f t`.

## Main results

* Linearity: `laplace_add`, `laplace_sub`, `laplace_neg`, `laplace_const_smul`,
  `laplace_const_mul`, `laplace_mul_const`, `laplace_sum`,
  `ContinuousLinearMap.laplace_comp`, `laplace_apply`.
* `LaplaceConvergent.of_re_le`: convergence at `s` gives convergence on `re s' ≥ re s`.
* `laplaceConvergent_of_norm_le_exp`, `laplaceConvergent_of_isBigO_exp`: convergence for
  exponential order `σ` on `re s > σ`.
* `hasDerivAt_laplace`, `differentiableOn_laplace`: holomorphy on `re s > σ`, with
  `deriv (laplace f) s = -laplace (t • f) s`.
* `laplace_cexp_smul`: the frequency-shift rule `laplace (exp (a t) • f) s = laplace f (s - a)`.
* `laplace_cexp`, `laplace_mul_cexp`: `laplace (exp (a t)) s = 1 / (s - a)` and
  `laplace (t exp (a t)) s = 1 / (s - a) ^ 2` for `re s > re a`.

## References

* D. V. Widder, *The Laplace Transform*, Princeton University Press, 1941, Chapter II
  (convergence; analyticity and the derivative of the transform). Locators to be checked.
-/

public section

open MeasureTheory Set Filter Topology Asymptotics

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- The one-sided Laplace transform of `f` **converges** at `s : ℂ`: the integrand
`t ↦ exp (-s t) • f t` is integrable on `(0, ∞)`. -/
@[expose] def LaplaceConvergent (f : ℝ → E) (s : ℂ) : Prop :=
  IntegrableOn (fun t : ℝ => Complex.exp (-s * t) • f t) (Ioi 0)

/-- The one-sided **Laplace transform** `∫ t in Ioi 0, exp (-s t) • f t`. It is `0` where the
integral does not converge (`LaplaceConvergent`). -/
@[expose] def laplace (f : ℝ → E) (s : ℂ) : E :=
  ∫ t : ℝ in Ioi 0, Complex.exp (-s * t) • f t

variable {f g : ℝ → E} {s : ℂ}

theorem laplaceConvergent_iff : LaplaceConvergent f s ↔
    IntegrableOn (fun t : ℝ => Complex.exp (-s * t) • f t) (Ioi 0) := Iff.rfl

theorem laplace_eq (f : ℝ → E) (s : ℂ) :
    laplace f s = ∫ t : ℝ in Ioi 0, Complex.exp (-s * t) • f t := rfl

/-- The Laplace transform depends only on the values of `f` on `(0, ∞)`. -/
theorem laplace_congr (h : EqOn f g (Ioi 0)) : laplace f s = laplace g s :=
  setIntegral_congr_fun measurableSet_Ioi fun t ht => by simp [h ht]

/-- Convergence depends only on the values of `f` on `(0, ∞)`. -/
theorem LaplaceConvergent.congr (hf : LaplaceConvergent f s) (h : EqOn f g (Ioi 0)) :
    LaplaceConvergent g s :=
  hf.congr_fun (fun t ht => by simp [h ht]) measurableSet_Ioi

/-! ### Linearity -/

theorem LaplaceConvergent.add (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    LaplaceConvergent (fun t => f t + g t) s := by
  simp only [LaplaceConvergent, smul_add] at *
  exact hf.add hg

theorem LaplaceConvergent.neg (hf : LaplaceConvergent f s) :
    LaplaceConvergent (fun t => -f t) s := by
  simp only [LaplaceConvergent, smul_neg] at *
  exact hf.neg

theorem LaplaceConvergent.sub (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    LaplaceConvergent (fun t => f t - g t) s := by
  simp only [LaplaceConvergent, smul_sub] at *
  exact hf.sub hg

theorem LaplaceConvergent.const_smul (hf : LaplaceConvergent f s) (c : ℂ) :
    LaplaceConvergent (fun t => c • f t) s := by
  simp only [LaplaceConvergent] at *
  simp_rw [smul_comm _ c]
  exact hf.smul c

theorem laplace_add (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    laplace (fun t => f t + g t) s = laplace f s + laplace g s := by
  unfold laplace
  simp_rw [smul_add]
  exact integral_add hf hg

theorem laplace_neg (f : ℝ → E) (s : ℂ) : laplace (fun t => -f t) s = -laplace f s := by
  unfold laplace
  simp_rw [smul_neg]
  exact integral_neg _

theorem laplace_sub (hf : LaplaceConvergent f s) (hg : LaplaceConvergent g s) :
    laplace (fun t => f t - g t) s = laplace f s - laplace g s := by
  unfold laplace
  simp_rw [smul_sub]
  exact integral_sub hf hg

theorem laplace_const_smul (f : ℝ → E) (s c : ℂ) :
    laplace (fun t => c • f t) s = c • laplace f s := by
  simp_rw [laplace, smul_comm _ c]
  exact integral_smul c _

theorem LaplaceConvergent.const_mul {f : ℝ → ℂ} (hf : LaplaceConvergent f s) (c : ℂ) :
    LaplaceConvergent (fun t => c * f t) s :=
  hf.const_smul c

theorem LaplaceConvergent.mul_const {f : ℝ → ℂ} (hf : LaplaceConvergent f s) (c : ℂ) :
    LaplaceConvergent (fun t => f t * c) s := by
  simp_rw [mul_comm _ c]
  exact hf.const_mul c

theorem laplace_const_mul (f : ℝ → ℂ) (s c : ℂ) :
    laplace (fun t => c * f t) s = c * laplace f s :=
  laplace_const_smul f s c

theorem laplace_mul_const (f : ℝ → ℂ) (s c : ℂ) :
    laplace (fun t => f t * c) s = laplace f s * c := by
  simp_rw [mul_comm _ c]
  exact laplace_const_mul f s c

theorem LaplaceConvergent.sum {ι : Type*} {f : ι → ℝ → E} {u : Finset ι}
    (hf : ∀ i ∈ u, LaplaceConvergent (f i) s) : LaplaceConvergent (fun t => ∑ i ∈ u, f i t) s := by
  unfold LaplaceConvergent at *
  simp_rw [Finset.smul_sum]
  exact integrable_finsetSum u hf

theorem laplace_sum {ι : Type*} {f : ι → ℝ → E} {u : Finset ι}
    (hf : ∀ i ∈ u, LaplaceConvergent (f i) s) :
    laplace (fun t => ∑ i ∈ u, f i t) s = ∑ i ∈ u, laplace (f i) s := by
  unfold laplace
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum u hf

/-- A continuous linear map commutes with the Laplace transform where it converges. -/
theorem ContinuousLinearMap.laplaceConvergent_comp (L : E →L[ℂ] F) (hf : LaplaceConvergent f s) :
    LaplaceConvergent (fun t => L (f t)) s := by
  have h := L.integrable_comp hf
  simp only [map_smul] at h
  exact h

/-- A continuous linear map commutes with the Laplace transform where it converges. -/
theorem ContinuousLinearMap.laplace_comp [CompleteSpace E] [CompleteSpace F] (L : E →L[ℂ] F)
    (hf : LaplaceConvergent f s) : laplace (fun t => L (f t)) s = L (laplace f s) := by
  have h := L.integral_comp_comm hf
  simp only [map_smul] at h
  unfold laplace
  exact h

/-- The Laplace transform of a function with values in a finite product is computed
coordinatewise. -/
theorem laplace_apply {ι : Type*} [Fintype ι] [CompleteSpace E] {f : ℝ → ι → E}
    (hf : LaplaceConvergent f s) (i : ι) : laplace f s i = laplace (fun t => f t i) s :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).laplace_comp hf).symm

/-- Coordinates of a convergent Laplace transform converge. -/
theorem LaplaceConvergent.apply {ι : Type*} [Fintype ι] {f : ℝ → ι → E}
    (hf : LaplaceConvergent f s) (i : ι) : LaplaceConvergent (fun t => f t i) s :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => E) i).laplaceConvergent_comp hf

/-- A function into a finite product converges iff all its coordinates do. -/
theorem laplaceConvergent_pi_iff {ι : Type*} [Fintype ι] {f : ℝ → ι → E} :
    LaplaceConvergent f s ↔ ∀ i, LaplaceConvergent (fun t => f t i) s := by
  exact integrable_pi_iff (f := fun (t : ℝ) i => Complex.exp (-s * t) • f t i)

/-! ### Convergence on half-planes -/

private theorem norm_cexp_neg_mul (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-s * t)‖ = Real.exp (-s.re * t) := by
  rw [Complex.norm_exp]
  simp

/-- Measurability of `f` on `(0, ∞)` follows from convergence at one point. -/
theorem LaplaceConvergent.aestronglyMeasurable (hf : LaplaceConvergent f s) :
    AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
  have h := (Continuous.aestronglyMeasurable (μ := volume.restrict (Ioi (0 : ℝ)))
    (f := fun t : ℝ => Complex.exp (s * t)) (by fun_prop)).smul hf.1
  refine h.congr (ae_of_all _ fun t => ?_)
  change Complex.exp (s * t) • Complex.exp (-s * t) • f t = f t
  rw [smul_smul, ← Complex.exp_add, show s * t + -s * t = 0 by ring, Complex.exp_zero, one_smul]

/-- **Convergence on a half-plane.** If the Laplace transform of `f` converges at `s`, it
converges at every `s'` with `re s ≤ re s'`. -/
theorem LaplaceConvergent.of_re_le (hf : LaplaceConvergent f s) {s' : ℂ} (h : s.re ≤ s'.re) :
    LaplaceConvergent f s' := by
  refine Integrable.mono' hf.norm ?_ ((ae_restrict_iff' measurableSet_Ioi).2 <|
    ae_of_all _ fun t (ht : 0 < t) => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).smul
      (LaplaceConvergent.aestronglyMeasurable hf)
  · rw [norm_smul, norm_smul, norm_cexp_neg_mul, norm_cexp_neg_mul]
    gcongr

/-- **Convergence for exponential order.** If `f` is a.e.-strongly measurable on `(0, ∞)` and
`‖f t‖ ≤ M exp (σ t)` for `t > 0`, the Laplace transform of `f` converges at every `s` with
`σ < re s`. -/
theorem laplaceConvergent_of_norm_le_exp {M σ : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hM : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ M * Real.exp (σ * t)) (hs : σ < s.re) :
    LaplaceConvergent f s := by
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := σ - s.re) (by linarith) 0).const_mul M)
    ((Continuous.aestronglyMeasurable (by fun_prop)).smul hf)
    ((ae_restrict_iff' measurableSet_Ioi).2 <| ae_of_all _ fun t ht => ?_)
  rw [norm_smul, norm_cexp_neg_mul]
  calc Real.exp (-s.re * t) * ‖f t‖ ≤ Real.exp (-s.re * t) * (M * Real.exp (σ * t)) := by
        gcongr
        exact hM t ht
    _ = M * Real.exp ((σ - s.re) * t) := by
        rw [mul_left_comm, ← Real.exp_add]
        ring_nf

/-- **Convergence for exponential order, asymptotic form.** If `f` is locally integrable on
`[0, ∞)` and `f = O(exp (σ t))` as `t → ∞`, the Laplace transform of `f` converges at every `s`
with `σ < re s`. -/
theorem laplaceConvergent_of_isBigO_exp {σ : ℝ} (hf : LocallyIntegrableOn f (Ici 0))
    (ho : f =O[atTop] fun t => Real.exp (σ * t)) (hs : σ < s.re) : LaplaceConvergent f s := by
  have hloc : LocallyIntegrableOn (fun t : ℝ => Complex.exp (-s * t) • f t) (Ici 0) :=
    hf.continuousOn_smul isClosed_Ici.isLocallyClosed (by fun_prop)
  have ho' : (fun t : ℝ => Complex.exp (-s * t) • f t) =O[atTop]
      fun t => Real.exp ((σ - s.re) * t) := by
    obtain ⟨c, hc⟩ := ho.bound
    refine IsBigO.of_bound c ?_
    filter_upwards [hc] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le] at ht
    rw [norm_smul, norm_cexp_neg_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
    calc Real.exp (-s.re * t) * ‖f t‖ ≤ Real.exp (-s.re * t) * (c * Real.exp (σ * t)) := by
          gcongr
      _ = c * Real.exp ((σ - s.re) * t) := by
          rw [mul_left_comm, ← Real.exp_add]
          ring_nf
  exact (hloc.integrableOn_of_isBigO_atTop ho' ⟨Ioi 0, Ioi_mem_atTop 0,
    integrableOn_exp_mul_Ioi (by linarith) 0⟩).mono_set Ioi_subset_Ici_self

/-! ### Holomorphy -/

/-- `t ≤ exp (ε t) / ε` for `ε > 0`. -/
private theorem le_exp_mul_div {ε : ℝ} (hε : 0 < ε) (t : ℝ) : t ≤ Real.exp (ε * t) / ε := by
  rw [le_div_iff₀ hε]
  linarith [Real.add_one_le_exp (ε * t)]

/-- **The Laplace transform is holomorphic on the half-plane of exponential order**, with
derivative `-laplace (t • f)`. If `f` is a.e.-strongly measurable on `(0, ∞)` and
`‖f t‖ ≤ M exp (σ t)` for `t > 0`, then at every `s` with `σ < re s` the Laplace transform of
`f` has complex derivative `-laplace (fun t => (t : ℂ) • f t) s`, and the Laplace transform of
`t • f` converges at `s`. -/
theorem hasDerivAt_laplace {M σ : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hM : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ M * Real.exp (σ * t)) (hs : σ < s.re) :
    HasDerivAt (laplace f) (-laplace (fun t => (t : ℂ) • f t) s) s := by
  set ε := (s.re - σ) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hM0 : 0 ≤ M := by
    have h := (norm_nonneg _).trans (hM 1 (by norm_num : (0 : ℝ) < 1))
    exact nonneg_of_mul_nonneg_left h (Real.exp_pos _)
  have hball : ∀ z ∈ Metric.ball s ε, σ + ε < z.re := fun z hz => by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 := (Complex.abs_re_le_norm (z - s)).trans_lt hz
    rw [Complex.sub_re, abs_lt] at h1
    rw [hε_def] at h1 ⊢
    linarith [h1.1]
  set F : ℂ → ℝ → E := fun z t => Complex.exp (-z * t) • f t
  set F' : ℂ → ℝ → E := fun z t => (-(t : ℂ) * Complex.exp (-z * t)) • f t
  set bound : ℝ → ℝ := fun t => M / (ε / 2) * Real.exp (-(ε / 2) * t)
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := fun z =>
    (Continuous.aestronglyMeasurable (by fun_prop)).smul hf
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
    (F := F) (F' := F') (x₀ := s) (bound := bound) (Metric.ball_mem_nhds s hε)
    (Eventually.of_forall hmeas)
    (laplaceConvergent_of_norm_le_exp hf hM hs)
    ((Continuous.aestronglyMeasurable (by fun_prop)).smul hf)
    ((ae_restrict_iff' measurableSet_Ioi).2 <| ae_of_all _ fun t (ht : 0 < t) z hz => ?_)
    ((integrableOn_exp_mul_Ioi (by linarith) 0).const_mul _)
    (ae_of_all _ fun t z _ => ?_)
  · have e : -laplace (fun t => (t : ℂ) • f t) s = ∫ t in Ioi 0, F' s t := by
      rw [laplace, ← integral_neg]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp only [F', smul_smul, neg_mul, neg_smul]
      ring_nf
    rw [e]
    exact h.2
  · have hz := hball z hz
    simp only [F', bound, norm_smul, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht, norm_cexp_neg_mul]
    have h1 := le_exp_mul_div (ε := ε / 2) (by linarith) t
    have h2 : Real.exp (-z.re * t) ≤ Real.exp (-(σ + ε) * t) :=
      Real.exp_le_exp.2 (by nlinarith)
    have h3 := hM t ht
    calc t * Real.exp (-z.re * t) * ‖f t‖
        ≤ (Real.exp (ε / 2 * t) / (ε / 2)) * Real.exp (-(σ + ε) * t) *
            (M * Real.exp (σ * t)) :=
          mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) h3 (norm_nonneg _)
            (by positivity)
      _ = M / (ε / 2) * Real.exp (-(ε / 2) * t) := by
          have e : Real.exp (-(ε / 2) * t) =
              Real.exp (ε / 2 * t) * Real.exp (-(σ + ε) * t) * Real.exp (σ * t) := by
            rw [← Real.exp_add, ← Real.exp_add]
            ring_nf
          rw [e]
          ring
  · have hd : HasDerivAt (fun w : ℂ => Complex.exp (-w * t)) (-(t : ℂ) * Complex.exp (-z * t)) z :=
      by simpa [mul_comm] using ((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp
    exact hd.smul_const (f t)

/-- **The Laplace transform is holomorphic on the half-plane of exponential order.** If `f` is
a.e.-strongly measurable on `(0, ∞)` and `‖f t‖ ≤ M exp (σ t)` for `t > 0`, the Laplace transform
of `f` is complex differentiable on the open half-plane `re s > σ`. -/
theorem differentiableOn_laplace {M σ : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hM : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ M * Real.exp (σ * t)) :
    DifferentiableOn ℂ (laplace f) {s | σ < s.re} := fun _ hs =>
  (hasDerivAt_laplace hf hM hs).differentiableAt.differentiableWithinAt

/-- The derivative of the Laplace transform on the half-plane of exponential order is
`deriv (laplace f) s = -laplace (fun t => (t : ℂ) • f t) s`. -/
theorem deriv_laplace {M σ : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)))
    (hM : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ M * Real.exp (σ * t)) (hs : σ < s.re) :
    deriv (laplace f) s = -laplace (fun t => (t : ℂ) • f t) s :=
  (hasDerivAt_laplace hf hM hs).deriv

/-! ### The frequency-shift rule -/

private theorem cexp_smul_cexp_smul (a s : ℂ) (t : ℝ) (v : E) :
    Complex.exp (-s * t) • Complex.exp (a * t) • v = Complex.exp (-(s - a) * t) • v := by
  rw [smul_smul, ← Complex.exp_add]
  ring_nf

/-- Convergence of the frequency-shifted transform: `exp (a t) • f t` converges at `s` iff `f`
converges at `s - a`. -/
theorem laplaceConvergent_cexp_smul_iff (a : ℂ) :
    LaplaceConvergent (fun t => Complex.exp (a * t) • f t) s ↔ LaplaceConvergent f (s - a) := by
  simp only [LaplaceConvergent, cexp_smul_cexp_smul]

/-- **The frequency-shift rule** `laplace (fun t => exp (a t) • f t) s = laplace f (s - a)`, for
all `a s : ℂ` (both sides are `0` where they do not converge). -/
theorem laplace_cexp_smul (f : ℝ → E) (a s : ℂ) :
    laplace (fun t => Complex.exp (a * t) • f t) s = laplace f (s - a) := by
  simp only [laplace, cexp_smul_cexp_smul]

/-! ### Basic transforms -/

/-- The exponential `exp (a t)` has a convergent Laplace transform on `re s > re a`. -/
theorem laplaceConvergent_cexp {a : ℂ} (hs : a.re < s.re) :
    LaplaceConvergent (fun t : ℝ => Complex.exp (a * t)) s := by
  have h := integrableOn_exp_mul_complex_Ioi (a := a - s) (by simpa using hs) 0
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  rw [smul_eq_mul, ← Complex.exp_add]
  ring_nf

/-- **The transform of an exponential**: `laplace (fun t => exp (a t)) s = 1 / (s - a)` on
`re s > re a`. -/
theorem laplace_cexp {a : ℂ} (hs : a.re < s.re) :
    laplace (fun t : ℝ => Complex.exp (a * t)) s = 1 / (s - a) := by
  have h := integral_exp_mul_complex_Ioi (a := a - s) (by simpa using hs) 0
  have e : laplace (fun t : ℝ => Complex.exp (a * t)) s =
      ∫ t : ℝ in Ioi 0, Complex.exp ((a - s) * t) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [smul_eq_mul, ← Complex.exp_add]
    ring_nf
  rw [e, h]
  have hne : a - s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp at this
    linarith
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [neg_div, ← div_neg, neg_sub]

/-- The transform of `t exp (a t)` converges on `re s > re a`. -/
theorem laplaceConvergent_mul_cexp {a : ℂ} (hs : a.re < s.re) :
    LaplaceConvergent (fun t : ℝ => (t : ℂ) * Complex.exp (a * t)) s := by
  obtain ⟨c, hc1, hc2⟩ := exists_between hs
  have hle : ∀ t ∈ Ioi (0 : ℝ), ‖(t : ℂ) * Complex.exp (a * t)‖ ≤
      1 / (c - a.re) * Real.exp (c * t) := fun t (ht : 0 < t) => by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, Complex.norm_exp]
    have h1 := le_exp_mul_div (ε := c - a.re) (by linarith) t
    calc t * Real.exp (a * t).re ≤ Real.exp ((c - a.re) * t) / (c - a.re) *
          Real.exp (a.re * t) := by
          gcongr
          · simp
      _ = 1 / (c - a.re) * Real.exp (c * t) := by
          rw [div_mul_eq_mul_div, ← Real.exp_add, one_div_mul_eq_div]
          ring_nf
  exact laplaceConvergent_of_norm_le_exp (Continuous.aestronglyMeasurable (by fun_prop)) hle hc2

/-- **The transform of `t exp (a t)`**: `laplace (fun t => t exp (a t)) s = 1 / (s - a) ^ 2` on
`re s > re a`. It is computed from `laplace_cexp` by the derivative rule `hasDerivAt_laplace`. -/
theorem laplace_mul_cexp {a : ℂ} (hs : a.re < s.re) :
    laplace (fun t : ℝ => (t : ℂ) * Complex.exp (a * t)) s = 1 / (s - a) ^ 2 := by
  have hle : ∀ t ∈ Ioi (0 : ℝ), ‖Complex.exp (a * t)‖ ≤ 1 * Real.exp (a.re * t) :=
    fun t _ => by rw [one_mul, Complex.norm_exp]; simp
  have h1 := hasDerivAt_laplace (Continuous.aestronglyMeasurable (by fun_prop)) hle hs
  have hne : s - a ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0
    simp at this
    linarith
  have h2 : HasDerivAt (fun z : ℂ => 1 / (z - a)) (-1 / (s - a) ^ 2) s := by
    convert (hasDerivAt_const s (1 : ℂ)).div ((hasDerivAt_id s).sub_const a) hne using 1
    · funext z
      simp
    · simp
  have heq : laplace (fun t : ℝ => Complex.exp (a * t)) =ᶠ[𝓝 s] fun z => 1 / (z - a) := by
    have ho : IsOpen {z : ℂ | a.re < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [ho.mem_nhds hs] with z hz using laplace_cexp hz
  have h3 := (h1.congr_of_eventuallyEq heq.symm).unique h2
  simp only [smul_eq_mul] at h3
  rw [neg_div] at h3
  exact neg_injective h3

end
