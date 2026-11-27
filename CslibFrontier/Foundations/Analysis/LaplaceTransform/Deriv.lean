/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, with `Mathlib/Analysis/LaplaceTransform.lean`)

public import CslibFrontier.Foundations.Analysis.LaplaceTransform.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The derivative rule for the Laplace transform

If `f : ℝ → E` is continuous from the right at `0`, has derivative `f' t` at every `t > 0`, `f`
is of exponential order `σ` and `f'` of exponential order `σ'` on `(0, ∞)` (with independent
constants), then at every `s` with `σ < re s` and `σ' < re s`
`laplace f' s = s • laplace f s - f 0` (`laplace_deriv`).

**Endpoint convention.** The transform integrates over `(0, ∞)`, so `f` and `f'` matter only
there; `f 0` enters through right-continuity at `0`: it is the right limit `f (0⁺)`. The value
`f' 0` is never used, and no derivative at `0` is assumed. This is the convention of the
`0⁺`-transform; a jump of `f` at `0` (a distribution with a Dirac part) is out of scope.

## Main results

* `laplaceConvergent_deriv`: the transform of `f'` converges on `re s > σ'`.
* `laplace_deriv`: `laplace f' s = s • laplace f s - f 0` on `re s > max σ σ'`.

## References

* [Widder1941], Chapter II, §2, Theorem 2.1 and its proof, pp. 38–39: if `α` is of bounded
  variation on every `[0, R]` and `α(t) = O(e^{γt})`, then for `re s > γ`
  `∫₀^∞ e^{-st} dα(t) = s ∫₀^∞ e^{-st} α(t) dt - α(0)`; Theorem 2.3a, p. 41, gives the same
  identity wherever the left side converges with `re s > 0`. Compare `laplace_deriv` with
  `α = f`: when `f` is right-continuous at `0` and differentiable on `(0, ∞)` with `f'` locally
  integrable, the Stieltjes integral is `laplace f' s`. Widder's left side may converge
  conditionally and needs no bound on `f'`; here `laplace f' s` is an absolutely convergent
  Lebesgue integral, which is why `f'` has its own exponential-order bound.
* S. Boyd, *EE263: Introduction to Linear Dynamical Systems*, Stanford, lecture notes
  "Solution via Laplace transform and matrix exponential" (Stanford Engineering Everywhere
  handout `10-expm.pdf`), slide 10–3 ("Derivative property"): `L(ż) = s Z(s) - z(0)`, by
  integration by parts.
-/

public section

open MeasureTheory Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f f' : ℝ → E} {s : ℂ}

/-- A function that is the derivative of `f` at every `t > 0` is a.e.-strongly measurable on
`(0, ∞)`. -/
private theorem aestronglyMeasurable_of_hasDerivAt [CompleteSpace E]
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t) :
    AEStronglyMeasurable f' (volume.restrict (Ioi 0)) :=
  (aestronglyMeasurable_deriv f _).congr <| (ae_restrict_iff' measurableSet_Ioi).2 <|
    ae_of_all _ fun t ht => (hderiv t ht).deriv

/-- If `f` has derivative `f' t` at every `t > 0` and `‖f' t‖ ≤ M exp (σ t)` for `t > 0`, the
Laplace transform of `f'` converges on `re s > σ`. -/
theorem laplaceConvergent_deriv [CompleteSpace E] {M σ : ℝ}
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hf'M : ∀ t ∈ Ioi (0 : ℝ), ‖f' t‖ ≤ M * Real.exp (σ * t)) (hs : σ < s.re) :
    LaplaceConvergent f' s :=
  laplaceConvergent_of_norm_le_exp (aestronglyMeasurable_of_hasDerivAt hderiv) hf'M hs

/-- **The derivative rule** `laplace f' s = s • laplace f s - f 0`. Hypotheses: `f` is continuous
from the right at `0` (so `f 0` is the right limit `f (0⁺)`), `f` has derivative `f' t` at every
`t > 0`, `‖f t‖ ≤ M exp (σ t)` and `‖f' t‖ ≤ M' exp (σ' t)` for `t > 0`; the conclusion holds
for every `s` with `σ < re s` and `σ' < re s`. -/
theorem laplace_deriv [CompleteSpace E] {M M' σ σ' : ℝ} (hf0 : ContinuousWithinAt f (Ici 0) 0)
    (hderiv : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt f (f' t) t)
    (hfM : ∀ t ∈ Ioi (0 : ℝ), ‖f t‖ ≤ M * Real.exp (σ * t))
    (hf'M : ∀ t ∈ Ioi (0 : ℝ), ‖f' t‖ ≤ M' * Real.exp (σ' * t)) (hs : σ < s.re)
    (hs' : σ' < s.re) :
    laplace f' s = s • laplace f s - f 0 := by
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi 0)) :=
    ContinuousOn.aestronglyMeasurable (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      measurableSet_Ioi
  have hL := laplaceConvergent_of_norm_le_exp hmeas hfM hs
  have hL' := laplaceConvergent_deriv hderiv hf'M hs'
  have hc : ∀ t : ℝ, HasDerivAt (fun τ : ℝ => Complex.exp (-s * τ))
      (-s * Complex.exp (-s * t)) t := fun t => by
    simpa [mul_comm] using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp
  have hG : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt (fun τ : ℝ => Complex.exp (-s * τ) • f τ)
      (Complex.exp (-s * t) • f' t + (-s * Complex.exp (-s * t)) • f t) t := fun t ht =>
    (hc t).smul (hderiv t ht)
  have hcont : ContinuousWithinAt (fun τ : ℝ => Complex.exp (-s * τ) • f τ) (Ici 0) 0 :=
    ((hc 0).continuousAt.continuousWithinAt).smul hf0
  have h2 : IntegrableOn (fun t : ℝ => (-s * Complex.exp (-s * t)) • f t) (Ioi 0) := by
    refine (Integrable.smul (-s) hL).congr (ae_of_all _ fun t => ?_)
    simp only [Pi.smul_apply, smul_smul]
  have hint : IntegrableOn
      (fun t : ℝ => Complex.exp (-s * t) • f' t + (-s * Complex.exp (-s * t)) • f t) (Ioi 0) := by
    exact Integrable.add hL' h2
  have hlim := tendsto_cexp_smul_of_norm_le_exp hfM hs
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hG hint hlim
  rw [integral_add hL' h2] at h
  simp only [mul_smul] at h
  rw [integral_smul] at h
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, zero_sub] at h
  change laplace f' s + (-s) • laplace f s = -f 0 at h
  rw [neg_smul] at h
  rw [sub_eq_neg_add, ← h]
  abel
