/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.POVM.Density
public import CslibFrontier.Probability.PMF
public import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Probability.PMF.Map

/-!
# Measuring finite mixtures

A finite PMF-weighted sum of density matrices is a density matrix. Measuring that sum agrees
with first sampling the classical index and then measuring its state. These are original bridges
between the existing density-matrix and PMF representations, with no new mixture or state type.

## Main results

* `Cslib.Quantum.isDensityMatrix_pmf_sum`: a finite probabilistic mixture is normalized.
* `Cslib.Quantum.POVM.measureDensity_pmf_sum`: measuring a mixture is a probabilistic bind.
-/

public section

namespace Cslib.Quantum

open Matrix Finset
open scoped ComplexOrder

variable {ι A B : Type*} [Fintype ι] [Fintype A]

/-- A finite probabilistic mixture of density matrices is again a density matrix. -/
theorem isDensityMatrix_pmf_sum (p : PMF A) (ρ : A → Matrix ι ι ℂ)
    (hρ : ∀ a, IsDensityMatrix (ρ a)) :
    IsDensityMatrix (∑ a, (p a).toReal • ρ a) := by
  refine ⟨posSemidef_sum _ (fun a _ => (hρ a).posSemidef.smul ENNReal.toReal_nonneg), ?_⟩
  rw [Matrix.trace_sum]
  simp only [Matrix.trace_smul, (hρ _).trace_eq_one]
  rw [← sum_smul, Probability.PMF.sum_toReal, one_smul]

omit [Fintype A] in
/-- The density probability is additive over finite sums, without normalization assumptions. -/
theorem POVM.densityProb_sum [DecidableEq ι] [Fintype B] (M : POVM B ι)
    (s : Finset A) (ρ : A → Matrix ι ι ℂ) (b : B) :
    M.densityProb (∑ a ∈ s, ρ a) b = ∑ a ∈ s, M.densityProb (ρ a) b := by
  simp [POVM.densityProb, Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

/-- Measuring a finite mixture agrees with sampling its classical index and measuring once. -/
theorem POVM.measureDensity_pmf_sum [DecidableEq ι] [Fintype B] (M : POVM B ι)
    (p : PMF A) (ρ : A → Matrix ι ι ℂ) (hρ : ∀ a, IsDensityMatrix (ρ a)) :
    M.measureDensity (∑ a, (p a).toReal • ρ a) (isDensityMatrix_pmf_sum p ρ hρ) =
      p.bind (fun a => M.measureDensity (ρ a) (hρ a)) := by
  ext b
  rw [POVM.measureDensity_apply, PMF.bind_apply, tsum_fintype, POVM.densityProb_sum]
  simp only [POVM.densityProb_smul, POVM.measureDensity_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ =>
    mul_nonneg ENNReal.toReal_nonneg (M.densityProb_nonneg (hρ a).posSemidef b))]
  apply sum_congr rfl
  intro a _
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (p.apply_ne_top a)]

namespace POVM

variable [DecidableEq ι] [Fintype B]

/-- Randomly select a measurement using an independent finite classical draw. -/
noncomputable def mixture (p : PMF A) (M : A → POVM B ι) : POVM B ι where
  effect b := ∑ a, (p a).toReal • (M a).effect b
  posSemidef b := posSemidef_sum _ fun a _ => ((M a).posSemidef b).smul ENNReal.toReal_nonneg
  sum_effect := by
    rw [Finset.sum_comm]
    simp only [← Finset.smul_sum, sum_effect, ← Finset.sum_smul,
      Probability.PMF.sum_toReal, one_smul]

/-- The randomized measurement produces the exact law of the two-stage experiment. -/
theorem measureDensity_mixture (p : PMF A) (M : A → POVM B ι)
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityMatrix ρ) :
    (mixture p M).measureDensity ρ hρ = p.bind fun a => (M a).measureDensity ρ hρ := by
  ext b
  simp only [measureDensity_apply, densityProb, mixture, Finset.sum_mul, Matrix.smul_mul,
    Matrix.trace_sum, Matrix.trace_smul, Complex.re_sum, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, PMF.bind_apply, tsum_fintype]
  change ENNReal.ofReal (∑ a, (p a).toReal * (M a).densityProb ρ b) =
    ∑ a, p a * ENNReal.ofReal ((M a).densityProb ρ b)
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => mul_nonneg (ENNReal.toReal_nonneg (a := p a))
    ((M a).densityProb_nonneg hρ.posSemidef b))]
  simp [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (p.apply_ne_top _)]

/-- The effect of a randomized measurement is the probability-weighted sum of effects. -/
theorem mixture_effect (p : PMF A) (M : A → POVM B ι) (b : B) :
    (mixture p M).effect b = ∑ a, (p a).toReal • (M a).effect b := by
  unfold mixture
  rfl

open scoped MatrixOrder in
/-- Each weighted branch effect lies below the effect of the mixture in Loewner order. -/
theorem smul_effect_le_mixture (p : PMF A) (M : A → POVM B ι) (a : A) (b : B) :
    (p a).toReal • (M a).effect b ≤ (mixture p M).effect b := by
  rw [mixture_effect]
  exact single_le_sum (fun i _ => ((M i).posSemidef b |>.smul ENNReal.toReal_nonneg).nonneg)
    (mem_univ a)

/-- Choosing a measurement at random and measuring a unit vector agrees with the two-stage
classical experiment. -/
theorem measure_mixture (p : PMF A) (M : A → POVM B ι)
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) :
    (mixture p M).measure ψ hψ = p.bind fun a => (M a).measure ψ hψ := by
  simp_rw [← measureDensity_pureState]
  exact measureDensity_mixture p M _ _

/-- A two-stage draw of a measurement can be averaged in either order. -/
theorem mixture_bind {Z : Type*} [Fintype Z] (r : PMF Z) (p : Z → PMF A)
    (M : A → POVM B ι) :
    mixture (r.bind p) M = mixture r (fun z => mixture (p z) M) := by
  ext1 b
  simp only [mixture_effect, Probability.PMF.bind_apply_toReal, Finset.sum_smul, Finset.smul_sum,
    smul_smul]
  exact Finset.sum_comm

open scoped unitInterval in
/-- A coin-controlled mixture of two question laws gives the corresponding convex combination
of the two averaged effects. -/
theorem mixture_coin_bind_effect (η : I) (p₀ p₁ : PMF A) (M : A → POVM B ι) (b : B) :
    (mixture ((Probability.PMF.coin η).bind fun erase => if erase then p₀ else p₁) M).effect b =
      (η : ℝ) • (mixture p₀ M).effect b + (1 - (η : ℝ)) • (mixture p₁ M).effect b := by
  rw [mixture_bind, mixture_effect, Fintype.sum_bool]
  simp only [Probability.PMF.coin_apply_toReal, Bool.false_eq_true, ite_true, ite_false]

open scoped Kronecker in
/-- Independent choices of local measurements give the mixture of their product POVMs. -/
theorem kronecker_mixture {C D κ : Type*} [Fintype C] [Fintype D] [Fintype κ] [DecidableEq κ]
    (p : PMF A) (q : PMF C) (M : A → POVM B ι) (N : C → POVM D κ) :
    (mixture p M).kronecker (mixture q N) =
      mixture (p.bind fun a => q.map (a, ·)) (fun (a, c) => (M a).kronecker (N c)) := by
  ext ⟨b, d⟩ ⟨i, k⟩ ⟨j, l⟩
  simp only [kronecker, mixture_effect, kronecker_apply, Matrix.sum_apply, Fintype.sum_prod_type,
    Probability.PMF.bind_map_prodMk_apply, ENNReal.toReal_mul]
  rw [Finset.sum_mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
  simp only [Matrix.smul_apply, Complex.real_smul, Complex.ofReal_mul, kroneckerMap_apply]
  ring

end POVM

end Cslib.Quantum
