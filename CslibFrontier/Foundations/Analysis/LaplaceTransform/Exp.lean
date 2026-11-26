/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, with `Mathlib/Analysis/LaplaceTransform.lean`)

public import CslibFrontier.Foundations.Analysis.LaplaceTransform.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Laplace transform of the exponential: the resolvent

In a complete normed `ℂ`-algebra `𝔸`, if `‖exp (t • a)‖ ≤ M exp (ω t)` for `t > 0`, then on the
half-plane `re s > ω` the element `s - a` is invertible and the Laplace transform of the flow
`t ↦ exp (t • a)` is its inverse, the resolvent (`isUnit_algebraMap_sub_of_norm_exp_le`,
`laplace_exp_smul`):
`laplace (fun t => exp ((t : ℂ) • a)) s = Ring.inverse (algebraMap ℂ 𝔸 s - a)`.
Invertibility is proved, not assumed: the transform is a two-sided inverse, by the fundamental
theorem of calculus on `(0, ∞)` applied to `t ↦ exp (-s t) • exp (t • a)`. In a normed algebra
with `‖1‖ = 1` the bound holds with `M = 1`, `ω = ‖a‖` (`norm_exp_smul_le`), which gives the
half-plane `re s > ‖a‖` (`laplace_exp_smul_of_norm_lt`).

For square complex matrices, with no norm chosen, the hypothesis is an entrywise bound
`‖exp (t • A) i j‖ ≤ M exp (ω t)` and the conclusion is entrywise:
`laplace (fun t => exp ((t : ℂ) • A) i j) s = (s • 1 - A)⁻¹ i j` on `re s > ω`
(`Matrix.isUnit_smul_one_sub_of_norm_exp_le`, `Matrix.laplace_exp_smul_apply`).

## Main results

* `laplaceConvergent_exp_smul`, `isUnit_algebraMap_sub_of_norm_exp_le`, `laplace_exp_smul`.
* `norm_exp_smul_le`, `isUnit_algebraMap_sub_of_norm_lt`, `laplace_exp_smul_of_norm_lt`.
* `Matrix.laplaceConvergent_exp_smul_apply`, `Matrix.isUnit_smul_one_sub_of_norm_exp_le`,
  `Matrix.laplace_exp_smul_apply`.

## References

* S. Boyd, *EE263: Introduction to Linear Dynamical Systems*, Stanford, lecture "Solution via
  Laplace transform and matrix exponential" (the resolvent `(sI - A)⁻¹` as the transform of
  `e^{tA}`). Locator to be checked.
-/

public section

open MeasureTheory Set Filter Topology NormedSpace

noncomputable section

section Algebra

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸] {a : 𝔸} {s : ℂ}
  {M ω : ℝ}

private theorem hasDerivAt_exp_ofReal_smul (a : 𝔸) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => exp ((τ : ℂ) • a)) (exp ((t : ℂ) • a) * a) t :=
  by
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℂ) a (Complex.ofRealCLM t)).scomp t
    (Complex.ofRealCLM.hasDerivAt (x := t))
  convert h using 1
  · funext τ
    simp
  · simp

private theorem continuous_exp_ofReal_smul (a : 𝔸) :
    Continuous fun τ : ℝ => exp ((τ : ℂ) • a) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_ofReal_smul a t).continuousAt

/-- The flow `t ↦ exp (t • a)` has a convergent Laplace transform on `re s > ω` when
`‖exp (t • a)‖ ≤ M exp (ω t)` for `t > 0`. -/
theorem laplaceConvergent_exp_smul
    (hM : ∀ t ∈ Ioi (0 : ℝ), ‖exp ((t : ℂ) • a)‖ ≤ M * Real.exp (ω * t)) (hs : ω < s.re) :
    LaplaceConvergent (fun t : ℝ => exp ((t : ℂ) • a)) s :=
  laplaceConvergent_of_norm_le_exp (continuous_exp_ofReal_smul a).aestronglyMeasurable hM hs

/-- The Laplace transform of the flow is a two-sided inverse of `s - a`. -/
private theorem laplace_exp_smul_mul_and
    (hM : ∀ t ∈ Ioi (0 : ℝ), ‖exp ((t : ℂ) • a)‖ ≤ M * Real.exp (ω * t)) (hs : ω < s.re) :
    laplace (fun t : ℝ => exp ((t : ℂ) • a)) s * (algebraMap ℂ 𝔸 s - a) = 1 ∧
      (algebraMap ℂ 𝔸 s - a) * laplace (fun t : ℝ => exp ((t : ℂ) • a)) s = 1 := by
  set R := laplace (fun t : ℝ => exp ((t : ℂ) • a)) s
  have hL := laplaceConvergent_exp_smul hM hs
  set Φ : ℝ → 𝔸 := fun t => Complex.exp (-s * t) • exp ((t : ℂ) • a)
  have hc : ∀ t : ℝ, HasDerivAt (fun τ : ℝ => Complex.exp (-s * τ))
      (-s * Complex.exp (-s * t)) t := fun t => by
    simpa [mul_comm] using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-s)).cexp
  have hcomm : ∀ t : ℝ, Commute a (exp ((t : ℂ) • a)) := fun t =>
    ((Commute.refl a).smul_right (t : ℂ)).exp_right
  have hΦ : ∀ t ∈ Ioi (0 : ℝ), HasDerivAt Φ (Φ t * (a - algebraMap ℂ 𝔸 s)) t := fun t _ => by
    convert (hc t).smul (hasDerivAt_exp_ofReal_smul a t) using 1
    simp only [Φ]
    rw [Algebra.algebraMap_eq_smul_one, mul_sub, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      mul_one, smul_smul]
    module
  have hΦ' : ∀ t, Φ t * (a - algebraMap ℂ 𝔸 s) = (a - algebraMap ℂ 𝔸 s) * Φ t := fun t => by
    simp only [Φ]
    rw [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, (hcomm t).eq, Algebra.commutes]
  have hint : IntegrableOn (fun t => Φ t * (a - algebraMap ℂ 𝔸 s)) (Ioi 0) :=
    (ContinuousLinearMap.mul ℂ 𝔸).flip (a - algebraMap ℂ 𝔸 s) |>.integrable_comp hL
  have hlim : Tendsto Φ atTop (𝓝 0) := tendsto_cexp_smul_of_norm_le_exp hM hs
  have hcont : ContinuousWithinAt Φ (Ici 0) 0 :=
    (((hc 0).continuousAt).smul (continuous_exp_ofReal_smul a).continuousAt).continuousWithinAt
  have h := integral_Ioi_of_hasDerivAt_of_tendsto hcont hΦ hint hlim
  have hR : ∫ t in Ioi (0 : ℝ), Φ t * (a - algebraMap ℂ 𝔸 s) = R * (a - algebraMap ℂ 𝔸 s) :=
    ((ContinuousLinearMap.mul ℂ 𝔸).flip (a - algebraMap ℂ 𝔸 s)).integral_comp_comm hL
  have hR' : ∫ t in Ioi (0 : ℝ), Φ t * (a - algebraMap ℂ 𝔸 s) = (a - algebraMap ℂ 𝔸 s) * R := by
    simp_rw [hΦ']
    exact ((ContinuousLinearMap.mul ℂ 𝔸) (a - algebraMap ℂ 𝔸 s)).integral_comp_comm hL
  have h0 : Φ 0 = 1 := by simp [Φ]
  rw [h0, zero_sub] at h
  constructor
  · rw [← neg_sub a, mul_neg, ← hR, h, neg_neg]
  · rw [← neg_sub a, neg_mul, ← hR', h, neg_neg]

/-- **`s - a` is invertible on the half-plane of growth of the flow.** If
`‖exp (t • a)‖ ≤ M exp (ω t)` for `t > 0`, then `algebraMap ℂ 𝔸 s - a` is a unit for every `s`
with `ω < re s`. -/
theorem isUnit_algebraMap_sub_of_norm_exp_le
    (hM : ∀ t ∈ Ioi (0 : ℝ), ‖exp ((t : ℂ) • a)‖ ≤ M * Real.exp (ω * t)) (hs : ω < s.re) :
    IsUnit (algebraMap ℂ 𝔸 s - a) :=
  let h := laplace_exp_smul_mul_and hM hs
  ⟨⟨_, _, h.2, h.1⟩, rfl⟩

/-- **The Laplace transform of the flow is the resolvent.** If `‖exp (t • a)‖ ≤ M exp (ω t)` for
`t > 0`, then `laplace (fun t => exp (t • a)) s = (s - a)⁻¹` for every `s` with `ω < re s`,
where `s - a` is invertible by `isUnit_algebraMap_sub_of_norm_exp_le`. -/
theorem laplace_exp_smul
    (hM : ∀ t ∈ Ioi (0 : ℝ), ‖exp ((t : ℂ) • a)‖ ≤ M * Real.exp (ω * t)) (hs : ω < s.re) :
    laplace (fun t : ℝ => exp ((t : ℂ) • a)) s = Ring.inverse (algebraMap ℂ 𝔸 s - a) := by
  have h := laplace_exp_smul_mul_and hM hs
  rw [← (isUnit_algebraMap_sub_of_norm_exp_le hM hs).unit_spec, Ring.inverse_unit]
  exact (Units.inv_eq_of_mul_eq_one_left h.1).symm

omit [CompleteSpace 𝔸] in
/-- The exponential bound `‖exp (t • a)‖ ≤ exp (‖a‖ t)` for `t ≥ 0` in a normed algebra with
`‖1‖ = 1`. -/
theorem norm_exp_smul_le [NormOneClass 𝔸] {t : ℝ} (ht : 0 ≤ t) :
    ‖exp ((t : ℂ) • a)‖ ≤ Real.exp (‖a‖ * t) := by
  set x := (t : ℂ) • a
  have hx : ‖x‖ = ‖a‖ * t := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg ht, mul_comm]
  rw [← hx, congrFun (exp_eq_tsum ℂ) x, Real.exp_eq_exp_ℝ, congrFun (exp_eq_tsum ℝ) ‖x‖]
  refine (norm_tsum_le_tsum_norm (norm_expSeries_summable' (𝕂 := ℂ) x)).trans ?_
  refine (norm_expSeries_summable' (𝕂 := ℂ) x).tsum_le_tsum (fun n => ?_)
    (expSeries_summable' (𝕂 := ℝ) ‖x‖)
  rw [norm_smul, smul_eq_mul, norm_inv, Complex.norm_natCast]
  gcongr
  exact norm_pow_le x n

/-- **The resolvent on `re s > ‖a‖`.** In a complete normed algebra with `‖1‖ = 1`, `s - a` is
invertible for every `s` with `‖a‖ < re s`. -/
theorem isUnit_algebraMap_sub_of_norm_lt [NormOneClass 𝔸] (hs : ‖a‖ < s.re) :
    IsUnit (algebraMap ℂ 𝔸 s - a) :=
  isUnit_algebraMap_sub_of_norm_exp_le (M := 1) (fun _ ht => by
    rw [one_mul]; exact norm_exp_smul_le (le_of_lt ht)) hs

/-- **The Laplace transform of the flow on `re s > ‖a‖`.** In a complete normed algebra with
`‖1‖ = 1`, `laplace (fun t => exp (t • a)) s = (s - a)⁻¹` for every `s` with `‖a‖ < re s`. -/
theorem laplace_exp_smul_of_norm_lt [NormOneClass 𝔸] (hs : ‖a‖ < s.re) :
    laplace (fun t : ℝ => exp ((t : ℂ) • a)) s = Ring.inverse (algebraMap ℂ 𝔸 s - a) :=
  laplace_exp_smul (M := 1) (fun _ ht => by
    rw [one_mul]; exact norm_exp_smul_le (le_of_lt ht)) hs

end Algebra

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} {s : ℂ} {M ω : ℝ}

open scoped Matrix.Norms.Operator in
/-- An entrywise bound gives a bound in the `L∞` operator norm. -/
private theorem norm_le_card_mul {X : Matrix n n ℂ} {K : ℝ} (h : ∀ i j, ‖X i j‖ ≤ K) :
    ‖X‖ ≤ Fintype.card n * K := by
  rw [linfty_opNorm_def]
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i0⟩⟩
  · simp [Finset.univ_eq_empty]
  · have hK : 0 ≤ K := (norm_nonneg _).trans (h i0 i0)
    have hs : (Finset.univ.sup fun i => ∑ j, ‖X i j‖₊) ≤
        ⟨Fintype.card n * K, by positivity⟩ := by
      refine Finset.sup_le fun i _ => ?_
      apply NNReal.coe_le_coe.1
      simp only [NNReal.coe_sum, coe_nnNorm]
      calc ∑ j, ‖X i j‖ ≤ ∑ _j : n, K := Finset.sum_le_sum fun j _ => h i j
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; rfl
    exact NNReal.coe_le_coe.2 hs

open scoped Matrix.Norms.Operator in
private theorem norm_exp_le_of_apply_le
    (hM : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, ‖exp ((t : ℂ) • A) i j‖ ≤ M * Real.exp (ω * t)) :
    ∀ t ∈ Ioi (0 : ℝ), ‖exp ((t : ℂ) • A)‖ ≤ (Fintype.card n * M) * Real.exp (ω * t) :=
  fun t ht => (norm_le_card_mul (hM t ht)).trans_eq (by ring)

open scoped Matrix.Norms.Operator in
/-- The entry map of a matrix as a continuous linear map. -/
private noncomputable def entryCLM (i j : n) : Matrix n n ℂ →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (entryLinearMap ℂ ℂ i j : Matrix n n ℂ →ₗ[ℂ] ℂ)

/-- Entries of the matrix flow have convergent Laplace transforms on `re s > ω` under an entrywise
bound `‖exp (t • A) i j‖ ≤ M exp (ω t)` for `t > 0`. -/
theorem laplaceConvergent_exp_smul_apply
    (hM : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, ‖exp ((t : ℂ) • A) i j‖ ≤ M * Real.exp (ω * t))
    (hs : ω < s.re) (i j : n) : LaplaceConvergent (fun t : ℝ => exp ((t : ℂ) • A) i j) s := by
  open scoped Matrix.Norms.Operator in
  exact (entryCLM i j).laplaceConvergent_comp
    (laplaceConvergent_exp_smul (norm_exp_le_of_apply_le hM) hs)

/-- **`s I - A` is invertible on the half-plane of growth of the flow.** If every entry of
`exp (t • A)` satisfies `‖exp (t • A) i j‖ ≤ M exp (ω t)` for `t > 0`, then `s • 1 - A` is
invertible for every `s` with `ω < re s`. -/
theorem isUnit_smul_one_sub_of_norm_exp_le
    (hM : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, ‖exp ((t : ℂ) • A) i j‖ ≤ M * Real.exp (ω * t))
    (hs : ω < s.re) : IsUnit (s • (1 : Matrix n n ℂ) - A) := by
  open scoped Matrix.Norms.Operator in
  have h := isUnit_algebraMap_sub_of_norm_exp_le (norm_exp_le_of_apply_le hM) hs
  rwa [Algebra.algebraMap_eq_smul_one] at h

/-- **The Laplace transform of the matrix exponential is the resolvent.** If every entry of
`exp (t • A)` satisfies `‖exp (t • A) i j‖ ≤ M exp (ω t)` for `t > 0`, then for every `s` with
`ω < re s` and all `i j`,
`laplace (fun t => exp (t • A) i j) s = (s • 1 - A)⁻¹ i j`, where `s • 1 - A` is invertible by
`Matrix.isUnit_smul_one_sub_of_norm_exp_le`. -/
theorem laplace_exp_smul_apply
    (hM : ∀ t ∈ Ioi (0 : ℝ), ∀ i j, ‖exp ((t : ℂ) • A) i j‖ ≤ M * Real.exp (ω * t))
    (hs : ω < s.re) (i j : n) :
    laplace (fun t : ℝ => exp ((t : ℂ) • A) i j) s = (s • (1 : Matrix n n ℂ) - A)⁻¹ i j := by
  open scoped Matrix.Norms.Operator in
  have hL := laplaceConvergent_exp_smul (norm_exp_le_of_apply_le hM) hs
  open scoped Matrix.Norms.Operator in
  have h := laplace_exp_smul (norm_exp_le_of_apply_le hM) hs
  rw [Algebra.algebraMap_eq_smul_one, ← nonsing_inv_eq_ringInverse] at h
  rw [← h]
  open scoped Matrix.Norms.Operator in
  exact (entryCLM i j).laplace_comp hL

end Matrix
