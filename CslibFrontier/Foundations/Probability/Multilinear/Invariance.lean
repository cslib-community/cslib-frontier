/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Probability.Multilinear.Bonami
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import CslibFrontier.Foundations.MeasureTheory.Integral.CauchySchwarz
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import CslibFrontier.Foundations.Probability.SmoothTests

/-!
# The Basic Invariance Principle

Let `F` be a formal multilinear polynomial of degree at most `k`, and let `x = (x₁, …, xₙ)` and
`y = (y₁, …, yₙ)` be sequences of independent random variables, each satisfying Hypothesis 11.65
(`HasInvarianceMoments`: mean `0`, variance `1`, third moment `0`, fourth moment at most `9`). If
`ψ : ℝ → ℝ` is `C⁴` with `‖ψ⁗‖_∞ ≤ C`, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 12 · 9 ^ k · ∑_t Inf_t[F] ^ 2`
(`abs_integral_comp_multilinearEval_sub_le`) [O'Donnell, Section 11.6, Basic Invariance
Principle, equation (11.29)][ODonnell2014]. In particular `F(x)` and `F(y)` are close in
distribution when every coordinate has small influence: if `Var[F] ≤ 1` and every `Inf_t[F] ≤ ε`,
the bound is `C / 12 · k 9 ^ k · ε` (`abs_integral_comp_multilinearEval_sub_le_of_influence_le`,
Corollary 11.67). The typical instance takes `x` uniform `±1` bits and `y` standard Gaussians
(`CslibFrontier.Foundations.BooleanAnalysis.Invariance`).

The proof is Lindeberg's replacement method. The hybrids `Measure.pi (s.piecewise ν μ)` replace the
coordinates in `s` one at a time (`MeasureTheory.abs_integral_pi_sub_le_sum`). Replacing coordinate
`t` writes `F = E_t F + z · D_t F` with `E_t F`, `D_t F` independent of the new coordinate `z`; by
Taylor's theorem to third order (the one-coordinate step
`ProbabilityTheory.abs_integral_sub_integral_le_of_moments` of
`CslibFrontier.Foundations.Probability.SmoothTests`), the first three moments of `x_t` and `y_t`
agree, so the step costs at most
`C / 24 · (E[x_t⁴] + E[y_t⁴]) · E[(D_t F)⁴] ≤ 3 C / 4 · E[(D_t F)⁴]`
(`HasInvarianceMoments.abs_integral_sub_le`). The Bonami Lemma for the hybrid ensemble
(`integral_multilinearEval_pow_four_le`) bounds `E[(D_t F)⁴] ≤ 9 ^ (k - 1) Inf_t[F] ^ 2`.

With a `C³` test function and a second-order expansion, the same argument gives
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 3 · 3 ^ k · ∑_t Inf_t[F] ^ (3 / 2)` when `‖ψ‴‖_∞ ≤ C`
(`abs_integral_comp_multilinearEval_sub_le_of_contDiff_three`): the step costs
`C / 6 · (E|x_t|³ + E|y_t|³) · E|D_t F|³`, Cauchy–Schwarz gives `E|z|³ ≤ √(E z² E z⁴) ≤ 3`, and
`E|D_t F|³ ≤ √(E (D_t F)² E (D_t F)⁴) ≤ 3 ^ (k - 1) Inf_t[F] ^ (3 / 2)`. This is the analogue under
Hypothesis 11.65 of [O'Donnell, Remark 11.66][ODonnell2014], which instead assumes the variables
are `(2, 3, ρ)`-hypercontractive with second moment `1` and has the factor `(1 / ρ) ^ (3 k)` in
place of `3 ^ k`; the hypercontractive version (Exercise 11.47) is not formalized here.

## Main results

* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le`: the Basic Invariance Principle.
* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le_of_influence_le`: Corollary 11.67.
* `ProbabilityTheory.abs_integral_comp_multilinearEval_sub_le_of_contDiff_three`: the `C³` form.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014], Section 11.6.
-/

public section

open MeasureTheory Finset
open scoped Nat ENNReal

namespace ProbabilityTheory

namespace HasInvarianceMoments

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- Under Hypothesis 11.65, `E|z|³ ≤ √(E z² · E z⁴) ≤ 3`. -/
theorem integral_abs_pow_three_le (hμ : HasInvarianceMoments μ) : ∫ s, |s| ^ 3 ∂μ ≤ 3 := by
  have h := sq_integral_abs_pow_three_le hμ.memLp_four
  rw [hμ.integral_sq, one_mul] at h
  have h0 : 0 ≤ ∫ s, |s| ^ 3 ∂μ := integral_nonneg fun _ => by positivity
  exact (pow_le_pow_iff_left₀ h0 (by norm_num) two_ne_zero).1
    (h.trans (by linarith [hμ.integral_pow_four_le]))

/-- **The replacement step under Hypothesis 11.65, `C⁴` form.** If `ψ` is `C⁴` with `|ψ⁗| ≤ C`,
then `|E_ν ψ(a + s b) - E_μ ψ(a + s b)| ≤ C / 24 · (E_ν s⁴ + E_μ s⁴) · b⁴ ≤ 3 C / 4 · b⁴`. -/
theorem abs_integral_sub_le (hμ : HasInvarianceMoments μ) (hν : HasInvarianceMoments ν)
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 4 ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv 4 ψ y| ≤ C) (a b : ℝ) :
    |∫ s, ψ (a + s * b) ∂ν - ∫ s, ψ (a + s * b) ∂μ| ≤ 3 / 4 * C * |b| ^ 4 := by
  have h := abs_integral_sub_integral_le_of_moments (n := 3) (by exact_mod_cast hν.memLp_four)
    (by exact_mod_cast hμ.memLp_four) ?_ hψ hC a b
  · have h4 (m : Measure ℝ) (hm : HasInvarianceMoments m) : ∫ s, |s| ^ (3 + 1) ∂m ≤ 9 := by
      simpa [Even.pow_abs (by decide : Even 4)] using hm.integral_pow_four_le
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    refine h.trans ((mul_le_mul_of_nonneg_left (add_le_add (h4 ν hν) (h4 μ hμ))
      (by positivity)).trans_eq ?_)
    rw [show ((3 + 1)! : ℝ) = 24 by norm_num [Nat.factorial]]; ring
  · intro j hj
    interval_cases j <;> simp [hν.integral_id, hμ.integral_id, hν.integral_sq, hμ.integral_sq,
      hν.integral_pow_three, hμ.integral_pow_three]

/-- **The replacement step under Hypothesis 11.65, `C³` form.** If `ψ` is `C³` with `|ψ‴| ≤ C`,
then `|E_ν ψ(a + s b) - E_μ ψ(a + s b)| ≤ C / 6 · (E_ν |s|³ + E_μ |s|³) · |b|³ ≤ C · |b|³`. -/
theorem abs_integral_sub_le_of_contDiff_three (hμ : HasInvarianceMoments μ)
    (hν : HasInvarianceMoments ν) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 ψ y| ≤ C) (a b : ℝ) :
    |∫ s, ψ (a + s * b) ∂ν - ∫ s, ψ (a + s * b) ∂μ| ≤ C * |b| ^ 3 := by
  have h := abs_integral_sub_integral_le_of_moments (n := 2)
    (by exact_mod_cast hν.memLp_four.mono_exponent (by norm_num))
    (by exact_mod_cast hμ.memLp_four.mono_exponent (by norm_num)) ?_ hψ hC a b
  · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    refine h.trans ((mul_le_mul_of_nonneg_left
      (add_le_add hν.integral_abs_pow_three_le hμ.integral_abs_pow_three_le)
      (by positivity)).trans_eq ?_)
    rw [show ((2 + 1)! : ℝ) = 6 by norm_num [Nat.factorial]]; ring
  · intro j hj
    interval_cases j <;> simp [hν.integral_id, hμ.integral_id, hν.integral_sq, hμ.integral_sq]

end HasInvarianceMoments

/-! ### The hybrid argument -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
theorem hasInvarianceMoments_piecewise (s : Finset ι) {μ ν : ι → Measure ℝ}
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i)) (i : ι) :
    HasInvarianceMoments (s.piecewise ν μ i) := by
  by_cases h : i ∈ s <;> simp [h, hμ i, hν i]

omit [DecidableEq ι] in
/-- A test function with bounded `(n+1)`st derivative, `n + 1 ≤ 4`, composed with a multilinear
polynomial of `L⁴` variables is integrable. -/
theorem integrable_comp_multilinearEval (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, MemLp id 4 (μ i)) (c : Finset ι → ℝ) {ψ : ℝ → ℝ} {n : ℕ} (hn : n + 1 ≤ 4)
    (hψ : ContDiff ℝ (n + 1) ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv (n + 1) ψ y| ≤ C) :
    Integrable (fun z => ψ (multilinearEval c z)) (Measure.pi μ) :=
  integrable_comp_of_memLp hψ hC ((memLp_multilinearEval μ (p := 4) (by norm_num)
    (by exact_mod_cast hμ) c).mono_exponent (by exact_mod_cast hn))

/-- `9 E[(D_t F)⁴] ≤ 9 ^ k Inf_t[F] ^ 2` for `F` of degree at most `k` (the Bonami Lemma for
`D_t F`, of degree at most `k - 1`). -/
private theorem integral_multilinearDerivCoeff_pow_four_le (P : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, HasInvarianceMoments (P i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) (t : ι) :
    9 * ∫ z, multilinearEval (multilinearDerivCoeff c t) z ^ 4 ∂Measure.pi P ≤
      9 ^ k * multilinearInfluence c t ^ 2 := by
  rcases k with _ | k
  · have hD0 := multilinearDerivCoeff_eq_zero_of_degree_zero hc t
    have hI : multilinearInfluence c t = 0 := by
      rw [multilinearInfluence_eq_sum_multilinearDerivCoeff_sq, hD0]; simp
    simp [hD0, hI]
  · have := integral_multilinearEval_pow_four_le P hP
      (multilinearDerivCoeff_eq_zero_of_card_lt hc t)
    rw [← multilinearInfluence_eq_sum_multilinearDerivCoeff_sq] at this
    rw [pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left this (by norm_num)

variable (μ ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]

/-- Shared hybrid argument: if each one-coordinate replacement costs at most `K |b| ^ (n + 1)` and
`K E|D_t F| ^ (n + 1) ≤ B t` over every hybrid, then `|E_μ ψ(F) - E_ν ψ(F)| ≤ ∑ t, B t`. -/
private theorem abs_integral_comp_multilinearEval_sub_le_of_step
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i))
    {c : Finset ι → ℝ} {ψ : ℝ → ℝ} {n : ℕ} (hn : n + 1 ≤ 4)
    (hψ : ContDiff ℝ (n + 1) ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv (n + 1) ψ y| ≤ C)
    {K : ℝ} (h1 : ∀ t a b, |∫ s, ψ (a + s * b) ∂ν t - ∫ s, ψ (a + s * b) ∂μ t| ≤ K * |b| ^ (n + 1))
    {B : ι → ℝ}
    (hD : ∀ s : Finset ι, ∀ t,
      K * ∫ z, |multilinearEval (multilinearDerivCoeff c t) z| ^ (n + 1)
        ∂Measure.pi (s.piecewise ν μ) ≤ B t) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      ∑ t, B t := by
  have hint (s : Finset ι) :
      Integrable (fun z => ψ (multilinearEval c z)) (Measure.pi (s.piecewise ν μ)) := by
    have := isProbabilityMeasure_piecewise μ ν s
    exact integrable_comp_multilinearEval _
      (fun i => (hasInvarianceMoments_piecewise s hμ hν i).memLp_four) c hn hψ hC
  refine abs_integral_pi_sub_le_sum μ ν _ fun s t ht => ?_
  have := isProbabilityMeasure_piecewise μ ν s
  have hPm := hasInvarianceMoments_piecewise s hμ hν
  rw [integral_pi_piecewise_insert_sub μ ν ht hint]
  refine (abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (ae_of_all _ fun _ => abs_nonneg _)
    ((integrable_abs_multilinearEval_pow _ (fun i => (hPm i).memLp_four) _ hn).const_mul K)
    (ae_of_all _ fun v => by simp only [multilinearEval_update c t]; exact h1 t _ _))).trans ?_
  rw [integral_const_mul]
  exact hD s t

/-- **The Basic Invariance Principle** [O'Donnell, Section 11.6, equation (11.29)][ODonnell2014].
Let `F` be a formal multilinear polynomial of degree at most `k`, and let `x` and `y` be vectors of
independent random variables with laws `μ i` and `ν i`, each satisfying Hypothesis 11.65. If
`ψ : ℝ → ℝ` is `C⁴` with `|ψ⁗| ≤ C`, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 12 · 9 ^ k · ∑_t Inf_t[F] ^ 2`. -/
theorem abs_integral_comp_multilinearEval_sub_le (hμ : ∀ i, HasInvarianceMoments (μ i))
    (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ} {c : Finset ι → ℝ}
    (hc : ∀ S, k < #S → c S = 0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 4 ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 4 ψ y| ≤ C) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      C / 12 * 9 ^ k * ∑ t, multilinearInfluence c t ^ 2 := by
  rw [mul_sum]
  refine abs_integral_comp_multilinearEval_sub_le_of_step μ ν hμ hν (n := 3) le_rfl hψ hC
    (fun t a b => (hμ t).abs_integral_sub_le (hν t) hψ hC a b) fun s t => ?_
  have := isProbabilityMeasure_piecewise μ ν s
  have hD := integral_multilinearDerivCoeff_pow_four_le _
    (hasInvarianceMoments_piecewise s hμ hν) hc t
  simp only [Even.pow_abs (by decide : Even 4)]
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  simpa only [← mul_assoc, show C / 12 * 9 = 3 / 4 * C by ring] using
    mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ C / 12)

/-- `∑_t Inf_t[F] ^ 2 ≤ ε k ∑_{S ≠ ∅} F̂(S) ^ 2` when `F` has degree at most `k` and every
influence is at most `ε` [O'Donnell, proof of Corollary 11.67][ODonnell2014]. -/
theorem sum_multilinearInfluence_sq_le {k : ℕ} {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ t, multilinearInfluence c t ≤ ε) :
    ∑ t, multilinearInfluence c t ^ 2 ≤ ε * k * ∑ S with S ≠ ∅, c S ^ 2 := by
  have hk : ∑ S, (#S : ℝ) * c S ^ 2 ≤ k * ∑ S with S ≠ ∅, c S ^ 2 := by
    rw [mul_sum, sum_filter]
    refine sum_le_sum fun S _ => ?_
    split_ifs with hS
    · rcases le_or_gt #S k with h | h
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast h) (sq_nonneg _)
      · rw [hc S h]; simp
    · rw [not_not.1 hS]; simp
  calc ∑ t, multilinearInfluence c t ^ 2 ≤ ∑ t, ε * multilinearInfluence c t :=
        sum_le_sum fun t _ => by
          rw [sq]; exact mul_le_mul_of_nonneg_right (hε t) (multilinearInfluence_nonneg c t)
    _ = ε * ∑ S, (#S : ℝ) * c S ^ 2 := by rw [← mul_sum, sum_multilinearInfluence]
    _ ≤ ε * (k * ∑ S with S ≠ ∅, c S ^ 2) := mul_le_mul_of_nonneg_left hk hε0
    _ = _ := by ring

/-- **Invariance for polynomials with small influences** [O'Donnell, Corollary 11.67]
[ODonnell2014]. In the setting of `abs_integral_comp_multilinearEval_sub_le`, if moreover
`Var[F] = ∑_{S ≠ ∅} F̂(S) ^ 2 ≤ 1` and `Inf_t[F] ≤ ε` for every `t`, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 12 · k 9 ^ k · ε`. The hypothesis `0 ≤ ε` only matters when there
are no coordinates. -/
theorem abs_integral_comp_multilinearEval_sub_le_of_influence_le
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) (hvar : ∑ S with S ≠ ∅, c S ^ 2 ≤ 1)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ∀ t, multilinearInfluence c t ≤ ε) {ψ : ℝ → ℝ}
    (hψ : ContDiff ℝ 4 ψ) {C : ℝ} (hC : ∀ y, |iteratedDeriv 4 ψ y| ≤ C) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      C / 12 * k * 9 ^ k * ε := by
  refine (abs_integral_comp_multilinearEval_sub_le μ ν hμ hν hc hψ hC).trans ?_
  have h := sum_multilinearInfluence_sq_le hc hε0 hε
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have h2 : ε * k * ∑ S with S ≠ ∅, c S ^ 2 ≤ ε * k := by
    have := mul_le_mul_of_nonneg_left hvar (by positivity : 0 ≤ ε * k); linarith
  calc C / 12 * 9 ^ k * ∑ t, multilinearInfluence c t ^ 2 ≤ C / 12 * 9 ^ k * (ε * k) :=
        mul_le_mul_of_nonneg_left (h.trans h2) (by positivity)
    _ = _ := by ring

/-- `3 E|D_t F|³ ≤ 3 ^ k Inf_t[F] ^ (3 / 2)` for `F` of degree at most `k`: Cauchy–Schwarz gives
`(E|D_t F|³)² ≤ E[(D_t F)²] E[(D_t F)⁴]`, and `E[(D_t F)²] = Inf_t[F]`, while the Bonami Lemma gives
`E[(D_t F)⁴] ≤ 9 ^ (k - 1) Inf_t[F] ^ 2`. -/
private theorem integral_abs_multilinearDerivCoeff_pow_three_le (P : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (P i)] (hP : ∀ i, HasInvarianceMoments (P i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) (t : ι) :
    3 * ∫ z, |multilinearEval (multilinearDerivCoeff c t) z| ^ 3 ∂Measure.pi P ≤
      3 ^ k * multilinearInfluence c t ^ ((3 : ℝ) / 2) := by
  set D := multilinearEval (multilinearDerivCoeff c t)
  set I := multilinearInfluence c t
  have hI0 : 0 ≤ I := multilinearInfluence_nonneg c t
  have hm4 (i : ι) := (hP i).memLp_four
  have h2 : ∫ z, D z ^ 2 ∂Measure.pi P = I := by
    rw [integral_multilinearEval_sq_of_hasInvarianceMoments P hP,
      ← multilinearInfluence_eq_sum_multilinearDerivCoeff_sq]
  have h4 := integral_multilinearDerivCoeff_pow_four_le P hP hc t
  have hD2 : Integrable (fun z => D z ^ 2) (Measure.pi P) :=
    integrable_multilinearEval_pow P hm4 _ (by norm_num)
  have hD4 : Integrable (fun z => D z ^ 4) (Measure.pi P) :=
    integrable_multilinearEval_pow P hm4 _ le_rfl
  have hD3 : Integrable (fun z => |D z| ^ 3) (Measure.pi P) :=
    integrable_abs_multilinearEval_pow P hm4 _ (by norm_num)
  have hCS := sq_integral_mul_le (P := Measure.pi P) (f := fun z => |D z|)
    (g := fun z => D z ^ 2) (by simpa using hD2) (by simpa only [← pow_mul] using hD4)
    (hD3.congr (ae_of_all _ fun z => by simp only; rw [← sq_abs (D z)]; ring))
  have h3 : ∫ z, |D z| * D z ^ 2 ∂Measure.pi P = ∫ z, |D z| ^ 3 ∂Measure.pi P := by
    congr 1 with z : 1; rw [← sq_abs (D z)]; ring
  simp only [sq_abs, ← pow_mul, Nat.reduceMul] at hCS
  rw [h3, h2] at hCS
  set M := ∫ z, |D z| ^ 3 ∂Measure.pi P
  have hM0 : 0 ≤ M := integral_nonneg fun _ => by positivity
  have hR0 : 0 ≤ 3 ^ k * I ^ ((3 : ℝ) / 2) := by positivity
  have hR : (3 ^ k * I ^ ((3 : ℝ) / 2)) ^ 2 = 9 ^ k * I ^ 3 := by
    rw [mul_pow, ← Real.rpow_mul_natCast hI0, ← pow_mul, mul_comm k, pow_mul]
    norm_num
  refine (pow_le_pow_iff_left₀ (by positivity) hR0 two_ne_zero).1 ?_
  rw [hR]
  calc (3 * M) ^ 2 = 9 * M ^ 2 := by ring
    _ ≤ 9 * (I * ∫ z, D z ^ 4 ∂Measure.pi P) := by gcongr
    _ = I * (9 * ∫ z, D z ^ 4 ∂Measure.pi P) := by ring
    _ ≤ I * (9 ^ k * I ^ 2) := by gcongr
    _ = 9 ^ k * I ^ 3 := by ring

/-- **The Basic Invariance Principle, `C³` form.** In the setting of
`abs_integral_comp_multilinearEval_sub_le`, if `ψ` is only `C³` with `|ψ‴| ≤ C`, then
`|E[ψ(F(x))] - E[ψ(F(y))]| ≤ C / 3 · 3 ^ k · ∑_t Inf_t[F] ^ (3 / 2)`. This is the analogue under
Hypothesis 11.65 of [O'Donnell, Remark 11.66][ODonnell2014], whose hypothesis is instead
`(2, 3, ρ)`-hypercontractivity of the variables and whose factor is `(1 / ρ) ^ (3 k)`; the factor
`3 ^ k` here is the value of that factor at `ρ = 3 ^ (-1 / 3)`. -/
theorem abs_integral_comp_multilinearEval_sub_le_of_contDiff_three
    (hμ : ∀ i, HasInvarianceMoments (μ i)) (hν : ∀ i, HasInvarianceMoments (ν i)) {k : ℕ}
    {c : Finset ι → ℝ} (hc : ∀ S, k < #S → c S = 0) {ψ : ℝ → ℝ} (hψ : ContDiff ℝ 3 ψ) {C : ℝ}
    (hC : ∀ y, |iteratedDeriv 3 ψ y| ≤ C) :
    |∫ z, ψ (multilinearEval c z) ∂Measure.pi μ - ∫ z, ψ (multilinearEval c z) ∂Measure.pi ν| ≤
      C / 3 * 3 ^ k * ∑ t, multilinearInfluence c t ^ ((3 : ℝ) / 2) := by
  rw [mul_sum]
  refine abs_integral_comp_multilinearEval_sub_le_of_step μ ν hμ hν (n := 2) (by norm_num) hψ hC
    (fun t a b => (hμ t).abs_integral_sub_le_of_contDiff_three (hν t) hψ hC a b) fun s t => ?_
  have := isProbabilityMeasure_piecewise μ ν s
  have hD := integral_abs_multilinearDerivCoeff_pow_three_le _
    (hasInvarianceMoments_piecewise s hμ hν) hc t
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  simpa only [← mul_assoc, show C / 3 * 3 = C by ring] using
    mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ C / 3)

end ProbabilityTheory
