/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.OddCircuitFourier
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import CslibFrontier.Foundations.Data.Code.BallVolume
import CslibFrontier.Foundations.Data.Nat.Choose.Entropy
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Lindsey
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Fourier estimates for the punctured Hamming ball

Let `B = {x ∈ 𝔽₂ⁿ | 0 < |x| ≤ w}` have `V` elements and let `μ̂(y) = charSum B y / V` be the
normalized Fourier transform of its indicator. Lemma 3.1 of [Saglam2027] bounds the third moment
`𝔼_y |μ̂(y)| ^ 3 = O(1 / (V n ^ 3))` and the tail
`Pr_y[|μ̂(y)| > 1 / n] ≤ 2 ^ (-n + 2 n (log₂ n / w) log₂ (e w / log₂ n))` for
`log n ≪ w ≤ (1 / 2 - ε) n`. `Cslib.Code.PuncturedBallFourierBounds n w C` states the two bounds
for one `n` and `w` with moment constant `C`; it is the input of the asymptotic code
construction in `CslibFrontier.Foundations.Data.Code.OddCircuitAsymptotic`.

Saglam derives Lemma 3.1 from two results of Kirshner and Samorodnitsky [KirshnerSamorodnitsky2021,
Corollary 1.4 and Theorem 1.5] about polynomials `f` of degree at most `w` on the cube, in the
specializations quoted in [Saglam2027, Appendix A]. Those results are **not proved here**; they are
stated as the hypotheses `Cslib.Code.KSThirdMomentBound` and `Cslib.Code.KSTailBound`, in nats:

* third moment: `𝔼|f| ^ 3 ≤ (𝔼 f ^ 2) ^ (3 / 2) exp (n (h(ρ) / 2 - γ(ρ)))` with `ρ = w / n` and
  `γ = Cslib.Code.ksGamma`;
* tail: `Pr[|f| > √(𝔼 f ^ 2) exp (n (T(ρ, k / n) - h(ρ) / 2))] ≤ exp (n (h(k / n) - log 2))` for
  integers `k` with `k / n ≤ 1 / 2 - √(ρ (1 - ρ))`, where `T = Cslib.Code.ksTailExponent`.

Here `h = Real.binEntropy` is the binary entropy in nats. Saglam writes both in bits with base-`2`
logarithms (`2 ^ (n (H₂(ρ)/2 - γ₂(ρ)))`, `2 ^ (n (H₂(y) - 1))`); multiplying the exponents by
`log 2` gives the forms above. A polynomial of degree at most `w` is written by its Fourier
coefficients `a x`, which vanish for `|x| > w`. The hypotheses are only required for `0 < w` and
`2 w < n`, the range in which they are used.

These forms agree with arXiv:1909.11929v1, which states both bounds for every `n` with no error
term. Saglam's `γ` is `H₂(ρ) / 2 - ψ(3, ρ)`, by Kirshner–Samorodnitsky Proposition 2.6 at `p = 3`
with `t = 1 - 2 δ`, which gives Saglam's `1 - 2 u = √(ρ / (2 - 3 ρ))`. Saglam's integral is their
tail exponent `τ` on `y ≤ 1 / 2 - √(ρ (1 - ρ))` (their §2.1.1–2.1.2).

Everything else in Saglam's Appendix A is proved: `μ̂` has degree at most `w` and
`𝔼 μ̂ ^ 2 = 1 / V` (`Cslib.Code.sum_charSum_sq`); `γ(ρ) ≥ c ρ` for `0 < ρ ≤ 1 / 2 - ε`
(`Cslib.Code.exists_mul_le_ksGamma`); `T(ρ, y) ≤ h(ρ) - 2 ρ y` (`Cslib.Code.ksTailExponent_le`);
`exp (n h(w / n)) ≤ (n + 1) V` (`Cslib.exp_mul_binEntropy_le_succ_mul_choose`); and
`h(y) ≤ y log (e / y)`. Together they give
`Cslib.Code.exists_puncturedBallFourierBounds_of_ks`: Lemma 3.1 with explicit constants, the
moment constant being `C = 2`.

Saglam proves `γ(ρ) = (ρ / 2) log₂ (1 / ρ) + O(ρ)`. The weaker `γ(ρ) ≥ c_ε ρ` suffices because
`w ≥ K log₂ n` is assumed with `K` at our disposal. Here it follows from
`(1 - ρ) ^ 4 < ρ (2 - 3 ρ) ^ 3` on `(3 / 20, 1 / 2)`, which makes `γ` strictly decreasing there to
`γ(1 / 2) = 0`, and from elementary logarithm bounds on `(0, 3 / 20]`.

## Main definitions

* `Cslib.Code.PuncturedBallFourierBounds`: the moment and tail bounds of Lemma 3.1 of
  [Saglam2027] for one `n` and `w`.
* `Cslib.Code.ksGamma`, `Cslib.Code.ksTailExponent`: the exponents of the Kirshner–Samorodnitsky
  bounds, in nats.
* `Cslib.Code.KSThirdMomentBound`, `Cslib.Code.KSTailBound`: the imported Kirshner–Samorodnitsky
  bounds, as hypotheses.

## Main results

* `Cslib.Code.sum_charSum_sq`: Parseval, `∑_y charSum B y ^ 2 = 2 ^ n |B|`.
* `Cslib.Code.exists_mul_le_ksGamma`: `γ(ρ) ≥ c ρ` on `(0, 1 / 2 - ε]`.
* `Cslib.Code.ksTailExponent_le`: `T(ρ, y) ≤ h(ρ) - 2 ρ y`.
* `Cslib.Code.exists_puncturedBallFourierBounds_of_ks`: Lemma 3.1 of [Saglam2027] from the
  Kirshner–Samorodnitsky bounds.

## References

* [M. Saglam, *Linear codes exceeding the Gilbert–Varshamov bound*][Saglam2027], STOC 2027
  submission 1516, Lemma 3.1 and Appendix A.
* [N. Kirshner and A. Samorodnitsky, *A moment ratio bound for polynomials and some extremal
  properties of Krawtchouk polynomials and Hamming spheres*][KirshnerSamorodnitsky2021],
  Corollary 1.4 and Theorem 1.5, as quoted in [Saglam2027, Appendix A].
-/

public section

namespace Cslib.Code

open Finset Matrix Real Set

section Parseval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Parseval for `charSum`**: `∑_y charSum B y ^ 2 = 2 ^ n |B|`, so `𝔼_y μ̂(y) ^ 2 = 1 / |B|` for
`μ̂ = charSum B / |B|`. -/
theorem sum_charSum_sq (B : Finset (ι → ZMod 2)) :
    ∑ y, charSum B y ^ 2 = 2 ^ Fintype.card ι * #B := by
  have hsq (y) : charSum B y ^ 2 = ∑ x ∈ B, ∑ x' ∈ B, (-1 : ℝ) ^ (y ⬝ᵥ (x + x')).val := by
    rw [sq, charSum, sum_mul_sum]
    exact sum_congr rfl fun x _ => sum_congr rfl fun x' _ => by
      rw [dotProduct_add, ZMod.neg_one_pow_val_add]
  simp_rw [hsq]
  rw [sum_comm]
  refine (sum_congr rfl fun x hx => ?_).trans (by rw [sum_const, nsmul_eq_mul, mul_comm])
  rw [sum_comm]
  simp_rw [sum_neg_one_pow_val_dotProduct]
  have heq (x' : ι → ZMod 2) : x + x' = 0 ↔ x = x' := by
    have hneg : -x' = x' := funext fun i => ZMod.neg_eq_self_mod_two _
    rw [← sub_eq_zero (a := x), sub_eq_add_neg, hneg]
  simp [heq, hx]

/-- `μ̂ = charSum B / |B|` is the Fourier expansion with coefficients `1 / |B|` on `B`. -/
theorem charSum_div_card_eq (B : Finset (ι → ZMod 2)) (y : ι → ZMod 2) :
    charSum B y / #B = ∑ x, (if x ∈ B then (#B : ℝ)⁻¹ else 0) * (-1 : ℝ) ^ (y ⬝ᵥ x).val := by
  simp only [ite_mul, zero_mul]
  rw [sum_ite_mem, Finset.univ_inter, charSum, sum_div]
  exact sum_congr rfl fun x _ => by ring

end Parseval

/-- **Lemma 3.1 of [Saglam2027]** for one `n` and `w`, with moment constant `C`. Let
`B = {x ∈ 𝔽₂ⁿ | x ≠ 0, |x| < w + 1}` and `μ̂ = charSum B / |B|`. Then
`𝔼_y |μ̂(y)| ^ 3 ≤ C / (|B| n ^ 3)` and
`Pr_y[|μ̂(y)| > 1 / n] ≤ 2 ^ (-n + 2 n (log₂ n / w) log₂ (e w / log₂ n))`, with expectations and
probabilities over uniform `y ∈ 𝔽₂ⁿ`. Saglam states the moment bound as `O(1 / (V n ^ 3))`. -/
@[expose] def PuncturedBallFourierBounds (n w : ℕ) (C : ℝ) : Prop :=
  let B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1}
  (∑ y, |charSum B y / #B| ^ 3) / 2 ^ n ≤ C / (#B * n ^ 3) ∧
    (#{y | 1 / (n : ℝ) < |charSum B y / #B|} : ℝ) / 2 ^ n ≤
      (2 : ℝ) ^ (-(n : ℝ) + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n))

section Exponents

/-- The exponent `γ` of the Kirshner–Samorodnitsky third-moment bound as specialized in
[Saglam2027, Appendix A], in nats:
`γ(ρ) = -(ρ / 2) log ρ - 2 (1 - ρ) log (1 - ρ) - log 2 + (1 - 3 ρ / 2) log (2 - 3 ρ)`. Saglam's
`γ` uses base-`2` logarithms and equals this value divided by `log 2`. -/
noncomputable def ksGamma (ρ : ℝ) : ℝ :=
  -(ρ / 2 * log ρ) - 2 * (1 - ρ) * log (1 - ρ) - log 2 + (1 - 3 * ρ / 2) * log (2 - 3 * ρ)

/-- The exponent vanishes at the end of the range: `γ(1 / 2) = 0`. -/
theorem ksGamma_half : ksGamma (1 / 2) = 0 := by
  have h : (2 : ℝ) - 3 * (1 / 2) = 1 / 2 := by norm_num
  rw [ksGamma, h, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, log_inv]
  ring

/-- The derivative `γ'(ρ) = (4 log (1 - ρ) - log ρ - 3 log (2 - 3 ρ)) / 2`. -/
private theorem hasDerivAt_ksGamma {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1 / 2) :
    HasDerivAt ksGamma ((4 * log (1 - ρ) - log ρ - 3 * log (2 - 3 * ρ)) / 2) ρ := by
  have ha : (1 - ρ) ≠ 0 := by linarith
  have hb : (2 - 3 * ρ) ≠ 0 := by linarith
  have e1 := ((hasDerivAt_id ρ).div_const 2).mul (hasDerivAt_log h0.ne')
  have e2 := (((hasDerivAt_const ρ (1 : ℝ)).sub (hasDerivAt_id ρ)).const_mul 2).mul
    (((hasDerivAt_const ρ (1 : ℝ)).sub (hasDerivAt_id ρ)).log ha)
  have e3 := ((hasDerivAt_const ρ (1 : ℝ)).sub ((hasDerivAt_id ρ).const_mul 3 |>.div_const 2)).mul
    (((hasDerivAt_const ρ (2 : ℝ)).sub ((hasDerivAt_id ρ).const_mul 3)).log hb)
  have := ((e1.neg.sub e2).sub (hasDerivAt_const ρ (log 2))).add e3
  convert this using 1
  · ext x; simp [ksGamma]
  · simp only [id, Pi.sub_apply]
    have k1 : (1 - 3 * ρ / 2) * ((0 - 3 * 1) / (2 - 3 * ρ)) = -3 / 2 := by field_simp; ring
    have k2 : 2 * (1 - ρ) * ((0 - 1) / (1 - ρ)) = -2 := by field_simp; ring
    have k3 : ρ / 2 * ρ⁻¹ = 1 / 2 := by field_simp
    linear_combination k3 + k2 - k1

/-- `(1 - ρ) ^ 4 < ρ (2 - 3 ρ) ^ 3` on `(3 / 20, 1 / 2)`: the difference is
`(2 ρ - 1) (14 ρ ^ 3 - 22 ρ ^ 2 + 10 ρ - 1)` and the cubic is positive there. -/
private theorem pow_four_lt {ρ : ℝ} (h0 : 3 / 20 < ρ) (h1 : ρ < 1 / 2) :
    (1 - ρ) ^ 4 < ρ * (2 - 3 * ρ) ^ 3 := by
  set t := 1 / 2 - ρ
  set s := ρ - 3 / 20
  have ht0 : 0 < t := sub_pos.2 h1
  have hs0 : 0 < s := sub_pos.2 h0
  have hdiff : 4000 * (ρ * (2 - 3 * ρ) ^ 3 - (1 - ρ) ^ 4) =
      2 * t * (s * (56000 * t ^ 2 + 23600 * t + 2260) + 209) := by
    simp only [t, s]; ring
  have hpos : 0 < 2 * t * (s * (56000 * t ^ 2 + 23600 * t + 2260) + 209) := by positivity
  rw [← hdiff] at hpos
  exact sub_pos.mp (pos_of_mul_pos_right hpos (by norm_num))

/-- `γ` is strictly decreasing on `[3 / 20, 1 / 2]`, because
`γ'(ρ) = log ((1 - ρ) ^ 4 / (ρ (2 - 3 ρ) ^ 3)) / 2` is negative there. -/
theorem strictAntiOn_ksGamma : StrictAntiOn ksGamma (Icc (3 / 20) (1 / 2)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _) ?_ ?_
  · intro x hx
    unfold ksGamma
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := linarith [hx.1, hx.2]))
  · intro x hx
    rw [interior_Icc] at hx
    have h0 : 0 < x := by linarith [hx.1]
    have hp1 : 0 < 1 - x := by linarith [hx.2]
    have hp2 : 0 < 2 - 3 * x := by linarith [hx.2]
    have hlog := log_lt_log (pow_pos hp1 4) (pow_four_lt hx.1 hx.2)
    rw [log_pow, log_mul h0.ne' (pow_pos hp2 3).ne', log_pow] at hlog
    push_cast at hlog
    rw [(hasDerivAt_ksGamma h0 hx.2).deriv, div_lt_iff₀ two_pos, zero_mul]
    linarith only [hlog]

/-- For `0 < ρ ≤ 3 / 20`, `ρ / 20 ≤ γ(ρ)`. -/
private theorem div_le_ksGamma_of_le {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 3 / 20) :
    ρ / 20 ≤ ksGamma ρ := by
  have hρ1 : 0 < 1 - ρ := by linarith only [h1]
  have ha : 0 < 1 - 3 * ρ / 2 := by linarith only [h1]
  -- `log (1 - ρ) ≤ -ρ`
  have l1 : log (1 - ρ) ≤ -ρ := by linarith only [log_le_sub_one_of_pos hρ1]
  -- `(1 - a) log (1 - a) ≥ -a`
  have l2 : -(3 * ρ / 2) ≤ (1 - 3 * ρ / 2) * log (1 - 3 * ρ / 2) := by
    have e : (1 - 3 * ρ / 2) * (1 - (1 - 3 * ρ / 2)⁻¹) = -(3 * ρ / 2) := by
      rw [mul_sub, mul_inv_cancel₀ ha.ne']; ring
    exact e ▸ mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos ha) ha.le
  have hsplit : log (2 - 3 * ρ) = log 2 + log (1 - 3 * ρ / 2) := by
    rw [← log_mul two_ne_zero ha.ne']; ring_nf
  -- `-log ρ ≥ log (20 / 3) ≥ 3 log 2 - 1 / 5`
  have l3 : 3 * log 2 - 1 / 5 ≤ -log ρ := by
    have hl : log (20 / 3) ≤ -log ρ := by
      rw [← log_inv]
      exact log_le_log (by norm_num) (by rw [le_inv_comm₀ (by norm_num) h0]; linarith only [h1])
    have h56 : -(1 / 5 : ℝ) ≤ log (5 / 6) :=
      (by norm_num : -(1 / 5 : ℝ) ≤ 1 - (5 / 6 : ℝ)⁻¹).trans
        (one_sub_inv_le_log_of_pos (by norm_num))
    have h20 : log (20 / 3) = 3 * log 2 + log (5 / 6) := by
      rw [show (20 / 3 : ℝ) = 2 ^ 3 * (5 / 6) by norm_num, log_mul (by norm_num) (by norm_num),
        log_pow]; norm_num
    linarith only [hl, h56, h20]
  have hm1 : 2 * (1 - ρ) * log (1 - ρ) ≤ 2 * (1 - ρ) * (-ρ) :=
    mul_le_mul_of_nonneg_left l1 (mul_nonneg zero_le_two hρ1.le)
  have hm3 : ρ / 2 * (3 * log 2 - 1 / 5) ≤ ρ / 2 * (-log ρ) :=
    mul_le_mul_of_nonneg_left l3 (div_nonneg h0.le zero_le_two)
  have hρ2 : ρ * ρ ≤ 3 / 20 * ρ := mul_le_mul_of_nonneg_right h1 h0.le
  rw [ksGamma, hsplit]
  linarith only [hm1, hm3, l2, hρ2, h0]

/-- **Positivity of the exponent** [Saglam2027, Appendix A]: for every `ε > 0` there is `c > 0` with
`c ρ ≤ γ(ρ)` for `0 < ρ ≤ 1 / 2 - ε`. -/
theorem exists_mul_le_ksGamma {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ ρ, 0 < ρ → ρ ≤ 1 / 2 - ε → c * ρ ≤ ksGamma ρ := by
  set ρ₀ := max (1 / 2 - ε) (3 / 20) with hρ₀
  have hρ₀m : ρ₀ ∈ Icc (3 / 20 : ℝ) (1 / 2) :=
    ⟨le_max_right _ _, max_le (sub_le_self _ hε.le) (by norm_num)⟩
  have hρ₀lt : ρ₀ < 1 / 2 := max_lt (sub_lt_self _ hε) (by norm_num)
  have hpos : 0 < ksGamma ρ₀ := by
    have := strictAntiOn_ksGamma hρ₀m ⟨by norm_num, le_rfl⟩ hρ₀lt
    rwa [ksGamma_half] at this
  refine ⟨min (1 / 20) (2 * ksGamma ρ₀), lt_min (by norm_num) (mul_pos two_pos hpos),
    fun ρ h0 h1 => ?_⟩
  rcases le_total ρ (3 / 20) with hs | hl
  · linarith only [mul_le_mul_of_nonneg_right (min_le_left (1 / 20) (2 * ksGamma ρ₀)) h0.le,
      div_le_ksGamma_of_le h0 hs]
  · have hρhalf : ρ ≤ 1 / 2 := h1.trans (sub_le_self _ hε.le)
    linarith only [mul_le_mul_of_nonneg_right (min_le_right (1 / 20) (2 * ksGamma ρ₀)) h0.le,
      mul_le_mul_of_nonneg_left hρhalf (mul_nonneg zero_le_two hpos.le),
      strictAntiOn_ksGamma.antitoneOn ⟨hl, hρhalf⟩ hρ₀m (h1.trans (le_max_left _ _))]

/-- The integrand `log ((1 - 2 ρ + √((1 - 2 ρ) ^ 2 - 4 z (1 - z))) / (2 (1 - z)))` of the
Kirshner–Samorodnitsky tail exponent [Saglam2027, Appendix A], in nats. -/
noncomputable def ksTailIntegrand (ρ z : ℝ) : ℝ :=
  log ((1 - 2 * ρ + √((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z))) / (2 * (1 - z)))

/-- The Kirshner–Samorodnitsky tail exponent `T(ρ, y) = h(ρ) + ∫_0^y ksTailIntegrand ρ z dz`
[Saglam2027, Appendix A], in nats; Saglam's `T` is this value divided by `log 2`. -/
noncomputable def ksTailExponent (ρ y : ℝ) : ℝ :=
  binEntropy ρ + ∫ z in (0 : ℝ)..y, ksTailIntegrand ρ z

/-- The argument of the logarithm in the tail integrand lies in `(0, 1 - 2 ρ]` for
`0 ≤ z ≤ 1 / 2`. -/
private theorem ksTailIntegrand_arg {ρ z : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2) (hz0 : 0 ≤ z)
    (hz : z ≤ 1 / 2) :
    0 < (1 - 2 * ρ + √((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z))) / (2 * (1 - z)) ∧
      (1 - 2 * ρ + √((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z))) / (2 * (1 - z)) ≤ 1 - 2 * ρ := by
  have h1ρ : 0 < 1 - 2 * ρ := sub_pos.mpr ((lt_div_iff₀' two_pos).mp hρ)
  have h1z : 0 ≤ 1 - 2 * z := sub_nonneg.mpr ((le_div_iff₀' two_pos).mp hz)
  have hd : 0 < 2 * (1 - z) := mul_pos two_pos (sub_pos.mpr (hz.trans_lt (by norm_num)))
  constructor
  · exact div_pos (add_pos_of_pos_of_nonneg h1ρ (sqrt_nonneg _)) hd
  · rw [div_le_iff₀ hd]
    have hs : √((1 - 2 * ρ) ^ 2 - 4 * z * (1 - z)) ≤ (1 - 2 * ρ) * (1 - 2 * z) := by
      rw [sqrt_le_left (mul_nonneg h1ρ.le h1z)]
      have h1 : (1 - 2 * ρ) ^ 2 ≤ 1 :=
        pow_le_one₀ h1ρ.le (sub_le_self _ (mul_nonneg zero_le_two hρ0))
      have h2 : 0 ≤ z * (1 - z) := mul_nonneg hz0 (sub_nonneg.mpr (hz.trans (by norm_num)))
      linarith [mul_le_mul_of_nonneg_right h1 h2]
    linarith only [hs]

/-- **The tail exponent bound** [Saglam2027, Appendix A]: the integrand is at most
`log (1 - 2 ρ) ≤ -2 ρ`, so `T(ρ, y) ≤ h(ρ) - 2 ρ y` for `0 ≤ y ≤ 1 / 2`. -/
theorem ksTailExponent_le {ρ y : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 2) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    ksTailExponent ρ y ≤ binEntropy ρ - 2 * ρ * y := by
  have hcont : ContinuousOn (ksTailIntegrand ρ) (Icc 0 y) := by
    refine ContinuousOn.log ?_ fun z hz => (ksTailIntegrand_arg hρ0 hρ hz.1 (hz.2.trans hy)).1.ne'
    refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
    exact (mul_pos two_pos (sub_pos.mpr ((hz.2.trans hy).trans_lt (by norm_num)))).ne'
  have hint : IntervalIntegrable (ksTailIntegrand ρ) MeasureTheory.volume 0 y :=
    (hcont.mono (by rw [uIcc_of_le hy0])).intervalIntegrable
  have hle : ∫ z in (0 : ℝ)..y, ksTailIntegrand ρ z ≤ ∫ _ in (0 : ℝ)..y, (-2 * ρ) := by
    refine intervalIntegral.integral_mono_on hy0 hint intervalIntegrable_const fun z hz => ?_
    obtain ⟨hpos, hle⟩ := ksTailIntegrand_arg hρ0 hρ hz.1 (hz.2.trans hy)
    calc ksTailIntegrand ρ z ≤ log (1 - 2 * ρ) := log_le_log hpos hle
      _ ≤ 1 - 2 * ρ - 1 := log_le_sub_one_of_pos (sub_pos.mpr ((lt_div_iff₀' two_pos).mp hρ))
      _ = -2 * ρ := by ring
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
  rw [ksTailExponent]
  linarith only [hle]

/-- `ε ^ 2 ≤ 1 / 2 - √(ρ (1 - ρ))` for `0 ≤ ρ ≤ 1 / 2 - ε`. -/
theorem sq_le_half_sub_sqrt {ε ρ : ℝ} (hε : 0 ≤ ε) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2 - ε) :
    ε ^ 2 ≤ 1 / 2 - √(ρ * (1 - ρ)) := by
  have hεsq : ε ^ 2 ≤ 1 / 2 :=
    (pow_le_pow_left₀ hε ((le_sub_comm.mp hρ).trans (sub_le_self _ hρ0)) 2).trans (by norm_num)
  rw [le_sub_comm, sqrt_le_left (sub_nonneg.mpr hεsq)]
  linarith only [pow_le_pow_left₀ hε (le_sub_comm.mp hρ) 2, sq_nonneg (ε ^ 2)]

end Exponents

section KirshnerSamorodnitsky

/-- **The Kirshner–Samorodnitsky third-moment bound** [KirshnerSamorodnitsky2021, Corollary 1.4],
in the specialization quoted in [Saglam2027, Appendix A], **imported as a hypothesis**: for
`0 < w`, `2 w < n` and `ρ = w / n`, every `f(y) = ∑_x a x (-1) ^ (y ⬝ᵥ x)` with `a x = 0` for
`|x| > w` (a polynomial of degree at most `w` in the signs `(-1) ^ y_i`) satisfies
`𝔼|f| ^ 3 ≤ (𝔼 f ^ 2) ^ (3 / 2) exp (n (h(ρ) / 2 - γ(ρ)))`. -/
def KSThirdMomentBound (n w : ℕ) : Prop :=
  0 < w → 2 * w < n → ∀ a : (Fin n → ZMod 2) → ℝ, (∀ x, w < hammingNorm x → a x = 0) →
    let f : (Fin n → ZMod 2) → ℝ := fun y => ∑ x, a x * (-1 : ℝ) ^ (y ⬝ᵥ x).val
    (∑ y, |f y| ^ 3) / 2 ^ n ≤
      ((∑ y, f y ^ 2) / 2 ^ n) ^ (3 / 2 : ℝ) * exp (n * (binEntropy (w / n) / 2 - ksGamma (w / n)))

/-- **The Kirshner–Samorodnitsky tail bound** [KirshnerSamorodnitsky2021, Theorem 1.5], in the
specialization quoted in [Saglam2027, Appendix A], **imported as a hypothesis**: for `0 < w`,
`2 w < n`, `ρ = w / n` and every `f` of degree at most `w` as in `KSThirdMomentBound`, every
integer `k` with `k / n ≤ 1 / 2 - √(ρ (1 - ρ))` satisfies
`Pr[|f| > √(𝔼 f ^ 2) exp (n (T(ρ, k / n) - h(ρ) / 2))] ≤ exp (n (h(k / n) - log 2))`.
Saglam and Kirshner–Samorodnitsky state the event with `≥`. The strict event used here is
smaller, so this hypothesis is weaker. The weakening, like the restriction `0 < w`, is needed:
as printed, Theorem 1.5 fails at degree `0`. For `f ≡ 1` and `k = 0` the threshold is
`‖f‖₂ = 1`, so the `≥` event has probability `1 > 2 ^ (-n)`. -/
def KSTailBound (n w : ℕ) : Prop :=
  0 < w → 2 * w < n → ∀ a : (Fin n → ZMod 2) → ℝ, (∀ x, w < hammingNorm x → a x = 0) →
    ∀ k : ℕ, (k : ℝ) / n ≤ 1 / 2 - √(w / n * (1 - w / n)) →
    let f : (Fin n → ZMod 2) → ℝ := fun y => ∑ x, a x * (-1 : ℝ) ^ (y ⬝ᵥ x).val
    (#{y | √((∑ y, f y ^ 2) / 2 ^ n) *
        exp (n * (ksTailExponent (w / n) (k / n) - binEntropy (w / n) / 2)) < |f y|} : ℝ) /
      2 ^ n ≤ exp (n * (binEntropy (k / n) - log 2))

variable {n w : ℕ}

/-- Facts about the punctured ball used by both estimates: the Fourier coefficients of `μ̂` vanish
above weight `w`, `𝔼 μ̂ ^ 2 = 1 / V`, and `√(exp (n h(w / n)) / V) ≤ √(n + 1)`. -/
private theorem puncturedBall_facts (hw0 : 0 < w) (hwn : w ≤ n) :
    let B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1}
    (0 : ℝ) < #B ∧
    (∀ x, w < hammingNorm x → (if x ∈ B then (#B : ℝ)⁻¹ else 0) = 0) ∧
    (∑ y, (charSum B y / #B) ^ 2) / 2 ^ n = (#B : ℝ)⁻¹ ∧
    √((#B : ℝ)⁻¹) * √(exp (n * binEntropy (w / n))) ≤ √(n + 1) := by
  intro B
  have hcard : (#B : ℝ) = ∑ i ∈ Ico 1 (w + 1), (n.choose i : ℝ) := by
    simp only [B]; rw [card_filter_ne_zero_hammingNorm_lt]; push_cast; rfl
  have hchoose : (n.choose w : ℝ) ≤ #B := by
    rw [hcard]
    exact single_le_sum (f := fun i => (n.choose i : ℝ)) (fun i _ => by positivity)
      (mem_Ico.2 ⟨hw0, by omega⟩)
  have hpos : (0 : ℝ) < #B :=
    lt_of_lt_of_le (by exact_mod_cast Nat.choose_pos hwn) hchoose
  refine ⟨hpos, fun x hx => ?_, ?_, ?_⟩
  · simp only [B, ite_eq_right_iff, mem_filter]
    omega
  · simp_rw [div_pow, ← sum_div, sum_charSum_sq B, Fintype.card_fin]
    field_simp
  · rw [← sqrt_mul (inv_nonneg.2 hpos.le)]
    refine sqrt_le_sqrt ?_
    rw [inv_mul_le_iff₀ hpos]
    calc exp (n * binEntropy (w / n)) ≤ (n + 1) * n.choose w :=
          exp_mul_binEntropy_le_succ_mul_choose hwn
      _ ≤ #B * (n + 1) := by rw [mul_comm]; gcongr

/-- `exp (-(t log n)) = n ^ (-t)` as an inverse power for natural `t`. -/
private theorem exp_neg_mul_log (t : ℕ) {x : ℝ} (hx : 0 < x) :
    exp (-(t * log x)) = (x ^ t)⁻¹ := by
  rw [exp_neg, ← log_pow, exp_log (by positivity)]

/-- `log n ≤ log₂ n` for `n ≥ 1`. -/
private theorem log_le_logb_two {x : ℝ} (hx : 1 ≤ x) : log x ≤ logb 2 x := by
  rw [logb, le_div_iff₀ (log_pos one_lt_two)]
  exact mul_le_of_le_one_right (log_nonneg hx) (log_two_lt_d9.le.trans (by norm_num))

/-- **The moment estimate of Lemma 3.1** [Saglam2027, Appendix A] from the Kirshner–Samorodnitsky
third-moment bound: if `γ(ρ) ≥ c ρ` at `ρ = w / n` and `w ≥ K log₂ n` with `c K ≥ 4`, then
`𝔼|μ̂| ^ 3 ≤ 2 / (V n ^ 3)`. -/
theorem moment_le_of_ksThirdMomentBound (hKS : KSThirdMomentBound n w) (hw0 : 0 < w)
    (hwn : 2 * w < n) {c K : ℝ} (hc0 : 0 < c) (hc : c * (w / n) ≤ ksGamma (w / n))
    (hcK : 4 ≤ c * K)
    (hK : K * logb 2 n ≤ w) :
    let B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1}
    (∑ y, |charSum B y / #B| ^ 3) / 2 ^ n ≤ 2 / (#B * n ^ 3) := by
  intro B
  obtain ⟨hV, hsupp, hpar, hsq⟩ := puncturedBall_facts (n := n) hw0 (by omega)
  have h := hKS hw0 hwn _ hsupp
  dsimp only at h
  simp_rw [← charSum_div_card_eq] at h
  rw [hpar] at h
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hn
  -- `(1 / V) ^ (3 / 2) = (1 / V) √(1 / V)`
  have hr : ((#B : ℝ)⁻¹) ^ (3 / 2 : ℝ) = (#B : ℝ)⁻¹ * √((#B : ℝ)⁻¹) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, rpow_add (inv_pos.2 hV), rpow_one,
      sqrt_eq_rpow]
  -- `n γ(ρ) ≥ 4 log n`
  have hγ : 4 * log n ≤ n * ksGamma (w / n) := by
    have h1 : c * w ≤ n * ksGamma (w / n) := by
      have := mul_le_mul_of_nonneg_left hc hnpos.le
      rwa [show (n : ℝ) * (c * (w / n)) = c * w by field_simp] at this
    have hlog := log_le_logb_two hn
    linarith only [hlog, h1, mul_le_mul_of_nonneg_right hcK ((log_nonneg hn).trans hlog),
      mul_le_mul_of_nonneg_left hK hc0.le]
  have hexp : exp (-(n * ksGamma (w / n))) ≤ ((n : ℝ) ^ 4)⁻¹ := by
    rw [← exp_neg_mul_log 4 hnpos]
    push_cast
    exact exp_le_exp.2 (neg_le_neg hγ)
  have hsplit : exp (n * (binEntropy (w / n) / 2 - ksGamma (w / n))) =
      √(exp (n * binEntropy (w / n))) * exp (-(n * ksGamma (w / n))) := by
    rw [← exp_half, ← exp_add]; ring_nf
  rw [hr, hsplit] at h
  have hsqn : √((n : ℝ) + 1) ≤ 2 * n := by
    rw [sqrt_le_left (mul_nonneg zero_le_two hnpos.le)]
    have hn2 : (n : ℝ) ≤ (n : ℝ) * n := le_mul_of_one_le_right hnpos.le hn
    linarith only [hn, hn2, show (2 * (n : ℝ)) ^ 2 = 4 * ((n : ℝ) * n) by ring]
  calc (∑ y, |charSum B y / #B| ^ 3) / 2 ^ n
      ≤ (#B : ℝ)⁻¹ * (√((#B : ℝ)⁻¹) * √(exp (n * binEntropy (w / n)))) *
          exp (-(n * ksGamma (w / n))) := by
        exact h.trans_eq (by ring)
    _ ≤ (#B : ℝ)⁻¹ * (2 * n) * ((n : ℝ) ^ 4)⁻¹ :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hsq.trans hsqn) (inv_nonneg.2 hV.le)) hexp
          (exp_pos _).le (mul_nonneg (inv_nonneg.2 hV.le) (mul_nonneg zero_le_two hnpos.le))
    _ = 2 / (#B * n ^ 3) := by field_simp

/-- The tail bound of Lemma 3.1 in nats: with `u = log₂ n / w`,
`2 ^ (-n + 2 n u log₂ (e w / log₂ n)) = exp (n (2 u log (e / u) - log 2))`. -/
theorem two_rpow_tail_eq (n w : ℝ) :
    (2 : ℝ) ^ (-n + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n)) =
      exp (n * (2 * (logb 2 n / w) * log (exp 1 / (logb 2 n / w)) - log 2)) := by
  have hl : log 2 ≠ 0 := (log_pos one_lt_two).ne'
  rw [← div_div_eq_mul_div, rpow_def_of_pos two_pos]
  congr 1
  generalize logb 2 n / w = u
  rw [logb]
  field_simp
  ring

/-- The threshold of the tail bound is at most `1 / n`: with `T(ρ, y) ≤ h(ρ) - 2 ρ y`,
`√(1 / V) exp (n (T(ρ, y) - h(ρ) / 2)) ≤ √(1 / V) √(exp (n h(ρ))) exp (-2 w y)`, and
`w y ≥ log n`. -/
private theorem threshold_le {n w y V : ℝ} (hn : 2 ≤ n) (hρ0 : 0 ≤ w / n)
    (hρ : w / n < 1 / 2) (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) (hwy : log n ≤ w * y)
    (hsq : √V⁻¹ * √(exp (n * binEntropy (w / n))) ≤ √(n + 1)) :
    √V⁻¹ * exp (n * (ksTailExponent (w / n) y - binEntropy (w / n) / 2)) ≤ 1 / n := by
  have hnpos : 0 < n := two_pos.trans_le hn
  have hT := ksTailExponent_le hρ0 hρ hy0 hy
  have hexp : exp (n * (ksTailExponent (w / n) y - binEntropy (w / n) / 2)) ≤
      √(exp (n * binEntropy (w / n))) * exp (-(2 * log n)) := by
    rw [← exp_half, ← exp_add]
    refine exp_le_exp.2 ?_
    have hwy' : n * (2 * (w / n) * y) = 2 * (w * y) := by field_simp
    have hm := mul_le_mul_of_nonneg_left hT hnpos.le
    rw [mul_sub, hwy'] at hm
    linarith only [hm, hwy]
  have hn2 : exp (-(2 * log n)) = (n ^ 2)⁻¹ := by
    rw [← Nat.cast_two]; exact exp_neg_mul_log 2 hnpos
  have hsqn : √(n + 1) ≤ n := by
    rw [sqrt_le_left hnpos.le]
    have h2 : 2 * n ≤ n ^ 2 := by rw [sq]; exact mul_le_mul_of_nonneg_right hn hnpos.le
    linarith only [hn, h2]
  calc √V⁻¹ * exp (n * (ksTailExponent (w / n) y - binEntropy (w / n) / 2))
      ≤ √V⁻¹ * (√(exp (n * binEntropy (w / n))) * (n ^ 2)⁻¹) := by
        rw [← hn2]; exact mul_le_mul_of_nonneg_left hexp (sqrt_nonneg _)
    _ = √V⁻¹ * √(exp (n * binEntropy (w / n))) * (n ^ 2)⁻¹ := by ring
    _ ≤ n * (n ^ 2)⁻¹ := mul_le_mul_of_nonneg_right (hsq.trans hsqn) (inv_nonneg.2 (sq_nonneg n))
    _ = 1 / n := by field_simp

/-- The tail probability of Lemma 3.1: with `u = log₂ n / w ≤ 1` and `u ≤ y ≤ 2 u < 1`,
`exp (n (h(y) - log 2)) ≤ 2 ^ (-n + 2 n u log₂ (e w / log₂ n))`, since
`h(y) ≤ y log (e / y) ≤ 2 u log (e / u)`. -/
private theorem exp_binEntropy_le_rpow {n w y : ℝ} (hw : 0 < w) (hlg : 0 < logb 2 n)
    (hu1 : logb 2 n / w ≤ 1) (hy1 : logb 2 n / w ≤ y) (hy2 : y ≤ 2 * (logb 2 n / w))
    (hy : y < 1) (hn : 0 ≤ n) :
    exp (n * (binEntropy y - log 2)) ≤
      (2 : ℝ) ^ (-n + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n)) := by
  set u := logb 2 n / w with hu
  have hu0 : 0 < u := div_pos hlg hw
  have hy0 : 0 < y := hu0.trans_le hy1
  have hlog0 : 0 ≤ log (exp 1 / u) := by
    refine log_nonneg ?_
    rw [le_div_iff₀ hu0, one_mul]
    exact hu1.trans (by linarith only [add_one_le_exp (1 : ℝ)])
  have hent : binEntropy y ≤ 2 * u * log (exp 1 / u) := by
    calc binEntropy y ≤ y * log (exp 1 / y) := binEntropy_le_mul_log_exp_one_div hy0 hy
      _ ≤ y * log (exp 1 / u) :=
        mul_le_mul_of_nonneg_left (log_le_log (div_pos (exp_pos 1) hy0)
          (div_le_div_of_nonneg_left (exp_pos 1).le hu0 hy1)) hy0.le
      _ ≤ 2 * u * log (exp 1 / u) := mul_le_mul_of_nonneg_right hy2 hlog0
  rw [two_rpow_tail_eq, ← hu]
  exact exp_le_exp.2 (mul_le_mul_of_nonneg_left (sub_le_sub_right hent (log 2)) hn)

/-- **The tail estimate of Lemma 3.1** [Saglam2027, Appendix A] from the Kirshner–Samorodnitsky
tail bound, with `k = ⌈n log₂ n / w⌉` and `y = k / n`: if `ρ = w / n ≤ 1 / 2 - ε`,
`w ≥ K log₂ n` with `K ≥ 2 / ε ^ 2`, and `n ≥ 2 / ε ^ 2`, then
`Pr[|μ̂| > 1 / n] ≤ 2 ^ (-n + 2 n (log₂ n / w) log₂ (e w / log₂ n))`. -/
theorem tail_le_of_ksTailBound (hKS : KSTailBound n w) (hw0 : 0 < w) {ε K : ℝ} (hε : 0 < ε)
    (hρ : (w : ℝ) ≤ (1 / 2 - ε) * n) (hK : 2 / ε ^ 2 ≤ K) (hnε : 2 / ε ^ 2 ≤ n)
    (hKw : K * logb 2 n ≤ w) :
    let B : Finset (Fin n → ZMod 2) := {x | x ≠ 0 ∧ hammingNorm x < w + 1}
    (#{y | 1 / (n : ℝ) < |charSum B y / #B|} : ℝ) / 2 ^ n ≤
      (2 : ℝ) ^ (-(n : ℝ) + 2 * n * (logb 2 n / w) * logb 2 (exp 1 * w / logb 2 n)) := by
  intro B
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw0
  have hε2pos : 0 < 2 / ε ^ 2 := div_pos two_pos (sq_pos_of_pos hε)
  have hnpos : (0 : ℝ) < n := hε2pos.trans_le hnε
  have hwn' : (2 * w : ℝ) < n := by linarith only [hρ, mul_pos hε hnpos]
  have hwn : 2 * w < n := by exact_mod_cast hwn'
  obtain ⟨hV, hsupp, hpar, hsq⟩ := puncturedBall_facts (n := n) hw0 (by omega)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hlg : 1 ≤ logb 2 n := by rw [le_logb_iff_rpow_le one_lt_two hnpos, rpow_one]; exact hn2
  have hKpos : 0 < K := hε2pos.trans_le hK
  have hwpos : (0 : ℝ) < w := zero_lt_one.trans_le hw1
  have hlgpos : 0 < logb 2 n := zero_lt_one.trans_le hlg
  have hu0 : 0 < logb 2 n / w := div_pos hlgpos hwpos
  have huK : logb 2 n / w ≤ ε ^ 2 / 2 := by
    have h1 : logb 2 n / w ≤ 1 / K := by
      rw [div_le_div_iff₀ hwpos hKpos, one_mul, mul_comm]; exact hKw
    exact h1.trans ((one_div_le_one_div_of_le hε2pos hK).trans_eq (one_div_div _ _))
  have hnu : 1 / (n : ℝ) ≤ logb 2 n / w := by
    rw [div_le_div_iff₀ hnpos hwpos, one_mul]
    linarith only [hwn', hw1, mul_le_mul_of_nonneg_right hlg hnpos.le]
  have hεhalf : ε < 1 / 2 :=
    sub_pos.mp (pos_of_mul_pos_left (hwpos.trans_le hρ) hnpos.le)
  have hε1 : ε ^ 2 < 1 / 4 := (pow_lt_pow_left₀ hεhalf hε.le two_ne_zero).trans_eq (by norm_num)
  -- the parameter `y = ⌈n u⌉ / n`
  have hky1 : logb 2 n / w ≤ (⌈n * (logb 2 n / w)⌉₊ : ℝ) / n := by
    rw [le_div_iff₀ hnpos, mul_comm]; exact Nat.le_ceil _
  have hky2 : (⌈n * (logb 2 n / w)⌉₊ : ℝ) / n ≤ 2 * (logb 2 n / w) := by
    rw [div_le_iff₀ hnpos]
    have hceil := Nat.ceil_lt_add_one (mul_nonneg hnpos.le hu0.le)
    rw [div_le_iff₀ hnpos] at hnu
    linarith only [hceil, hnu]
  have hy0 : 0 < (⌈n * (logb 2 n / w)⌉₊ : ℝ) / n := hu0.trans_le hky1
  have hyε : (⌈n * (logb 2 n / w)⌉₊ : ℝ) / n ≤ ε ^ 2 :=
    hky2.trans
      ((mul_le_mul_of_nonneg_left huK zero_le_two).trans_eq (mul_div_cancel₀ _ two_ne_zero))
  have hρ0 : 0 ≤ (w : ℝ) / n := div_nonneg hwpos.le hnpos.le
  have hρε : (w : ℝ) / n ≤ 1 / 2 - ε := by rw [div_le_iff₀ hnpos]; exact hρ
  have h := hKS hw0 hwn _ hsupp _ (hyε.trans (sq_le_half_sub_sqrt hε.le hρ0 hρε))
  dsimp only at h
  simp_rw [← charSum_div_card_eq] at h
  rw [hpar] at h
  have hwy : log n ≤ w * ((⌈n * (logb 2 n / w)⌉₊ : ℝ) / n) :=
    (log_le_logb_two (one_le_two.trans hn2)).trans ((mul_div_cancel₀ _ hwpos.ne').symm.trans_le
      (mul_le_mul_of_nonneg_left hky1 hwpos.le))
  have hthr := threshold_le hn2 hρ0 (hρε.trans_lt (sub_lt_self _ hε)) hy0.le
    (hyε.trans (hε1.le.trans (by norm_num))) hwy hsq
  refine le_trans ?_ (exp_binEntropy_le_rpow hwpos hlgpos
    (huK.trans ((div_le_iff₀ two_pos).mpr (hε1.le.trans (by norm_num)))) hky1 hky2
    (hyε.trans_lt (hε1.trans (by norm_num))) hnpos.le)
  refine le_trans (div_le_div_of_nonneg_right ?_ (pow_nonneg zero_le_two n)) h
  refine Nat.cast_le.2 (card_le_card fun y hy => ?_)
  rw [mem_filter] at hy ⊢
  exact ⟨hy.1, hthr.trans_lt hy.2⟩

/-- **Lemma 3.1 of [Saglam2027] from the Kirshner–Samorodnitsky bounds.** For every `ε > 0` there
are `K` and `N` such that for all `n ≥ N` and `K log₂ n ≤ w ≤ (1 / 2 - ε) n`, the
Kirshner–Samorodnitsky bounds at `n` and `w` imply the moment and tail estimates of Lemma 3.1 with
moment constant `C = 2`. -/
theorem exists_puncturedBallFourierBounds_of_ks {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ w : ℕ, K * logb 2 n ≤ w → (w : ℝ) ≤ (1 / 2 - ε) * n →
      KSThirdMomentBound n w → KSTailBound n w → PuncturedBallFourierBounds n w 2 := by
  obtain ⟨c, hc, hγ⟩ := exists_mul_le_ksGamma hε
  refine ⟨max (4 / c) (2 / ε ^ 2), max 2 ⌈2 / ε ^ 2⌉₊, fun n hn w hKw hρ hM hT => ?_⟩
  have hn2 : 2 ≤ n := le_of_max_le_left hn
  have hnε : 2 / ε ^ 2 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlg : 1 ≤ logb 2 n := by
    rw [le_logb_iff_rpow_le one_lt_two hnpos, rpow_one]; exact_mod_cast hn2
  have hK4 : 4 / c ≤ max (4 / c) (2 / ε ^ 2) := le_max_left _ _
  have hKε : 2 / ε ^ 2 ≤ max (4 / c) (2 / ε ^ 2) := le_max_right _ _
  have hw0 : 0 < w := by
    have hKpos := (div_pos two_pos (sq_pos_of_pos hε)).trans_le hKε
    exact_mod_cast (mul_pos hKpos (zero_lt_one.trans_le hlg)).trans_le hKw
  have hwn : 2 * w < n := by
    exact_mod_cast (by linarith only [hρ, mul_pos hε hnpos] : (2 * w : ℝ) < n)
  exact ⟨moment_le_of_ksThirdMomentBound hM hw0 hwn hc
      (hγ _ (div_pos (mod_cast hw0) hnpos) ((div_le_iff₀ hnpos).2 hρ))
      (((div_le_iff₀ hc).1 hK4).trans_eq (mul_comm _ _)) hKw,
    tail_le_of_ksTailBound hT hw0 hε hρ hKε hnε hKw⟩

end KirshnerSamorodnitsky

end Cslib.Code
