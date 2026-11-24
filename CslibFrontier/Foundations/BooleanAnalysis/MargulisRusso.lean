/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
public import CslibFrontier.Foundations.BooleanAnalysis.Influence
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# The Margulis–Russo Formula

Under the `p`-biased distribution each bit is `true` independently with probability `p`
(`BitString.bernoulliAverage`). The expectation of any `h : (ι → Bool) → ℝ` is a polynomial in
`p`, and its derivative is the sum over the coordinates `i` of the expected change of `h` when bit
`i` goes from `false` to `true` (`BitString.hasDerivAt_bernoulliAverage`), the classical form of
the Margulis–Russo Formula: differentiating the weight `p` or `1 - p` of bit `i` gives `±1`, and
pairing each string with its flip at `i` turns these into differences. Since `true` reads as `-1`,
the change is `-2` times the derivative `D_{x_i} h` (`BitString.derivative` of
`CslibFrontier.Foundations.BooleanAnalysis.Influence`), so the slope in `p` is
`-2 ∑ᵢ 𝔼_p[D_{x_i} h]` (`BitString.hasDerivAt_bernoulliAverage_sum_derivative`). Both hold as
identities of polynomials at every real `p`; the weighted sums are expectations only for
`0 ≤ p ≤ 1`.

The book states the formula [O'Donnell, Section 8.4, (8.8)][ODonnell2014] for `0 < p < 1` as a
derivative in the mean `μ = 1 - 2p` of a bit read as a sign: it is `σ⁻¹ ∑ᵢ f̂^{(p)}(i)`, where
`σ = 2√(p(1 - p))` and `f̂^{(p)}(i) = 𝔼_p[h · (signVal (x i) - μ) / σ]` is the `p`-biased Fourier
coefficient on `{i}` (Definitions 8.39 and 8.40). That statement is
`BitString.hasDerivAt_bernoulliAverage_one_sub_div_two`, which differentiates
`m ↦ bernoulliAverage ((1 - m) / 2) h` at `μ`. Its proof follows the book's: `d/dμ = -(1/2) d/dp`,
and pairing across bit `i` gives `𝔼_p[h · (signVal (x i) - μ)] = σ² 𝔼_p[D_{x_i} h]`
(`BitString.bernoulliAverage_mul_signVal_sub`).

For a monotone Boolean function the change is the indicator that `i` is pivotal, so the derivative
of `Pr_p[f = true]` is the expected number of pivotal coordinates
(`BitString.hasDerivAt_bernoulliAverage_bitVal_of_monotone`), the expected sensitivity
`𝔼_p[sens_f]`. With `f` read as signs this is `∑ᵢ 𝔼_p[(D_{x_i} f)²]`
(`BitString.hasDerivAt_bernoulliAverage_bitVal_sum_sq_derivative_of_monotone`). Both hold as
identities of polynomials at every real `p`. They read as statements about `Pr_p[f = true]` only
for `0 ≤ p ≤ 1`, and their right sides are the book's `I[f^{(p)}] / σ²` only for `0 < p < 1`,
where `f^{(p)}` is defined (Notation 8.43) and `σ² > 0`: there Proposition 8.45 equates
`𝔼_p[sens_f]` with `I[f^{(p)}] / σ²`, and `Inf_i[f^{(p)}] = σ² 𝔼_p[(D_{x_i} f)²]`, so the second
form is the book's (8.9). At `p = 0` or `1` a dictator still has slope `1` while `σ² = 0`. Hence
`Pr_p[f = true]` is strictly increasing on `[0, 1]` for a nonconstant monotone `f`
[O'Donnell, Remark 8.48][ODonnell2014]
(`BitString.strictMonoOn_bernoulliAverage_bitVal_of_monotone`).

The book writes `±1` bits with `π_p(-1) = p`; here `true` is the bit of probability `p`, which is
`-1` under `signVal`. Reading `true` as `-1` reverses the order on inputs and outputs alike, so
`Monotone` with `false < true` is the book's monotonicity.

## Usage

Open `Cslib.BitString`. The `p`-biased expectation of `h` is `bernoulliAverage p h`, and
`Pr_p[f = true]` is `bernoulliAverage p fun x => bitVal ℝ (f x)`. Each theorem is a `HasDerivAt`
of `fun q => bernoulliAverage q _` at an arbitrary real `p`, so `.deriv` gives the value of
`deriv` and `.congr_deriv` rewrites the slope into a closed form; no range hypothesis on `p` is
needed, except in the book's form of (8.8), which takes `0 < p < 1` and differentiates in the mean
`m` at `1 - 2p`. For a monotone `f`, pass `hf : Monotone f`; for strict increase also pass
`hc : ∃ x y, f x ≠ f y`, and apply the result to two points of `Set.Icc 0 1`. The weak
monotonicity of `Pr_p[f = true]` without `hc` is
`BitString.bernoulliAverage_le_bernoulliAverage_of_antitone` of
`CslibFrontier.Foundations.BooleanAnalysis.Bernoulli`, applied to the real negation
`fun x => -bitVal ℝ (f x)`.

The bit-string helpers of `CslibFrontier.Foundations.Data.BitString.Flip` connect the two ways of
naming a pivotal coordinate: `BitString.exists_update_ne_of_nonconstant` finds `x` and `i` with
`f (Function.update x i (!x i)) ≠ f x`, and
`BitString.apply_update_false_eq_apply_update_true_iff` converts that form into the
`false`/`true` form used here. `BitString.sum_update_false_add_update_true` pairs every vector
with its flip at `i` in any additive commutative monoid, which is how the bit weights are
regrouped in the proof; `BitString.bernoulliWeight_pos` gives positive mask weights for
`0 < p < 1`.

Checked clients differentiate the product of two bits (slope `2p`), a dictator (slope `1`, also
in the influence form) and the dictator read as a sign (slope `-2` in `p`, in the derivative form,
and slope `1` in `μ`, in the book's form, where its coefficient on `{0}` is `σ`); they find a
pivotal coordinate of the AND of two bits, show that its probability is strictly increasing with
`Pr_{1/4} < Pr_{1/2}`, and check the helpers on small instances, in
[`CslibFrontierTests/BooleanAnalysisMargulisRusso.lean`](https://github.com/cslib-community/cslib-frontier/blob/main/CslibFrontierTests/BooleanAnalysisMargulisRusso.lean).

## Main results

* `Cslib.BitString.hasDerivAt_bernoulliAverage`: the Margulis–Russo Formula in its classical
  form, the expected change when a bit is set.
* `Cslib.BitString.hasDerivAt_bernoulliAverage_sum_derivative`: the same, in terms of the
  derivatives `Dᵢ h`.
* `Cslib.BitString.bernoulliAverage_mul_signVal_sub`: the `p`-biased Fourier coefficient on `{i}`
  is `σ` times the expected derivative `Dᵢ h`.
* `Cslib.BitString.hasDerivAt_bernoulliAverage_one_sub_div_two`: the Margulis–Russo Formula
  (8.8) in the book's form.
* `Cslib.BitString.hasDerivAt_bernoulliAverage_bitVal_of_monotone`: the formula for monotone
  Boolean functions, via pivotal coordinates.
* `Cslib.BitString.hasDerivAt_bernoulliAverage_bitVal_sum_sq_derivative_of_monotone`: the same as
  `∑ᵢ 𝔼_p[(D_{x_i} f)²]`, which is `I[f^{(p)}] / σ²` for `0 < p < 1`, the book's (8.9).
* `Cslib.BitString.strictMonoOn_bernoulliAverage_bitVal_of_monotone`: Remark 8.48.

## References

* [R. O'Donnell, *Analysis of Boolean Functions*][ODonnell2014]
-/

public section

namespace Cslib.BitString

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The derivative in `p` of the `p`-biased expectation of `h` is the sum over the coordinates `i`
of the `p`-biased expectation of `h(x^{i ↦ true}) - h(x^{i ↦ false})`. This is the classical form
of the Margulis–Russo Formula; the book's form (8.8) is
`hasDerivAt_bernoulliAverage_one_sub_div_two`. -/
theorem hasDerivAt_bernoulliAverage (h : (ι → Bool) → ℝ) (p : ℝ) :
    HasDerivAt (fun q => bernoulliAverage q h)
      (∑ i, bernoulliAverage p fun x =>
        h (Function.update x i true) - h (Function.update x i false)) p := by
  set w : ι → (ι → Bool) → ℝ → ℝ := fun j s q => if s j = true then q else 1 - q
  have hw (j : ι) (s : ι → Bool) :
      HasDerivAt (w j s) (if s j = true then 1 else -1) p := by
    by_cases hj : s j = true
    · simpa [w, hj] using hasDerivAt_id' p
    · simpa [w, hj] using (hasDerivAt_id p).const_sub 1
  have hsum := HasDerivAt.fun_sum (u := univ) fun s _ =>
    (HasDerivAt.fun_finsetProd (u := univ) fun j _ => hw j s).mul_const (h s)
  refine hsum.congr_deriv ?_
  -- the derivative, regrouped by coordinate
  have hW (t : ι → Bool) (i : ι) :
      bernoulliWeight p t = w i t p * ∏ j ∈ univ.erase i, w j t p :=
    (mul_prod_erase univ (fun j => w j t p) (mem_univ i)).symm
  have hR (i : ι) (s : ι → Bool) (b : Bool) :
      ∏ j ∈ univ.erase i, w j (Function.update s i b) p = ∏ j ∈ univ.erase i, w j s p :=
    prod_congr rfl fun j hj => by simp [w, Function.update_of_ne (ne_of_mem_erase hj)]
  have key (i : ι) : ∑ s, (∏ j ∈ univ.erase i, w j s p) * (if s i = true then 1 else -1) * h s =
      bernoulliAverage p fun x => h (Function.update x i true) - h (Function.update x i false) := by
    have e₁ := sum_update_false_add_update_true i
      fun s => (∏ j ∈ univ.erase i, w j s p) * (if s i = true then 1 else -1) * h s
    have e₂ := sum_update_false_add_update_true i fun s => bernoulliWeight p s *
      (h (Function.update s i true) - h (Function.update s i false))
    have hpt (x : ι → Bool) :
        (∏ j ∈ univ.erase i, w j (Function.update x i false) p) *
            (if Function.update x i false i = true then 1 else -1) *
            h (Function.update x i false) +
          (∏ j ∈ univ.erase i, w j (Function.update x i true) p) *
            (if Function.update x i true i = true then 1 else -1) *
            h (Function.update x i true) =
        bernoulliWeight p (Function.update x i false) *
            (h (Function.update (Function.update x i false) i true) -
              h (Function.update (Function.update x i false) i false)) +
          bernoulliWeight p (Function.update x i true) *
            (h (Function.update (Function.update x i true) i true) -
              h (Function.update (Function.update x i true) i false)) := by
      simp only [hW _ i, hR, Function.update_idem, Function.update_self, w]
      simp only [Bool.false_eq_true, ite_false, ite_true]
      ring
    simp only [hpt] at e₁
    rw [bernoulliAverage]
    linear_combination e₂ / 2 - e₁ / 2
  simp only [smul_eq_mul, sum_mul, ← key]
  exact sum_comm

/-- The derivative in `p` of the `p`-biased expectation of `h` is `-2 ∑ᵢ 𝔼_p[Dᵢ h]`. With
`μ = 1 - 2p`, this is the step `d/dμ 𝔼[h^{(p)}] = ∑ᵢ 𝔼[D_{x_i} h^{(p)}]` of the proof of (8.8)
[O'Donnell, Section 8.4][ODonnell2014]. -/
theorem hasDerivAt_bernoulliAverage_sum_derivative (h : (ι → Bool) → ℝ) (p : ℝ) :
    HasDerivAt (fun q => bernoulliAverage q h)
      (-2 * ∑ i, bernoulliAverage p (derivative i h)) p := by
  refine (hasDerivAt_bernoulliAverage h p).congr_deriv ?_
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← bernoulliAverage_const_mul]
  congr 1
  funext x
  rw [derivative]
  ring

/-- Pairing across bit `i` against the centered sign of bit `i`: with `μ = 1 - 2p`, the mean of
`signVal (x i)`, the `p`-biased expectation of `h · (signVal (x i) - μ)` is `4p(1 - p)` times that
of the derivative `Dᵢ h`. Since `σ² = 4p(1 - p)`, this is the step
`𝔼_p[D_{x_i} f] = σ⁻¹ f̂^{(p)}(i)` of the book's proof of (8.8). -/
theorem bernoulliAverage_mul_signVal_sub (h : (ι → Bool) → ℝ) (p : ℝ) (i : ι) :
    (bernoulliAverage p fun x => h x * (signVal (x i) - (1 - 2 * p))) =
      4 * p * (1 - p) * bernoulliAverage p (derivative i h) := by
  have hw (x : ι → Bool) : (1 - p) * bernoulliWeight p (Function.update x i true) =
      p * bernoulliWeight p (Function.update x i false) := by
    have hR (b : Bool) : ∏ j ∈ univ.erase i, (if Function.update x i b j = true then p else 1 - p)
        = ∏ j ∈ univ.erase i, (if x j = true then p else 1 - p) :=
      prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_erase hj)]
    rw [bernoulliWeight, bernoulliWeight, ← mul_prod_erase univ _ (mem_univ i),
      ← mul_prod_erase univ _ (mem_univ i), hR, hR]
    simp only [Function.update_self, ite_true, Bool.false_eq_true, ite_false]
    ring
  have e₁ := sum_update_false_add_update_true i fun x =>
    bernoulliWeight p x * (h x * (signVal (x i) - (1 - 2 * p)))
  have e₂ := sum_update_false_add_update_true i fun x =>
    bernoulliWeight p x * (4 * p * (1 - p) * derivative i h x)
  have e₃ : ∑ x, (bernoulliWeight p (Function.update x i false) *
        (h (Function.update x i false) * (signVal (Function.update x i false i) - (1 - 2 * p))) +
      bernoulliWeight p (Function.update x i true) *
        (h (Function.update x i true) * (signVal (Function.update x i true i) - (1 - 2 * p)))) =
      ∑ x, (bernoulliWeight p (Function.update x i false) *
          (4 * p * (1 - p) * derivative i h (Function.update x i false)) +
        bernoulliWeight p (Function.update x i true) *
          (4 * p * (1 - p) * derivative i h (Function.update x i true))) :=
    sum_congr rfl fun x _ => by
      simp only [derivative, Function.update_self, Function.update_idem, signVal_true,
        signVal_false]
      linear_combination (-2 * (1 - p) * h (Function.update x i true) -
        2 * p * h (Function.update x i false)) * hw x
  beta_reduce at e₁ e₂
  rw [← bernoulliAverage_const_mul]
  simp only [bernoulliAverage]
  linarith

/-- **The Margulis–Russo Formula** [O'Donnell, Section 8.4, (8.8)][ODonnell2014], in the book's
form: for `0 < p < 1`, with `μ = 1 - 2p` and `σ = 2√(p(1 - p))`, the derivative in `μ` of the
`p`-biased expectation of `h` is `σ⁻¹ ∑ᵢ f̂^{(p)}(i)`. Here `f̂^{(p)}(i)` is the `p`-biased Fourier
coefficient `𝔼_p[h · φ(x i)]` of `h` on `{i}`, with `φ(x i) = (signVal (x i) - μ) / σ`
[O'Donnell, Definitions 8.39 and 8.40][ODonnell2014], and the expectation at mean `m` is the one
at rate `(1 - m) / 2`. -/
theorem hasDerivAt_bernoulliAverage_one_sub_div_two (h : (ι → Bool) → ℝ) {p : ℝ} (hp : 0 < p)
    (hp' : p < 1) :
    HasDerivAt (fun m => bernoulliAverage ((1 - m) / 2) h)
      ((2 * √(p * (1 - p)))⁻¹ * ∑ i, bernoulliAverage p fun x =>
        h x * ((signVal (x i) - (1 - 2 * p)) / (2 * √(p * (1 - p))))) (1 - 2 * p) := by
  set σ := 2 * √(p * (1 - p)) with hσ
  have hσ2 : σ ^ 2 = 4 * p * (1 - p) := by
    rw [hσ, mul_pow, Real.sq_sqrt (mul_pos hp (by linarith)).le]
    ring
  have hσ0 : σ ≠ 0 := fun h0 => by
    rw [h0] at hσ2
    nlinarith
  have hm : HasDerivAt (fun m : ℝ => (1 - m) / 2) (-1 / 2) (1 - 2 * p) := by
    simpa using ((hasDerivAt_id (1 - 2 * p)).const_sub 1).div_const 2
  have hd := (hasDerivAt_bernoulliAverage_sum_derivative h ((1 - (1 - 2 * p)) / 2)).comp
    (1 - 2 * p) hm
  rw [show (1 - (1 - 2 * p)) / 2 = p by ring] at hd
  refine hd.congr_deriv ?_
  have hc (i : ι) : (bernoulliAverage p fun x => h x * ((signVal (x i) - (1 - 2 * p)) / σ)) =
      σ⁻¹ * (4 * p * (1 - p) * bernoulliAverage p (derivative i h)) := by
    rw [← bernoulliAverage_mul_signVal_sub, ← bernoulliAverage_const_mul]
    congr 1
    funext x
    ring
  simp only [hc, ← mul_sum]
  rw [← hσ2]
  field_simp

/-- **The Margulis–Russo Formula for monotone functions** [O'Donnell, Section 8.4][ODonnell2014]:
the derivative in `p` of `Pr_p[f = true]` is the expected number of pivotal coordinates, that is
`∑ᵢ Pr_p[f(x^{i ↦ true}) ≠ f(x^{i ↦ false})]`, the expected sensitivity `𝔼_p[sens_f]`. The
identity holds as polynomials at every real `p`; it is about probabilities only for `0 ≤ p ≤ 1`,
and for `0 < p < 1` the book's `I[f^{(p)}] / σ²` equals the right side by
[O'Donnell, Proposition 8.45][ODonnell2014]. -/
theorem hasDerivAt_bernoulliAverage_bitVal_of_monotone {f : (ι → Bool) → Bool} (hf : Monotone f)
    (p : ℝ) :
    HasDerivAt (fun q => bernoulliAverage q fun x => bitVal ℝ (f x))
      (∑ i, bernoulliAverage p fun x =>
        if f (Function.update x i true) ≠ f (Function.update x i false) then 1 else 0) p := by
  refine (hasDerivAt_bernoulliAverage _ p).congr_deriv (sum_congr rfl fun i _ => ?_)
  congr 1
  funext x
  have hle : f (Function.update x i false) ≤ f (Function.update x i true) :=
    hf (Function.update_mono (by decide))
  revert hle
  cases f (Function.update x i true) <;> cases f (Function.update x i false) <;> simp

/-- **The Margulis–Russo Formula for monotone functions, influence form** [O'Donnell, Section 8.4,
(8.9)][ODonnell2014]: for `f` read as signs, the derivative in `p` of `Pr_p[f = true]` is
`∑ᵢ 𝔼_p[(D_{x_i} f)²]`. The identity holds as polynomials at every real `p`. For `0 < p < 1` the
right side is the book's `I[f^{(p)}] / σ²`, since the `p`-biased influence is
`Inf_i[f^{(p)}] = σ² 𝔼_p[(D_{x_i} f)²]` [O'Donnell, proof of Proposition 8.45][ODonnell2014]; the
book defines `f^{(p)}` only for `0 < p < 1` (Notation 8.43), and at `p = 0` or `1` a dictator
still has slope `1` while `σ² = 0`. -/
theorem hasDerivAt_bernoulliAverage_bitVal_sum_sq_derivative_of_monotone {f : (ι → Bool) → Bool}
    (hf : Monotone f) (p : ℝ) :
    HasDerivAt (fun q => bernoulliAverage q fun x => bitVal ℝ (f x))
      (∑ i, bernoulliAverage p fun x => derivative i (fun y => signVal (f y)) x ^ 2) p := by
  refine (hasDerivAt_bernoulliAverage_bitVal_of_monotone hf p).congr_deriv
    (sum_congr rfl fun i _ => ?_)
  congr 1
  funext x
  rw [sq_derivative_signVal_eq_ite]
  have hiff := apply_update_false_eq_apply_update_true_iff f i x
  by_cases hx : f (Function.update x i false) = f (Function.update x i true)
  · simp [hx, hiff.1 hx]
  · simp [Ne.symm hx, mt hiff.2 hx]

/-- **Nonconstant monotone functions have strictly increasing `p`-biased probability**
[O'Donnell, Remark 8.48][ODonnell2014]: `Pr_p[f = true]` is strictly increasing on `[0, 1]`,
since by the Margulis–Russo Formula its derivative on `(0, 1)` is the expected number of pivotal
coordinates, which is positive. The weak monotonicity holds for all monotone `f`
(`bernoulliAverage_le_bernoulliAverage_of_antitone`, applied to `fun x => -bitVal ℝ (f x)`). -/
theorem strictMonoOn_bernoulliAverage_bitVal_of_monotone {f : (ι → Bool) → Bool} (hf : Monotone f)
    (hc : ∃ x y, f x ≠ f y) :
    StrictMonoOn (fun q => bernoulliAverage q fun x => bitVal ℝ (f x)) (Set.Icc 0 1) := by
  have hd := hasDerivAt_bernoulliAverage_bitVal_of_monotone hf
  refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
    (fun q _ => (hd q).continuousAt.continuousWithinAt) fun q hq => ?_
  rw [interior_Icc] at hq
  rw [(hd q).deriv]
  obtain ⟨x, i, hxi⟩ := exists_update_ne_of_nonconstant hc
  have hne : f (Function.update x i true) ≠ f (Function.update x i false) := fun h =>
    hxi ((apply_update_false_eq_apply_update_true_iff f i x).1 h.symm)
  have hpos := bernoulliWeight_pos (ι := ι) hq.1 hq.2
  have hnn (j : ι) : 0 ≤ bernoulliAverage q fun y =>
      if f (Function.update y j true) ≠ f (Function.update y j false) then (1 : ℝ) else 0 :=
    sum_nonneg fun y _ => mul_nonneg (hpos y).le (by dsimp only; split_ifs <;> norm_num)
  refine lt_of_lt_of_le ?_ (single_le_sum (fun j _ => hnn j) (mem_univ i))
  refine lt_of_lt_of_le ?_ (single_le_sum (fun y _ => mul_nonneg (hpos y).le
    (by split_ifs <;> norm_num)) (mem_univ x))
  simpa [hne] using hpos x

end Cslib.BitString
