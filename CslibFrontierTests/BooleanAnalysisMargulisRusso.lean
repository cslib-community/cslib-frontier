/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.MargulisRusso

/-! # Tests for the Margulis–Russo Formula

The product of two bits has `p`-biased expectation `p²`, and the formula gives its slope `2p`. The
`p`-biased probability of a dictator has slope one, also in the influence form of (8.9), and
the dictator read as a sign has slope `-2` in the derivative form and slope `1` in the mean `μ`,
in the book's form of (8.8), where its `p`-biased Fourier coefficient on its bit is `σ`. The AND
of two bits has a pivotal coordinate, a non-pivotal one where the other bit is `false`, and
strictly increasing `p`-biased probability on `[0, 1]`. Pairing across a bit and the positivity of
mask weights are checked on small instances.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisMargulisRusso

open Cslib Cslib.BitString Finset

/-- The AND of two bits is monotone. -/
theorem monotone_and : Monotone fun x : Fin 2 → Bool => x 0 && x 1 := fun x y h => by
  change (x 0 && x 1) ≤ (y 0 && y 1)
  have h0 := h 0
  have h1 := h 1
  revert h0 h1
  cases x 0 <;> cases x 1 <;> cases y 0 <;> cases y 1 <;> decide

/-- The Margulis–Russo Formula for the product of two bits read as `0` or `1`: setting either bit
changes the product by the other bit, which is set with probability `p`, so the slope is `2p`. -/
example (p : ℝ) : HasDerivAt
    (fun q => bernoulliAverage q fun x : Fin 2 → Bool => bitVal ℝ (x 0) * bitVal ℝ (x 1))
    (2 * p) p := by
  refine (hasDerivAt_bernoulliAverage _ p).congr_deriv ?_
  have h0 := bernoulliAverage_coordinate (ι := Fin 2) p 0
  have h1 := bernoulliAverage_coordinate (ι := Fin 2) p 1
  simp only [Fin.sum_univ_two, Function.update, bitVal] at h0 h1 ⊢
  simp [h0, h1]
  ring

/-- A dictator is `true` with probability `p`, so its slope is one: its own bit is always pivotal
and the other never is. -/
example (p : ℝ) :
    HasDerivAt (fun q => bernoulliAverage q fun x : Fin 2 → Bool => bitVal ℝ (x 0)) 1 p := by
  refine (hasDerivAt_bernoulliAverage_bitVal_of_monotone (fun _ _ h => h 0) p).congr_deriv ?_
  simp [Fin.sum_univ_two, Function.update, bernoulliAverage_const]

/-- The AND of two bits has a pivotal coordinate. -/
example : ∃ (x : Fin 2 → Bool) (i : Fin 2),
    ((Function.update x i (!x i)) 0 && (Function.update x i (!x i)) 1) ≠ (x 0 && x 1) :=
  exists_update_ne_of_nonconstant (f := fun x : Fin 2 → Bool => x 0 && x 1)
    ⟨fun _ => true, fun _ => false, by decide⟩

/-- Where bit `1` is `false`, bit `0` is not pivotal for the AND of two bits (both settings of
bit `0` give `false`), so flipping bit `0` keeps the value. -/
example (x : Fin 2 → Bool) (hx : x 1 = false) :
    (Function.update x 0 (!x 0) 0 && Function.update x 0 (!x 0) 1) = (x 0 && x 1) :=
  (apply_update_false_eq_apply_update_true_iff (fun x : Fin 2 → Bool => x 0 && x 1) 0 x).1
    (by simp [Function.update, hx])

/-- Pairing across bit `0`: the indicator of bit `0` is `1` at exactly one of the two settings, so
the paired sum over the four inputs is `4`, twice the two inputs with bit `0` set. -/
example : ∑ x : Fin 2 → Bool, ((if Function.update x 0 false 0 then 1 else 0) +
    (if Function.update x 0 true 0 then 1 else 0) : ℕ) = 4 := by
  rw [sum_update_false_add_update_true 0 fun x : Fin 2 → Bool => if x 0 then 1 else 0]
  decide

/-- At rate `1/3`, the all-`true` mask on three coordinates has positive probability, so the
`p`-biased average of its indicator is positive. -/
example : 0 < bernoulliAverage (1 / 3) fun x : Fin 3 → Bool =>
    if x = fun _ => true then (1 : ℝ) else 0 := by
  simp only [bernoulliAverage, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  exact bernoulliWeight_pos (by norm_num) (by norm_num) _

/-- The derivative of the dictator read as a sign in its own bit is `1`. -/
theorem derivative_zero_signVal_dictator :
    derivative 0 (fun x : Fin 2 → Bool => signVal (x 0)) = fun _ => 1 := by
  funext x
  norm_num [derivative]

/-- The derivative of the dictator read as a sign in the other bit is `0`. -/
theorem derivative_one_signVal_dictator :
    derivative 1 (fun x : Fin 2 → Bool => signVal (x 0)) = fun _ => 0 := by
  funext x
  simp [derivative, Function.update]

/-- The dictator read as a sign has `p`-biased expectation `1 - 2p`; its derivative in bit `0` is
`1` and in bit `1` is `0`, so the derivative form of the formula gives slope `-2`. -/
example (p : ℝ) :
    HasDerivAt (fun q => bernoulliAverage q fun x : Fin 2 → Bool => signVal (x 0)) (-2) p := by
  refine (hasDerivAt_bernoulliAverage_sum_derivative _ p).congr_deriv ?_
  simp [Fin.sum_univ_two, derivative_zero_signVal_dictator, derivative_one_signVal_dictator,
    bernoulliAverage_const]

/-- The dictator read as a sign is `1` or `-1`, so its centered sign has expectation `σ² = 4pq`:
`𝔼_p[x₀ (x₀ - μ)] = 1 - μ² = 4p(1 - p)`. -/
example (p : ℝ) : (bernoulliAverage p fun x : Fin 2 → Bool =>
    signVal (x 0) * (signVal (x 0) - (1 - 2 * p))) = 4 * p * (1 - p) := by
  rw [bernoulliAverage_mul_signVal_sub, derivative_zero_signVal_dictator, bernoulliAverage_const,
    mul_one]

/-- The book's form of (8.8) for the dictator read as a sign: its `p`-biased expectation is the
mean `μ` itself, so the slope in `μ` is `1`; its `p`-biased Fourier coefficient on `{0}` is `σ`,
and on `{1}` it is `0`. -/
example {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt (fun m => bernoulliAverage ((1 - m) / 2) fun x : Fin 2 → Bool => signVal (x 0))
      1 (1 - 2 * p) := by
  refine (hasDerivAt_bernoulliAverage_one_sub_div_two _ hp hp').congr_deriv ?_
  have hσ : (2 * √(p * (1 - p))) ^ 2 = 4 * p * (1 - p) := by
    rw [mul_pow, Real.sq_sqrt (mul_pos hp (by linarith)).le]
    ring
  have hσ0 : 2 * √(p * (1 - p)) ≠ 0 :=
    (mul_pos two_pos (Real.sqrt_pos.2 (mul_pos hp (by linarith)))).ne'
  have hc (i : Fin 2) : (bernoulliAverage p fun x : Fin 2 → Bool =>
      signVal (x 0) * ((signVal (x i) - (1 - 2 * p)) / (2 * √(p * (1 - p))))) =
      (2 * √(p * (1 - p)))⁻¹ * (4 * p * (1 - p) *
        bernoulliAverage p (derivative i fun x : Fin 2 → Bool => signVal (x 0))) := by
    rw [← bernoulliAverage_mul_signVal_sub, ← bernoulliAverage_const_mul]
    congr 1
    funext x
    ring
  simp only [hc, Fin.sum_univ_two, derivative_zero_signVal_dictator,
    derivative_one_signVal_dictator, bernoulliAverage_const, mul_one, mul_zero, add_zero]
  rw [← hσ]
  field_simp

/-- The influence form of (8.9) for a dictator: its own bit has squared derivative `1` and the
other `0`, so the slope of its `p`-biased probability is `1`. -/
example (p : ℝ) :
    HasDerivAt (fun q => bernoulliAverage q fun x : Fin 2 → Bool => bitVal ℝ (x 0)) 1 p := by
  refine (hasDerivAt_bernoulliAverage_bitVal_sum_sq_derivative_of_monotone
    (fun _ _ h => h 0) p).congr_deriv ?_
  simp [Fin.sum_univ_two, derivative_zero_signVal_dictator, derivative_one_signVal_dictator,
    bernoulliAverage_const]

/-- The AND of two bits has strictly increasing `p`-biased probability. -/
example : StrictMonoOn
    (fun q => bernoulliAverage q fun x : Fin 2 → Bool => bitVal ℝ (x 0 && x 1)) (Set.Icc 0 1) :=
  strictMonoOn_bernoulliAverage_bitVal_of_monotone monotone_and
    ⟨fun _ => true, fun _ => false, by decide⟩

/-- The AND of two bits is less likely at rate `1/4` than at rate `1/2`. -/
example : (bernoulliAverage (1 / 4) fun x : Fin 2 → Bool => bitVal ℝ (x 0 && x 1)) <
    bernoulliAverage (1 / 2) fun x : Fin 2 → Bool => bitVal ℝ (x 0 && x 1) :=
  strictMonoOn_bernoulliAverage_bitVal_of_monotone monotone_and
    ⟨fun _ => true, fun _ => false, by decide⟩ (by norm_num) (by norm_num) (by norm_num)

end CslibFrontierTests.BooleanAnalysisMargulisRusso
