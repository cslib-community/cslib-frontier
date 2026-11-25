/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.NonlinearCost
public import CslibFrontier.Computability.Circuit.Boolean.Zhegalkin
public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Data.Nat.Digits.Defs
import CslibFrontier.Foundations.BooleanAnalysis.MajorityFourier
import CslibFrontier.Foundations.Data.Nat.Choose.Factorization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Majority needs at least `n - B(n)` nonlinear gates

Here `B(n)` is the sum of the binary digits of `n`. Every circuit over a Boolean basis of
fan-in at most two computing majority on `n` inputs has at least `n - B(n)` nonaffine gates,
with no restriction on depth, fanout, or the number of affine gates. Specializing to the native
Zhegalkin basis `{⊕, ∧, 1}` gives
`n - B(n) ≤ Zhegalkin.multiplicativeComplexity (single (majority n))`, the multiplicative
complexity lower bound of [Chistopolskaya and Podolskii, Corollary 11, §4, p. 12]
[ChistopolskayaPodolskii2018].

The source counts AND gates in the basis `{AND, XOR, NOT}`. The native basis uses a free
constant `1` in place of NOT: negation is XOR with `1`, and for a nonempty input a constant
`1` can be made as `NOT (x XOR x)`, with no AND gates. Thus the cost conventions agree for
positive input counts. The zero-input case here is the trivial extension, computed by the
free constant `1`.

The proof combines the integer-denominator invariant in `Boolean.NonlinearCost` with one
explicit Fourier coefficient. On `2 r + 1` inputs, a singleton coefficient is `C(2r,r) / 4^r`.
On `2 r` inputs, the constant coefficient is its negative: the library's majority convention
accepts ties. The exponent of two dividing `C(2r,r)` is `B(r)`, by Legendre's formula, so its
denominator forces at least `2r - B(r)` nonlinear gates. The binary digit identities for `2r`
and `2r + 1` give the claimed bound for every input count, including zero.

## Main results

* `Cslib.Circuits.Circuit.sub_sum_digits_le_nonlinearCost_of_eval_eq_majority`: every designated
  output computing majority requires at least `n - B(n)` nonaffine gates.
* `Cslib.Circuits.Boolean.Zhegalkin.sub_sum_digits_le_multiplicativeComplexity_majority`:
  the native multiplicative complexity of majority is at least `n - B(n)`.

## References

* [A. Chistopolskaya and V. V. Podolskii, *Parity Decision Tree Complexity is Greater Than
  Granularity*, Corollary 11][ChistopolskayaPodolskii2018]
-/

public section

namespace Cslib.Circuits

open Finset BitString

universe u

private theorem two_mul_le_add_sum_digits_of_centralBinom_denominator (r k : ℕ)
    (h : ∃ z : ℤ, (r.centralBinom : ℝ) / (4 : ℝ) ^ r = z / (2 : ℝ) ^ k) :
    2 * r ≤ k + (Nat.digits 2 r).sum := by
  obtain ⟨z, hz⟩ := h
  rw [show (4 : ℝ) ^ r = (2 : ℝ) ^ (2 * r) by norm_num [pow_mul]] at hz
  have hmulZ : (r.centralBinom : ℤ) * (2 : ℤ) ^ k = z * (2 : ℤ) ^ (2 * r) := by
    exact_mod_cast (div_eq_div_iff (by positivity) (by positivity)).mp hz
  have hdvdZ : (2 : ℤ) ^ (2 * r) ∣ (r.centralBinom : ℤ) * (2 : ℤ) ^ k :=
    ⟨z, hmulZ.trans (mul_comm _ _)⟩
  have hdvd : 2 ^ (2 * r) ∣ r.centralBinom * 2 ^ k := by exact_mod_cast hdvdZ
  have hval := (Nat.prime_two.pow_dvd_iff_le_factorization
    (mul_ne_zero (Nat.centralBinom_ne_zero r) (pow_ne_zero k (by decide)))).mp hdvd
  rw [Nat.factorization_mul (Nat.centralBinom_ne_zero r) (pow_ne_zero k (by decide)),
    Finsupp.add_apply, Nat.factorization_centralBinom_two,
    Nat.factorization_pow_self Nat.prime_two] at hval
  omega

/-- A designated circuit output computing majority on `n` inputs requires at least `n - B(n)`
nonaffine gates, where `B(n)` is the sum of the binary digits of `n`. All affine operations and
arbitrary wire reuse are free. This generalizes [Chistopolskaya and Podolskii, Corollary 11]
[ChistopolskayaPodolskii2018] from the basis `{AND, XOR, NOT}` to every basis of fan-in at most
two; the cited statement is
`Boolean.Zhegalkin.sub_sum_digits_le_multiplicativeComplexity_majority`. -/
theorem Circuit.sub_sum_digits_le_nonlinearCost_of_eval_eq_majority
    {σ : Signature.{u}} {n m : ℕ} (c : Circuit σ n m) (I : Interpretation σ Bool)
    (hArity : ∀ op, σ.Arity op ≤ 2) (j : Fin m)
    (hmajority : ∀ x, c.eval I x j = majority n x) :
    n - (Nat.digits 2 n).sum ≤ c.program.cost (Boolean.nonlinearCost I) := by
  obtain ⟨r, rfl | rfl⟩ := Nat.even_or_odd' n
  · obtain ⟨z, hz⟩ :=
      c.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_nonlinearCost I hArity j ∅
    simp only [hmajority, fourierCoeff_signVal_majority_two_mul_empty] at hz
    have hbound := two_mul_le_add_sum_digits_of_centralBinom_denominator r _ ⟨-z, by
      simpa only [Nat.centralBinom_eq_two_mul_choose, Int.cast_neg, neg_div, neg_neg] using
        congrArg Neg.neg hz⟩
    have hDigits : (Nat.digits 2 (2 * r)).sum = (Nat.digits 2 r).sum := by
      rcases eq_or_ne r 0 with rfl | hr
      · simp
      · simpa using congrArg List.sum (Nat.digits_add 2 (by decide) 0 r (by decide) (.inr hr))
    omega
  · obtain ⟨z, hz⟩ :=
      c.exists_fourierCoeff_signVal_eval_eq_intCast_div_two_pow_nonlinearCost I hArity j
        {⟨0, by omega⟩}
    simp only [hmajority, fourierCoeff_signVal_majority_singleton] at hz
    have hbound := two_mul_le_add_sum_digits_of_centralBinom_denominator r _ ⟨z, by
      simpa only [Nat.centralBinom_eq_two_mul_choose] using hz⟩
    have hDigits : (Nat.digits 2 (2 * r + 1)).sum = (Nat.digits 2 r).sum + 1 := by
      simpa [Nat.add_comm] using congrArg List.sum
        (Nat.digits_add 2 (by decide) 1 r (by decide) (.inl (by decide)))
    omega

namespace Boolean.Zhegalkin

/-- In the Zhegalkin basis, precisely conjunction is nonaffine, so the native nonlinear cost
equals the existing conjunction-gate cost. -/
@[simp] theorem nonlinearCost_eq_andCost : nonlinearCost interpretation = andCost := by
  funext op
  cases op with
  | one =>
    have h : IsAffine (interpretation .one) := isAffine_const (by decide) true
    simp [nonlinearCost, h]
  | xor =>
    have h : IsAffine (interpretation .xor) := fun x y z => by
      simp only [interpretation_xor, ← Bool.add_eq_xor, Pi.add_apply]; ring
    simp [nonlinearCost, h]
  | and =>
    have h : ¬IsAffine (interpretation .and) := fun h => by
      have h' := h ![false, false] ![true, false] ![false, true]
      norm_num [interpretation, Pi.add_apply, Bool.add_eq_xor] at h'
    simp [nonlinearCost, h]

/-- **Majority multiplicative-complexity lower bound** [Chistopolskaya and Podolskii,
Corollary 11, §4, p. 12][ChistopolskayaPodolskii2018]: computing majority on `n` inputs needs at
least `n - B(n)` conjunction gates over `{⊕, ∧, 1}`, where `B(n)` is the binary digit sum. -/
theorem sub_sum_digits_le_multiplicativeComplexity_majority (n : ℕ) :
    n - (Nat.digits 2 n).sum ≤ multiplicativeComplexity (single (majority n)) := by
  obtain ⟨c, hc, hcost⟩ := exists_computes_cost_eq_multiplicativeComplexity (single (majority n))
  have h := c.sub_sum_digits_le_nonlinearCost_of_eval_eq_majority interpretation
    (fun op => by cases op <;> decide) 0 (fun x => congrFun (hc x) 0)
  rwa [nonlinearCost_eq_andCost, hcost] at h

end Boolean.Zhegalkin

end Cslib.Circuits
