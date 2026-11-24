/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib `Data/Nat/Choose/Factorization.lean`)

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Choose.Factorization

/-!
# The power of two dividing a central binomial coefficient

The exponent of two in `C(2n, n)` equals the sum of the binary digits of `n`
(`Nat.factorization_centralBinom_two`). This is the central-binomial case of Kummer's theorem.
The proof uses Mathlib's Legendre formula for `n!` and the identity
`C(2n, n) · n! · n! = (2n)!`.

## Main results

* `Nat.factorization_centralBinom_two`: the exponent of two in `C(2n, n)` is the binary digit
  sum of `n`.
-/

public section

namespace Nat

/-- The exponent of two in the central binomial coefficient `C(2n, n)` is the sum of the binary
digits of `n`. This is the `p = 2`, `k = n` case of Mathlib's Kummer theorem
`sub_one_mul_multiplicity_choose_eq_sub_sum_digits'`, simplified using that `2 * n` and `n` have
the same binary digit sum. -/
theorem factorization_centralBinom_two (n : ℕ) :
    n.centralBinom.factorization 2 = (Nat.digits 2 n).sum := by
  have hprod : n.centralBinom * n.factorial * n.factorial = (2 * n).factorial := by
    simpa only [centralBinom_eq_two_mul_choose, two_mul] using
      add_choose_mul_factorial_mul_factorial n n
  have h := congrArg (fun a : ℕ => a.factorization 2) hprod
  rw [factorization_mul (mul_ne_zero (centralBinom_ne_zero n) (factorial_ne_zero n))
      (factorial_ne_zero n),
    factorization_mul (centralBinom_ne_zero n) (factorial_ne_zero n)] at h
  simp only [Finsupp.add_apply, factorization_factorial_mul prime_two] at h
  have hLegendre : n.factorial.factorization 2 = n - (Nat.digits 2 n).sum := by
    simpa using sub_one_mul_factorization_factorial (n := n) prime_two
  have hDigits := digit_sum_le 2 n
  omega

end Nat
