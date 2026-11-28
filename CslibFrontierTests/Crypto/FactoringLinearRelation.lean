/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.Factoring.LinearRelation
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Prime

/-!
# Linear-relation Fermat factoring: checked instances

Concrete regression checks for `CslibFrontier/Crypto/Computational/Factoring/LinearRelation.lean`:

* Positive factorizations for `(a, b) = (3, 2)` and `(5, 3)`, both by evaluation and via
  `fermatFactorLinear_mul_eq`, `fermatFactorLinear_mul_eq_of_lt_rpow`,
  `abs_add_div_two_sub_sqrt_mul_lt_half`, and `RSADesc.fermatFactorLinear_eq_of_lt_rpow`.
* Output ordering follows `b * q ≤ a * p` rather than `q ≤ p`, checked on `(3, 2, 7, 11)`.
* Exercise 16.14's 309-digit challenge (`a = 3`, `b = 2`), verified both by `norm_num` evaluation
  and via `fermatFactorLinear_mul_eq_of_lt_rpow`.
* Counterexamples showing necessity of `Nat.Coprime (2 * a) q`, `Nat.Coprime (2 * b) p`, `0 < a`
  in `fermatFactorLinear_mul_eq_of_lt_rpow`, and the fourth-root closeness bound.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FactoringLinearRelation

open Cslib.Crypto

private def challengeN : ℕ :=
  ((((720062263 * 10 ^ 60 +
  747350425279564435525583738338084451473999841826653057981916) * 10 ^ 60 +
  355690188337790423408664187663938485175264994017897083524079) * 10 ^ 60 +
  135686877441155132015188279331812309091996246361896836573643) * 10 ^ 60 +
  119174094961348524639707885238799396839230364676670221627018) * 10 ^ 60 +
  353299443241192173812729276147530748597302192751375739387929

private def challengeP : ℕ :=
  (21909849592475533092273988531583955 * 10 ^ 60 +
  898982176093344929030099423584127212078126150044721102570957) * 10 ^ 60 +
  812665127475051465088833555993294644190955293613411658629209

private def challengeQ : ℕ :=
  (32864774388713299638410982797375933 * 10 ^ 60 +
  848473264140017393545149135376190818117189240035825816494954) * 10 ^ 60 +
  711821626076210364113848440012285863311027426121370050758081

private def rsa15251 : RSADesc :=
  { p := 101, q := 151, e := 7, d := 2143, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- Concrete `(a, b) = (3, 2)` factorization of `101 * 151 = 15251`, checked by evaluation. -/
example : fermatFactorLinear 3 2 (101 * 151) = (101, 151) := by
  unfold fermatFactorLinear fermatFactor factorOfTotient
  norm_num

/-- Checked via `RSADesc.fermatFactorLinear_eq_of_lt_rpow` on `rsa15251`. -/
example : fermatFactorLinear 3 2 rsa15251.modulus = (101, 151) := by
  have hlt : |(3 : ℝ) * 101 - 2 * 151| < (rsa15251.modulus : ℝ) ^ (1 / 4 : ℝ) := by
    rw [one_div, Real.lt_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity) (by norm_num)]
    norm_num [RSADesc.modulus, rsa15251]
  simpa [rsa15251] using
    rsa15251.fermatFactorLinear_eq_of_lt_rpow (a := 3) (b := 2) (by decide) (by decide) hlt

/-- Non-unit closeness difference `|5 * 101 - 3 * 167| = 4` still recovers `(101, 167)`. -/
example : fermatFactorLinear 5 3 (101 * 167) = (101, 167) := by
  have hlt : |(5 : ℝ) * 101 - 3 * 167| < (4 * (5 : ℝ) * 3 * 101 * 167) ^ (1 / 4 : ℝ) := by
    rw [one_div, Real.lt_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity) (by norm_num)]
    norm_num
  simpa using fermatFactorLinear_mul_eq (a := 5) (b := 3) (p := 101) (q := 167)
    (by decide) (by decide) hlt

/-- Real Lemma 16.4 check: `(3 * 101 + 2 * 151) / 2` lies within `< 1 / 2` of
`√((3 * 101) * (2 * 151))`. -/
example : |((3 : ℝ) * 101 + 2 * 151) / 2 - Real.sqrt ((3 * 101) * (2 * 151))| < 1 / 2 := by
  have h1 : |(3 : ℝ) * 101 - 2 * 151| < 2 := by norm_num
  have h2 : (1 : ℝ) ≤ ((3 * 101 : ℝ) * (2 * 151)) ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow (by norm_num) (by norm_num)
  exact abs_add_div_two_sub_sqrt_mul_lt_half (by norm_num) (by norm_num) (by linarith)

/-- Output order tracks `b * q ≤ a * p` rather than `q ≤ p`: for `p = 7 < q = 11` with
`3 * 7 = 21 < 2 * 11 = 22`, `fermatFactorLinear 3 2 (7 * 11)` returns `(11, 7)`. -/
example : fermatFactorLinear 3 2 (7 * 11) = (11, 7) := by
  unfold fermatFactorLinear fermatFactor factorOfTotient
  norm_num

/-- Boneh–Shoup Exercise 16.14 (p. 710): the 309-digit modulus `challengeN` factors as
`challengeP * challengeQ`. -/
theorem challengeN_eq_mul : challengeP * challengeQ = challengeN := by
  norm_num [challengeP, challengeQ, challengeN]

/-- Exercise 16.14 (p. 710): `|3 * p - 2 * q| < n ^ (1 / 4)` holds for the 309-digit modulus,
so `fermatFactorLinear_mul_eq_of_lt_rpow` factors `challengeN`. -/
example : fermatFactorLinear 3 2 challengeN = (challengeQ, challengeP) := by
  have hlt : |(3 : ℝ) * challengeP - 2 * challengeQ| <
      ((challengeP : ℝ) * challengeQ) ^ (1 / 4 : ℝ) := by
    rw [one_div, Real.lt_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity) (by norm_num)]
    norm_num [challengeP, challengeQ]
  have hcop_a : Nat.Coprime (2 * 3) challengeQ := by norm_num [challengeQ]
  have hcop_b : Nat.Coprime (2 * 2) challengeP := by norm_num [challengeP]
  have hle : ¬ 2 * challengeQ ≤ 3 * challengeP := by norm_num [challengeP, challengeQ]
  rw [← challengeN_eq_mul,
    fermatFactorLinear_mul_eq_of_lt_rpow (by norm_num) (by norm_num) hcop_a hcop_b hlt,
    ite_eq_right hle]

/-- Exercise 16.14 (p. 710): direct `norm_num` evaluation of `fermatFactorLinear 3 2` on the
309-digit modulus `challengeN` returns `(challengeQ, challengeP)`. -/
example : fermatFactorLinear 3 2 challengeN = (challengeQ, challengeP) := by
  unfold fermatFactorLinear fermatFactor factorOfTotient
  norm_num [challengeN, challengeP, challengeQ]

/-- Necessity of `Nat.Coprime (2 * a) q`: when `a = 1`, `b = 5`, `p = 11`, `q = 2`, the other
hypotheses (`0 < a`, `0 < b`, `Nat.Coprime (2 * b) p`, and
`|a * p - b * q| < (4 * a * b * p * q) ^ (1 / 4)`) hold, yet `q ∣ 2 * a` and
`fermatFactorLinear 1 5 (11 * 2)` returns `(22, 2)`. -/
example : Nat.Coprime (2 * 5) 11 ∧ ¬ Nat.Coprime (2 * 1) 2 ∧
    |(1 : ℝ) * 11 - 5 * 2| < (4 * (1 : ℝ) * 5 * 11 * 2) ^ (1 / 4 : ℝ) ∧
    fermatFactorLinear 1 5 (11 * 2) = (22, 2) := by
  refine ⟨by decide, by decide, ?_,
    by unfold fermatFactorLinear fermatFactor factorOfTotient; norm_num⟩
  rw [one_div, Real.lt_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity) (by norm_num)]
  norm_num

/-- Necessity of `Nat.Coprime (2 * b) p`: when `a = 1`, `b = 1`, `p = 2`, `q = 3`, the other
hypotheses (`0 < a`, `0 < b`, `Nat.Coprime (2 * a) q`, and `|a * p - b * q| < (p * q) ^ (1 / 4)`)
hold, yet `p ∣ 2 * b` and `fermatFactorLinear 1 1 (2 * 3)` returns `(6, 2)`. -/
example : Nat.Coprime (2 * 1) 3 ∧ ¬ Nat.Coprime (2 * 1) 2 ∧
    |(1 : ℝ) * 2 - 1 * 3| < ((2 : ℝ) * 3) ^ (1 / 4 : ℝ) ∧
    fermatFactorLinear 1 1 (2 * 3) = (6, 2) := by
  refine ⟨by decide, by decide, ?_,
    by unfold fermatFactorLinear fermatFactor factorOfTotient; norm_num⟩
  rw [one_div, Real.lt_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity) (by norm_num)]
  norm_num

/-- Necessity of `0 < a` in `fermatFactorLinear_mul_eq_of_lt_rpow`:
for `(a, b, p, q) = (0, 1, 3, 1)`, every other hypothesis (`0 < b`, `Nat.Coprime (2 * a) q`,
`Nat.Coprime (2 * b) p`, and `|a * p - b * q| < (p * q) ^ (1 / 4)`) holds, yet
`fermatFactorLinear 0 1 (3 * 1)` returns `(3, 3)` (`Nat.gcd 0 n = n`). -/
example : 0 < (1 : ℕ) ∧ Nat.Coprime (2 * 0) 1 ∧ Nat.Coprime (2 * 1) 3 ∧
    |(0 : ℝ) * 3 - 1 * 1| < ((3 : ℝ) * 1) ^ (1 / 4 : ℝ) ∧
    fermatFactorLinear 0 1 (3 * 1) = (3, 3) := by
  refine ⟨by decide, by decide, by decide, ?_,
    by unfold fermatFactorLinear fermatFactor factorOfTotient; norm_num⟩
  rw [one_div, Real.lt_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity) (by norm_num)]
  norm_num

/-- Necessity of the closeness bound: for `a = 3`, `b = 2`, `p = 5`, `q = 53`, the positivity and
coprimality hypotheses hold (`|3 * 5 - 2 * 53| = 91`), yet `fermatFactorLinear 3 2 (5 * 53)` returns
`(1, 1)` instead of `(5, 53)` or `(53, 5)`. -/
example : Nat.Coprime (2 * 3) 53 ∧ Nat.Coprime (2 * 2) 5 ∧
    ¬ |(3 : ℝ) * 5 - 2 * 53| < (4 * (3 : ℝ) * 2 * 5 * 53) ^ (1 / 4 : ℝ) ∧
    fermatFactorLinear 3 2 (5 * 53) = (1, 1) := by
  refine ⟨by decide, by decide, ?_,
    by unfold fermatFactorLinear fermatFactor factorOfTotient; norm_num⟩
  rw [one_div, Real.lt_rpow_inv_iff_of_pos (abs_nonneg _) (by positivity) (by norm_num)]
  norm_num

/-- Polynomial-time certificate check in a `module` client. -/
example : Turing.MultiTapeTM.ComputableInPolyTime
    (fun p : (ℕ × ℕ) × ℕ => fermatFactorLinear p.1.1 p.1.2 p.2)
    (Turing.MultiTapeTM.encPair
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat)
      Turing.MultiTapeTM.encNat)
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat) :=
  computableInPolyTime_fermatFactorLinear_prod

/-- Compositional `@[fun_prop]` check for fixed `(a, b) = (3, 2)`. -/
example : Turing.MultiTapeTM.ComputableInPolyTime (fun n => fermatFactorLinear 3 2 n)
    Turing.MultiTapeTM.encNat
    (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encNat Turing.MultiTapeTM.encNat) := by
  fun_prop

end CslibFrontierTests.Crypto.FactoringLinearRelation
