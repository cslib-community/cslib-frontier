/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.MajorityFourier
public import CslibFrontier.Foundations.BooleanAnalysis.TransitiveSymmetric
import CslibFrontier.Foundations.Data.BitString.AgreeExpect
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.BigOperators.Fin

/-! # Tests for the Fourier coefficients of majority

Majority of three bits has no ties, so it agrees with strict majority, unlike majority of four
bits, and complementing the input complements it. Read as signs, it is
`(x₀ + x₁ + x₂) / 2 - x₀ x₁ x₂ / 2`: its coefficients are `1 / 2` on the singletons, `-1 / 2` on
the whole set, and `0` on the sets of even size. The coefficients on a singleton and on the whole
set are also computed by brute force over the eight inputs. Majority of five bits has coefficients
`3 / 8` on the singletons, `-1 / 8` on the sets of size three, and `3 / 8` on the whole set. The
lemmas behind the theorem are also checked on small cases: counting the true bits outside a
coordinate and their distribution, symmetric spectra, and the derivative of majority.

Complementary levels of majority of three bits have opposite coefficients. The level-one weight of
majority drops from `3 / 4` on three bits to `45 / 64` on five, majority of five bits has no
weight on level two, the noise stability of majority of three bits is `3 / 4 ρ + 1 / 4 ρ ^ 3`, and
majority of five bits is strictly less noise-stable. On five bits the top weight `W^5` is `1 / 5`
of the level-one weight `W^1`. No coefficient exceeds the singleton coefficient, and on seven bits
the coefficients drop from `5 / 16` on a singleton to `1 / 16` on three and five bits, then rise to
`5 / 16` on all seven.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisMajorityFourier

open Cslib Cslib.BitString Finset
open scoped BigOperators

/-- Majority of three bits, read as signs. -/
noncomputable abbrev maj₃ (x : Fin 3 → Bool) : ℝ :=
  signVal (majority (2 * 1 + 1) x)

-- On three bits there are no ties, so majority is strict majority.
example : majority (2 * 1 + 1) ![true, false, true] = strictMajority 3 ![true, false, true] :=
  congrFun (majority_eq_strictMajority 1) _

-- On four bits they differ at a tie.
example :
    majority 4 ![true, true, false, false] ≠ strictMajority 4 ![true, true, false, false] := by
  decide

-- Complementing `(true, false, false)` to `(false, true, true)` complements majority.
example : majority (2 * 1 + 1) ![false, true, true] =
    !majority (2 * 1 + 1) ![true, false, false] := by
  rw [show ![false, true, true] = ![true, false, false] + fun _ => true by decide]
  exact isOdd_majority 1 _

-- The coefficient on a singleton is `1 / 2`.
example : fourierCoeff maj₃ {0} = 1 / 2 := by
  rw [fourierCoeff_signVal_majority_of_card_eq 1 0 (by simp)]
  norm_num

-- Brute force over the eight inputs gives the same `1 / 2`.
example : fourierCoeff maj₃ {0} = 1 / 2 := by
  simp only [fourierCoeff, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  simp [maj₃, chi, majority, threshold_apply, weight_eq_sum_toNat, Fin.sum_univ_succ]

-- The coefficient on the whole set is `-1 / 2`.
example : fourierCoeff maj₃ univ = -1 / 2 := by
  rw [fourierCoeff_signVal_majority_of_card_eq 1 1 (by simp)]
  norm_num

-- Brute force over the eight inputs gives the whole-set coefficient `-1 / 2`, which checks the
-- sign `(-1) ^ j`.
example : fourierCoeff maj₃ univ = -1 / 2 := by
  simp only [fourierCoeff, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  simp [maj₃, chi, majority, threshold_apply, weight_eq_sum_toNat, Fin.sum_univ_succ,
    Fin.prod_univ_succ]

-- The coefficient on a pair vanishes.
example : fourierCoeff maj₃ {0, 1} = 0 :=
  fourierCoeff_signVal_majority_of_even 1 (by decide)

-- Majority of five bits: `3 / 8` on a singleton, `-1 / 8` on a set of size three, and `3 / 8` on
-- the whole set.
example : fourierCoeff (fun x => signVal (majority (2 * 2 + 1) x)) {0} = 3 / 8 := by
  rw [fourierCoeff_signVal_majority_of_card_eq 2 0 (by simp)]
  norm_num [Nat.choose]

example : fourierCoeff (fun x => signVal (majority (2 * 2 + 1) x)) {0, 1, 2} = -1 / 8 := by
  rw [fourierCoeff_signVal_majority_of_card_eq 2 1 (by decide)]
  norm_num [Nat.choose]

example : fourierCoeff (fun x => signVal (majority (2 * 2 + 1) x)) univ = 3 / 8 := by
  rw [fourierCoeff_signVal_majority_of_card_eq 2 2 (by simp)]
  norm_num [Nat.choose]

-- Two of the three bits of `(true, true, false)` are true; one of them is outside bit `0`.
example : #{j ∈ univ.erase (0 : Fin 3) | ![true, true, false] j = true} = 1 := by
  rw [card_filter_erase_eq_weight_update_false]
  decide

-- Exactly one of the first two of three uniformly random bits is true with probability `1 / 2`.
example :
    𝔼 x : Fin 3 → Bool, (if #{i ∈ ({0, 1} : Finset (Fin 3)) | x i = true} = 1 then (1 : ℝ) else 0) =
      1 / 2 := by
  rw [expect_ite_card_filter_eq, show #({0, 1} : Finset (Fin 3)) = 2 from rfl]
  norm_num

-- The weight is symmetric, so its coefficients on `{0}` and `{2}` agree.
example : fourierCoeff (fun x : Fin 3 → Bool => (weight x : ℝ)) {0} =
    fourierCoeff (fun x : Fin 3 → Bool => (weight x : ℝ)) {2} :=
  fourierCoeff_eq_of_card_eq (fun _ _ h => by rw [h]) rfl

-- Bit `0` of majority of three bits is pivotal exactly when the other two bits tie.
example : derivative 0 (fun x => signVal (majority (2 * 1 + 1) x)) ![false, true, false] = 1 := by
  rw [derivative_signVal_majority, ite_eq_left (by decide)]

example : derivative 0 (fun x => signVal (majority (2 * 1 + 1) x)) ![false, true, true] = 0 := by
  rw [derivative_signVal_majority, ite_eq_right (by decide)]

-- Complementary levels of majority of three bits: `|{0}| + |univ| = 4`, so the whole-set
-- coefficient is `(-1) ^ 1` times the singleton coefficient.
example : fourierCoeff maj₃ univ = -fourierCoeff maj₃ {0} := by
  rw [fourierCoeff_signVal_majority_of_card_add_card 1 (S := {0}) (T := univ) (by simp)]
  ring

-- The level-one weight is `3 (1 / 2) ^ 2 = 3 / 4` for three bits and `5 (3 / 8) ^ 2 = 45 / 64` for
-- five bits.
example : levelWeight (2 * 0 + 1) (fun x => signVal (majority (2 * 1 + 1) x)) = 3 / 4 := by
  rw [levelWeight_signVal_majority_of_odd]
  norm_num [Nat.choose]

example : levelWeight (2 * 0 + 1) (fun x => signVal (majority (2 * 2 + 1) x)) = 45 / 64 := by
  rw [levelWeight_signVal_majority_of_odd]
  norm_num [Nat.choose]

-- Majority of five bits has no weight on level two.
example : levelWeight 2 (fun x => signVal (majority (2 * 2 + 1) x)) = 0 :=
  levelWeight_signVal_majority_of_even 2 even_two

-- So the level-one weight of majority of five bits is below the `3 / 4` of three bits.
example : levelWeight (2 * 0 + 1) (fun x => signVal (majority (2 * (1 + 1) + 1) x)) < 3 / 4 := by
  refine (levelWeight_signVal_majority_succ_lt 1 0 (by norm_num)).trans_eq ?_
  rw [levelWeight_signVal_majority_of_odd]
  norm_num [Nat.choose]

-- By degree, the noise stability of majority of three bits is `3 / 4 ρ + 1 / 4 ρ ^ 3`.
example (ρ : ℝ) : noiseStability ρ maj₃ = 3 / 4 * ρ + 1 / 4 * ρ ^ 3 := by
  have h1 : levelWeight 1 maj₃ = 3 / 4 := by
    have := levelWeight_signVal_majority_of_odd 1 0
    norm_num [Nat.choose] at this
    exact this
  have h3 : levelWeight 3 maj₃ = 1 / 4 := by
    have := levelWeight_signVal_majority_of_odd 1 1
    norm_num [Nat.choose] at this
    exact this
  rw [noiseStability_eq_sum_levelWeight, Fintype.card_fin]
  simp only [sum_range_succ, sum_range_zero, h1, h3,
    levelWeight_signVal_majority_of_even 1 Even.zero,
    levelWeight_signVal_majority_of_even 1 even_two]
  ring

-- Majority of five bits is strictly less noise-stable than majority of three bits.
example : noiseStability (1 / 2) (fun x => signVal (majority (2 * (1 + 1) + 1) x)) <
    noiseStability (1 / 2) (fun x => signVal (majority (2 * 1 + 1) x)) :=
  noiseStability_signVal_majority_succ_lt 1 (by norm_num) (by norm_num)

-- On five bits, `5 W^5 = 1 · W^1`: the top weight is `(45 / 64) / 5 = 9 / 64`.
example : levelWeight (2 * (2 - 0) + 1) (fun x => signVal (majority (2 * 2 + 1) x)) = 9 / 64 := by
  have h := card_mul_levelWeight_signVal_majority 2 0 (by norm_num)
  rw [levelWeight_signVal_majority_of_odd 2 0] at h
  norm_num [Nat.choose] at h ⊢
  linarith

-- No coefficient of majority of five bits exceeds the singleton coefficient `C(4, 2) / 16 = 3 / 8`.
example (S : Finset (Fin (2 * 2 + 1))) :
    |fourierCoeff (fun x => signVal (majority (2 * 2 + 1) x)) S| ≤ 3 / 8 := by
  refine (abs_fourierCoeff_signVal_majority_le_singleton 2 S 0).trans_eq ?_
  rw [fourierCoeff_signVal_majority_singleton]
  norm_num [Nat.choose]

-- On seven bits the coefficient is `5 / 16` on a singleton and `-1 / 16` on three bits.
example : fourierCoeff (fun x => signVal (majority (2 * 3 + 1) x)) {0} = 5 / 16 := by
  rw [fourierCoeff_signVal_majority_singleton]
  norm_num [Nat.choose]

example : fourierCoeff (fun x => signVal (majority (2 * 3 + 1) x)) {0, 1, 2} = -1 / 16 := by
  rw [fourierCoeff_signVal_majority_of_card_eq 3 1 (by decide)]
  norm_num [Nat.choose]

-- The odd coefficients do not grow in size up to level `m + 2 = 5`.
example : |fourierCoeff (fun x => signVal (majority (2 * 3 + 1) x)) {0, 1, 2, 3, 4}| ≤
    |fourierCoeff (fun x => signVal (majority (2 * 3 + 1) x)) {0, 1, 2}| :=
  abs_fourierCoeff_signVal_majority_le_of_card_le 3 (by decide) (by decide) (by decide)
    (by decide)

-- Beyond level `m + 2` they grow again: the whole set has `5 / 16 > 1 / 16`.
example : |fourierCoeff (fun x => signVal (majority (2 * 3 + 1) x)) {0, 1, 2, 3, 4}| <
    |fourierCoeff (fun x => signVal (majority (2 * 3 + 1) x)) univ| := by
  rw [fourierCoeff_signVal_majority_of_card_eq 3 2 (by decide),
    fourierCoeff_signVal_majority_of_card_eq 3 3 (by simp)]
  norm_num [Nat.choose, abs_div]

end CslibFrontierTests.BooleanAnalysisMajorityFourier
