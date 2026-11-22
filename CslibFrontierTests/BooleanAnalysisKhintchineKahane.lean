/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.KhintchineKahane
public import CslibFrontier.Foundations.BooleanAnalysis.PolynomialThresholdWeight
import CslibFrontier.Foundations.BooleanAnalysis.Degree
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # Tests for the Khintchine–Kahane inequality and Theorem 5.2

The constant `2` of the Khintchine–Kahane inequality is the least one that works for every pair
of real weights [O'Donnell, Exercise 2.55(c)][ODonnell2014]; the inequality also applies in the
sup norm of `ℝ²`. The Laplacian along `0` fixes `x₀`, and translating `x₀` by `y` scales its
coefficient by `χ_{0}(y)`. The function `|x₀ + x₁|` is even, so it has no weight on `{0}`, and
the character `x₀ x₁` is even, so `2 Var[x₀ x₁] ≤ I[x₀ x₁] = 2`. The affine form `1 + x₀ + x₁`
has degree one and a nonzero constant term, so it goes through the extra-sign step of
Exercise 5.5; its sign is the two-bit AND (true = `-1`), a linear threshold function. Theorem 5.2
is checked for that AND, also through the form `x₀ + x₁`, which vanishes on half the cube, and for
a dictator. -/

public section

namespace CslibFrontierTests.KhintchineKahane

open Cslib BitString Finset
open scoped BigOperators

/-! ### The Khintchine–Kahane inequality -/

/-- `2` is the least constant `c` with `𝔼 ‖∑ᵢ xᵢ wᵢ‖² ≤ c (𝔼 ‖∑ᵢ xᵢ wᵢ‖)²` for all real
`w₀, w₁`. -/
theorem isLeast_two : IsLeast {c : ℝ | ∀ w : Fin 2 → ℝ,
    𝔼 x : Fin 2 → Bool, ‖∑ i, signVal (x i) • w i‖ ^ 2 ≤
      c * (𝔼 x : Fin 2 → Bool, ‖∑ i, signVal (x i) • w i‖) ^ 2} 2 :=
  ⟨fun w => expect_norm_sum_sq_le_two_mul_sq w,
    fun _ hc => two_le_of_forall_expect_norm_sum_sq_le hc⟩

/-- The inequality in the sup norm of `ℝ²`, for the two unit vectors. -/
example : 𝔼 x : Fin 2 → Bool, ‖∑ i, signVal (x i) • (Pi.single i 1 : Fin 2 → ℝ)‖ ^ 2 ≤
    2 * (𝔼 x : Fin 2 → Bool, ‖∑ i, signVal (x i) • (Pi.single i 1 : Fin 2 → ℝ)‖) ^ 2 :=
  expect_norm_sum_sq_le_two_mul_sq fun i => Pi.single i 1

/-- At the all-`false` point, `‖x₀ + x₁‖ = 2` bounds its Laplacian. -/
example : laplacian (fun x : Fin 2 → Bool => ‖∑ i, signVal (x i) • (1 : ℝ)‖) (fun _ => false) ≤
    2 :=
  (laplacian_norm_sum_le (fun _ => (1 : ℝ)) fun _ => false).trans_eq (by norm_num)

/-- The coordinate Laplacian of `x₀` along coordinate `0` is `x₀` itself. -/
example (x : Fin 2 → Bool) : coordLaplacian 0 (chi ℝ {0}) x = chi ℝ {0} x := by
  rw [coordLaplacian_eq_flip]
  simp only [chi_singleton, Function.update_self, signVal_not]
  ring

/-! ### Translates and even functions -/

/-- A nonzero function, `x₀`, has a positive second moment. -/
example : 0 < 𝔼 x : Fin 2 → Bool, chi ℝ {0} x ^ 2 :=
  Fintype.expect_sq_pos fun h => by simpa using congrFun h 0

/-- The character of `{0, 1}` is `1` at the all-`true` string. -/
example : chi ℝ ({0, 1} : Finset (Fin 2)) (fun _ => true) = 1 := by
  rw [chi_const_true, card_pair (by decide : (0 : Fin 2) ≠ 1)]
  norm_num

/-- Translating `x₀` by `y` multiplies its coefficient on `{0}` by `χ_{0}(y)`. -/
example (y : Fin 2 → Bool) : fourierCoeff (fun x => chi ℝ {0} (x + y)) {0} = chi ℝ {0} y := by
  rw [fourierCoeff_comp_add, fourierCoeff_chi]
  simp

/-- Complementing the input negates the coefficient of `x₀` on `{0}`. -/
example : fourierCoeff (fun x : Fin 2 → Bool => chi ℝ {0} fun i => !x i) {0} = -1 := by
  rw [fourierCoeff_comp_not, fourierCoeff_chi]
  simp

/-- `|x₀ + x₁|` is even, so it has no weight on `{0}`. -/
example : fourierCoeff (fun x : Fin 2 → Bool => |signVal (x 0) + signVal (x 1)|) {0} = 0 :=
  fourierCoeff_eq_zero_of_odd_card (fun x => by simp only [signVal_not, ← neg_add, abs_neg])
    (by simp)

/-- The character `x₀ x₁` is even, and `2 Var[x₀ x₁] ≤ I[x₀ x₁] = 2`. -/
example : 2 * 𝔼 x : Fin 2 → Bool, (chi ℝ {0, 1} x - 𝔼 y : Fin 2 → Bool, chi ℝ {0, 1} y) ^ 2 ≤
    2 := by
  have h := two_mul_expect_sub_expect_sq_le_totalInfluence_of_even
    (g := chi ℝ ({0, 1} : Finset (Fin 2))) fun x => by
      rw [chi_eq_prod_signVal, chi_eq_prod_signVal]
      simp only [signVal_not, prod_neg, card_pair (by decide : (0 : Fin 2) ≠ 1)]
      norm_num
  rwa [totalInfluence_chi, card_pair (by decide : (0 : Fin 2) ≠ 1), Nat.cast_ofNat] at h

/-! ### Affine forms -/

/-- The affine form `1 + x₀ + x₁`. -/
noncomputable def ell (x : Fin 2 → Bool) : ℝ := 1 + chi ℝ {0} x + chi ℝ {1} x

/-- `1 + x₀ + x₁` has degree at most one. -/
theorem ell_mem_lowDegree : ell ∈ lowDegree ℝ (Fin 2) 1 := by
  have hchi (i : Fin 2) : chi ℝ {i} ∈ lowDegree ℝ (Fin 2) 1 := by
    simpa only [card_singleton] using chi_mem_lowDegree (F := ℝ) ({i} : Finset (Fin 2))
  exact add_mem (add_mem (const_mem_lowDegree 1 1) (hchi 0)) (hchi 1)

/-- With one more sign, `|1 + x₀ + x₁|` has the moments of `|x₋ + x₀ + x₁|`. -/
example : 𝔼 y : Option (Fin 2) → Bool,
      |1 * signVal (y none) + ∑ i, 1 * signVal (y (some i))| =
    𝔼 x : Fin 2 → Bool, |1 + ∑ i, 1 * signVal (x i)| :=
  expect_signVal_none_mul_add_sum_eq (fun t => |t|) abs_neg 1 fun _ => 1

/-- The Khintchine–Kahane inequality for the affine form `1 + x₀ + x₁`. -/
example : 𝔼 x, ell x ^ 2 ≤ 2 * (𝔼 x, |ell x|) ^ 2 :=
  expect_sq_le_two_mul_expect_abs_sq_of_mem_lowDegree_one ell_mem_lowDegree

/-! ### Linear threshold functions -/

/-- Two-bit AND (true = `-1`) is the sign of `1 + x₀ + x₁`. -/
theorem signVal_and_mul_ell_pos (x : Fin 2 → Bool) : 0 < signVal (x 0 && x 1) * ell x := by
  simp only [ell, chi_singleton]
  cases x 0 <;> cases x 1 <;> norm_num

/-- Two-bit AND is a linear threshold function. -/
theorem isPTF_one_and : IsPTF 1 fun x : Fin 2 → Bool => x 0 && x 1 :=
  isPTF_iff.2 ⟨ell, mem_lowDegree_iff_fourierCoeff_eq_zero.1 ell_mem_lowDegree,
    signVal_and_mul_ell_pos⟩

/-- The Cauchy–Schwarz step for two-bit AND and `1 + x₀ + x₁`. -/
example : (𝔼 x, |ell x|) ^ 2 ≤
    (∑ S with #S ≤ 1, fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) S ^ 2) *
      𝔼 x, ell x ^ 2 :=
  sq_expect_abs_le_sum_fourierCoeff_sq_mul
    (fun S hS => mem_lowDegree_iff_fourierCoeff_eq_zero.1 ell_mem_lowDegree S
      (by simpa using hS))
    fun x => (signVal_and_mul_ell_pos x).le

/-- **Theorem 5.2** for two-bit AND, whose representing form has a constant term. -/
example : 1 / 2 ≤ ∑ S with #S ≤ 1,
    fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) S ^ 2 :=
  isPTF_one_and.one_half_le_sum_fourierCoeff_sq

/-- **Theorem 5.2** for two-bit AND through `x₀ + x₁`, which vanishes where the bits differ. -/
example : 1 / 2 ≤ ∑ S with #S ≤ 1,
    fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) S ^ 2 := by
  have hsum : (fun x : Fin 2 → Bool => chi ℝ {0} x + chi ℝ {1} x) ∈ lowDegree ℝ (Fin 2) 1 := by
    have hchi (i : Fin 2) : chi ℝ {i} ∈ lowDegree ℝ (Fin 2) 1 := by
      simpa only [card_singleton] using chi_mem_lowDegree (F := ℝ) ({i} : Finset (Fin 2))
    exact add_mem (hchi 0) (hchi 1)
  refine one_half_le_sum_fourierCoeff_sq_of_nonneg_mul hsum (fun h => ?_) fun x => ?_
  · have h0 := congrFun h fun _ => false
    simp only [chi_singleton, Pi.zero_apply] at h0
    norm_num at h0
  · simp only [chi_singleton]
    cases x 0 <;> cases x 1 <;> norm_num

/-- **Theorem 5.2** for the dictator `x ↦ x₀`. -/
example : 1 / 2 ≤ ∑ S with #S ≤ 1,
    fourierCoeff (fun x : Fin 3 → Bool => signVal (x 0)) S ^ 2 := by
  refine IsPTF.one_half_le_sum_fourierCoeff_sq (f := fun x => x 0) ?_
  refine isPTF_iff.2 ⟨chi ℝ {0}, fun S hS => ?_, fun x => ?_⟩
  · rw [fourierCoeff_chi, ite_eq_right_iff.2]
    rintro rfl
    simp at hS
  · rw [chi_singleton]
    cases x 0 <;> norm_num

end CslibFrontierTests.KhintchineKahane
