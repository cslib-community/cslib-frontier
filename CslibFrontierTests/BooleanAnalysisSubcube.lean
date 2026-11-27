/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.Subcube
public import CslibFrontier.Foundations.Data.BitString.AgreeExpect
import CslibFrontier.Foundations.Data.Finset.Expect

/-! # The Fourier expansion of a subcube

The characters of the subsets of `{0}` at two points of `Fin 2 → Bool`, summed, are `2` when the
points agree at `0` and `0` when they do not. The conjunction of two bits, as a `0`/`1` indicator,
is the subcube of codimension two where both bits are `true`: it has density `1 / 4`, coefficient
`-1 / 4` on `{0}` (also checked by brute force over the four inputs), and degree-one weight
`2 · (1 / 4) ^ 2 = 1 / 8`. A coefficient outside the constraints is `0`, the subcube of codimension
zero has density `1`, and the subcube where `x₀ = true` and `x₁ = false` has density `1 / 4` and
the positive coefficient `1 / 4` on `{1}`.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisSubcube

open Cslib Cslib.BitString Finset
open scoped BigOperators

-- Two points that agree at `0`: the sum over the subsets of `{0}` is `2 ^ 1`.
example : ∑ S ∈ ({0} : Finset (Fin 2)).powerset,
    chi ℤ S ![true, false] * chi ℤ S ![true, true] = 2 := by
  rw [sum_powerset_chi_mul_chi, ite_eq_left (by decide)]
  simp

-- Two points that differ at `0`: the sum is `0`.
example : ∑ S ∈ ({0} : Finset (Fin 2)).powerset,
    chi ℤ S ![true, false] * chi ℤ S ![false, false] = 0 := by
  rw [sum_powerset_chi_mul_chi, ite_eq_right (by decide)]

/-- The conjunction of two bits as a `0`/`1` indicator. -/
noncomputable abbrev and₂ (x : Fin 2 → Bool) : ℝ :=
  if ∀ i ∈ (univ : Finset (Fin 2)), x i = true then 1 else 0

example : 𝔼 x, and₂ x = 1 / 4 := by
  rw [expect_ite_forall_mem_eq]
  norm_num

example : fourierCoeff and₂ {0} = -1 / 4 := by
  rw [fourierCoeff_ite_forall_mem_eq, ite_eq_left (subset_univ _), chi_singleton]
  norm_num

-- Brute force over the four inputs gives the same `-1 / 4`.
example : fourierCoeff and₂ {0} = -1 / 4 := by
  simp only [fourierCoeff, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  simp [and₂, chi, Fin.forall_fin_two]
  norm_num

example : levelWeight 1 and₂ = 1 / 8 := by
  rw [levelWeight_one_ite_forall_mem_eq]
  norm_num

-- The same weight as the sum of the squared degree-one coefficients.
example : ∑ i, fourierCoeff and₂ {i} ^ 2 = 1 / 8 := by
  rw [← levelWeight_one, levelWeight_one_ite_forall_mem_eq]
  norm_num

-- A coordinate outside the subcube's constraints has coefficient `0`.
example : fourierCoeff (fun x : Fin 2 → Bool =>
    if ∀ i ∈ ({0} : Finset (Fin 2)), x i = true then (1 : ℝ) else 0) {1} = 0 := by
  rw [fourierCoeff_ite_forall_mem_eq, ite_eq_right (by decide)]

-- The subcube of codimension zero is the whole cube.
example : 𝔼 x : Fin 2 → Bool,
    (if ∀ i ∈ (∅ : Finset (Fin 2)), x i = true then (1 : ℝ) else 0) = 1 := by
  rw [expect_ite_forall_mem_eq]
  simp

-- The subcube where `x₀ = true` and `x₁ = false` has density `1 / 4`.
example : 𝔼 x : Fin 2 → Bool,
    (if ∀ i ∈ (univ : Finset (Fin 2)), x i = ![true, false] i then (1 : ℝ) else 0) = 1 / 4 := by
  rw [expect_ite_forall_mem_eq]
  norm_num

-- The sign `χ_S(b)`: where `x₀ = true` and `x₁ = false`, the coefficient on `{1}` is `+1 / 4`.
example : fourierCoeff (fun x : Fin 2 → Bool =>
    if ∀ i ∈ (univ : Finset (Fin 2)), x i = ![true, false] i then (1 : ℝ) else 0) {1} =
      1 / 4 := by
  rw [fourierCoeff_ite_forall_mem_eq, ite_eq_left (subset_univ _), chi_singleton]
  norm_num

end CslibFrontierTests.BooleanAnalysisSubcube
