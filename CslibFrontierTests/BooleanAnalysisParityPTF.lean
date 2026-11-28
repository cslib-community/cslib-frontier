/-
Copyright (c) 2026 Josh Liebow-Feeser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Josh Liebow-Feeser
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.ParityPTF
import Mathlib.Tactic.NormNum

/-! # The PTF degree of parity

Checked witnesses for `CslibFrontier.Foundations.BooleanAnalysis.ParityPTF`:
* `parity 2` is a PTF of degree `2` (and over `{univ}`), and not of degree `1` (nor over
  `{∅, {0}, {1}}`).
* `parity 3` is a PTF of degree `3`, and not of degree `2`; any degree-`2` `p` with
  `0 ≤ signVal (parity 3 x) * p x` everywhere vanishes identically.
* A polynomial with zeros (`1 + χ_{0,1}`) has `0 ≤ signVal (parity 2 x) * p x` everywhere and
  strictly positive Fourier coefficient on `{0, 1}`.
* On `0` bits, `parity 0` is constantly `false` and has PTF degree `0`; `p = 0` witnesses why
  `p ≠ 0` cannot be omitted in the nonneg-product bounds.
-/

public section

namespace CslibFrontierTests.BooleanAnalysisParityPTF

open Cslib Cslib.BitString Finset

/-- `parity 2` is a polynomial threshold function of degree `2`. -/
theorem isPTF_two_parity_two : IsPTF 2 (parity 2) :=
  isPTF_parity_iff.2 le_rfl

/-- `parity 2` is not a linear threshold function (`IsPTF 1`). -/
theorem not_isPTF_one_parity_two : ¬ IsPTF 1 (parity 2) := by
  rw [isPTF_parity_iff]
  norm_num

/-- `parity 2` is a PTF over the singleton family `{univ}`. -/
theorem isPTFOn_univ_parity_two :
    IsPTFOn ({univ} : Finset (Finset (Fin 2))) (parity 2) := by
  rw [parity, isPTFOn_parityOn_iff]
  exact mem_singleton_self _

/-- `parity 2` is not a PTF over the proper subsets `{∅, {0}, {1}}`. -/
theorem not_isPTFOn_proper_parity_two :
    ¬ IsPTFOn ({∅, {0}, {1}} : Finset (Finset (Fin 2))) (parity 2) := by
  rw [parity, isPTFOn_parityOn_iff]
  decide

/-- `parity 3` is a polynomial threshold function of degree `3`. -/
theorem isPTF_three_parity_three : IsPTF 3 (parity 3) :=
  isPTF_parity_iff.2 le_rfl

/-- `parity 3` is not a polynomial threshold function of degree `2`. -/
theorem not_isPTF_two_parity_three : ¬ IsPTF 2 (parity 3) := by
  rw [isPTF_parity_iff]
  norm_num

/-- Any degree-`2` polynomial agreeing in sign with `parity 3` where nonzero is identically
zero. -/
theorem eq_zero_of_nonneg_mul_parity_three {p : BitString 3 → ℝ}
    (hpk : ∀ S : Finset (Fin 3), 2 < #S → fourierCoeff p S = 0)
    (hp : ∀ x, 0 ≤ signVal (parity 3 x) * p x) : p = 0 := by
  by_contra hp₀
  have hle := le_of_nonneg_mul_parity hpk hp₀ hp
  norm_num at hle

/-- A nonzero function with zeros (`1 + χ_{univ}`, vanishing on odd-weight inputs) satisfies
`0 ≤ signVal (parity 2 x) * p x` everywhere and has strictly positive top Fourier coefficient. -/
theorem fourierCoeff_pos_with_zeros :
    0 < fourierCoeff (fun x : BitString 2 => 1 + chi ℝ univ x) univ := by
  refine fourierCoeff_pos_of_nonneg_mul_parityOn (fun h => ?_) (fun x => ?_)
  · have := congrFun h (fun _ => false)
    norm_num [chi] at this
  · rw [← chi_eq_signVal_parityOn]
    rcases eq_or_ne (chi ℝ univ x) 1 with hx | hx
    · norm_num [hx]
    · have habs : |chi ℝ univ x| = 1 := abs_chi univ x
      have hx' : chi ℝ univ x = -1 := by
        rcases abs_eq (zero_le_one' ℝ) |>.1 habs with h | h
        · exact absurd h hx
        · exact h
      norm_num [hx']

/-- On `0` bits, `parity 0` is constantly `false`. -/
theorem parity_zero_eq_false (x : BitString 0) : parity 0 x = false := by
  simp [parity, parityOn_eq_sum]
  rfl

/-- On `0` bits, `parity 0` is a PTF of degree `0`. -/
theorem isPTF_zero_parity_zero : IsPTF 0 (parity 0) :=
  isPTF_parity_iff.2 le_rfl

/-- `p = 0` satisfies the remaining hypotheses of `le_of_nonneg_mul_parity` at `n = 2, k = 1`,
witnessing that `p ≠ 0` cannot be omitted. -/
theorem zero_satisfies_hypotheses_parity_two :
    (∀ S : Finset (Fin 2), 1 < #S → fourierCoeff (0 : BitString 2 → ℝ) S = 0) ∧
      (∀ x : BitString 2, 0 ≤ signVal (parity 2 x) * (0 : BitString 2 → ℝ) x) ∧
      ¬ (2 ≤ 1) := by
  refine ⟨fun S _ => ?_, fun x => by simp, by norm_num⟩
  simp [fourierCoeff]

end CslibFrontierTests.BooleanAnalysisParityPTF
