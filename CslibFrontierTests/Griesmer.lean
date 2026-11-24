/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

import CslibFrontier.Foundations.Data.Code.Griesmer
import CslibFrontier.Foundations.Data.Code.Singleton
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.NormNum.Prime

/-!
# Finite-field witness tests for residual codes, the Griesmer bound, and `$q$-ary simplex codes`

Exercises `Cslib.Code.residualLinear`, `le_minDist_residualLinear`,
`finrank_residualLinear_add_one`, `sum_ceilDiv_pow_le_card`, `add_sub_one_le_sum_ceilDiv_pow`,
`SimplexPoint`, `simplexEncode`, `simplexCode`, `card_simplexPoint`, `finrank_simplexCode`,
`hammingNorm_simplexEncode`, `minDist_simplexCode`, and `sum_ceilDiv_pow_simplexCode` via ordinary
`module` imports over `ZMod 2`, `ZMod 3`, and `ZMod 5`:

1. **Strict separation from Singleton and Hamming bounds over `ZMod 2` and `ZMod 3`**:
   * No binary `[7, 4, 4]_2` linear code exists (`4 + 2 + 1 + 1 = 8 > 7`), even though both the
     Singleton bound (`4 + 4 ≤ 7 + 1`) and the Hamming bound (`2 ^ 4 * (1 + 7) = 128 ≤ 2 ^ 7`) hold.
   * No ternary `[6, 3, 4]_3` linear code exists (`4 + 2 + 1 = 7 > 6`), even though the Singleton
     bound (`3 + 4 ≤ 6 + 1`) holds.
2. **Tight `[8, 4, 4]_2` extended binary Hamming code and exact weight-threshold boundary for
   `finrank_residualLinear_add_one`**:
   * Explicit `[8, 4, 4]_2` code attains Griesmer equality `4 + 2 + 1 + 1 = 8`, and puncturing at a
     weight-`4` codeword (`(2 - 1) * 4 = 4 < 2 * 4`) yields a `[4, 3, ≥ 2]_2` residual code.
   * Boundary witness: the all-ones codeword `c₁` of weight `8` satisfies
     `(2 - 1) * 8 = 8 = 2 * 4` (violating strict `<` at equality), and its residual code has
     dimension `0` (`0 + 1 ≠ 4`), confirming the `<` guard in `finrank_residualLinear_add_one` is
     sharp.
3. **Executable `$q$-ary simplex codes` over `ZMod 2` (`[7, 3, 4]_2`), `ZMod 3` (`[13, 3, 9]_3`),
   and `ZMod 5` (`[6, 2, 5]_5`)** attaining constant weight `q ^ (k - 1)` and exact Griesmer
   equality.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Griesmer

open Cslib Cslib.Code Finset
open scoped BigOperators

instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 3) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-! ### 1. Non-existence witnesses strictly refining Singleton and Hamming bounds -/

/-- No binary `[7, 4, 4]_2` linear code exists, even though `4 + 4 ≤ 7 + 1` (Singleton) and
`2 ^ 4 * (1 + 7) ≤ 2 ^ 7` (Hamming sphere-packing) both hold. -/
theorem not_exists_binary_linear_7_4_4 :
    (4 + 4 ≤ 7 + 1 ∧ 2 ^ 4 * (Nat.choose 7 0 + Nat.choose 7 1) ≤ 2 ^ 7) ∧
      ¬ ∃ C : Submodule (ZMod 2) (Fin 7 → ZMod 2),
        Module.finrank (ZMod 2) C = 4 ∧ (4 : ℕ∞) ≤ minDist (C : Set (Fin 7 → ZMod 2)) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨C, hdim, hd⟩
  have hg := sum_ceilDiv_pow_le_card C hd
  rw [hdim, ZMod.card 2, Fintype.card_fin] at hg
  simp only [Nat.ceilDiv_eq_add_pred_div] at hg
  exact absurd hg (by decide)

/-- No ternary `[6, 3, 4]_3` linear code exists, even though `3 + 4 ≤ 6 + 1` (Singleton) holds. -/
theorem not_exists_ternary_linear_6_3_4 :
    3 + 4 ≤ 6 + 1 ∧
      ¬ ∃ C : Submodule (ZMod 3) (Fin 6 → ZMod 3),
        Module.finrank (ZMod 3) C = 3 ∧ (4 : ℕ∞) ≤ minDist (C : Set (Fin 6 → ZMod 3)) := by
  refine ⟨by decide, ?_⟩
  rintro ⟨C, hdim, hd⟩
  have hg := sum_ceilDiv_pow_le_card C hd
  rw [hdim, ZMod.card 3, Fintype.card_fin] at hg
  simp only [Nat.ceilDiv_eq_add_pred_div] at hg
  exact absurd hg (by decide)

-- Arithmetic Singleton-refinement check: for `d = 9, k = 3, q = 3`, Singleton gives `9 + 2 = 11`,
-- whereas the Griesmer sum is `9 + 3 + 1 = 13`.
example : 9 + (3 - 1) ≤ ∑ i ∈ range 3, 9 ⌈/⌉ 3 ^ i ∧
    ∑ i ∈ range 3, 9 ⌈/⌉ 3 ^ i = 13 :=
  ⟨add_sub_one_le_sum_ceilDiv_pow (by decide) (by decide) (by decide), by
    simp only [Nat.ceilDiv_eq_add_pred_div]
    decide⟩

/-! ### 2. Explicit `[8, 4, 4]_2` extended Hamming code & sharp residual-code boundary -/

def extHammingMatrix : Matrix (Fin 4) (Fin 8) (ZMod 2) :=
  !![1, 0, 0, 0, 0, 1, 1, 1;
     0, 1, 0, 0, 1, 0, 1, 1;
     0, 0, 1, 0, 1, 1, 0, 1;
     0, 0, 0, 1, 1, 1, 1, 0]

def extHammingGen : (Fin 4 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun x j := ∑ i : Fin 4, x i * extHammingMatrix i j
  map_add' x y := funext fun j => by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := funext fun j => by simp [mul_assoc, ← Finset.mul_sum]

def extHammingCode : Submodule (ZMod 2) (Fin 8 → ZMod 2) :=
  LinearMap.range extHammingGen

lemma extHammingGen_injective : Function.Injective extHammingGen := by
  decide

lemma finrank_extHammingCode : Module.finrank (ZMod 2) extHammingCode = 4 := by
  rw [extHammingCode, LinearMap.finrank_range_of_inj extHammingGen_injective,
    Module.finrank_fin_fun]

lemma minDist_extHammingCode :
    minDist (extHammingCode : Set (Fin 8 → ZMod 2)) = 4 := by
  refine le_antisymm ?_ ?_
  · have hmem : extHammingGen ![1, 0, 0, 0] ∈ extHammingCode := ⟨![1, 0, 0, 0], rfl⟩
    have hne : extHammingGen ![1, 0, 0, 0] ≠ 0 := by decide
    have hwt : hammingNorm (extHammingGen ![1, 0, 0, 0]) = 4 := by decide
    have hle := minDist_le_hammingDist hmem extHammingCode.zero_mem hne
    rwa [hammingDist_zero_right, hwt] at hle
  · refine (le_minDist_iff_hammingNorm extHammingCode).2 fun w hw hw0 => ?_
    obtain ⟨x, rfl⟩ := hw
    have hx0 : x ≠ 0 := fun h0 => hw0 (by simp [h0])
    have hall : ∀ u : Fin 4 → ZMod 2, u ≠ 0 → 4 ≤ hammingNorm (extHammingGen u) := by decide
    exact Nat.cast_le.2 (hall x hx0)

/-- `extHammingCode` attains the `[8, 4, 4]_2` Griesmer bound with equality, and its residual code
at the weight-`4` codeword `extHammingGen ![1, 0, 0, 0]` is a `[4, 3, ≥ 2]_2` code. -/
theorem test_extHammingCode_griesmer_and_residual :
    ∑ i ∈ range (Module.finrank (ZMod 2) extHammingCode),
        4 ⌈/⌉ Fintype.card (ZMod 2) ^ i = Fintype.card (Fin 8) ∧
      Module.finrank (ZMod 2) (residualLinear extHammingCode (extHammingGen ![1, 0, 0, 0])) = 3 ∧
      (2 : ℕ∞) ≤ minDist
        (residualLinear extHammingCode (extHammingGen ![1, 0, 0, 0]) :
          Set ({i : Fin 8 // extHammingGen ![1, 0, 0, 0] i = 0} → ZMod 2)) := by
  have hc : extHammingGen ![1, 0, 0, 0] ∈ extHammingCode := ⟨![1, 0, 0, 0], rfl⟩
  have hc0 : extHammingGen ![1, 0, 0, 0] ≠ 0 := by decide
  have hwt : hammingNorm (extHammingGen ![1, 0, 0, 0]) = 4 := by decide
  have hd : (4 : ℕ∞) ≤ minDist (extHammingCode : Set (Fin 8 → ZMod 2)) :=
    minDist_extHammingCode.ge
  refine ⟨?_, ?_, ?_⟩
  · rw [finrank_extHammingCode, ZMod.card 2, Fintype.card_fin]
    simp only [Nat.ceilDiv_eq_add_pred_div]
    decide
  · have hdim := finrank_residualLinear_add_one hc hc0 hd (by simp [ZMod.card, hwt])
    rw [finrank_extHammingCode] at hdim
    omega
  · have hres := le_minDist_residualLinear hc hd
    have hval : (Fintype.card (ZMod 2) * 4 -
        (Fintype.card (ZMod 2) - 1) * hammingNorm (extHammingGen ![1, 0, 0, 0])) ⌈/⌉
        Fintype.card (ZMod 2) = 2 := by
      rw [ZMod.card 2, hwt, Nat.ceilDiv_eq_add_pred_div]
    rwa [hval] at hres

/-- Sharpness of `(q - 1) * wt(c) < q * d` in `finrank_residualLinear_add_one`: the all-ones
codeword `c₁ = extHammingGen ![1, 1, 1, 1]` has `(2 - 1) * 8 = 2 * 4`, and its residual code has
dimension `0` (`0 + 1 ≠ 4`). -/
theorem test_residualLinear_weight_threshold_sharp :
    let c₁ := extHammingGen ![1, 1, 1, 1]
    c₁ ∈ extHammingCode ∧ c₁ ≠ 0 ∧
      (Fintype.card (ZMod 2) - 1) * hammingNorm c₁ = Fintype.card (ZMod 2) * 4 ∧
      Module.finrank (ZMod 2) (residualLinear extHammingCode c₁) + 1 ≠
        Module.finrank (ZMod 2) extHammingCode := by
  dsimp only
  refine ⟨⟨![1, 1, 1, 1], rfl⟩, by decide, ?_, ?_⟩
  · have hwt : hammingNorm (extHammingGen ![1, 1, 1, 1]) = 8 := by decide
    simp [ZMod.card, hwt]
  · have hle := Submodule.finrank_le
      (residualLinear extHammingCode (extHammingGen ![1, 1, 1, 1]))
    rw [Module.finrank_fintype_fun_eq_card] at hle
    have hcard0 : Fintype.card {i : Fin 8 // extHammingGen ![1, 1, 1, 1] i = 0} = 0 := by decide
    rw [finrank_extHammingCode]
    omega

/-! ### 3. Executable `$q$-ary simplex codes` over `ZMod 2`, `ZMod 3`, and `ZMod 5` -/

theorem test_binary_simplex_7_3_4 :
    Fintype.card (SimplexPoint (ZMod 2) 3) = 7 ∧
      Module.finrank (ZMod 2) (simplexCode (ZMod 2) 3) = 3 ∧
      hammingNorm (simplexEncode (ZMod 2) 3 ![1, 0, 1]) = 4 ∧
      minDist (simplexCode (ZMod 2) 3 : Set (SimplexPoint (ZMod 2) 3 → ZMod 2)) = 4 ∧
      ∑ i ∈ range (Module.finrank (ZMod 2) (simplexCode (ZMod 2) 3)),
        4 ⌈/⌉ Fintype.card (ZMod 2) ^ i = Fintype.card (SimplexPoint (ZMod 2) 3) := by
  refine ⟨by decide, finrank_simplexCode _ 3, by decide, ?_, ?_⟩
  · rw [minDist_simplexCode (by decide), ZMod.card 2]
    norm_num
  · simpa [ZMod.card] using sum_ceilDiv_pow_simplexCode (ZMod 2) (k := 3) (by decide)

theorem test_ternary_simplex_13_3_9 :
    Fintype.card (SimplexPoint (ZMod 3) 3) = 13 ∧
      Module.finrank (ZMod 3) (simplexCode (ZMod 3) 3) = 3 ∧
      hammingNorm (simplexEncode (ZMod 3) 3 ![1, 2, 1]) = 9 ∧
      minDist (simplexCode (ZMod 3) 3 : Set (SimplexPoint (ZMod 3) 3 → ZMod 3)) = 9 ∧
      ∑ i ∈ range (Module.finrank (ZMod 3) (simplexCode (ZMod 3) 3)),
        9 ⌈/⌉ Fintype.card (ZMod 3) ^ i = Fintype.card (SimplexPoint (ZMod 3) 3) := by
  refine ⟨by decide, finrank_simplexCode _ 3, by decide, ?_, ?_⟩
  · rw [minDist_simplexCode (by decide), ZMod.card 3]
    norm_num
  · simpa [ZMod.card] using sum_ceilDiv_pow_simplexCode (ZMod 3) (k := 3) (by decide)

theorem test_quinary_simplex_6_2_5 :
    Fintype.card (SimplexPoint (ZMod 5) 2) = 6 ∧
      Module.finrank (ZMod 5) (simplexCode (ZMod 5) 2) = 2 ∧
      minDist (simplexCode (ZMod 5) 2 : Set (SimplexPoint (ZMod 5) 2 → ZMod 5)) = 5 ∧
      Module.finrank (ZMod 5) (simplexCode (ZMod 5) 2) + 5 =
        Fintype.card (SimplexPoint (ZMod 5) 2) + 1 ∧
      ∑ i ∈ range (Module.finrank (ZMod 5) (simplexCode (ZMod 5) 2)),
        5 ⌈/⌉ Fintype.card (ZMod 5) ^ i = Fintype.card (SimplexPoint (ZMod 5) 2) := by
  refine ⟨by decide, finrank_simplexCode _ 2, ?_, ?_, ?_⟩
  · rw [minDist_simplexCode (by decide), ZMod.card 5]
    norm_num
  · rw [finrank_simplexCode]
    decide
  · simpa [ZMod.card] using sum_ceilDiv_pow_simplexCode (ZMod 5) (k := 2) (by decide)

end CslibFrontierTests.Griesmer
