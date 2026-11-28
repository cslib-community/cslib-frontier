/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Foundations.Data.Code.ProximityGap.Curve
import CslibFrontier.Foundations.Data.Hamming
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for weighted, curve, and affine-space proximity gaps

Exercises `CslibFrontier.Foundations.Data.Code.ProximityGap.Curve` via ordinary `module` imports
on concrete finite-field Reed–Solomon instances:
1. **Non-constant `ℕ`-weighted & `ℚ`-weighted correlated agreement on lines and degree-2 curves
   over `ZMod 11`** (`n = 5`, `k = 3`, `e = 1`): uses genuinely non-uniform weights
   `W = ![0, 2, 2, 2, 1]` (`M = 2`, `B = 7`) and `μ = ![0, 1, 1, 1, 1 / 2]` (`θ = 7 / 2`) with
   corrupted words `u₀, u₁, u₂ ∉ RS`.
2. **Negative / tightness weighted dichotomy over `ZMod 11`:** uses non-constant weights
   `W = ![1, 1, 2, 2, 2]` on disjoint spikes (`z = 0` achieves weight `7`, `z = 1` achieves weight
   `< 7` for every codeword) to instantiate `weighted_proximityGap_unique`.
3. **2D affine space (`ℓ = 2`) over `ZMod 23`:**
   - Positive nonzero-error instantiation of
     `exists_uniqueMaximal_correlatedAgreement_affine_unique`,
     `exists_correlatedAgreement_affine_of_curve`, and
     `exists_weighted_correlatedAgreement_affine_unique_sharp` with three corrupted words `∉ RS`;
   - Upper-bound regression for `proximityGap_affine_unique` proving at most `115`
     (`23 * #T ≤ 5 * 23 ^ 2 = 2645`) of the `529` affine combinations lie within distance `1`
     of the code.
4. **Dimension-independent 2D affine space (`ℓ = 2`) over `ZMod 11` (`5 * 120 = 600 < 10 * #T`):**
   - Here the linear-in-`ℓ` bound `2 * (5 + 1) * 11 = 132 > 121 = 11 ^ 2` is vacuous even on the
     entire plane, while the dimension-independent thresholds are `#T > 55` (exact unweighted) and
     `#T > 60` (weighted);
   - Positive unweighted, `ℕ`-weighted, and `ℚ`-weighted correlated agreement on a proper subset
     `T` of size `66 < 121` (`exists_uniqueMaximal_correlatedAgreement_affine_unique`,
     `exists_weighted_correlatedAgreement_affine_unique_sharp`,
     `exists_ratWeighted_correlatedAgreement_affine_unique_sharp`);
   - Weighted upper-bound regressions proving at most `60` of the `121` affine points lie close
     (`weighted_proximityGap_affine_unique_sharp`,
     `ratWeighted_proximityGap_affine_unique_sharp`).
5. **Beyond-unique-decoding Johnson 2D affine spaces & `ℚ`-weighted curves over `ZMod 65537`
   (`n = 5`, `k = 2`, `e = 2 > 1`, `m = 1`, `D = 2`, `L = 2`):**
   - List-premise-free unweighted, `ℕ`-weighted, and `ℚ`-weighted 2D affine correlated agreement on
     proper subsets of `Fin 2 → ZMod 65537` at exact threshold `B_line * |F| ^ ℓ < |F| * #T`, with
     corrupted words `∉ RS`;
   - `ℚ`-weighted line and degree-2 curve Johnson correlated agreement
     (`exists_ratWeighted_correlatedAgreement_line_johnson`,
     `exists_ratWeighted_correlatedAgreement_curve_johnson`);
   - Negative / tightness exact Johnson 2D affine dichotomies
     (`proximityGap_affine_johnson_exact`, `weighted_proximityGap_affine_johnson_exact`,
     `ratWeighted_proximityGap_affine_johnson_exact`) with exact denominator `|F|`, using the
     parabola `u₀ i = (α i) ^ 2`.
6. **Genuine multiplicity `m = 2` beyond-unique-decoding 2D affine space over `ZMod 200003`:**
   `n = 5`, `k = 2`, `e = 2 > 1`, `m = 2`, `D = 5`, `L = 5`, `B_line = 30807`, on the proper strip
   `strip2D 200003 30808`.
7. **Beyond-unique-decoding real-asymptotic curve & affine dichotomies and closed-form correlated
   agreement over `GaloisField 11 14`:**
   `n = 9`, `k = 1`, `e = 5 > 4 = (9 - 1) / 2`, `m = 2`, `η = 1 / 9`, exercising all 8
   real-asymptotic curve and dimension-independent affine dichotomies plus all 6 closed-form
   `_of_multiplicity` and `_of_eta` affine correlated-agreement theorems on corrupted words `∉ RS`.
8. **List-premise-free affine correlated agreement over `ZMod 2003` (`1698 < 2003 < 3396`):**
   `n = 5`, `k = 2`, `e = 2 > 1`, `m = 1`, `D = 2`, `L = 2`, `B_line = 1698`, where
   `L * B_line = 3396 > 2003 = |F|` refutes the former list-size premise while
   `exists_correlatedAgreement_affine_johnson` fires on `strip2D 2003 1699`.
9. **Zero-weight coordinate regression (`W 0 = 0`, `μ 0 = 0`) over `ZMod 65537`:**
   `u₀ = 0` and a generator corrupted solely at coordinate `0` (`∉ RS`), refuting naive
   `D'_1 = univ` at `u* = 0` while exercising `exists_weighted_correlatedAgreement_affine_of_line`,
   `exists_weighted_correlatedAgreement_affine_of_divergence`,
   `exists_weighted_correlatedAgreement_affine_johnson`, and
   `exists_ratWeighted_correlatedAgreement_affine_johnson` at full weight `B_W = 6` (`0 ∉ D'`).
10. **Exact eq. (1.2) Theorem 1.6 uniqueness & maximality tests and sharpness counterexample:**
    - Positive 2D affine space over `ZMod 11` (`n = 5`, `k = 3`, `e = 1`) on a proper subset `T56`
      of size `56` (`5 * 11 ^ 2 = 605 < 616 = 11 * 56`, strictly below the weighted `61` cutoff
      where `10 * 56 = 560 ≤ 600`), instantiating
      `exists_uniqueMaximal_correlatedAgreement_affine_unique`, pinning `D' = Finset.univ.erase 0`,
      unique codewords `(v0 11, ![v1 11, v2 11])`, and the literal `∃!` maximal-set consequence;
    - Upper-bound regression for `proximityGap_affine_unique` bounding `#T ≤ 55` out of `121`
      (separate finite enumeration of the quadratic code over `ZMod 11` gives `44` close pairs);
    - One-point (`ℓ = 0`) regression exercising the weighted theorems at `n = q` over `ZMod 5`
      and `exists_uniqueMaximal_correlatedAgreement_affine_unique` at `n < q` over `ZMod 11`;
    - Sharpness counterexample at `2 * e + k = n + 1` (`n = 5`, `k = 2`, `e = 2` over `ZMod 11`)
      exhibiting two distinct maximal qualifying sets `{0, 1, 2}` and `{0, 3, 4}` with distinct
      codewords `0 ≠ pts5 11`, showing `2 * e + k ≤ n` is sharp for Theorem 1.6's uniqueness clause.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.Data.Code.ProximityGap.Curve

open scoped BigOperators
open Cslib Cslib.Code Finset Polynomial

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩
instance : Fact (Nat.Prime 23) := ⟨by decide⟩

/-! ### Shared helpers over `ZMod p` -/

/-- Five distinct evaluation points `0, 1, 2, 3, 4` in `ZMod p`. -/
private def pts5 (p : ℕ) : Fin 5 → ZMod p := fun i => (i : ℕ)

private theorem pts5_5_injective : Function.Injective (pts5 5) := by decide
private theorem pts5_11_injective : Function.Injective (pts5 11) := by decide
private theorem pts5_23_injective : Function.Injective (pts5 23) := by decide

private theorem eval_eq_of_degree_lt_three {p : ℕ} [Fact (Nat.Prime p)]
    {f : (ZMod p)[X]} (hf : f.degree < (3 : ℕ)) (x : ZMod p) :
    f.eval x = f.coeff 0 + f.coeff 1 * x + f.coeff 2 * x ^ 2 := by
  have hdeg : f.natDegree < 3 := by
    by_cases hf0 : f = 0
    · rw [hf0, natDegree_zero]; decide
    · exact (natDegree_lt_iff_degree_lt hf0).2 hf
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, mul_one, pow_one]

private theorem third_diff_zero_of_mem_rs {p : ℕ} [Fact (Nat.Prime p)]
    {c : Fin 5 → ZMod p} (hc : c ∈ reedSolomon (pts5 p) 3) :
    c 0 - 3 * c 1 + 3 * c 2 - c 3 = 0 := by
  obtain ⟨f, hf, rfl⟩ := mem_reedSolomon.1 hc
  simp only [eval_eq_of_degree_lt_three hf, pts5, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  change (f.coeff 0 + f.coeff 1 * 0 + f.coeff 2 * 0 ^ 2) -
      3 * (f.coeff 0 + f.coeff 1 * 1 + f.coeff 2 * 1 ^ 2) +
      3 * (f.coeff 0 + f.coeff 1 * 2 + f.coeff 2 * 2 ^ 2) -
      (f.coeff 0 + f.coeff 1 * 3 + f.coeff 2 * 3 ^ 2) = 0
  ring

private theorem card_agree_add_hammingDist {p : ℕ} {n : ℕ} (x y : Fin n → ZMod p) :
    (Finset.univ.filter fun i => x i = y i).card + hammingDist x y = n := by
  simpa only [Fintype.card_fin] using card_filter_eq_add_hammingDist x y

/-- Underlying codewords and corrupted words over `ZMod p` sharing a single error at index `0`. -/
private noncomputable def v0 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => (1 + X ^ 2 : (ZMod p)[X]).eval (pts5 p i)

private noncomputable def v1 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => (C (2 : ZMod p) * X).eval (pts5 p i)

private def v2 (p : ℕ) : Fin 5 → ZMod p := fun _ => 3

private noncomputable def u0 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => if i = 0 then v0 p i + 1 else v0 p i

private noncomputable def u1 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => if i = 0 then v1 p i + 3 else v1 p i

private def u2 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => if i = 0 then 5 else 3

private theorem v0_mem_rs {p : ℕ} [Fact (Nat.Prime p)] : v0 p ∈ reedSolomon (pts5 p) 3 := by
  refine eval_mem_reedSolomon (pts5 p) ?_
  have h1 : (1 : (ZMod p)[X]).degree < (3 : ℕ) := by
    rw [degree_one]; exact Nat.cast_lt.2 (by decide)
  have h2 : (X ^ 2 : (ZMod p)[X]).degree < (3 : ℕ) := by
    rw [degree_X_pow]; exact Nat.cast_lt.2 (by decide)
  exact (degree_add_le _ _).trans_lt (max_lt h1 h2)

private theorem v1_mem_rs {p : ℕ} [Fact (Nat.Prime p)] : v1 p ∈ reedSolomon (pts5 p) 3 := by
  refine eval_mem_reedSolomon (pts5 p) ?_
  refine (degree_mul_le _ _).trans_lt ?_
  have h1 : (C (2 : ZMod p)).degree ≤ 0 := degree_C_le
  have h2 : (X : (ZMod p)[X]).degree = 1 := degree_X
  rw [h2]
  exact (add_le_add h1 le_rfl).trans_lt (by rw [zero_add]; exact Nat.cast_lt.2 (by decide))

private theorem v2_mem_rs {p : ℕ} [Fact (Nat.Prime p)] : v2 p ∈ reedSolomon (pts5 p) 3 := by
  refine mem_reedSolomon.2 ⟨C 3, ?_, funext fun _ => eval_C⟩
  exact degree_C_le.trans_lt (Nat.cast_lt.2 (by decide))

private theorem u0_not_mem_rs_11 : u0 11 ∉ reedSolomon (pts5 11) 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u0 11 0 - 3 * u0 11 1 + 3 * u0 11 2 - u0 11 3 = 1 := by
    simp only [u0, v0, pts5, eval_add, eval_one, eval_pow, eval_X]; decide
  rw [hval] at hdiff
  exact one_ne_zero hdiff

private theorem u1_not_mem_rs_11 : u1 11 ∉ reedSolomon (pts5 11) 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u1 11 0 - 3 * u1 11 1 + 3 * u1 11 2 - u1 11 3 = 3 := by
    simp only [u1, v1, pts5, eval_mul, eval_C, eval_X]; decide
  rw [hval] at hdiff
  exact (by decide : (3 : ZMod 11) ≠ 0) hdiff

private theorem u2_not_mem_rs_11 : u2 11 ∉ reedSolomon (pts5 11) 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u2 11 0 - 3 * u2 11 1 + 3 * u2 11 2 - u2 11 3 = 2 := by
    simp only [u2]; decide
  rw [hval] at hdiff
  exact (by decide : (2 : ZMod 11) ≠ 0) hdiff

private theorem u0_not_mem_rs_23 : u0 23 ∉ reedSolomon (pts5 23) 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u0 23 0 - 3 * u0 23 1 + 3 * u0 23 2 - u0 23 3 = 1 := by
    simp only [u0, v0, pts5, eval_add, eval_one, eval_pow, eval_X]; decide
  rw [hval] at hdiff
  exact one_ne_zero hdiff

private theorem u1_not_mem_rs_23 : u1 23 ∉ reedSolomon (pts5 23) 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u1 23 0 - 3 * u1 23 1 + 3 * u1 23 2 - u1 23 3 = 3 := by
    simp only [u1, v1, pts5, eval_mul, eval_C, eval_X]; decide
  rw [hval] at hdiff
  exact (by decide : (3 : ZMod 23) ≠ 0) hdiff

private theorem u2_not_mem_rs_23 : u2 23 ∉ reedSolomon (pts5 23) 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u2 23 0 - 3 * u2 23 1 + 3 * u2 23 2 - u2 23 3 = 2 := by
    simp only [u2]; decide
  rw [hval] at hdiff
  exact (by decide : (2 : ZMod 23) ≠ 0) hdiff

/-! ### Test 1: Non-constant `ℕ`-weighted & `ℚ`-weighted correlated agreement (lines & curves) -/

/-- Non-constant integer weights taking all three values `{0, 1, 2}` (`M = 2`). -/
private def wNonConst : Fin 5 → ℕ := ![0, 2, 2, 2, 1]

/-- Matching non-constant rational weights in `[0, 1]` taking `{0, 1/2, 1}`. -/
private def muNonConst : Fin 5 → ℚ := ![0, 1, 1, 1, (1 : ℚ) / 2]

/-- Positive non-constant `ℕ`-weighted line instantiation of
`exists_weighted_correlatedAgreement_unique` over `ZMod 11` (`W = ![0, 2, 2, 2, 1]`, `M = 2`,
`B = 7`, `#S = 6 > 5`). -/
theorem test_weighted_correlatedAgreement_unique_positive :
    u0 11 ∉ reedSolomon (pts5 11) 3 ∧
    u1 11 ∉ reedSolomon (pts5 11) 3 ∧
    ∃ D' : Finset (Fin 5), 7 ≤ ∑ i ∈ D', wNonConst i ∧
      ∃ v₀ ∈ reedSolomon (pts5 11) 3, ∃ v₁ ∈ reedSolomon (pts5 11) 3,
        ∀ i ∈ D', u0 11 i = v₀ i ∧ u1 11 i = v₁ i := by
  let S : Finset (ZMod 11) := {0, 1, 2, 3, 4, 5}
  have hS : Fintype.card (Fin 5) < S.card := by decide
  have hW : ∀ i : Fin 5, wNonConst i ≤ 2 := by decide
  have hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon (pts5 11) 3,
      7 ≤ ∑ i ∈ Finset.univ.filter (fun i => (u0 11 + z • u1 11) i = c i), wNonConst i := by
    intro z _
    refine ⟨v0 11 + z • v1 11,
      Submodule.add_mem _ v0_mem_rs (Submodule.smul_mem _ z v1_mem_rs), ?_⟩
    have hD : 7 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 5), wNonConst i := by decide
    refine hD.trans (Finset.sum_le_sum_of_subset ?_)
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    refine mem_filter.2 ⟨mem_univ i, ?_⟩
    simp only [u0, u1, Pi.add_apply, Pi.smul_apply, hne, ↓reduceIte]
  obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hagree⟩ :=
    exists_weighted_correlatedAgreement_unique pts5_11_injective (k := 3) (M := 2) (B := 7)
      (by decide) hW (by decide) (u0 11) (u1 11) S hS hclose
  exact ⟨u0_not_mem_rs_11, u1_not_mem_rs_11, D', hD', v₀, hv₀, v₁, hv₁, hagree⟩

/-- Positive non-constant `ℚ`-weighted degree-2 curve instantiation of
`exists_ratWeighted_correlatedAgreement_curve_unique` over `ZMod 11` (`μ = ![0, 1, 1, 1, 1/2]`,
`θ = 7/2`, `2 * 5 = 10 < 11`). -/
theorem test_ratWeighted_correlatedAgreement_curve_deg2 :
    u2 11 ∉ reedSolomon (pts5 11) 3 ∧
    ∃ D' : Finset (Fin 5), (7 : ℚ) / 2 ≤ ∑ i ∈ D', muNonConst i ∧
      ∃ v : Fin 3 → (Fin 5 → ZMod 11), (∀ j, v j ∈ reedSolomon (pts5 11) 3) ∧
        ∀ i ∈ D', ∀ j, (![u0 11, u1 11, u2 11] j) i = v j i := by
  let u : Fin 3 → (Fin 5 → ZMod 11) := ![u0 11, u1 11, u2 11]
  let vTrue : Fin 3 → (Fin 5 → ZMod 11) := ![v0 11, v1 11, v2 11]
  have hvTrue_mem : ∀ j : Fin 3, vTrue j ∈ reedSolomon (pts5 11) 3 := by
    intro j; fin_cases j
    · exact v0_mem_rs
    · exact v1_mem_rs
    · exact v2_mem_rs
  have hμ_le : ∀ i : Fin 5, muNonConst i ≤ 1 := by
    intro i; fin_cases i <;> norm_num [muNonConst]
  have hμ_nonneg : ∀ i : Fin 5, 0 ≤ muNonConst i := by
    intro i; fin_cases i <;> norm_num [muNonConst]
  have hagree_true : ∀ i ∈ Finset.univ.erase (0 : Fin 5), ∀ j : Fin 3, u j i = vTrue j i := by
    intro i hi j
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    fin_cases j
    · change u0 11 i = v0 11 i; simp only [u0, hne, ↓reduceIte]
    · change u1 11 i = v1 11 i; simp only [u1, hne, ↓reduceIte]
    · change u2 11 i = v2 11 i; simp only [u2, v2, hne, ↓reduceIte]
  have hclose : ∀ z ∈ (Finset.univ : Finset (ZMod 11)), ∃ c ∈ reedSolomon (pts5 11) 3,
      (7 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (∑ j : Fin 3, z ^ (j : ℕ) • u j) i = c i), muNonConst i := by
    intro z _
    refine ⟨∑ j : Fin 3, z ^ (j : ℕ) • vTrue j,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j), ?_⟩
    have hsum_er : (7 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 5), muNonConst i := by
      have hset : Finset.univ.erase (0 : Fin 5) = {1, 2, 3, 4} := by decide
      rw [hset]
      norm_num [muNonConst]
    exact hsum_er.trans (ratWeightedAgree_curve_ge_of_eq_on hμ_nonneg hagree_true z)
  have hθ : ((Fintype.card (Fin 5) - 1 : ℕ) : ℚ) - 1 < (7 : ℚ) / 2 := by
    simp only [Fintype.card_fin]; norm_num
  have hS : 2 * Fintype.card (Fin 5) < (Finset.univ : Finset (ZMod 11)).card := by decide
  obtain ⟨D', hD', v, hvRS, hagree⟩ :=
    exists_ratWeighted_correlatedAgreement_curve_unique (d := 2) pts5_11_injective
      (e := 1) (k := 3) (by decide) hμ_le hθ u Finset.univ hS hclose
  exact ⟨u2_not_mem_rs_11, D', hD', v, hvRS, hagree⟩

/-! ### Test 2: Negative / tightness weighted dichotomy (`weighted_proximityGap_unique`) -/

private def spike0 (p : ℕ) : Fin 5 → ZMod p := fun i => if i = 0 then 1 else 0
private def spike1 (p : ℕ) : Fin 5 → ZMod p := fun i => if i = 1 then 1 else 0

/-- Over any prime field `ZMod p` (`p ∈ {11, 23}`), the two-spike word `(1, 1, 0, 0, 0)` lies at
Hamming distance `> 1` from every codeword in `reedSolomon (pts5 p) 3`. -/
private theorem spike_far_at_one {p : ℕ} [Fact (Nat.Prime p)]
    (h2ne : (2 : ZMod p) ≠ 0) (h5ne : (5 : ZMod p) ≠ 0) :
    ∀ c ∈ reedSolomon (pts5 p) 3, 1 < hammingDist (spike0 p + (1 : ZMod p) • spike1 p) c := by
  intro c hcRS
  by_contra hle
  push Not at hle
  obtain ⟨f, hf, rfl⟩ := mem_reedSolomon.1 hcRS
  let w : Fin 5 → ZMod p := spike0 p + (1 : ZMod p) • spike1 p
  have hagree_card : 4 ≤ (Finset.univ.filter fun i : Fin 5 => w i = f.eval (pts5 p i)).card := by
    have htot := card_agree_add_hammingDist w (fun i => f.eval (pts5 p i))
    change hammingDist w (fun i => f.eval (pts5 p i)) ≤ 1 at hle
    omega
  let a := f.coeff 0
  let b := f.coeff 1
  let d := f.coeff 2
  have hev : ∀ i : Fin 5, f.eval (pts5 p i) = a + b * pts5 p i + d * pts5 p i ^ 2 :=
    fun i => eval_eq_of_degree_lt_three hf (pts5 p i)
  have hex : ∃ j : Fin 5, ∀ i : Fin 5, i ≠ j → w i = f.eval (pts5 p i) := by
    by_cases hall : ∀ i : Fin 5, w i = f.eval (pts5 p i)
    · exact ⟨0, fun i _ => hall i⟩
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      refine ⟨j, fun i hij => ?_⟩
      by_contra hi
      have hsub : (Finset.univ.filter fun t : Fin 5 => w t = f.eval (pts5 p t)) ⊆
          (Finset.univ.erase j).erase i := by
        intro t ht
        have hteq := (mem_filter.1 ht).2
        refine mem_erase.2 ⟨fun h => hi (h ▸ hteq), mem_erase.2 ⟨fun h => hj (h ▸ hteq),
          mem_univ t⟩⟩
      have hle2 := card_le_card hsub
      have hcard_er : ((Finset.univ.erase j).erase i).card = 3 := by
        rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ i⟩), card_erase_of_mem (mem_univ j),
          card_univ, Fintype.card_fin]
      omega
  obtain ⟨j, hj⟩ := hex
  have h0eq : w 0 = f.eval (pts5 p 0) → (1 : ZMod p) = a := by
    intro h; rw [hev 0] at h
    have hw : w 0 = 1 := by
      simp only [w, spike0, spike1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ↓reduceIte]
      have h01 : (0 : Fin 5) ≠ 1 := by decide
      simp only [h01, ↓reduceIte, mul_zero, add_zero]
    have hp0 : pts5 p 0 = 0 := by simp only [pts5, Fin.val_zero, Nat.cast_zero]
    rw [hw, hp0] at h; linear_combination h
  have h1eq : w 1 = f.eval (pts5 p 1) → (1 : ZMod p) = a + b + d := by
    intro h; rw [hev 1] at h
    have hw : w 1 = 1 := by
      simp only [w, spike0, spike1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ↓reduceIte]
      have h10 : (1 : Fin 5) ≠ 0 := by decide
      simp only [h10, ↓reduceIte, mul_one, zero_add]
    have hp1 : pts5 p 1 = 1 := by simp only [pts5, Fin.val_one, Nat.cast_one]
    rw [hw, hp1] at h; linear_combination h
  have h2eq : w 2 = f.eval (pts5 p 2) → (0 : ZMod p) = a + 2 * b + 4 * d := by
    intro h; rw [hev 2] at h
    have hw : w 2 = 0 := by
      have h20 : (2 : Fin 5) ≠ 0 := by decide
      have h21 : (2 : Fin 5) ≠ 1 := by decide
      simp only [w, spike0, spike1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h20, h21, ↓reduceIte,
        mul_zero, add_zero]
    have hp2 : pts5 p 2 = 2 := by simp only [pts5, Fin.val_two, Nat.cast_ofNat]
    rw [hw, hp2] at h; linear_combination h
  have h3eq : w 3 = f.eval (pts5 p 3) → (0 : ZMod p) = a + 3 * b + 9 * d := by
    intro h; rw [hev 3] at h
    have hw : w 3 = 0 := by
      have h30 : (3 : Fin 5) ≠ 0 := by decide
      have h31 : (3 : Fin 5) ≠ 1 := by decide
      simp only [w, spike0, spike1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h30, h31, ↓reduceIte,
        mul_zero, add_zero]
    have hp3 : pts5 p 3 = 3 := by change ((3 : ℕ) : ZMod p) = 3; simp only [Nat.cast_ofNat]
    rw [hw, hp3] at h; linear_combination h
  have h4eq : w 4 = f.eval (pts5 p 4) → (0 : ZMod p) = a + 4 * b + 16 * d := by
    intro h; rw [hev 4] at h
    have hw : w 4 = 0 := by
      have h40 : (4 : Fin 5) ≠ 0 := by decide
      have h41 : (4 : Fin 5) ≠ 1 := by decide
      simp only [w, spike0, spike1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h40, h41, ↓reduceIte,
        mul_zero, add_zero]
    have hp4 : pts5 p 4 = 4 := by change ((4 : ℕ) : ZMod p) = 4; simp only [Nat.cast_ofNat]
    rw [hw, hp4] at h; linear_combination h
  fin_cases j
  · have h1 := h1eq (hj 1 (by decide))
    have h2 := h2eq (hj 2 (by decide))
    have h3 := h3eq (hj 3 (by decide))
    have h4 := h4eq (hj 4 (by decide))
    have : (1 : ZMod p) = 0 := by linear_combination h1 - 3 * h2 + 3 * h3 - h4
    exact one_ne_zero this
  · have h0 := h0eq (hj 0 (by decide))
    have h2 := h2eq (hj 2 (by decide))
    have h3 := h3eq (hj 3 (by decide))
    have h4 := h4eq (hj 4 (by decide))
    have : (1 : ZMod p) = 0 := by linear_combination h0 - 6 * h2 + 8 * h3 - 3 * h4
    exact one_ne_zero this
  · have h0 := h0eq (hj 0 (by decide))
    have h1 := h1eq (hj 1 (by decide))
    have h3 := h3eq (hj 3 (by decide))
    have h4 := h4eq (hj 4 (by decide))
    have : (1 : ZMod p) = 0 := by linear_combination -1 * h0 + 2 * h1 - 2 * h3 + h4
    exact one_ne_zero this
  · have h0 := h0eq (hj 0 (by decide))
    have h1 := h1eq (hj 1 (by decide))
    have h2 := h2eq (hj 2 (by decide))
    have h4 := h4eq (hj 4 (by decide))
    have : (5 : ZMod p) = 0 := by linear_combination -3 * h0 + 8 * h1 - 6 * h2 + h4
    exact h5ne this
  · have h0 := h0eq (hj 0 (by decide))
    have h1 := h1eq (hj 1 (by decide))
    have h2 := h2eq (hj 2 (by decide))
    have h3 := h3eq (hj 3 (by decide))
    have : (2 : ZMod p) = 0 := by linear_combination -1 * h0 + 3 * h1 - 3 * h2 + h3
    exact h2ne this

/-- Non-constant weights for the negative dichotomy test (`![1, 1, 2, 2, 2]`, `M = 2`, `B = 7`). -/
private def wSpike : Fin 5 → ℕ := ![1, 1, 2, 2, 2]

/-- Negative / tightness weighted dichotomy instantiation of `weighted_proximityGap_unique`:
at `z = 0`, `spike0` achieves weighted agreement `7` with `0 ∈ RS`; at `z = 1`, no codeword
achieves weight `7`, so at most `5` scalars in `ZMod 11` do. -/
theorem test_weighted_proximityGap_unique_negative :
    open scoped Classical in
    (∃ c ∈ reedSolomon (pts5 11) 3,
      7 ≤ ∑ i ∈ Finset.univ.filter (fun i => (spike0 11 + (0 : ZMod 11) • spike1 11) i = c i),
        wSpike i) ∧
    (Finset.univ.filter fun z : ZMod 11 => ∃ c ∈ reedSolomon (pts5 11) 3,
      7 ≤ ∑ i ∈ Finset.univ.filter (fun i => (spike0 11 + z • spike1 11) i = c i),
        wSpike i).card ≤ 5 := by
  classical
  have hW : ∀ i : Fin 5, wSpike i ≤ 2 := by decide
  constructor
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    have hsum : 7 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 5), wSpike i := by decide
    refine hsum.trans (Finset.sum_le_sum_of_subset ?_)
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    refine mem_filter.2 ⟨mem_univ i, ?_⟩
    simp only [spike0, Pi.add_apply, Pi.zero_apply, zero_smul, add_zero, hne, ↓reduceIte]
  · rcases weighted_proximityGap_unique pts5_11_injective (k := 3) (M := 2) (B := 7)
        (by decide) hW (by decide) (spike0 11) (spike1 11) with hall | hcard
    · obtain ⟨c, hcRS, hge⟩ := hall 1
      have hfar := spike_far_at_one (p := 11) (by decide) (by decide) c hcRS
      set A := Finset.univ.filter fun i : Fin 5 => (spike0 11 + (1 : ZMod 11) • spike1 11) i = c i
      have hle_sum : ∑ i ∈ A, wSpike i ≤ 2 * A.card := by
        calc ∑ i ∈ A, wSpike i ≤ ∑ _i ∈ A, 2 := Finset.sum_le_sum fun i _ => hW i
          _ = 2 * A.card := by simp only [Finset.sum_const, smul_eq_mul, mul_comm]
      have htot := card_agree_add_hammingDist (spike0 11 + (1 : ZMod 11) • spike1 11) c
      change A.card + hammingDist (spike0 11 + (1 : ZMod 11) • spike1 11) c = 5 at htot
      omega
    · simpa only [Fintype.card_fin] using hcard

/-! ### Test 3: 2D affine space (`ℓ = 2`) over `ZMod 23` (positive, weighted, & negative) -/

/-- Positive nonzero-error 2D affine space (`ℓ = 2`) instantiation of
`exists_uniqueMaximal_correlatedAgreement_affine_unique` (and the generic curve reduction
`exists_correlatedAgreement_affine_of_curve`) over `ZMod 23`. -/
theorem test_correlatedAgreement_affine_unique_2d :
    u0 23 ∉ reedSolomon (pts5 23) 3 ∧
    u1 23 ∉ reedSolomon (pts5 23) 3 ∧
    u2 23 ∉ reedSolomon (pts5 23) 3 ∧
    ∃ D' : Finset (Fin 5), 4 ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon (pts5 23) 3, ∃ v : Fin 2 → (Fin 5 → ZMod 23),
        (∀ j, v j ∈ reedSolomon (pts5 23) 3) ∧
        ∀ i ∈ D', u0 23 i = v₀ i ∧ ∀ j, (![u1 23, u2 23] j) i = v j i := by
  let u : Fin 2 → (Fin 5 → ZMod 23) := ![u1 23, u2 23]
  let vTrue : Fin 2 → (Fin 5 → ZMod 23) := ![v1 23, v2 23]
  have hvTrue_mem : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 23) 3 := by
    intro j; fin_cases j
    · exact v1_mem_rs
    · exact v2_mem_rs
  have hagree_true : ∀ i ∈ Finset.univ.erase (0 : Fin 5),
      u0 23 i = v0 23 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    refine ⟨by simp only [u0, hne, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change u1 23 i = v1 23 i; simp only [u1, hne, ↓reduceIte]
    · change u2 23 i = v2 23 i; simp only [u2, v2, hne, ↓reduceIte]
  have hclose : ∀ z ∈ (Finset.univ : Finset (Fin 2 → ZMod 23)), ∃ c ∈ reedSolomon (pts5 23) 3,
      hammingDist (u0 23 + ∑ j : Fin 2, z j • u j) c ≤ 1 := by
    intro z _
    refine ⟨v0 23 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ v0_mem_rs
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j)),
      hammingDist_affine_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hagree_true z⟩
  -- Also exercise the `(Fˣ)^ℓ × Fˣ` curve reduction `exists_correlatedAgreement_affine_of_curve`.
  have hT_curve : (2 * Fintype.card (Fin 5) + 2) * (Fintype.card (ZMod 23)) ^ (2 - 1) <
      (Finset.univ : Finset (Fin 2 → ZMod 23)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    norm_num
  have _h_of_curve :=
    exists_correlatedAgreement_affine_of_curve (α := pts5 23) (k := 3) (ℓ := 2)
      (B_curve := 2 * Fintype.card (Fin 5)) (by omega)
      (P := fun w => ∃ c ∈ reedSolomon (pts5 23) 3, hammingDist w c ≤ 1)
      (Q := fun D' => Fintype.card (Fin 5) - 1 ≤ D'.card)
      (fun u' S hS hcl =>
        exists_correlatedAgreement_curve_unique (d := 2) pts5_23_injective (e := 1) (k := 3)
          (by decide) u' S hS hcl)
      (u0 23) u Finset.univ hT_curve hclose
  have hT : Fintype.card (Fin 5) * (Fintype.card (ZMod 23)) ^ 2 <
      Fintype.card (ZMod 23) * (Finset.univ : Finset (Fin 2 → ZMod 23)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    norm_num
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree, _⟩ :=
    exists_uniqueMaximal_correlatedAgreement_affine_unique (ℓ := 2) pts5_23_injective (e := 1)
      (k := 3) (by decide) (u0 23) u Finset.univ hT hclose
  exact ⟨u0_not_mem_rs_23, u1_not_mem_rs_23, u2_not_mem_rs_23, D',
    by simpa only [Fintype.card_fin] using hD', v₀, hv₀, v, hvRS, hagree⟩

/-- Positive weighted 2D affine space (`ℓ = 2`, non-constant `W = ![0, 2, 2, 2, 1]`, `M = 2`,
`B = 7`) instantiation of `exists_weighted_correlatedAgreement_affine_unique_sharp` over
`ZMod 23`. -/
theorem test_weighted_correlatedAgreement_affine_unique_2d :
    ∃ D' : Finset (Fin 5), 7 ≤ ∑ i ∈ D', wNonConst i ∧
      ∃ v₀ ∈ reedSolomon (pts5 23) 3, ∃ v : Fin 2 → (Fin 5 → ZMod 23),
        (∀ j, v j ∈ reedSolomon (pts5 23) 3) ∧
        ∀ i ∈ D', u0 23 i = v₀ i ∧ ∀ j, (![u1 23, u2 23] j) i = v j i := by
  let u : Fin 2 → (Fin 5 → ZMod 23) := ![u1 23, u2 23]
  let vTrue : Fin 2 → (Fin 5 → ZMod 23) := ![v1 23, v2 23]
  have hvTrue_mem : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 23) 3 := by
    intro j; fin_cases j
    · exact v1_mem_rs
    · exact v2_mem_rs
  have hW : ∀ i : Fin 5, wNonConst i ≤ 2 := by decide
  have hagree_true : ∀ i ∈ Finset.univ.erase (0 : Fin 5),
      u0 23 i = v0 23 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    refine ⟨by simp only [u0, hne, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change u1 23 i = v1 23 i; simp only [u1, hne, ↓reduceIte]
    · change u2 23 i = v2 23 i; simp only [u2, v2, hne, ↓reduceIte]
  have hclose : ∀ z ∈ (Finset.univ : Finset (Fin 2 → ZMod 23)), ∃ c ∈ reedSolomon (pts5 23) 3,
      7 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u0 23 + ∑ j : Fin 2, z j • u j) i = c i), wNonConst i := by
    intro z _
    refine ⟨v0 23 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ v0_mem_rs
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j)), ?_⟩
    have hD : 7 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 5), wNonConst i := by decide
    exact hD.trans (weightedAgree_affine_ge_of_eq_on wNonConst hagree_true z)
  have hT : Fintype.card (Fin 5) * ((Fintype.card (ZMod 23)) ^ 2 - 1) <
      (Fintype.card (ZMod 23) - 1) * (Finset.univ : Finset (Fin 2 → ZMod 23)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    norm_num
  exact exists_weighted_correlatedAgreement_affine_unique_sharp (ℓ := 2) pts5_23_injective
    (k := 3) (M := 2) (B := 7) (by decide) hW (by decide) (u0 23) u Finset.univ hT hclose

/-- Upper-bound regression for `proximityGap_affine_unique` over `ZMod 23`: since
`(z₀, z₁) = (1, 0)` yields `spike0 + 1 • spike1` at distance `> 1` from every codeword,
`23 * #T ≤ 5 * 23 ^ 2 = 2645`, so at most `115` of the `529` affine combinations lie within
distance `1`. -/
theorem test_proximityGap_affine_unique_negative_2d :
    open scoped Classical in
    (Finset.univ.filter fun z : Fin 2 → ZMod 23 => ∃ c ∈ reedSolomon (pts5 23) 3,
      hammingDist (spike0 23 + ∑ j : Fin 2, z j • (![spike1 23, (0 : Fin 5 → ZMod 23)] j)) c ≤
        1).card ≤ 115 := by
  classical
  let u : Fin 2 → (Fin 5 → ZMod 23) := ![spike1 23, 0]
  rcases proximityGap_affine_unique (ℓ := 2) pts5_23_injective (e := 1) (k := 3) (by decide)
      (spike0 23) u with hall | hcard
  · obtain ⟨c, hcRS, hdist⟩ := hall ![1, 0]
    have hsum : (spike0 23 + ∑ j : Fin 2, (![(1 : ZMod 23), 0] j) • u j) =
        spike0 23 + (1 : ZMod 23) • spike1 23 := by
      rw [Fin.sum_univ_two]
      change spike0 23 + ((1 : ZMod 23) • spike1 23 + (0 : ZMod 23) • (0 : Fin 5 → ZMod 23)) =
        spike0 23 + (1 : ZMod 23) • spike1 23
      simp only [zero_smul, add_zero]
    rw [hsum] at hdist
    exact absurd hdist (not_le.2 (spike_far_at_one (p := 23) (by decide) (by decide) c hcRS))
  · rw [Fintype.card_fin, ZMod.card] at hcard
    dsimp only [u] at hcard
    omega

/-! ### Test 4: Dimension-independent 2D affine space (`ℓ = 2`) over `ZMod 11` -/

/-- A proper subset `T ⊂ (Fin 2 → ZMod 11)` of cardinality `66` (`60 < 66 < 121`), strictly below
the linear-in-`ℓ` bound `132 > 121` yet strictly above the dimension-independent threshold `60`. -/
private def halfPlane11 : Finset (Fin 2 → ZMod 11) :=
  Finset.univ.filter fun z => (z 0).val < 6

private theorem halfPlane11_card : halfPlane11.card = 66 := by
  let e : (Fin 2 → ZMod 11) ≃ ZMod 11 × ZMod 11 :=
    { toFun := fun z => (z 0, z 1)
      invFun := fun p => ![p.1, p.2]
      left_inv := fun z => by funext j; fin_cases j <;> rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  let A : Finset (ZMod 11) := Finset.univ.filter fun a : ZMod 11 => a.val < 6
  have hA : A.card = 6 := by decide
  have hmap : halfPlane11.image e = A ×ˢ (Finset.univ : Finset (ZMod 11)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_image, halfPlane11, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, and_true, A]
    constructor
    · rintro ⟨z, hz, hez⟩
      have h0 : z 0 = a := (Prod.mk.inj hez).1
      rw [← h0]
      exact hz
    · intro ha
      refine ⟨![a, b], ha, ?_⟩
      rfl
  calc halfPlane11.card
      = (halfPlane11.image e).card := (Finset.card_image_of_injective _ e.injective).symm
    _ = (A ×ˢ (Finset.univ : Finset (ZMod 11))).card := by rw [hmap]
    _ = A.card * (Finset.univ : Finset (ZMod 11)).card := Finset.card_product _ _
    _ = 66 := by rw [hA, Finset.card_univ, ZMod.card]

/-- Matching rational spike weights `![1/2, 1/2, 1, 1, 1]` in `[0, 1]` (`wSpike / 2`). -/
private def muSpike : Fin 5 → ℚ := ![(1 : ℚ) / 2, (1 : ℚ) / 2, 1, 1, 1]

/-- Positive dimension-independent unweighted 2D affine space correlated agreement over `ZMod 11`
on the proper subset `halfPlane11` (`#T = 66`, `5 * 11 ^ 2 = 605 < 726 = 11 * 66`), where the
linear-in-`ℓ` bound `132 > 121` is vacuous. -/
theorem test_correlatedAgreement_affine_unique_2d_zmod11 :
    u0 11 ∉ reedSolomon (pts5 11) 3 ∧
    u1 11 ∉ reedSolomon (pts5 11) 3 ∧
    u2 11 ∉ reedSolomon (pts5 11) 3 ∧
    ∃ D' : Finset (Fin 5), 4 ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon (pts5 11) 3, ∃ v : Fin 2 → (Fin 5 → ZMod 11),
        (∀ j, v j ∈ reedSolomon (pts5 11) 3) ∧
        ∀ i ∈ D', u0 11 i = v₀ i ∧ ∀ j, (![u1 11, u2 11] j) i = v j i := by
  let u : Fin 2 → (Fin 5 → ZMod 11) := ![u1 11, u2 11]
  let vTrue : Fin 2 → (Fin 5 → ZMod 11) := ![v1 11, v2 11]
  have hvTrue_mem : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 11) 3 := by
    intro j; fin_cases j
    · exact v1_mem_rs
    · exact v2_mem_rs
  have hagree_true : ∀ i ∈ Finset.univ.erase (0 : Fin 5),
      u0 11 i = v0 11 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    refine ⟨by simp only [u0, hne, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change u1 11 i = v1 11 i; simp only [u1, hne, ↓reduceIte]
    · change u2 11 i = v2 11 i; simp only [u2, v2, hne, ↓reduceIte]
  have hclose : ∀ z ∈ halfPlane11, ∃ c ∈ reedSolomon (pts5 11) 3,
      hammingDist (u0 11 + ∑ j : Fin 2, z j • u j) c ≤ 1 := by
    intro z _
    refine ⟨v0 11 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ v0_mem_rs
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j)),
      hammingDist_affine_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hagree_true z⟩
  have hT : Fintype.card (Fin 5) * (Fintype.card (ZMod 11)) ^ 2 <
      Fintype.card (ZMod 11) * halfPlane11.card := by
    rw [Fintype.card_fin, ZMod.card, halfPlane11_card]
    norm_num
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree, _⟩ :=
    exists_uniqueMaximal_correlatedAgreement_affine_unique (ℓ := 2) pts5_11_injective (e := 1)
      (k := 3) (by decide) (u0 11) u halfPlane11 hT hclose
  exact ⟨u0_not_mem_rs_11, u1_not_mem_rs_11, u2_not_mem_rs_11, D',
    by simpa only [Fintype.card_fin] using hD', v₀, hv₀, v, hvRS, hagree⟩

/-- Positive dimension-independent `ℕ`-weighted (`W = wNonConst`, `M = 2`, `B = 7`) and
`ℚ`-weighted (`μ = muNonConst`, `θ = 7 / 2`) 2D affine space correlated agreement over `ZMod 11`
on the proper subset `halfPlane11` (`#T = 66 < 121`). -/
theorem test_weighted_correlatedAgreement_affine_unique_sharp_2d_zmod11 :
    (∃ D' : Finset (Fin 5), 7 ≤ ∑ i ∈ D', wNonConst i ∧
      ∃ v₀ ∈ reedSolomon (pts5 11) 3, ∃ v : Fin 2 → (Fin 5 → ZMod 11),
        (∀ j, v j ∈ reedSolomon (pts5 11) 3) ∧
        ∀ i ∈ D', u0 11 i = v₀ i ∧ ∀ j, (![u1 11, u2 11] j) i = v j i) ∧
    (∃ D' : Finset (Fin 5), (7 : ℚ) / 2 ≤ ∑ i ∈ D', muNonConst i ∧
      ∃ v₀ ∈ reedSolomon (pts5 11) 3, ∃ v : Fin 2 → (Fin 5 → ZMod 11),
        (∀ j, v j ∈ reedSolomon (pts5 11) 3) ∧
        ∀ i ∈ D', u0 11 i = v₀ i ∧ ∀ j, (![u1 11, u2 11] j) i = v j i) := by
  let u : Fin 2 → (Fin 5 → ZMod 11) := ![u1 11, u2 11]
  let vTrue : Fin 2 → (Fin 5 → ZMod 11) := ![v1 11, v2 11]
  have hvTrue_mem : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 11) 3 := by
    intro j; fin_cases j
    · exact v1_mem_rs
    · exact v2_mem_rs
  have hW : ∀ i : Fin 5, wNonConst i ≤ 2 := by decide
  have hμ_nonneg : ∀ i : Fin 5, 0 ≤ muNonConst i := by
    intro i; fin_cases i <;> norm_num [muNonConst]
  have hμ_le : ∀ i : Fin 5, muNonConst i ≤ 1 := by
    intro i; fin_cases i <;> norm_num [muNonConst]
  have hagree_true : ∀ i ∈ Finset.univ.erase (0 : Fin 5),
      u0 11 i = v0 11 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    refine ⟨by simp only [u0, hne, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change u1 11 i = v1 11 i; simp only [u1, hne, ↓reduceIte]
    · change u2 11 i = v2 11 i; simp only [u2, v2, hne, ↓reduceIte]
  have hT : Fintype.card (Fin 5) * ((Fintype.card (ZMod 11)) ^ 2 - 1) <
      (Fintype.card (ZMod 11) - 1) * halfPlane11.card := by
    rw [Fintype.card_fin, ZMod.card, halfPlane11_card]
    norm_num
  constructor
  · have hclose : ∀ z ∈ halfPlane11, ∃ c ∈ reedSolomon (pts5 11) 3,
        7 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u0 11 + ∑ j : Fin 2, z j • u j) i = c i), wNonConst i := by
      intro z _
      refine ⟨v0 11 + ∑ j : Fin 2, z j • vTrue j,
        Submodule.add_mem _ v0_mem_rs
          (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j)), ?_⟩
      have hD : 7 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 5), wNonConst i := by decide
      exact hD.trans (weightedAgree_affine_ge_of_eq_on wNonConst hagree_true z)
    exact exists_weighted_correlatedAgreement_affine_unique_sharp (ℓ := 2) pts5_11_injective
      (k := 3) (M := 2) (B := 7) (by decide) hW (by decide) (u0 11) u halfPlane11 hT hclose
  · have hclose : ∀ z ∈ halfPlane11, ∃ c ∈ reedSolomon (pts5 11) 3,
        (7 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (u0 11 + ∑ j : Fin 2, z j • u j) i = c i), muNonConst i := by
      intro z _
      refine ⟨v0 11 + ∑ j : Fin 2, z j • vTrue j,
        Submodule.add_mem _ v0_mem_rs
          (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j)), ?_⟩
      have hD : (7 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 5), muNonConst i := by
        norm_num [Fin.sum_univ_five, Finset.sum_erase_eq_sub, muNonConst]
      exact hD.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nonneg hagree_true z)
    have hθ : ((Fintype.card (Fin 5) - 1 : ℕ) : ℚ) - 1 < (7 : ℚ) / 2 := by
      rw [Fintype.card_fin]; norm_num
    exact exists_ratWeighted_correlatedAgreement_affine_unique_sharp (ℓ := 2) pts5_11_injective
      (e := 1) (k := 3) (by decide) hμ_le hθ (u0 11) u halfPlane11 hT hclose

/-- Upper-bound regressions for the weighted dimension-independent 2D affine space dichotomies over
`ZMod 11`: `ℕ`-weighted (`weighted_proximityGap_affine_unique_sharp`) and `ℚ`-weighted
(`ratWeighted_proximityGap_affine_unique_sharp`) both bound the close set to at most `60` of the
`121` points (`10 * #T ≤ 600`) while `z = ![0, 0]` is close and `z = ![1, 0]` is far. -/
theorem test_weighted_proximityGap_affine_unique_sharp_negative_2d_zmod11 :
    open scoped Classical in
    (Finset.univ.filter fun z : Fin 2 → ZMod 11 => ∃ c ∈ reedSolomon (pts5 11) 3,
      7 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (spike0 11 + ∑ j : Fin 2, z j • (![spike1 11, (0 : Fin 5 → ZMod 11)] j)) i = c i),
        wSpike i).card ≤ 60 ∧
    (Finset.univ.filter fun z : Fin 2 → ZMod 11 => ∃ c ∈ reedSolomon (pts5 11) 3,
      (7 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (spike0 11 + ∑ j : Fin 2, z j • (![spike1 11, (0 : Fin 5 → ZMod 11)] j)) i = c i),
        muSpike i).card ≤ 60 := by
  classical
  set u : Fin 2 → (Fin 5 → ZMod 11) := ![spike1 11, 0]
  have hsum1 : (spike0 11 + ∑ j : Fin 2, (![(1 : ZMod 11), 0] j) • u j) =
      spike0 11 + (1 : ZMod 11) • spike1 11 := by
    rw [Fin.sum_univ_two]
    change spike0 11 + ((1 : ZMod 11) • spike1 11 + (0 : ZMod 11) • (0 : Fin 5 → ZMod 11)) =
      spike0 11 + (1 : ZMod 11) • spike1 11
    simp only [zero_smul, add_zero]
  have hW : ∀ i : Fin 5, wSpike i ≤ 2 := by decide
  have hμ_nonneg : ∀ i : Fin 5, 0 ≤ muSpike i := by
    intro i; fin_cases i <;> norm_num [muSpike]
  have hμ_le : ∀ i : Fin 5, muSpike i ≤ 1 := by
    intro i; fin_cases i <;> norm_num [muSpike]
  have hθ : ((Fintype.card (Fin 5) - 1 : ℕ) : ℚ) - 1 < (7 : ℚ) / 2 := by
    rw [Fintype.card_fin]; norm_num
  refine ⟨?_, ?_⟩
  · rcases weighted_proximityGap_affine_unique_sharp (ℓ := 2) pts5_11_injective (k := 3) (M := 2)
        (B := 7) (by decide) hW (by decide) (spike0 11) u with hall | hcard
    · obtain ⟨c, hcRS, hge⟩ := hall ![1, 0]
      rw [hsum1] at hge
      have hfar := spike_far_at_one (p := 11) (by decide) (by decide) c hcRS
      set A := Finset.univ.filter fun i : Fin 5 => (spike0 11 + (1 : ZMod 11) • spike1 11) i = c i
      have hle_sum : ∑ i ∈ A, wSpike i ≤ 2 * A.card := by
        calc ∑ i ∈ A, wSpike i ≤ ∑ _i ∈ A, 2 := Finset.sum_le_sum fun i _ => hW i
          _ = 2 * A.card := by simp only [Finset.sum_const, smul_eq_mul, mul_comm]
      have htot := card_agree_add_hammingDist (spike0 11 + (1 : ZMod 11) • spike1 11) c
      change A.card + hammingDist (spike0 11 + (1 : ZMod 11) • spike1 11) c = 5 at htot
      omega
    · rw [Fintype.card_fin, ZMod.card] at hcard
      omega
  · rcases ratWeighted_proximityGap_affine_unique_sharp (ℓ := 2) pts5_11_injective (e := 1) (k := 3)
        (by decide) hμ_nonneg hμ_le hθ (spike0 11) u with hall | hcard
    · obtain ⟨c, hcRS, hge⟩ := hall ![1, 0]
      rw [hsum1] at hge
      have hfar := spike_far_at_one (p := 11) (by decide) (by decide) c hcRS
      set A := Finset.univ.filter fun i : Fin 5 => (spike0 11 + (1 : ZMod 11) • spike1 11) i = c i
      have hle_sum : ∑ i ∈ A, muSpike i ≤ (A.card : ℚ) := by
        calc ∑ i ∈ A, muSpike i ≤ ∑ _i ∈ A, (1 : ℚ) := Finset.sum_le_sum fun i _ => hμ_le i
          _ = (A.card : ℚ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      have htot := card_agree_add_hammingDist (spike0 11 + (1 : ZMod 11) • spike1 11) c
      change A.card + hammingDist (spike0 11 + (1 : ZMod 11) • spike1 11) c = 5 at htot
      have hA_le : (A.card : ℚ) ≤ 3 := by exact_mod_cast (by omega : A.card ≤ 3)
      linarith
    · rw [Fintype.card_fin, ZMod.card] at hcard
      omega

/-! ### Test 5: Beyond-unique-decoding Johnson 2D affine spaces & `ℚ`-weighted curves -/

instance : Fact (Nat.Prime 2003) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 65537) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 200003) := ⟨by norm_num⟩

private theorem card_monomials_1_2 : #(Sudan.monomials 1 2) = 6 := by decide
private theorem maxYDeg_1_2 : ProximityGap.maxYDeg 1 2 = 2 := by decide
private theorem card_monomials_1_5 : #(Sudan.monomials 1 5) = 21 := by decide
private theorem maxYDeg_1_5 : ProximityGap.maxYDeg 1 5 = 5 := by decide

private theorem pts5_injective {p : ℕ} (hp : 5 ≤ p) : Function.Injective (pts5 p) := by
  intro i j h
  have hv := congrArg ZMod.val h
  dsimp only [pts5] at hv
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
  exact Fin.ext hv

private theorem pts5_65537_injective : Function.Injective (pts5 65537) :=
  pts5_injective (by omega)

private theorem pts5_200003_injective : Function.Injective (pts5 200003) :=
  pts5_injective (by omega)

private theorem eval_eq_of_degree_lt_two {F : Type*} [Field F] {f : F[X]}
    (hf : f.degree < (2 : ℕ)) (x : F) : f.eval x = f.coeff 0 + f.coeff 1 * x := by
  have hdeg : f.natDegree < 2 := by
    by_cases hf0 : f = 0
    · rw [hf0, natDegree_zero]; decide
    · exact (natDegree_lt_iff_degree_lt hf0).2 hf
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, mul_one, pow_one]

private theorem second_diff_zero_of_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)]
    {c : Fin 5 → ZMod p} (hc : c ∈ reedSolomon (pts5 p) 2) :
    c 0 - 2 * c 1 + c 2 = 0 ∧ c 1 - 2 * c 2 + c 3 = 0 := by
  obtain ⟨f, hf, rfl⟩ := mem_reedSolomon.1 hc
  constructor <;>
    · simp only [eval_eq_of_degree_lt_two hf, pts5, Fin.val_zero, Fin.val_one, Fin.val_two,
        show (3 : Fin 5).val = 3 from rfl, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
      ring

private def lin0 (p : ℕ) : Fin 5 → ZMod p := fun i => 1 + pts5 p i
private def lin1 (p : ℕ) : Fin 5 → ZMod p := fun i => 2 * pts5 p i
private def lin2 (p : ℕ) : Fin 5 → ZMod p := fun i => 3 + pts5 p i

private theorem lin0_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)] : lin0 p ∈ reedSolomon (pts5 p) 2 := by
  refine mem_reedSolomon.2 ⟨1 + X, ?_, funext fun i => by simp only [lin0, eval_add, eval_one,
    eval_X]⟩
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · rw [degree_one]; exact Nat.cast_lt.2 (by decide)
  · rw [degree_X]; exact Nat.cast_lt.2 (by decide)

private theorem lin1_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)] : lin1 p ∈ reedSolomon (pts5 p) 2 := by
  refine mem_reedSolomon.2 ⟨C (2 : ZMod p) * X, ?_, funext fun i => by
    simp only [lin1, eval_mul, eval_C, eval_X]⟩
  refine (degree_mul_le _ _).trans_lt ?_
  refine (add_le_add degree_C_le le_rfl).trans_lt ?_
  rw [zero_add, degree_X]
  exact Nat.cast_lt.2 (by decide)

private theorem lin2_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)] : lin2 p ∈ reedSolomon (pts5 p) 2 := by
  refine mem_reedSolomon.2 ⟨C (3 : ZMod p) + X, ?_, funext fun i => by
    simp only [lin2, eval_add, eval_C, eval_X]⟩
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · exact degree_C_le.trans_lt (Nat.cast_lt.2 (by decide))
  · rw [degree_X]; exact Nat.cast_lt.2 (by decide)

/-- Corrupted words at distance `2 > 1` (strictly beyond unique decoding for `n = 5, k = 2`),
agreeing with `lin0, lin1, lin2` on `{1, 2, 3}` (corrupted at `0` and `4`). -/
private def cor0 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => if i = 0 ∨ i = 4 then lin0 p i + 1 else lin0 p i

private def cor1 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => if i = 0 ∨ i = 4 then lin1 p i + 2 else lin1 p i

private def cor2 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => if i = 0 ∨ i = 4 then lin2 p i + 3 else lin2 p i

private theorem cor0_not_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)] :
    cor0 p ∉ reedSolomon (pts5 p) 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
  have hval : cor0 p 0 - 2 * cor0 p 1 + cor0 p 2 = 1 := by
    have h1 : ¬ ((1 : Fin 5) = 0 ∨ (1 : Fin 5) = 4) := by decide
    have h2 : ¬ ((2 : Fin 5) = 0 ∨ (2 : Fin 5) = 4) := by decide
    simp only [cor0, lin0, pts5, true_or, ↓reduceIte, h1, h2, Fin.val_zero, Fin.val_one,
      Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hval] at hdiff
  exact one_ne_zero hdiff

private theorem cor1_not_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)] (h2ne : (2 : ZMod p) ≠ 0) :
    cor1 p ∉ reedSolomon (pts5 p) 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
  have hval : cor1 p 0 - 2 * cor1 p 1 + cor1 p 2 = 2 := by
    have h1 : ¬ ((1 : Fin 5) = 0 ∨ (1 : Fin 5) = 4) := by decide
    have h2 : ¬ ((2 : Fin 5) = 0 ∨ (2 : Fin 5) = 4) := by decide
    simp only [cor1, lin1, pts5, true_or, ↓reduceIte, h1, h2, Fin.val_zero, Fin.val_one,
      Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hval] at hdiff
  exact h2ne hdiff

private theorem cor2_not_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)] (h3ne : (3 : ZMod p) ≠ 0) :
    cor2 p ∉ reedSolomon (pts5 p) 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
  have hval : cor2 p 0 - 2 * cor2 p 1 + cor2 p 2 = 3 := by
    have h1 : ¬ ((1 : Fin 5) = 0 ∨ (1 : Fin 5) = 4) := by decide
    have h2 : ¬ ((2 : Fin 5) = 0 ∨ (2 : Fin 5) = 4) := by decide
    simp only [cor2, lin2, pts5, true_or, ↓reduceIte, h1, h2, Fin.val_zero, Fin.val_one,
      Fin.val_two, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hval] at hdiff
  exact h3ne hdiff

/-- Non-constant integer weights `![0, 1, 2, 2, 1]` (`M = 2`, `W_tot = 6`, sum on `{1, 2, 3}` is
`5`). -/
private def wJ5 : Fin 5 → ℕ := ![0, 1, 2, 2, 1]

/-- Matching rational weights `![0, 1/2, 1, 1, 1/2]` (`M = 2`, sum on `{1, 2, 3}` is `5/2`). -/
private def muJ5 : Fin 5 → ℚ := ![0, (1 : ℚ) / 2, 1, 1, (1 : ℚ) / 2]

/-- Vertical strip `{z : Fin 2 → ZMod p | (z 0).val < K}` of exact cardinality `K * p`
(for `K ≤ p`). -/
private def strip2D (p K : ℕ) [NeZero p] : Finset (Fin 2 → ZMod p) :=
  Finset.univ.filter fun z => (z 0).val < K

private theorem strip2D_card {p K : ℕ} [NeZero p] (hKp : K ≤ p) :
    (strip2D p K).card = K * p := by
  let e : (Fin 2 → ZMod p) ≃ ZMod p × ZMod p :=
    { toFun := fun z => (z 0, z 1)
      invFun := fun q => ![q.1, q.2]
      left_inv := fun z => by funext j; fin_cases j <;> rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  let A : Finset (ZMod p) := Finset.univ.filter fun a : ZMod p => a.val < K
  have hA : A.card = K := by
    have hmapA : A = (Finset.range K).image (fun n : ℕ => (n : ZMod p)) := by
      ext a
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_range]
      constructor
      · intro ha
        exact ⟨a.val, ha, ZMod.natCast_zmod_val a⟩
      · rintro ⟨n, hn, rfl⟩
        rw [ZMod.val_natCast_of_lt (hn.trans_le hKp)]
        exact hn
    rw [hmapA, Finset.card_image_of_injOn, Finset.card_range]
    intro a ha b hb hab
    have hltA : a < p := (Finset.mem_range.1 ha).trans_le hKp
    have hltB : b < p := (Finset.mem_range.1 hb).trans_le hKp
    have hv := congrArg ZMod.val hab
    rwa [ZMod.val_natCast_of_lt hltA, ZMod.val_natCast_of_lt hltB] at hv
  have hmap : (strip2D p K).image e = A ×ˢ (Finset.univ : Finset (ZMod p)) := by
    ext ⟨a, b⟩
    simp only [Finset.mem_image, strip2D, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_product, and_true, A]
    constructor
    · rintro ⟨z, hz, hez⟩
      have h0 : z 0 = a := (Prod.mk.inj hez).1
      rw [← h0]
      exact hz
    · intro ha
      exact ⟨![a, b], ha, rfl⟩
  calc (strip2D p K).card
      = ((strip2D p K).image e).card := (Finset.card_image_of_injective _ e.injective).symm
    _ = (A ×ˢ (Finset.univ : Finset (ZMod p))).card := by rw [hmap]
    _ = A.card * (Finset.univ : Finset (ZMod p)).card := Finset.card_product _ _
    _ = K * p := by rw [hA, Finset.card_univ, ZMod.card]

/-- Beyond-unique-decoding (`n = 5, k = 2, e = 2 > 1, m = 1, D = 2, L = 2`) 2D affine correlated
agreement over `ZMod 65537`: `exists_correlatedAgreement_affine_johnson` fires right above
`B_line = 1698` on `strip2D 65537 1699` (`1698 * 65537 ^ 2 < 65537 * (1699 * 65537)`) with no
list-size premise. -/
theorem test_correlatedAgreement_affine_johnson_2d_zmod65537 :
    cor0 65537 ∉ reedSolomon (pts5 65537) 2 ∧
    cor1 65537 ∉ reedSolomon (pts5 65537) 2 ∧
    cor2 65537 ∉ reedSolomon (pts5 65537) 2 ∧
    ProximityGap.johnsonCurveBound 5 1 1 2 1 5 = 1698 ∧
    ∃ D' : Finset (Fin 5), 3 ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon (pts5 65537) 2, ∃ v : Fin 2 → (Fin 5 → ZMod 65537),
        (∀ j, v j ∈ reedSolomon (pts5 65537) 2) ∧
        ∀ i ∈ D', cor0 65537 i = v₀ i ∧ ∀ j, (![cor1 65537, cor2 65537] j) i = v j i := by
  have hjb : ProximityGap.johnsonCurveBound 5 1 1 2 1 5 = 1698 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hinterp : Fintype.card (Fin 5) * (1 * (1 + 1) / 2) < #(Sudan.monomials (2 - 1) 2) := by
    rw [Fintype.card_fin]
    change 5 * 1 < #(Sudan.monomials 1 2)
    rw [card_monomials_1_2]
    omega
  let u : Fin 2 → (Fin 5 → ZMod 65537) := ![cor1 65537, cor2 65537]
  let vTrue : Fin 2 → (Fin 5 → ZMod 65537) := ![lin1 65537, lin2 65537]
  have hvTrue : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 65537) 2 := by
    intro j; fin_cases j
    · exact lin1_mem_rs2
    · exact lin2_mem_rs2
  have hagree_true : ∀ i ∈ ({1, 2, 3} : Finset (Fin 5)),
      cor0 65537 i = lin0 65537 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hnot : ¬ (i = 0 ∨ i = 4) := by fin_cases hi <;> decide
    refine ⟨by simp only [cor0, hnot, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change cor1 65537 i = lin1 65537 i; simp only [cor1, hnot, ↓reduceIte]
    · change cor2 65537 i = lin2 65537 i; simp only [cor2, hnot, ↓reduceIte]
  have hclose_all : ∀ z : Fin 2 → ZMod 65537, ∃ c ∈ reedSolomon (pts5 65537) 2,
      hammingDist (cor0 65537 + ∑ j : Fin 2, z j • u j) c ≤ 2 := fun z =>
    ⟨lin0 65537 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ lin0_mem_rs2
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hammingDist_affine_le_of_eq_on (D' := {1, 2, 3}) (by decide) hagree_true z⟩
  have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 1
      (Fintype.card (Fin 5)) * (Fintype.card (ZMod 65537)) ^ 2 <
      Fintype.card (ZMod 65537) * (strip2D 65537 1699).card := by
    rw [Fintype.card_fin, ZMod.card, strip2D_card (by omega)]
    change ProximityGap.johnsonCurveBound 5 1 1 2 1 5 * 65537 ^ 2 < 65537 * (1699 * 65537)
    rw [hjb]
    norm_num
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_correlatedAgreement_affine_johnson (ℓ := 2) pts5_65537_injective (k := 2) (e := 2)
      (m := 1) (D := 2) (by omega) (by omega) (by rw [Fintype.card_fin]; omega) hinterp
      (by rw [Fintype.card_fin]; omega) (cor0 65537) u (strip2D 65537 1699) hT
      (fun z _ => hclose_all z)
  exact ⟨cor0_not_mem_rs2, cor1_not_mem_rs2 (by decide), cor2_not_mem_rs2 (by decide), hjb,
    D', by simpa only [Fintype.card_fin] using hD', v₀, hv₀, v, hvRS, hagree⟩

/-- Beyond-unique-decoding `ℕ`-weighted (`W = wJ5`, `M = 2`, `W_tot = 6`, `B_W = 5`) and
`ℚ`-weighted (`μ = muJ5`, `M = 2`, `θ = 5/2`) 2D affine correlated agreement (with no list-size
premise), plus `ℚ`-weighted line and degree-2 curve Johnson correlated agreement over
`ZMod 65537`. -/
theorem test_weighted_and_ratWeighted_johnson_zmod65537 :
    (∃ D' : Finset (Fin 5), 5 ≤ ∑ i ∈ D', wJ5 i ∧
      ∃ v₀ ∈ reedSolomon (pts5 65537) 2, ∃ v : Fin 2 → (Fin 5 → ZMod 65537),
        (∀ j, v j ∈ reedSolomon (pts5 65537) 2) ∧
        ∀ i ∈ D', cor0 65537 i = v₀ i ∧ ∀ j, (![cor1 65537, cor2 65537] j) i = v j i) ∧
    (∃ D' : Finset (Fin 5), (5 : ℚ) / 2 ≤ ∑ i ∈ D', muJ5 i ∧
      ∃ v₀ ∈ reedSolomon (pts5 65537) 2, ∃ v : Fin 2 → (Fin 5 → ZMod 65537),
        (∀ j, v j ∈ reedSolomon (pts5 65537) 2) ∧
        ∀ i ∈ D', cor0 65537 i = v₀ i ∧ ∀ j, (![cor1 65537, cor2 65537] j) i = v j i) ∧
    (∃ D' : Finset (Fin 5), (5 : ℚ) / 2 ≤ ∑ i ∈ D', muJ5 i ∧
      ∃ v₀ ∈ reedSolomon (pts5 65537) 2, ∃ v₁ ∈ reedSolomon (pts5 65537) 2,
        ∀ i ∈ D', cor0 65537 i = v₀ i ∧ cor1 65537 i = v₁ i) ∧
    (∃ D' : Finset (Fin 5), (5 : ℚ) / 2 ≤ ∑ i ∈ D', muJ5 i ∧
      ∃ v : Fin 3 → (Fin 5 → ZMod 65537), (∀ j, v j ∈ reedSolomon (pts5 65537) 2) ∧
        ∀ i ∈ D', ∀ j, (![cor0 65537, cor1 65537, cor2 65537] j) i = v j i) := by
  have hjb6 : ProximityGap.johnsonCurveBound 5 1 1 2 1 6 = 2026 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hjb10 : ProximityGap.johnsonCurveBound 5 1 1 2 1 10 = 3338 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hjb10_r2 : ProximityGap.johnsonCurveBound 5 1 1 2 2 10 = 6668 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hinterp : Fintype.card (Fin 5) * (1 * (1 + 1) / 2) < #(Sudan.monomials (2 - 1) 2) := by
    rw [Fintype.card_fin]; change 5 * 1 < #(Sudan.monomials 1 2); rw [card_monomials_1_2]; omega
  have hW_le : ∀ i : Fin 5, wJ5 i ≤ 2 := by intro i; fin_cases i <;> decide
  have hW_sum : ∑ i : Fin 5, wJ5 i ≤ 6 := by decide
  have hμ_le : ∀ i : Fin 5, muJ5 i ≤ 1 := by intro i; fin_cases i <;> norm_num [muJ5]
  have hμ_nn : ∀ i : Fin 5, 0 ≤ muJ5 i := by intro i; fin_cases i <;> norm_num [muJ5]
  have hμ_den : ∀ i : Fin 5, ∃ a : ℕ, muJ5 i = (a : ℚ) / (2 : ℕ) := by
    intro i; fin_cases i
    · exact ⟨0, by norm_num [muJ5]⟩
    · exact ⟨1, by norm_num [muJ5]⟩
    · exact ⟨2, by norm_num [muJ5]⟩
    · exact ⟨2, by norm_num [muJ5]⟩
    · exact ⟨1, by norm_num [muJ5]⟩
  let u : Fin 2 → (Fin 5 → ZMod 65537) := ![cor1 65537, cor2 65537]
  let vTrue : Fin 2 → (Fin 5 → ZMod 65537) := ![lin1 65537, lin2 65537]
  have hvTrue : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 65537) 2 := by
    intro j; fin_cases j
    · exact lin1_mem_rs2
    · exact lin2_mem_rs2
  have hagree_aff : ∀ i ∈ ({1, 2, 3} : Finset (Fin 5)),
      cor0 65537 i = lin0 65537 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hnot : ¬ (i = 0 ∨ i = 4) := by fin_cases hi <;> decide
    refine ⟨by simp only [cor0, hnot, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change cor1 65537 i = lin1 65537 i; simp only [cor1, hnot, ↓reduceIte]
    · change cor2 65537 i = lin2 65537 i; simp only [cor2, hnot, ↓reduceIte]
  have hW_sub : (5 : ℕ) ≤ ∑ i ∈ ({1, 2, 3} : Finset (Fin 5)), wJ5 i := by decide
  have hμ_sub : (5 : ℚ) / 2 ≤ ∑ i ∈ ({1, 2, 3} : Finset (Fin 5)), muJ5 i := by
    have hcard : ({1, 2, 3} : Finset (Fin 5)) = {1, 2, 3} := rfl
    norm_num [muJ5]
  have hcloseW_aff : ∀ z : Fin 2 → ZMod 65537, ∃ c ∈ reedSolomon (pts5 65537) 2,
      5 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (cor0 65537 + ∑ j : Fin 2, z j • u j) i = c i), wJ5 i := fun z =>
    ⟨lin0 65537 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ lin0_mem_rs2
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hW_sub.trans (weightedAgree_affine_ge_of_eq_on wJ5 hagree_aff z)⟩
  have hcloseμ_aff : ∀ z : Fin 2 → ZMod 65537, ∃ c ∈ reedSolomon (pts5 65537) 2,
      (5 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (cor0 65537 + ∑ j : Fin 2, z j • u j) i = c i), muJ5 i := fun z =>
    ⟨lin0 65537 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ lin0_mem_rs2
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hμ_sub.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nn hagree_aff z)⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `ℕ`-weighted affine on `strip2D 65537 2027` (`2026 < 2027`, no list-size premise).
    have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 1 6 *
        (Fintype.card (ZMod 65537)) ^ 2 <
        Fintype.card (ZMod 65537) * (strip2D 65537 2027).card := by
      rw [Fintype.card_fin, ZMod.card, strip2D_card (by omega)]
      change ProximityGap.johnsonCurveBound 5 1 1 2 1 6 * 65537 ^ 2 < 65537 * (2027 * 65537)
      rw [hjb6]; norm_num
    exact exists_weighted_correlatedAgreement_affine_johnson (ℓ := 2) pts5_65537_injective
      (k := 2) (m := 1) (D := 2) (M := 2) (W_tot := 6) (B_W := 5) (by omega) (by omega) (by omega)
      hW_le hW_sum (by omega) hinterp (by omega) (cor0 65537) u (strip2D 65537 2027) hT
      (fun z _ => hcloseW_aff z)
  · -- `ℚ`-weighted affine on `strip2D 65537 3339` (`3338 < 3339`, no list-size premise).
    have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 1
        (2 * Fintype.card (Fin 5)) * (Fintype.card (ZMod 65537)) ^ 2 <
        Fintype.card (ZMod 65537) * (strip2D 65537 3339).card := by
      rw [Fintype.card_fin, ZMod.card, strip2D_card (by omega)]
      change ProximityGap.johnsonCurveBound 5 1 1 2 1 10 * 65537 ^ 2 < 65537 * (3339 * 65537)
      rw [hjb10]; norm_num
    exact exists_ratWeighted_correlatedAgreement_affine_johnson (ℓ := 2) pts5_65537_injective
      (k := 2) (m := 1) (D := 2) (M := 2) (θ := 5 / 2) (by omega) (by omega) (by omega) hμ_le
      hμ_den (by norm_num) hinterp (by norm_num) (cor0 65537) u (strip2D 65537 3339) hT
      (fun z _ => hcloseμ_aff z)
  · -- `ℚ`-weighted line over `ZMod 65537`.
    have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 1
        (2 * Fintype.card (Fin 5)) < #(Finset.univ : Finset (ZMod 65537)) := by
      rw [Fintype.card_fin, Finset.card_univ, ZMod.card]
      change ProximityGap.johnsonCurveBound 5 1 1 2 1 10 < 65537
      rw [hjb10]; omega
    have hcloseL : ∀ z ∈ (Finset.univ : Finset (ZMod 65537)), ∃ c ∈ reedSolomon (pts5 65537) 2,
        (5 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (cor0 65537 + z • cor1 65537) i = c i), muJ5 i := by
      intro z _
      refine ⟨lin0 65537 + z • lin1 65537,
        Submodule.add_mem _ lin0_mem_rs2 (Submodule.smul_mem _ z lin1_mem_rs2),
        hμ_sub.trans (Finset.sum_le_sum_of_subset_of_nonneg (fun i hi => ?_)
          fun i _ _ => hμ_nn i)⟩
      have hnot : ¬ (i = 0 ∨ i = 4) := by fin_cases hi <;> decide
      exact mem_filter.2 ⟨mem_univ i, by simp only [cor0, cor1, Pi.add_apply, Pi.smul_apply, hnot,
        ↓reduceIte]⟩
    exact exists_ratWeighted_correlatedAgreement_line_johnson pts5_65537_injective (k := 2) (m := 1)
      (D := 2) (M := 2) (θ := 5 / 2) (by omega) (by omega) (by omega) hμ_le hμ_den (by norm_num)
      hinterp (by norm_num) (cor0 65537) (cor1 65537) Finset.univ hT hcloseL
  · -- `ℚ`-weighted degree-2 curve (`r = 2`) over `ZMod 65537`.
    let uc : Fin 3 → (Fin 5 → ZMod 65537) := ![cor0 65537, cor1 65537, cor2 65537]
    let vc : Fin 3 → (Fin 5 → ZMod 65537) := ![lin0 65537, lin1 65537, lin2 65537]
    have hvc : ∀ j : Fin 3, vc j ∈ reedSolomon (pts5 65537) 2 := by
      intro j; fin_cases j
      · exact lin0_mem_rs2
      · exact lin1_mem_rs2
      · exact lin2_mem_rs2
    have hagree_c : ∀ i ∈ ({1, 2, 3} : Finset (Fin 5)), ∀ j : Fin 3, uc j i = vc j i := by
      intro i hi j
      have hnot : ¬ (i = 0 ∨ i = 4) := by fin_cases hi <;> decide
      fin_cases j
      · change cor0 65537 i = lin0 65537 i; simp only [cor0, hnot, ↓reduceIte]
      · change cor1 65537 i = lin1 65537 i; simp only [cor1, hnot, ↓reduceIte]
      · change cor2 65537 i = lin2 65537 i; simp only [cor2, hnot, ↓reduceIte]
    have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 2
        (2 * Fintype.card (Fin 5)) < #(Finset.univ : Finset (ZMod 65537)) := by
      rw [Fintype.card_fin, Finset.card_univ, ZMod.card]
      change ProximityGap.johnsonCurveBound 5 1 1 2 2 10 < 65537
      rw [hjb10_r2]; omega
    have hcloseC : ∀ z ∈ (Finset.univ : Finset (ZMod 65537)), ∃ c ∈ reedSolomon (pts5 65537) 2,
        (5 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
          (∑ j : Fin 3, z ^ (j : ℕ) • uc j) i = c i), muJ5 i := fun z _ =>
      ⟨∑ j : Fin 3, z ^ (j : ℕ) • vc j,
        Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvc j),
        hμ_sub.trans (ratWeightedAgree_curve_ge_of_eq_on hμ_nn hagree_c z)⟩
    exact exists_ratWeighted_correlatedAgreement_curve_johnson (r := 2) pts5_65537_injective
      (k := 2) (m := 1) (D := 2) (M := 2) (θ := 5 / 2) (by omega) (by omega) (by omega) hμ_le
      hμ_den (by norm_num) hinterp (by norm_num) uc Finset.univ hT hcloseC

/-- The parabola `x ↦ x ^ 2` agrees with any linear codeword in `reedSolomon (pts5 p) 2` on at
most `2` points. -/
private def parabola5 (p : ℕ) : Fin 5 → ZMod p := fun i => (pts5 p i) ^ 2

private theorem card_agree_parabola_le_two {p : ℕ} [Fact (Nat.Prime p)]
    (hα : Function.Injective (pts5 p)) {c : Fin 5 → ZMod p} (hc : c ∈ reedSolomon (pts5 p) 2) :
    (Finset.univ.filter fun i : Fin 5 => parabola5 p i = c i).card ≤ 2 := by
  obtain ⟨f, hf, rfl⟩ := mem_reedSolomon.1 hc
  set q : (ZMod p)[X] := X ^ 2 - f
  have hdeg_f : f.degree < (X ^ 2 : (ZMod p)[X]).degree := by
    rw [degree_X_pow]
    exact hf
  have hq_deg : q.degree = (2 : ℕ) := by
    dsimp only [q]
    rw [degree_sub_eq_left_of_degree_lt hdeg_f, degree_X_pow]
  have hq_ne : q ≠ 0 := by
    intro h0
    rw [h0, degree_zero] at hq_deg
    exact absurd hq_deg (by decide)
  have hq_nd : q.natDegree = 2 := natDegree_eq_of_degree_eq_some hq_deg
  set A := Finset.univ.filter fun i : Fin 5 => parabola5 p i = f.eval (pts5 p i)
  have hsub : A.image (pts5 p) ⊆ q.roots.toFinset := by
    intro x hx
    obtain ⟨i, hiA, rfl⟩ := mem_image.1 hx
    have heq := (mem_filter.1 hiA).2
    rw [Multiset.mem_toFinset, mem_roots hq_ne, IsRoot]
    simp only [q, eval_sub, eval_pow, eval_X]
    exact sub_eq_zero.2 heq
  calc A.card = (A.image (pts5 p)).card := (Finset.card_image_of_injective A hα).symm
    _ ≤ q.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ q.roots.card := Multiset.toFinset_card_le _
    _ ≤ q.natDegree := Polynomial.card_roots' q
    _ = 2 := hq_nd

/-- Negative / tightness exact Johnson 2D affine dichotomies over `ZMod 65537`: using `parabola5`,
which agrees with every linear codeword on at most `2` points (`hammingDist ≥ 3 > 2`, `W`-weight
`≤ 4 < 5`, `μ`-weight `≤ 2 < 5/2`), all three exact dichotomies
(`proximityGap_affine_johnson_exact`, `weighted_proximityGap_affine_johnson_exact`,
`ratWeighted_proximityGap_affine_johnson_exact`) refute the everywhere-close branch and prove
exact-denominator close counts `≤ B_line * 65537`. -/
theorem test_proximityGap_affine_johnson_exact_negative_2d_zmod65537 :
    open scoped Classical in
    (Finset.univ.filter fun z : Fin 2 → ZMod 65537 => ∃ c ∈ reedSolomon (pts5 65537) 2,
      hammingDist (parabola5 65537 + ∑ j : Fin 2, z j • (0 : Fin 2 → Fin 5 → ZMod 65537) j) c ≤
        2).card ≤ 1698 * 65537 ∧
    (Finset.univ.filter fun z : Fin 2 → ZMod 65537 => ∃ c ∈ reedSolomon (pts5 65537) 2,
      5 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (parabola5 65537 + ∑ j : Fin 2, z j • (0 : Fin 2 → Fin 5 → ZMod 65537) j) i = c i),
        wJ5 i).card ≤ 2026 * 65537 ∧
    (Finset.univ.filter fun z : Fin 2 → ZMod 65537 => ∃ c ∈ reedSolomon (pts5 65537) 2,
      (5 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (parabola5 65537 + ∑ j : Fin 2, z j • (0 : Fin 2 → Fin 5 → ZMod 65537) j) i = c i),
        muJ5 i).card ≤ 3338 * 65537 := by
  classical
  have hjb5 : ProximityGap.johnsonCurveBound 5 1 1 2 1 5 = 1698 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hjb6 : ProximityGap.johnsonCurveBound 5 1 1 2 1 6 = 2026 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hjb10 : ProximityGap.johnsonCurveBound 5 1 1 2 1 10 = 3338 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hinterp : Fintype.card (Fin 5) * (1 * (1 + 1) / 2) < #(Sudan.monomials (2 - 1) 2) := by
    rw [Fintype.card_fin]; change 5 * 1 < #(Sudan.monomials 1 2); rw [card_monomials_1_2]; omega
  have hW_le : ∀ i : Fin 5, wJ5 i ≤ 2 := by intro i; fin_cases i <;> decide
  have hW_sum : ∑ i : Fin 5, wJ5 i ≤ 6 := by decide
  have hμ_le : ∀ i : Fin 5, muJ5 i ≤ 1 := by intro i; fin_cases i <;> norm_num [muJ5]
  have hμ_den : ∀ i : Fin 5, ∃ a : ℕ, muJ5 i = (a : ℚ) / (2 : ℕ) := by
    intro i; fin_cases i
    · exact ⟨0, by norm_num [muJ5]⟩
    · exact ⟨1, by norm_num [muJ5]⟩
    · exact ⟨2, by norm_num [muJ5]⟩
    · exact ⟨2, by norm_num [muJ5]⟩
    · exact ⟨1, by norm_num [muJ5]⟩
  have hzero_sum : parabola5 65537 + ∑ j : Fin 2, (0 : Fin 2 → ZMod 65537) j •
      (0 : Fin 2 → Fin 5 → ZMod 65537) j = parabola5 65537 := by
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  refine ⟨?_, ?_, ?_⟩
  · rcases proximityGap_affine_johnson_exact (ℓ := 2) pts5_65537_injective (k := 2) (e := 2)
        (m := 1) (D := 2) (by omega) (by omega) (by rw [Fintype.card_fin]; omega) hinterp
        (by rw [Fintype.card_fin]; omega) (parabola5 65537) 0 with hall | hmul
    · obtain ⟨c, hcRS, hdist⟩ := hall 0
      rw [hzero_sum] at hdist
      have hcard := card_agree_parabola_le_two pts5_65537_injective hcRS
      have htot := card_agree_add_hammingDist (parabola5 65537) c
      omega
    · rw [Fintype.card_fin, ZMod.card] at hmul
      change 65537 * _ ≤ ProximityGap.johnsonCurveBound 5 1 1 2 1 5 * 65537 ^ 2 at hmul
      rw [hjb5] at hmul
      omega
  · rcases weighted_proximityGap_affine_johnson_exact (ℓ := 2) pts5_65537_injective (k := 2)
        (m := 1) (D := 2) (M := 2) (W_tot := 6) (B_W := 5) (by omega) (by omega) (by omega) hW_le
        hW_sum (by omega) hinterp (by omega) (parabola5 65537) 0 with hall | hmul
    · obtain ⟨c, hcRS, hge⟩ := hall 0
      rw [hzero_sum] at hge
      have hcard := card_agree_parabola_le_two pts5_65537_injective hcRS
      have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => parabola5 65537 i = c i), wJ5 i ≤
          (Finset.univ.filter fun i => parabola5 65537 i = c i).card * 2 := by
        calc ∑ i ∈ Finset.univ.filter (fun i => parabola5 65537 i = c i), wJ5 i
            ≤ ∑ _i ∈ Finset.univ.filter (fun i => parabola5 65537 i = c i), 2 :=
              Finset.sum_le_sum fun i _ => hW_le i
          _ = (Finset.univ.filter fun i => parabola5 65537 i = c i).card * 2 := by
              rw [Finset.sum_const, smul_eq_mul]
      omega
    · rw [Fintype.card_fin, ZMod.card] at hmul
      change 65537 * _ ≤ ProximityGap.johnsonCurveBound 5 1 1 2 1 6 * 65537 ^ 2 at hmul
      rw [hjb6] at hmul
      omega
  · rcases ratWeighted_proximityGap_affine_johnson_exact (ℓ := 2) pts5_65537_injective (k := 2)
        (m := 1) (D := 2) (M := 2) (θ := 5 / 2) (by omega) (by omega) (by omega) hμ_le hμ_den
        (by norm_num) hinterp (by norm_num) (parabola5 65537) 0 with hall | hmul
    · obtain ⟨c, hcRS, hge⟩ := hall 0
      rw [hzero_sum] at hge
      have hcard := card_agree_parabola_le_two pts5_65537_injective hcRS
      have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => parabola5 65537 i = c i), muJ5 i ≤
          ((Finset.univ.filter fun i => parabola5 65537 i = c i).card : ℚ) := by
        calc ∑ i ∈ Finset.univ.filter (fun i => parabola5 65537 i = c i), muJ5 i
            ≤ ∑ _i ∈ Finset.univ.filter (fun i => parabola5 65537 i = c i), (1 : ℚ) :=
              Finset.sum_le_sum fun i _ => hμ_le i
          _ = ((Finset.univ.filter fun i => parabola5 65537 i = c i).card : ℚ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hcardQ : ((Finset.univ.filter fun i => parabola5 65537 i = c i).card : ℚ) ≤ 2 := by
        exact_mod_cast hcard
      linarith
    · rw [Fintype.card_fin, ZMod.card] at hmul
      change 65537 * _ ≤ ProximityGap.johnsonCurveBound 5 1 1 2 1 10 * 65537 ^ 2 at hmul
      rw [hjb10] at hmul
      omega

/-! ### Test 6: Genuine multiplicity `m = 2` beyond-unique-decoding 2D affine space -/

/-- Genuine multiplicity `m = 2` (`D = 5`, `L = 5`, `B_line = 30807`) beyond-unique-decoding 2D
affine correlated agreement over `ZMod 200003` (`n = 5`, `k = 2`, `e = 2 > 1`) on the proper strip
`strip2D 200003 30808` with three corrupted words outside `reedSolomon` and no list-size premise. -/
theorem test_correlatedAgreement_affine_johnson_m2_2d_zmod200003 :
    cor0 200003 ∉ reedSolomon (pts5 200003) 2 ∧
    cor1 200003 ∉ reedSolomon (pts5 200003) 2 ∧
    cor2 200003 ∉ reedSolomon (pts5 200003) 2 ∧
    ProximityGap.johnsonCurveBound 5 2 1 5 1 5 = 30807 ∧
    ∃ D' : Finset (Fin 5), 3 ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon (pts5 200003) 2, ∃ v : Fin 2 → (Fin 5 → ZMod 200003),
        (∀ j, v j ∈ reedSolomon (pts5 200003) 2) ∧
        ∀ i ∈ D', cor0 200003 i = v₀ i ∧ ∀ j, (![cor1 200003, cor2 200003] j) i = v j i := by
  have hjb : ProximityGap.johnsonCurveBound 5 2 1 5 1 5 = 30807 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_5,
      maxYDeg_1_5]
    norm_num
  have hinterp : Fintype.card (Fin 5) * (2 * (2 + 1) / 2) < #(Sudan.monomials (2 - 1) 5) := by
    rw [Fintype.card_fin]; change 5 * 3 < #(Sudan.monomials 1 5); rw [card_monomials_1_5]; omega
  let u : Fin 2 → (Fin 5 → ZMod 200003) := ![cor1 200003, cor2 200003]
  let vTrue : Fin 2 → (Fin 5 → ZMod 200003) := ![lin1 200003, lin2 200003]
  have hvTrue : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 200003) 2 := by
    intro j; fin_cases j
    · exact lin1_mem_rs2
    · exact lin2_mem_rs2
  have hagree_true : ∀ i ∈ ({1, 2, 3} : Finset (Fin 5)),
      cor0 200003 i = lin0 200003 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hnot : ¬ (i = 0 ∨ i = 4) := by fin_cases hi <;> decide
    refine ⟨by simp only [cor0, hnot, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change cor1 200003 i = lin1 200003 i; simp only [cor1, hnot, ↓reduceIte]
    · change cor2 200003 i = lin2 200003 i; simp only [cor2, hnot, ↓reduceIte]
  have hclose : ∀ z ∈ strip2D 200003 30808,
      ∃ c ∈ reedSolomon (pts5 200003) 2,
        hammingDist (cor0 200003 + ∑ j : Fin 2, z j • u j) c ≤ 2 := fun z _ =>
    ⟨lin0 200003 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ lin0_mem_rs2
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hammingDist_affine_le_of_eq_on (D' := {1, 2, 3}) (by decide) hagree_true z⟩
  have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 2 (2 - 1) 5 1
      (Fintype.card (Fin 5)) * (Fintype.card (ZMod 200003)) ^ 2 <
      Fintype.card (ZMod 200003) * (strip2D 200003 30808).card := by
    rw [Fintype.card_fin, ZMod.card, strip2D_card (by omega)]
    change ProximityGap.johnsonCurveBound 5 2 1 5 1 5 * 200003 ^ 2 < 200003 * (30808 * 200003)
    rw [hjb]; norm_num
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_correlatedAgreement_affine_johnson (ℓ := 2) pts5_200003_injective (k := 2) (e := 2)
      (m := 2) (D := 5) (by omega) (by omega) (by rw [Fintype.card_fin]; omega) hinterp
      (by rw [Fintype.card_fin]; omega) (cor0 200003) u (strip2D 200003 30808) hT hclose
  exact ⟨cor0_not_mem_rs2, cor1_not_mem_rs2 (by decide), cor2_not_mem_rs2 (by decide), hjb,
    D', by simpa only [Fintype.card_fin] using hD', v₀, hv₀, v, hvRS, hagree⟩

/-! ### Test 8: List-premise-free regime `B_line < |F| < L * B_line` over `ZMod 2003` -/

/-- Over `ZMod 2003` (`n = 5`, `k = 2`, `e = 2 > 1`, `m = 1`, `D = 2`, `L = 2`, `B_line = 1698`),
`|F| = 2003 < 3396 = L * B_line` explicitly refutes the former list-size premise while
`exists_correlatedAgreement_affine_johnson` fires cleanly on `strip2D 2003 1699`. -/
theorem test_correlatedAgreement_affine_johnson_no_list_premise_zmod2003 :
    Fintype.card (ZMod 2003) <
      ProximityGap.maxYDeg 1 2 * ProximityGap.johnsonCurveBound 5 1 1 2 1 5 ∧
    cor0 2003 ∉ reedSolomon (pts5 2003) 2 ∧
    cor1 2003 ∉ reedSolomon (pts5 2003) 2 ∧
    cor2 2003 ∉ reedSolomon (pts5 2003) 2 ∧
    ∃ D' : Finset (Fin 5), 3 ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon (pts5 2003) 2, ∃ v : Fin 2 → (Fin 5 → ZMod 2003),
        (∀ j, v j ∈ reedSolomon (pts5 2003) 2) ∧
        ∀ i ∈ D', cor0 2003 i = v₀ i ∧ ∀ j, (![cor1 2003, cor2 2003] j) i = v j i := by
  have hjb : ProximityGap.johnsonCurveBound 5 1 1 2 1 5 = 1698 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hviol : Fintype.card (ZMod 2003) <
      ProximityGap.maxYDeg 1 2 * ProximityGap.johnsonCurveBound 5 1 1 2 1 5 := by
    rw [ZMod.card, maxYDeg_1_2, hjb]
    omega
  have hinterp : Fintype.card (Fin 5) * (1 * (1 + 1) / 2) < #(Sudan.monomials (2 - 1) 2) := by
    rw [Fintype.card_fin]; change 5 * 1 < #(Sudan.monomials 1 2); rw [card_monomials_1_2]; omega
  let u : Fin 2 → (Fin 5 → ZMod 2003) := ![cor1 2003, cor2 2003]
  let vTrue : Fin 2 → (Fin 5 → ZMod 2003) := ![lin1 2003, lin2 2003]
  have hvTrue : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 2003) 2 := by
    intro j; fin_cases j
    · exact lin1_mem_rs2
    · exact lin2_mem_rs2
  have hagree_true : ∀ i ∈ ({1, 2, 3} : Finset (Fin 5)),
      cor0 2003 i = lin0 2003 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hnot : ¬ (i = 0 ∨ i = 4) := by fin_cases hi <;> decide
    refine ⟨by simp only [cor0, hnot, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change cor1 2003 i = lin1 2003 i; simp only [cor1, hnot, ↓reduceIte]
    · change cor2 2003 i = lin2 2003 i; simp only [cor2, hnot, ↓reduceIte]
  have hclose : ∀ z ∈ strip2D 2003 1699, ∃ c ∈ reedSolomon (pts5 2003) 2,
      hammingDist (cor0 2003 + ∑ j : Fin 2, z j • u j) c ≤ 2 := fun z _ =>
    ⟨lin0 2003 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ lin0_mem_rs2
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hammingDist_affine_le_of_eq_on (D' := {1, 2, 3}) (by decide) hagree_true z⟩
  have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 1
      (Fintype.card (Fin 5)) * (Fintype.card (ZMod 2003)) ^ 2 <
      Fintype.card (ZMod 2003) * (strip2D 2003 1699).card := by
    rw [Fintype.card_fin, ZMod.card, strip2D_card (by omega)]
    change ProximityGap.johnsonCurveBound 5 1 1 2 1 5 * 2003 ^ 2 < 2003 * (1699 * 2003)
    rw [hjb]; norm_num
  obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
    exists_correlatedAgreement_affine_johnson (ℓ := 2) (pts5_injective (by omega)) (k := 2)
      (e := 2) (m := 1) (D := 2) (by omega) (by omega) (by rw [Fintype.card_fin]; omega) hinterp
      (by rw [Fintype.card_fin]; omega) (cor0 2003) u (strip2D 2003 1699) hT hclose
  exact ⟨hviol, cor0_not_mem_rs2, cor1_not_mem_rs2 (by decide), cor2_not_mem_rs2 (by decide),
    D', by simpa only [Fintype.card_fin] using hD', v₀, hv₀, v, hvRS, hagree⟩

/-! ### Test 9: Zero-weight coordinate regression (`W 0 = 0`, `μ 0 = 0`) over `ZMod 65537` -/

/-- Word corrupted solely at the zero-weight coordinate `0` (`wJ5 0 = 0`, `muJ5 0 = 0`). -/
private def spikeZero5 (p : ℕ) : Fin 5 → ZMod p := fun i => if i = 0 then 1 else 0

/-- Second generator corrupted solely at the zero-weight coordinate `0`. -/
private def spikeLin5 (p : ℕ) : Fin 5 → ZMod p :=
  fun i => if i = 0 then lin2 p 0 + 3 else lin2 p i

private theorem spikeZero5_not_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)] :
    spikeZero5 p ∉ reedSolomon (pts5 p) 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
  have hval : spikeZero5 p 0 - 2 * spikeZero5 p 1 + spikeZero5 p 2 = 1 := by
    have h1 : (1 : Fin 5) ≠ 0 := by decide
    have h2 : (2 : Fin 5) ≠ 0 := by decide
    simp only [spikeZero5, ↓reduceIte, h1, h2]
    ring
  rw [hval] at hdiff
  exact one_ne_zero hdiff

private theorem spikeLin5_not_mem_rs2 {p : ℕ} [Fact (Nat.Prime p)] (h3ne : (3 : ZMod p) ≠ 0) :
    spikeLin5 p ∉ reedSolomon (pts5 p) 2 := by
  intro hmem
  have hdiff := (second_diff_zero_of_mem_rs2 hmem).1
  have hval : spikeLin5 p 0 - 2 * spikeLin5 p 1 + spikeLin5 p 2 = 3 := by
    have h1 : (1 : Fin 5) ≠ 0 := by decide
    have h2 : (2 : Fin 5) ≠ 0 := by decide
    simp only [spikeLin5, lin2, pts5, ↓reduceIte, h1, h2, Fin.val_zero, Fin.val_one, Fin.val_two,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
    ring
  rw [hval] at hdiff
  exact h3ne hdiff

private theorem eq_of_mem_rs2_eq_at_one_two {p : ℕ} [Fact (Nat.Prime p)]
    {c₁ c₂ : Fin 5 → ZMod p}
    (hc₁ : c₁ ∈ reedSolomon (pts5 p) 2) (hc₂ : c₂ ∈ reedSolomon (pts5 p) 2)
    (h1 : c₁ 1 = c₂ 1) (h2 : c₁ 2 = c₂ 2) : c₁ = c₂ := by
  obtain ⟨f₁, hf₁, rfl⟩ := mem_reedSolomon.1 hc₁
  obtain ⟨f₂, hf₂, rfl⟩ := mem_reedSolomon.1 hc₂
  have he1 : f₁.eval (1 : ZMod p) = f₂.eval (1 : ZMod p) := by simpa only [pts5, Fin.val_one,
    Nat.cast_one] using h1
  have he2 : f₁.eval (2 : ZMod p) = f₂.eval (2 : ZMod p) := by simpa only [pts5, Fin.val_two,
    Nat.cast_ofNat] using h2
  rw [eval_eq_of_degree_lt_two hf₁, eval_eq_of_degree_lt_two hf₂] at he1 he2
  funext i
  rw [eval_eq_of_degree_lt_two hf₁, eval_eq_of_degree_lt_two hf₂]
  have hb : f₁.coeff 1 = f₂.coeff 1 := by linear_combination he2 - he1
  have ha : f₁.coeff 0 = f₂.coeff 0 := by linear_combination 2 * he1 - he2
  rw [ha, hb]

/-- Zero-weight coordinate regression (`wJ5 = ![0, 1, 2, 2, 1]`, `B_W = 6`, `muJ5`, `θ = 3`) over
`ZMod 65537`: at `u* = u₀ = 0`, the unguarded candidate agreement set
`{i | (0 : Fin 5 → ZMod 65537) i = 0} = univ` admits **no** codeword matching `spikeZero5 65537`
(demonstrating why printed p. 34's `D' = D'_i` claim fails without intersecting with `supp W`),
while `exists_weighted_correlatedAgreement_affine_of_line`,
`exists_weighted_correlatedAgreement_affine_of_divergence`,
`exists_weighted_correlatedAgreement_affine_johnson`, and
`exists_ratWeighted_correlatedAgreement_affine_johnson` all succeed and avoid coordinate `0`. -/
theorem test_weighted_correlatedAgreement_zero_weight_spike_zmod65537 :
    spikeZero5 65537 ∉ reedSolomon (pts5 65537) 2 ∧
    spikeLin5 65537 ∉ reedSolomon (pts5 65537) 2 ∧
    (¬ ∃ v ∈ reedSolomon (pts5 65537) 2,
      ∀ i ∈ Finset.univ.filter (fun i : Fin 5 =>
        (0 : Fin 5 → ZMod 65537) i = (0 : Fin 5 → ZMod 65537) i),
        spikeZero5 65537 i = v i) ∧
    (∃ D' : Finset (Fin 5), (0 : Fin 5) ∉ D' ∧ 6 ≤ ∑ i ∈ D', wJ5 i ∧
      ∃ v₀ ∈ reedSolomon (pts5 65537) 2, ∃ v : Fin 2 → (Fin 5 → ZMod 65537),
        (∀ j, v j ∈ reedSolomon (pts5 65537) 2) ∧
        ∀ i ∈ D', (0 : Fin 5 → ZMod 65537) i = v₀ i ∧
          ∀ j, (![spikeZero5 65537, spikeLin5 65537] j) i = v j i) ∧
    (∃ D' : Finset (Fin 5), (0 : Fin 5) ∉ D' ∧ (3 : ℚ) ≤ ∑ i ∈ D', muJ5 i ∧
      ∃ v₀ ∈ reedSolomon (pts5 65537) 2, ∃ v : Fin 2 → (Fin 5 → ZMod 65537),
        (∀ j, v j ∈ reedSolomon (pts5 65537) 2) ∧
        ∀ i ∈ D', (0 : Fin 5 → ZMod 65537) i = v₀ i ∧
          ∀ j, (![spikeZero5 65537, spikeLin5 65537] j) i = v j i) := by
  classical
  have hnaive_false : ¬ ∃ v ∈ reedSolomon (pts5 65537) 2,
      ∀ i ∈ Finset.univ.filter (fun i : Fin 5 =>
        (0 : Fin 5 → ZMod 65537) i = (0 : Fin 5 → ZMod 65537) i),
        spikeZero5 65537 i = v i := by
    rintro ⟨v, hvRS, hall⟩
    have hv_eq : spikeZero5 65537 = v := funext fun i => hall i (mem_filter.2 ⟨mem_univ i, rfl⟩)
    exact spikeZero5_not_mem_rs2 (hv_eq ▸ hvRS)
  have hjb6 : ProximityGap.johnsonCurveBound 5 1 1 2 1 6 = 2026 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hjb10 : ProximityGap.johnsonCurveBound 5 1 1 2 1 10 = 3338 := by
    simp only [ProximityGap.johnsonCurveBound, ProximityGap.siegelZDeg, card_monomials_1_2,
      maxYDeg_1_2]
    norm_num
  have hinterp : Fintype.card (Fin 5) * (1 * (1 + 1) / 2) < #(Sudan.monomials (2 - 1) 2) := by
    rw [Fintype.card_fin]; change 5 * 1 < #(Sudan.monomials 1 2); rw [card_monomials_1_2]; omega
  have hW_le : ∀ i : Fin 5, wJ5 i ≤ 2 := by intro i; fin_cases i <;> decide
  have hW_sum : ∑ i : Fin 5, wJ5 i ≤ 6 := by decide
  have hμ_le : ∀ i : Fin 5, muJ5 i ≤ 1 := by intro i; fin_cases i <;> norm_num [muJ5]
  have hμ_nn : ∀ i : Fin 5, 0 ≤ muJ5 i := by intro i; fin_cases i <;> norm_num [muJ5]
  have hμ_den : ∀ i : Fin 5, ∃ a : ℕ, muJ5 i = (a : ℚ) / (2 : ℕ) := by
    intro i; fin_cases i
    · exact ⟨0, by norm_num [muJ5]⟩
    · exact ⟨1, by norm_num [muJ5]⟩
    · exact ⟨2, by norm_num [muJ5]⟩
    · exact ⟨2, by norm_num [muJ5]⟩
    · exact ⟨1, by norm_num [muJ5]⟩
  let u₀ : Fin 5 → ZMod 65537 := 0
  let u : Fin 2 → (Fin 5 → ZMod 65537) := ![spikeZero5 65537, spikeLin5 65537]
  let vTrue : Fin 2 → (Fin 5 → ZMod 65537) := ![0, lin2 65537]
  have hvTrue : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 65537) 2 := by
    intro j; fin_cases j
    · exact Submodule.zero_mem _
    · exact lin2_mem_rs2
  have hagree_pos : ∀ i ∈ ({1, 2, 3, 4} : Finset (Fin 5)),
      u₀ i = (0 : Fin 5 → ZMod 65537) i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hne0 : i ≠ 0 := by fin_cases hi <;> decide
    refine ⟨rfl, fun j => ?_⟩
    fin_cases j
    · change spikeZero5 65537 i = 0; simp only [spikeZero5, hne0, ↓reduceIte]
    · change spikeLin5 65537 i = lin2 65537 i; simp only [spikeLin5, hne0, ↓reduceIte]
  have hW_pos : (6 : ℕ) ≤ ∑ i ∈ ({1, 2, 3, 4} : Finset (Fin 5)), wJ5 i := by decide
  have hμ_pos : (3 : ℚ) ≤ ∑ i ∈ ({1, 2, 3, 4} : Finset (Fin 5)), muJ5 i := by
    have hcard : ({1, 2, 3, 4} : Finset (Fin 5)) = {1, 2, 3, 4} := rfl
    norm_num [muJ5]
  have hcloseW_all : ∀ z : Fin 2 → ZMod 65537, ∃ c ∈ reedSolomon (pts5 65537) 2,
      6 ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin 2, z j • u j) i = c i), wJ5 i :=
    fun z => ⟨0 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ (Submodule.zero_mem _)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hW_pos.trans (weightedAgree_affine_ge_of_eq_on wJ5 hagree_pos z)⟩
  have hcloseμ_all : ∀ z : Fin 2 → ZMod 65537, ∃ c ∈ reedSolomon (pts5 65537) 2,
      (3 : ℚ) ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin 2, z j • u j) i = c i), muJ5 i :=
    fun z => ⟨0 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ (Submodule.zero_mem _)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hμ_pos.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nn hagree_pos z)⟩
  -- Exercise generic `exists_weighted_correlatedAgreement_affine_of_divergence` & `..._of_line`
  -- directly (`L = 1`: weight `≥ 6` forces agreement at coordinates `1` and `2`).
  have hmem_12_of_w6 :
      ∀ S : Finset (Fin 5), 6 ≤ ∑ i ∈ S, wJ5 i → (1 : Fin 5) ∈ S ∧ (2 : Fin 5) ∈ S := by
    intro S hS
    revert hS
    decide +revert
  have hlist1 : ∀ w : Fin 5 → ZMod 65537, ∃ Lset : Finset (Fin 5 → ZMod 65537), Lset.card ≤ 1 ∧
      ∀ c ∈ reedSolomon (pts5 65537) 2,
        6 ≤ ∑ i ∈ Finset.univ.filter (fun i => w i = c i), wJ5 i → c ∈ Lset := by
    intro w
    by_cases hex : ∃ c ∈ reedSolomon (pts5 65537) 2,
        6 ≤ ∑ i ∈ Finset.univ.filter (fun i => w i = c i), wJ5 i
    · refine ⟨{Classical.choose hex}, (Finset.card_singleton _).le, fun c hcRS hcW => ?_⟩
      obtain ⟨hc0RS, hc0W⟩ := Classical.choose_spec hex
      obtain ⟨h1c, h2c⟩ := hmem_12_of_w6 _ hcW
      obtain ⟨h10, h20⟩ := hmem_12_of_w6 _ hc0W
      rw [Finset.mem_singleton]
      exact eq_of_mem_rs2_eq_at_one_two hcRS hc0RS
        (((mem_filter.1 h1c).2).symm.trans (mem_filter.1 h10).2)
        (((mem_filter.1 h2c).2).symm.trans (mem_filter.1 h20).2)
    · refine ⟨∅, by decide, fun c hcRS hcW => (hex ⟨c, hcRS, hcW⟩).elim⟩
  have hline6 : ∀ {B' : ℕ}, 6 ≤ B' → ∀ (a b : Fin 5 → ZMod 65537) (S : Finset (ZMod 65537)),
      2026 < S.card →
      (∀ t ∈ S, ∃ c ∈ reedSolomon (pts5 65537) 2,
        B' ≤ ∑ i ∈ Finset.univ.filter (fun i => (a + t • b) i = c i), wJ5 i) →
      ∃ D' : Finset (Fin 5), B' ≤ ∑ i ∈ D', wJ5 i ∧
        ∃ w₀ ∈ reedSolomon (pts5 65537) 2, ∃ w₁ ∈ reedSolomon (pts5 65537) 2,
          ∀ i ∈ D', a i = w₀ i ∧ b i = w₁ i := by
    intro B' hB' a b S hS hcl
    have ht_le : 3 ≤ (B' + 2 - 1) / 2 := by omega
    have hS' : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 1 6 < S.card := by
      rw [Fintype.card_fin]; change ProximityGap.johnsonCurveBound 5 1 1 2 1 6 < S.card
      rwa [hjb6]
    exact exists_weighted_correlatedAgreement_line_johnson pts5_65537_injective (k := 2) (m := 1)
      (D := 2) (M := 2) (W_tot := 6) (B_W := B') (by omega) (by omega) (by omega) hW_le hW_sum
      (by omega) hinterp (by omega) a b S hS' hcl
  have _hdiv_witness := exists_weighted_correlatedAgreement_affine_of_divergence hlist1
    (fun hB' a b hcl => hline6 hB' a b Finset.univ
      (by rw [Finset.card_univ, ZMod.card]; omega) (fun t _ => hcl t))
    (fun _ => by rw [ZMod.card]; omega) u₀ u hcloseW_all
  have hTW : 2026 * (Fintype.card (ZMod 65537)) ^ 2 <
      Fintype.card (ZMod 65537) * (strip2D 65537 2027).card := by
    rw [ZMod.card, strip2D_card (by omega)]; norm_num
  obtain ⟨D'₀, hsupp₀, _, _, _, _, _, _⟩ :=
    exists_weighted_correlatedAgreement_affine_of_line hlist1 hline6
      (fun _ => by rw [ZMod.card]; omega) u₀ u (strip2D 65537 2027) hTW (fun z _ => hcloseW_all z)
  have _h0_not_mem₀ : (0 : Fin 5) ∉ D'₀ := fun h0 => hsupp₀ 0 h0 rfl
  -- Any `D'` of weight `≥ 6` on which `spikeZero5 65537` matches an RS codeword avoids `0`.
  have h0_not_of_agree : ∀ (D' : Finset (Fin 5)) (v : Fin 2 → Fin 5 → ZMod 65537),
      6 ≤ ∑ i ∈ D', wJ5 i → v 0 ∈ reedSolomon (pts5 65537) 2 →
      (∀ i ∈ D', spikeZero5 65537 i = v 0 i) → (0 : Fin 5) ∉ D' := by
    intro D' v hDW hv0 hsp h0mem
    obtain ⟨h1D, h2D⟩ := hmem_12_of_w6 D' hDW
    have hsp1 : spikeZero5 65537 1 = 0 := by
      simp only [spikeZero5, show (1 : Fin 5) ≠ 0 by decide, ↓reduceIte]
    have hsp2 : spikeZero5 65537 2 = 0 := by
      simp only [spikeZero5, show (2 : Fin 5) ≠ 0 by decide, ↓reduceIte]
    have hv0_eq : v 0 = 0 := eq_of_mem_rs2_eq_at_one_two hv0 (Submodule.zero_mem _)
      ((hsp 1 h1D).symm.trans hsp1) ((hsp 2 h2D).symm.trans hsp2)
    have h0eq := hsp 0 h0mem
    rw [hv0_eq] at h0eq
    exact one_ne_zero h0eq
  refine ⟨spikeZero5_not_mem_rs2, spikeLin5_not_mem_rs2 (by decide), hnaive_false, ?_, ?_⟩
  · have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 1 6 *
        (Fintype.card (ZMod 65537)) ^ 2 <
        Fintype.card (ZMod 65537) * (strip2D 65537 2027).card := by
      rw [Fintype.card_fin, ZMod.card, strip2D_card (by omega)]
      change ProximityGap.johnsonCurveBound 5 1 1 2 1 6 * 65537 ^ 2 < 65537 * (2027 * 65537)
      rw [hjb6]; norm_num
    obtain ⟨D', hDW, v₀, hv₀, v, hvRS, hagree⟩ :=
      exists_weighted_correlatedAgreement_affine_johnson (ℓ := 2) pts5_65537_injective
        (k := 2) (m := 1) (D := 2) (M := 2) (W_tot := 6) (B_W := 6) (by omega) (by omega)
        (by omega) hW_le hW_sum (by omega) hinterp (by omega) u₀ u (strip2D 65537 2027) hT
        (fun z _ => hcloseW_all z)
    refine ⟨D', h0_not_of_agree D' v hDW (hvRS 0) (fun i hi => (hagree i hi).2 0), hDW, v₀, hv₀, v,
      hvRS, hagree⟩
  · have hT : ProximityGap.johnsonCurveBound (Fintype.card (Fin 5)) 1 (2 - 1) 2 1
        (2 * Fintype.card (Fin 5)) * (Fintype.card (ZMod 65537)) ^ 2 <
        Fintype.card (ZMod 65537) * (strip2D 65537 3339).card := by
      rw [Fintype.card_fin, ZMod.card, strip2D_card (by omega)]
      change ProximityGap.johnsonCurveBound 5 1 1 2 1 10 * 65537 ^ 2 < 65537 * (3339 * 65537)
      rw [hjb10]; norm_num
    obtain ⟨D', hDμ, v₀, hv₀, v, hvRS, hagree⟩ :=
      exists_ratWeighted_correlatedAgreement_affine_johnson (ℓ := 2) pts5_65537_injective
        (k := 2) (m := 1) (D := 2) (M := 2) (θ := 3) (by omega) (by omega) (by omega) hμ_le hμ_den
        (by norm_num) hinterp (by norm_num) u₀ u (strip2D 65537 3339) hT
        (fun z _ => hcloseμ_all z)
    have hDW : 6 ≤ ∑ i ∈ D', wJ5 i := by
      have h2 : ∑ i ∈ D', (wJ5 i : ℚ) = 2 * ∑ i ∈ D', muJ5 i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        fin_cases i <;> norm_num [wJ5, muJ5]
      have h6Q : (6 : ℚ) ≤ ((∑ i ∈ D', wJ5 i : ℕ) : ℚ) := by
        rw [Nat.cast_sum, h2]
        linarith
      exact_mod_cast h6Q
    refine ⟨D', h0_not_of_agree D' v hDW (hvRS 0) (fun i hi => (hagree i hi).2 0), hDμ, v₀, hv₀, v,
      hvRS, hagree⟩

/-! ### Test 7: Beyond-unique-decoding real-asymptotic curve & affine dichotomies and CA -/

section RealAsymptoticJohnsonTests

private noncomputable local instance : Fintype (GaloisField 11 14) := Fintype.ofFinite _

private theorem eq_const_of_mem_rs1 {F ι : Type*} [Field F] {α : ι → F} {c : ι → F}
    (hc : c ∈ reedSolomon α 1) : ∃ a : F, ∀ i, c i = a := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hc
  refine ⟨p.coeff 0, fun i => ?_⟩
  have hdeg0 : p.natDegree = 0 := by
    by_cases hp0 : p = 0
    · rw [hp0, natDegree_zero]
    · have := (natDegree_lt_iff_degree_lt hp0).2 hp
      omega
  dsimp only
  conv_lhs => rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg0]
  rw [eval_C]

/-- If `α : ι → F` is injective, any constant codeword `c ∈ reedSolomon α 1` agrees with `α` on at
most one coordinate. -/
private theorem card_agree_inj_rs1_le_one {F ι : Type*} [Field F] [Fintype ι] [DecidableEq F]
    {α : ι → F} (hα : Function.Injective α) {c : ι → F} (hc : c ∈ reedSolomon α 1) :
    (Finset.univ.filter fun i => α i = c i).card ≤ 1 := by
  obtain ⟨a, ha⟩ := eq_const_of_mem_rs1 hc
  refine Finset.card_le_one.2 fun i hi j hj => ?_
  have hi' := (mem_filter.1 hi).2
  have hj' := (mem_filter.1 hj).2
  exact hα (hi'.trans ((ha i).trans ((ha j).symm.trans hj'.symm)))

/-- Non-constant integer weights on `Fin 9` with `M = 2`. -/
private def wJ9 : Fin 9 → ℕ := ![2, 2, 2, 2, 2, 1, 1, 1, 0]

/-- Matching rational weights on `Fin 9` with denominator `M = 2`. -/
private def muJ9 : Fin 9 → ℚ := ![1, 1, 1, 1, 1, (1 : ℚ) / 2, (1 : ℚ) / 2, (1 : ℚ) / 2, 0]

/-- Beyond-unique-decoding (`n = 9`, `k = 1`, `e = 5 > 4 = (9 - 1) / 2`, `m = 2`, `η = 1 / 9`)
real-asymptotic curve proximity-gap dichotomies over `GaloisField 11 14` (`r = 2`):
exercises `proximityGap_curve_johnson`, `proximityGap_curve_johnson_of_eta`,
`weighted_proximityGap_curve_johnson`, and `ratWeighted_proximityGap_curve_johnson`, refuting the
everywhere-close branch via `u 0 = α` and proving exceptional fractions strictly below `1`. -/
theorem test_proximityGap_curve_johnson_asymptotic_gf11_14 :
    open scoped Classical in
    let α : Fin 9 → GaloisField 11 14 :=
      fun i => algebraMap (ZMod 11) (GaloisField 11 14) (i.val : ZMod 11)
    let u : Fin 3 → (Fin 9 → GaloisField 11 14) := ![α, 0, 0]
    ((#(Finset.univ.filter fun z : GaloisField 11 14 => ∃ c ∈ reedSolomon α 1,
        hammingDist (∑ j : Fin 3, z ^ (j : ℕ) • u j) c ≤ 5) : ℝ) /
      (Fintype.card (GaloisField 11 14) : ℝ)) < 1 ∧
    ((#(Finset.univ.filter fun z : GaloisField 11 14 => ∃ c ∈ reedSolomon α 1,
        8 ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin 3, z ^ (j : ℕ) • u j) i = c i), wJ9 i) : ℝ) /
      (Fintype.card (GaloisField 11 14) : ℝ)) < 1 ∧
    ((#(Finset.univ.filter fun z : GaloisField 11 14 => ∃ c ∈ reedSolomon α 1,
        (4 : ℚ) ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin 3, z ^ (j : ℕ) • u j) i = c i), muJ9 i) : ℝ) /
      (Fintype.card (GaloisField 11 14) : ℝ)) < 1 := by
  classical
  intro α u
  have hcard : Fintype.card (GaloisField 11 14) = 11 ^ 14 :=
    (Nat.card_eq_fintype_card (α := GaloisField 11 14)).symm.trans
      (GaloisField.card 11 14 (by omega))
  have hα : Function.Injective α := by
    intro i j h
    have h1 : (i.val : ZMod 11) = (j.val : ZMod 11) :=
      (algebraMap (ZMod 11) (GaloisField 11 14)).injective h
    have hv := congrArg ZMod.val h1
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv
  have hsq : Real.sqrt ((1 : ℝ) / 9) = 1 / 3 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have he_m2 : ((5 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
        Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
    rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
  have he_eta : ((5 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) - (1 / 9 : ℝ) := by
    rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
  have hcurve0 : (∑ j : Fin 3, (0 : GaloisField 11 14) ^ (j : ℕ) • u j) = α := by
    rw [Fin.sum_univ_three]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, Fin.val_two,
      zero_pow (by decide : 2 ≠ 0), zero_smul, u, Matrix.cons_val_zero, add_zero]
  have hW_le : ∀ i : Fin 9, wJ9 i ≤ 2 := by intro i; fin_cases i <;> decide
  have hμ_le : ∀ i : Fin 9, muJ9 i ≤ 1 := by intro i; fin_cases i <;> norm_num [muJ9]
  have hμ_den : ∀ i : Fin 9, ∃ a : ℕ, muJ9 i = (a : ℚ) / (2 : ℕ) := by
    intro i; fin_cases i
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨0, by norm_num [muJ9]⟩
  have hnot_unw : ¬ (∀ z : GaloisField 11 14, ∃ c ∈ reedSolomon α 1,
      hammingDist (∑ j : Fin 3, z ^ (j : ℕ) • u j) c ≤ 5) := by
    intro hall
    obtain ⟨c, hcRS, hdist⟩ := hall 0
    rw [hcurve0] at hdist
    have hle1 := card_agree_inj_rs1_le_one hα hcRS
    have htot := card_filter_eq_add_hammingDist α c
    rw [Fintype.card_fin] at htot
    omega
  -- Exercise both `proximityGap_curve_johnson` and `proximityGap_curve_johnson_of_eta`.
  have hgap_m := (proximityGap_curve_johnson (e := 5) (k := 1) (m := 2) (r := 2) hα (by omega)
    (by rw [Fintype.card_fin]; omega) (by omega) he_m2 u).resolve_left hnot_unw
  have hgap_eta := (proximityGap_curve_johnson_of_eta (e := 5) (k := 1) (r := 2) (η := 1 / 9) hα
    (by omega) (by rw [Fintype.card_fin]; omega) (by norm_num) he_eta u).resolve_left hnot_unw
  have _h_m_lt : ((#(Finset.univ.filter fun z : GaloisField 11 14 => ∃ c ∈ reedSolomon α 1,
      hammingDist (∑ j : Fin 3, z ^ (j : ℕ) • u j) c ≤ 5) : ℝ) /
      (Fintype.card (GaloisField 11 14) : ℝ)) < 1 := by
    refine hgap_m.trans_lt ?_
    rw [Fintype.card_fin, hcard]; norm_num
  refine ⟨hgap_eta.trans_lt (by rw [Fintype.card_fin, hcard]; norm_num), ?_, ?_⟩
  · -- `weighted_proximityGap_curve_johnson` (`B_W = 8`, `M = 2`, `n - (8 + 2 - 1)/2 = 5`).
    have hnotW : ¬ (∀ z : GaloisField 11 14, ∃ c ∈ reedSolomon α 1,
        8 ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin 3, z ^ (j : ℕ) • u j) i = c i), wJ9 i) := by
      intro hall
      obtain ⟨c, hcRS, hge⟩ := hall 0
      rw [hcurve0] at hge
      have hle1 := card_agree_inj_rs1_le_one hα hcRS
      have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => α i = c i), wJ9 i ≤
          (Finset.univ.filter fun i => α i = c i).card * 2 := by
        calc ∑ i ∈ Finset.univ.filter (fun i => α i = c i), wJ9 i
            ≤ ∑ _i ∈ Finset.univ.filter (fun i => α i = c i), 2 :=
              Finset.sum_le_sum fun i _ => hW_le i
          _ = (Finset.univ.filter fun i => α i = c i).card * 2 := by
              rw [Finset.sum_const, smul_eq_mul]
      omega
    have hB : ((Fintype.card (Fin 9) - (8 + 2 - 1) / 2 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
        1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
          Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
      rw [Fintype.card_fin]; norm_num [hsq]
    have hgapW := (weighted_proximityGap_curve_johnson (k := 1) (m := 2) (r := 2) (M := 2)
      (B_W := 8) hα (by omega) (by rw [Fintype.card_fin]; omega) (by omega) (by omega) hW_le hB
      u).resolve_left hnotW
    exact hgapW.trans_lt (by rw [Fintype.card_fin, hcard]; norm_num)
  · -- `ratWeighted_proximityGap_curve_johnson` (`θ = 4`, `M = 2`, `1 - 4/9 = 5/9 ≤ 7/12`).
    have hnotμ : ¬ (∀ z : GaloisField 11 14, ∃ c ∈ reedSolomon α 1,
        (4 : ℚ) ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (∑ j : Fin 3, z ^ (j : ℕ) • u j) i = c i), muJ9 i) := by
      intro hall
      obtain ⟨c, hcRS, hge⟩ := hall 0
      rw [hcurve0] at hge
      have hle1 := card_agree_inj_rs1_le_one hα hcRS
      have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => α i = c i), muJ9 i ≤
          ((Finset.univ.filter fun i => α i = c i).card : ℚ) := by
        calc ∑ i ∈ Finset.univ.filter (fun i => α i = c i), muJ9 i
            ≤ ∑ _i ∈ Finset.univ.filter (fun i => α i = c i), (1 : ℚ) :=
              Finset.sum_le_sum fun i _ => hμ_le i
          _ = ((Finset.univ.filter fun i => α i = c i).card : ℚ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hle1Q : ((Finset.univ.filter fun i => α i = c i).card : ℚ) ≤ 1 := by exact_mod_cast hle1
      linarith
    have hθ : 1 - ((4 : ℚ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
        1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
          Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
      rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
    have hgapμ := (ratWeighted_proximityGap_curve_johnson (k := 1) (m := 2) (r := 2) (M := 2)
      (θ := 4) hα (by omega) (by rw [Fintype.card_fin]; omega) (by omega) (by omega) hμ_le hμ_den
      hθ u).resolve_left hnotμ
    exact hgapμ.trans_lt (by rw [Fintype.card_fin, hcard]; norm_num)

/-- Beyond-unique-decoding (`n = 9`, `k = 1`, `e = 5 > 4 = (9 - 1) / 2`, `m = 2`, `η = 1 / 9`)
dimension-independent 2D affine proximity-gap dichotomies over `GaloisField 11 14` (`ℓ = 2`):
exercises `proximityGap_affine_johnson`, `proximityGap_affine_johnson_of_eta`,
`weighted_proximityGap_affine_johnson`, and `ratWeighted_proximityGap_affine_johnson`, proving
nontrivial exceptional fractions strictly below `1`. -/
theorem test_proximityGap_affine_johnson_asymptotic_gf11_14 :
    open scoped Classical in
    let α : Fin 9 → GaloisField 11 14 :=
      fun i => algebraMap (ZMod 11) (GaloisField 11 14) (i.val : ZMod 11)
    let u : Fin 2 → (Fin 9 → GaloisField 11 14) := 0
    ((#(Finset.univ.filter fun z : Fin 2 → GaloisField 11 14 => ∃ c ∈ reedSolomon α 1,
        hammingDist (α + ∑ j : Fin 2, z j • u j) c ≤ 5) : ℝ) /
      ((Fintype.card (GaloisField 11 14) : ℝ) ^ 2)) < 1 ∧
    ((#(Finset.univ.filter fun z : Fin 2 → GaloisField 11 14 => ∃ c ∈ reedSolomon α 1,
        8 ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (α + ∑ j : Fin 2, z j • u j) i = c i), wJ9 i) : ℝ) /
      ((Fintype.card (GaloisField 11 14) : ℝ) ^ 2)) < 1 ∧
    ((#(Finset.univ.filter fun z : Fin 2 → GaloisField 11 14 => ∃ c ∈ reedSolomon α 1,
        (4 : ℚ) ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (α + ∑ j : Fin 2, z j • u j) i = c i), muJ9 i) : ℝ) /
      ((Fintype.card (GaloisField 11 14) : ℝ) ^ 2)) < 1 := by
  classical
  intro α u
  have hcard : Fintype.card (GaloisField 11 14) = 11 ^ 14 :=
    (Nat.card_eq_fintype_card (α := GaloisField 11 14)).symm.trans
      (GaloisField.card 11 14 (by omega))
  have hα : Function.Injective α := by
    intro i j h
    have h1 : (i.val : ZMod 11) = (j.val : ZMod 11) :=
      (algebraMap (ZMod 11) (GaloisField 11 14)).injective h
    have hv := congrArg ZMod.val h1
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv
  have hsq : Real.sqrt ((1 : ℝ) / 9) = 1 / 3 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have he_m2 : ((5 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
        Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
    rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
  have he_eta : ((5 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) - (1 / 9 : ℝ) := by
    rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
  have haff0 : α + ∑ j : Fin 2, (0 : Fin 2 → GaloisField 11 14) j • u j = α := by
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  have hW_le : ∀ i : Fin 9, wJ9 i ≤ 2 := by intro i; fin_cases i <;> decide
  have hμ_le : ∀ i : Fin 9, muJ9 i ≤ 1 := by intro i; fin_cases i <;> norm_num [muJ9]
  have hμ_den : ∀ i : Fin 9, ∃ a : ℕ, muJ9 i = (a : ℚ) / (2 : ℕ) := by
    intro i; fin_cases i
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨0, by norm_num [muJ9]⟩
  have hnot_unw : ¬ (∀ z : Fin 2 → GaloisField 11 14, ∃ c ∈ reedSolomon α 1,
      hammingDist (α + ∑ j : Fin 2, z j • u j) c ≤ 5) := by
    intro hall
    obtain ⟨c, hcRS, hdist⟩ := hall 0
    rw [haff0] at hdist
    have hle1 := card_agree_inj_rs1_le_one hα hcRS
    have htot := card_filter_eq_add_hammingDist α c
    rw [Fintype.card_fin] at htot
    omega
  -- Exercise both `proximityGap_affine_johnson` and `proximityGap_affine_johnson_of_eta`.
  have hgap_m := (proximityGap_affine_johnson (e := 5) (k := 1) (m := 2) (ℓ := 2) hα (by omega)
    (by rw [Fintype.card_fin]; omega) (by omega) he_m2 α u).resolve_left hnot_unw
  have hgap_eta := (proximityGap_affine_johnson_of_eta (e := 5) (k := 1) (ℓ := 2) (η := 1 / 9) hα
    (by omega) (by rw [Fintype.card_fin]; omega) (by norm_num) he_eta α u).resolve_left hnot_unw
  have _h_m_lt : ((#(Finset.univ.filter fun z : Fin 2 → GaloisField 11 14 => ∃ c ∈ reedSolomon α 1,
      hammingDist (α + ∑ j : Fin 2, z j • u j) c ≤ 5) : ℝ) /
      ((Fintype.card (GaloisField 11 14) : ℝ) ^ 2)) < 1 := by
    refine hgap_m.trans_lt ?_
    rw [Fintype.card_fin, hcard]; norm_num
  refine ⟨hgap_eta.trans_lt (by rw [Fintype.card_fin, hcard]; norm_num), ?_, ?_⟩
  · -- `weighted_proximityGap_affine_johnson` (`B_W = 8`, `M = 2`).
    have hnotW : ¬ (∀ z : Fin 2 → GaloisField 11 14, ∃ c ∈ reedSolomon α 1,
        8 ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (α + ∑ j : Fin 2, z j • u j) i = c i), wJ9 i) := by
      intro hall
      obtain ⟨c, hcRS, hge⟩ := hall 0
      rw [haff0] at hge
      have hle1 := card_agree_inj_rs1_le_one hα hcRS
      have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => α i = c i), wJ9 i ≤
          (Finset.univ.filter fun i => α i = c i).card * 2 := by
        calc ∑ i ∈ Finset.univ.filter (fun i => α i = c i), wJ9 i
            ≤ ∑ _i ∈ Finset.univ.filter (fun i => α i = c i), 2 :=
              Finset.sum_le_sum fun i _ => hW_le i
          _ = (Finset.univ.filter fun i => α i = c i).card * 2 := by
              rw [Finset.sum_const, smul_eq_mul]
      omega
    have hB : ((Fintype.card (Fin 9) - (8 + 2 - 1) / 2 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
        1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
          Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
      rw [Fintype.card_fin]; norm_num [hsq]
    have hgapW := (weighted_proximityGap_affine_johnson (k := 1) (m := 2) (ℓ := 2) (M := 2)
      (B_W := 8) hα (by omega) (by rw [Fintype.card_fin]; omega) (by omega) (by omega) hW_le hB
      α u).resolve_left hnotW
    exact hgapW.trans_lt (by rw [Fintype.card_fin, hcard]; norm_num)
  · -- `ratWeighted_proximityGap_affine_johnson` (`θ = 4`, `M = 2`).
    have hnotμ : ¬ (∀ z : Fin 2 → GaloisField 11 14, ∃ c ∈ reedSolomon α 1,
        (4 : ℚ) ≤ ∑ i ∈ Finset.univ.filter
          (fun i => (α + ∑ j : Fin 2, z j • u j) i = c i), muJ9 i) := by
      intro hall
      obtain ⟨c, hcRS, hge⟩ := hall 0
      rw [haff0] at hge
      have hle1 := card_agree_inj_rs1_le_one hα hcRS
      have hsum_le : ∑ i ∈ Finset.univ.filter (fun i => α i = c i), muJ9 i ≤
          ((Finset.univ.filter fun i => α i = c i).card : ℚ) := by
        calc ∑ i ∈ Finset.univ.filter (fun i => α i = c i), muJ9 i
            ≤ ∑ _i ∈ Finset.univ.filter (fun i => α i = c i), (1 : ℚ) :=
              Finset.sum_le_sum fun i _ => hμ_le i
          _ = ((Finset.univ.filter fun i => α i = c i).card : ℚ) := by
              rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      have hle1Q : ((Finset.univ.filter fun i => α i = c i).card : ℚ) ≤ 1 := by exact_mod_cast hle1
      linarith
    have hθ : 1 - ((4 : ℚ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
        1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
          Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
      rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
    have hgapμ := (ratWeighted_proximityGap_affine_johnson (k := 1) (m := 2) (ℓ := 2) (M := 2)
      (θ := 4) hα (by omega) (by rw [Fintype.card_fin]; omega) (by omega) (by omega) hμ_le hμ_den
      hθ α u).resolve_left hnotμ
    exact hgapμ.trans_lt (by rw [Fintype.card_fin, hcard]; norm_num)

/-- Corrupted words on `Fin 9` over `GaloisField 11 14` agreeing with the constant `c` on
`{0, 1, 2, 3, 4}` (distance `4 ≤ 5`, `wJ9`-weight `10 ≥ 8`, `muJ9`-weight `5 ≥ 4`) and with `α`
on `{5, 6, 7, 8}` (`∉ reedSolomon α 1` for `c ≠ 5`). -/
private noncomputable def cor9 (c : ZMod 11) : Fin 9 → GaloisField 11 14 :=
  fun i => if i.val < 5 then algebraMap (ZMod 11) (GaloisField 11 14) c
    else algebraMap (ZMod 11) (GaloisField 11 14) (i.val : ZMod 11)

private theorem cor9_not_mem_rs1 {c : ZMod 11} (hc5 : c ≠ 5) :
    cor9 c ∉ reedSolomon
      (fun i : Fin 9 => algebraMap (ZMod 11) (GaloisField 11 14) (i.val : ZMod 11)) 1 := by
  intro hmem
  obtain ⟨a, ha⟩ := eq_const_of_mem_rs1 hmem
  have h0 : algebraMap (ZMod 11) (GaloisField 11 14) c = a := by
    simpa only [cor9, Fin.val_zero, show 0 < 5 by decide, ↓reduceIte] using ha 0
  have h5 : algebraMap (ZMod 11) (GaloisField 11 14) 5 = a := by
    simpa only [cor9, show (5 : Fin 9).val = 5 from rfl, show ¬ (5 < 5) by decide,
      ↓reduceIte, Nat.cast_ofNat] using ha 5
  exact hc5 ((algebraMap (ZMod 11) (GaloisField 11 14)).injective (h0.trans h5.symm))

/-- Closed-form beyond-unique-decoding (`n = 9`, `k = 1`, `e = 5 > 4`, `m = 2`, `η = 1 / 9`)
2D affine correlated agreement over `GaloisField 11 14` on a proper subset `T = univ.erase 0`
with three corrupted words `cor9 1, cor9 2, cor9 3 ∉ reedSolomon α 1`: exercises all six
closed-form correlated-agreement theorems
(`exists_correlatedAgreement_affine_johnson_of_multiplicity`, `..._of_eta`,
`exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity`, `..._of_eta`,
`exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity`, `..._of_eta`). -/
theorem test_correlatedAgreement_affine_johnson_closed_form_gf11_14 :
    open scoped Classical in
    let α : Fin 9 → GaloisField 11 14 :=
      fun i => algebraMap (ZMod 11) (GaloisField 11 14) (i.val : ZMod 11)
    let u₀ : Fin 9 → GaloisField 11 14 := cor9 1
    let u : Fin 2 → (Fin 9 → GaloisField 11 14) := ![cor9 2, cor9 3]
    u₀ ∉ reedSolomon α 1 ∧ u 0 ∉ reedSolomon α 1 ∧ u 1 ∉ reedSolomon α 1 ∧
    (∃ D' : Finset (Fin 9), 4 ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α 1, ∃ v : Fin 2 → (Fin 9 → GaloisField 11 14),
        (∀ j, v j ∈ reedSolomon α 1) ∧ ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) ∧
    (∃ D' : Finset (Fin 9), 4 ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon α 1, ∃ v : Fin 2 → (Fin 9 → GaloisField 11 14),
        (∀ j, v j ∈ reedSolomon α 1) ∧ ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) ∧
    (∃ D' : Finset (Fin 9), 8 ≤ ∑ i ∈ D', wJ9 i ∧
      ∃ v₀ ∈ reedSolomon α 1, ∃ v : Fin 2 → (Fin 9 → GaloisField 11 14),
        (∀ j, v j ∈ reedSolomon α 1) ∧ ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) ∧
    (∃ D' : Finset (Fin 9), 8 ≤ ∑ i ∈ D', wJ9 i ∧
      ∃ v₀ ∈ reedSolomon α 1, ∃ v : Fin 2 → (Fin 9 → GaloisField 11 14),
        (∀ j, v j ∈ reedSolomon α 1) ∧ ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) ∧
    (∃ D' : Finset (Fin 9), (4 : ℚ) ≤ ∑ i ∈ D', muJ9 i ∧
      ∃ v₀ ∈ reedSolomon α 1, ∃ v : Fin 2 → (Fin 9 → GaloisField 11 14),
        (∀ j, v j ∈ reedSolomon α 1) ∧ ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) ∧
    (∃ D' : Finset (Fin 9), (4 : ℚ) ≤ ∑ i ∈ D', muJ9 i ∧
      ∃ v₀ ∈ reedSolomon α 1, ∃ v : Fin 2 → (Fin 9 → GaloisField 11 14),
        (∀ j, v j ∈ reedSolomon α 1) ∧ ∀ i ∈ D', u₀ i = v₀ i ∧ ∀ j, u j i = v j i) := by
  classical
  intro α u₀ u
  have hcard : Fintype.card (GaloisField 11 14) = 11 ^ 14 :=
    (Nat.card_eq_fintype_card (α := GaloisField 11 14)).symm.trans
      (GaloisField.card 11 14 (by omega))
  have hα : Function.Injective α := by
    intro i j h
    have h1 : (i.val : ZMod 11) = (j.val : ZMod 11) :=
      (algebraMap (ZMod 11) (GaloisField 11 14)).injective h
    have hv := congrArg ZMod.val h1
    rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv
    exact Fin.ext hv
  have hsq : Real.sqrt ((1 : ℝ) / 9) = 1 / 3 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]; norm_num
  have he_m2 : ((5 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
        Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
    rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
  have he_eta : ((5 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) - (1 / 9 : ℝ) := by
    rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
  have hB_m2 : ((Fintype.card (Fin 9) - (8 + 2 - 1) / 2 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
        Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
    rw [Fintype.card_fin]; norm_num [hsq]
  have hB_eta : ((Fintype.card (Fin 9) - (8 + 2 - 1) / 2 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) - (1 / 9 : ℝ) := by
    rw [Fintype.card_fin]; norm_num [hsq]
  have hθ_m2 : 1 - ((4 : ℚ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) -
        Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) / (2 * ((2 : ℕ) : ℝ)) := by
    rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
  have hθ_eta : 1 - ((4 : ℚ) : ℝ) / (Fintype.card (Fin 9) : ℝ) ≤
      1 - Real.sqrt (((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) - (1 / 9 : ℝ) := by
    rw [Fintype.card_fin]; push_cast; rw [hsq]; norm_num
  have hW_le : ∀ i : Fin 9, wJ9 i ≤ 2 := by intro i; fin_cases i <;> decide
  have hμ_le : ∀ i : Fin 9, muJ9 i ≤ 1 := by intro i; fin_cases i <;> norm_num [muJ9]
  have hμ_nn : ∀ i : Fin 9, 0 ≤ muJ9 i := by intro i; fin_cases i <;> norm_num [muJ9]
  have hμ_den : ∀ i : Fin 9, ∃ a : ℕ, muJ9 i = (a : ℚ) / (2 : ℕ) := by
    intro i; fin_cases i
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨2, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨1, by norm_num [muJ9]⟩
    · exact ⟨0, by norm_num [muJ9]⟩
  have hconst_mem : ∀ c : GaloisField 11 14, (fun _ : Fin 9 => c) ∈ reedSolomon α 1 := fun c =>
    mem_reedSolomon.2 ⟨C c, degree_C_le.trans_lt (Nat.cast_lt.2 (by decide)),
      funext fun _ => eval_C⟩
  let v₀True : Fin 9 → GaloisField 11 14 := fun _ => algebraMap (ZMod 11) (GaloisField 11 14) 1
  let vTrue : Fin 2 → (Fin 9 → GaloisField 11 14) :=
    ![fun _ => algebraMap (ZMod 11) (GaloisField 11 14) 2,
      fun _ => algebraMap (ZMod 11) (GaloisField 11 14) 3]
  have hvTrue : ∀ j : Fin 2, vTrue j ∈ reedSolomon α 1 := by
    intro j; fin_cases j <;> exact hconst_mem _
  let S5 : Finset (Fin 9) := {0, 1, 2, 3, 4}
  have hagree5 : ∀ i ∈ S5, u₀ i = v₀True i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hlt5 : i.val < 5 := by fin_cases hi <;> decide
    refine ⟨by simp only [u₀, cor9, hlt5, ↓reduceIte, v₀True], fun j => ?_⟩
    fin_cases j
    · change cor9 2 i = vTrue 0 i; simp only [cor9, hlt5, ↓reduceIte, vTrue, Matrix.cons_val_zero]
    · change cor9 3 i = vTrue 1 i; simp only [cor9, hlt5, ↓reduceIte, vTrue, Matrix.cons_val_one,
        Matrix.cons_val_zero]
  have hW_S5 : (8 : ℕ) ≤ ∑ i ∈ S5, wJ9 i := by decide
  have hμ_S5 : (4 : ℚ) ≤ ∑ i ∈ S5, muJ9 i := by
    have hS5 : S5 = {0, 1, 2, 3, 4} := rfl
    norm_num [hS5, muJ9]
  let T : Finset (Fin 2 → GaloisField 11 14) := Finset.univ.erase 0
  have hT_card : T.card = (11 ^ 14) ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, hcard]
  have hclose_unw : ∀ z ∈ T, ∃ c ∈ reedSolomon α 1,
      hammingDist (u₀ + ∑ j : Fin 2, z j • u j) c ≤ 5 := fun z _ =>
    ⟨v₀True + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ (hconst_mem _)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hammingDist_affine_le_of_eq_on (D' := S5) (by decide) hagree5 z⟩
  have hclose_w : ∀ z ∈ T, ∃ c ∈ reedSolomon α 1,
      8 ≤ ∑ i ∈ Finset.univ.filter (fun i => (u₀ + ∑ j : Fin 2, z j • u j) i = c i), wJ9 i :=
    fun z _ => ⟨v₀True + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ (hconst_mem _)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hW_S5.trans (weightedAgree_affine_ge_of_eq_on wJ9 hagree5 z)⟩
  have hclose_μ : ∀ z ∈ T, ∃ c ∈ reedSolomon α 1,
      (4 : ℚ) ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u₀ + ∑ j : Fin 2, z j • u j) i = c i), muJ9 i :=
    fun z _ => ⟨v₀True + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ (hconst_mem _)
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue j)),
      hμ_S5.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nn hagree5 z)⟩
  have hT_big : 115200 * (2 : ℝ) * ((Fintype.card (Fin 9) : ℝ) ^ 2) /
      ((((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) * ((1 / 9 : ℝ) ^ 6) *
        (Fintype.card (GaloisField 11 14) : ℝ)) <
      (T.card : ℝ) / ((Fintype.card (GaloisField 11 14) : ℝ) ^ 2) := by
    rw [Fintype.card_fin, hcard, hT_card, Nat.cast_sub (by norm_num)]
    norm_num
  have hT_unw_m : 1800 * ((2 + 1 : ℝ) ^ 6) * ((Fintype.card (Fin 9) : ℝ) ^ 2) /
      ((((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) * (Fintype.card (GaloisField 11 14) : ℝ)) <
      (T.card : ℝ) / ((Fintype.card (GaloisField 11 14) : ℝ) ^ 2) := by
    refine lt_of_le_of_lt ?_ hT_big
    rw [Fintype.card_fin, hcard]; norm_num
  have hT_unw_eta : 115200 * ((Fintype.card (Fin 9) : ℝ) ^ 2) /
      ((((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) * ((1 / 9 : ℝ) ^ 6) *
        (Fintype.card (GaloisField 11 14) : ℝ)) <
      (T.card : ℝ) / ((Fintype.card (GaloisField 11 14) : ℝ) ^ 2) := by
    refine lt_of_le_of_lt ?_ hT_big
    rw [Fintype.card_fin, hcard]; norm_num
  have hT_w_m : 1800 * ((2 : ℕ) : ℝ) * ((2 + 1 : ℝ) ^ 6) * ((Fintype.card (Fin 9) : ℝ) ^ 2) /
      ((((1 : ℕ) : ℝ) / (Fintype.card (Fin 9) : ℝ)) * (Fintype.card (GaloisField 11 14) : ℝ)) <
      (T.card : ℝ) / ((Fintype.card (GaloisField 11 14) : ℝ) ^ 2) := by
    refine lt_of_le_of_lt ?_ hT_big
    rw [Fintype.card_fin, hcard]; norm_num
  have hkn9 : 1 ≤ Fintype.card (Fin 9) := by rw [Fintype.card_fin]; omega
  refine ⟨cor9_not_mem_rs1 (by decide), cor9_not_mem_rs1 (by decide), cor9_not_mem_rs1 (by decide),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
      exists_correlatedAgreement_affine_johnson_of_multiplicity (e := 5) (k := 1) (m := 2) (ℓ := 2)
        hα le_rfl hkn9 (by omega) he_m2 u₀ u T hT_unw_m hclose_unw
    exact ⟨D', by simpa only [Fintype.card_fin] using hD', v₀, hv₀, v, hvRS, hagree⟩
  · obtain ⟨D', hD', v₀, hv₀, v, hvRS, hagree⟩ :=
      exists_correlatedAgreement_affine_johnson_of_eta (e := 5) (k := 1) (ℓ := 2) (η := 1 / 9)
        hα le_rfl hkn9 (by norm_num) he_eta u₀ u T hT_unw_eta hclose_unw
    exact ⟨D', by simpa only [Fintype.card_fin] using hD', v₀, hv₀, v, hvRS, hagree⟩
  · exact exists_weighted_correlatedAgreement_affine_johnson_of_multiplicity (k := 1) (m := 2)
      (ℓ := 2) (M := 2) (B_W := 8) hα le_rfl hkn9 (by omega) (by omega) hW_le hB_m2 u₀ u T hT_w_m
      hclose_w
  · exact exists_weighted_correlatedAgreement_affine_johnson_of_eta (k := 1) (ℓ := 2) (M := 2)
      (B_W := 8) (η := 1 / 9) hα le_rfl hkn9 (by omega) (by norm_num) hW_le hB_eta u₀ u T hT_big
      hclose_w
  · exact exists_ratWeighted_correlatedAgreement_affine_johnson_of_multiplicity (k := 1) (m := 2)
      (ℓ := 2) (M := 2) (θ := 4) hα le_rfl hkn9 (by omega) (by omega) hμ_le hμ_den hθ_m2 u₀ u T
      hT_w_m hclose_μ
  · exact exists_ratWeighted_correlatedAgreement_affine_johnson_of_eta (k := 1) (ℓ := 2) (M := 2)
      (θ := 4) (η := 1 / 9) hα le_rfl hkn9 (by omega) (by norm_num) hμ_le hμ_den hθ_eta u₀ u T
      hT_big hclose_μ

end RealAsymptoticJohnsonTests

/-! ### Test 10: Exact eq. (1.2) Theorem 1.6 uniqueness & maximality and sharpness counterexample -/

/-- Positive exact-threshold 2D affine space uniqueness-clause test over `ZMod 11` (`n = 5`,
`k = 3`, `e = 1`) on `T56 = insert ![5, 0] (strip2D 11 5)` of size `56`:
`5 * 11 ^ 2 = 605 < 616 = 11 * 56` clears Theorem 1.6's exact eq. (1.2) threshold while falling
strictly below the weighted cutoff (`10 * 56 = 560 ≤ 600 = 5 * (11 ^ 2 - 1)`). Pins the exact
unique maximal set `Finset.univ.erase 0`, exact codewords `(v0 11, ![v1 11, v2 11])`, and the
literal `∃!` maximal-set consequence. -/
theorem test_uniqueMaximal_correlatedAgreement_affine_unique_exact :
    u0 11 ∉ reedSolomon (pts5 11) 3 ∧
    u1 11 ∉ reedSolomon (pts5 11) 3 ∧
    u2 11 ∉ reedSolomon (pts5 11) 3 ∧
    (∃! D' : Finset (Fin 5),
      (4 ≤ D'.card ∧ ∃ v₀ ∈ reedSolomon (pts5 11) 3, ∃ v : Fin 2 → (Fin 5 → ZMod 11),
        (∀ j, v j ∈ reedSolomon (pts5 11) 3) ∧
        ∀ i ∈ D', u0 11 i = v₀ i ∧ ∀ j, (![u1 11, u2 11] j) i = v j i) ∧
      ∀ D₂ : Finset (Fin 5),
        (4 ≤ D₂.card ∧ ∃ w₀ ∈ reedSolomon (pts5 11) 3, ∃ w : Fin 2 → (Fin 5 → ZMod 11),
          (∀ j, w j ∈ reedSolomon (pts5 11) 3) ∧
          ∀ i ∈ D₂, u0 11 i = w₀ i ∧ ∀ j, (![u1 11, u2 11] j) i = w j i) →
        D' ⊆ D₂ → D₂ = D') ∧
    ∀ (D'' : Finset (Fin 5)) (w₀ : Fin 5 → ZMod 11) (w : Fin 2 → (Fin 5 → ZMod 11)),
      4 ≤ D''.card → w₀ ∈ reedSolomon (pts5 11) 3 → (∀ j, w j ∈ reedSolomon (pts5 11) 3) →
      (∀ i ∈ D'', u0 11 i = w₀ i ∧ ∀ j, (![u1 11, u2 11] j) i = w j i) →
      D'' ⊆ Finset.univ.erase 0 ∧ w₀ = v0 11 ∧ w = ![v1 11, v2 11] := by
  let u : Fin 2 → (Fin 5 → ZMod 11) := ![u1 11, u2 11]
  let vTrue : Fin 2 → (Fin 5 → ZMod 11) := ![v1 11, v2 11]
  have hvTrue_mem : ∀ j : Fin 2, vTrue j ∈ reedSolomon (pts5 11) 3 := by
    intro j; fin_cases j
    · exact v1_mem_rs
    · exact v2_mem_rs
  have hagree_true : ∀ i ∈ Finset.univ.erase (0 : Fin 5),
      u0 11 i = v0 11 i ∧ ∀ j : Fin 2, u j i = vTrue j i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    refine ⟨by simp only [u0, hne, ↓reduceIte], fun j => ?_⟩
    fin_cases j
    · change u1 11 i = v1 11 i; simp only [u1, hne, ↓reduceIte]
    · change u2 11 i = v2 11 i; simp only [u2, v2, hne, ↓reduceIte]
  let z50 : Fin 2 → ZMod 11 := ![5, 0]
  let T56 : Finset (Fin 2 → ZMod 11) := insert z50 (strip2D 11 5)
  have hz50_not : z50 ∉ strip2D 11 5 := by
    intro hmem
    have hlt : (z50 0).val < 5 := (mem_filter.1 hmem).2
    have hv : (z50 0).val = 5 := by decide
    omega
  have hT56_card : T56.card = 56 := by
    rw [Finset.card_insert_of_notMem hz50_not, strip2D_card (by omega)]
  have hT56_lt : Fintype.card (Fin 5) * (Fintype.card (ZMod 11)) ^ 2 <
      Fintype.card (ZMod 11) * T56.card := by
    rw [Fintype.card_fin, ZMod.card, hT56_card]; norm_num
  have hclose : ∀ z ∈ T56, ∃ c ∈ reedSolomon (pts5 11) 3,
      hammingDist (u0 11 + ∑ j : Fin 2, z j • u j) c ≤ 1 := fun z _ =>
    ⟨v0 11 + ∑ j : Fin 2, z j • vTrue j,
      Submodule.add_mem _ v0_mem_rs
        (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j)),
      hammingDist_affine_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hagree_true z⟩
  obtain ⟨D', _, v₀, _, v, _, hagree, hmax⟩ :=
    exists_uniqueMaximal_correlatedAgreement_affine_unique (ℓ := 2) pts5_11_injective
      (e := 1) (k := 3) (by decide) (u0 11) u T56 hT56_lt hclose
  obtain ⟨her_sub, hv₀_eq, hv_eq⟩ :=
    hmax (Finset.univ.erase 0) (v0 11) vTrue (by decide) v0_mem_rs hvTrue_mem hagree_true
  subst hv₀_eq hv_eq
  have hD'_eq : D' = Finset.univ.erase 0 := by
    refine Finset.Subset.antisymm (fun i hi => mem_erase.2 ⟨?_, mem_univ i⟩) her_sub
    rintro rfl
    have h0 := (hagree 0 hi).1
    simp only [u0, ↓reduceIte, add_eq_left] at h0
    exact one_ne_zero h0
  subst hD'_eq
  refine ⟨u0_not_mem_rs_11, u1_not_mem_rs_11, u2_not_mem_rs_11, ?_, ?_⟩
  · refine ⟨Finset.univ.erase 0, ⟨⟨by decide, v0 11, v0_mem_rs, vTrue, hvTrue_mem, hagree_true⟩,
      fun D₂ hD₂ hsub => ?_⟩, fun D₁ hD₁ => ?_⟩
    · obtain ⟨hcard₂, w₀, hw₀, w, hw, hag₂⟩ := hD₂
      exact Finset.Subset.antisymm (hmax D₂ w₀ w (by simpa only [Fintype.card_fin] using hcard₂)
        hw₀ hw hag₂).1 hsub
    · obtain ⟨⟨hcard₁, w₀, hw₀, w, hw, hag₁⟩, hmax₁⟩ := hD₁
      have hsub := (hmax D₁ w₀ w (by simpa only [Fintype.card_fin] using hcard₁)
        hw₀ hw hag₁).1
      exact (hmax₁ (Finset.univ.erase 0)
        ⟨by decide, v0 11, v0_mem_rs, vTrue, hvTrue_mem, hagree_true⟩ hsub).symm
  · intro D'' w₀ w hD'' hw₀ hw hag''
    exact hmax D'' w₀ w (by simpa only [Fintype.card_fin] using hD'') hw₀ hw hag''

/-- Upper-bound regression for `proximityGap_affine_unique` over `ZMod 11`: proves the close
parameter set has cardinality at most `55` of `121` points (`11 * #T ≤ 5 * 121 = 605`). A separate
finite enumeration of this quadratic code over `ZMod 11` gives `44` close parameter pairs in this
fixture. -/
theorem test_proximityGap_affine_unique_upper_bound_regression :
    open scoped Classical in
    (Finset.univ.filter fun z : Fin 2 → ZMod 11 => ∃ c ∈ reedSolomon (pts5 11) 3,
      hammingDist (spike0 11 + ∑ j : Fin 2, z j • (![spike1 11, (0 : Fin 5 → ZMod 11)] j)) c ≤
        1).card ≤ 55 := by
  classical
  set u : Fin 2 → (Fin 5 → ZMod 11) := ![spike1 11, 0]
  rcases proximityGap_affine_unique (ℓ := 2) pts5_11_injective (e := 1) (k := 3) (by decide)
      (spike0 11) u with hall | hcard
  · obtain ⟨c, hcRS, hdist⟩ := hall ![1, 0]
    have hsum1 : (spike0 11 + ∑ j : Fin 2, (![(1 : ZMod 11), 0] j) • u j) =
        spike0 11 + (1 : ZMod 11) • spike1 11 := by
      rw [Fin.sum_univ_two]
      change spike0 11 + ((1 : ZMod 11) • spike1 11 + (0 : ZMod 11) • (0 : Fin 5 → ZMod 11)) =
        spike0 11 + (1 : ZMod 11) • spike1 11
      simp only [zero_smul, add_zero]
    rw [hsum1] at hdist
    exact absurd hdist (not_le.2 (spike_far_at_one (p := 11) (by decide) (by decide) c hcRS))
  · rw [Fintype.card_fin, ZMod.card] at hcard
    omega

/-- One-point (`ℓ = 0`) regression exercising both `n = q` over `ZMod 5` (for the weighted
`*_affine_unique_sharp` theorems, where `(q - 1) * #T = 4 > 0 = n * (q ^ 0 - 1)`) and `n < q` over
`ZMod 11` (for `exists_uniqueMaximal_correlatedAgreement_affine_unique` at
`5 * 11 ^ 0 < 11 * 1`). -/
theorem test_affine_unique_zero_dim :
    u0 5 ∉ reedSolomon (pts5 5) 3 ∧
    (∃ D' : Finset (Fin 5), (7 : ℚ) / 2 ≤ ∑ i ∈ D', muNonConst i ∧
      ∃ v₀ ∈ reedSolomon (pts5 5) 3, ∀ i ∈ D', u0 5 i = v₀ i) ∧
    (∃ D' : Finset (Fin 5), 7 ≤ ∑ i ∈ D', wNonConst i ∧
      ∃ v₀ ∈ reedSolomon (pts5 5) 3, ∀ i ∈ D', u0 5 i = v₀ i) ∧
    (∃ D' : Finset (Fin 5), 4 ≤ D'.card ∧
      ∃ v₀ ∈ reedSolomon (pts5 11) 3,
        (∀ i ∈ D', u0 11 i = v₀ i) ∧
        ∀ (D'' : Finset (Fin 5)) (w₀ : Fin 5 → ZMod 11),
          4 ≤ D''.card → w₀ ∈ reedSolomon (pts5 11) 3 →
          (∀ i ∈ D'', u0 11 i = w₀ i) → D'' ⊆ D' ∧ w₀ = v₀) := by
  let u5 : Fin 0 → (Fin 5 → ZMod 5) := Fin.elim0
  let u11 : Fin 0 → (Fin 5 → ZMod 11) := Fin.elim0
  have hu0_5_not : u0 5 ∉ reedSolomon (pts5 5) 3 := by
    intro hmem
    have hdiff := third_diff_zero_of_mem_rs hmem
    have hval : u0 5 0 - 3 * u0 5 1 + 3 * u0 5 2 - u0 5 3 = 1 := by
      simp only [u0, v0, pts5, eval_add, eval_one, eval_pow, eval_X]; decide
    rw [hval] at hdiff
    exact one_ne_zero hdiff
  have hag5 : ∀ i ∈ Finset.univ.erase (0 : Fin 5),
      u0 5 i = v0 5 i ∧ ∀ j : Fin 0, u5 j i = u5 j i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    exact ⟨by simp only [u0, hne, ↓reduceIte], fun j => Fin.elim0 j⟩
  have hT5 : Fintype.card (Fin 5) * ((Fintype.card (ZMod 5)) ^ 0 - 1) <
      (Fintype.card (ZMod 5) - 1) * (Finset.univ : Finset (Fin 0 → ZMod 5)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    norm_num
  have hμ_nonneg : ∀ i : Fin 5, 0 ≤ muNonConst i := by
    intro i; fin_cases i <;> norm_num [muNonConst]
  have hμ_le : ∀ i : Fin 5, muNonConst i ≤ 1 := by
    intro i; fin_cases i <;> norm_num [muNonConst]
  have hθ : ((Fintype.card (Fin 5) - 1 : ℕ) : ℚ) - 1 < (7 : ℚ) / 2 := by
    rw [Fintype.card_fin]; norm_num
  have hclose_μ5 : ∀ z ∈ (Finset.univ : Finset (Fin 0 → ZMod 5)), ∃ c ∈ reedSolomon (pts5 5) 3,
      (7 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u0 5 + ∑ j : Fin 0, z j • u5 j) i = c i), muNonConst i := by
    intro z _
    refine ⟨v0 5, v0_mem_rs, ?_⟩
    have hD : (7 : ℚ) / 2 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 5), muNonConst i := by
      norm_num [Fin.sum_univ_five, Finset.sum_erase_eq_sub, muNonConst]
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] using
      hD.trans (ratWeightedAgree_affine_ge_of_eq_on hμ_nonneg hag5 z)
  obtain ⟨Dμ, hDμ, vμ, hvμ, _, _, hagμ⟩ :=
    exists_ratWeighted_correlatedAgreement_affine_unique_sharp (ℓ := 0) pts5_5_injective
      (e := 1) (k := 3) (by decide) hμ_le hθ (u0 5) u5 Finset.univ hT5 hclose_μ5
  have hW : ∀ i : Fin 5, wNonConst i ≤ 2 := by decide
  have hclose_W5 : ∀ z ∈ (Finset.univ : Finset (Fin 0 → ZMod 5)), ∃ c ∈ reedSolomon (pts5 5) 3,
      7 ≤ ∑ i ∈ Finset.univ.filter (fun i =>
        (u0 5 + ∑ j : Fin 0, z j • u5 j) i = c i), wNonConst i := by
    intro z _
    refine ⟨v0 5, v0_mem_rs, ?_⟩
    have hD : 7 ≤ ∑ i ∈ Finset.univ.erase (0 : Fin 5), wNonConst i := by decide
    simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] using
      hD.trans (weightedAgree_affine_ge_of_eq_on wNonConst hag5 z)
  obtain ⟨DW, hDW, vW, hvW, _, _, hagW⟩ :=
    exists_weighted_correlatedAgreement_affine_unique_sharp (ℓ := 0) pts5_5_injective
      (k := 3) (M := 2) (B := 7) (by decide) hW (by decide) (u0 5) u5 Finset.univ hT5 hclose_W5
  have hag11 : ∀ i ∈ Finset.univ.erase (0 : Fin 5),
      u0 11 i = v0 11 i ∧ ∀ j : Fin 0, u11 j i = u11 j i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    exact ⟨by simp only [u0, hne, ↓reduceIte], fun j => Fin.elim0 j⟩
  have hT11 : Fintype.card (Fin 5) * (Fintype.card (ZMod 11)) ^ 0 <
      Fintype.card (ZMod 11) * (Finset.univ : Finset (Fin 0 → ZMod 11)).card := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ZMod.card]
    norm_num
  have hclose11 : ∀ z ∈ (Finset.univ : Finset (Fin 0 → ZMod 11)), ∃ c ∈ reedSolomon (pts5 11) 3,
      hammingDist (u0 11 + ∑ j : Fin 0, z j • u11 j) c ≤ 1 := fun z _ =>
    ⟨v0 11 + ∑ j : Fin 0, z j • u11 j,
      by simpa only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] using v0_mem_rs,
      hammingDist_affine_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hag11 z⟩
  obtain ⟨D11, hD11, v11, hv11, _, _, hag11', hmax11⟩ :=
    exists_uniqueMaximal_correlatedAgreement_affine_unique (ℓ := 0) pts5_11_injective
      (e := 1) (k := 3) (by decide) (u0 11) u11 Finset.univ hT11 hclose11
  refine ⟨hu0_5_not, ⟨Dμ, hDμ, vμ, hvμ, fun i hi => (hagμ i hi).1⟩,
    ⟨DW, hDW, vW, hvW, fun i hi => (hagW i hi).1⟩,
    ⟨D11, by simpa only [Fintype.card_fin] using hD11, v11, hv11,
      fun i hi => (hag11' i hi).1, fun D'' w₀ hD'' hw₀ hag'' => ?_⟩⟩
  obtain ⟨hsub, hw₀_eq, _⟩ := hmax11 D'' w₀ u11 (by simpa only [Fintype.card_fin] using hD'')
    hw₀ (fun j => Fin.elim0 j) (fun i hi => ⟨hag'' i hi, fun j => Fin.elim0 j⟩)
  exact ⟨hsub, hw₀_eq⟩

/-- Sharpness counterexample just beyond the unique-decoding radius (`2 * e + k = n + 1` at
`n = 5`, `k = 2`, `e = 2` over `ZMod 11`): on the constant 2D affine space generated by
`u₀ = ![0, 0, 0, 3, 4]` and `u = ![0, 0]`, every affine point lies within distance `2` of
`reedSolomon (pts5 11) 2`, yet `D₁ = {0, 1, 2}` (with `c₁ = 0`) and `D₂ = {0, 3, 4}` (with
`c₂ = pts5 11`) are two **distinct maximal** qualifying agreement sets with distinct codewords,
showing `2 * e + k ≤ n` is sharp for Theorem 1.6's uniqueness clause. -/
theorem test_uniqueMaximal_fails_beyond_unique_decoding :
    let u₀ : Fin 5 → ZMod 11 := ![0, 0, 0, 3, 4]
    let u : Fin 2 → (Fin 5 → ZMod 11) := ![0, 0]
    let c₁ : Fin 5 → ZMod 11 := 0
    let c₂ : Fin 5 → ZMod 11 := pts5 11
    let D₁ : Finset (Fin 5) := {0, 1, 2}
    let D₂ : Finset (Fin 5) := {0, 3, 4}
    D₁ ≠ D₂ ∧ c₁ ≠ c₂ ∧
    (∀ z : Fin 2 → ZMod 11, ∃ c ∈ reedSolomon (pts5 11) 2,
      hammingDist (u₀ + ∑ j : Fin 2, z j • u j) c ≤ 2) ∧
    (3 ≤ D₁.card ∧ c₁ ∈ reedSolomon (pts5 11) 2 ∧
      (∀ i ∈ D₁, u₀ i = c₁ i ∧ ∀ j, u j i = (0 : Fin 5 → ZMod 11) i) ∧
      ∀ (D' : Finset (Fin 5)) (w₀ : Fin 5 → ZMod 11),
        w₀ ∈ reedSolomon (pts5 11) 2 → (∀ i ∈ D', u₀ i = w₀ i) → D₁ ⊆ D' → D' = D₁) ∧
    (3 ≤ D₂.card ∧ c₂ ∈ reedSolomon (pts5 11) 2 ∧
      (∀ i ∈ D₂, u₀ i = c₂ i ∧ ∀ j, u j i = (0 : Fin 5 → ZMod 11) i) ∧
      ∀ (D' : Finset (Fin 5)) (w₀ : Fin 5 → ZMod 11),
        w₀ ∈ reedSolomon (pts5 11) 2 → (∀ i ∈ D', u₀ i = w₀ i) → D₂ ⊆ D' → D' = D₂) := by
  intro u₀ u c₁ c₂ D₁ D₂
  have hc₁_mem : c₁ ∈ reedSolomon (pts5 11) 2 := Submodule.zero_mem _
  have hc₂_mem : c₂ ∈ reedSolomon (pts5 11) 2 :=
    mem_reedSolomon.2 ⟨X, by rw [degree_X]; exact Nat.cast_lt.2 (by decide), funext fun _ => eval_X⟩
  have huniq_k2 : ∀ {w c : Fin 5 → ZMod 11} {D : Finset (Fin 5)},
      w ∈ reedSolomon (pts5 11) 2 → c ∈ reedSolomon (pts5 11) 2 →
      2 ≤ D.card → (∀ i ∈ D, w i = c i) → w = c := by
    intro w c D hw hc hD hag
    by_contra hne
    have hnorm := le_hammingNorm_of_mem_reedSolomon pts5_11_injective
      (Submodule.sub_mem _ hw hc) (sub_ne_zero.2 hne)
    have hsub : D ⊆ Finset.univ.filter fun i => w i = c i :=
      fun i hi => mem_filter.2 ⟨mem_univ i, hag i hi⟩
    have htot := card_agree_add_hammingDist w c
    have hdist : hammingDist w c = hammingNorm (w - c) := by
      rw [hammingDist_comm, hammingDist_eq_hammingNorm, neg_add_eq_sub]
    have hle := Finset.card_le_card hsub
    simp only [Fintype.card_fin] at hnorm
    omega
  have hag₁ : ∀ i ∈ D₁, u₀ i = c₁ i ∧ ∀ j : Fin 2, u j i = (0 : Fin 5 → ZMod 11) i := by
    intro i hi
    refine ⟨by revert i hi; decide, fun j => by fin_cases j <;> rfl⟩
  have hag₂ : ∀ i ∈ D₂, u₀ i = c₂ i ∧ ∀ j : Fin 2, u j i = (0 : Fin 5 → ZMod 11) i := by
    intro i hi
    refine ⟨by revert i hi; decide, fun j => by fin_cases j <;> rfl⟩
  refine ⟨by decide, fun h => by
      have h1 : c₁ 1 = c₂ 1 := congrFun h 1
      revert h1; decide,
    fun z => ⟨c₁ + ∑ j : Fin 2, z j • (0 : Fin 5 → ZMod 11),
      Submodule.add_mem _ hc₁_mem
        (Submodule.sum_mem _ fun _ _ => Submodule.smul_mem _ _ (Submodule.zero_mem _)),
      hammingDist_affine_le_of_eq_on (D' := D₁) (by decide) hag₁ z⟩,
    ⟨by decide, hc₁_mem, hag₁, fun D' w₀ hw₀ hag' hsub => ?_⟩,
    ⟨by decide, hc₂_mem, hag₂, fun D' w₀ hw₀ hag' hsub => ?_⟩⟩
  · have hw₀_eq : w₀ = c₁ := huniq_k2 hw₀ hc₁_mem (by decide : 2 ≤ D₁.card) fun i hi =>
      (hag' i (hsub hi)).symm.trans (hag₁ i hi).1
    subst hw₀_eq
    exact Finset.Subset.antisymm
      (fun i hi => (by decide : ∀ j : Fin 5, u₀ j = c₁ j → j ∈ D₁) i (hag' i hi)) hsub
  · have hw₀_eq : w₀ = c₂ := huniq_k2 hw₀ hc₂_mem (by decide : 2 ≤ D₂.card) fun i hi =>
      (hag' i (hsub hi)).symm.trans (hag₂ i hi).1
    subst hw₀_eq
    exact Finset.Subset.antisymm
      (fun i hi => (by decide : ∀ j : Fin 5, u₀ j = c₂ j → j ∈ D₂) i (hag' i hi)) hsub

end CslibFrontierTests.Foundations.Data.Code.ProximityGap.Curve
