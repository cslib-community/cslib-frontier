/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

import CslibFrontier.Foundations.Data.Code.ProximityGap.Unique
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Tests for unique-decoding proximity gaps for Reed–Solomon codes

Exercises `CslibFrontier.Foundations.Data.Code.ProximityGap.Unique` via ordinary `module`
imports on concrete finite-field Reed–Solomon instances over `ZMod 11` at length `n = 5`,
dimension `k = 3`, and tight unique-decoding radius `e = 1` (`2 * 1 + 3 = 5`):
1. **Nonzero-error correlated agreement on affine lines:** constructs corrupted words
   `u₀, u₁ ∉ reedSolomon points5 3` sharing a single error at coordinate `0`, verifies that `6 > 5`
   scalars lie within distance `1` of the code, applies `exists_correlatedAgreement_unique`, and
   verifies that the recovered codewords uniquely match the underlying polynomials.
2. **Negative / tightness dichotomy on affine lines:** constructs `u₀, u₁` with disjoint errors
   where `z = 0` is within distance `1` while `z = 1` is at distance `> 1` from every codeword,
   and applies `proximityGap_unique` to deduce that at most `5` scalars in `ZMod 11` are close.
3. **Parameterized curve (`d = 2`, three words):** constructs three corrupted words sharing a
   single error at coordinate `0` over `ZMod 11` (`d * n = 10 < 11 = |ZMod 11|`), and applies
   `exists_correlatedAgreement_curve_unique` and `proximityGap_curve_unique`.
4. **Uniqueness & maximality clauses (BCIKS20 Theorems 1.4 & 1.5):** instantiates
   `exists_uniqueMaximal_correlatedAgreement_unique` and
   `exists_uniqueMaximal_correlatedAgreement_curve_unique` on corrupted words `∉ RS`, pinning the
   exact unique maximal agreement set `Finset.univ.erase 0`, the exact unique codewords, and the
   literal `∃!` maximal-set consequence; plus a length-`7`, `k = 3`, `e = 2` (`2 * 2 + 3 = 7`)
   instance with 1-error words showing a valid non-maximal set `D'' = {2, 3, 4, 5, 6}` of size
   `5 = 7 - 2` strictly contained in the unique maximal set `Finset.univ.erase 0` of size `6`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.Data.Code.ProximityGap.Unique

open Cslib Cslib.Code Finset Polynomial

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Five distinct evaluation points `0, 1, 2, 3, 4` in `ZMod 11`. -/
private def points5 : Fin 5 → ZMod 11 := fun i => (i : ℕ)

private theorem points5_injective : Function.Injective points5 := by decide

/-- Helper: any polynomial of degree `< 3` over `ZMod 11` is determined by its first three
coefficients. -/
private theorem eval_eq_of_degree_lt_three {p : (ZMod 11)[X]} (hp : p.degree < (3 : ℕ))
    (x : ZMod 11) :
    p.eval x = p.coeff 0 + p.coeff 1 * x + p.coeff 2 * x ^ 2 := by
  have hdeg : p.natDegree < 3 := by
    by_cases hp0 : p = 0
    · rw [hp0, natDegree_zero]; decide
    · exact (natDegree_lt_iff_degree_lt hp0).2 hp
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [pow_zero, mul_one, pow_one]

/-- Helper: agreement count plus Hamming distance equals the block length. -/
private theorem card_agree_add_hammingDist {n : ℕ} (x y : Fin n → ZMod 11) :
    (Finset.univ.filter fun i => x i = y i).card + hammingDist x y = n := by
  rw [hammingDist, ← Finset.card_union_of_disjoint]
  · have hunion : (Finset.univ.filter fun i => x i = y i) ∪
        (Finset.univ.filter fun i => x i ≠ y i) = Finset.univ := by
      ext i; simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]; exact em _
    rw [hunion, Finset.card_univ, Fintype.card_fin]
  · exact Finset.disjoint_filter.2 fun _ _ h hne => hne h

/-- Helper: second finite difference of any polynomial of degree `< 3` evaluated at `0, 1, 2, 3`
satisfies `f(0) - 3 f(1) + 3 f(2) - f(3) = 0`. -/
private theorem third_diff_zero_of_mem_rs {c : Fin 5 → ZMod 11}
    (hc : c ∈ reedSolomon points5 3) :
    c 0 - 3 * c 1 + 3 * c 2 - c 3 = 0 := by
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hc
  simp only [eval_eq_of_degree_lt_three hp, points5, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  change (p.coeff 0 + p.coeff 1 * 0 + p.coeff 2 * 0 ^ 2) -
      3 * (p.coeff 0 + p.coeff 1 * 1 + p.coeff 2 * 1 ^ 2) +
      3 * (p.coeff 0 + p.coeff 1 * 2 + p.coeff 2 * 2 ^ 2) -
      (p.coeff 0 + p.coeff 1 * 3 + p.coeff 2 * 3 ^ 2) = 0
  ring

/-! ### Test 1: Positive nonzero-error line instance -/

/-- Underlying codeword `v₀(i) = 1 + i^2` of degree `2 < 3`. -/
private noncomputable def v0True : Fin 5 → ZMod 11 :=
  fun i => (1 + X ^ 2 : (ZMod 11)[X]).eval (points5 i)

/-- Underlying codeword `v₁(i) = 2 * i` of degree `1 < 3`. -/
private noncomputable def v1True : Fin 5 → ZMod 11 :=
  fun i => (C (2 : ZMod 11) * X).eval (points5 i)

/-- Corrupted word `u₀`, differing from `v₀` at coordinate `0` (`+1`). -/
private noncomputable def u0Corrupt : Fin 5 → ZMod 11 :=
  fun i => if i = 0 then v0True i + 1 else v0True i

/-- Corrupted word `u₁`, differing from `v₁` at coordinate `0` (`+3`). -/
private noncomputable def u1Corrupt : Fin 5 → ZMod 11 :=
  fun i => if i = 0 then v1True i + 3 else v1True i

private theorem v0True_mem_rs : v0True ∈ reedSolomon points5 3 := by
  refine eval_mem_reedSolomon points5 ?_
  have h1 : (1 : (ZMod 11)[X]).degree < (3 : ℕ) := by
    rw [degree_one]; exact Nat.cast_lt.2 (by decide)
  have h2 : (X ^ 2 : (ZMod 11)[X]).degree < (3 : ℕ) := by
    rw [degree_X_pow]; exact Nat.cast_lt.2 (by decide)
  exact (degree_add_le _ _).trans_lt (max_lt h1 h2)

private theorem v1True_mem_rs : v1True ∈ reedSolomon points5 3 := by
  refine eval_mem_reedSolomon points5 ?_
  refine (degree_mul_le _ _).trans_lt ?_
  have h1 : (C (2 : ZMod 11)).degree ≤ 0 := degree_C_le
  have h2 : (X : (ZMod 11)[X]).degree = 1 := degree_X
  rw [h2]
  exact (add_le_add h1 le_rfl).trans_lt (by rw [zero_add]; exact Nat.cast_lt.2 (by decide))

private theorem u0Corrupt_not_mem_rs : u0Corrupt ∉ reedSolomon points5 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u0Corrupt 0 - 3 * u0Corrupt 1 + 3 * u0Corrupt 2 - u0Corrupt 3 = 1 := by
    simp only [u0Corrupt, v0True, points5, eval_add, eval_one, eval_pow, eval_X]
    decide
  rw [hval] at hdiff
  exact one_ne_zero hdiff

private theorem u1Corrupt_not_mem_rs : u1Corrupt ∉ reedSolomon points5 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u1Corrupt 0 - 3 * u1Corrupt 1 + 3 * u1Corrupt 2 - u1Corrupt 3 = 3 := by
    simp only [u1Corrupt, v1True, points5, eval_mul, eval_C, eval_X]
    decide
  rw [hval] at hdiff
  exact (by decide : (3 : ZMod 11) ≠ 0) hdiff

/-- Concrete nonzero-error instantiation of `exists_correlatedAgreement_unique` over `ZMod 11`
(`n = 5`, `k = 3`, `e = 1`, `#S = 6 > 5`), also proving uniqueness of the recovered codewords. -/
theorem test_correlatedAgreement_unique_positive :
    u0Corrupt ∉ reedSolomon points5 3 ∧
    u1Corrupt ∉ reedSolomon points5 3 ∧
    ∃ D' : Finset (Fin 5), 4 ≤ D'.card ∧
      ∀ i ∈ D', u0Corrupt i = v0True i ∧ u1Corrupt i = v1True i := by
  let S : Finset (ZMod 11) := {0, 1, 2, 3, 4, 5}
  have hS : Fintype.card (Fin 5) < S.card := by decide
  have hagree_true : ∀ i ∈ (Finset.univ.erase (0 : Fin 5)),
      u0Corrupt i = v0True i ∧ u1Corrupt i = v1True i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    simp only [u0Corrupt, u1Corrupt, hne, ↓reduceIte, and_self]
  have hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon points5 3,
      hammingDist (u0Corrupt + z • u1Corrupt) c ≤ 1 := by
    intro z _
    refine ⟨v0True + z • v1True, Submodule.add_mem _ v0True_mem_rs
      (Submodule.smul_mem _ z v1True_mem_rs), ?_⟩
    exact hammingDist_add_smul_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hagree_true z
  obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hagree⟩ :=
    exists_correlatedAgreement_unique points5_injective (e := 1) (k := 3) (by decide)
      u0Corrupt u1Corrupt S hS hclose
  -- By RS minimum distance `5 - 3 + 1 = 3`, agreeing with `v₀True` at `≥ 3` points forces equality.
  have hv₀_eq : v₀ = v0True := by
    have hsub : D'.erase 0 ⊆ Finset.univ.filter fun i => v₀ i = v0True i := by
      intro i hi
      refine mem_filter.2 ⟨mem_univ i, ?_⟩
      have hne : i ≠ 0 := (mem_erase.1 hi).1
      have hmem : i ∈ D' := (mem_erase.1 hi).2
      rw [← (hagree i hmem).1]
      simp only [u0Corrupt, hne, ↓reduceIte]
    have hcard : 3 ≤ (D'.erase 0).card := by
      have := Finset.card_erase_le (s := D') (a := (0 : Fin 5))
      have hge := Finset.pred_card_le_card_erase (s := D') (a := (0 : Fin 5))
      simp only [Fintype.card_fin] at hD'
      omega
    have hle := card_le_card hsub
    by_contra hne
    have hdiff_mem : v₀ - v0True ∈ reedSolomon points5 3 := Submodule.sub_mem _ hv₀ v0True_mem_rs
    have hdiff_ne : v₀ - v0True ≠ 0 := sub_ne_zero.2 hne
    have hnorm := le_hammingNorm_of_mem_reedSolomon points5_injective hdiff_mem hdiff_ne
    have htot := card_agree_add_hammingDist v₀ v0True
    have hdist : hammingDist v₀ v0True = hammingNorm (v₀ - v0True) := by
      rw [hammingDist_comm, hammingDist_eq_hammingNorm, neg_add_eq_sub]
    simp only [Fintype.card_fin] at hnorm
    omega
  have hv₁_eq : v₁ = v1True := by
    have hsub : D'.erase 0 ⊆ Finset.univ.filter fun i => v₁ i = v1True i := by
      intro i hi
      refine mem_filter.2 ⟨mem_univ i, ?_⟩
      have hne : i ≠ 0 := (mem_erase.1 hi).1
      have hmem : i ∈ D' := (mem_erase.1 hi).2
      rw [← (hagree i hmem).2]
      simp only [u1Corrupt, hne, ↓reduceIte]
    have hcard : 3 ≤ (D'.erase 0).card := by
      have hge := Finset.pred_card_le_card_erase (s := D') (a := (0 : Fin 5))
      simp only [Fintype.card_fin] at hD'
      omega
    have hle := card_le_card hsub
    by_contra hne
    have hdiff_mem : v₁ - v1True ∈ reedSolomon points5 3 := Submodule.sub_mem _ hv₁ v1True_mem_rs
    have hdiff_ne : v₁ - v1True ≠ 0 := sub_ne_zero.2 hne
    have hnorm := le_hammingNorm_of_mem_reedSolomon points5_injective hdiff_mem hdiff_ne
    have htot := card_agree_add_hammingDist v₁ v1True
    have hdist : hammingDist v₁ v1True = hammingNorm (v₁ - v1True) := by
      rw [hammingDist_comm, hammingDist_eq_hammingNorm, neg_add_eq_sub]
    simp only [Fintype.card_fin] at hnorm
    omega
  refine ⟨u0Corrupt_not_mem_rs, u1Corrupt_not_mem_rs, D', ?_, ?_⟩
  · simpa only [Fintype.card_fin] using hD'
  · subst hv₀_eq hv₁_eq
    exact hagree

/-! ### Test 2: Negative / tightness line dichotomy instance -/

/-- Disjoint single-coordinate spikes at coordinates `0` and `1`. -/
private def spike0 : Fin 5 → ZMod 11 := fun i => if i = 0 then 1 else 0
private def spike1 : Fin 5 → ZMod 11 := fun i => if i = 1 then 1 else 0

/-- At `z = 1`, the word `spike0 + 1 • spike1` (equal to `(1, 1, 0, 0, 0)`) has distance `> 1`
from every codeword in `reedSolomon points5 3`. -/
private theorem spike_line_far_at_one :
    ∀ c ∈ reedSolomon points5 3, 1 < hammingDist (spike0 + (1 : ZMod 11) • spike1) c := by
  intro c hcRS
  by_contra hle
  push Not at hle
  obtain ⟨p, hp, rfl⟩ := mem_reedSolomon.1 hcRS
  let w : Fin 5 → ZMod 11 := spike0 + (1 : ZMod 11) • spike1
  have hagree_card : 4 ≤ (Finset.univ.filter fun i : Fin 5 => w i = p.eval (points5 i)).card := by
    have htot := card_agree_add_hammingDist w (fun i => p.eval (points5 i))
    change hammingDist w (fun i => p.eval (points5 i)) ≤ 1 at hle
    omega
  let a := p.coeff 0
  let b := p.coeff 1
  let d := p.coeff 2
  have hev : ∀ i : Fin 5, p.eval (points5 i) = a + b * points5 i + d * points5 i ^ 2 :=
    fun i => eval_eq_of_degree_lt_three hp (points5 i)
  -- At most one coordinate of `Fin 5` disagrees; split on which coordinate `j` might disagree.
  have hex : ∃ j : Fin 5, ∀ i : Fin 5, i ≠ j → w i = p.eval (points5 i) := by
    by_cases hall : ∀ i : Fin 5, w i = p.eval (points5 i)
    · exact ⟨0, fun i _ => hall i⟩
    · push Not at hall
      obtain ⟨j, hj⟩ := hall
      refine ⟨j, fun i hij => ?_⟩
      by_contra hi
      have hsub : (Finset.univ.filter fun t : Fin 5 => w t = p.eval (points5 t)) ⊆
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
  have h0eq : w 0 = p.eval (points5 0) → (1 : ZMod 11) = a := by
    intro h; rw [hev 0] at h
    have hw : w 0 = 1 := by decide
    have hp0 : points5 0 = 0 := by decide
    rw [hw, hp0] at h; linear_combination h
  have h1eq : w 1 = p.eval (points5 1) → (1 : ZMod 11) = a + b + d := by
    intro h; rw [hev 1] at h
    have hw : w 1 = 1 := by decide
    have hp1 : points5 1 = 1 := by decide
    rw [hw, hp1] at h; linear_combination h
  have h2eq : w 2 = p.eval (points5 2) → (0 : ZMod 11) = a + 2 * b + 4 * d := by
    intro h; rw [hev 2] at h
    have hw : w 2 = 0 := by decide
    have hp2 : points5 2 = 2 := by decide
    rw [hw, hp2] at h; linear_combination h
  have h3eq : w 3 = p.eval (points5 3) → (0 : ZMod 11) = a + 3 * b + 9 * d := by
    intro h; rw [hev 3] at h
    have hw : w 3 = 0 := by decide
    have hp3 : points5 3 = 3 := by decide
    rw [hw, hp3] at h; linear_combination h
  have h4eq : w 4 = p.eval (points5 4) → (0 : ZMod 11) = a + 4 * b + 16 * d := by
    intro h; rw [hev 4] at h
    have hw : w 4 = 0 := by decide
    have hp4 : points5 4 = 4 := by decide
    rw [hw, hp4] at h; linear_combination h
  fin_cases j
  · have h1 := h1eq (hj 1 (by decide))
    have h2 := h2eq (hj 2 (by decide))
    have h3 := h3eq (hj 3 (by decide))
    have h4 := h4eq (hj 4 (by decide))
    have : (1 : ZMod 11) = 0 := by linear_combination h1 - 3 * h2 + 3 * h3 - h4
    exact one_ne_zero this
  · have h0 := h0eq (hj 0 (by decide))
    have h2 := h2eq (hj 2 (by decide))
    have h3 := h3eq (hj 3 (by decide))
    have h4 := h4eq (hj 4 (by decide))
    have : (1 : ZMod 11) = 0 := by linear_combination h0 - 6 * h2 + 8 * h3 - 3 * h4
    exact one_ne_zero this
  · have h0 := h0eq (hj 0 (by decide))
    have h1 := h1eq (hj 1 (by decide))
    have h3 := h3eq (hj 3 (by decide))
    have h4 := h4eq (hj 4 (by decide))
    have : (1 : ZMod 11) = 0 := by linear_combination -1 * h0 + 2 * h1 - 2 * h3 + h4
    exact one_ne_zero this
  · have h0 := h0eq (hj 0 (by decide))
    have h1 := h1eq (hj 1 (by decide))
    have h2 := h2eq (hj 2 (by decide))
    have h4 := h4eq (hj 4 (by decide))
    have : (5 : ZMod 11) = 0 := by linear_combination -3 * h0 + 8 * h1 - 6 * h2 + h4
    exact (by decide : (5 : ZMod 11) ≠ 0) this
  · have h0 := h0eq (hj 0 (by decide))
    have h1 := h1eq (hj 1 (by decide))
    have h2 := h2eq (hj 2 (by decide))
    have h3 := h3eq (hj 3 (by decide))
    have : (2 : ZMod 11) = 0 := by linear_combination -1 * h0 + 3 * h1 - 3 * h2 + h3
    exact (by decide : (2 : ZMod 11) ≠ 0) this

/-- Negative/tightness instantiation of `proximityGap_unique`: `z = 0` is within distance `1` of
the code, `z = 1` is not, and therefore at most `5` scalars in `ZMod 11` are within distance `1`. -/
theorem test_proximityGap_unique_negative :
    open scoped Classical in
    (∃ c ∈ reedSolomon points5 3, hammingDist (spike0 + (0 : ZMod 11) • spike1) c ≤ 1) ∧
    (Finset.univ.filter fun z : ZMod 11 =>
      ∃ c ∈ reedSolomon points5 3, hammingDist (spike0 + z • spike1) c ≤ 1).card ≤ 5 := by
  classical
  constructor
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    have hdist : hammingDist (spike0 + (0 : ZMod 11) • spike1) 0 = 1 := by decide
    omega
  · rcases proximityGap_unique points5_injective (e := 1) (k := 3) (by decide) spike0 spike1 with
      hall | hcard
    · obtain ⟨c, hcRS, hdist⟩ := hall 1
      exact absurd hdist (not_le.2 (spike_line_far_at_one c hcRS))
    · simpa only [Fintype.card_fin] using hcard

/-! ### Test 3: Parameterized curve instance (`d = 2`, three corrupted words) -/

/-- Third codeword `v₂(i) = 3` (constant) and its corrupted version differing at coordinate `0`. -/
private def v2True : Fin 5 → ZMod 11 := fun _ => 3

private def u2Corrupt : Fin 5 → ZMod 11 := fun i => if i = 0 then 5 else 3

private theorem v2True_mem_rs : v2True ∈ reedSolomon points5 3 := by
  refine mem_reedSolomon.2 ⟨C 3, ?_, funext fun _ => eval_C⟩
  exact degree_C_le.trans_lt (Nat.cast_lt.2 (by decide))

private theorem u2Corrupt_not_mem_rs : u2Corrupt ∉ reedSolomon points5 3 := by
  intro hmem
  have hdiff := third_diff_zero_of_mem_rs hmem
  have hval : u2Corrupt 0 - 3 * u2Corrupt 1 + 3 * u2Corrupt 2 - u2Corrupt 3 = 2 := by
    simp only [u2Corrupt]; decide
  rw [hval] at hdiff
  exact (by decide : (2 : ZMod 11) ≠ 0) hdiff

/-- Concrete `d = 2` (three-word) curve instantiation of `exists_correlatedAgreement_curve_unique`
over `ZMod 11` (`d * n = 10 < 11 = |ZMod 11|`). -/
theorem test_correlatedAgreement_curve_unique_deg2 :
    u2Corrupt ∉ reedSolomon points5 3 ∧
    ∃ D' : Finset (Fin 5), 4 ≤ D'.card ∧
      ∃ v : Fin 3 → (Fin 5 → ZMod 11), (∀ j, v j ∈ reedSolomon points5 3) ∧
        ∀ i ∈ D', ∀ j, (![u0Corrupt, u1Corrupt, u2Corrupt] j) i = v j i := by
  let u : Fin 3 → (Fin 5 → ZMod 11) := ![u0Corrupt, u1Corrupt, u2Corrupt]
  let vTrue : Fin 3 → (Fin 5 → ZMod 11) := ![v0True, v1True, v2True]
  have hvTrue_mem : ∀ j : Fin 3, vTrue j ∈ reedSolomon points5 3 := by
    intro j
    fin_cases j
    · exact v0True_mem_rs
    · exact v1True_mem_rs
    · exact v2True_mem_rs
  have hagree_true : ∀ i ∈ (Finset.univ.erase (0 : Fin 5)), ∀ j : Fin 3, u j i = vTrue j i := by
    intro i hi j
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    fin_cases j
    · change u0Corrupt i = v0True i; simp only [u0Corrupt, hne, ↓reduceIte]
    · change u1Corrupt i = v1True i; simp only [u1Corrupt, hne, ↓reduceIte]
    · change u2Corrupt i = v2True i; simp only [u2Corrupt, v2True, hne, ↓reduceIte]
  have hclose : ∀ z ∈ (Finset.univ : Finset (ZMod 11)), ∃ c ∈ reedSolomon points5 3,
      hammingDist (∑ j : Fin 3, z ^ (j : ℕ) • u j) c ≤ 1 := by
    intro z _
    refine ⟨∑ j : Fin 3, z ^ (j : ℕ) • vTrue j,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j),
      hammingDist_curve_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hagree_true z⟩
  have hS : 2 * Fintype.card (Fin 5) < (Finset.univ : Finset (ZMod 11)).card := by decide
  obtain ⟨D', hD', v, hvRS, hagree⟩ :=
    exists_correlatedAgreement_curve_unique (d := 2) points5_injective (e := 1) (k := 3)
      (by decide) u Finset.univ hS hclose
  exact ⟨u2Corrupt_not_mem_rs, D', by simpa only [Fintype.card_fin] using hD', v, hvRS, hagree⟩

/-- Concrete `d = 2` dichotomy instantiation of `proximityGap_curve_unique` over `ZMod 11`:
since `z = 1` lies at distance `> 1` on the curve `spike0 + z • spike1 + z^2 • 0`, at most
`2 * 5 = 10` scalars in `ZMod 11` lie within distance `1` of the code. -/
theorem test_proximityGap_curve_unique_deg2 :
    open scoped Classical in
    (Finset.univ.filter fun z : ZMod 11 =>
      ∃ c ∈ reedSolomon points5 3,
        hammingDist (∑ j : Fin 3, z ^ (j : ℕ) • (![spike0, spike1, (0 : Fin 5 → ZMod 11)] j)) c ≤
          1).card ≤ 10 := by
  classical
  let u : Fin 3 → (Fin 5 → ZMod 11) := ![spike0, spike1, 0]
  rcases proximityGap_curve_unique (d := 2) points5_injective (e := 1) (k := 3) (by decide) u with
    hall | hcard
  · obtain ⟨c, hcRS, hdist⟩ := hall 1
    have hsum : (∑ j : Fin 3, (1 : ZMod 11) ^ (j : ℕ) • u j) =
        spike0 + (1 : ZMod 11) • spike1 := by
      rw [Fin.sum_univ_three]
      change (1 : ZMod 11) ^ 0 • spike0 + (1 : ZMod 11) ^ 1 • spike1 +
        (1 : ZMod 11) ^ 2 • (0 : Fin 5 → ZMod 11) = spike0 + (1 : ZMod 11) • spike1
      simp only [pow_zero, one_smul, pow_one, smul_zero, add_zero]
    rw [hsum] at hdist
    exact absurd hdist (not_le.2 (spike_line_far_at_one c hcRS))
  · simpa only [Fintype.card_fin] using hcard

/-! ### Test 4: Uniqueness & maximality clauses (Theorems 1.4 & 1.5) -/

/-- Line uniqueness-clause test (`exists_uniqueMaximal_correlatedAgreement_unique`): pins the exact
unique maximal set `Finset.univ.erase 0`, the exact codewords `(v0True, v1True)`, and the literal
`∃!` maximal qualifying set over `ZMod 11` (`n = 5`, `k = 3`, `e = 1`). -/
theorem test_uniqueMaximal_correlatedAgreement_unique :
    u0Corrupt ∉ reedSolomon points5 3 ∧
    u1Corrupt ∉ reedSolomon points5 3 ∧
    (∃! D' : Finset (Fin 5),
      (4 ≤ D'.card ∧ ∃ v₀ ∈ reedSolomon points5 3, ∃ v₁ ∈ reedSolomon points5 3,
        ∀ i ∈ D', u0Corrupt i = v₀ i ∧ u1Corrupt i = v₁ i) ∧
      ∀ D₂ : Finset (Fin 5),
        (4 ≤ D₂.card ∧ ∃ w₀ ∈ reedSolomon points5 3, ∃ w₁ ∈ reedSolomon points5 3,
          ∀ i ∈ D₂, u0Corrupt i = w₀ i ∧ u1Corrupt i = w₁ i) →
        D' ⊆ D₂ → D₂ = D') ∧
    ∀ (D'' : Finset (Fin 5)) (w₀ w₁ : Fin 5 → ZMod 11),
      4 ≤ D''.card → w₀ ∈ reedSolomon points5 3 → w₁ ∈ reedSolomon points5 3 →
      (∀ i ∈ D'', u0Corrupt i = w₀ i ∧ u1Corrupt i = w₁ i) →
      D'' ⊆ Finset.univ.erase 0 ∧ w₀ = v0True ∧ w₁ = v1True := by
  let S : Finset (ZMod 11) := {0, 1, 2, 3, 4, 5}
  have hS : Fintype.card (Fin 5) < S.card := by decide
  have hagree_true : ∀ i ∈ (Finset.univ.erase (0 : Fin 5)),
      u0Corrupt i = v0True i ∧ u1Corrupt i = v1True i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    simp only [u0Corrupt, u1Corrupt, hne, ↓reduceIte, and_self]
  have hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon points5 3,
      hammingDist (u0Corrupt + z • u1Corrupt) c ≤ 1 := fun z _ =>
    ⟨v0True + z • v1True, Submodule.add_mem _ v0True_mem_rs
      (Submodule.smul_mem _ z v1True_mem_rs),
      hammingDist_add_smul_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hagree_true z⟩
  obtain ⟨D', hD', v₀, hv₀, v₁, hv₁, hagree, hmax⟩ :=
    exists_uniqueMaximal_correlatedAgreement_unique points5_injective (e := 1) (k := 3) (by decide)
      u0Corrupt u1Corrupt S hS hclose
  obtain ⟨her_sub, hv₀_eq, hv₁_eq⟩ :=
    hmax (Finset.univ.erase 0) v0True v1True (by decide) v0True_mem_rs v1True_mem_rs hagree_true
  subst hv₀_eq hv₁_eq
  have hD'_eq : D' = Finset.univ.erase 0 := by
    refine Finset.Subset.antisymm (fun i hi => mem_erase.2 ⟨?_, mem_univ i⟩) her_sub
    rintro rfl
    have h0 := (hagree 0 hi).1
    simp only [u0Corrupt, ↓reduceIte, add_eq_left] at h0
    exact one_ne_zero h0
  subst hD'_eq
  refine ⟨u0Corrupt_not_mem_rs, u1Corrupt_not_mem_rs, ?_, ?_⟩
  · refine ⟨Finset.univ.erase 0, ⟨⟨by decide, v0True, v0True_mem_rs, v1True, v1True_mem_rs,
      hagree_true⟩, fun D₂ hD₂ hsub => ?_⟩, fun D₁ hD₁ => ?_⟩
    · obtain ⟨hcard₂, w₀, hw₀, w₁, hw₁, hag₂⟩ := hD₂
      exact Finset.Subset.antisymm (hmax D₂ w₀ w₁ (by simpa only [Fintype.card_fin] using hcard₂)
        hw₀ hw₁ hag₂).1 hsub
    · obtain ⟨⟨hcard₁, w₀, hw₀, w₁, hw₁, hag₁⟩, hmax₁⟩ := hD₁
      have hsub := (hmax D₁ w₀ w₁ (by simpa only [Fintype.card_fin] using hcard₁)
        hw₀ hw₁ hag₁).1
      exact (hmax₁ (Finset.univ.erase 0)
        ⟨by decide, v0True, v0True_mem_rs, v1True, v1True_mem_rs, hagree_true⟩ hsub).symm
  · intro D'' w₀ w₁ hD'' hw₀ hw₁ hag''
    exact hmax D'' w₀ w₁ (by simpa only [Fintype.card_fin] using hD'') hw₀ hw₁ hag''

/-- Curve uniqueness-clause test (`exists_uniqueMaximal_correlatedAgreement_curve_unique`, `d = 2`):
pins the exact unique maximal set `Finset.univ.erase 0` and exact codewords
`![v0True, v1True, v2True]` over `ZMod 11`. -/
theorem test_uniqueMaximal_correlatedAgreement_curve_deg2 :
    u2Corrupt ∉ reedSolomon points5 3 ∧
    ∀ (D'' : Finset (Fin 5)) (w : Fin 3 → (Fin 5 → ZMod 11)),
      4 ≤ D''.card → (∀ j, w j ∈ reedSolomon points5 3) →
      (∀ i ∈ D'', ∀ j, (![u0Corrupt, u1Corrupt, u2Corrupt] j) i = w j i) →
      D'' ⊆ Finset.univ.erase 0 ∧ w = ![v0True, v1True, v2True] := by
  let u : Fin 3 → (Fin 5 → ZMod 11) := ![u0Corrupt, u1Corrupt, u2Corrupt]
  let vTrue : Fin 3 → (Fin 5 → ZMod 11) := ![v0True, v1True, v2True]
  have hvTrue_mem : ∀ j : Fin 3, vTrue j ∈ reedSolomon points5 3 := by
    intro j; fin_cases j
    · exact v0True_mem_rs
    · exact v1True_mem_rs
    · exact v2True_mem_rs
  have hagree_true : ∀ i ∈ (Finset.univ.erase (0 : Fin 5)), ∀ j : Fin 3, u j i = vTrue j i := by
    intro i hi j
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    fin_cases j
    · change u0Corrupt i = v0True i; simp only [u0Corrupt, hne, ↓reduceIte]
    · change u1Corrupt i = v1True i; simp only [u1Corrupt, hne, ↓reduceIte]
    · change u2Corrupt i = v2True i; simp only [u2Corrupt, v2True, hne, ↓reduceIte]
  have hclose : ∀ z ∈ (Finset.univ : Finset (ZMod 11)), ∃ c ∈ reedSolomon points5 3,
      hammingDist (∑ j : Fin 3, z ^ (j : ℕ) • u j) c ≤ 1 := fun z _ =>
    ⟨∑ j : Fin 3, z ^ (j : ℕ) • vTrue j,
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hvTrue_mem j),
      hammingDist_curve_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hagree_true z⟩
  have hS : 2 * Fintype.card (Fin 5) < (Finset.univ : Finset (ZMod 11)).card := by decide
  obtain ⟨D', _, v, _, hagree, hmax⟩ :=
    exists_uniqueMaximal_correlatedAgreement_curve_unique (d := 2) points5_injective
      (e := 1) (k := 3) (by decide) u Finset.univ hS hclose
  obtain ⟨her_sub, hv_eq⟩ :=
    hmax (Finset.univ.erase 0) vTrue (by decide) hvTrue_mem hagree_true
  subst hv_eq
  have hD'_eq : D' = Finset.univ.erase 0 := by
    refine Finset.Subset.antisymm (fun i hi => mem_erase.2 ⟨?_, mem_univ i⟩) her_sub
    rintro rfl
    have h0 : u0Corrupt 0 = v0True 0 := hagree 0 hi 0
    simp only [u0Corrupt, ↓reduceIte, add_eq_left] at h0
    exact one_ne_zero h0
  subst hD'_eq
  exact ⟨u2Corrupt_not_mem_rs, fun D'' w hD'' hwRS hag'' =>
    hmax D'' w (by simpa only [Fintype.card_fin] using hD'') hwRS hag''⟩

/-- Non-maximal strict-subset test at `n = 7`, `k = 3`, `e = 2` (`2 * 2 + 3 = 7`) over `ZMod 11`:
words corrupted at only coordinate `0` admit a valid non-maximal agreement set
`D'' = {2, 3, 4, 5, 6}` of size `5 = 7 - 2`, which sits strictly inside the unique maximal set
`Finset.univ.erase 0` of size `6` (`D'' ⊂ D'`) with the same unique codewords. -/
theorem test_uniqueMaximal_strict_subset_e2 :
    let pts7 : Fin 7 → ZMod 11 := fun i => (i : ℕ)
    let v0_7 : Fin 7 → ZMod 11 := fun i => (1 + X ^ 2 : (ZMod 11)[X]).eval (pts7 i)
    let v1_7 : Fin 7 → ZMod 11 := fun i => (C (2 : ZMod 11) * X).eval (pts7 i)
    let u0_7 : Fin 7 → ZMod 11 := fun i => if i = 0 then v0_7 i + 1 else v0_7 i
    let u1_7 : Fin 7 → ZMod 11 := fun i => if i = 0 then v1_7 i + 3 else v1_7 i
    let D_nonmax : Finset (Fin 7) := {2, 3, 4, 5, 6}
    D_nonmax.card = 5 ∧
    (∀ i ∈ D_nonmax, u0_7 i = v0_7 i ∧ u1_7 i = v1_7 i) ∧
    ∃ D' : Finset (Fin 7), D_nonmax ⊂ D' ∧ D' = Finset.univ.erase 0 ∧
      ∀ (D'' : Finset (Fin 7)) (w₀ w₁ : Fin 7 → ZMod 11),
        5 ≤ D''.card → w₀ ∈ reedSolomon pts7 3 → w₁ ∈ reedSolomon pts7 3 →
        (∀ i ∈ D'', u0_7 i = w₀ i ∧ u1_7 i = w₁ i) →
        D'' ⊆ D' ∧ w₀ = v0_7 ∧ w₁ = v1_7 := by
  intro pts7 v0_7 v1_7 u0_7 u1_7 D_nonmax
  have hpts7 : Function.Injective pts7 := by decide
  have hv0_mem : v0_7 ∈ reedSolomon pts7 3 := by
    refine eval_mem_reedSolomon pts7 ?_
    exact (degree_add_le _ _).trans_lt (max_lt
      (by rw [degree_one]; exact Nat.cast_lt.2 (by decide))
      (by rw [degree_X_pow]; exact Nat.cast_lt.2 (by decide)))
  have hv1_mem : v1_7 ∈ reedSolomon pts7 3 := by
    refine eval_mem_reedSolomon pts7 ?_
    refine (degree_mul_le _ _).trans_lt ?_
    rw [degree_X]
    exact (add_le_add degree_C_le le_rfl).trans_lt
      (by rw [zero_add]; exact Nat.cast_lt.2 (by decide))
  have hag_er : ∀ i ∈ Finset.univ.erase (0 : Fin 7), u0_7 i = v0_7 i ∧ u1_7 i = v1_7 i := by
    intro i hi
    have hne : i ≠ 0 := (mem_erase.1 hi).1
    simp only [u0_7, u1_7, hne, ↓reduceIte, and_self]
  have hag_nm : ∀ i ∈ D_nonmax, u0_7 i = v0_7 i ∧ u1_7 i = v1_7 i :=
    fun i hi => hag_er i (by revert i hi; decide)
  let S : Finset (ZMod 11) := {0, 1, 2, 3, 4, 5, 6, 7}
  have hS : Fintype.card (Fin 7) < S.card := by decide
  have hclose : ∀ z ∈ S, ∃ c ∈ reedSolomon pts7 3, hammingDist (u0_7 + z • u1_7) c ≤ 2 := fun z _ =>
    ⟨v0_7 + z • v1_7, Submodule.add_mem _ hv0_mem (Submodule.smul_mem _ z hv1_mem),
      hammingDist_add_smul_le_of_eq_on (D' := Finset.univ.erase 0) (by decide) hag_er z⟩
  obtain ⟨D', _, v₀, _, v₁, _, hagree, hmax⟩ :=
    exists_uniqueMaximal_correlatedAgreement_unique hpts7 (e := 2) (k := 3) (by decide)
      u0_7 u1_7 S hS hclose
  obtain ⟨her_sub, hv₀_eq, hv₁_eq⟩ :=
    hmax (Finset.univ.erase 0) v0_7 v1_7 (by decide) hv0_mem hv1_mem hag_er
  subst hv₀_eq hv₁_eq
  have hD'_eq : D' = Finset.univ.erase 0 := by
    refine Finset.Subset.antisymm (fun i hi => mem_erase.2 ⟨?_, mem_univ i⟩) her_sub
    rintro rfl
    have h0 := (hagree 0 hi).1
    simp only [u0_7, ↓reduceIte, add_eq_left] at h0
    exact one_ne_zero h0
  subst hD'_eq
  refine ⟨by decide, hag_nm, Finset.univ.erase 0, ?_, rfl, fun D'' w₀ w₁ hD'' hw₀ hw₁ hag'' =>
    hmax D'' w₀ w₁ (by simpa only [Fintype.card_fin] using hD'') hw₀ hw₁ hag''⟩
  rw [Finset.ssubset_iff_of_subset (hmax D_nonmax v0_7 v1_7 (by decide) hv0_mem hv1_mem hag_nm).1]
  exact ⟨1, by decide, by decide⟩

end CslibFrontierTests.Foundations.Data.Code.ProximityGap.Unique
