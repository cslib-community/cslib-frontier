/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Foundations.BooleanAnalysis.FriedgutJunta

/-! # Tests for concentration on the influential coordinates

The dictator `x ↦ x 0` on two bits has variance `1`, so the sharp form of Proposition 3.31 puts it
within relative distance `1/2` of a constant, where Proposition 3.31 alone gives `1`. It has total
influence `1`, all of it on coordinate `0`, and no Fourier weight above degree `1`. At the threshold
`τ = 1` both the count of Theorem 9.28 and its weight bound for `J = ∅` and `k = 1` are attained.
With `K = 1`, `ε = 1/4`, `k = 1` and `J = {0}` it satisfies the hypotheses of the book-threshold
parts of Theorem 9.28, and they give its concentration on the subsets of `{0}` and a nearby
`{0}`-junta. -/

public section

namespace CslibFrontierTests.BooleanAnalysisFriedgutConcentration

open Cslib Cslib.BitString Finset

/-! ### The dictator on two bits -/

/-- The dictator `x ↦ x 0` on two bits, read as signs, is the character of `{0}`. -/
theorem signVal_dictator : (fun x : Fin 2 → Bool => signVal (x 0)) = chi ℝ {0} :=
  funext fun x => (chi_singleton 0 x).symm

/-- The dictator has total influence `1`. -/
theorem totalInfluence_dictator :
    totalInfluence (fun x : Fin 2 → Bool => signVal (x 0)) = 1 := by
  rw [signVal_dictator, totalInfluence_chi, card_singleton, Nat.cast_one]

/-- The influence of a coordinate on the dictator is `1` on coordinate `0` and `0` elsewhere. -/
theorem influence_dictator (i : Fin 2) :
    influence i (fun x : Fin 2 → Bool => signVal (x 0)) = if i = 0 then 1 else 0 := by
  rw [signVal_dictator, influence_chi]
  simp

/-- The coordinate `1` has no influence on the dictator. -/
theorem influence_dictator_of_notMem {i : Fin 2} (hi : i ∉ ({0} : Finset (Fin 2))) :
    influence i (fun x : Fin 2 → Bool => signVal (x 0)) = 0 := by
  rw [mem_singleton] at hi
  simp [influence_dictator, hi]

/-- The dictator's Fourier weight outside the subsets of `∅`, its variance, is `1`. -/
theorem sum_not_subset_empty_fourierCoeff_sq_dictator :
    ∑ S with ¬S ⊆ (∅ : Finset (Fin 2)), fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0)) S ^ 2
      = 1 := by
  simp [signVal_dictator, fourierCoeff_chi]

/-- The dictator has no Fourier weight above degree `1`. -/
theorem sum_one_lt_card_fourierCoeff_sq_dictator :
    ∑ S with 1 < #S, fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0)) S ^ 2 = 0 := by
  refine sum_eq_zero fun S hS => ?_
  have hS : S ≠ {0} := by
    rintro rfl
    simp at hS
  simp [signVal_dictator, fourierCoeff_chi, Ne.symm hS]

/-! ### The sharp junta bound -/

/-- **The sharp junta bound for the dictator**: it is within relative distance `1/2` of a constant,
where Proposition 3.31 alone gives `1`. -/
theorem exists_dependsOn_empty_hammingDist_dictator_le :
    ∃ g : (Fin 2 → Bool) → Bool, DependsOn g ((∅ : Finset (Fin 2)) : Set (Fin 2)) ∧
      (hammingDist (fun x : Fin 2 → Bool => x 0) g : ℝ) / 2 ^ Fintype.card (Fin 2) ≤ 1 / 2 := by
  obtain ⟨g, hg, hfg⟩ :=
    exists_dependsOn_two_mul_hammingDist_div_le_sum_not_subset_fourierCoeff_sq
      (fun x : Fin 2 → Bool => x 0) ∅
  rw [sum_not_subset_empty_fourierCoeff_sq_dictator] at hfg
  exact ⟨g, hg, by linarith⟩

/-! ### Theorem 9.28 -/

/-- At the threshold `τ = 1` the count `K / τ` with `K = 1` is attained: exactly one coordinate,
`0`, has influence at least `1`. -/
theorem card_filter_one_le_influence_dictator :
    (#{i | (1 : ℝ) ≤ influence i (fun x : Fin 2 → Bool => signVal (x 0))} : ℝ) ≤ 1 ∧
      #{i | (1 : ℝ) ≤ influence i (fun x : Fin 2 → Bool => signVal (x 0))} = 1 := by
  refine ⟨(card_filter_le_influence_le_div_of_totalInfluence_le _ one_pos
    totalInfluence_dictator.le).trans_eq (div_one 1), ?_⟩
  rw [card_eq_one]
  refine ⟨0, ?_⟩
  ext i
  fin_cases i <;> simp [influence_dictator]

/-- With `J = ∅`, threshold `τ = 1` and `k = 1`, the weight bound `3ᵏ / 3 · √τ · I[F] = 1` is
attained: the weight on the nonempty sets of size at most `1` is `1`. -/
theorem sum_filter_not_subset_empty_and_card_le_one_fourierCoeff_sq_dictator :
    ∑ S with ¬S ⊆ (∅ : Finset (Fin 2)) ∧ #S ≤ 1,
        fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0)) S ^ 2 ≤ 1 ∧
      ∑ S with ¬S ⊆ (∅ : Finset (Fin 2)) ∧ #S ≤ 1,
        fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0)) S ^ 2 = 1 := by
  refine ⟨(sum_filter_not_subset_and_card_le_fourierCoeff_sq_le (τ := 1) _
    (fun i _ => (influence_dictator i).trans_le (by split_ifs <;> norm_num)) 1).trans_eq ?_, ?_⟩
  · rw [totalInfluence_dictator, Real.sqrt_one]
    norm_num
  · simp [signVal_dictator, fourierCoeff_chi]

/-- With `K = 1`, `ε = 1/4`, `k = 1` and `J = {0}`, the book's threshold `ε² / (K² 9ᵏ)` holds
outside `J`, and the weight outside `{S ⊆ J} ∪ {|S| > 1}` is at most `ε / 3 = 1/12`. -/
theorem sum_filter_not_subset_and_card_le_fourierCoeff_sq_dictator_le :
    ∑ S with ¬S ⊆ ({0} : Finset (Fin 2)) ∧ #S ≤ 1,
      fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0)) S ^ 2 ≤ 1 / 4 / 3 :=
  sum_filter_not_subset_and_card_le_fourierCoeff_sq_le_of_totalInfluence_le _ (by norm_num)
    totalInfluence_dictator.le 1
    (fun i hi => (influence_dictator_of_notMem hi).trans_le (by norm_num))

/-- With the same parameters and no weight above degree `1`, the dictator's spectrum is
`1/2`-concentrated on the subsets of `{0}` of size at most `1`. -/
theorem sum_filter_not_subset_or_lt_card_fourierCoeff_sq_dictator_le :
    ∑ S with ¬S ⊆ ({0} : Finset (Fin 2)) ∨ 1 < #S,
      fourierCoeff (fun x : Fin 2 → Bool => signVal (x 0)) S ^ 2 ≤ 2 * (1 / 4) :=
  sum_filter_not_subset_or_lt_card_fourierCoeff_sq_le _ totalInfluence_dictator.le 1
    (fun i hi => (influence_dictator_of_notMem hi).trans_le (by norm_num))
    (sum_one_lt_card_fourierCoeff_sq_dictator.trans_le (by norm_num))

/-- With the same parameters, the dictator is `1/4`-close to a `{0}`-junta. -/
theorem exists_dependsOn_singleton_hammingDist_dictator_le :
    ∃ g : (Fin 2 → Bool) → Bool, DependsOn g (({0} : Finset (Fin 2)) : Set (Fin 2)) ∧
      (hammingDist (fun x : Fin 2 → Bool => x 0) g : ℝ) / 2 ^ Fintype.card (Fin 2) ≤ 1 / 4 :=
  exists_dependsOn_hammingDist_div_le_of_sum_lt_card_fourierCoeff_sq_le _
    totalInfluence_dictator.le 1
    (fun i hi => (influence_dictator_of_notMem hi).trans_le (by norm_num))
    (sum_one_lt_card_fourierCoeff_sq_dictator.trans_le (by norm_num))

end CslibFrontierTests.BooleanAnalysisFriedgutConcentration
