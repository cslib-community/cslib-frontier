/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Boolean.Braverman.AlmostResilience
import CslibFrontier.Foundations.BooleanAnalysis.FourierBitVal
import CslibFrontier.Foundations.BooleanAnalysis.Majority
import CslibFrontier.Foundations.BooleanAnalysis.ResilientComposition
public import CslibFrontier.Probability.Extractor.LeftoverHash
public import CslibFrontier.Probability.Extractor.ResilientTwoSource
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform

/-!
# Chattopadhyay–Zuckerman resilient functions and two-source extractor reduction

Non-vacuous concrete instances and boundary checks across the five modules formalizing steps toward
[Chattopadhyay–Zuckerman][ChattopadhyayZuckerman2019]:
1. Fourier smoothing (`Cslib.BitString.exists_isKWiseIndependent_dist_le`,
   `exists_isKWiseIndependent_dist_le_of_dist_map_restrict_le`) and almost-`t`-wise Braverman /
   Tribes resilience (`Cslib.Circuits.Boolean.Braverman.AlmostResilience`) on an explicit
   small-bias distribution `smallBiasPair n γ` that is genuinely NOT `t`-wise independent.
2. Cube-versus-marginal equivalence (`isKWiseResilient_iff_forall_compl`) and sharp NOBF
   extraction (`dist_map_uniformOfFintype_bool_le_of_coalitionInfluence`,
   `dist_map_uniformOfFintype_bool_le_of_isKWiseSmallBias_restrict`) on a `3`-bit non-oblivious
   bit-fixing source for `Cslib.majority 3`, paired with a negative parity boundary.
3. Exact `3`-majority coalition-influence composition (`coalitionInfluence_composeBlocks_maj3`) and
   Ben-Or–Linial iterated `3`-majority (`iterMaj3`, `isResilient_iterMaj3`) on `9` bits.
4. Concrete unconditional `IsTwoSourceExtractor` instantiation at error `3 / 16 < 1 / 2` for weak
   sources (`k₁ = 13 < 24`, `k₂ = 70 < 72`) via `isTwoSourceExtractor_of_resilient_condenser`, plus
   a Markov bad-seed check on `LinearHash.isStrongExtractor` and a deterministic check of
   `isTwoSourceExtractor_of_resilient_strongExtractor`.
-/

namespace CslibFrontierTests.CZResilientExtractor

open Finset Function Cslib Cslib.BitString Cslib.Probability Cslib.Probability.PMF
  Cslib.Circuits.Boolean.Braverman
open scoped BigOperators NNReal

/-! ### 1. Fourier smoothing & almost-`t`-wise Tribes resilience on non-independent sources -/

section SmallBiasPair

private noncomputable def smallBiasPair (n : ℕ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hn : 2 ≤ n) : PMF (BitString n) :=
  let pairSet : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩}
  have hsum : ∑ x : BitString n,
      ENNReal.ofReal ((1 + γ * chi ℝ pairSet x) / 2 ^ n) = 1 := by
    have hnn (x : BitString n) : 0 ≤ (1 + γ * chi ℝ pairSet x) / (2 : ℝ) ^ n := by
      have hca : |chi ℝ pairSet x| = 1 := abs_chi pairSet x
      have hchi : -1 ≤ chi ℝ pairSet x := (abs_le.mp hca.le).1
      have hmul : -1 ≤ γ * chi ℝ pairSet x := by nlinarith
      exact div_nonneg (by linarith) (by positivity)
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => hnn x)]
    have hpne : pairSet.Nonempty := ⟨⟨0, by omega⟩, by simp [pairSet]⟩
    have hreal : ∑ x : BitString n, (1 + γ * chi ℝ pairSet x) / (2 : ℝ) ^ n = 1 := by
      rw [← sum_div, sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, ← mul_sum, sum_chi, ite_eq_right hpne.ne_empty, mul_zero, add_zero,
        nsmul_eq_mul, mul_one]
      push_cast
      have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
      exact div_self hpow
    rw [hreal, ENNReal.ofReal_one]
  PMF.ofFintype (fun x => ENNReal.ofReal ((1 + γ * chi ℝ pairSet x) / 2 ^ n)) hsum

private theorem bias_smallBiasPair (n : ℕ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hn : 2 ≤ n)
    {S : Finset (Fin n)} (hS : S.Nonempty) :
    bias (smallBiasPair n γ hγ0 hγ1 hn) S =
      if ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin n)) = S then γ else 0 := by
  let pairSet : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩}
  have hnn (x : BitString n) : 0 ≤ (1 + γ * chi ℝ pairSet x) / (2 : ℝ) ^ n := by
    have hca : |chi ℝ pairSet x| = 1 := abs_chi pairSet x
    have hchi : -1 ≤ chi ℝ pairSet x := (abs_le.mp hca.le).1
    have hmul : -1 ≤ γ * chi ℝ pairSet x := by nlinarith
    exact div_nonneg (by linarith) (by positivity)
  have htoReal (x : BitString n) :
      ((smallBiasPair n γ hγ0 hγ1 hn) x).toReal = (1 + γ * chi ℝ pairSet x) / 2 ^ n := by
    change (ENNReal.ofReal ((1 + γ * chi ℝ pairSet x) / 2 ^ n)).toReal = _
    exact ENNReal.toReal_ofReal (hnn x)
  rw [bias]
  simp_rw [htoReal, div_mul_eq_mul_div, ← sum_div, add_mul, sum_add_distrib, one_mul]
  rw [sum_chi, ite_eq_right hS.ne_empty, zero_add]
  have hdot : ∑ x : BitString n, γ * chi ℝ pairSet x * chi ℝ S x =
      if pairSet = S then γ * (2 : ℝ) ^ n else 0 := by
    simp_rw [mul_assoc, ← mul_sum]
    have hex := expect_chi_mul_chi pairSet S
    rw [Fintype.expect_eq_sum_div_card] at hex
    have hcard : (Fintype.card (BitString n) : ℝ) = (2 : ℝ) ^ n := by simp
    rw [hcard] at hex
    have hsum_chi : ∑ x : BitString n, chi ℝ pairSet x * chi ℝ S x =
        if pairSet = S then (2 : ℝ) ^ n else 0 := by
      have hpos : (2 : ℝ) ^ n ≠ 0 := by positivity
      calc ∑ x : BitString n, chi ℝ pairSet x * chi ℝ S x
          = ((∑ x : BitString n, chi ℝ pairSet x * chi ℝ S x) / (2 : ℝ) ^ n) * (2 : ℝ) ^ n := by
            field_simp
        _ = (if pairSet = S then (1 : ℝ) else 0) * (2 : ℝ) ^ n := by rw [hex]
        _ = if pairSet = S then (2 : ℝ) ^ n else 0 := by split_ifs <;> ring
    rw [hsum_chi]
    split_ifs <;> ring
  rw [hdot]
  have hpow : (2 : ℝ) ^ n ≠ 0 := by positivity
  split_ifs
  · field_simp [hpow]
  · simp

private theorem isKWiseSmallBias_smallBiasPair (n k : ℕ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hn : 2 ≤ n) : IsKWiseSmallBias k γ (smallBiasPair n γ hγ0 hγ1 hn) := by
  intro S hS _
  rw [bias_smallBiasPair n γ hγ0 hγ1 hn hS]
  split_ifs
  · exact (abs_of_nonneg hγ0).le
  · rw [abs_zero]; exact hγ0

private theorem not_isKWiseIndependent_smallBiasPair (n k : ℕ) (hk : 2 ≤ k) (γ : ℝ)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hn : 2 ≤ n) :
    ¬IsKWiseIndependent k (smallBiasPair n γ hγ0.le hγ1 hn) := by
  intro hind
  let pairSet : Finset (Fin n) := {⟨0, by omega⟩, ⟨1, by omega⟩}
  have hp_ne : pairSet.Nonempty := ⟨⟨0, by omega⟩, by simp [pairSet]⟩
  have hp_card : #pairSet ≤ k := card_le_two.trans hk
  have h0 := hind pairSet hp_ne hp_card
  rw [bias_smallBiasPair n γ hγ0.le hγ1 hn hp_ne, ite_eq_left rfl, abs_of_pos hγ0] at h0
  linarith

private noncomputable def smallBiasThree : PMF (BitString 3) :=
  smallBiasPair 3 (1 / 8) (by norm_num) (by norm_num) (by norm_num)

-- `smallBiasThree` is `2`-wise `(1 / 8)`-biased, NOT `2`-wise independent, and Fourier-smoothes
-- to an exact `2`-wise independent distribution within statistical distance `1 / 9`.
example : ¬IsKWiseIndependent 2 smallBiasThree :=
  not_isKWiseIndependent_smallBiasPair 3 2 le_rfl (1 / 8) (by norm_num) (by norm_num) (by norm_num)

example :
    ∃ D' : PMF (BitString 3), IsKWiseIndependent 2 D' ∧ dist smallBiasThree D' ≤ 1 / 9 := by
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le smallBiasThree 2
  refine ⟨D', hD'_ind, hdist.trans ?_⟩
  let pairSet : Finset (Fin 3) := {⟨0, by omega⟩, ⟨1, by omega⟩}
  have hp_ne : pairSet.Nonempty := ⟨⟨0, by decide⟩, mem_insert_self _ _⟩
  have hp_mem : pairSet ∈ (univ : Finset (Finset (Fin 3))).filter fun S => S.Nonempty ∧ #S ≤ 2 :=
    mem_filter.mpr ⟨mem_univ _, hp_ne, card_le_two⟩
  have hB_eq :
      (∑ S ∈ (univ : Finset (Finset (Fin 3))).filter (fun S => S.Nonempty ∧ #S ≤ 2),
        |bias smallBiasThree S|) = 1 / 8 := by
    rw [sum_eq_single pairSet]
    · dsimp only [smallBiasThree]
      rw [bias_smallBiasPair 3 (1 / 8) _ _ _ hp_ne, ite_eq_left rfl, abs_of_nonneg (by norm_num)]
    · intro S hS hSne
      dsimp only [smallBiasThree]
      rw [bias_smallBiasPair 3 (1 / 8) _ _ _ (mem_filter.mp hS).2.1,
        ite_eq_right fun h => hSne h.symm, abs_zero]
    · intro h
      exact absurd hp_mem h
  rw [hB_eq]
  norm_num

-- Also exercise `exists_isKWiseIndependent_dist_le_of_dist_map_restrict_le`: a `2`-bit `(1 / 64)`-
-- biased distribution has every `T`-marginal within `1 / 64` of uniform (`2 * 2 ^ 2 * (1 / 64)`
-- gives `dist ≤ 1 / 8 < 1`).
example :
    let D : PMF (BitString 2) := smallBiasPair 2 (1 / 64) (by norm_num) (by norm_num) (by norm_num)
    ∃ D' : PMF (BitString 2), IsKWiseIndependent 2 D' ∧ dist D D' ≤ 1 / 8 := by
  intro D
  have hD_bias : IsKWiseSmallBias 2 (1 / 64) D :=
    isKWiseSmallBias_smallBiasPair 2 2 (1 / 64) (by norm_num) (by norm_num) (by norm_num)
  have hmarg (T : Finset (Fin 2)) (hT : #T ≤ 2) :
      dist (D.map T.restrict) (PMF.uniformOfFintype (↥T → Bool)) ≤ 1 / 64 := by
    refine (hD_bias.dist_map_restrict_le hT).trans ?_
    have hpow : ((2 : ℝ) ^ #T - 1) ≤ 4 := by
      have h1 : (2 : ℝ) ^ #T ≤ 2 ^ 2 := by gcongr; norm_num
      linarith
    have hsqrt : Real.sqrt ((2 : ℝ) ^ #T - 1) ≤ 2 :=
      (Real.sqrt_le_sqrt hpow).trans_eq (by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)])
    nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ #T - 1)]
  obtain ⟨D', hD'_ind, hdist⟩ := exists_isKWiseIndependent_dist_le_of_dist_map_restrict_le hmarg
  refine ⟨D', hD'_ind, hdist.trans ?_⟩
  simp only [Fintype.card_fin]
  norm_num

private theorem tribes_bias_smallBiasPair (w p t : ℕ) (hn : 2 ≤ tribesSize w * w) (ht2 : 2 ≤ t)
    (hp : 1 ≤ p) (hs : tribesSize w < 2 ^ p) (hw : w < 2 ^ p) (ht : (64 * p) ^ 64 ≤ t) :
    ∃ D : PMF (BitString (tribesSize w * w)), ¬IsKWiseIndependent t D ∧
      |∑ x, (D x).toReal * bitVal ℝ (tribes w (tribesSize w) x) - 1 / 2| ≤
        2⁻¹ ^ w + 1 / 2 ^ p + 1 / ((tribesSize w * w : ℕ) : ℝ) := by
  let s := tribesSize w
  let n := s * w
  let γ : ℝ := (n : ℝ)⁻¹ ^ (t + 1)
  have hn1 : 1 ≤ n := (by norm_num : 1 ≤ 2).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by norm_num : 0 < 2).trans_le hn
  have hγpos : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 :=
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by exact_mod_cast hn1))
  let D := smallBiasPair n γ hγpos.le hγ1 hn
  refine ⟨D, not_isKWiseIndependent_smallBiasPair n t ht2 γ hγpos hγ1 hn, ?_⟩
  have h := abs_sum_bitVal_tribes_sub_half_le_of_isKWiseSmallBias (w := w) (s := s) (p := p)
    (t := t) (D := D) (γ := γ) hp hs hw (one_div_two_le_pow_tribesSize w)
    (pow_tribesSize_add_one_lt_one_div_two w) ht hγpos.le
    (isKWiseSmallBias_smallBiasPair n t γ hγpos.le hγ1 hn)
  have herr : (s * w : ℝ) ^ t * γ = 1 / ((s * w : ℕ) : ℝ) := by
    have hsw : (s * w : ℝ) = ((s * w : ℕ) : ℝ) := by push_cast; rfl
    dsimp only [γ, n]
    rw [hsw, pow_succ, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hn0.ne', one_pow, one_mul, one_div]
  rwa [herr] at h

-- Under `smallBiasPair n γ` with `n = tribesSize 1015 * 1015`, `p = 1016`,
-- `t = 2 ^ 1024 ≥ (64 * 1016) ^ 64`, and `γ = n⁻¹ ^ (t + 1)`, the distribution is NOT `t`-wise
-- independent yet `Tribes` bias is at most `2⁻¹ ^ 1015 + 1 / 2 ^ 1016 + 1 / n`.
set_option exponentiation.threshold 1024 in
example :
    ∃ D : PMF (BitString (tribesSize 1015 * 1015)),
      ¬IsKWiseIndependent (2 ^ 1024) D ∧
        |∑ x, (D x).toReal * bitVal ℝ (tribes 1015 (tribesSize 1015) x) - 1 / 2| ≤
          2⁻¹ ^ 1015 + 1 / 2 ^ 1016 + 1 / ((tribesSize 1015 * 1015 : ℕ) : ℝ) := by
  have hs := two_pow_sub_one_le_tribesSize (by norm_num : 1 ≤ 1015)
  have h2w : 2 ≤ 2 ^ (1015 - 1) := Nat.le_self_pow (Nat.sub_ne_zero_of_lt (by norm_num)) 2
  have hn : 2 ≤ tribesSize 1015 * 1015 :=
    (Nat.le_mul_of_pos_right _ (by norm_num)).trans (Nat.mul_le_mul_right 1015 (h2w.trans hs))
  have ht2 : 2 ≤ 2 ^ 1024 := Nat.le_self_pow (by norm_num) 2
  have ht : (64 * 1016) ^ 64 ≤ 2 ^ 1024 := by
    calc (64 * 1016) ^ 64 ≤ (64 * 1024) ^ 64 := by gcongr; norm_num
      _ = 2 ^ 1024 := by
        rw [show 64 = 2 ^ 6 by norm_num, show 1024 = 2 ^ 10 by norm_num, ← pow_add, ← pow_mul]
        exact congrArg (2 ^ ·) (by norm_num)
  have hw_lt : 1015 < 2 ^ 1016 :=
    (by norm_num : 1015 < 2 ^ 10).trans (Nat.pow_lt_pow_right one_lt_two (by norm_num))
  exact tribes_bias_smallBiasPair 1015 1016 (2 ^ 1024) hn ht2 (by norm_num)
    ((tribesSize_lt_two_pow 1015).trans (Nat.pow_lt_pow_right one_lt_two (by norm_num)))
    hw_lt ht

end SmallBiasPair

/-! ### 2. Non-oblivious bit-fixing (NOBF) extraction and negative boundary -/

section NOBF

private abbrev Q₀ : Finset (Fin 3) := {0}

private noncomputable def nobf3 : PMF (BitString 3) :=
  (PMF.uniformOfFintype (↥Q₀ᶜ → Bool)).map fun u i =>
    if h : i ∈ Q₀ then u ⟨1, by decide⟩ ^^ u ⟨2, by decide⟩ else u ⟨i, mem_compl.mpr h⟩

private theorem nobf3_map_restrict :
    nobf3.map Q₀ᶜ.restrict = PMF.uniformOfFintype (↥Q₀ᶜ → Bool) := by
  rw [nobf3, PMF.map_comp]
  have hfn : (Q₀ᶜ.restrict ∘ fun (u : ↥Q₀ᶜ → Bool) i =>
      if h : i ∈ Q₀ then u ⟨1, by decide⟩ ^^ u ⟨2, by decide⟩ else u ⟨i, mem_compl.mpr h⟩) =
      id := by
    funext u ⟨i, hi⟩
    dsimp only [Function.comp_def, Finset.restrict, id_eq]
    exact dite_eq_right fun h => absurd h (mem_compl.mp hi)
  rw [hfn, PMF.map_id]

private theorem extendUniform_uniformOfFintype_three :
    extendUniform Q₀ (PMF.uniformOfFintype (↥Q₀ᶜ → Bool)) =
      PMF.uniformOfFintype (BitString 3) := by
  have hsb : IsSmallBias 0 (extendUniform Q₀ (PMF.uniformOfFintype (↥Q₀ᶜ → Bool))) := by
    intro S hS
    by_cases hSQ : Disjoint S Q₀
    · rw [bias_extendUniform_of_disjoint hSQ, bias_uniformOfFintype]
      have hne : (S.subtype (· ∈ Q₀ᶜ)).Nonempty := by
        obtain ⟨i, hiS⟩ := hS
        exact ⟨⟨i, mem_compl.mpr (Finset.disjoint_left.mp hSQ hiS)⟩, mem_subtype.mpr hiS⟩
      rw [ite_eq_right hne.ne_empty, abs_zero]
    · rw [bias_extendUniform_of_not_disjoint hSQ, abs_zero]
  have hdist := hsb.dist_uniform_le
  rw [mul_zero, zero_div] at hdist
  exact dist_eq_zero.mp (le_antisymm hdist dist_nonneg)

private theorem coalitionInfluence_maj3_pair {D : PMF (BitString 3)}
    (hD : IsKWiseIndependent 2 D) (a b c : Fin 3) (hbc : b ≠ c)
    (hiff : ∀ x : BitString 3, IsUndetermined {a} (majority 3) x ↔ x b ≠ x c) :
    coalitionInfluence D {a} (majority 3) = 1 / 2 := by
  rw [coalitionInfluence]
  have hpt (x : BitString 3) :
      (if IsUndetermined {a} (majority 3) x then (1 : ℝ) else 0) =
        (1 - chi ℝ ({b, c} : Finset (Fin 3)) x) / 2 := by
    have hchi : chi ℝ ({b, c} : Finset (Fin 3)) x = signVal (x b) * signVal (x c) := by
      rw [← chi_singleton b x, ← chi_singleton c x, ← chi_union (disjoint_singleton.mpr hbc)]
      rfl
    rw [if_congr (hiff x) rfl rfl, hchi]
    cases x b <;> cases x c <;> norm_num
  simp_rw [hpt, mul_div_assoc', ← sum_div, mul_sub, mul_one, sum_sub_distrib, sum_toReal]
  have h0 : bias D {b, c} = 0 := abs_nonpos_iff.mp (hD {b, c} ⟨b, by simp⟩ card_le_two)
  rw [← bias, h0, sub_zero]

private theorem coalitionInfluence_maj3_eq_half {D : PMF (BitString 3)}
    (hD : IsKWiseIndependent 2 D) {Q : Finset (Fin 3)} (hQ : #Q = 1) :
    coalitionInfluence D Q (majority 3) = 1 / 2 := by
  rw [card_eq_one] at hQ
  obtain ⟨j, rfl⟩ := hQ
  fin_cases j
  · exact coalitionInfluence_maj3_pair hD 0 1 2 (by decide) fun x => by revert x; decide
  · exact coalitionInfluence_maj3_pair hD 1 0 2 (by decide) fun x => by revert x; decide
  · exact coalitionInfluence_maj3_pair hD 2 0 1 (by decide) fun x => by revert x; decide

-- Positive NOBF extraction check on `majority 3` via
-- `dist_map_uniformOfFintype_bool_le_of_coalitionInfluence`:
-- `dist (nobf3.map (majority 3)) uniform ≤ 1 / 2`.
example :
    dist (nobf3.map (majority 3)) (PMF.uniformOfFintype Bool) ≤ 1 / 2 := by
  have h := dist_map_uniformOfFintype_bool_le_of_coalitionInfluence nobf3
    (PMF.uniformOfFintype (BitString 3)) Q₀ (majority 3)
  have hmean : ∑ x : BitString 3,
      ((PMF.uniformOfFintype (BitString 3)) x).toReal * bitVal ℝ (majority 3 x) = 1 / 2 := by
    rw [sum_uniformOfFintype_mul]
    exact expect_bitVal_eq_half_of_selfDual (majority_not 1)
  have hmarg : nobf3.map Q₀ᶜ.restrict = (PMF.uniformOfFintype (BitString 3)).map Q₀ᶜ.restrict := by
    rw [← extendUniform_uniformOfFintype_three, map_restrict_compl_extendUniform,
      nobf3_map_restrict]
  have hinf := coalitionInfluence_maj3_eq_half
    (isKWiseIndependent_uniformOfFintype (ι := Fin 3) 2) (card_singleton 0)
  rw [hmean, sub_self, abs_zero, zero_add, hinf, hmarg, dist_self, add_zero] at h
  exact h

-- Cube-vs-marginal equivalence (`isKWiseResilient_iff_forall_compl`) and
-- `dist_map_uniformOfFintype_bool_le_of_isKWiseSmallBias_restrict` checked on `majority 3`.
example :
    (∀ Q : Finset (Fin 3), #Q = 1 → ∀ D' : PMF (↥Qᶜ → Bool), IsKWiseIndependent 2 D' →
      coalitionInfluence (extendUniform Q D') Q (majority 3) ≤ 1 / 2) ↔
    IsKWiseResilient 2 1 (1 / 2) (majority 3) :=
  isKWiseResilient_iff_forall_compl.symm

example : dist (nobf3.map (majority 3)) (PMF.uniformOfFintype Bool) ≤ 1 / 2 := by
  have hZ : IsKWiseSmallBias 3 0 (nobf3.map Q₀ᶜ.restrict) := by
    rw [nobf3_map_restrict]
    exact isKWiseIndependent_uniformOfFintype 3
  have hf_bias : ∀ D' : PMF (BitString 3), IsKWiseIndependent 3 D' →
      |(∑ x, (D' x).toReal * bitVal ℝ (majority 3 x)) - 1 / 2| ≤ 0 := by
    intro D' hD'
    have hmaj : ∀ x : BitString 3,
        majority 3 x = ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) := by
      decide
    have hf : ∀ x : BitString 3, bitVal ℝ (majority 3 x) =
        1 / 2 - (chi ℝ ({0} : Finset (Fin 3)) x + chi ℝ ({1} : Finset (Fin 3)) x +
          chi ℝ ({2} : Finset (Fin 3)) x - chi ℝ ({0, 1, 2} : Finset (Fin 3)) x) / 4 := by
      intro x
      have h012 : chi ℝ ({0, 1, 2} : Finset (Fin 3)) x =
          signVal (x 0) * signVal (x 1) * signVal (x 2) := by
        have hu : ({0, 1, 2} : Finset (Fin 3)) = {0} ∪ ({1} ∪ {2}) := by decide
        rw [hu, chi_union (by decide), chi_union (by decide), chi_singleton, chi_singleton,
          chi_singleton, mul_assoc]
      rw [chi_singleton, chi_singleton, chi_singleton, h012, hmaj]
      cases x 0 <;> cases x 1 <;> cases x 2 <;> simp [bitVal] <;> norm_num
    have hsum : ∑ x, (D' x).toReal * bitVal ℝ (majority 3 x) =
        1 / 2 - (bias D' {0} + bias D' {1} + bias D' {2} - bias D' {0, 1, 2}) / 4 := by
      simp_rw [hf, mul_sub, sum_sub_distrib, ← sum_mul, sum_toReal, one_mul, mul_div_assoc',
        ← sum_div, mul_sub, mul_add, sum_sub_distrib, sum_add_distrib]
      rw [← bias, ← bias, ← bias, ← bias]
    have hb0 : bias D' {0} = 0 := abs_nonpos_iff.mp (hD' {0} ⟨0, by simp⟩ (by decide))
    have hb1 : bias D' {1} = 0 := abs_nonpos_iff.mp (hD' {1} ⟨1, by simp⟩ (by decide))
    have hb2 : bias D' {2} = 0 := abs_nonpos_iff.mp (hD' {2} ⟨2, by simp⟩ (by decide))
    have hball : bias D' {0, 1, 2} = 0 :=
      abs_nonpos_iff.mp (hD' {0, 1, 2} ⟨0, by simp⟩ (by decide))
    rw [hsum, hb0, hb1, hb2, hball]
    norm_num
  have hf_res : IsKWiseResilient 3 1 (1 / 2) (majority 3) := fun Q hQ D hD =>
    (coalitionInfluence_maj3_eq_half (hD.mono (by decide)) hQ).le
  have h := dist_map_uniformOfFintype_bool_le_of_isKWiseSmallBias_restrict nobf3 Q₀ (majority 3)
    (t := 3) (q := 1) (ε₁ := 0) (ε₂ := 1 / 2) (γ := 0) (by decide) (by decide) le_rfl
    hZ hf_bias hf_res
  simpa using h

-- Negative NOBF boundary: `parity₃` has uniform coalition influence `1` and collapses to the
-- constant `false` distribution (`dist = 1 / 2` from uniform) under `nobf3`.
example :
    coalitionInfluence (PMF.uniformOfFintype (BitString 3)) Q₀ (fun x => x 0 ^^ x 1 ^^ x 2) = 1 ∧
      nobf3.map (fun x => x 0 ^^ x 1 ^^ x 2) = PMF.pure false ∧
      dist (nobf3.map fun x => x 0 ^^ x 1 ^^ x 2) (PMF.uniformOfFintype Bool) = 1 / 2 := by
  have hund : ∀ x : BitString 3, IsUndetermined Q₀ (fun y => y 0 ^^ y 1 ^^ y 2) x := by
    intro x
    refine ⟨Function.update x 0 (!x 0), x,
      fun i hi => Function.update_of_ne (by simpa [Q₀] using hi) _ _, fun _ _ => rfl, ?_⟩
    dsimp only
    rw [Function.update_self,
      Function.update_of_ne (by decide : (1 : Fin 3) ≠ 0),
      Function.update_of_ne (by decide : (2 : Fin 3) ≠ 0)]
    have key : ∀ a b c : Bool, (!a ^^ b ^^ c) ≠ (a ^^ b ^^ c) := by decide
    exact key _ _ _
  have hmap : nobf3.map (fun x => x 0 ^^ x 1 ^^ x 2) = PMF.pure false := by
    rw [nobf3, PMF.map_comp]
    have hconst : ((fun x : BitString 3 => x 0 ^^ x 1 ^^ x 2) ∘ fun (u : ↥Q₀ᶜ → Bool) i =>
        if h : i ∈ Q₀ then u ⟨1, by decide⟩ ^^ u ⟨2, by decide⟩ else u ⟨i, mem_compl.mpr h⟩) =
        Function.const (↥Q₀ᶜ → Bool) false := by
      funext u
      dsimp only [Function.comp_def, Function.const_apply]
      have h0 : (0 : Fin 3) ∈ Q₀ := by decide
      have h1 : (1 : Fin 3) ∉ Q₀ := by decide
      have h2 : (2 : Fin 3) ∉ Q₀ := by decide
      simp only [h0, h1, h2, ↓reduceDIte]
      cases u ⟨1, by decide⟩ <;> cases u ⟨2, by decide⟩ <;> rfl
    rw [hconst, PMF.map_const]
  refine ⟨coalitionInfluence_eq_one_of_forall _ hund, hmap, ?_⟩
  rw [hmap, dist_uniformOfFintype_bool]
  simp

end NOBF

/-! ### 3. Block composition & Ben-Or–Linial iterated `3`-majority -/

section Composition

-- `iterMaj3 2` on `9` bits is monotone, self-dual, balanced (`1 / 2`), and `(q, q / 4)`-resilient.
example :
    Monotone (iterMaj3 2) ∧
      (𝔼 x : BitString (3 ^ 2), bitVal ℝ (iterMaj3 2 x) = 1 / 2) ∧
      IsResilient 1 (1 / 4) (iterMaj3 2) ∧
      IsResilient 2 (1 / 2) (iterMaj3 2) := by
  refine ⟨monotone_iterMaj3 2, expect_bitVal_iterMaj3 2, ?_, ?_⟩
  · convert isResilient_iterMaj3 2 1 using 1
    norm_num
  · convert isResilient_iterMaj3 2 2 using 1
    norm_num

-- Exact `3`-majority composition identity on `3 * 3` bits with one compromised bit per block
-- (`Q = {0, 3, 6}`): each block has influence `1 / 2`, giving
-- `(1 / 2 + 1 / 2 + 1 / 2 - 1 / 8) / 2 = 11 / 16`, strictly below the naive union bound `3 / 4`.
example :
    coalitionInfluence (PMF.uniformOfFintype (BitString (3 * 3 ^ 1)))
      ({0, 3, 6} : Finset (Fin (3 * 3 ^ 1)))
      (composeBlocks (majority 3) (fun _ => iterMaj3 1)) = 11 / 16 := by
  rw [coalitionInfluence_composeBlocks_maj3 _ (fun _ => iterMaj3_not 1)]
  dsimp only
  have hsingle (j : Fin 3)
      (hpart : tribePart ({0, 3, 6} : Finset (Fin (3 * 3 ^ 1))) j = {0}) :
      coalitionInfluence (PMF.uniformOfFintype (BitString (3 ^ 1)))
        (tribePart ({0, 3, 6} : Finset (Fin (3 * 3 ^ 1))) j) (iterMaj3 1) = 1 / 2 := by
    rw [hpart]
    have hfun : (iterMaj3 1 : BitString 3 → Bool) = majority 3 := by
      funext x
      rfl
    rw [hfun]
    exact coalitionInfluence_maj3_eq_half
      (isKWiseIndependent_uniformOfFintype 2) (card_singleton 0)
  have hp0 : tribePart ({0, 3, 6} : Finset (Fin (3 * 3 ^ 1))) 0 = {0} := by
    ext i; rw [mem_tribePart]; fin_cases i <;> decide
  have hp1 : tribePart ({0, 3, 6} : Finset (Fin (3 * 3 ^ 1))) 1 = {0} := by
    ext i; rw [mem_tribePart]; fin_cases i <;> decide
  have hp2 : tribePart ({0, 3, 6} : Finset (Fin (3 * 3 ^ 1))) 2 = {0} := by
    ext i; rw [mem_tribePart]; fin_cases i <;> decide
  rw [hsingle 0 hp0, hsingle 1 hp1, hsingle 2 hp2]
  norm_num

end Composition

/-! ### 4. Two-source extractor reduction from resilient functions -/

section TwoSourceReduction

private theorem proj0_bias_zero (D : ℕ) [NeZero D] (D' : PMF (BitString D))
    (hD' : IsKWiseIndependent (0 + 1) D') :
    |(∑ z, (D' z).toReal * bitVal ℝ (z 0)) - 1 / 2| ≤ 0 := by
  have h1 : ∀ z : BitString D, bitVal ℝ (z 0) = (1 - chi ℝ ({0} : Finset (Fin D)) z) / 2 := by
    intro z
    rw [chi_singleton]
    cases z 0 <;> simp [bitVal]
  have hb : ∑ z, (D' z).toReal * bitVal ℝ (z 0) = 1 / 2 - bias D' {0} / 2 := by
    simp_rw [h1, mul_div_assoc', ← sum_div, mul_sub, mul_one, sum_sub_distrib, sum_toReal]
    rw [← bias]
    ring
  have h0 : bias D' {0} = 0 := abs_nonpos_iff.mp (hD' {0} ⟨0, by simp⟩ (by simp))
  rw [hb, h0]
  norm_num

private theorem isKWiseResilient_zero_zero {D : ℕ} (t : ℕ) (f : BitString D → Bool) :
    IsKWiseResilient t 0 0 f := by
  intro Q hQ D' _
  rw [card_eq_zero.mp hQ]
  have hzero : ∀ z : BitString D, ¬IsUndetermined ∅ f z := by
    rintro z ⟨a, b, ha, hb, hne⟩
    exact hne (congrArg f ((funext fun i => ha i (notMem_empty i)).trans
      (funext fun i => hb i (notMem_empty i)).symm))
  rw [coalitionInfluence_eq_zero_of_forall_not D' hzero]

public def blockCond (y : BitString (3 * 24)) (i : Fin 3) : Fin 1 → BitString 24 :=
  fun _ k => y (finProdFinEquiv (i, k))

private theorem blockCond_isSource (q : PMF (BitString (3 * 24))) (hq : 70 ≤ minEntropy q)
    (i : Fin 3) :
    IsSource (q.map fun y => blockCond y i)
      (Real.logb 2 (Fintype.card (Fin 1 → BitString 24)) - 2) 0 := by
  classical
  have hlog : Real.logb 2 (Fintype.card (Fin 1 → BitString 24)) = 24 := by
    have hcard : Fintype.card (Fin 1 → BitString 24) = 2 ^ 24 := by simp
    rw [hcard, Nat.cast_pow, Nat.cast_ofNat, Real.logb_pow]
    norm_num
  rw [hlog]
  refine isSource_of_le_minEntropy ((le_minEntropy_iff _).mpr fun r => ?_) 0
  rw [map_apply_toReal]
  let other (y : BitString (3 * 24)) : Fin 2 × Fin 24 → Bool :=
    fun ⟨j, k⟩ => y (finProdFinEquiv (i.succAbove j, k))
  let toPair (y : BitString (3 * 24)) : (Fin 1 → BitString 24) × (Fin 2 × Fin 24 → Bool) :=
    (blockCond y i, other y)
  let fromPair (ru : (Fin 1 → BitString 24) × (Fin 2 × Fin 24 → Bool)) : BitString (3 * 24) :=
    fun idx =>
      let ⟨b, k⟩ := finProdFinEquiv.symm idx
      if hb : b = i then ru.1 0 k
      else ru.2 (Classical.choose (Fin.exists_succAbove_eq hb), k)
  let e : BitString (3 * 24) ≃ (Fin 1 → BitString 24) × (Fin 2 × Fin 24 → Bool) :=
    { toFun := toPair
      invFun := fromPair
      left_inv := fun y => by
        funext idx
        obtain ⟨⟨b, k⟩, rfl⟩ := finProdFinEquiv.surjective idx
        dsimp only [fromPair, toPair]
        rw [Equiv.symm_apply_apply]
        by_cases hb : b = i
        · subst hb
          rw [dite_eq_left rfl]
          rfl
        · rw [dite_eq_right hb]
          dsimp only [other]
          rw [Classical.choose_spec (Fin.exists_succAbove_eq hb)]
      right_inv := fun ⟨r', u⟩ => Prod.ext
        (funext fun j => funext fun k => by
          rw [Subsingleton.elim j 0]
          dsimp only [toPair, blockCond, fromPair]
          rw [Equiv.symm_apply_apply, dite_eq_left rfl])
        (funext fun ⟨j, k⟩ => by
          dsimp only [toPair, other, fromPair]
          rw [Equiv.symm_apply_apply, dite_eq_right (Fin.succAbove_ne i j)]
          have hch : Classical.choose (Fin.exists_succAbove_eq (Fin.succAbove_ne i j)) = j :=
            Fin.succAbove_right_injective
              (Classical.choose_spec (Fin.exists_succAbove_eq (Fin.succAbove_ne i j)))
          rw [hch]) }
  have heq : (∑ y : BitString (3 * 24), if r = blockCond y i then (q y).toReal else 0) =
      ∑ ru : (Fin 1 → BitString 24) × (Fin 2 × Fin 24 → Bool),
        if r = ru.1 then (q (e.symm ru)).toReal else 0 :=
    Fintype.sum_equiv e _ _ fun y => by
      rw [e.symm_apply_apply]
      rfl
  rw [heq, Fintype.sum_prod_type, sum_comm]
  have hinner (u : Fin 2 × Fin 24 → Bool) :
      (∑ r' : Fin 1 → BitString 24, if r = r' then (q (e.symm (r', u))).toReal else 0) =
        (q (e.symm (r, u))).toReal := by
    simp_rw [eq_comm (a := r)]
    rw [sum_ite_eq', ite_eq_left (mem_univ r)]
  simp_rw [hinner]
  calc ∑ u : Fin 2 × Fin 24 → Bool, (q (e.symm (r, u))).toReal
      ≤ ∑ _u : Fin 2 × Fin 24 → Bool, (2 : ℝ) ^ (-(70 : ℝ)) :=
        sum_le_sum fun u _ => (le_minEntropy_iff q).mp hq (e.symm (r, u))
    _ = (#(univ : Finset (Fin 2 × Fin 24 → Bool)) : ℝ) * (2 : ℝ) ^ (-(70 : ℝ)) := by
        rw [sum_const, nsmul_eq_mul]
    _ = ((2 ^ 48 : ℕ) : ℝ) * (2 : ℝ) ^ (-(70 : ℝ)) := by
        rw [card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin 2,
          Fintype.card_fin 24, Fintype.card_bool, show 2 * 24 = 48 by decide]
    _ = (2 : ℝ) ^ (-((24 : ℝ) - 2)) := by
        rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast (2 : ℝ) 48,
          ← Real.rpow_add two_pos]
        exact congrArg ((2 : ℝ) ^ ·) (by norm_num)

private theorem linearHash24_isAdviceNM :
    IsAdviceNonMalleableExtractor
      (fun (x : BitString 24) (r : Fin 1 → BitString 24) (_ : Fin 3) => LinearHash.hash r x 0)
      0 13 (1 / 128) := by
  rw [isAdviceNonMalleableExtractor_zero_iff]
  intro _ source hsource
  have hhk : ((1 : ℕ) : ℝ) + 2 * Real.logb 2 ((1 / 64 : ℝ)⁻¹) ≤ 13 := by
    rw [show (1 / 64 : ℝ)⁻¹ = (2 : ℝ) ^ 6 by norm_num, Real.logb_pow]
    norm_num
  have hLH := LinearHash.isStrongExtractor 24 1 (by norm_num : (0 : ℝ) < 1 / 64) hhk source hsource
  let eOut : BitString 1 ≃ Bool :=
    { toFun := fun b => b 0
      invFun := fun b _ => b
      left_inv := fun b => funext fun j => by rw [Subsingleton.elim j 0]
      right_inv := fun _ => rfl }
  let e := Equiv.prodCongr (Equiv.refl (Fin 1 → BitString 24)) eOut
  have hmapL :
      (source.bind fun x => (PMF.uniformOfFintype (Fin 1 → BitString 24)).map fun r =>
        (r, LinearHash.hash r x 0)) =
      (source.bind fun x => (PMF.uniformOfFintype (Fin 1 → BitString 24)).map fun r =>
        (r, LinearHash.hash r x)).map e := by
    rw [PMF.map_bind]
    refine congrArg (source.bind ·) (funext fun x => ?_)
    rw [PMF.map_comp]
    rfl
  have hmapR :
      (PMF.uniformOfFintype ((Fin 1 → BitString 24) × BitString 1)).map e =
        PMF.uniformOfFintype ((Fin 1 → BitString 24) × Bool) :=
    uniformOfFintype_map_equiv e
  rw [hmapL, ← hmapR]
  have hdist := (dist_map_le _ _ e).trans hLH
  linarith

-- Concrete unconditional `IsTwoSourceExtractor` witness (`t = 0, q_bad = 0`) for genuinely weak
-- sources (`k₁ = 13 < 24`, `k₂ = 70 < 72`) with non-trivial error `3 / 16 < 1 / 2`.
public theorem cz_blockCondenser_twoSourceExtractor :
    IsTwoSourceExtractor
      (fun (x : BitString 24) (y : BitString (3 * 24)) =>
        LinearHash.hash (blockCond y 0) x 0) 13 70 (3 / 16) := by
  have h := isTwoSourceExtractor_of_resilient_condenser blockCond
    (fun (x : BitString 24) (r : Fin 1 → BitString 24) (_ : Fin 3) => LinearHash.hash r x 0)
    (fun z : BitString 3 => z 0)
    (fun q hq => ⟨∅, by simp, fun i _ => blockCond_isSource q hq i⟩)
    linearHash24_isAdviceNM (by decide) (proj0_bias_zero 3) (isKWiseResilient_zero_zero 1 _)
  refine h.mono le_rfl le_rfl (le_of_eq ?_)
  norm_num

-- Exercise Markov bad-seed extraction (`exists_badSet_isSource_of_isStrongExtractor`) on
-- `LinearHash.isStrongExtractor 10 1` (`D = 1024`, `k₂ = 7 < 10`, `ε_ext = 1 / 16`, `δ = 1 / 8`
-- -> `#B ≤ 512`).
example (q : PMF (BitString 10)) (hq : 7 ≤ minEntropy q) :
    let eSeed : (Fin 1 → BitString 10) ≃ Fin 1024 :=
      Fintype.equivFinOfCardEq (by simp)
    ∃ B : Finset (Fin 1024), #B ≤ 512 ∧
      ∀ i ∉ B, IsSource (q.map fun y => LinearHash.hash (eSeed.symm i) y) 1 (1 / 8 : ℝ≥0) := by
  intro eSeed
  have hhk : ((1 : ℕ) : ℝ) + 2 * Real.logb 2 ((1 / 8 : ℝ)⁻¹) ≤ 7 := by
    rw [show (1 / 8 : ℝ)⁻¹ = (2 : ℝ) ^ 3 by norm_num, Real.logb_pow]
    norm_num
  have hLH := LinearHash.isStrongExtractor 10 1 (by norm_num : (0 : ℝ) < 1 / 8) hhk
  have hcond : IsStrongExtractor (fun y i => LinearHash.hash (eSeed.symm i) y) 7 (1 / 16) := by
    intro source hsource
    let e := Equiv.prodCongr eSeed (Equiv.refl (BitString 1))
    have hmapL :
        (source.bind fun y => (PMF.uniformOfFintype (Fin 1024)).map fun i =>
          (i, LinearHash.hash (eSeed.symm i) y)) =
        (source.bind fun y => (PMF.uniformOfFintype (Fin 1 → BitString 10)).map fun s =>
          (s, LinearHash.hash s y)).map e := by
      rw [PMF.map_bind]
      refine congrArg (source.bind ·) (funext fun y => ?_)
      rw [PMF.map_comp, ← uniformOfFintype_map_equiv eSeed, PMF.map_comp]
      refine congrArg (fun g => (PMF.uniformOfFintype (Fin 1 → BitString 10)).map g) ?_
      funext s
      simp [e]
    have hmapR :
        (PMF.uniformOfFintype ((Fin 1 → BitString 10) × BitString 1)).map e =
          PMF.uniformOfFintype (Fin 1024 × BitString 1) :=
      uniformOfFintype_map_equiv e
    rw [hmapL, ← hmapR]
    have hd := (dist_map_le _ _ e).trans (hLH source hsource)
    linarith
  obtain ⟨B, hBcard, hBgood⟩ :=
    exists_badSet_isSource_of_isStrongExtractor hcond hq (by norm_num : (0 : ℝ≥0) < 1 / 8)
  have hlog : Real.logb 2 (Fintype.card (BitString 1)) = 1 := by
    have hcard : Fintype.card (BitString 1) = 2 := by simp
    rw [hcard, Nat.cast_ofNat, Real.logb_self_eq_one one_lt_two]
  rw [hlog] at hBgood
  have hfloor : Nat.floor ((1 / 16 : ℝ) * (1024 : ℕ) / ((1 / 8 : ℝ≥0) : ℝ)) ≤ 512 := by
    norm_num
  exact ⟨B, hBcard.trans hfloor, hBgood⟩

-- Exercise `isTwoSourceExtractor_of_resilient_strongExtractor` at `t = 0, D = 1, q_bad = 0` on
-- `LinearHash` (`k₁ = 13 < 24`, `k₂ = 24`, error `3 / 128 < 1 / 2`).
example :
    IsTwoSourceExtractor
      (fun (x y : BitString 24) => LinearHash.hash (fun _ : Fin 1 => y) x 0) 13 24 (3 / 128) := by
  have hcond : IsStrongExtractor (fun (y : BitString 24) (_ : Fin 1) => y) 24 0 := by
    intro q hq
    have hmass : ∀ y : BitString 24,
        (q y).toReal ≤ (PMF.uniformOfFintype (BitString 24) y).toReal := by
      intro y
      have hle := (le_minEntropy_iff q).mp hq y
      have heq : (2 : ℝ) ^ (-(24 : ℝ)) = (PMF.uniformOfFintype (BitString 24) y).toReal := by
        rw [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
          Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat,
          Real.rpow_neg zero_le_two]
        norm_cast
      exact hle.trans_eq heq
    have hdiff_zero :
        ∑ y : BitString 24, ((PMF.uniformOfFintype (BitString 24) y).toReal - (q y).toReal) =
          0 := by
      rw [sum_sub_distrib, sum_toReal, sum_toReal, sub_self]
    have hpt_eq : q = PMF.uniformOfFintype (BitString 24) := by
      have hall := (sum_eq_zero_iff_of_nonneg fun y _ => sub_nonneg.mpr (hmass y)).mp hdiff_zero
      ext y
      have hy := sub_eq_zero.mp (hall y (mem_univ y))
      exact ((ENNReal.toReal_eq_toReal_iff'
        (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp hy).symm
    subst hpt_eq
    have hpair :
        ((PMF.uniformOfFintype (BitString 24)).bind fun y =>
          (PMF.uniformOfFintype (Fin 1)).map fun i => (i, y)) =
        PMF.uniformOfFintype (Fin 1 × BitString 24) := by
      let he : BitString 24 ≃ Fin 1 × BitString 24 :=
        ⟨fun y => (0, y), Prod.snd, fun _ => rfl, fun ⟨i, y⟩ => by rw [Subsingleton.elim i 0]⟩
      have hmap :
          ((PMF.uniformOfFintype (BitString 24)).bind fun y =>
            (PMF.uniformOfFintype (Fin 1)).map fun i => (i, y)) =
          (PMF.uniformOfFintype (BitString 24)).map he := by
        rw [PMF.map]
        refine congrArg ((PMF.uniformOfFintype (BitString 24)).bind ·) (funext fun y => ?_)
        have hconst : (fun i : Fin 1 => (i, y)) = Function.const (Fin 1) (he y) := by
          funext i
          dsimp only [he, Function.const_apply]
          exact Prod.ext (Subsingleton.elim i 0) rfl
        rw [hconst, PMF.map_const]
        rfl
      rw [hmap, uniformOfFintype_map_equiv he]
    rw [hpair, dist_self]
  have hnm : IsAdviceNonMalleableExtractor
      (fun (x r : BitString 24) (_ : Fin 1) => LinearHash.hash (fun _ : Fin 1 => r) x 0)
      0 13 (1 / 128) := by
    rw [isAdviceNonMalleableExtractor_zero_iff]
    intro _ source hsource
    have hstrong : IsStrongExtractor
        (fun (x : BitString 24) (r : Fin 1 → BitString 24) => LinearHash.hash r x 0)
        13 (1 / 128) :=
      (isAdviceNonMalleableExtractor_zero_iff _ 13 (1 / 128)).mp linearHash24_isAdviceNM 0
    let eSeed : (Fin 1 → BitString 24) ≃ BitString 24 :=
      ⟨fun r => r 0, fun r _ => r, fun r => funext fun j => by rw [Subsingleton.elim j 0],
        fun _ => rfl⟩
    let e := Equiv.prodCongr eSeed (Equiv.refl Bool)
    have hmapL :
        (source.bind fun x => (PMF.uniformOfFintype (BitString 24)).map fun r =>
          (r, LinearHash.hash (fun _ : Fin 1 => r) x 0)) =
        (source.bind fun x => (PMF.uniformOfFintype (Fin 1 → BitString 24)).map fun r =>
          (r, LinearHash.hash r x 0)).map e := by
      rw [PMF.map_bind]
      refine congrArg (source.bind ·) (funext fun x => ?_)
      rw [PMF.map_comp, ← uniformOfFintype_map_equiv eSeed, PMF.map_comp]
      refine congrArg (fun g => (PMF.uniformOfFintype (Fin 1 → BitString 24)).map g) ?_
      funext r
      have hr : (fun _ : Fin 1 => r 0) = r := funext fun j => by rw [Subsingleton.elim j 0]
      simp [e, eSeed, hr]
    have hmapR :
        (PMF.uniformOfFintype ((Fin 1 → BitString 24) × Bool)).map e =
          PMF.uniformOfFintype (BitString 24 × Bool) :=
      uniformOfFintype_map_equiv e
    rw [hmapL, ← hmapR]
    exact (dist_map_le _ _ e).trans (hstrong source hsource)
  have h := isTwoSourceExtractor_of_resilient_strongExtractor
    (fun (y : BitString 24) (_ : Fin 1) => y)
    (fun (x r : BitString 24) (_ : Fin 1) => LinearHash.hash (fun _ : Fin 1 => r) x 0)
    (fun z : BitString 1 => z 0) (δ := 1 / 256) (by norm_num : (0 : ℝ≥0) < 1 / 256) hcond hnm
    (by norm_num) (by decide) (proj0_bias_zero 1) (isKWiseResilient_zero_zero 1 _)
  refine h.mono le_rfl le_rfl (le_of_eq ?_)
  norm_num

end TwoSourceReduction

end CslibFrontierTests.CZResilientExtractor
