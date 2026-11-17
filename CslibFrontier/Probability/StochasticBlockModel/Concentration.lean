/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.StochasticBlockModel.Model
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Probability.Concentration.WeightedSum
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Union
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Concentration of true-label row margins in the stochastic block model

Each row of the shifted centered adjacency matrix has expected signed label margin `gap * n`.
A weighted Hoeffding bound controls its centered sum of independent incident edges. A union
bound shows that every row margin exceeds half its expectation except with probability at most
`2 n exp (-gap² n / 8)`.

These are margins against the fixed hidden labels. The argument makes no independence claim
for labels estimated from the observed graph; deterministic robustness of cleanup handles those
estimates separately.

## Main results

* `Cslib.Probability.StochasticBlockModel.coinLaw_exists_low_margin_le`: all true-label margins.
-/

public section

open Finset
open scoped unitInterval

namespace Cslib.Probability.StochasticBlockModel

variable {n : ℕ}

private def rowCoeff (g : Fin n → Bool) (i : Fin n) (e : Fin n × Fin n) : ℝ :=
  (if e.1 = i ∧ i < e.2 then BitString.signVal (g i) * BitString.signVal (g e.2) else 0) +
    (if e.2 = i ∧ e.1 < i then BitString.signVal (g i) * BitString.signVal (g e.1) else 0)

private theorem rowCoeff_sq (g : Fin n → Bool) (i : Fin n) (e : Fin n × Fin n) :
    rowCoeff g i e ^ 2 =
      (if e.1 = i ∧ i < e.2 then (1 : ℝ) else 0) +
        (if e.2 = i ∧ e.1 < i then (1 : ℝ) else 0) := by
  have hs (j : Fin n) : (BitString.signVal (g i) * BitString.signVal (g j)) ^ 2 = 1 := by
    rw [mul_pow, pow_two, pow_two, BitString.signVal_mul_self, BitString.signVal_mul_self]
    norm_num
  by_cases h₁ : e.1 = i ∧ i < e.2
  · simp [rowCoeff, h₁, hs]
  · by_cases h₂ : e.2 = i ∧ e.1 < i <;> simp [rowCoeff, h₁, h₂, hs]

private theorem sum_rowCoeff_sq_le (g : Fin n → Bool) (i : Fin n) :
    ∑ e, rowCoeff g i e ^ 2 ≤ (n : ℝ) := by
  simp only [rowCoeff_sq, sum_add_distrib, Fintype.sum_prod_type, ite_and]
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  rw [← sum_add_distrib]
  calc
    _ ≤ ∑ _j : Fin n, (1 : ℝ) := by
      apply sum_le_sum
      intro j _
      rcases lt_trichotomy i j with h | h | h
      · simp [h, not_lt_of_ge h.le]
      · simp [h]
      · simp [h, not_lt_of_ge h.le]
    _ = n := by simp

private theorem sum_rowCoeff_noise (p q : I) (g : Fin n → Bool) (i : Fin n) (ω : Coins n) :
    ∑ e, rowCoeff g i e *
      (BitString.bitVal ℝ (ω e) - edgeProbability p q g e.1 e.2) =
        BitString.signVal (g i) * ∑ j, noise p q g ω i j * BitString.signVal (g j) := by
  simp only [rowCoeff, add_mul, sum_add_distrib, Fintype.sum_prod_type,
    ite_mul, zero_mul, ite_and]
  simp only [sum_ite_irrel, sum_const_zero, sum_ite_eq', mem_univ, ite_true]
  simp only [noise, upperNoise, Matrix.add_apply, Matrix.transpose_apply, add_mul,
    sum_add_distrib, mul_add, mul_sum, mul_ite, ite_mul, mul_zero, zero_mul]
  congr 1 <;> apply sum_congr rfl <;> intro j _ <;> split_ifs <;> ring

private theorem row_margin_eq (p q : I) (g : Fin n → Bool) (i : Fin n) (ω : Coins n) :
    BitString.signVal (g i) *
        ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * BitString.signVal (g j) =
      gap p q * n + BitString.signVal (g i) *
        ∑ j, noise p q g ω i j * BitString.signVal (g j) := by
  rw [shiftedCenteredAdjacency_sample p q g ω]
  change BitString.signVal (g i) * ∑ j,
      (gap p q * (BitString.signVal (g i) * BitString.signVal (g j)) +
        noise p q g ω i j) * BitString.signVal (g j) = _
  simp only [add_mul, sum_add_distrib, mul_add]
  congr 1
  rw [mul_sum]
  have h (j : Fin n) : BitString.signVal (g i) *
      (gap p q * (BitString.signVal (g i) * BitString.signVal (g j)) *
        BitString.signVal (g j)) = gap p q := by
    calc
      _ = gap p q * (BitString.signVal (g i) * BitString.signVal (g i)) *
          (BitString.signVal (g j) * BitString.signVal (g j)) := by ring
      _ = _ := by rw [BitString.signVal_mul_self, BitString.signVal_mul_self]; ring
  simp only [h, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

private theorem coinLaw_low_margin_le (p q : I) (g : Fin n → Bool)
    (hgap : 0 ≤ gap p q) (i : Fin n) :
    ((coinLaw p q g).toOuterMeasure {ω |
      BitString.signVal (g i) *
        ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * BitString.signVal (g j) ≤
          gap p q * n / 2}).toReal ≤
      2 * Real.exp (-(gap p q) ^ 2 * n / 8) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.zero_lt_of_lt i.isLt
  let score (e : Fin n × Fin n) (b : Bool) : ℝ :=
    BitString.bitVal ℝ b - edgeProbability p q g e.1 e.2
  have hmean (e : Fin n × Fin n) :
      ∑ b, (PMF.coin (edgeProbability p q g e.1 e.2) b).toReal * score e b = 0 := by
    simp [score, PMF.coin_apply_toReal]
    ring
  have hosc (e : Fin n × Fin n) (a b : Bool) : |score e a - score e b| ≤ 2 := by
    simp only [score, sub_sub_sub_cancel_right]
    cases a <;> cases b <;> norm_num
  have htail := PMF.pi_abs_sum_mul_ge_le_of_centered
    (fun e : Fin n × Fin n => PMF.coin (edgeProbability p q g e.1 e.2)) score
    (rowCoeff g i) hmean hosc hn.le (sum_rowCoeff_sq_le g i)
    (show 0 ≤ gap p q * n / 2 by positivity)
  have hsub : {ω : Coins n |
      BitString.signVal (g i) *
        ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * BitString.signVal (g j) ≤
          gap p q * n / 2} ⊆
      {ω | gap p q * n / 2 ≤ |∑ e, rowCoeff g i e * score e (ω e)|} := by
    intro ω hω
    change gap p q * n / 2 ≤ |∑ e, rowCoeff g i e * score e (ω e)|
    change BitString.signVal (g i) *
      ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * BitString.signVal (g j) ≤
        gap p q * n / 2 at hω
    rw [row_margin_eq p q g i ω] at hω
    change gap p q * n / 2 ≤
      |∑ e, rowCoeff g i e * (BitString.bitVal ℝ (ω e) - edgeProbability p q g e.1 e.2)|
    rw [sum_rowCoeff_noise p q g i ω]
    exact (show gap p q * n / 2 ≤
      -(BitString.signVal (g i) * ∑ j, noise p q g ω i j * BitString.signVal (g j)) by
        linarith).trans (neg_le_abs _)
  have hprob := ENNReal.toReal_mono (PMF.toOuterMeasure_ne_top (coinLaw p q g) _)
    ((coinLaw p q g).toOuterMeasure.mono hsub)
  apply hprob.trans (htail.trans_eq ?_)
  congr 2
  field_simp
  ring

/-- Every true-label row margin is greater than half its mean, except with probability at most
`2 n exp (-gap² n / 8)`. The hidden labeling is fixed before the independent edges are sampled. -/
theorem coinLaw_exists_low_margin_le (p q : I) (g : Fin n → Bool) (hgap : 0 ≤ gap p q) :
    ((coinLaw p q g).toOuterMeasure {ω | ∃ i : Fin n,
      BitString.signVal (g i) *
        ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * BitString.signVal (g j) ≤
          gap p q * n / 2}).toReal ≤
      2 * n * Real.exp (-(gap p q) ^ 2 * n / 8) := by
  classical
  let bad (i : Fin n) : Set (Coins n) := {ω |
    BitString.signVal (g i) *
      ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * BitString.signVal (g j) ≤
        gap p q * n / 2}
  have h := PMF.toOuterMeasure_toReal_biUnion_finset_le (coinLaw p q g) univ bad
  have hset : {ω : Coins n | ∃ i : Fin n,
      BitString.signVal (g i) *
        ∑ j, shiftedCenteredAdjacency p q (sample ω) i j * BitString.signVal (g j) ≤
          gap p q * n / 2} = ⋃ i ∈ univ, bad i := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, mem_univ, exists_prop, true_and, bad]
  rw [hset]
  calc
    _ ≤ ∑ i : Fin n, ((coinLaw p q g).toOuterMeasure (bad i)).toReal := h
    _ ≤ ∑ _i : Fin n, 2 * Real.exp (-(gap p q) ^ 2 * n / 8) :=
      sum_le_sum fun i _ => coinLaw_low_margin_le p q g hgap i
    _ = _ := by simp; ring

end Cslib.Probability.StochasticBlockModel
