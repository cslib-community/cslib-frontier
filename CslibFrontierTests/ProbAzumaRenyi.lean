/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.MachineLearning.Replicable.BiasEstimation
public import CslibFrontier.Privacy.DifferentialPrivacy.RandomizedResponse
public import CslibFrontier.Privacy.DifferentialPrivacy.Renyi
public import CslibFrontier.Probability.Azuma
public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.Renyi
public import CslibFrontier.Probability.StochasticDomination.Adapted
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Sequential `PMF` Azuma–Hoeffding and Rényi divergence: checked instances

Concrete checked instances for:
1. `Cslib.Probability.PMF.seqProcess` (`seqProcess_apply`, `seqProcess_mul_exp_le`,
   `seqProcess_ge_le`, `seqProcess_le_le`, `seqProcess_abs_sub_ge_le`) on a stateful adaptive
   random walk over `ℤ` (without `[Fintype ℤ]` or `[MeasurableSpace ℤ]`) whose step distribution
   switches between `{-1, 3}` and `{-2, 2}` depending on the sign of the current cumulative sum,
   plus `seqCount_ge_le` / `seqCount_le_le` and infinite-domain `boundedMean_concentrates`.
2. `Cslib.Probability.renyiMoment` and `Cslib.Probability.PMF.renyiDiv`: exact order-`2` value
   `log (7 / 3)` on Bernoulli `(3 / 4, 1 / 4)` vs `(1 / 4, 3 / 4)`, off-support `⊤` behavior,
   data processing (`renyiDiv_bind_le`, `renyiDiv_map_le`), adaptive two-stage composition
   (`renyiDiv_bind_pair_le`), `hockeyStick_le_of_renyiDiv_le` conversion, and
   `Cslib.Privacy.RenyiDifferentiallyPrivate` on `randomizedResponse` and
   `randomizedResponseSurvey`.
-/

public section

namespace CslibFrontierTests.ProbAzumaRenyi

open Cslib Cslib.Privacy Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators ENNReal

/-! ### 1. Stateful adaptive walk on `ℤ` (`Probability.Azuma`) -/

/-- Biased probability `1 / 4` in `[0, 1]`. -/
noncomputable def quarterProb : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩

/-- Fair probability `1 / 2` in `[0, 1]`. -/
noncomputable def halfProb : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Biased probability `3 / 4` in `[0, 1]`. -/
noncomputable def threeQuarterProb : unitInterval := ⟨3 / 4, by norm_num, by norm_num⟩

/-- Asymmetric zero-mean step on `{-1, 3} ⊂ ℤ` (`P(3) = 1/4`, `P(-1) = 3/4`, width `4`). -/
noncomputable def asymStep : PMF ℤ :=
  (coin quarterProb).map fun b => if b then 3 else -1

/-- Symmetric zero-mean step on `{-2, 2} ⊂ ℤ` (`P(2) = 1/2`, `P(-2) = 1/2`, width `4`). -/
noncomputable def symStep : PMF ℤ :=
  (coin halfProb).map fun b => if b then 2 else -2

/-- Stateful adaptive transition kernel on `ℤ`: chooses `asymStep` when the running sum of the
prefix `h : Fin t → ℤ` is nonnegative and `symStep` when the running sum is negative. -/
noncomputable def adaptiveWalkStep (t : ℕ) (h : Fin t → ℤ) : PMF ℤ :=
  if 0 ≤ ∑ j : Fin t, h j then asymStep else symStep

/-- Cumulative real position of a trajectory `h : Fin k → ℤ`. -/
def walkPos (k : ℕ) (h : Fin k → ℤ) : ℝ :=
  ∑ j : Fin k, (h j : ℝ)

private theorem asymStep_apply (z : ℤ) :
    asymStep z =
      (if z = 3 then (1 / 4 : ℝ≥0∞) else 0) + (if z = -1 then (3 / 4 : ℝ≥0∞) else 0) := by
  rw [asymStep, _root_.PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  have h14 : coin quarterProb true = 1 / 4 := by
    rw [coin_apply]; simp only [↓reduceIte, quarterProb]; ennreal_to_real
  have h34 : coin quarterProb false = 3 / 4 := by
    rw [coin_apply]; simp only [Bool.false_eq_true, ↓reduceIte, quarterProb]
    ennreal_to_real; norm_num
  simp only [↓reduceIte, Bool.false_eq_true, h14, h34]

private theorem symStep_apply (z : ℤ) :
    symStep z =
      (if z = 2 then (1 / 2 : ℝ≥0∞) else 0) + (if z = -2 then (1 / 2 : ℝ≥0∞) else 0) := by
  rw [symStep, _root_.PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  have h1 : coin halfProb true = 1 / 2 := by
    rw [coin_apply]; simp only [↓reduceIte, halfProb]; ennreal_to_real
  have h2 : coin halfProb false = 1 / 2 := by
    rw [coin_apply]; simp only [Bool.false_eq_true, ↓reduceIte, halfProb]
    ennreal_to_real; norm_num
  simp only [↓reduceIte, Bool.false_eq_true, h1, h2]

private theorem tsum_asymStep_add (c : ℝ) :
    (∑' z : ℤ, (asymStep z).toReal * (c + (z : ℝ))) = c := by
  have hsupp : ∀ z ∉ ({3, -1} : Finset ℤ), (asymStep z).toReal * (c + (z : ℝ)) = 0 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    rw [asymStep_apply, ite_eq_right hz.1, ite_eq_right hz.2, add_zero, ENNReal.toReal_zero,
      zero_mul]
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by decide : (3 : ℤ) ≠ -1), asymStep_apply,
    asymStep_apply]
  simp only [↓reduceIte, show (3 : ℤ) ≠ -1 by decide, show (-1 : ℤ) ≠ 3 by decide, add_zero,
    zero_add]
  have h14 : ((1 / 4 : ℝ≥0∞)).toReal = 1 / 4 := by norm_num
  have h34 : ((3 / 4 : ℝ≥0∞)).toReal = 3 / 4 := by norm_num
  rw [h14, h34]
  push_cast
  ring

private theorem tsum_symStep_add (c : ℝ) :
    (∑' z : ℤ, (symStep z).toReal * (c + (z : ℝ))) = c := by
  have hsupp : ∀ z ∉ ({2, -2} : Finset ℤ), (symStep z).toReal * (c + (z : ℝ)) = 0 := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
    rw [symStep_apply, ite_eq_right hz.1, ite_eq_right hz.2, add_zero, ENNReal.toReal_zero,
      zero_mul]
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by decide : (2 : ℤ) ≠ -2), symStep_apply, symStep_apply]
  simp only [↓reduceIte, show (2 : ℤ) ≠ -2 by decide, show (-2 : ℤ) ≠ 2 by decide, add_zero,
    zero_add]
  have h12 : ((1 / 2 : ℝ≥0∞)).toReal = 1 / 2 := by norm_num
  rw [h12]
  push_cast
  ring

private theorem walkPos_snoc (k : ℕ) (h : Fin k → ℤ) (z : ℤ) :
    walkPos (k + 1) (Fin.snoc h z) = walkPos k h + (z : ℝ) := by
  simp only [walkPos, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

private theorem adaptiveWalk_martingale (k : ℕ) (h : Fin k → ℤ) :
    (∑' z : ℤ, ((adaptiveWalkStep k h) z).toReal * walkPos (k + 1) (Fin.snoc h z)) =
      walkPos k h := by
  simp_rw [walkPos_snoc, adaptiveWalkStep]
  split_ifs
  · exact tsum_asymStep_add (walkPos k h)
  · exact tsum_symStep_add (walkPos k h)

private theorem adaptiveWalk_range (k : ℕ) (h : Fin k → ℤ) :
    ∃ a b : ℝ, b - a ≤ 4 ∧
      ∀ z ∈ (adaptiveWalkStep k h).support, walkPos (k + 1) (Fin.snoc h z) ∈ Set.Icc a b := by
  dsimp only [adaptiveWalkStep]
  split_ifs
  · refine ⟨walkPos k h - 1, walkPos k h + 3, by linarith, fun z hz => ?_⟩
    rw [asymStep, _root_.PMF.mem_support_map_iff] at hz
    obtain ⟨b, _, rfl⟩ := hz
    rw [walkPos_snoc]
    cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> constructor <;> push_cast <;>
      linarith
  · refine ⟨walkPos k h - 2, walkPos k h + 2, by linarith, fun z hz => ?_⟩
    rw [symStep, _root_.PMF.mem_support_map_iff] at hz
    obtain ⟨b, _, rfl⟩ := hz
    rw [walkPos_snoc]
    cases b <;> simp only [↓reduceIte, Bool.false_eq_true] <;> constructor <;> push_cast <;>
      linarith

/-- Explicit trajectory masses showing `seqProcess adaptiveWalkStep 2` is genuinely stateful
(`![3, -1]` stays in `asymStep` with mass `(1/4)*(3/4) = 3/16`, whereas `![-1, 2]` switches to
`symStep` at step `1` with mass `(3/4)*(1/2) = 3/8`), together with MGF and Azuma–Hoeffding tail
bounds over `8` adaptive steps on `ℤ`. -/
theorem adaptiveWalk_azuma_check :
    seqProcess adaptiveWalkStep 2 ![3, -1] = 3 / 16 ∧
      seqProcess adaptiveWalkStep 2 ![-1, 2] = 3 / 8 ∧
      (∑' h : Fin 8 → ℤ, seqProcess adaptiveWalkStep 8 h *
        ENNReal.ofReal (Real.exp ((1 / 2 : ℝ) * walkPos 8 h))) ≤
        ENNReal.ofReal (Real.exp 4) ∧
      ((seqProcess adaptiveWalkStep 8).toOuterMeasure {h | 8 ≤ walkPos 8 h}).toReal ≤
        Real.exp (-1) ∧
      ((seqProcess adaptiveWalkStep 8).toOuterMeasure {h | walkPos 8 h ≤ -8}).toReal ≤
        Real.exp (-1) ∧
      ((seqProcess adaptiveWalkStep 8).toOuterMeasure {h | 8 ≤ |walkPos 8 h|}).toReal ≤
        2 * Real.exp (-1) := by
  have htraj1 : seqProcess adaptiveWalkStep 2 ![3, -1] = 3 / 16 := by
    rw [seqProcess_apply, Fin.prod_univ_two]
    have hp1 : (fun j : Fin 1 => (![3, -1] : Fin 2 → ℤ)
        (Fin.castLT j (lt_trans j.isLt (by decide : 1 < 2)))) = ![3] :=
      funext fun j => by fin_cases j; rfl
    simp only [Fin.val_zero, Fin.val_one, hp1, adaptiveWalkStep, Fin.sum_univ_zero,
      Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, le_refl,
      show (0 : ℤ) ≤ 3 by decide, ↓reduceIte, asymStep_apply,
      show (3 : ℤ) ≠ -1 by decide, show (-1 : ℤ) ≠ 3 by decide, add_zero, zero_add]
    ennreal_to_real
    norm_num
  have htraj2 : seqProcess adaptiveWalkStep 2 ![-1, 2] = 3 / 8 := by
    rw [seqProcess_apply, Fin.prod_univ_two]
    have hp2 : (fun j : Fin 1 => (![-1, 2] : Fin 2 → ℤ)
        (Fin.castLT j (lt_trans j.isLt (by decide : 1 < 2)))) = ![-1] :=
      funext fun j => by fin_cases j; rfl
    simp only [Fin.val_zero, Fin.val_one, hp2, adaptiveWalkStep, Fin.sum_univ_zero,
      Fin.sum_univ_one, Matrix.cons_val_zero, Matrix.cons_val_one, le_refl,
      show ¬(0 : ℤ) ≤ -1 by decide, ↓reduceIte, asymStep_apply, symStep_apply,
      show (-1 : ℤ) ≠ 3 by decide, show (2 : ℤ) ≠ -2 by decide, add_zero, zero_add]
    ennreal_to_real
    norm_num
  have hmgf := seqProcess_mul_exp_le adaptiveWalkStep walkPos (fun _ => 4) 8
    (fun k _ h _ => (adaptiveWalk_martingale k h).le)
    (fun k _ h _ => adaptiveWalk_range k h) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  simp only [walkPos, Fin.sum_univ_zero, sub_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hmgf
  have hge := seqProcess_ge_le adaptiveWalkStep walkPos (fun _ => 4) 8
    (fun k _ h _ => (adaptiveWalk_martingale k h).le)
    (fun k _ h _ => adaptiveWalk_range k h) (by norm_num : (0 : ℝ) ≤ 8)
  simp only [walkPos, Fin.sum_univ_zero, zero_add, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hge
  have hle := seqProcess_le_le adaptiveWalkStep walkPos (fun _ => 4) 8
    (fun k _ h _ => (adaptiveWalk_martingale k h).ge)
    (fun k _ h _ => adaptiveWalk_range k h) (by norm_num : (0 : ℝ) ≤ 8)
  simp only [walkPos, Fin.sum_univ_zero, zero_sub, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hle
  have habs := seqProcess_abs_sub_ge_le adaptiveWalkStep walkPos (fun _ => 4) 8
    (fun k _ h _ => adaptiveWalk_martingale k h)
    (fun k _ h _ => adaptiveWalk_range k h) (by norm_num : (0 : ℝ) ≤ 8)
  simp only [walkPos, Fin.sum_univ_zero, sub_zero, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at habs
  exact ⟨htraj1, htraj2,
    hmgf.trans_eq (congrArg (ENNReal.ofReal ∘ Real.exp) (by norm_num)),
    hge.trans_eq (congrArg Real.exp (by norm_num)),
    hle.trans_eq (congrArg Real.exp (by norm_num)),
    habs.trans_eq (by congr 2; norm_num)⟩

/-- Sequential Azuma event-count tails (`seqCount_ge_le`, `seqCount_le_le`) on `adaptiveWalkStep`
for the event `{z | 0 < z}` (whose conditional probability is `1 / 4` under `asymStep` and `1 / 2`
under `symStep`, hence always in `[1 / 4, 1 / 2]`), plus infinite-domain
`MachineLearning.Replicable.boundedMean_concentrates` on `PMF ℤ`. -/
theorem seqCount_and_infinite_domain_mean_check :
    (((seqProcess adaptiveWalkStep 8).toOuterMeasure
      {h | 6 ≤ (seqCount (fun _ _ => {z : ℤ | 0 < z}) 8 h : ℝ)}).toReal ≤ Real.exp (-1)) ∧
    (((seqProcess adaptiveWalkStep 8).toOuterMeasure
      {h | (seqCount (fun _ _ => {z : ℤ | 0 < z}) 8 h : ℝ) ≤ 0}).toReal ≤ Real.exp (-1)) ∧
    ((iid asymStep 8).toOuterMeasure
      {S : Fin 8 → ℤ |
        (1 / 2 : ℝ) <
          |MachineLearning.Replicable.empiricalMean (fun z : ℤ => if z = 3 then (1 : ℝ) else 0) S -
            (1 / 4 : ℝ)|}).toReal ≤ 2 * Real.exp (-4) := by
  have hpos_asym : (asymStep.toOuterMeasure {z : ℤ | 0 < z}).toReal = 1 / 4 := by
    rw [asymStep, _root_.PMF.toOuterMeasure_map_apply,
      show (fun b : Bool => if b then (3 : ℤ) else -1) ⁻¹' {z : ℤ | 0 < z} = {true} by
        ext b; cases b <;> simp,
      _root_.PMF.toOuterMeasure_apply_singleton, coin_apply_toReal]
    simp [quarterProb]
  have hpos_sym : (symStep.toOuterMeasure {z : ℤ | 0 < z}).toReal = 1 / 2 := by
    rw [symStep, _root_.PMF.toOuterMeasure_map_apply,
      show (fun b : Bool => if b then (2 : ℤ) else -2) ⁻¹' {z : ℤ | 0 < z} = {true} by
        ext b; cases b <;> simp,
      _root_.PMF.toOuterMeasure_apply_singleton, coin_apply_toReal]
    simp [halfProb]
  have hcount_hi := seqCount_ge_le adaptiveWalkStep (fun _ _ => {z : ℤ | 0 < z})
    (fun _ => (1 / 2 : ℝ)) 8 (fun t _ h _ => by
      dsimp only [adaptiveWalkStep]
      split_ifs
      · rw [hpos_asym]; norm_num
      · rw [hpos_sym])
    (by norm_num : (0 : ℝ) ≤ 2)
  have hcount_lo := seqCount_le_le adaptiveWalkStep (fun _ _ => {z : ℤ | 0 < z})
    (fun _ => (1 / 4 : ℝ)) 8 (fun t _ h _ => by
      dsimp only [adaptiveWalkStep]
      split_ifs
      · rw [hpos_asym]
      · rw [hpos_sym]; norm_num)
    (by norm_num : (0 : ℝ) ≤ 2)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_ofNat,
    show (8 : ℝ) * (1 / 2) + 2 = 6 by norm_num,
    show (8 : ℝ) * (1 / 4) - 2 = 0 by norm_num,
    show -2 * (2 : ℝ) ^ 2 / 8 = -1 by norm_num] at hcount_hi hcount_lo
  have hexp_ind : MachineLearning.Replicable.distExpectation asymStep
      (fun z : ℤ => if z = 3 then (1 : ℝ) else 0) = 1 / 4 := by
    rw [MachineLearning.Replicable.distExpectation, tsum_eq_single (3 : ℤ) fun z hz => by
      simp [hz]]
    simp only [↓reduceIte, mul_one, asymStep_apply, show (3 : ℤ) ≠ -1 by decide, add_zero]
    norm_num
  have hconc := MachineLearning.Replicable.boundedMean_concentrates asymStep
    (fun z : ℤ => if z = 3 then (1 : ℝ) else 0) (a := 0) (b := 1)
    (fun z _ => by split_ifs <;> norm_num) 8 (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [hexp_ind] at hconc
  exact ⟨hcount_hi, hcount_lo, hconc.trans_eq (by congr 2; norm_num)⟩

/-! ### 2. Rényi divergence & Rényi differential privacy (`Probability.Renyi`, `Privacy.Renyi`) -/

/-- Exact order-`2` Rényi moment `7 / 3` and Rényi divergence `log (7 / 3)` between `coin (3 / 4)`
and `coin (1 / 4)`, together with off-support `renyiDiv 2 (pure true) (pure false) = ⊤`. -/
theorem renyiDiv_bernoulli_exact_and_off_support :
    renyiMoment 2 (coin threeQuarterProb) (coin quarterProb) = 7 / 3 ∧
      renyiDiv 2 (coin threeQuarterProb) (coin quarterProb) =
        ENNReal.ofReal (Real.log (7 / 3)) ∧
      renyiDiv 2 (_root_.PMF.pure true) (_root_.PMF.pure false) = ⊤ := by
  have hmom : renyiMoment 2 (coin threeQuarterProb) (coin quarterProb) = 7 / 3 := by
    rw [renyiMoment, tsum_fintype, Fintype.sum_bool, show (2 : ℝ) - 1 = 1 by norm_num]
    simp only [ENNReal.rpow_one, coin_apply, ↓reduceIte, Bool.false_eq_true, threeQuarterProb,
      quarterProb]
    ennreal_to_real
    norm_num
  have hdiv : renyiDiv 2 (coin threeQuarterProb) (coin quarterProb) =
      ENNReal.ofReal (Real.log (7 / 3)) := by
    have h73 : (7 / 3 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top (by norm_num) (by norm_num)
    simp only [renyiDiv, hmom, h73, ↓reduceIte]
    have htr : ((7 / 3 : ℝ≥0∞)).toReal = 7 / 3 := by norm_num
    rw [htr, show (2 : ℝ) - 1 = 1 by norm_num, div_one]
  have htop : renyiDiv 2 (_root_.PMF.pure true) (_root_.PMF.pure false) = ⊤ := by
    have hmom_top : renyiMoment 2 (_root_.PMF.pure true) (_root_.PMF.pure false) = ⊤ := by
      rw [renyiMoment, tsum_fintype, Fintype.sum_bool, show (2 : ℝ) - 1 = 1 by norm_num]
      simp
    simp [renyiDiv, hmom_top]
  exact ⟨hmom, hdiv, htop⟩

/-- Data processing (`renyiDiv_bind_le`, `renyiDiv_map_le`), adaptive two-stage composition
(`renyiDiv_bind_pair_le`), and Rényi-to-`hockeyStick` conversion (`hockeyStick_le_of_renyiDiv_le`)
on Bernoulli distributions at `α = 2`. -/
theorem renyiDiv_data_processing_composition_and_hockeyStick :
    (∀ K : Bool → PMF ℕ,
      renyiDiv 2 ((coin threeQuarterProb).bind K) ((coin quarterProb).bind K) ≤
        ENNReal.ofReal (Real.log (7 / 3))) ∧
    renyiDiv 2 ((coin threeQuarterProb).map fun _ => (0 : ℕ))
        ((coin quarterProb).map fun _ => (0 : ℕ)) = 0 ∧
    renyiDiv 2
        ((coin threeQuarterProb).bind fun b₁ =>
          (if b₁ then coin threeQuarterProb else coin quarterProb).bind fun b₂ =>
            _root_.PMF.pure (b₁, b₂))
        ((coin quarterProb).bind fun b₁ =>
          (if b₁ then coin quarterProb else coin threeQuarterProb).bind fun b₂ =>
            _root_.PMF.pure (b₁, b₂)) ≤
      ENNReal.ofReal (2 * Real.log (7 / 3)) ∧
    hockeyStick (14 / 3) (coin threeQuarterProb) (coin quarterProb) ≤ 1 / 2 := by
  have hbase := renyiDiv_bernoulli_exact_and_off_support.2.1
  have hrev : renyiDiv 2 (coin quarterProb) (coin threeQuarterProb) =
      ENNReal.ofReal (Real.log (7 / 3)) := by
    have hswap : coin quarterProb = (coin threeQuarterProb).map Bool.not := by
      ext b
      rw [_root_.PMF.map_apply, tsum_fintype, Fintype.sum_bool]
      cases b <;>
        simp only [coin_apply, quarterProb, threeQuarterProb, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, add_zero, zero_add] <;>
        ennreal_to_real <;> norm_num
    have hswap2 : coin threeQuarterProb = (coin quarterProb).map Bool.not := by
      ext b
      rw [_root_.PMF.map_apply, tsum_fintype, Fintype.sum_bool]
      cases b <;>
        simp only [coin_apply, quarterProb, threeQuarterProb, Bool.not_true, Bool.not_false,
          Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, add_zero, zero_add] <;>
        ennreal_to_real <;> norm_num
    apply le_antisymm
    · have hm := renyiDiv_map_le one_lt_two (coin threeQuarterProb) (coin quarterProb) Bool.not
      rwa [← hswap, ← hswap2, hbase] at hm
    · have hm := renyiDiv_map_le one_lt_two (coin quarterProb) (coin threeQuarterProb) Bool.not
      rwa [← hswap2, ← hswap, hbase] at hm
  have hlog_nn : 0 ≤ Real.log (7 / 3) := Real.log_nonneg (by norm_num)
  refine ⟨fun K => (renyiDiv_bind_le one_lt_two _ _ K).trans_eq hbase, ?_, ?_, ?_⟩
  · change renyiDiv 2 ((coin threeQuarterProb).map (Function.const Bool (0 : ℕ)))
      ((coin quarterProb).map (Function.const Bool (0 : ℕ))) = 0
    rw [_root_.PMF.map_const, _root_.PMF.map_const, renyiDiv_self]
  · have hpair := renyiDiv_bind_pair_le one_lt_two (coin threeQuarterProb) (coin quarterProb)
      (K := fun b₁ => if b₁ then coin threeQuarterProb else coin quarterProb)
      (L := fun b₁ => if b₁ then coin quarterProb else coin threeQuarterProb)
      (B := ENNReal.ofReal (Real.log (7 / 3))) fun b₁ _ => by
        cases b₁ <;> simp [hbase, hrev]
    refine hpair.trans_eq ?_
    rw [hbase, ← ENNReal.ofReal_add hlog_nn hlog_nn]
    exact congrArg ENNReal.ofReal (by ring)
  · have hhs := hockeyStick_le_of_renyiDiv_le one_lt_two hlog_nn (by norm_num : (0 : ℝ) < 1 / 2)
      hbase.le
    have hc : ENNReal.ofReal (Real.exp (Real.log (7 / 3) + Real.log (1 / (1 / 2)) / (2 - 1))) =
        (14 / 3 : ℝ≥0∞) := by
      rw [show (1 : ℝ) / (1 / 2) = 2 by norm_num, show (2 : ℝ) - 1 = 1 by norm_num, div_one,
        Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by norm_num)]
      ennreal_to_real
      norm_num
    have hd : ENNReal.ofReal (1 / 2 : ℝ) = 1 / 2 := by ennreal_to_real
    rwa [hc, hd] at hhs

/-- `RenyiDifferentiallyPrivate` on `randomizedResponse` (`(2, log (7 / 3))`-RDP, strictly tighter
than `(2, (log 3)²)` from generic pure-DP conversion), `n`-respondent `randomizedResponseSurvey`,
`k`-round adaptive composition, and conversion to `(ε', δ)`-DP. -/
theorem randomizedResponse_rdp_composition_and_dp_conversion (n k : ℕ) :
    RenyiDifferentiallyPrivate (fun _ _ => True)
      (fun b => ProbComp.eval (randomizedResponse b)) 2 (Real.log (7 / 3)) ∧
    RenyiDifferentiallyPrivate HammingAdjacent
      (fun x : Fin n → Bool => ProbComp.eval (randomizedResponseSurvey x)) 2
      (Real.log (7 / 3)) ∧
    RenyiDifferentiallyPrivate (fun _ _ => True)
      (Privacy.adaptiveComposition
        (fun (_ : List Bool) b => ProbComp.eval (randomizedResponse b)) k) 2
      (k * Real.log (7 / 3)) ∧
    DifferentiallyPrivate (fun _ _ => True)
      (Privacy.adaptiveComposition
        (fun (_ : List Bool) b => ProbComp.eval (randomizedResponse b)) k)
      (k * Real.log (7 / 3) + Real.log 8) (1 / 8) := by
  have hrdp1 : RenyiDifferentiallyPrivate (fun _ _ => True)
      (fun b => ProbComp.eval (randomizedResponse b)) 2 (Real.log (7 / 3)) := by
    have h := renyiDifferentiallyPrivate_randomizedResponse one_lt_two
    refine h.mono (le_of_eq ?_)
    norm_num
  have hrdp_survey : RenyiDifferentiallyPrivate HammingAdjacent
      (fun x : Fin n → Bool => ProbComp.eval (randomizedResponseSurvey x)) 2
      (Real.log (7 / 3)) := by
    have h := renyiDifferentiallyPrivate_randomizedResponseSurvey n one_lt_two
    refine h.mono (le_of_eq ?_)
    norm_num
  have hlog_nn : 0 ≤ Real.log (7 / 3) := Real.log_nonneg (by norm_num)
  have hrdp_comp : RenyiDifferentiallyPrivate (fun _ _ => True)
      (Privacy.adaptiveComposition
        (fun (_ : List Bool) b => ProbComp.eval (randomizedResponse b)) k) 2
      (k * Real.log (7 / 3)) := by
    have h := RenyiDifferentiallyPrivate.adaptiveComposition (ε := fun _ => Real.log (7 / 3))
      one_lt_two k (fun _ _ => hlog_nn) (fun _ _ => hrdp1)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  have hdp : DifferentiallyPrivate (fun _ _ => True)
      (Privacy.adaptiveComposition
        (fun (_ : List Bool) b => ProbComp.eval (randomizedResponse b)) k)
      (k * Real.log (7 / 3) + Real.log 8) (1 / 8) := by
    have h := hrdp_comp.differentiallyPrivate one_lt_two (mul_nonneg k.cast_nonneg hlog_nn)
      (by norm_num : (0 : ℝ) < 1 / 8)
    have h18 : ENNReal.ofReal (1 / 8 : ℝ) = 1 / 8 := by ennreal_to_real
    rw [h18] at h
    exact h.mono (le_of_eq (by norm_num)) le_rfl
  exact ⟨hrdp1, hrdp_survey, hrdp_comp, hdp⟩

end CslibFrontierTests.ProbAzumaRenyi
