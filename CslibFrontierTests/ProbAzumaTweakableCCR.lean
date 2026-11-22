/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Crypto.Primitives.Garbling.BinaryToOneHotObliviousness
public import CslibFrontier.Crypto.Primitives.Garbling.CircularCorrelationRobust
public import CslibFrontier.Crypto.Primitives.Garbling.Switch.Oblivious
public import CslibFrontier.Probability.Azuma
public import CslibFrontier.Probability.Concentration
public import CslibFrontier.Probability.HockeyStick
public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.PMF.UniformBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Sequential Azuma–Hoeffding, hockey-stick divergence, `UniformBridge`, and tweak-unique CCR

Concrete checked instances for:
1. `Cslib.Probability.PMF.azuma_le` and `azuma_abs_le` on state-dependent walks over `ℤ` (without
   `[Fintype ℤ]` or `[MeasurableSpace ℤ]`), paired with an exact 2-step tail evaluation.
2. `Cslib.Probability.PMF.hockeyStick` on explicit Bernoulli coins (`3/4` vs `1/4`) across
   thresholds `c = 3, 2, 1`, data processing, and power-ratio moment bounds.
3. `Cslib.Probability.PMF.UniformBridge` on an explicit subset `{-3, -1, 2, 4} : Finset ℤ`.
4. `Cslib.Crypto.Garbling.CCR.idealFreshGame_eq_prfIdealGame_of_isTweakUnique` and
   `CCR.Arithmetic.idealGame_eq_runWith_memoize_of_isTweakUnique` on adaptive 2-query adversaries,
   plus an explicit counterexample showing `idealFreshGame ≠ eval ∘ PRF.idealExperiment` when a
   tweak is queried twice.
-/

public section

namespace CslibFrontierTests.ProbAzumaTweakableCCR

open Cslib Cslib.Crypto Cslib.Crypto.Garbling Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators ENNReal

/-! ### 1. Adaptive biased/fair walk and martingale walk on `ℤ` (`Probability.Azuma`) -/

/-- Biased probability `1 / 4` in `[0, 1]`. -/
noncomputable def quarterProb : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩

/-- Fair probability `1 / 2` in `[0, 1]`. -/
noncomputable def halfProb : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Biased probability `3 / 4` in `[0, 1]`. -/
noncomputable def threeQuarterProb : unitInterval := ⟨3 / 4, by norm_num, by norm_num⟩

/-- State-dependent walk on `ℤ`: from `s ≥ 0` it steps `+1` with probability `1/4` and `-1` with
probability `3/4` (drift `-1/2`); from `s < 0` it steps `±1` with a fair coin (drift `0`). -/
noncomputable def adaptiveWalkStep (_ : ℕ) (s : ℤ) : PMF ℤ :=
  (coin (if 0 ≤ s then quarterProb else halfProb)).map fun b => s + if b then 1 else -1

private theorem adaptiveWalkStep_apply (i : ℕ) (s s' : ℤ) :
    adaptiveWalkStep i s s' =
      (if s' = s + 1 then (coin (if 0 ≤ s then quarterProb else halfProb)) true else 0) +
      (if s' = s - 1 then (coin (if 0 ≤ s then quarterProb else halfProb)) false else 0) := by
  rw [adaptiveWalkStep, _root_.PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true, sub_eq_add_neg]

private theorem adaptiveWalkStep_drift_nonpos (i : ℕ) (s : ℤ) :
    (∑' s' : ℤ, (adaptiveWalkStep i s s').toReal * ((s' : ℝ) - s)) ≤ 0 := by
  have hsupp : ∀ s' ∉ ({s + 1, s - 1} : Finset ℤ),
      (adaptiveWalkStep i s s').toReal * ((s' : ℝ) - s) = 0 := by
    intro s' hs'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs'
    rw [adaptiveWalkStep_apply, ite_eq_right hs'.1, ite_eq_right hs'.2, add_zero,
      ENNReal.toReal_zero, zero_mul]
  rw [tsum_eq_sum hsupp, Finset.sum_pair (by omega : s + 1 ≠ s - 1)]
  rw [adaptiveWalkStep_apply, adaptiveWalkStep_apply]
  have hne1 : s + 1 ≠ s - 1 := by omega
  have hne2 : s - 1 ≠ s + 1 := by omega
  simp only [↓reduceIte, hne1, hne2, add_zero, zero_add]
  by_cases hs : 0 ≤ s
  · simp only [hs, ↓reduceIte, coin_apply_toReal, quarterProb]
    push_cast
    linarith
  · simp only [hs, ↓reduceIte, coin_apply_toReal, halfProb]
    push_cast
    linarith

private theorem adaptiveWalkStep_range (i : ℕ) (s : ℤ) :
    ∃ a : ℝ, ∀ s' ∈ (adaptiveWalkStep i s).support, ((s' : ℝ) - s) ∈ Set.Icc a (a + 2) := by
  refine ⟨-1, fun s' hs' => ?_⟩
  rw [adaptiveWalkStep, _root_.PMF.mem_support_map_iff] at hs'
  obtain ⟨b, _, rfl⟩ := hs'
  cases b <;> constructor <;> push_cast <;> norm_num

/-- **Azuma–Hoeffding on an adaptive biased/fair walk over `ℤ`**: for every horizon `n` and
`ε ≥ 0`, the upper tail `Pr[X_n ≥ ε]` is at most `exp (-2 ε² / (4 n))`. -/
theorem adaptiveWalk_tail_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((chain (_root_.PMF.pure (0 : ℤ)) adaptiveWalkStep n).toOuterMeasure
        {s : ℤ | ε ≤ (s : ℝ)}).toReal ≤
      Real.exp (-2 * ε ^ 2 / (4 * n)) := by
  have h := azuma_le (_root_.PMF.pure (0 : ℤ)) adaptiveWalkStep (fun _ (s : ℤ) => (s : ℝ))
    (fun _ => 2) (m := 0) (ε := ε) n hε
    (fun s hs => by
      simp only [_root_.PMF.support_pure, Set.mem_singleton_iff] at hs
      simp [hs])
    (fun i _ s _ => adaptiveWalkStep_drift_nonpos i s)
    (fun i _ s _ => adaptiveWalkStep_range i s)
  have hev : {s : ℤ | (0 : ℝ) + ε ≤ (s : ℝ)} = {s : ℤ | ε ≤ (s : ℝ)} := by
    simp only [zero_add]
  rw [hev] at h
  refine h.trans_eq ?_
  congr 1
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Exact 2-step check: from `0`, reaching `s ≥ 2` in `2` steps requires two `+1` moves from
nonnegative states (`(1/4) * (1/4) = 1/16`), which is strictly below Azuma's `exp (-1)` bound. -/
theorem adaptiveWalk_two_step_ge_two :
    ((chain (_root_.PMF.pure (0 : ℤ)) adaptiveWalkStep 2).toOuterMeasure
        {s : ℤ | (2 : ℝ) ≤ (s : ℝ)}).toReal = 1 / 16 ∧
      ((chain (_root_.PMF.pure (0 : ℤ)) adaptiveWalkStep 2).toOuterMeasure
        {s : ℤ | (2 : ℝ) ≤ (s : ℝ)}).toReal ≤ Real.exp (-1) := by
  refine ⟨?_, ?_⟩
  · have hchain :
        chain (_root_.PMF.pure (0 : ℤ)) adaptiveWalkStep 2 =
          (adaptiveWalkStep 0 0).bind (adaptiveWalkStep 1) := by
      rw [chain_succ, chain_succ, chain_zero, _root_.PMF.pure_bind]
    rw [hchain, _root_.PMF.toOuterMeasure_bind_apply]
    have h0 : ∀ s ∉ ({1, -1} : Finset ℤ),
        adaptiveWalkStep 0 0 s * (adaptiveWalkStep 1 s).toOuterMeasure {s' : ℤ | (2 : ℝ) ≤ s'} =
          0 := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      rw [adaptiveWalkStep_apply, ite_eq_right (by omega), ite_eq_right (by omega), add_zero,
        zero_mul]
    rw [tsum_eq_sum h0, Finset.sum_pair (by decide : (1 : ℤ) ≠ -1)]
    have h1 : (adaptiveWalkStep 1 1).toOuterMeasure {s' : ℤ | (2 : ℝ) ≤ s'} =
        adaptiveWalkStep 1 1 2 := by
      rw [_root_.PMF.toOuterMeasure_apply, tsum_eq_single 2]
      · simp
      · intro s' hs'
        by_cases hle : s' ∈ {x : ℤ | (2 : ℝ) ≤ (x : ℝ)}
        · have hs'2 : 2 < s' := by
            have : (2 : ℤ) ≤ s' := by exact_mod_cast hle
            omega
          rw [Set.indicator_of_mem hle, adaptiveWalkStep_apply,
            ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
        · exact Set.indicator_of_notMem hle _
    have hm1 : (adaptiveWalkStep 1 (-1)).toOuterMeasure {s' : ℤ | (2 : ℝ) ≤ s'} = 0 := by
      rw [_root_.PMF.toOuterMeasure_apply, tsum_eq_zero_iff]
      intro s'
      by_cases hle : s' ∈ {x : ℤ | (2 : ℝ) ≤ (x : ℝ)}
      · have : (2 : ℤ) ≤ s' := by exact_mod_cast hle
        rw [Set.indicator_of_mem hle, adaptiveWalkStep_apply,
          ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
      · exact Set.indicator_of_notMem hle _
    rw [h1, hm1, mul_zero, add_zero, ENNReal.toReal_mul]
    have hstep0 : adaptiveWalkStep 0 0 1 = coin quarterProb true := by
      rw [adaptiveWalkStep_apply]
      simp
    have hstep1 : adaptiveWalkStep 1 1 2 = coin quarterProb true := by
      rw [adaptiveWalkStep_apply]
      simp
    rw [hstep0, hstep1, coin_apply_toReal]
    simp only [↓reduceIte, quarterProb]
    norm_num
  · refine (adaptiveWalk_tail_le 2 (ε := 2) (by norm_num)).trans_eq ?_
    congr 1
    norm_num

/-- Adaptive zero-mean martingale step on `ℤ`: fair `±1` step on `s ≥ 0` and fair `±2` step on
`s < 0` (every step has conditional expectation `0` and range width at most `4`). -/
noncomputable def adaptiveMartingaleStep (_ : ℕ) (s : ℤ) : PMF ℤ :=
  let stepSize : ℤ := if 0 ≤ s then 1 else 2
  (coin halfProb).map fun b => s + if b then stepSize else -stepSize

/-- Two-sided Azuma–Hoeffding check (`azuma_abs_le`) on `adaptiveMartingaleStep`. -/
theorem adaptiveMartingale_abs_tail_le (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ((chain (_root_.PMF.pure (0 : ℤ)) adaptiveMartingaleStep n).toOuterMeasure
        {s : ℤ | ε ≤ |(s : ℝ)|}).toReal ≤
      2 * Real.exp (-2 * ε ^ 2 / (16 * n)) := by
  have h := azuma_abs_le (_root_.PMF.pure (0 : ℤ)) adaptiveMartingaleStep
    (fun _ (s : ℤ) => (s : ℝ)) (fun _ => 4) (m := 0) (ε := ε) n hε
    (fun s hs => by
      simp only [_root_.PMF.support_pure, Set.mem_singleton_iff] at hs
      simp [hs])
    (fun i _ s _ => by
      dsimp only [adaptiveMartingaleStep]
      set d : ℤ := if 0 ≤ s then 1 else 2
      have hd : s + d ≠ s + -d := by
        by_cases hs0 : 0 ≤ s <;> simp [d, hs0]
      have hsupp : ∀ s' ∉ ({s + d, s + -d} : Finset ℤ),
          (((coin halfProb).map fun b => s + if b then d else -d) s').toReal * ((s' : ℝ) - s) =
            0 := by
        intro s' hs'
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs'
        rw [_root_.PMF.map_apply, tsum_fintype, Fintype.sum_bool]
        simp only [↓reduceIte, Bool.false_eq_true]
        rw [ite_eq_right hs'.1, ite_eq_right hs'.2, add_zero, ENNReal.toReal_zero, zero_mul]
      rw [tsum_eq_sum hsupp, Finset.sum_pair hd, _root_.PMF.map_apply, _root_.PMF.map_apply,
        tsum_fintype, tsum_fintype, Fintype.sum_bool, Fintype.sum_bool]
      simp only [↓reduceIte, Bool.false_eq_true, hd, hd.symm, add_zero, zero_add,
        coin_apply_toReal, halfProb]
      push_cast
      ring)
    (fun i _ s _ => ⟨-2, fun s' hs' => by
      rw [adaptiveMartingaleStep, _root_.PMF.mem_support_map_iff] at hs'
      obtain ⟨b, _, rfl⟩ := hs'
      by_cases hs0 : 0 ≤ s <;> cases b <;> simp only [hs0, ↓reduceIte] <;>
        constructor <;> push_cast <;> norm_num⟩)
  have hev : {s : ℤ | ε ≤ |(s : ℝ) - 0|} = {s : ℤ | ε ≤ |(s : ℝ)|} := by
    simp only [sub_zero]
  rw [hev] at h
  refine h.trans_eq ?_
  congr 2
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-! ### 2. Explicit Bernoulli hockey-stick divergences (`Probability.HockeyStick`) -/

/-- Exact hockey-stick values for `coin (3/4)` vs `coin (1/4)` at `c = 3`, `c = 2`, and `c = 1`. -/
theorem hockeyStick_bernoulli_values :
    hockeyStick 3 (coin threeQuarterProb) (coin quarterProb) = 0 ∧
      hockeyStick 2 (coin threeQuarterProb) (coin quarterProb) = 1 / 4 ∧
      hockeyStick 1 (coin threeQuarterProb) (coin quarterProb) = 1 / 2 ∧
      CloseTo (coin threeQuarterProb) (coin quarterProb) (1 / 2) := by
  have h3 : hockeyStick 3 (coin threeQuarterProb) (coin quarterProb) = 0 := by
    rw [hockeyStick_eq_zero_iff]
    intro b
    cases b <;> simp only [coin_apply, ↓reduceIte, Bool.false_eq_true,
      threeQuarterProb, quarterProb]
    · rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    · rw [← ENNReal.ofReal_ofNat 3, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h2 : hockeyStick 2 (coin threeQuarterProb) (coin quarterProb) = 1 / 4 := by
    rw [hockeyStick_eq_sum, Fintype.sum_bool]
    have hfalse : coin threeQuarterProb false - 2 * coin quarterProb false = 0 := by
      rw [tsub_eq_zero_iff_le, coin_apply, coin_apply]
      simp only [Bool.false_eq_true, ↓reduceIte, threeQuarterProb, quarterProb]
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    have htrue : coin threeQuarterProb true - 2 * coin quarterProb true = 1 / 4 := by
      rw [coin_apply, coin_apply]
      simp only [↓reduceIte, threeQuarterProb, quarterProb]
      rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_sub _ (by norm_num),
        show ((3 : ℝ) / 4 - 2 * (1 / 4)) = (4 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat, one_div]
    rw [htrue, hfalse, add_zero]
  have h1 : hockeyStick 1 (coin threeQuarterProb) (coin quarterProb) = 1 / 2 := by
    rw [hockeyStick_eq_sum, Fintype.sum_bool, one_mul, one_mul]
    have hfalse : coin threeQuarterProb false - coin quarterProb false = 0 := by
      rw [tsub_eq_zero_iff_le, coin_apply, coin_apply]
      simp only [Bool.false_eq_true, ↓reduceIte, threeQuarterProb, quarterProb]
      exact ENNReal.ofReal_le_ofReal (by norm_num)
    have htrue : coin threeQuarterProb true - coin quarterProb true = 1 / 2 := by
      rw [coin_apply, coin_apply]
      simp only [↓reduceIte, threeQuarterProb, quarterProb]
      rw [← ENNReal.ofReal_sub _ (by norm_num),
        show ((3 : ℝ) / 4 - 1 / 4) = (2 : ℝ)⁻¹ by norm_num,
        ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat, one_div]
    rw [htrue, hfalse, add_zero]
  exact ⟨h3, h2, h1, (hockeyStick_one_le_iff_closeTo _ _ _).mp h1.le⟩

/-- Data-processing check (`hockeyStick_bind_le`) on post-processing `coin (3/4)` and `coin (1/4)`
through a noisy flip channel. -/
example :
    let ch : Bool → PMF Bool := fun b => if b then coin threeQuarterProb else coin quarterProb
    hockeyStick 2 ((coin threeQuarterProb).bind ch) ((coin quarterProb).bind ch) ≤ 1 / 4 := by
  intro ch
  exact (hockeyStick_bind_le 2 (coin threeQuarterProb) (coin quarterProb) ch).trans_eq
    hockeyStick_bernoulli_values.2.1

/-! ### 3. `UniformBridge` on an explicit `Finset ℤ` -/

/-- Explicit four-element subset of `ℤ`. -/
def sampleInts : Finset ℤ := {-3, -1, 2, 4}

theorem sampleInts_nonempty : sampleInts.Nonempty := ⟨-3, by decide⟩

instance : Nonempty sampleInts := sampleInts_nonempty.to_subtype

/-- Checking `UniformBridge` expectation, subtype indicator density, and filter count on
`sampleInts = {-3, -1, 2, 4}`. -/
theorem uniformBridge_sampleInts_checks :
    (∑' z : ℤ, ((uniformOfFinset sampleInts sampleInts_nonempty) z).toReal *
        (z : ℝ) ^ 2) = 15 / 2 ∧
      (∑ x : sampleInts,
        if 0 < x.1 then ((uniformOfFintype sampleInts) x).toReal else 0) = 1 / 2 ∧
      ((sampleInts.filter (0 < ·)).card : ℝ) =
        sampleInts.card *
          ((uniformOfFinset sampleInts sampleInts_nonempty).toOuterMeasure
            {z : ℤ | 0 < z}).toReal := by
  refine ⟨?_, ?_, card_filter_eq_card_mul_toOuterMeasure_uniformOfFinset
    sampleInts sampleInts_nonempty (0 < ·)⟩
  · rw [tsum_uniformOfFinset_toReal_mul, Finset.expect_eq_sum_div_card]
    have hcard : (sampleInts.card : ℝ) = 4 := by
      exact_mod_cast (by decide : sampleInts.card = 4)
    have hsum : (∑ z ∈ sampleInts, (z : ℝ) ^ 2) = 30 := by
      have hval : (∑ z ∈ sampleInts, z ^ 2) = 30 := by decide
      exact_mod_cast hval
    rw [hcard, hsum]
    norm_num
  · rw [sum_subtype_uniformOfFintype_ite_toReal]
    have h1 : (sampleInts.filter (0 < ·)).card = 2 := by decide
    have h2 : sampleInts.card = 4 := by decide
    rw [h1, h2]
    norm_num

/-! ### 4. Fresh-ideal vs PRF-ideal under tweak uniqueness, and failure on repeated tweaks -/

/-- Adaptive 2-query Boolean CCR adversary: queries tweak `false`, then uses the reply `r₁` as both
the label and offset bit of a second query at fresh tweak `true`. -/
def adaptiveUniqueAdv : ProbOracleComp (fun _ : CCR.Query Bool Bool => Bool) Bool := do
  let r₁ ← ProbOracleComp.query ⟨false, false, false⟩
  let r₂ ← ProbOracleComp.query ⟨r₁, true, r₁⟩
  pure (r₁ == r₂)

theorem isTweakUnique_adaptiveUniqueAdv : CCR.IsTweakUnique adaptiveUniqueAdv := by
  intro t
  dsimp only [adaptiveUniqueAdv]
  refine ((ProbOracleComp.isCostBounded_query
    (spec := fun _ : CCR.Query Bool Bool => Bool)
    (fun q : CCR.Query Bool Bool => if q.tweak = t then 1 else 0)
    ⟨false, false, false⟩).bind (m := if true = t then 1 else 0) fun r₁ =>
    ((ProbOracleComp.isCostBounded_query
      (spec := fun _ : CCR.Query Bool Bool => Bool)
      (fun q : CCR.Query Bool Bool => if q.tweak = t then 1 else 0)
      ⟨r₁, true, r₁⟩).bind fun r₂ =>
      OracleComp.IsCostBounded.pure (r₁ == r₂) 0).mono (by simp)).mono ?_
  cases t <;> simp

/-- Because `adaptiveUniqueAdv` never repeats a tweak, answering its queries with fresh uniform bits
equals running `PRF.idealExperiment`. -/
theorem idealFreshGame_adaptiveUniqueAdv :
    CCR.idealFreshGame adaptiveUniqueAdv = ProbComp.eval (PRF.idealExperiment adaptiveUniqueAdv) :=
  CCR.idealFreshGame_eq_prfIdealGame_of_isTweakUnique isTweakUnique_adaptiveUniqueAdv

/-- Adaptive 2-query arithmetic CCR adversary over `ZMod 4`: queries tweak `0`, then adaptively
queries label `r₁` with shift `r₁ + 1` at tweak `1`. -/
def arithUniqueAdv : ProbOracleComp (fun _ : CCR.Arithmetic.Query (ZMod 4) (ZMod 4) => ZMod 4)
    Bool := do
  let r₁ ← ProbOracleComp.query ⟨0, 0, 1⟩
  let r₂ ← ProbOracleComp.query ⟨r₁, 1, r₁ + 1⟩
  pure (decide (r₁ + r₂ = 0))

theorem isTweakUnique_arithUniqueAdv : CCR.Arithmetic.IsTweakUnique arithUniqueAdv := by
  intro t
  dsimp only [arithUniqueAdv]
  refine ((ProbOracleComp.isCostBounded_query
    (spec := fun _ : CCR.Arithmetic.Query (ZMod 4) (ZMod 4) => ZMod 4)
    (fun q : CCR.Arithmetic.Query (ZMod 4) (ZMod 4) => if q.tweak = t then 1 else 0)
    ⟨0, 0, 1⟩).bind (m := if 1 = t then 1 else 0) fun r₁ =>
    ((ProbOracleComp.isCostBounded_query
      (spec := fun _ : CCR.Arithmetic.Query (ZMod 4) (ZMod 4) => ZMod 4)
      (fun q : CCR.Arithmetic.Query (ZMod 4) (ZMod 4) => if q.tweak = t then 1 else 0)
      ⟨r₁, 1, r₁ + 1⟩).bind fun r₂ =>
      OracleComp.IsCostBounded.pure (decide (r₁ + r₂ = 0)) 0).mono (by simp)).mono ?_
  by_cases h0 : 0 = t <;> by_cases h1 : 1 = t <;> simp_all

/-- Arithmetic CCR tweak-uniqueness equivalence on `arithUniqueAdv`. -/
theorem idealGame_arithUniqueAdv_eq_memoize :
    CCR.Arithmetic.idealGame arithUniqueAdv =
      (ProbOracleComp.runWith
        (memoize fun _ : CCR.Arithmetic.Query (ZMod 4) (ZMod 4) =>
          uniformOfFintype (ZMod 4))
        arithUniqueAdv []).map Prod.fst :=
  CCR.Arithmetic.idealGame_eq_runWith_memoize_of_isTweakUnique isTweakUnique_arithUniqueAdv

/-- Non-tweak-unique adversary that queries the same tweak `false` twice and tests equality of the
two replies. -/
def repeatTweakAdv : ProbOracleComp (fun _ : CCR.Query Bool Bool => Bool) Bool := do
  let r₁ ← ProbOracleComp.query ⟨false, false, false⟩
  let r₂ ← ProbOracleComp.query ⟨false, false, false⟩
  pure (r₁ == r₂)

/-- `repeatTweakAdv` violates `CCR.IsTweakUnique`. -/
theorem not_isTweakUnique_repeatTweakAdv : ¬ CCR.IsTweakUnique repeatTweakAdv := by
  intro h
  have h1 := h false
  dsimp only [repeatTweakAdv, ProbOracleComp.query] at h1
  obtain ⟨_, hcont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h1
  have h2 := hcont (false : Bool)
  simp only [Sum.elim_inr, ↓reduceIte, Nat.sub_self] at h2
  obtain ⟨hle, _⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h2
  simp at hle

/-- **Failure without tweak uniqueness**: against a random function (`PRF.idealExperiment`),
`repeatTweakAdv` outputs `true` with probability `1`, whereas against fresh uniform answers
(`CCR.idealFreshGame`) it outputs `true` with probability `1 / 2`; hence the two games differ. -/
theorem idealFreshGame_repeatTweakAdv_ne_prfIdealGame :
    (ProbComp.eval (PRF.idealExperiment repeatTweakAdv) true).toReal = 1 ∧
      (CCR.idealFreshGame repeatTweakAdv true).toReal = 1 / 2 ∧
      CCR.idealFreshGame repeatTweakAdv ≠ ProbComp.eval (PRF.idealExperiment repeatTweakAdv) := by
  have hprf : (ProbComp.eval (PRF.idealExperiment repeatTweakAdv) true).toReal = 1 := by
    simp only [PRF.idealExperiment, repeatTweakAdv, ProbOracleComp.run_bind,
      ProbOracleComp.run_query, ProbOracleComp.run_pure, pure_bind, beq_self_eq_true,
      ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure, _root_.PMF.bind_const,
      _root_.PMF.pure_apply, ↓reduceIte, ENNReal.toReal_one]
  have hfresh : (CCR.idealFreshGame repeatTweakAdv true).toReal = 1 / 2 := by
    simp only [CCR.idealFreshGame, repeatTweakAdv, ProbOracleComp.run_bind,
      ProbOracleComp.run_query, ProbOracleComp.run_pure, ProbComp.eval_bind,
      ProbComp.eval_uniform, ProbComp.eval_pure, _root_.PMF.bind_apply,
      uniformOfFintype_apply, _root_.PMF.pure_apply, Fintype.card_bool,
      tsum_fintype, Fintype.sum_bool]
    simp only [Bool.true_beq, Bool.false_beq, Bool.not_true, Bool.not_false, Bool.true_eq_false,
      ↓reduceIte, mul_one, mul_zero, add_zero, zero_add]
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top (by simp) (by simp))
      (ENNReal.mul_ne_top (by simp) (by simp)),
      ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    norm_num
  refine ⟨hprf, hfresh, fun heq => ?_⟩
  have hcongr := congrArg (fun g : Game => (g true).toReal) heq
  linarith

end CslibFrontierTests.ProbAzumaTweakableCCR
