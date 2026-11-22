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
public import CslibFrontier.Probability.Concentration
public import CslibFrontier.Probability.HockeyStick
public import CslibFrontier.Probability.HoeffdingStep
public import CslibFrontier.Probability.PMF.Coin
public import CslibFrontier.Probability.PMF.UniformBridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Hoeffding's centered MGF step, hockey-stick divergence, `UniformBridge`, and tweak-unique CCR

Concrete checked instances for:
1. `Cslib.Probability.PMF.tsum_mul_exp_sub_mean_le` on a 2-point `PMF ℤ` supported on `{-1, 3}`
   (without `[Fintype ℤ]` or `[MeasurableSpace ℤ]`) and
   `Cslib.Probability.PMF.sum_mul_exp_sub_mean_le` on a biased `±1` score under `coin (1/4)`.
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

/-! ### 1. Hoeffding's centered MGF bound on `ℤ` and `Bool` (`Probability.HoeffdingStep`) -/

/-- Biased probability `1 / 4` in `[0, 1]`. -/
noncomputable def quarterProb : unitInterval := ⟨1 / 4, by norm_num, by norm_num⟩

/-- Fair probability `1 / 2` in `[0, 1]`. -/
noncomputable def halfProb : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Biased probability `3 / 4` in `[0, 1]`. -/
noncomputable def threeQuarterProb : unitInterval := ⟨3 / 4, by norm_num, by norm_num⟩

/-- Asymmetric zero-mean law on `ℤ`: puts mass `1 / 4` on `3` and mass `3 / 4` on `-1` (range
`[-1, 3]` of width `4`, without `[Fintype ℤ]` or `[MeasurableSpace ℤ]`). -/
noncomputable def intTwoPoint : PMF ℤ :=
  (coin quarterProb).map fun b => if b then 3 else -1

private theorem intTwoPoint_apply (z : ℤ) :
    intTwoPoint z =
      (if z = 3 then coin quarterProb true else 0) +
      (if z = -1 then coin quarterProb false else 0) := by
  rw [intTwoPoint, _root_.PMF.map_apply, tsum_fintype, Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]

/-- Exact mean `0` and uncentered exponential moment bound `exp (2 t²)` on `ℤ` via
`tsum_mul_exp_sub_mean_le` (`(3 - (-1))² / 8 = 2`). -/
theorem intTwoPoint_mean_zero_and_mgf_le (t : ℝ) :
    (∑' z : ℤ, (intTwoPoint z).toReal * (z : ℝ)) = 0 ∧
      ∑' z : ℤ, intTwoPoint z * ENNReal.ofReal (Real.exp (t * (z : ℝ))) ≤
        ENNReal.ofReal (Real.exp (2 * t ^ 2)) := by
  have hmean : (∑' z : ℤ, (intTwoPoint z).toReal * (z : ℝ)) = 0 := by
    have hsupp : ∀ z ∉ ({3, -1} : Finset ℤ), (intTwoPoint z).toReal * (z : ℝ) = 0 := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hz
      rw [intTwoPoint_apply, ite_eq_right hz.1, ite_eq_right hz.2, add_zero, ENNReal.toReal_zero,
        zero_mul]
    rw [tsum_eq_sum hsupp, Finset.sum_pair (by decide : (3 : ℤ) ≠ -1), intTwoPoint_apply,
      intTwoPoint_apply]
    simp only [↓reduceIte, show (3 : ℤ) ≠ -1 by decide, show (-1 : ℤ) ≠ 3 by decide, add_zero,
      zero_add, coin_apply_toReal, quarterProb]
    norm_num
  refine ⟨hmean, ?_⟩
  have h := tsum_mul_exp_sub_mean_le intTwoPoint (fun z : ℤ => (z : ℝ)) (a := -1) (b := 3)
    (fun z hz => by
      rw [intTwoPoint, _root_.PMF.mem_support_map_iff] at hz
      obtain ⟨b, _, rfl⟩ := hz
      cases b <;> constructor <;> push_cast <;> norm_num) t
  simp only [hmean, sub_zero] at h
  refine h.trans_eq (congrArg (ENNReal.ofReal ∘ Real.exp) ?_)
  ring

/-- Finite centered MGF check (`sum_mul_exp_sub_mean_le`) on a `±1`-valued score under
`coin (1/4)` (mean `-1/2`, range `[-1, 1]` of width `2`):
`(1/4) exp (3 t / 2) + (3/4) exp (-t / 2) ≤ exp (t² / 2)`. -/
theorem biased_pm_one_centered_mgf_le (t : ℝ) :
    (1 / 4 : ℝ) * Real.exp (3 * t / 2) + (3 / 4 : ℝ) * Real.exp (-t / 2) ≤
      Real.exp (t ^ 2 / 2) := by
  have h := sum_mul_exp_sub_mean_le (coin quarterProb)
    (fun b : Bool => if b then (1 : ℝ) else -1) (a := -1) (b := 1)
    (fun b _ => by cases b <;> norm_num) t
  simp only [Fintype.sum_bool, coin_apply_toReal, quarterProb, ↓reduceIte, Bool.false_eq_true] at h
  refine (le_of_eq ?_).trans (h.trans_eq ?_)
  · congr 1 <;> congr 1 <;> congr 1 <;> ring
  · congr 1
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
