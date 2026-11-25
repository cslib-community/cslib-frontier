/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.FairDivision.Basic
public import CslibFrontier.GameTheory.FairDivision.Proportional
public import CslibFrontier.GameTheory.FairDivision.SelfridgeConway
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Cake-Cutting Protocol Witnesses and Boundary Tests

Representative ordinary-`module` client (`import` without `import all`) exercising
`CslibFrontier.GameTheory.FairDivision.{Basic,Proportional,SelfridgeConway}` on concrete affine and
piecewise-uniform valuations (including zero-density regions), explicit closed-form Robertson–Webb
oracles, Cut-and-Choose, the `2`-cut untrimmed and `5`-cut trimmed regimes of Selfridge–Conway,
`O(n²)` vs. `O(n log n)` query bounds for Dubins–Spanier and Even–Paz, and negative
fairness/separation counterexamples.
-/

public section

namespace CslibFrontierTests.FairDivision

open Cslib (FreeM)
open Cslib.GameTheory.FairDivision

/-! ### 1. Concrete Affine and Piecewise-Uniform Valuations -/

/-- Increasing linear density `f(x) = 2x` on `[0, 1]` (`CDF(x) = x²`). -/
noncomputable def incLinear : CakeValuation :=
  CakeValuation.affine 2 (by norm_num) (by norm_num)

/-- Decreasing linear density `f(x) = 2(1 - x)` on `[0, 1]` (`CDF(x) = 2x - x²`). -/
noncomputable def decLinear : CakeValuation :=
  CakeValuation.affine (-2) (by norm_num) (by norm_num)

/-- Strictly positive affine density `f(x) = 1/2 + x` on `[0, 1]`. -/
noncomputable def mildAffine : CakeValuation :=
  CakeValuation.affine 1 (by norm_num) (by norm_num)

/-- Piecewise-uniform valuation concentrated on `[0, 1/2]` (density `2` on `[0, 1/2]`, `0` on
`[1/2, 1]`). -/
noncomputable def leftHalf : CakeValuation :=
  CakeValuation.uniformOn 0 (1 / 2) (by norm_num) (by norm_num) (by norm_num)

/-- Piecewise-uniform valuation concentrated on `[1/2, 1]` (density `0` on `[0, 1/2]`, `2` on
`[1/2, 1]`). -/
noncomputable def rightHalf : CakeValuation :=
  CakeValuation.uniformOn (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)

/-- Piecewise-uniform valuation concentrated on `[0, 1/6]` (density `6` on `[0, 1/6]`, `0` on
`[1/6, 1]`). -/
noncomputable def firstSixth : CakeValuation :=
  CakeValuation.uniformOn 0 (1 / 6) (by norm_num) (by norm_num) (by norm_num)

/-- Two-step piecewise-uniform valuation (`3/4 · leftHalf + 1/4 · rightHalf`, density `3/2` on
`[0, 1/2]` and `1/2` on `[1/2, 1]`). -/
noncomputable def twoStepPiecewise : CakeValuation :=
  CakeValuation.convexComb (3 / 4) (by norm_num) (by norm_num) leftHalf rightHalf

-- Checked concrete evaluations on affine and piecewise-uniform valuations (including zero-density
-- subintervals).
example : CakeValuation.uniform (1 / 4) (3 / 4) = 1 / 2 := by
  rw [CakeValuation.uniform_apply_of_le (by norm_num)]
  norm_num

example : incLinear 0 (1 / 2) = 1 / 4 ∧ incLinear (1 / 2) 1 = 3 / 4 := by
  rw [incLinear, CakeValuation.affine_apply_of_le _ _ _ (by norm_num),
    CakeValuation.affine_apply_of_le _ _ _ (by norm_num)]
  norm_num

example : decLinear 0 (1 / 2) = 3 / 4 ∧ decLinear (1 / 2) 1 = 1 / 4 := by
  rw [decLinear, CakeValuation.affine_apply_of_le _ _ _ (by norm_num),
    CakeValuation.affine_apply_of_le _ _ _ (by norm_num)]
  norm_num

example : mildAffine 0 (1 / 2) = 3 / 8 ∧ mildAffine (1 / 2) 1 = 5 / 8 := by
  rw [mildAffine, CakeValuation.affine_apply_of_le _ _ _ (by norm_num),
    CakeValuation.affine_apply_of_le _ _ _ (by norm_num)]
  norm_num

example : leftHalf 0 (1 / 4) = 1 / 2 ∧ leftHalf (1 / 2) 1 = 0 := by
  rw [leftHalf, CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num),
    CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num)]
  norm_num

example : twoStepPiecewise 0 (1 / 3) = 1 / 2 ∧ twoStepPiecewise (1 / 3) 1 = 1 / 2 := by
  simp only [twoStepPiecewise, CakeValuation.convexComb_apply, leftHalf, rightHalf,
    CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
    CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (1 / 3 : ℝ) ≤ 1)]
  norm_num

/-! ### 2. Explicit Closed-Form Robertson–Webb Oracle for `uniformOn` Profiles -/

/-- Closed-form cut point for `CakeValuation.uniformOn l r` without `Classical.choose`. -/
noncomputable def cutUniformOn (l r a α : ℝ) : ℝ :=
  min 1 (max a (min r (max l a) + α * (r - l)))

/-- `cutUniformOn` produces a valid Robertson–Webb cut point on `[a, 1]` for `uniformOn l r`. -/
theorem cutUniformOn_valid {l r : ℝ} (hl : 0 ≤ l) (hlr : l < r) (hr : r ≤ 1)
    {a α : ℝ} (ha1 : a ≤ 1) (hα0 : 0 ≤ α)
    (hα1 : α ≤ CakeValuation.uniformOn l r hl hlr hr a 1) :
    let x := cutUniformOn l r a α
    x ∈ Set.Icc a 1 ∧ CakeValuation.uniformOn l r hl hlr hr a x = α := by
  have hrl_pos : 0 < r - l := sub_pos.mpr hlr
  rw [CakeValuation.uniformOn_apply_of_le _ _ _ _ _ ha1] at hα1
  have h1_clamp : min r (max l (1 : ℝ)) = r := by
    rw [max_eq_right (hlr.le.trans hr), min_eq_left hr]
  rw [h1_clamp] at hα1
  set base := min r (max l a)
  have hbase_le_r : base ≤ r := min_le_left r (max l a)
  have hbase_ge_l : l ≤ base := le_min hlr.le (le_max_left l a)
  have hprod_le : α * (r - l) ≤ r - base := by
    have hmul := mul_le_mul_of_nonneg_right hα1 hrl_pos.le
    have hsimp : ((r - l) / (r - l) - (base - l) / (r - l)) * (r - l) = r - base := by
      field_simp [hrl_pos.ne']
      ring
    linarith
  set x := cutUniformOn l r a α
  have hx_ge_a : a ≤ x := by
    simp only [x, cutUniformOn, le_min_iff]
    exact ⟨ha1, le_max_left _ _⟩
  have hx_le_1 : x ≤ 1 := min_le_left _ _
  refine ⟨⟨hx_ge_a, hx_le_1⟩, ?_⟩
  rw [CakeValuation.uniformOn_apply_of_le _ _ _ _ _ hx_ge_a]
  by_cases har : a ≤ r
  · have hbase_ge_a : a ≤ base := le_min har (le_max_right l a)
    have htarget_ge_a : a ≤ base + α * (r - l) := by nlinarith
    have htarget_le_1 : base + α * (r - l) ≤ 1 := by linarith
    have hx_eq : x = base + α * (r - l) := by
      change min 1 (max a (base + α * (r - l))) = base + α * (r - l)
      rw [max_eq_right htarget_ge_a, min_eq_right htarget_le_1]
    have hmax_x : max l x = base + α * (r - l) := by
      rw [hx_eq, max_eq_right (by nlinarith)]
    have hmin_x : min r (max l x) = base + α * (r - l) := by
      rw [hmax_x, min_eq_right (by linarith)]
    rw [hmin_x]
    field_simp [hrl_pos.ne']
    ring
  · have hra : r ≤ a := le_of_not_ge har
    have hbase_r : base = r := min_eq_left (hra.trans (le_max_right l a))
    have hα_zero : α = 0 := by
      rw [hbase_r] at hprod_le
      nlinarith
    have hx_a : x = a := by
      change min 1 (max a (base + α * (r - l))) = a
      rw [hbase_r, hα_zero, zero_mul, add_zero, max_eq_left hra, min_eq_right ha1]
    rw [hx_a, hα_zero, sub_self]

/-! ### 3. Negative and Separation Witnesses (Non-Vacuity of Fairness Predicates) -/

/-- Biased `1`-cut division `[0, 1/4]` vs `[1/4, 1]`: valid partition, neither proportional nor
envy-free under uniform valuations. -/
noncomputable def biasedTwoDiv : DividedCake 2 where
  cuts := [1 / 4]
  pieces i := if i = 0 then [⟨0, 1 / 4⟩] else [⟨1 / 4, 1⟩]

example :
    biasedTwoDiv.IsValidPartition ∧
      ¬ biasedTwoDiv.IsProportional (fun _ => CakeValuation.uniform) ∧
      ¬ biasedTwoDiv.IsEnvyFree (fun _ => CakeValuation.uniform) := by
  refine ⟨⟨⟨by norm_num, by norm_num⟩, ?_⟩, ?_, ?_⟩
  · exact List.Perm.refl _
  · intro hprop
    have h0 := hprop 0
    simp only [biasedTwoDiv, ↓reduceIte, CakeValuation.bundleVal_singleton,
      CakeValuation.uniform_apply_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4)] at h0
    norm_num at h0
  · intro hef
    have h01 := hef 0 1
    simp only [biasedTwoDiv, Fin.isValue, ↓reduceIte, one_ne_zero,
      CakeValuation.bundleVal_singleton,
      CakeValuation.uniform_apply_of_le (by norm_num : (0 : ℝ) ≤ 1 / 4),
      CakeValuation.uniform_apply_of_le (by norm_num : (1 / 4 : ℝ) ≤ 1)] at h01
    norm_num at h01

/-- Three-player separation witness: on `n = 3`, a valid partition can be **proportional** (`≥ 1/3`
for all three players) while **failing envy-freeness** (Player `0` receives `1/3` on `[0, 1/3]` but
values Player `2`'s `[1/2, 1]` at `1/2 > 1/3`). -/
noncomputable def propNotEnvyFreeThree : DividedCake 3 where
  cuts := [1 / 3, 1 / 2]
  pieces
    | 0 => [⟨0, 1 / 3⟩]
    | 1 => [⟨1 / 3, 1 / 2⟩]
    | 2 => [⟨1 / 2, 1⟩]

noncomputable def sepThreeProfile : Fin 3 → CakeValuation
  | 0 => CakeValuation.uniform
  | 1 => CakeValuation.uniformOn (1 / 3) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  | 2 => CakeValuation.uniform

example :
    propNotEnvyFreeThree.IsValidPartition ∧
      propNotEnvyFreeThree.IsProportional sepThreeProfile ∧
      ¬ propNotEnvyFreeThree.IsEnvyFree sepThreeProfile := by
  refine ⟨⟨⟨by norm_num, by norm_num, by norm_num⟩, List.Perm.refl _⟩, ?_, ?_⟩
  · intro i
    fin_cases i
    · simp only [propNotEnvyFreeThree, sepThreeProfile, Fin.zero_eta, Fin.isValue,
        CakeValuation.bundleVal_singleton,
        CakeValuation.uniform_apply_of_le (by norm_num : (0 : ℝ) ≤ 1 / 3)]
      norm_num
    · simp only [propNotEnvyFreeThree, sepThreeProfile, Fin.mk_one, Fin.isValue,
        CakeValuation.bundleVal_singleton,
        CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2)]
      norm_num
    · simp only [propNotEnvyFreeThree, sepThreeProfile, Fin.reduceFinMk,
        CakeValuation.bundleVal_singleton,
        CakeValuation.uniform_apply_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)]
      norm_num
  · intro hef
    have h02 := hef 0 2
    simp only [propNotEnvyFreeThree, sepThreeProfile, Fin.isValue,
      CakeValuation.bundleVal_singleton,
      CakeValuation.uniform_apply_of_le (by norm_num : (0 : ℝ) ≤ 1 / 3),
      CakeValuation.uniform_apply_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at h02
    norm_num at h02

/-! ### 4. Checked Cut-and-Choose Witnesses (`n = 2`) -/

noncomputable def heterogTwoProfile : Fin 2 → CakeValuation
  | 0 => leftHalf
  | 1 => rightHalf

noncomputable def heterogTwoOracle : {ι : Type} → RWQuery (Fin 2) ι → ι
  | _, .eval i a b => heterogTwoProfile i a b
  | _, .cut 0 a α => cutUniformOn 0 (1 / 2) a α
  | _, .cut 1 a α => cutUniformOn (1 / 2) 1 a α

theorem isValidOracle_heterogTwoOracle :
    RWQuery.IsValidOracle heterogTwoProfile heterogTwoOracle := by
  refine ⟨fun _ _ _ => rfl, fun i a α ha0 ha1 hα0 hα1 => ?_⟩
  fin_cases i
  · exact cutUniformOn_valid (by norm_num) (by norm_num) (by norm_num) ha1 hα0 hα1
  · exact cutUniformOn_valid (by norm_num) (by norm_num) (by norm_num) ha1 hα0 hα1

-- Explicit execution of `cutAndChooseQ` on `(leftHalf, rightHalf)`: Player 0 cuts at `1 / 4`,
-- Player 1 values `[0, 1 / 4]` at `0 < 1 / 2` and takes `[1 / 4, 1]` of value `1 > 1 / 2` (strict
-- surplus), while Player 0 receives `[0, 1 / 4]` of value `1 / 2`.
example :
    (cutAndChooseQ.eval heterogTwoOracle).cuts = [1 / 4] ∧
      (cutAndChooseQ.eval heterogTwoOracle).pieces 0 = [⟨0, 1 / 4⟩] ∧
      (cutAndChooseQ.eval heterogTwoOracle).pieces 1 = [⟨1 / 4, 1⟩] ∧
      (heterogTwoProfile 1).bundleVal ((cutAndChooseQ.eval heterogTwoOracle).pieces 1) = 1 ∧
      (cutAndChooseQ.eval heterogTwoOracle).IsEnvyFree heterogTwoProfile ∧
      cutAndChooseQ.countQueries heterogTwoOracle = 2 := by
  have hc : (RWQuery.cutIn (0 : Fin 2) 0 1 (1 / 2)).eval heterogTwoOracle = 1 / 4 := by
    simp only [RWQuery.cutIn, FreeM.eval_map, FreeM.eval_lift, heterogTwoOracle, cutUniformOn]
    norm_num
  have hvL : (RWQuery.evalAsk (1 : Fin 2) 0 (1 / 4)).eval heterogTwoOracle = 0 := by
    simp only [RWQuery.evalAsk, FreeM.eval_lift, heterogTwoOracle, heterogTwoProfile, rightHalf,
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    norm_num
  have hnot : ¬ (1 / 2 : ℝ) ≤ 0 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, isEnvyFree_cutAndChooseQ isValidOracle_heterogTwoOracle,
    countQueries_cutAndChooseQ _⟩
  · simp only [cutAndChooseQ, FreeM.eval_bind, hc, hvL, hnot, ↓reduceIte, FreeM.eval_pure]
  · simp only [cutAndChooseQ, FreeM.eval_bind, hc, hvL, hnot, ↓reduceIte, FreeM.eval_pure]
  · simp only [cutAndChooseQ, FreeM.eval_bind, hc, hvL, hnot, ↓reduceIte, FreeM.eval_pure,
      Fin.isValue, one_ne_zero]
  · simp only [cutAndChooseQ, FreeM.eval_bind, hc, hvL, hnot, ↓reduceIte, FreeM.eval_pure,
      Fin.isValue, one_ne_zero, CakeValuation.bundleVal_singleton, heterogTwoProfile, rightHalf,
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (1 / 4 : ℝ) ≤ 1)]
    norm_num

-- Affine two-player Cut-and-Choose (`incLinear` vs `decLinear`).
example :
    let v : Fin 2 → CakeValuation := fun i => if i = 0 then incLinear else decLinear
    (cutAndChoose v).IsValidPartition ∧
      (cutAndChoose v).numCuts = 1 ∧
      (cutAndChoose v).IsContiguous ∧
      (cutAndChoose v).IsEnvyFree v ∧
      (cutAndChoose v).IsProportional v := by
  intro v
  exact ⟨isValidPartition_cutAndChooseQ _, numCuts_cutAndChooseQ _, isContiguous_cutAndChooseQ _,
    isEnvyFree_cutAndChooseQ (RWQuery.isValidOracle_oracleOf v),
    isProportional_cutAndChooseQ (RWQuery.isValidOracle_oracleOf v)⟩

/-! ### 5. Checked Dubins–Spanier (`O(n²)`) and Even–Paz (`O(n log n)`) Witnesses -/

-- Proportionality holds at `n = 0` without requiring `1 ≤ n`.
example (v : Fin 0 → CakeValuation) :
    (dubinsSpanier v).IsProportional v ∧ (evenPaz v).IsProportional v :=
  ⟨isProportional_dubinsSpanierQ (RWQuery.isValidOracle_oracleOf v),
    isProportional_evenPazQ (RWQuery.isValidOracle_oracleOf v)⟩

noncomputable def fourAgentProfile : Fin 4 → CakeValuation
  | 0 => CakeValuation.uniform
  | 1 => incLinear
  | 2 => decLinear
  | 3 => twoStepPiecewise

-- Four-agent Dubins–Spanier: 3 cuts, contiguous, every agent receives ≥ 1 / 4, exact 9 queries.
example (oracle : {ι : Type} → RWQuery (Fin 4) ι → ι) :
    (dubinsSpanier fourAgentProfile).IsValidPartition ∧
      (dubinsSpanier fourAgentProfile).numCuts = 3 ∧
      (dubinsSpanier fourAgentProfile).IsContiguous ∧
      (∀ i : Fin 4, 1 / 4 ≤ (fourAgentProfile i).bundleVal
        ((dubinsSpanier fourAgentProfile).pieces i)) ∧
      (dubinsSpanierQ 4).countQueries oracle = 9 := by
  obtain ⟨hP, hC, hCont⟩ :=
    isValidPartition_dubinsSpanierQ (by omega : 1 ≤ 4) (RWQuery.oracleOf fourAgentProfile)
  have hProp := isProportional_dubinsSpanierQ (RWQuery.isValidOracle_oracleOf fourAgentProfile)
  refine ⟨hP, hC, hCont, fun i => ?_, ?_⟩
  · dsimp only [dubinsSpanier]
    simpa only [Nat.cast_ofNat] using hProp i
  · rw [countQueries_dubinsSpanierQ (by omega : 1 ≤ 4) oracle]

-- Four-agent Even–Paz: 3 cuts, contiguous, every agent receives ≥ 1 / 4, at most 16 queries;
-- at n = 16, Even–Paz uses ≤ 128 queries versus Dubins–Spanier's exact 135 queries.
example (o4 : {ι : Type} → RWQuery (Fin 4) ι → ι)
    (o16 : {ι : Type} → RWQuery (Fin 16) ι → ι) :
    (evenPaz fourAgentProfile).IsValidPartition ∧
      (evenPaz fourAgentProfile).numCuts = 3 ∧
      (evenPaz fourAgentProfile).IsContiguous ∧
      (∀ i : Fin 4, 1 / 4 ≤ (fourAgentProfile i).bundleVal
        ((evenPaz fourAgentProfile).pieces i)) ∧
      (evenPazQ 4).countQueries o4 ≤ 16 ∧
      (evenPazQ 16).countQueries o16 < (dubinsSpanierQ 16).countQueries o16 := by
  obtain ⟨hP, hC, hCont⟩ :=
    isValidPartition_evenPazQ (by omega : 1 ≤ 4) (RWQuery.oracleOf fourAgentProfile)
  have hProp := isProportional_evenPazQ (RWQuery.isValidOracle_oracleOf fourAgentProfile)
  have hq4 : (evenPazQ 4).countQueries o4 ≤ 2 * 4 * Nat.clog 2 4 := countQueries_evenPazQ_le 4 o4
  have hclog4 : Nat.clog 2 4 = 2 := by decide
  have hq16 : (evenPazQ 16).countQueries o16 ≤ 2 * 16 * Nat.clog 2 16 :=
    countQueries_evenPazQ_le 16 o16
  have hclog16 : Nat.clog 2 16 = 4 := by decide
  have hds16 : (dubinsSpanierQ 16).countQueries o16 = 135 := by
    rw [countQueries_dubinsSpanierQ (by omega : 1 ≤ 16) o16]
  refine ⟨hP, hC, hCont, fun i => ?_, by omega, by omega⟩
  dsimp only [evenPaz]
  simpa only [Nat.cast_ofNat] using hProp i

/-! ### 6. Checked Three-Player Selfridge–Conway Witnesses (`2`-Cut and `5`-Cut Regimes) -/

-- Mixed affine + piecewise-uniform 3-player profile (`twoStepPiecewise`, `incLinear`,
-- `mildAffine`).
noncomputable def mixedThreeProfile : Fin 3 → CakeValuation
  | 0 => twoStepPiecewise
  | 1 => incLinear
  | 2 => mildAffine

example :
    (selfridgeConway mixedThreeProfile).IsValidPartition ∧
      (selfridgeConway mixedThreeProfile).numCuts ≤ 5 ∧
      (∀ i : Fin 3, ((selfridgeConway mixedThreeProfile).pieces i).length ≤ 2) ∧
      (selfridgeConway mixedThreeProfile).IsEnvyFree mixedThreeProfile ∧
      (selfridgeConway mixedThreeProfile).IsProportional mixedThreeProfile :=
  ⟨isValidPartition_selfridgeConwayQ _,
    numCuts_selfridgeConwayQ_le _,
    length_pieces_selfridgeConwayQ_le _,
    isEnvyFree_selfridgeConwayQ (RWQuery.isValidOracle_oracleOf mixedThreeProfile),
    isProportional_selfridgeConwayQ (RWQuery.isValidOracle_oracleOf mixedThreeProfile)⟩

-- Explicit closed-form checks verifying:
--   (a) `numCuts = 2` (untrimmed branch) on `(uniform, uniform, uniform)`, and
--   (b) `numCuts = 5` (trimmed regime via `numCuts_selfridgeConwayQ_eq_five_of_strict_max`),
--       partition validity, envy-freeness, and Player `2`'s `≥ 1 / 3` support share on two
--       piecewise-uniform profiles (`trimmedB2Profile` where `v₂ = rightHalf` is supported on
--       `[1/2, 1]`, and `trimmedB1Profile` where `v₂ = firstSixth` is supported on `[0, 1/6]`;
--       internal Phase 1 branch state of `selfridgeConwayQ` remains `private`).
noncomputable def uniformThreeProfile : Fin 3 → CakeValuation :=
  fun _ => CakeValuation.uniform

example :
    (selfridgeConway uniformThreeProfile).numCuts = 2 ∧
      (selfridgeConway uniformThreeProfile).IsEnvyFree uniformThreeProfile ∧
      (selfridgeConway uniformThreeProfile).IsProportional uniformThreeProfile :=
  ⟨numCuts_selfridgeConwayQ_eq_two_of_eq (RWQuery.isValidOracle_oracleOf uniformThreeProfile) rfl,
    isEnvyFree_selfridgeConwayQ (RWQuery.isValidOracle_oracleOf uniformThreeProfile),
    isProportional_selfridgeConwayQ (RWQuery.isValidOracle_oracleOf uniformThreeProfile)⟩

noncomputable def trimmedB2Profile : Fin 3 → CakeValuation
  | 0 => CakeValuation.uniform
  | 1 => leftHalf
  | 2 => rightHalf

noncomputable def trimmedB2Oracle : {ι : Type} → RWQuery (Fin 3) ι → ι
  | _, .eval i a b => trimmedB2Profile i a b
  | _, .cut 0 a α => min 1 (max a (a + α))
  | _, .cut 1 a α => cutUniformOn 0 (1 / 2) a α
  | _, .cut 2 a α => cutUniformOn (1 / 2) 1 a α

theorem isValidOracle_trimmedB2Oracle :
    RWQuery.IsValidOracle trimmedB2Profile trimmedB2Oracle := by
  refine ⟨fun _ _ _ => rfl, fun i a α ha0 ha1 hα0 hα1 => ?_⟩
  fin_cases i
  · dsimp only [trimmedB2Oracle, trimmedB2Profile] at hα1 ⊢
    rw [CakeValuation.uniform_apply_of_le ha1] at hα1
    have hge : a ≤ a + α := by linarith
    have hle : a + α ≤ 1 := by linarith
    rw [max_eq_right hge, min_eq_right hle, CakeValuation.uniform_apply_of_le hge]
    exact ⟨⟨hge, hle⟩, by ring⟩
  · exact cutUniformOn_valid (by norm_num) (by norm_num) (by norm_num) ha1 hα0 hα1
  · exact cutUniformOn_valid (by norm_num) (by norm_num) (by norm_num) ha1 hα0 hα1

example :
    (selfridgeConwayQ.eval trimmedB2Oracle).numCuts = 5 ∧
      (selfridgeConwayQ.eval trimmedB2Oracle).IsValidPartition ∧
      (selfridgeConwayQ.eval trimmedB2Oracle).IsEnvyFree trimmedB2Profile ∧
      1 / 3 ≤ rightHalf.bundleVal ((selfridgeConwayQ.eval trimmedB2Oracle).pieces 2) := by
  have hc1 : (RWQuery.cutIn (0 : Fin 3) 0 1 (1 / 3)).eval trimmedB2Oracle = 1 / 3 := by
    simp only [RWQuery.cutIn, FreeM.eval_map, FreeM.eval_lift, trimmedB2Oracle]
    norm_num
  have hc2 : (RWQuery.cutIn (0 : Fin 3) (1 / 3) 1 (1 / 3)).eval trimmedB2Oracle = 2 / 3 := by
    simp only [RWQuery.cutIn, FreeM.eval_map, FreeM.eval_lift, trimmedB2Oracle]
    norm_num
  have hprop2 := isProportional_selfridgeConwayQ isValidOracle_trimmedB2Oracle 2
  refine ⟨numCuts_selfridgeConwayQ_eq_five_of_strict_max isValidOracle_trimmedB2Oracle 0 ?_,
    isValidPartition_selfridgeConwayQ _,
    isEnvyFree_selfridgeConwayQ isValidOracle_trimmedB2Oracle,
    by simpa only [Nat.cast_ofNat, trimmedB2Profile] using hprop2⟩
  intro j hj
  dsimp only
  rw [hc1, hc2]
  fin_cases j
  · exact absurd rfl hj
  · simp only [trimmedB2Profile, CakeValuation.pieceVal, leftHalf,
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3)]
    norm_num
  · simp only [trimmedB2Profile, CakeValuation.pieceVal, leftHalf,
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (2 / 3 : ℝ) ≤ 1)]
    norm_num

noncomputable def trimmedB1Profile : Fin 3 → CakeValuation
  | 0 => CakeValuation.uniform
  | 1 => leftHalf
  | 2 => firstSixth

noncomputable def trimmedB1Oracle : {ι : Type} → RWQuery (Fin 3) ι → ι
  | _, .eval i a b => trimmedB1Profile i a b
  | _, .cut 0 a α => min 1 (max a (a + α))
  | _, .cut 1 a α => cutUniformOn 0 (1 / 2) a α
  | _, .cut 2 a α => cutUniformOn 0 (1 / 6) a α

theorem isValidOracle_trimmedB1Oracle :
    RWQuery.IsValidOracle trimmedB1Profile trimmedB1Oracle := by
  refine ⟨fun _ _ _ => rfl, fun i a α ha0 ha1 hα0 hα1 => ?_⟩
  fin_cases i
  · dsimp only [trimmedB1Oracle, trimmedB1Profile] at hα1 ⊢
    rw [CakeValuation.uniform_apply_of_le ha1] at hα1
    have hge : a ≤ a + α := by linarith
    have hle : a + α ≤ 1 := by linarith
    rw [max_eq_right hge, min_eq_right hle, CakeValuation.uniform_apply_of_le hge]
    exact ⟨⟨hge, hle⟩, by ring⟩
  · exact cutUniformOn_valid (by norm_num) (by norm_num) (by norm_num) ha1 hα0 hα1
  · exact cutUniformOn_valid (by norm_num) (by norm_num) (by norm_num) ha1 hα0 hα1

example :
    (selfridgeConwayQ.eval trimmedB1Oracle).numCuts = 5 ∧
      (selfridgeConwayQ.eval trimmedB1Oracle).IsValidPartition ∧
      (selfridgeConwayQ.eval trimmedB1Oracle).IsEnvyFree trimmedB1Profile ∧
      1 / 3 ≤ firstSixth.bundleVal ((selfridgeConwayQ.eval trimmedB1Oracle).pieces 2) := by
  have hc1 : (RWQuery.cutIn (0 : Fin 3) 0 1 (1 / 3)).eval trimmedB1Oracle = 1 / 3 := by
    simp only [RWQuery.cutIn, FreeM.eval_map, FreeM.eval_lift, trimmedB1Oracle]
    norm_num
  have hc2 : (RWQuery.cutIn (0 : Fin 3) (1 / 3) 1 (1 / 3)).eval trimmedB1Oracle = 2 / 3 := by
    simp only [RWQuery.cutIn, FreeM.eval_map, FreeM.eval_lift, trimmedB1Oracle]
    norm_num
  have hprop2 := isProportional_selfridgeConwayQ isValidOracle_trimmedB1Oracle 2
  refine ⟨numCuts_selfridgeConwayQ_eq_five_of_strict_max isValidOracle_trimmedB1Oracle 0 ?_,
    isValidPartition_selfridgeConwayQ _,
    isEnvyFree_selfridgeConwayQ isValidOracle_trimmedB1Oracle,
    by simpa only [Nat.cast_ofNat, trimmedB1Profile] using hprop2⟩
  intro j hj
  dsimp only
  rw [hc1, hc2]
  fin_cases j
  · exact absurd rfl hj
  · simp only [trimmedB1Profile, CakeValuation.pieceVal, leftHalf,
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (1 / 3 : ℝ) ≤ 2 / 3)]
    norm_num
  · simp only [trimmedB1Profile, CakeValuation.pieceVal, leftHalf,
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (0 : ℝ) ≤ 1 / 3),
      CakeValuation.uniformOn_apply_of_le _ _ _ _ _ (by norm_num : (2 / 3 : ℝ) ≤ 1)]
    norm_num

end CslibFrontierTests.FairDivision
