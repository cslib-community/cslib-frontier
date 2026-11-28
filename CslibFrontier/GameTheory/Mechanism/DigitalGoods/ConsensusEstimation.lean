/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.DigitalGoods.ProfitExtraction
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Consensus estimation profit extraction (CEPE) and truthfulness with high probability

This module formalizes the Consensus Estimation Profit Extraction (`CEPE`) framework of
[HartlineKarlin2007], §13.4.6 (pp. 349–350) and Exercise 13.11 (p. 361):

* **Solution concepts (`Definitions 13.43–13.45`, pp. 349–350):** for mechanisms and functions
  randomized by a uniform draw `U ∈ [0, 1]` (modeled via Lebesgue outer measure `volume.real` and
  interval integrals `∫ u in (0 : ℝ)..1, …`), we define truthfulness with high probability
  (`IsTruthfulWithHighProbAt`, `IsTruthfulWithHighProb`), `ρ`-consensus (`IsRhoConsensus`), and
  `β`-estimation (`IsBetaEstimate`). Following Definition 13.43 verbatim,
  `IsTruthfulWithHighProbAt` and `IsRhoConsensus` upper-bound the outer measure of the *failure*
  event by `ε` rather than lower-bounding the outer measure of the good event, avoiding
  non-measurable outer-measure loopholes.
* **Random geometric rounding `r_α` (`Definition 13.46`, `Lemmas 13.47–13.48`, p. 350):**
  `roundDown α u V := if 0 < V then α ^ (⌊Real.logb α V - u⌋ + u) else 0` rounds `V > 0` down to
  the nearest `α ^ (i + u)` (`i : ℤ`). For `1 < α`:
  - **Lemma 13.47** (`measurableSet_roundDown_consensus`, `volume_real_roundDown_consensus`,
    `roundDown_isRhoConsensus`): for `1 ≤ ρ ≤ α` and `0 < V`, the consensus event
    `{u ∈ [0, 1] | ∀ V' ∈ [V / ρ, V], roundDown α u V' = roundDown α u V}` is measurable with exact
    Lebesgue measure `1 - Real.logb α ρ`, and its complement on `[0, 1]` has measure
    `Real.logb α ρ`.
  - **Lemma 13.48** (`integral_roundDown`, `roundDown_isBetaEstimate`): for `0 < V`,
    `∫ u in (0 : ℝ)..1, roundDown α u V = V / ((α * Real.log α) / (α - 1))`, so `roundDown α` is
    a `β`-estimate with exact `β = (α * Real.log α) / (α - 1)`.
* **Deterministic consensus ex-post equilibrium (`Exercise 13.11(a)`, p. 361; Footnote 2, p. 350):**
  Given a nonnegative monotone benchmark `G`, a nonnegative monotone rounding function `r`, and a
  family `PE : ℝ → Mechanism ι` of DSIC, normalized mechanisms whose allocations are antitone in
  the target profit `R ≥ 0` (capturing monotone-in-`R` offered prices in `[0, ∞]`, via
  `SingleParameter.utility_myerson`), if `r (G (Function.update v i 0)) = r (G v)` then bidding
  `v i` maximizes bidder `i`'s utility in `cepeDet G PE r` over all `bᵢ ≥ 0`
  (`cepeDet_optimal_response_of_consensus`).
* **CEPE competitiveness and truthfulness (`Theorem 13.49` & `Exercise 13.11(b)`, pp. 350, 361):**
  For any single-parameter problem with seller cost function `c : (ι → ℝ) → ℝ` and target-monotone
  profit extractor `PE` extracting exact profit `R` whenever `0 ≤ R ≤ G b`, `cepe G PE α` has
  exact expected profit `G b / ((α * Real.log α) / (α - 1))` (`cepeExpectedProfit_eq`), is
  `(α * Real.log α) / (α - 1)`-competitive against `G` (`cepe_isCompetitive`), and on inputs
  satisfying `G v / ρ ≤ G (Function.update v i 0)` the failure event that *some* deviation `bᵢ ≥ 0`
  strictly improves bidder `i`'s utility has outer measure at most `Real.logb α ρ`
  (`cepe_nontruthful_measure_le`, `cepe_isTruthfulWithHighProbAt`).
* **Digital goods instantiation (p. 349):** `optimalProfitTwo` is monotone in bids
  (`singlePriceProfitOn_mono`) and `profitExtractOn s R` has allocations antitone in `R ≥ 0`
  (`profitExtractOn_allocation_antitone`). Instantiating Theorem 13.49 yields `cepeDigitalGoods`,
  which is `(α * Real.log α) / (α - 1)`-competitive against `ℱ⁽²⁾`
  (`cepeDigitalGoods_isCompetitive`) and truthful with probability at least
  `1 - Real.logb α (m / (m - 1)) ≥ 1 - 1 / ((m - 1) * Real.log α)` whenever `ℱ⁽²⁾(b)` is
  realized by `m ≥ 3` winners with `m / (m - 1) ≤ α` (`cepeDigitalGoods_truthful_of_winners`).
  Note the `m ≥ 3` boundary: at `m = 2`, removing one winner can drop `ℱ⁽²⁾` to `0` (verified in
  `CslibFrontierTests.GameTheory.DigitalGoodsBoundsCEPE`).

No running-time claim is made.

## Main definitions

* `IsTruthfulWithHighProbAt`, `IsTruthfulWithHighProb`: truthfulness with high probability
  ([HartlineKarlin2007], Definition 13.43, p. 349).
* `IsRhoConsensus`: `ρ`-consensus ([HartlineKarlin2007], Definition 13.44, p. 349).
* `IsBetaEstimate`: `β`-estimate ([HartlineKarlin2007], Definition 13.45, p. 350).
* `roundDown`: random geometric rounding `r_α` ([HartlineKarlin2007], Definition 13.46, p. 350).
* `cepeDet`, `cepe`, `cepeExpectedProfit`, `cepeDigitalGoods`: the CEPE mechanism and its digital
  goods instantiation.

## Main results

* `roundDown_pos`, `roundDown_le`, `div_lt_roundDown`, `roundDown_mono`: basic bounds and
  monotonicity of `r_α`.
* `measurableSet_roundDown_consensus`, `volume_real_roundDown_consensus`,
  `roundDown_isRhoConsensus`: **Lemma 13.47** ([HartlineKarlin2007], §13.4.6, p. 350).
* `integral_roundDown`, `roundDown_isBetaEstimate`: **Lemma 13.48** ([HartlineKarlin2007],
  §13.4.6, p. 350).
* `cepeDet_optimal_response_of_consensus`: **Exercise 13.11(a)** ([HartlineKarlin2007], p. 361).
* `cepeExpectedProfit_eq`, `cepe_isCompetitive`, `cepe_nontruthful_measure_le`,
  `cepe_isTruthfulWithHighProbAt`: **Theorem 13.49** and **Exercise 13.11(b)**
  ([HartlineKarlin2007], §13.4.6, p. 350; p. 361).
* `singlePriceProfitOn_mono`, `optimalProfitTwo_le_optimalProfit`,
  `profitExtractOn_allocation_antitone`, `cepeDigitalGoods_isCompetitive`,
  `cepeDigitalGoods_truthful_of_winners`: digital goods instantiation ([HartlineKarlin2007],
  §13.4.6, p. 349).

## References

* [J. D. Hartline and A. R. Karlin, *Profit Maximization in Mechanism Design*, Chapter 13 of
  *Algorithmic Game Theory*][HartlineKarlin2007]
-/

open Finset MeasureTheory
open scoped BigOperators

public section

namespace Cslib.GameTheory.SingleParameter.DigitalGoods

/-! ### Solution concepts (`Definitions 13.43–13.45`, pp. 349–350) -/

section Definitions

variable {ι : Type*}

/-- Pointwise truthfulness with probability at least `1 - ε` for bidder `i` at nonnegative profile
`v`, for a mechanism randomized over `U ~ Uniform[0, 1]` ([HartlineKarlin2007], Definition 13.43,
p. 349, localized to a given profile and bidder as used in Theorem 13.49, p. 350): for every
nonnegative deviation `bᵢ`, the outer Lebesgue measure of draws `u ∈ [0, 1]` for which bidder `i`
strictly benefits from bidding `bᵢ` is at most `ε`. -/
@[expose] def IsTruthfulWithHighProbAt [DecidableEq ι] (M : ℝ → Mechanism ι) (v : ι → ℝ)
    (i : ι) (ε : ℝ) : Prop :=
  ∀ b_i : ℝ, 0 ≤ b_i →
    volume.real
      {u ∈ Set.Icc (0 : ℝ) 1 |
        (M u).utility i (v i) v < (M u).utility i (v i) (Function.update v i b_i)} ≤ ε

/-- **Truthfulness with high probability `1 - ε`** ([HartlineKarlin2007], Definition 13.43,
p. 349): for every nonnegative profile `v`, bidder `i`, and nonnegative deviation `bᵢ`, the outer
measure over `U ~ Uniform[0, 1]` of draws where bidder `i` strictly benefits by bidding `bᵢ` is at
most `ε`. -/
@[expose] def IsTruthfulWithHighProb [DecidableEq ι] (M : ℝ → Mechanism ι) (ε : ℝ) : Prop :=
  ∀ v : ι → ℝ, 0 ≤ v → ∀ i : ι, IsTruthfulWithHighProbAt M v i ε

/-- **Consensus function** ([HartlineKarlin2007], Definition 13.44, p. 349): a function `r`
randomized over `U ~ Uniform[0, 1]` is a `ρ`-consensus with probability at least `1 - ε` if for
every `V > 0`, the outer measure of draws `u ∈ [0, 1]` failing `∀ V' ∈ [V / ρ, V], r u V' = r u V`
is at most `ε`. -/
@[expose] def IsRhoConsensus (r : ℝ → ℝ → ℝ) (ρ ε : ℝ) : Prop :=
  ∀ V : ℝ, 0 < V →
    volume.real
      {u ∈ Set.Icc (0 : ℝ) 1 | ¬ ∀ V' ∈ Set.Icc (V / ρ) V, r u V' = r u V} ≤ ε

/-- **`β`-estimate** ([HartlineKarlin2007], Definition 13.45, p. 350): a function `r` randomized
over `U ~ Uniform[0, 1]` is a `β`-estimate (`β > 0`) if for every `V > 0`, `r u V ≤ V` for all
`u ∈ [0, 1]` and `∫ u in (0 : ℝ)..1, r u V ≥ V / β`. -/
@[expose] def IsBetaEstimate (r : ℝ → ℝ → ℝ) (β : ℝ) : Prop :=
  0 < β ∧ ∀ V : ℝ, 0 < V →
    (∀ u ∈ Set.Icc (0 : ℝ) 1, r u V ≤ V) ∧ V / β ≤ ∫ u in (0 : ℝ)..1, r u V

end Definitions

/-! ### Random geometric rounding `r_α` (`Definition 13.46`, `Lemmas 13.47–13.48`) -/

section RoundDown

/-- **Random geometric rounding `r_α`** ([HartlineKarlin2007], Definition 13.46, p. 350): given
base `α > 1` and shift `u ∈ [0, 1]`, rounds `V > 0` down to the largest power `α ^ (i + u)`
(`i : ℤ`) at most `V`, and maps `V ≤ 0` to `0`. -/
@[expose] noncomputable def roundDown (α u V : ℝ) : ℝ :=
  if 0 < V then α ^ ((⌊Real.logb α V - u⌋ : ℝ) + u) else 0

theorem roundDown_of_nonpos (α u : ℝ) {V : ℝ} (hV : V ≤ 0) : roundDown α u V = 0 := by
  simp only [roundDown, not_lt.2 hV, ↓reduceIte]

theorem roundDown_pos {α : ℝ} (hα : 1 < α) (u : ℝ) {V : ℝ} (hV : 0 < V) :
    0 < roundDown α u V := by
  simp only [roundDown, hV, ↓reduceIte]
  exact Real.rpow_pos_of_pos (by linarith) _

theorem roundDown_nonneg {α : ℝ} (hα : 1 < α) (u V : ℝ) : 0 ≤ roundDown α u V := by
  by_cases hV : 0 < V
  · exact (roundDown_pos hα u hV).le
  · rw [roundDown_of_nonpos α u (not_lt.1 hV)]

theorem roundDown_le {α : ℝ} (hα : 1 < α) (u : ℝ) {V : ℝ} (hV : 0 ≤ V) :
    roundDown α u V ≤ V := by
  rcases hV.eq_or_lt with rfl | hpos
  · rw [roundDown_of_nonpos α u le_rfl]
  · simp only [roundDown, hpos, ↓reduceIte]
    have hexp : (⌊Real.logb α V - u⌋ : ℝ) + u ≤ Real.logb α V := by
      linarith [Int.floor_le (Real.logb α V - u)]
    calc α ^ ((⌊Real.logb α V - u⌋ : ℝ) + u)
        ≤ α ^ (Real.logb α V) := Real.rpow_le_rpow_of_exponent_le hα.le hexp
      _ = V := Real.rpow_logb (by linarith) hα.ne' hpos

theorem div_lt_roundDown {α : ℝ} (hα : 1 < α) (u : ℝ) {V : ℝ} (hV : 0 < V) :
    V / α < roundDown α u V := by
  simp only [roundDown, hV, ↓reduceIte]
  have hexp : Real.logb α V - 1 < (⌊Real.logb α V - u⌋ : ℝ) + u := by
    linarith [Int.sub_one_lt_floor (Real.logb α V - u)]
  calc V / α = α ^ (Real.logb α V) / α ^ (1 : ℝ) := by
        rw [Real.rpow_logb (by linarith) hα.ne' hV, Real.rpow_one]
    _ = α ^ (Real.logb α V - 1) := (Real.rpow_sub (by linarith) _ _).symm
    _ < α ^ ((⌊Real.logb α V - u⌋ : ℝ) + u) := Real.rpow_lt_rpow_of_exponent_lt hα hexp

/-- For fixed `α > 1` and `u`, `roundDown α u` is monotone on `[0, ∞)` (in fact on `ℝ`). -/
theorem roundDown_mono {α : ℝ} (hα : 1 < α) (u : ℝ) : Monotone (roundDown α u) := by
  intro V₁ V₂ hV
  by_cases h1 : 0 < V₁
  · have h2 : 0 < V₂ := h1.trans_le hV
    simp only [roundDown, h1, h2, ↓reduceIte]
    refine Real.rpow_le_rpow_of_exponent_le hα.le ?_
    have hlog : Real.logb α V₁ ≤ Real.logb α V₂ := Real.logb_le_logb_of_le hα h1 hV
    have hfl : ⌊Real.logb α V₁ - u⌋ ≤ ⌊Real.logb α V₂ - u⌋ :=
      Int.floor_mono (sub_le_sub_right hlog u)
    have hflR : (⌊Real.logb α V₁ - u⌋ : ℝ) ≤ (⌊Real.logb α V₂ - u⌋ : ℝ) := by exact_mod_cast hfl
    linarith
  · rw [roundDown_of_nonpos α u (not_lt.1 h1)]
    exact roundDown_nonneg hα u V₂

private theorem floor_sub_eq_of_le_fract (x u : ℝ) (hu0 : 0 ≤ u) (huf : u ≤ Int.fract x) :
    ⌊x - u⌋ = ⌊x⌋ := by
  rw [Int.floor_eq_iff]
  have hfract_lt : Int.fract x < 1 := Int.fract_lt_one x
  have hdef : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
  constructor <;> linarith

private theorem floor_sub_eq_of_fract_lt (x u : ℝ) (hfu : Int.fract x < u) (hu1 : u ≤ 1) :
    ⌊x - u⌋ = ⌊x⌋ - 1 := by
  rw [Int.floor_eq_iff]
  have hfract0 : 0 ≤ Int.fract x := Int.fract_nonneg x
  have hdef : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
  push_cast
  constructor <;> linarith

/-- Explicit interval description of the `ρ`-consensus event for `roundDown α` on `[0, 1]`. -/
private theorem roundDown_consensus_set_eq {α ρ V : ℝ} (hα : 1 < α) (hρ1 : 1 ≤ ρ)
    (hρα : ρ ≤ α) (hV : 0 < V) :
    let f := Int.fract (Real.logb α V)
    let d := Real.logb α ρ
    {u ∈ Set.Icc (0 : ℝ) 1 | ∀ V' ∈ Set.Icc (V / ρ) V, roundDown α u V' = roundDown α u V} =
      if d ≤ f then Set.Icc 0 (f - d) ∪ Set.Ioc f 1 else Set.Ioc f (1 + f - d) := by
  intro f d
  set x : ℝ := Real.logb α V with hx
  have hd0 : 0 ≤ d := Real.logb_nonneg hα hρ1
  have hd1 : d ≤ 1 := by
    have hlogα : Real.logb α α = 1 := Real.logb_self_eq_one hα
    exact (Real.logb_le_logb_of_le hα (by linarith) hρα).trans_eq hlogα
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hf1 : f < 1 := Int.fract_lt_one x
  have hf_def : f = x - (⌊x⌋ : ℝ) := rfl
  have hVρ : 0 < V / ρ := div_pos hV (by linarith)
  have hlog_div : Real.logb α (V / ρ) = x - d := Real.logb_div hV.ne' (by linarith)
  have hequiv : ∀ u : ℝ,
      (∀ V' ∈ Set.Icc (V / ρ) V, roundDown α u V' = roundDown α u V) ↔
        ⌊x - d - u⌋ = ⌊x - u⌋ := by
    intro u
    constructor
    · intro h
      have hlow := h (V / ρ) ⟨le_rfl, div_le_self hV.le hρ1⟩
      simp only [roundDown, hVρ, hV, ↓reduceIte, hlog_div, ← hx] at hlow
      have hexp := (Real.rpow_right_inj (by linarith : 0 < α) hα.ne').1 hlow
      have hflR : (⌊x - d - u⌋ : ℝ) = (⌊x - u⌋ : ℝ) := by linarith
      exact_mod_cast hflR
    · intro hfl V' hV'
      have hlow : roundDown α u (V / ρ) = roundDown α u V := by
        simp only [roundDown, hVρ, hV, ↓reduceIte, hlog_div, ← hx, hfl]
      exact le_antisymm (roundDown_mono hα u hV'.2) (hlow ▸ roundDown_mono hα u hV'.1)
  ext u
  rw [Set.mem_sep_iff, hequiv u, Set.mem_Icc]
  split_ifs with hdf
  · simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hu0, hu1⟩, hfl⟩
      by_cases huf : u ≤ f
      · left
        refine ⟨hu0, ?_⟩
        rw [floor_sub_eq_of_le_fract x u hu0 huf, Int.floor_eq_iff] at hfl
        linarith
      · right
        exact ⟨lt_of_not_ge huf, hu1⟩
    · rintro (⟨hu0, hu_le⟩ | ⟨hfu, hu1⟩)
      · refine ⟨⟨hu0, by linarith⟩, ?_⟩
        rw [floor_sub_eq_of_le_fract x u hu0 (by linarith), Int.floor_eq_iff]
        constructor <;> linarith
      · refine ⟨⟨by linarith, hu1⟩, ?_⟩
        rw [floor_sub_eq_of_fract_lt x u hfu hu1, Int.floor_eq_iff]
        push_cast
        constructor <;> linarith
  · push Not at hdf
    simp only [Set.mem_Ioc]
    constructor
    · rintro ⟨⟨hu0, hu1⟩, hfl⟩
      by_cases huf : u ≤ f
      · rw [floor_sub_eq_of_le_fract x u hu0 huf, Int.floor_eq_iff] at hfl
        linarith
      · push Not at huf
        rw [floor_sub_eq_of_fract_lt x u huf hu1, Int.floor_eq_iff] at hfl
        push_cast at hfl
        exact ⟨huf, by linarith⟩
    · rintro ⟨hfu, hu_le⟩
      have hu0 : 0 ≤ u := by linarith
      have hu1 : u ≤ 1 := by linarith
      refine ⟨⟨hu0, hu1⟩, ?_⟩
      rw [floor_sub_eq_of_fract_lt x u hfu hu1, Int.floor_eq_iff]
      push_cast
      constructor <;> linarith

/-- **Lemma 13.47 (measurability)** ([HartlineKarlin2007], §13.4.6, p. 350): for `1 < α`,
`1 ≤ ρ ≤ α`, and `V > 0`, the `ρ`-consensus event of `roundDown α` on `[0, 1]` is measurable. -/
theorem measurableSet_roundDown_consensus {α ρ V : ℝ} (hα : 1 < α) (hρ1 : 1 ≤ ρ) (hρα : ρ ≤ α)
    (hV : 0 < V) :
    MeasurableSet
      {u ∈ Set.Icc (0 : ℝ) 1 | ∀ V' ∈ Set.Icc (V / ρ) V, roundDown α u V' = roundDown α u V} := by
  rw [roundDown_consensus_set_eq hα hρ1 hρα hV]
  split_ifs
  · exact measurableSet_Icc.union measurableSet_Ioc
  · exact measurableSet_Ioc

/-- **Lemma 13.47 (exact measure)** ([HartlineKarlin2007], §13.4.6, p. 350): for `1 < α`,
`1 ≤ ρ ≤ α`, and `V > 0`, the Lebesgue measure of the `ρ`-consensus event of `roundDown α` on
`[0, 1]` equals `1 - Real.logb α ρ`. -/
theorem volume_real_roundDown_consensus {α ρ V : ℝ} (hα : 1 < α) (hρ1 : 1 ≤ ρ) (hρα : ρ ≤ α)
    (hV : 0 < V) :
    volume.real
      {u ∈ Set.Icc (0 : ℝ) 1 | ∀ V' ∈ Set.Icc (V / ρ) V, roundDown α u V' = roundDown α u V} =
      1 - Real.logb α ρ := by
  rw [roundDown_consensus_set_eq hα hρ1 hρα hV]
  set f : ℝ := Int.fract (Real.logb α V)
  set d : ℝ := Real.logb α ρ
  have hd0 : 0 ≤ d := Real.logb_nonneg hα hρ1
  have hd1 : d ≤ 1 := by
    have hlogα : Real.logb α α = 1 := Real.logb_self_eq_one hα
    exact (Real.logb_le_logb_of_le hα (by linarith) hρα).trans_eq hlogα
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hf1 : f < 1 := Int.fract_lt_one _
  split_ifs with hdf
  · have hdisj : Disjoint (Set.Icc (0 : ℝ) (f - d)) (Set.Ioc f 1) :=
      Set.disjoint_left.2 fun u h1 h2 => by linarith [h1.2, h2.1]
    rw [measureReal_union hdisj measurableSet_Ioc (by simp [Real.volume_Icc])
        (by simp [Real.volume_Ioc]),
      Real.volume_real_Icc_of_le (by linarith), Real.volume_real_Ioc_of_le hf1.le]
    ring
  · rw [Real.volume_real_Ioc_of_le (by linarith)]
    ring

/-- The complement of the `ρ`-consensus event of `roundDown α` on `[0, 1]` has exact Lebesgue
measure `Real.logb α ρ`. -/
private theorem volume_real_roundDown_nonconsensus {α ρ V : ℝ} (hα : 1 < α) (hρ1 : 1 ≤ ρ)
    (hρα : ρ ≤ α) (hV : 0 < V) :
    volume.real
      {u ∈ Set.Icc (0 : ℝ) 1 | ¬ ∀ V' ∈ Set.Icc (V / ρ) V, roundDown α u V' = roundDown α u V} =
      Real.logb α ρ := by
  set C : Set ℝ :=
    {u ∈ Set.Icc (0 : ℝ) 1 | ∀ V' ∈ Set.Icc (V / ρ) V, roundDown α u V' = roundDown α u V}
  set B : Set ℝ :=
    {u ∈ Set.Icc (0 : ℝ) 1 | ¬ ∀ V' ∈ Set.Icc (V / ρ) V, roundDown α u V' = roundDown α u V}
  have hB_eq : B = Set.Icc (0 : ℝ) 1 \ C := by
    ext u
    simp only [B, C, Set.mem_sdiff, Set.mem_sep_iff, not_and]
    exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun _ => h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2 h1⟩⟩
  have hC_meas : MeasurableSet C := measurableSet_roundDown_consensus hα hρ1 hρα hV
  have hB_meas : MeasurableSet B := hB_eq ▸ measurableSet_Icc.diff hC_meas
  have hdisj : Disjoint C B := Set.disjoint_left.2 fun _ h1 h2 => h2.2 h1.2
  have hunion : C ∪ B = Set.Icc (0 : ℝ) 1 := by
    ext u
    simp only [C, B, Set.mem_union, Set.mem_sep_iff]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hp : ∀ V' ∈ Set.Icc (V / ρ) V, roundDown α u V' = roundDown α u V
      · exact Or.inl ⟨h, hp⟩
      · exact Or.inr ⟨h, hp⟩
  have hC_fin : volume C ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono fun _ hu => hu.1)
  have hB_fin : volume B ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono fun _ hu => hu.1)
  have hsum : volume.real (C ∪ B) = volume.real C + volume.real B :=
    measureReal_union hdisj hB_meas hC_fin hB_fin
  rw [hunion, Real.volume_real_Icc_of_le zero_le_one,
    volume_real_roundDown_consensus hα hρ1 hρα hV] at hsum
  linarith

/-- **Lemma 13.47** ([HartlineKarlin2007], §13.4.6, p. 350): `roundDown α` is a `ρ`-consensus
with failure probability `Real.logb α ρ` (consensus probability `1 - Real.logb α ρ`) whenever
`1 < α` and `1 ≤ ρ ≤ α`. -/
theorem roundDown_isRhoConsensus {α ρ : ℝ} (hα : 1 < α) (hρ1 : 1 ≤ ρ) (hρα : ρ ≤ α) :
    IsRhoConsensus (roundDown α) ρ (Real.logb α ρ) :=
  fun _ hV => (volume_real_roundDown_nonconsensus hα hρ1 hρα hV).le

/-- Explicit integral of `u ↦ α ^ (c + u)` on `[a, b]` for `1 < α`. -/
private theorem integral_rpow_add {α : ℝ} (hα : 1 < α) (c a b : ℝ) :
    ∫ u in a..b, α ^ (c + u) = (α ^ (c + b) - α ^ (c + a)) / Real.log α := by
  have hα0 : 0 < α := by linarith
  have hlog_pos : 0 < Real.log α := Real.log_pos hα
  have hrew : ∀ u : ℝ, α ^ (c + u) = α ^ c * Real.exp (Real.log α * u) := fun u => by
    rw [Real.rpow_add hα0, Real.rpow_def_of_pos hα0, Real.rpow_def_of_pos hα0]
  simp_rw [hrew, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_mul_left (fun t => Real.exp t) hlog_pos.ne',
    integral_exp]
  rw [smul_eq_mul]
  field_simp [hlog_pos.ne']

/-- **Lemma 13.48 (exact expectation)** ([HartlineKarlin2007], §13.4.6, p. 350): for `1 < α` and
`V > 0`, `∫ u in (0 : ℝ)..1, roundDown α u V = V / ((α * Real.log α) / (α - 1))`. -/
theorem integral_roundDown {α V : ℝ} (hα : 1 < α) (hV : 0 < V) :
    ∫ u in (0 : ℝ)..1, roundDown α u V = V / ((α * Real.log α) / (α - 1)) := by
  set x : ℝ := Real.logb α V
  set k : ℤ := ⌊x⌋
  set f : ℝ := Int.fract x
  have hα0 : 0 < α := by linarith
  have hlog_pos : 0 < Real.log α := Real.log_pos hα
  have hf0 : 0 ≤ f := Int.fract_nonneg x
  have hf1 : f < 1 := Int.fract_lt_one x
  have hkf : (k : ℝ) + f = x := Int.floor_add_fract x
  have hαx : α ^ x = V := Real.rpow_logb hα0 hα.ne' hV
  -- On `[0, f]`, `roundDown α u V = α ^ (k + u)`.
  have hleft : ∀ u ∈ Set.uIoc (0 : ℝ) f, roundDown α u V = α ^ ((k : ℝ) + u) := by
    intro u hu
    rw [Set.uIoc_of_le hf0] at hu
    simp only [roundDown, hV, ↓reduceIte]
    rw [floor_sub_eq_of_le_fract x u hu.1.le hu.2]
  -- On `(f, 1]`, `roundDown α u V = α ^ ((k - 1) + u)`.
  have hright : ∀ u ∈ Set.uIoc f 1, roundDown α u V = α ^ (((k : ℝ) - 1) + u) := by
    intro u hu
    rw [Set.uIoc_of_le hf1.le] at hu
    simp only [roundDown, hV, ↓reduceIte]
    rw [floor_sub_eq_of_fract_lt x u hu.1 hu.2]
    push_cast
    rfl
  have hint_cont : ∀ c a b : ℝ, IntervalIntegrable (fun u => α ^ (c + u)) volume a b := by
    intro c a b
    refine Continuous.intervalIntegrable ?_ a b
    exact continuous_const.rpow (continuous_const.add continuous_id) fun _ => Or.inl hα0.ne'
  have hint1 : IntervalIntegrable (fun u => roundDown α u V) volume 0 f :=
    (hint_cont (k : ℝ) 0 f).congr fun u hu => (hleft u hu).symm
  have hint2 : IntervalIntegrable (fun u => roundDown α u V) volume f 1 :=
    (hint_cont ((k : ℝ) - 1) f 1).congr fun u hu => (hright u hu).symm
  rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2,
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hleft),
    intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall hright),
    integral_rpow_add hα (k : ℝ) 0 f, integral_rpow_add hα ((k : ℝ) - 1) f 1]
  have hkf1 : ((k : ℝ) - 1) + 1 = (k : ℝ) := by ring
  have hkf2 : ((k : ℝ) - 1) + f = x - 1 := by linarith
  have hsub1 : α ^ (x - 1) = V / α := by
    rw [Real.rpow_sub hα0, Real.rpow_one, hαx]
  rw [hkf, add_zero, hkf1, hkf2, hαx, hsub1]
  have hαsub : α - 1 ≠ 0 := by linarith
  field_simp [hlog_pos.ne', hα0.ne', hαsub]
  ring

/-- **Lemma 13.48** ([HartlineKarlin2007], §13.4.6, p. 350): for `1 < α`, `roundDown α` is a
`β`-estimate with `β = (α * Real.log α) / (α - 1)`. -/
theorem roundDown_isBetaEstimate {α : ℝ} (hα : 1 < α) :
    IsBetaEstimate (roundDown α) ((α * Real.log α) / (α - 1)) := by
  have hlog_pos : 0 < Real.log α := Real.log_pos hα
  have hβ_pos : 0 < (α * Real.log α) / (α - 1) :=
    div_pos (mul_pos (by linarith) hlog_pos) (by linarith)
  refine ⟨hβ_pos, fun V hV => ⟨fun u _ => roundDown_le hα u hV.le, ?_⟩⟩
  rw [integral_roundDown hα hV]

end RoundDown

/-! ### CEPE framework (`Exercise 13.11` & `Theorem 13.49`, pp. 350, 361) -/

section CEPE

variable {ι : Type*}

/-- Deterministic CEPE auction parameterized by a profit benchmark `G`, a family of profit
extractors `PE : ℝ → Mechanism ι`, and a deterministic estimate function `r : ℝ → ℝ`: computes
`R = r (G b)` and runs `PE R` on `b` ([HartlineKarlin2007], Exercise 13.11, p. 361). -/
@[expose] def cepeDet (G : (ι → ℝ) → ℝ) (PE : ℝ → Mechanism ι) (r : ℝ → ℝ) : Mechanism ι where
  allocation b i := (PE (r (G b))).allocation b i
  payment b i := (PE (r (G b))).payment b i

/-- **Exercise 13.11(a)** ([HartlineKarlin2007], p. 361; Footnote 2, p. 350): given a nonnegative
monotone benchmark `G`, a nonnegative monotone rounding function `r`, and a family `PE` of DSIC,
normalized mechanisms whose allocations are antitone in the target profit `R ≥ 0` (equivalently,
offered prices in `[0, ∞]` are nondecreasing in `R`), whenever consensus
`r (G (Function.update v i 0)) = r (G v)` holds at nonnegative valuations `v`, truthful bidding
`bᵢ = vᵢ` maximizes bidder `i`'s utility over all `bᵢ ≥ 0`. -/
theorem cepeDet_optimal_response_of_consensus [DecidableEq ι]
    {G : (ι → ℝ) → ℝ} (hG_nonneg : ∀ b, 0 ≤ b → 0 ≤ G b)
    (hG_mono : ∀ ⦃b b'⦄, 0 ≤ b → 0 ≤ b' → b ≤ b' → G b ≤ G b')
    {PE : ℝ → Mechanism ι}
    (hPE_DSIC : ∀ R, 0 ≤ R → (PE R).IsDSIC)
    (hPE_norm : ∀ R, 0 ≤ R → (PE R).IsNormalized)
    (hPE_anti : ∀ ⦃R₁ R₂⦄, 0 ≤ R₁ → R₁ ≤ R₂ → ∀ b, 0 ≤ b → ∀ i,
      (PE R₂).allocation b i ≤ (PE R₁).allocation b i)
    {r : ℝ → ℝ} (hr_nonneg : ∀ V, 0 ≤ V → 0 ≤ r V) (hr_mono : MonotoneOn r (Set.Ici 0))
    {v : ι → ℝ} (hv : 0 ≤ v) {i : ι}
    (hcons : r (G (Function.update v i 0)) = r (G v))
    {b_i : ℝ} (hb_i : 0 ≤ b_i) :
    (cepeDet G PE r).utility i (v i) (Function.update v i b_i) ≤
      (cepeDet G PE r).utility i (v i) v := by
  set v' : ι → ℝ := Function.update v i b_i
  have hv' : 0 ≤ v' := update_nonneg hv i hb_i
  have hv0 : 0 ≤ Function.update v i 0 := update_nonneg hv i le_rfl
  set R_star : ℝ := r (G v)
  set R' : ℝ := r (G v')
  have hR_star0 : 0 ≤ R_star := hr_nonneg _ (hG_nonneg v hv)
  have hR'0 : 0 ≤ R' := hr_nonneg _ (hG_nonneg v' hv')
  rcases le_total b_i (v i) with hle | hge
  · have hle1 : Function.update v i 0 ≤ v' := fun j => by
      by_cases hj : j = i
      · subst hj; simpa only [v', Function.update_self] using hb_i
      · simp only [v', Function.update_of_ne hj, le_refl]
    have hle2 : v' ≤ v := fun j => by
      by_cases hj : j = i
      · subst hj; simpa only [v', Function.update_self] using hle
      · simp only [v', Function.update_of_ne hj, le_refl]
    have hR_eq : R' = R_star := le_antisymm
      (hr_mono (hG_nonneg v' hv') (hG_nonneg v hv) (hG_mono hv' hv hle2))
      (hcons ▸ hr_mono (hG_nonneg _ hv0) (hG_nonneg v' hv') (hG_mono hv0 hv' hle1))
    have hdsic := hPE_DSIC R_star hR_star0 i v' (v i) hv' (hv i)
    have hupd_back : Function.update v' i (v i) = v := by
      simp only [v', Function.update_idem, Function.update_eq_self]
    rw [hupd_back] at hdsic
    dsimp only [R_star, R'] at hR_eq hdsic
    simpa only [Mechanism.utility, cepeDet, hR_eq] using hdsic
  · have hv_le : v ≤ v' := fun j => by
      by_cases hj : j = i
      · subst hj; simpa only [v', Function.update_self] using hge
      · simp only [v', Function.update_of_ne hj, le_refl]
    have hR_le : R_star ≤ R' :=
      hr_mono (hG_nonneg v hv) (hG_nonneg v' hv') (hG_mono hv hv' hv_le)
    have hdsic := hPE_DSIC R' hR'0 i v' (v i) hv' (hv i)
    have hupd_back : Function.update v' i (v i) = v := by
      simp only [v', Function.update_idem, Function.update_eq_self]
    rw [hupd_back] at hdsic
    -- By Myerson's utility identity, truthful utility is `∫₀^{vᵢ} xᵢ(z, v₋ᵢ) dz`, antitone in `R`.
    have hutil_eq : ∀ R, 0 ≤ R →
        (PE R).utility i (v i) v =
          ∫ z in (0 : ℝ)..v i, (PE R).allocation (Function.update v i z) i := by
      intro R hR
      have hpay := (hPE_DSIC R hR).payment_eq_myersonPayment (hPE_norm R hR) i hv
      have := utility_myerson (PE R).allocation i v
      simp only [Mechanism.utility, myerson] at this ⊢
      rw [hpay]
      exact this
    have hint : ∀ R, 0 ≤ R →
        IntervalIntegrable (fun z => (PE R).allocation (Function.update v i z) i) volume 0 (v i) :=
      fun R hR =>
        (((hPE_DSIC R hR).isMonotone i v hv).mono fun c (hc : c ∈ Set.uIcc 0 (v i)) =>
          le_trans (le_inf le_rfl (hv i)) hc.1).intervalIntegrable
    have hutil_le : (PE R').utility i (v i) v ≤ (PE R_star).utility i (v i) v := by
      rw [hutil_eq R' hR'0, hutil_eq R_star hR_star0]
      exact intervalIntegral.integral_mono_on (hv i) (hint R' hR'0) (hint R_star hR_star0)
        fun z hz => hPE_anti hR_star0 hR_le _ (update_nonneg hv i hz.1) i
    exact hdsic.trans hutil_le

/-- The randomized **CEPE** (Consensus Estimate Profit Extraction) auction
([HartlineKarlin2007], §13.4.6, Theorem 13.49, p. 350), indexed by the uniform draw `u ∈ [0, 1]`. -/
@[expose] noncomputable def cepe (G : (ι → ℝ) → ℝ) (PE : ℝ → Mechanism ι) (α u : ℝ) :
    Mechanism ι :=
  cepeDet G PE (roundDown α u)

/-- Expected profit of `cepe G PE α` over `U ~ Uniform[0, 1]` for a single-parameter problem with
seller production cost `c : (ι → ℝ) → ℝ` ([HartlineKarlin2007], §13.1, pp. 331–332; §13.4.6,
p. 350). -/
@[expose] noncomputable def cepeExpectedProfit [Fintype ι] (G : (ι → ℝ) → ℝ)
    (PE : ℝ → Mechanism ι) (c : (ι → ℝ) → ℝ) (α : ℝ) (b : ι → ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    ((∑ i, (cepe G PE α u).payment b i) - c ((cepe G PE α u).allocation b))

/-- Exact expected profit of **CEPE** ([HartlineKarlin2007], Theorem 13.49, p. 350): when `PE`
extracts profit `R` whenever `0 ≤ R ≤ G b`, the expected profit of `cepe G PE α` on `b ≥ 0` equals
`G b / ((α * Real.log α) / (α - 1))`. -/
theorem cepeExpectedProfit_eq [Fintype ι] {G : (ι → ℝ) → ℝ}
    (hG_nonneg : ∀ b, 0 ≤ b → 0 ≤ G b) {PE : ℝ → Mechanism ι} {c : (ι → ℝ) → ℝ}
    (hPE_extract : ∀ R b, 0 ≤ b → 0 ≤ R → R ≤ G b →
      (∑ i, (PE R).payment b i) - c ((PE R).allocation b) = R)
    {α : ℝ} (hα : 1 < α) {b : ι → ℝ} (hb : 0 ≤ b) :
    cepeExpectedProfit G PE c α b = G b / ((α * Real.log α) / (α - 1)) := by
  have hpoint : ∀ u : ℝ,
      (∑ i, (cepe G PE α u).payment b i) - c ((cepe G PE α u).allocation b) =
        roundDown α u (G b) := fun u =>
    hPE_extract (roundDown α u (G b)) b hb (roundDown_nonneg hα u (G b))
      (roundDown_le hα u (hG_nonneg b hb))
  unfold cepeExpectedProfit
  simp_rw [hpoint]
  rcases (hG_nonneg b hb).eq_or_lt with h0 | hpos
  · rw [← h0]
    simp_rw [roundDown_of_nonpos α _ le_rfl]
    simp only [intervalIntegral.integral_zero, zero_div]
  · exact integral_roundDown hα hpos

/-- **Theorem 13.49 (competitive ratio)** ([HartlineKarlin2007], §13.4.6, p. 350; Exercise 13.11(b),
p. 361): `CEPE` is `(α * Real.log α) / (α - 1)`-competitive against the profit benchmark `G`. -/
theorem cepe_isCompetitive [Fintype ι] {G : (ι → ℝ) → ℝ}
    (hG_nonneg : ∀ b, 0 ≤ b → 0 ≤ G b) {PE : ℝ → Mechanism ι} {c : (ι → ℝ) → ℝ}
    (hPE_extract : ∀ R b, 0 ≤ b → 0 ≤ R → R ≤ G b →
      (∑ i, (PE R).payment b i) - c ((PE R).allocation b) = R)
    {α : ℝ} (hα : 1 < α) :
    IsCompetitive G (cepeExpectedProfit G PE c α) ((α * Real.log α) / (α - 1)) := by
  have hβ_pos : 0 < (α * Real.log α) / (α - 1) :=
    div_pos (mul_pos (by linarith) (Real.log_pos hα)) (by linarith)
  refine ⟨hβ_pos.le, fun b hb => ?_⟩
  rw [cepeExpectedProfit_eq hG_nonneg hPE_extract hα hb, mul_div_cancel₀ _ hβ_pos.ne']

/-- **Theorem 13.49 (simultaneous nontruthfulness failure bound)** ([HartlineKarlin2007], §13.4.6,
p. 350; Exercise 13.11(b), p. 361): on any nonnegative input `v` and bidder `i` satisfying
`G v / ρ ≤ G (Function.update v i 0)` (`1 ≤ ρ ≤ α`), the outer Lebesgue measure of draws
`u ∈ [0, 1]` for which some nonnegative deviation `bᵢ ≥ 0` strictly improves bidder `i`'s utility
is at most `Real.logb α ρ`. -/
theorem cepe_nontruthful_measure_le [DecidableEq ι]
    {G : (ι → ℝ) → ℝ} (hG_nonneg : ∀ b, 0 ≤ b → 0 ≤ G b)
    (hG_mono : ∀ ⦃b b'⦄, 0 ≤ b → 0 ≤ b' → b ≤ b' → G b ≤ G b')
    {PE : ℝ → Mechanism ι}
    (hPE_DSIC : ∀ R, 0 ≤ R → (PE R).IsDSIC)
    (hPE_norm : ∀ R, 0 ≤ R → (PE R).IsNormalized)
    (hPE_anti : ∀ ⦃R₁ R₂⦄, 0 ≤ R₁ → R₁ ≤ R₂ → ∀ b, 0 ≤ b → ∀ i,
      (PE R₂).allocation b i ≤ (PE R₁).allocation b i)
    {α ρ : ℝ} (hα : 1 < α) (hρ1 : 1 ≤ ρ) (hρα : ρ ≤ α)
    {v : ι → ℝ} (hv : 0 ≤ v) {i : ι}
    (hρv : G v / ρ ≤ G (Function.update v i 0)) :
    volume.real
      {u ∈ Set.Icc (0 : ℝ) 1 | ∃ b_i : ℝ, 0 ≤ b_i ∧
        (cepe G PE α u).utility i (v i) v <
          (cepe G PE α u).utility i (v i) (Function.update v i b_i)} ≤
      Real.logb α ρ := by
  have hv0 : 0 ≤ Function.update v i 0 := update_nonneg hv i le_rfl
  have hv0_le : Function.update v i 0 ≤ v := fun j => by
    by_cases hj : j = i
    · rw [hj, Function.update_self]; exact hv i
    · simp only [Function.update_of_ne hj, le_refl]
  have hGv0_le : G (Function.update v i 0) ≤ G v := hG_mono hv0 hv hv0_le
  rcases (hG_nonneg v hv).eq_or_lt with h0 | hpos
  · have hGv0_eq : G (Function.update v i 0) = G v :=
      le_antisymm hGv0_le (h0 ▸ hG_nonneg _ hv0)
    have hempty :
        {u ∈ Set.Icc (0 : ℝ) 1 | ∃ b_i : ℝ, 0 ≤ b_i ∧
          (cepe G PE α u).utility i (v i) v <
            (cepe G PE α u).utility i (v i) (Function.update v i b_i)} = ∅ := by
      ext u
      simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false, not_and, not_exists]
      intro _ b_i hb_i hlt
      exact hlt.not_ge (cepeDet_optimal_response_of_consensus hG_nonneg hG_mono
        hPE_DSIC hPE_norm hPE_anti (fun _ _ => roundDown_nonneg hα u _)
        ((roundDown_mono hα u).monotoneOn _) hv (by rw [hGv0_eq]) hb_i)
    rw [hempty, measureReal_empty]
    exact Real.logb_nonneg hα hρ1
  · set B : Set ℝ :=
      {u ∈ Set.Icc (0 : ℝ) 1 |
        ¬ ∀ V' ∈ Set.Icc (G v / ρ) (G v), roundDown α u V' = roundDown α u (G v)}
    have hsub :
        {u ∈ Set.Icc (0 : ℝ) 1 | ∃ b_i : ℝ, 0 ≤ b_i ∧
          (cepe G PE α u).utility i (v i) v <
            (cepe G PE α u).utility i (v i) (Function.update v i b_i)} ⊆ B := by
      rintro u ⟨hu, b_i, hb_i, hlt⟩
      refine ⟨hu, fun hcons => hlt.not_ge ?_⟩
      exact cepeDet_optimal_response_of_consensus hG_nonneg hG_mono
        hPE_DSIC hPE_norm hPE_anti (fun _ _ => roundDown_nonneg hα u _)
        ((roundDown_mono hα u).monotoneOn _) hv
        (hcons (G (Function.update v i 0)) ⟨hρv, hGv0_le⟩) hb_i
    have hB_fin : volume B ≠ ⊤ :=
      ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono fun _ hu => hu.1)
    exact (ENNReal.toReal_mono hB_fin (measure_mono hsub)).trans_eq
      (volume_real_roundDown_nonconsensus hα hρ1 hρα hpos)

/-- **Theorem 13.49 (truthfulness with high probability)** ([HartlineKarlin2007], §13.4.6, p. 350;
Definition 13.43, p. 349; Exercise 13.11(b), p. 361): on inputs satisfying
`G v / ρ ≤ G (Function.update v i 0)` (`1 ≤ ρ ≤ α`), `CEPE` is truthful at `(v, i)` with
failure probability at most `Real.logb α ρ` (truthfulness probability at least
`1 - Real.logb α ρ`). -/
theorem cepe_isTruthfulWithHighProbAt [DecidableEq ι]
    {G : (ι → ℝ) → ℝ} (hG_nonneg : ∀ b, 0 ≤ b → 0 ≤ G b)
    (hG_mono : ∀ ⦃b b'⦄, 0 ≤ b → 0 ≤ b' → b ≤ b' → G b ≤ G b')
    {PE : ℝ → Mechanism ι}
    (hPE_DSIC : ∀ R, 0 ≤ R → (PE R).IsDSIC)
    (hPE_norm : ∀ R, 0 ≤ R → (PE R).IsNormalized)
    (hPE_anti : ∀ ⦃R₁ R₂⦄, 0 ≤ R₁ → R₁ ≤ R₂ → ∀ b, 0 ≤ b → ∀ i,
      (PE R₂).allocation b i ≤ (PE R₁).allocation b i)
    {α ρ : ℝ} (hα : 1 < α) (hρ1 : 1 ≤ ρ) (hρα : ρ ≤ α)
    {v : ι → ℝ} (hv : 0 ≤ v) {i : ι}
    (hρv : G v / ρ ≤ G (Function.update v i 0)) :
    IsTruthfulWithHighProbAt (cepe G PE α) v i (Real.logb α ρ) := by
  intro b_i hb_i
  have hsub :
      {u ∈ Set.Icc (0 : ℝ) 1 |
        (cepe G PE α u).utility i (v i) v <
          (cepe G PE α u).utility i (v i) (Function.update v i b_i)} ⊆
      {u ∈ Set.Icc (0 : ℝ) 1 | ∃ b_i : ℝ, 0 ≤ b_i ∧
        (cepe G PE α u).utility i (v i) v <
          (cepe G PE α u).utility i (v i) (Function.update v i b_i)} :=
    fun _ hu => ⟨hu.1, b_i, hb_i, hu.2⟩
  have hfin : volume
      {u ∈ Set.Icc (0 : ℝ) 1 | ∃ b_i : ℝ, 0 ≤ b_i ∧
        (cepe G PE α u).utility i (v i) v <
          (cepe G PE α u).utility i (v i) (Function.update v i b_i)} ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Icc]) (measure_mono fun _ hu => hu.1)
  exact (ENNReal.toReal_mono hfin (measure_mono hsub)).trans
    (cepe_nontruthful_measure_le hG_nonneg hG_mono hPE_DSIC hPE_norm hPE_anti hα hρ1 hρα hv hρv)

end CEPE

/-! ### Digital goods instantiation (`§13.4.6`, p. 349) -/

section DigitalGoodsCEPE

variable {ι : Type*}

/-- `singlePriceProfitOn m s` is monotone in the bid profile `b` on nonnegative bids. -/
theorem singlePriceProfitOn_mono {m : ℕ} {s : Finset ι} {b b' : ι → ℝ}
    (hb : ∀ i ∈ s, 0 ≤ b i) (hle : ∀ i ∈ s, b i ≤ b' i) :
    singlePriceProfitOn m s b ≤ singlePriceProfitOn m s b' := by
  classical
  have hb' : ∀ i ∈ s, 0 ≤ b' i := fun i hi => (hb i hi).trans (hle i hi)
  rcases lt_or_ge s.card m with hsmall | hcard
  · rw [singlePriceProfitOn_eq_zero_of_card_lt b hsmall]
    exact singlePriceProfitOn_nonneg hb'
  · rcases s.eq_empty_or_nonempty with rfl | hsne
    · simp only [singlePriceProfitOn_empty, le_refl]
    · obtain ⟨j, hj, hjm, hjeq⟩ := exists_mem_eq_singlePriceProfitOn hsne hcard (b := b)
      rw [hjeq]
      exact mul_card_le_singlePriceProfitOn hb' (filter_subset _ _) hjm fun i hi =>
        (mem_filter.1 hi).2.trans (hle i (mem_filter.1 hi).1)

/-- For nonnegative bids, `ℱ⁽²⁾(b) ≤ ℱ(b)`. -/
theorem optimalProfitTwo_le_optimalProfit [Fintype ι] {b : ι → ℝ} (hb : 0 ≤ b) :
    optimalProfitTwo b ≤ optimalProfit b :=
  singlePriceProfitOn_le (singlePriceProfitOn_nonneg fun i _ => hb i) fun j _ hj =>
    mul_card_le_singlePriceProfitOn (fun i _ => hb i) (filter_subset _ _) (by omega)
      fun i hi => (mem_filter.1 hi).2

/-- The allocation rule of `profitExtractOn s R` is antitone in the target profit `R ≥ 0`
(equivalently, each bidder's offered threshold price in `ProfitExtract_R` is nondecreasing in `R`,
[HartlineKarlin2007], §13.4.6, Footnote 2, p. 350). -/
theorem profitExtractOn_allocation_antitone (s : Finset ι) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁)
    (hR : R₁ ≤ R₂) (b : ι → ℝ) (i : ι) :
    (profitExtractOn s R₂).allocation b i ≤ (profitExtractOn s R₁).allocation b i := by
  classical
  have hR₂ : 0 ≤ R₂ := hR₁.trans hR
  dsimp only [profitExtractOn]
  by_cases hwin₂ : i ∈ s ∧ 0 < profitExtractSize s R₂ b ∧
      R₂ / (profitExtractSize s R₂ b : ℝ) ≤ b i
  · rw [ite_eq_left hwin₂]
    obtain ⟨his, hk₂_pos, hbid₂⟩ := hwin₂
    have hmem₂ : profitExtractSize s R₂ b ∈ (Finset.Icc 1 s.card).filter fun k : ℕ =>
        k ≤ (s.filter fun j => R₂ / (k : ℝ) ≤ b j).card := by
      have hk₂_pos' := hk₂_pos
      unfold profitExtractSize at hk₂_pos'
      simp only [hR₂, ↓reduceIte] at hk₂_pos'
      split_ifs at hk₂_pos' with hne
      · unfold profitExtractSize
        simp only [hR₂, hne, ↓reduceIte, ↓reduceDIte]
        exact max'_mem _ hne
      · exact absurd hk₂_pos' (lt_irrefl 0)
    set k₂ := profitExtractSize s R₂ b
    have hmem₁ : k₂ ∈ (Finset.Icc 1 s.card).filter fun k : ℕ =>
        k ≤ (s.filter fun j => R₁ / (k : ℝ) ≤ b j).card := by
      refine mem_filter.2 ⟨(mem_filter.1 hmem₂).1,
        (mem_filter.1 hmem₂).2.trans (card_le_card fun j hj => ?_)⟩
      refine mem_filter.2 ⟨(mem_filter.1 hj).1, ?_⟩
      exact (div_le_div_of_nonneg_right hR (Nat.cast_nonneg k₂)).trans (mem_filter.1 hj).2
    have hk₂_le_k₁ : k₂ ≤ profitExtractSize s R₁ b := by
      unfold profitExtractSize
      simp only [hR₁, ↓reduceIte]
      have hne₁ : ((Finset.Icc 1 s.card).filter fun k : ℕ =>
          k ≤ (s.filter fun j => R₁ / (k : ℝ) ≤ b j).card).Nonempty := ⟨k₂, hmem₁⟩
      rw [dite_eq_left hne₁]
      exact le_max' _ k₂ hmem₁
    have hwin₁ : i ∈ s ∧ 0 < profitExtractSize s R₁ b ∧
        R₁ / (profitExtractSize s R₁ b : ℝ) ≤ b i := by
      refine ⟨his, hk₂_pos.trans_le hk₂_le_k₁, ?_⟩
      calc R₁ / (profitExtractSize s R₁ b : ℝ)
          ≤ R₁ / (k₂ : ℝ) :=
            div_le_div_of_nonneg_left hR₁ (Nat.cast_pos.2 hk₂_pos) (Nat.cast_le.2 hk₂_le_k₁)
        _ ≤ R₂ / (k₂ : ℝ) := div_le_div_of_nonneg_right hR (Nat.cast_nonneg k₂)
        _ ≤ b i := hbid₂
    rw [ite_eq_left hwin₁]
  · rw [ite_eq_right hwin₂]
    split_ifs <;> norm_num

/-- **Digital goods CEPE auction** ([HartlineKarlin2007], §13.4.6, pp. 349–350): runs
`ProfitExtract_R` with `R = roundDown α u (ℱ⁽²⁾(b))`. -/
@[expose] noncomputable def cepeDigitalGoods [Fintype ι] (α u : ℝ) : Mechanism ι :=
  cepe optimalProfitTwo profitExtract α u

/-- **Digital goods CEPE competitive ratio**: `cepeDigitalGoods α` is
`(α * Real.log α) / (α - 1)`-competitive against `ℱ⁽²⁾` with zero seller cost. -/
theorem cepeDigitalGoods_isCompetitive [Fintype ι] {α : ℝ} (hα : 1 < α) :
    IsCompetitive (optimalProfitTwo (ι := ι))
      (cepeExpectedProfit optimalProfitTwo profitExtract (fun _ => 0) α)
      ((α * Real.log α) / (α - 1)) :=
  cepe_isCompetitive (fun _ hb => singlePriceProfitOn_nonneg fun i _ => hb i)
    (fun R b hb hR hle => by
      simpa only [sub_zero] using
        sum_payment_profitExtract_of_le hR hb (hle.trans (optimalProfitTwo_le_optimalProfit hb)))
    hα

/-- **Digital goods CEPE truthfulness (`1 - O(1/m)`)** ([HartlineKarlin2007], §13.4.6, p. 349):
when `ℱ⁽²⁾(v)` is attained by `m = W.card ≥ 3` winners at price `p` and `m / (m - 1) ≤ α`,
`cepeDigitalGoods α` is truthful for every bidder `i` with probability at least
`1 - Real.logb α (m / (m - 1))`, which is in turn at least `1 - 1 / ((m - 1) * Real.log α)`.

The hypothesis `3 ≤ W.card` is tight: when `W.card = 2`, removing one winner can drop `ℱ⁽²⁾` to
`0` (since `ℱ⁽²⁾` requires at least two winners). -/
theorem cepeDigitalGoods_truthful_of_winners [Fintype ι] [DecidableEq ι]
    {α : ℝ} (hα : 1 < α) {v : ι → ℝ} (hv : 0 ≤ v)
    {W : Finset ι} {p : ℝ} (hp : 0 ≤ p) (hW3 : 3 ≤ W.card)
    (hWb : ∀ j ∈ W, p ≤ v j) (hF2 : optimalProfitTwo v = p * (W.card : ℝ))
    (hρα : (W.card : ℝ) / ((W.card : ℝ) - 1) ≤ α) (i : ι) :
    IsTruthfulWithHighProbAt (cepeDigitalGoods α) v i
        (Real.logb α ((W.card : ℝ) / ((W.card : ℝ) - 1))) ∧
      Real.logb α ((W.card : ℝ) / ((W.card : ℝ) - 1)) ≤
        1 / (((W.card : ℝ) - 1) * Real.log α) := by
  have hm3 : (3 : ℝ) ≤ (W.card : ℝ) := by exact_mod_cast hW3
  have hm1_pos : (0 : ℝ) < (W.card : ℝ) - 1 := by linarith
  set ρ : ℝ := (W.card : ℝ) / ((W.card : ℝ) - 1)
  have hρ1 : 1 ≤ ρ := (one_le_div hm1_pos).2 (by linarith)
  have hρv : optimalProfitTwo v / ρ ≤ optimalProfitTwo (Function.update v i 0) := by
    have hcard_erase : W.card - 1 ≤ (W.erase i).card := by
      by_cases hi : i ∈ W
      · rw [card_erase_of_mem hi]
      · rw [erase_eq_of_notMem hi]; omega
    have hcard2 : 2 ≤ (W.erase i).card := by omega
    have hle := mul_card_le_singlePriceProfitOn (m := 2) (s := univ) (W := W.erase i)
      (b := Function.update v i 0) (p := p)
      (fun j _ => update_nonneg hv i le_rfl j) (subset_univ _) hcard2 fun j hj => by
        rw [Function.update_of_ne (mem_erase.1 hj).1]
        exact hWb j (mem_erase.1 hj).2
    have hcast : (W.card : ℝ) - 1 ≤ ((W.erase i).card : ℝ) := by
      have h1 : ((W.card - 1 : ℕ) : ℝ) ≤ ((W.erase i).card : ℝ) := by exact_mod_cast hcard_erase
      rw [Nat.cast_sub (by omega : 1 ≤ W.card), Nat.cast_one] at h1
      exact h1
    have hdiv : optimalProfitTwo v / ρ = p * ((W.card : ℝ) - 1) := by
      rw [hF2]; dsimp only [ρ]; field_simp [hm1_pos.ne']
    rw [hdiv]
    exact (mul_le_mul_of_nonneg_left hcast hp).trans hle
  refine ⟨cepe_isTruthfulWithHighProbAt
      (fun _ hb => singlePriceProfitOn_nonneg fun j _ => hb j)
      (fun _ _ hb _ hle => singlePriceProfitOn_mono (fun j _ => hb j) fun j _ => hle j)
      (fun R _ => profitExtractOn_isDSIC univ R)
      (fun R _ => profitExtractOn_isNormalized univ R)
      (fun _ _ hR₁ hR b _ j => profitExtractOn_allocation_antitone univ hR₁ hR b j)
      hα hρ1 hρα hv hρv, ?_⟩
  rw [Real.logb]
  have hlog_pos : 0 < Real.log α := Real.log_pos hα
  have hlog_le : Real.log ρ ≤ 1 / ((W.card : ℝ) - 1) := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith) hm1_pos : 0 < ρ)
    have hsub : ρ - 1 = 1 / ((W.card : ℝ) - 1) := by
      dsimp only [ρ]; field_simp [hm1_pos.ne']; ring
    rwa [hsub] at h
  calc Real.log ρ / Real.log α
      ≤ (1 / ((W.card : ℝ) - 1)) / Real.log α := div_le_div_of_nonneg_right hlog_le hlog_pos.le
    _ = 1 / (((W.card : ℝ) - 1) * Real.log α) := by rw [div_div]

end DigitalGoodsCEPE

end Cslib.GameTheory.SingleParameter.DigitalGoods
