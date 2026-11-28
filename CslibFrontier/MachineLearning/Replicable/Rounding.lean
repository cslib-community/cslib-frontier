/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.MachineLearning.Replicable.Basic
public import CslibFrontier.Languages.Probabilistic.Basic
public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import CslibFrontier.Languages.Probabilistic.Semantics
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EventBind
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Order.Floor.BigOperators

/-!
# Randomized-threshold rounding rules

This module formalizes the randomized-threshold and periodic grid rounding primitives from
Impagliazzo–Lei–Pitassi–Sorrell [ImpagliazzoLeiPitassiSorrell2022]:

* **Bounded interval threshold rounding**: `thresholdRound a b N i x` compares a real statistic `x`
  against a discrete uniform grid threshold `thresholdValue a b N i ∈ [a, b)` for `i : Fin N`, and
  `continuousThresholdRound a b u x` is its continuous counterpart for `u ∈ [0, 1)`. Two inputs
  `x₁, x₂` disagree with probability at most `|x₁ - x₂| / (b - a) + 1 / N` discretely, and with
  Lebesgue measure at most `|x₁ - x₂| / (b - a)` continuously.
* **Periodic grid rounding**: `roundGrid w N i x` snaps an arbitrary real `x` to the midpoint of a
  randomly shifted interval of width `w` with discrete shift `i / N` (`i : Fin N`). Every rounded
  output lies within `w / 2` of `x` (`abs_roundGrid_sub_le`), and two inputs `x₁, x₂` land in
  different grid bins with probability at most `|x₁ - x₂| / w + 1 / N` (`roundGrid_disagree_le`,
  proved via Hermite's identity `Int.sum_floor_add_div`). The continuous counterpart
  `continuousRoundGrid w u x` has disagreement Lebesgue measure at most `|x₁ - x₂| / w`.
* **Replicable rounding of concentrating estimators**: any deterministic estimator `est` that
  concentrates within `δ` of `target D` except with probability `β` becomes both
  `(w / 2 + δ, β)`-accurate and `(2 * δ / w + 1 / N + 2 * β)`-replicable under `roundGridProg`.

## Main definitions

* `Cslib.MachineLearning.Replicable.thresholdValue`,
  `Cslib.MachineLearning.Replicable.thresholdRound`,
  `Cslib.MachineLearning.Replicable.thresholdProg`: discrete shared-seed threshold rounding.
* `Cslib.MachineLearning.Replicable.roundGridBin`, `Cslib.MachineLearning.Replicable.roundGrid`,
  `Cslib.MachineLearning.Replicable.roundGridProg`: periodic shared-seed grid rounding.
* `Cslib.MachineLearning.Replicable.continuousThresholdRound`,
  `Cslib.MachineLearning.Replicable.continuousRoundGridBin`,
  `Cslib.MachineLearning.Replicable.continuousRoundGrid`: continuous `[0, 1)` rounding rules.

## Main results

* `Cslib.MachineLearning.Replicable.thresholdRound_disagree_le`: discrete `[a, b)` threshold
  disagreement probability `≤ |x₁ - x₂| / (b - a) + 1 / N`.
* `Cslib.MachineLearning.Replicable.abs_roundGrid_sub_le`: `|roundGrid w N i x - x| ≤ w / 2`.
* `Cslib.MachineLearning.Replicable.roundGrid_disagree_le`: periodic grid rounding disagreement
  probability `≤ |x₁ - x₂| / w + 1 / N`.
* `Cslib.MachineLearning.Replicable.volume_thresholdRound_ne_le`,
  `Cslib.MachineLearning.Replicable.volume_roundGrid_ne_le`: continuous Lebesgue-measure rounding
  lemmas.
* `Cslib.MachineLearning.Replicable.isAccurateFor_roundGridProg_of_concentrates`,
  `Cslib.MachineLearning.Replicable.isReplicableFor_roundGridProg_of_concentrates`: turning any
  concentrating estimator into a replicable accurate `Program`.

## References

* [Impagliazzo, Lei, Pitassi, Sorrell (STOC 2022)][ImpagliazzoLeiPitassiSorrell2022],
  *Reproducibility in Learning* (paper PDF not directly inspected; rounding bounds and
  `MeasureTheory.volume` / `ProbComp` formulations are formalized directly in Lean).
-/

public section

namespace Cslib.MachineLearning.Replicable

section Definitions

/-- Grid threshold at index `i : Fin N` partitioning `[a, b)`. -/
@[expose] noncomputable def thresholdValue (a b : ℝ) (N : ℕ) (i : Fin N) : ℝ :=
  a + (b - a) * (i : ℝ) / N

/-- Randomized-threshold boolean rounding on `[a, b)` using shared discrete seed `i : Fin N`. -/
@[expose] noncomputable def thresholdRound (a b : ℝ) (N : ℕ) (i : Fin N) (x : ℝ) : Bool :=
  decide (thresholdValue a b N i ≤ x)

/-- `ProbComp`-backed ideal real-arithmetic threshold-rounding `Program` applied to a real
estimator `est` (interpreted via `Program.toAlgorithm`). -/
@[expose] noncomputable def thresholdProg {X : Type} {m : ℕ} (a b : ℝ) (N : ℕ) [NeZero N]
    (est : (Fin m → X) → ℝ) : Program X (Fin N) Bool m :=
  Program.deterministic (ProbComp.uniform (Fin N)) (fun S i => thresholdRound a b N i (est S))

/-- Periodic grid bin index of `x` with grid width `w` and discrete random phase `i : Fin N`. -/
@[expose] noncomputable def roundGridBin (w : ℝ) (N : ℕ) (i : Fin N) (x : ℝ) : ℤ :=
  ⌊x / w + (i : ℝ) / N⌋

/-- Periodic randomized grid rounding: snaps `x` to the midpoint of its shifted `w`-bin. -/
@[expose] noncomputable def roundGrid (w : ℝ) (N : ℕ) (i : Fin N) (x : ℝ) : ℝ :=
  ((roundGridBin w N i x : ℝ) + 1 / 2 - (i : ℝ) / N) * w

/-- `ProbComp`-backed ideal real-arithmetic periodic grid-rounding `Program` applied to a real
estimator `est` (interpreted via `Program.toAlgorithm`). -/
@[expose] noncomputable def roundGridProg {X : Type} {m : ℕ} (w : ℝ) (N : ℕ) [NeZero N]
    (est : (Fin m → X) → ℝ) : Program X (Fin N) ℝ m :=
  Program.deterministic (ProbComp.uniform (Fin N)) (fun S i => roundGrid w N i (est S))

/-- Continuous randomized-threshold boolean rounding on `[a, b]` using `u ∈ [0, 1)`. -/
@[expose] noncomputable def continuousThresholdRound (a b u x : ℝ) : Bool :=
  decide (a + (b - a) * u ≤ x)

/-- Continuous periodic grid bin index with width `w` and shift `u ∈ [0, 1)`. -/
@[expose] noncomputable def continuousRoundGridBin (w u x : ℝ) : ℤ :=
  ⌊x / w + u⌋

/-- Continuous periodic grid rounding with width `w` and shift `u ∈ [0, 1)`. -/
@[expose] noncomputable def continuousRoundGrid (w u x : ℝ) : ℝ :=
  ((continuousRoundGridBin w u x : ℝ) + 1 / 2 - u) * w

end Definitions

section DeterministicProperties

theorem thresholdRound_false_of_lt_left {a b : ℝ} (hab : a ≤ b) {N : ℕ} (i : Fin N) {x : ℝ}
    (hx : x < a) : thresholdRound a b N i x = false := by
  have hnonneg : 0 ≤ (b - a) * (i : ℝ) / N := by positivity [sub_nonneg.mpr hab]
  exact decide_eq_false (not_le.mpr (by unfold thresholdValue; linarith))

theorem thresholdRound_true_of_right_le {a b : ℝ} (hab : a ≤ b) {N : ℕ} (i : Fin N) {x : ℝ}
    (hx : b ≤ x) : thresholdRound a b N i x = true := by
  rcases eq_or_ne N 0 with rfl | hN
  · exact i.elim0
  · have hpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hle : (i : ℝ) / N ≤ 1 := (div_le_one hpos).mpr (by exact_mod_cast i.isLt.le)
    have hmul : (b - a) * ((i : ℝ) / N) ≤ b - a := mul_le_of_le_one_right (sub_nonneg.mpr hab) hle
    exact decide_eq_true (by
      unfold thresholdValue
      linarith [show (b - a) * (i : ℝ) / N = (b - a) * ((i : ℝ) / N) by ring])

private theorem abs_floor_add_half_sub_mul_le {w : ℝ} (hw : 0 < w) (t : ℝ) :
    |((⌊t⌋ : ℝ) + 1 / 2 - t) * w| ≤ w / 2 := by
  have ht : |(⌊t⌋ : ℝ) + 1 / 2 - t| ≤ 1 / 2 :=
    abs_le.mpr ⟨by linarith [Int.lt_floor_add_one t], by linarith [Int.floor_le t]⟩
  rw [abs_mul, abs_of_pos hw]
  linarith [mul_le_mul_of_nonneg_right ht hw.le]

/-- Deterministic discretization error of `roundGrid`: always within `w / 2` of `x`. -/
theorem abs_roundGrid_sub_le {w : ℝ} (hw : 0 < w) (N : ℕ) (i : Fin N) (x : ℝ) :
    |roundGrid w N i x - x| ≤ w / 2 := by
  convert abs_floor_add_half_sub_mul_le hw (x / w + (i : ℝ) / N) using 2
  simp only [roundGrid, roundGridBin]
  field_simp [hw.ne']
  ring

/-- Deterministic discretization error of `continuousRoundGrid`: always within `w / 2` of `x`. -/
theorem abs_continuousRoundGrid_sub_le {w : ℝ} (hw : 0 < w) (u x : ℝ) :
    |continuousRoundGrid w u x - x| ≤ w / 2 := by
  convert abs_floor_add_half_sub_mul_le hw (x / w + u) using 2
  simp only [continuousRoundGrid, continuousRoundGridBin]
  field_simp [hw.ne']
  ring

end DeterministicProperties

section DiscreteDisagreement

/-- Two thresholds `x₁ ≤ x₂` disagree at a cut `v` only when `x₁ < v ≤ x₂`. -/
private theorem lt_and_le_of_decide_ne {v x₁ x₂ : ℝ} (hx : x₁ ≤ x₂)
    (h : decide (v ≤ x₁) ≠ decide (v ≤ x₂)) : x₁ < v ∧ v ≤ x₂ :=
  ⟨not_le.mp fun h1 => h (by simp [h1, h1.trans hx]),
    by_contra fun h2 => h (by simp [h2, hx.trans_lt (not_le.mp h2)])⟩

private theorem thresholdRound_disagree_le_of_le {a b : ℝ} (hab : a < b) {N : ℕ} [NeZero N]
    {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
      {i : Fin N | thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂}).toReal ≤
      (x₂ - x₁) / (b - a) + 1 / N := by
  classical
  rw [Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fin]
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hba : 0 < b - a := sub_pos.mpr hab
  let u₁ : ℝ := (N : ℝ) * (x₁ - a) / (b - a)
  let u₂ : ℝ := (N : ℝ) * (x₂ - a) / (b - a)
  have hcard := Finset.card_le_card_of_injOn (s := Finset.univ.filter
      (· ∈ {i : Fin N | thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂}))
    (t := Finset.Ioc ⌊u₁⌋ ⌊u₂⌋) (fun i : Fin N => (i.val : ℤ)) (fun i hi => by
      obtain ⟨h1, h2⟩ := lt_and_le_of_decide_ne hx (v := thresholdValue a b N i)
        (by simpa [thresholdRound] using hi)
      simp only [thresholdValue] at h1 h2
      refine Finset.mem_Ioc.mpr ⟨Int.floor_lt.mpr ?_, Int.le_floor.mpr ?_⟩ <;>
        push_cast <;> dsimp only [u₁, u₂]
      · rw [div_lt_iff₀ hba]
        linarith [(lt_div_iff₀ hN).mp (show x₁ - a < (b - a) * i / N by linarith)]
      · rw [le_div_iff₀ hba]
        linarith [(div_le_iff₀ hN).mp (show (b - a) * i / N ≤ x₂ - a by linarith)])
    fun i _ j _ hij => Fin.ext (Int.ofNat.inj hij)
  have hfloor : ⌊u₁⌋ ≤ ⌊u₂⌋ := Int.floor_mono (by dsimp only [u₁, u₂]; gcongr)
  have hsz : ((Finset.Ioc ⌊u₁⌋ ⌊u₂⌋).card : ℝ) = ⌊u₂⌋ - ⌊u₁⌋ := by
    rw [Int.card_Ioc]
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hfloor)
  have hudiff : u₂ - u₁ = (N : ℝ) * ((x₂ - x₁) / (b - a)) := by dsimp only [u₁, u₂]; ring
  rw [div_le_iff₀ hN, add_mul, one_div_mul_cancel hN.ne']
  linarith [(Nat.cast_le (α := ℝ)).mpr hcard, Int.sub_one_lt_floor u₁, Int.floor_le u₂]

/-- **Discrete randomized-threshold rounding lemma** [ImpagliazzoLeiPitassiSorrell2022]: for any
`a < b` and `[NeZero N]`, two real numbers `x₁, x₂` thresholded against a shared uniform seed
`i : Fin N` on `[a, b)` disagree with probability at most `|x₁ - x₂| / (b - a) + 1 / N`. -/
theorem thresholdRound_disagree_le {a b : ℝ} (hab : a < b) {N : ℕ} [NeZero N] (x₁ x₂ : ℝ) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
      {i : Fin N | thresholdRound a b N i x₁ ≠ thresholdRound a b N i x₂}).toReal ≤
      |x₁ - x₂| / (b - a) + 1 / N := by
  rcases le_total x₁ x₂ with hle | hle
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
    exact thresholdRound_disagree_le_of_le hab hle
  · simpa only [ne_comm, abs_of_nonneg (sub_nonneg.mpr hle)] using
      thresholdRound_disagree_le_of_le hab hle

private theorem roundGrid_eq_iff_bin_eq {w : ℝ} (hw : 0 < w) {N : ℕ} (i : Fin N) (x₁ x₂ : ℝ) :
    roundGrid w N i x₁ = roundGrid w N i x₂ ↔ roundGridBin w N i x₁ = roundGridBin w N i x₂ := by
  simp [roundGrid, hw.ne']

private theorem roundGrid_disagree_le_of_le {w : ℝ} (hw : 0 < w) {N : ℕ} [NeZero N]
    {x₁ x₂ : ℝ} (hx : x₁ ≤ x₂) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
      {i : Fin N | roundGrid w N i x₁ ≠ roundGrid w N i x₂}).toReal ≤
      (x₂ - x₁) / w + 1 / N := by
  classical
  rw [Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, Fintype.card_fin]
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hbin (i : Fin N) : roundGridBin w N i x₁ ≤ roundGridBin w N i x₂ :=
    Int.floor_mono (by gcongr)
  have hcard : ((Finset.univ.filter
      (· ∈ {i : Fin N | roundGrid w N i x₁ ≠ roundGrid w N i x₂})).card : ℤ) ≤
      ⌊(N : ℝ) * (x₂ / w)⌋ - ⌊(N : ℝ) * (x₁ / w)⌋ := by
    rw [Finset.card_filter, Nat.cast_sum]
    refine (Finset.sum_le_sum (g := fun i => roundGridBin w N i x₂ - roundGridBin w N i x₁)
      fun i _ => ?_).trans_eq ?_
    · simp only [Set.mem_ofPred_eq, ne_eq, roundGrid_eq_iff_bin_eq hw]
      split_ifs with hne
      · exact_mod_cast sub_nonneg.mpr (hbin i)
      · have := lt_of_le_of_ne (hbin i) hne
        push_cast
        omega
    · simp only [roundGridBin, Finset.sum_sub_distrib]
      rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ⌊x₂ / w + (i : ℝ) / N⌋) N,
        Fin.sum_univ_eq_sum_range (fun i : ℕ => ⌊x₁ / w + (i : ℝ) / N⌋) N,
        Int.sum_floor_add_div (x₂ / w) N, Int.sum_floor_add_div (x₁ / w) N]
  have hcardR := (Int.cast_le (R := ℝ)).mpr hcard
  push_cast at hcardR
  rw [div_le_iff₀ hN, add_mul, one_div_mul_cancel hN.ne']
  linarith [Int.sub_one_lt_floor ((N : ℝ) * (x₁ / w)), Int.floor_le ((N : ℝ) * (x₂ / w)),
    show (N : ℝ) * (x₂ / w) - N * (x₁ / w) = (x₂ - x₁) / w * N by ring]

/-- **Periodic grid rounding lemma** [ImpagliazzoLeiPitassiSorrell2022]: for any `w > 0` and
`[NeZero N]`, two real numbers `x₁, x₂` fall into different bins of `roundGrid w N` under a
uniform shared seed `i : Fin N` with probability at most `|x₁ - x₂| / w + 1 / N`. -/
theorem roundGrid_disagree_le {w : ℝ} (hw : 0 < w) {N : ℕ} [NeZero N] (x₁ x₂ : ℝ) :
    ((Probability.PMF.uniformOfFintype (Fin N)).toOuterMeasure
      {i : Fin N | roundGrid w N i x₁ ≠ roundGrid w N i x₂}).toReal ≤
      |x₁ - x₂| / w + 1 / N := by
  rcases le_total x₁ x₂ with hle | hle
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
    exact roundGrid_disagree_le_of_le hw hle
  · simpa only [ne_comm, abs_of_nonneg (sub_nonneg.mpr hle)] using
      roundGrid_disagree_le_of_le hw hle

end DiscreteDisagreement

section ContinuousDisagreement

private theorem volume_thresholdRound_ne_le_of_le {a b : ℝ} (hab : a < b) {x₁ x₂ : ℝ}
    (hx : x₁ ≤ x₂) :
    MeasureTheory.volume
      {u ∈ Set.Ico (0 : ℝ) 1 |
        continuousThresholdRound a b u x₁ ≠ continuousThresholdRound a b u x₂} ≤
      ENNReal.ofReal ((x₂ - x₁) / (b - a)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  refine (MeasureTheory.measure_mono (t := Set.Ioc ((x₁ - a) / (b - a)) ((x₂ - a) / (b - a)))
    fun u hu => ?_).trans ?_
  · obtain ⟨h1, h2⟩ := lt_and_le_of_decide_ne hx hu.2
    exact ⟨(div_lt_iff₀' hba).mpr (by linarith), (le_div_iff₀' hba).mpr (by linarith)⟩
  · rw [Real.volume_Ioc, ← sub_div, sub_sub_sub_cancel_right]

/-- **Continuous randomized-threshold rounding lemma**: for `a < b` and `u ~ Uniform([0, 1))`, the
disagreement measure is at most `|x₁ - x₂| / (b - a)`. -/
theorem volume_thresholdRound_ne_le {a b : ℝ} (hab : a < b) (x₁ x₂ : ℝ) :
    MeasureTheory.volume
      {u ∈ Set.Ico (0 : ℝ) 1 |
        continuousThresholdRound a b u x₁ ≠ continuousThresholdRound a b u x₂} ≤
      ENNReal.ofReal (|x₁ - x₂| / (b - a)) := by
  rcases le_total x₁ x₂ with hle | hle
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
    exact volume_thresholdRound_ne_le_of_le hab hle
  · simpa only [ne_comm, abs_of_nonneg (sub_nonneg.mpr hle)] using
      volume_thresholdRound_ne_le_of_le hab hle

private theorem volume_continuousRoundGridBin_ne_le_of_le {w : ℝ} (hw : 0 < w) {x₁ x₂ : ℝ}
    (hx : x₁ ≤ x₂) :
    MeasureTheory.volume
      {u ∈ Set.Ico (0 : ℝ) 1 |
        continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂} ≤
      ENNReal.ofReal ((x₂ - x₁) / w) := by
  let y₁ : ℝ := x₁ / w
  let y₂ : ℝ := x₂ / w
  have hy : y₁ ≤ y₂ := by dsimp only [y₁, y₂]; gcongr
  have hydiff : y₂ - y₁ = (x₂ - x₁) / w := by dsimp only [y₁, y₂]; ring
  let k : ℤ := ⌊y₁⌋ + 1
  have hk : (k : ℝ) = ⌊y₁⌋ + 1 := by push_cast [k]; rfl
  have hk₁ := Int.floor_le y₁
  have hk₂ := Int.lt_floor_add_one y₁
  -- The bins differ only when the first integer above `y₁ + u`, which is `k` or `k + 1`, is at
  -- most `y₂ + u`.
  have hsub :
      {u ∈ Set.Ico (0 : ℝ) 1 |
        continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂} ⊆
      Set.Ico (max 0 ((k : ℝ) - y₂)) ((k : ℝ) - y₁) ∪ Set.Ico ((k : ℝ) + 1 - y₂) 1 := by
    rintro u ⟨⟨hu0, hu1⟩, hne⟩
    have hlt : ⌊y₁ + u⌋ < ⌊y₂ + u⌋ := lt_of_le_of_ne (Int.floor_mono (by linarith)) hne
    have h1 := Int.lt_floor_add_one (y₁ + u)
    have h2 : ((⌊y₁ + u⌋ : ℤ) : ℝ) + 1 ≤ y₂ + u := by
      exact_mod_cast (Int.cast_le.mpr hlt).trans (Int.floor_le (y₂ + u))
    have h3 : ⌊y₁⌋ ≤ ⌊y₁ + u⌋ := Int.floor_mono (by linarith)
    have h4 : ⌊y₁ + u⌋ < ⌊y₁⌋ + 2 := Int.floor_lt.mpr (by push_cast; linarith)
    rcases (show ⌊y₁ + u⌋ = ⌊y₁⌋ ∨ ⌊y₁ + u⌋ = ⌊y₁⌋ + 1 by omega) with h | h <;>
      have h' := congrArg (Int.cast (R := ℝ)) h <;> push_cast at h'
    · exact Or.inl ⟨max_le hu0 (by linarith), by linarith⟩
    · exact Or.inr ⟨by linarith, hu1⟩
  refine (MeasureTheory.measure_mono hsub).trans ((MeasureTheory.measure_union_le _ _).trans ?_)
  rw [Real.volume_Ico, Real.volume_Ico, ← hydiff]
  rcases le_total y₂ k with hk2 | hk2
  · rw [max_eq_right (by linarith),
      ENNReal.ofReal_of_nonpos (show 1 - ((k : ℝ) + 1 - y₂) ≤ 0 by linarith), add_zero]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · rw [max_eq_left (by linarith), ← ENNReal.ofReal_add (by linarith) (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Continuous periodic grid rounding lemma**: for `w > 0` and `u ~ Uniform([0, 1))`, the
disagreement measure of `continuousRoundGrid w u` is at most `|x₁ - x₂| / w`. -/
theorem volume_roundGrid_ne_le {w : ℝ} (hw : 0 < w) (x₁ x₂ : ℝ) :
    MeasureTheory.volume
      {u ∈ Set.Ico (0 : ℝ) 1 | continuousRoundGrid w u x₁ ≠ continuousRoundGrid w u x₂} ≤
      ENNReal.ofReal (|x₁ - x₂| / w) := by
  have hbin (u : ℝ) : continuousRoundGrid w u x₁ ≠ continuousRoundGrid w u x₂ ↔
      continuousRoundGridBin w u x₁ ≠ continuousRoundGridBin w u x₂ := by
    simp [continuousRoundGrid, hw.ne']
  simp only [hbin]
  rcases le_total x₁ x₂ with hle | hle
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)]
    exact volume_continuousRoundGridBin_ne_le_of_le hw hle
  · simpa only [ne_comm, abs_of_nonneg (sub_nonneg.mpr hle)] using
      volume_continuousRoundGridBin_ne_le_of_le hw hle

end ContinuousDisagreement

section RoundingPrograms

variable {X : Type} {m : ℕ}

/-- Accuracy of `roundGridProg`: whenever `est S` is within `δ` of `target D` except with
probability `β`, rounding to a periodic grid of width `w` preserves estimation within `w / 2 + δ`
with the same failure probability `β`. -/
theorem isAccurateFor_roundGridProg_of_concentrates {w δ β : ℝ} (hw : 0 < w)
    (N : ℕ) [NeZero N] (est : (Fin m → X) → ℝ) (𝒟 : Set (PMF X)) (target : PMF X → ℝ)
    (hconc : ∀ D ∈ 𝒟,
      ((Probability.PMF.iid D m).toOuterMeasure {S | δ < |est S - target D|}).toReal ≤ β) :
    EstimatesFor (roundGridProg w N est).toAlgorithm 𝒟 target (w / 2 + δ) β := by
  intro D hD
  have hβ : 0 ≤ β := ENNReal.toReal_nonneg.trans (hconc D hD)
  have hmarg : (roundGridProg w N est).toAlgorithm.marginal D =
      (ProbComp.eval (ProbComp.uniform (Fin N))).bind fun i =>
        (Probability.PMF.iid D m).map fun S => roundGrid w N i (est S) := by
    simp only [roundGridProg, Program.toAlgorithm_deterministic, Algorithm.marginal_eq_seed_bind,
      Algorithm.deterministic]
    rfl
  rw [hmarg, ProbComp.eval_uniform]
  refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ Set.univ _ hβ
    fun i _ _ => ?_).trans_eq ?_
  · rw [PMF.toOuterMeasure_map_apply]
    have hsub : (fun S => roundGrid w N i (est S)) ⁻¹' {y | |y - target D| ≤ w / 2 + δ}ᶜ ⊆
        {S | δ < |est S - target D|} := by
      intro S hS
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hS ⊢
      linarith [abs_sub_le (roundGrid w N i (est S)) (est S) (target D),
        abs_roundGrid_sub_le hw N i (est S)]
    exact (Probability.PMF.toOuterMeasure_toReal_mono _ hsub).trans (hconc D hD)
  · simp

/-- Replicability of `roundGridProg`: if `est S` concentrates within `δ` of `target D` except with
probability `β` for every `D ∈ 𝒟`, then `roundGridProg w N est` is
`(2 * δ / w + 1 / N + 2 * β)`-replicable over `𝒟`. -/
theorem isReplicableFor_roundGridProg_of_concentrates {w δ β : ℝ} (hw : 0 < w)
    (N : ℕ) [NeZero N] (est : (Fin m → X) → ℝ) (𝒟 : Set (PMF X)) (target : PMF X → ℝ)
    (hδ : 0 ≤ δ) (hβ : 0 ≤ β)
    (hconc : ∀ D ∈ 𝒟,
      ((Probability.PMF.iid D m).toOuterMeasure {S | δ < |est S - target D|}).toReal ≤ β) :
    IsReplicableFor (roundGridProg w N est).toAlgorithm 𝒟 (2 * δ / w + 1 / N + 2 * β) := by
  intro D hD
  have hcomm :
      (roundGridProg w N est).toAlgorithm.pairedOutput D =
        (Probability.PMF.iid D m).bind fun S₁ =>
          (Probability.PMF.iid D m).bind fun S₂ =>
            (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
              (roundGrid w N i (est S₁), roundGrid w N i (est S₂)) := by
    simp only [roundGridProg, Program.toAlgorithm_deterministic,
      Algorithm.pairedOutput_deterministic, ProbComp.eval_uniform]
    rw [PMF.bind_comm]
    exact congrArg (PMF.bind (Probability.PMF.iid D m)) (funext fun S₁ => PMF.bind_comm _ _ _)
  rw [Algorithm.disagreeProb, hcomm]
  let good : Set (Fin m → X) := {S | |est S - target D| ≤ δ}
  let c : ℝ := 2 * δ / w + 1 / N
  have hc : 0 ≤ c := by positivity
  have hgoodc : ((Probability.PMF.iid D m).toOuterMeasure goodᶜ).toReal ≤ β := by
    have heq : goodᶜ = {S | δ < |est S - target D|} := by
      ext S
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, good]
    rw [heq]
    exact hconc D hD
  have hinner :
      ∀ S₁ ∈ good,
        (((Probability.PMF.iid D m).bind fun S₂ =>
          (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
            (roundGrid w N i (est S₁), roundGrid w N i (est S₂))).toOuterMeasure
          {p : ℝ × ℝ | p.1 ≠ p.2}).toReal ≤ β + c := by
    intro S₁ hS₁
    refine (Probability.PMF.toOuterMeasure_bind_failure_toReal_le _ _ good _ hc ?_).trans
      (add_le_add hgoodc le_rfl)
    intro S₂ _ hS₂
    rw [PMF.toOuterMeasure_map_apply]
    have hpre : (fun i : Fin N => (roundGrid w N i (est S₁), roundGrid w N i (est S₂))) ⁻¹'
        {p : ℝ × ℝ | p.1 ≠ p.2} =
        {i : Fin N | roundGrid w N i (est S₁) ≠ roundGrid w N i (est S₂)} :=
      rfl
    rw [hpre]
    have hdist : |est S₁ - est S₂| ≤ 2 * δ := by
      linarith [abs_sub_le (est S₁) (target D) (est S₂), abs_sub_comm (target D) (est S₂),
        show |est S₁ - target D| ≤ δ from hS₁, show |est S₂ - target D| ≤ δ from hS₂]
    refine (roundGrid_disagree_le hw (est S₁) (est S₂)).trans ?_
    dsimp only [c]
    gcongr
  have houter := Probability.PMF.toOuterMeasure_bind_failure_toReal_le (Probability.PMF.iid D m)
    (fun S₁ => (Probability.PMF.iid D m).bind fun S₂ =>
      (Probability.PMF.uniformOfFintype (Fin N)).map fun i =>
        (roundGrid w N i (est S₁), roundGrid w N i (est S₂)))
    good {p : ℝ × ℝ | p.1 ≠ p.2} (add_nonneg hβ hc) (fun S₁ _ hS₁ => hinner S₁ hS₁)
  refine houter.trans ?_
  dsimp only [c]
  linarith

end RoundingPrograms

end Cslib.MachineLearning.Replicable
