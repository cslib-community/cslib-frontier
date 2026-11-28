/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.SupportTsum
import CslibFrontier.Probability.PMF.ToReal
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

/-!
# Statistical distance (`CloseTo`) on probability mass functions

Two probability mass functions `μ, ν : PMF α` are within statistical distance `ε` (`CloseTo μ ν ε`)
if for every event `E ⊆ α`, `μ.toOuterMeasure E ≤ ν.toOuterMeasure E + ε`. This definition operates
directly on `PMF`s with error in `ℝ≥0∞` without requiring `Fintype α` or metric spaces.

Quantifying over all events makes this notion symmetric, and it coincides with total variation
distance.

## Main definitions

* `Cslib.Probability.CloseTo`: `μ` and `ν` are within statistical distance `ε`.

## Main results

* `Cslib.Probability.closeTo_iff_tsum_tsub_le`: closeness is the positive-part sum
  `∑' a, (μ a - ν a)` being at most `ε`.
* `Cslib.Probability.PMF.tsum_tsub_comm`: the two positive-part sums of a pair of PMFs agree.
* `Cslib.Probability.PMF.toOuterMeasure_eq_add_tsum_tsub`: the positive-part sum is the excess
  probability of an event separating where `μ` and `ν` dominate.
* `Cslib.Probability.CloseTo.refl`: every distribution is `0`-close to itself.
* `Cslib.Probability.CloseTo.mono`: enlarging the error preserves closeness.
* `Cslib.Probability.CloseTo.symm`: statistical closeness is symmetric on any type.
* `Cslib.Probability.CloseTo.map`: statistical closeness is preserved by postprocessing.
* `Cslib.Probability.CloseTo.trans`: statistical closeness errors add along a chain.
* `Cslib.Probability.CloseTo.bind_left`: data processing under a shared continuation.
* `Cslib.Probability.CloseTo.bind_right`: pointwise closeness of continuations is preserved across
  `PMF.bind`.
* `Cslib.Probability.CloseTo.bind`: combined first-stage and continuation error addition.
* `Cslib.Probability.CloseTo.abs_toReal_sub_le`: closeness bounds the real probability difference
  on every event by `ε`.
* `Cslib.Probability.CloseTo.of_one_sub_mul_le`,
  `Cslib.Probability.CloseTo.of_le_apply`: a distribution pointwise dominating `(1 - ε) * ν` is
  `ε`-close to `ν`.
* `Cslib.Probability.closeTo_pure_iff`: `CloseTo μ (PMF.pure b) ε` holds iff
  `μ.toOuterMeasure {b}ᶜ ≤ ε`.
* `Cslib.Probability.CloseTo.toReal_apply_le_of_uniformOfFintype`: a distribution `δ`-close to
  `PMF.uniformOfFintype α` assigns mass at most `1 / Fintype.card α + δ` to every atom.
-/

public section

open scoped ENNReal NNReal

namespace Cslib.Probability

/-- `μ` is within statistical distance `ε` of `ν`: no event is more likely under `μ` than under
`ν` by more than `ε`. Quantifying over all events makes this symmetric, and it is the total
variation distance on any type, finite or not. -/
@[expose] def CloseTo {α : Type*} (μ ν : PMF α) (ε : ℝ≥0∞) : Prop :=
  ∀ event : Set α, μ.toOuterMeasure event ≤ ν.toOuterMeasure event + ε

/-- Every distribution is `0`-close to itself. -/
@[simp] theorem CloseTo.refl {α : Type*} (μ : PMF α) : CloseTo μ μ 0 :=
  fun _ => by rw [add_zero]

/-- Enlarging the error bound preserves statistical closeness. -/
theorem CloseTo.mono {α : Type*} {μ ν : PMF α} {ε δ : ℝ≥0∞} (h : CloseTo μ ν ε)
    (hle : ε ≤ δ) : CloseTo μ ν δ :=
  fun event => (h event).trans (add_le_add le_rfl hle)

/-- An event containing every point where `μ` is larger and none where it is smaller has
`μ`-probability equal to its `ν`-probability plus the positive-part sum `∑' a, (μ a - ν a)`. -/
theorem PMF.toOuterMeasure_eq_add_tsum_tsub {α : Type*} (μ ν : PMF α) {s : Set α}
    (h₁ : ∀ a ∈ s, ν a ≤ μ a) (h₂ : ∀ a ∉ s, μ a ≤ ν a) :
    μ.toOuterMeasure s = ν.toOuterMeasure s + ∑' a, (μ a - ν a) := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← tsum_add]
  congr 1 with a
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha, add_tsub_cancel_of_le (h₁ a ha)]
  · simp only [Set.indicator_of_notMem ha, tsub_eq_zero_of_le (h₂ a ha), add_zero]

/-- Statistical closeness is the positive-part sum `∑' a, (μ a - ν a)` (truncated subtraction in
`ℝ≥0∞`) being at most `ε`: the event `{a | ν a < μ a}` is the worst case. -/
theorem closeTo_iff_tsum_tsub_le {α : Type*} {μ ν : PMF α} {ε : ℝ≥0∞} :
    CloseTo μ ν ε ↔ ∑' a, (μ a - ν a) ≤ ε := by
  refine ⟨fun h => ?_, fun h event => ?_⟩
  · have h := h {a | ν a < μ a}
    rw [PMF.toOuterMeasure_eq_add_tsum_tsub μ ν (fun _ ha => le_of_lt ha)
      fun _ ha => not_lt.1 ha] at h
    exact (ENNReal.add_le_add_iff_left (PMF.toOuterMeasure_ne_top ν _)).1 h
  · rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    calc
      ∑' a, event.indicator μ a ≤ ∑' a, (event.indicator ν a + (μ a - ν a)) :=
        tsum_le_tsum fun a => by
          by_cases ha : a ∈ event
          · simpa only [Set.indicator_of_mem ha] using le_add_tsub
          · simp only [Set.indicator_of_notMem ha, zero_add, zero_le]
      _ ≤ ∑' a, event.indicator ν a + ε := by rw [tsum_add]; gcongr

/-- The two positive-part sums of a pair of PMFs agree. -/
theorem PMF.tsum_tsub_comm {α : Type*} (μ ν : PMF α) : ∑' a, (μ a - ν a) = ∑' a, (ν a - μ a) := by
  have h (ρ σ : PMF α) : ∑' a, (ρ a - σ a) + 1 = ∑' a, max (ρ a) (σ a) := by
    rw [← σ.tsum_coe, ← tsum_add]
    simp only [tsub_add_eq_max]
  refine (ENNReal.add_left_inj ENNReal.one_ne_top).1 ?_
  simp only [h, max_comm]

/-- Statistical closeness is symmetric, on any type. -/
theorem CloseTo.symm {α : Type*} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CloseTo μ ν ε) :
    CloseTo ν μ ε :=
  closeTo_iff_tsum_tsub_le.2 <| (PMF.tsum_tsub_comm ν μ).trans_le (closeTo_iff_tsum_tsub_le.1 h)

/-- Statistical closeness is preserved by postprocessing. -/
theorem CloseTo.map {α : Type*} {β : Type*} {μ ν : PMF α} {ε : ℝ≥0∞}
    (h : CloseTo μ ν ε) (f : α → β) :
    CloseTo (μ.map f) (ν.map f) ε := fun event => by
  simpa only [PMF.toOuterMeasure_map_apply] using h (f ⁻¹' event)

/-- Statistical closeness errors add along a chain. -/
theorem CloseTo.trans {α : Type*} {μ ν ρ : PMF α} {ε δ : ℝ≥0∞} (h₁ : CloseTo μ ν ε)
    (h₂ : CloseTo ν ρ δ) : CloseTo μ ρ (ε + δ) := fun event =>
  (h₁ event).trans <| by
    rw [add_comm ε δ, ← add_assoc]
    exact add_le_add (h₂ event) le_rfl

/-- Data processing in the first stage: replacing `μ` by an `ε`-close `ν` before a common
randomized continuation `f` preserves `ε`-closeness, without finiteness assumptions. -/
theorem CloseTo.bind_left {α : Type*} {β : Type*} {μ ν : PMF α} {ε : ℝ≥0∞} (h : CloseTo μ ν ε)
    (f : α → PMF β) : CloseTo (μ.bind f) (ν.bind f) ε := fun event => by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  calc
    ∑' a, μ a * (f a).toOuterMeasure event
      ≤ ∑' a, (ν a * (f a).toOuterMeasure event + (μ a - ν a)) :=
        tsum_le_tsum fun a => calc
          _ ≤ (ν a + (μ a - ν a)) * (f a).toOuterMeasure event := by gcongr; exact le_add_tsub
          _ ≤ _ := by
            rw [add_mul]
            gcongr
            exact mul_le_of_le_one_right zero_le (PMF.toOuterMeasure_le_one (f a) event)
    _ ≤ ∑' a, ν a * (f a).toOuterMeasure event + ε := by
        rw [tsum_add]
        gcongr
        exact closeTo_iff_tsum_tsub_le.1 h

/-- Pointwise statistical closeness of continuations on `μ.support` is preserved across
`PMF.bind`. -/
theorem CloseTo.bind_right {α : Type*} {β : Type*} (μ : PMF α) {f g : α → PMF β} {ε : ℝ≥0∞}
    (h : ∀ a ∈ μ.support, CloseTo (f a) (g a) ε) :
    CloseTo (μ.bind f) (μ.bind g) ε := fun event => by
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  calc
    ∑' a, μ a * (f a).toOuterMeasure event
      ≤ ∑' a, μ a * ((g a).toOuterMeasure event + ε) :=
        PMF.tsum_mul_mono_support μ fun a ha => h a ha event
    _ = ∑' a, μ a * (g a).toOuterMeasure event + ε := by
        simp only [mul_add, tsum_add, ENNReal.tsum_mul_right, μ.tsum_coe, one_mul]

/-- Combining `CloseTo.bind_left` and `CloseTo.bind_right` adds the first-stage and continuation
errors. -/
theorem CloseTo.bind {α : Type*} {β : Type*} {μ ν : PMF α} {f g : α → PMF β} {ε δ : ℝ≥0∞}
    (h₁ : CloseTo μ ν ε) (h₂ : ∀ a ∈ ν.support, CloseTo (f a) (g a) δ) :
    CloseTo (μ.bind f) (ν.bind g) (ε + δ) :=
  (h₁.bind_left f).trans (CloseTo.bind_right ν h₂)

/-- Closeness within a real tolerance `ε ≥ 0` bounds the real difference of the probabilities of
every event by `ε`. -/
theorem CloseTo.abs_toReal_sub_le {β : Type*} {μ ν : PMF β} {ε : ℝ} (hε : 0 ≤ ε)
    (h : CloseTo μ ν (ENNReal.ofReal ε)) (E : Set β) :
    |(μ.toOuterMeasure E).toReal - (ν.toOuterMeasure E).toReal| ≤ ε := by
  have h₁ := h E
  have h₂ := h.symm E
  ennreal_to_real at h₁ h₂
  rw [abs_le]
  constructor <;> linarith

/-- A law dominating `(1 - ε) * ν` pointwise in `ℝ≥0∞` is within statistical distance `ε` of `ν`. -/
theorem CloseTo.of_one_sub_mul_le {β : Type*} {μ ν : PMF β} {ε : ℝ≥0∞}
    (h : ∀ b, (1 - ε) * ν b ≤ μ b) :
    CloseTo μ ν ε := by
  refine CloseTo.symm fun E => ?_
  have hle : (1 - ε) * ν.toOuterMeasure E ≤ μ.toOuterMeasure E := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
    refine tsum_le_tsum fun b => ?_
    by_cases hb : b ∈ E
    · simp only [Set.indicator_of_mem hb]
      exact h b
    · simp only [Set.indicator_of_notMem hb, mul_zero, le_refl]
  have hν := PMF.toOuterMeasure_le_one ν E
  rcases le_or_gt 1 ε with hε1 | hε1
  · exact (hν.trans hε1).trans le_add_self
  calc ν.toOuterMeasure E
      = (1 - ε) * ν.toOuterMeasure E + ε * ν.toOuterMeasure E := by
        rw [← add_mul, tsub_add_cancel_of_le hε1.le, one_mul]
    _ ≤ μ.toOuterMeasure E + ε :=
        add_le_add hle (mul_le_of_le_one_right zero_le hν)

/-- A law dominating `(1 - ε) ν` pointwise is within statistical distance `ε` of `ν`. -/
theorem CloseTo.of_le_apply {β : Type*} {μ ν : PMF β} {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ b, ENNReal.ofReal (1 - ε) * ν b ≤ μ b) :
    CloseTo μ ν (ENNReal.ofReal ε) := by
  refine CloseTo.of_one_sub_mul_le fun b => ?_
  simpa only [ENNReal.ofReal_sub 1 hε, ENNReal.ofReal_one] using h b

/-- `μ` is within statistical distance `ε` of `PMF.pure b` if and only if `{b}ᶜ` has `μ`-measure at
most `ε`. -/
theorem closeTo_pure_iff {β : Type*} {μ : PMF β} {b : β} {ε : ℝ≥0∞} :
    CloseTo μ (PMF.pure b) ε ↔ μ.toOuterMeasure {b}ᶜ ≤ ε := by
  constructor
  · intro h
    have hc := h {b}ᶜ
    rw [PMF.toOuterMeasure_pure_apply, Set.mem_compl_singleton_iff, ite_eq_right (not_not.mpr rfl),
      zero_add] at hc
    exact hc
  · intro h E
    by_cases hb : b ∈ E
    · rw [PMF.toOuterMeasure_pure_apply, ite_eq_left hb]
      exact (PMF.toOuterMeasure_le_one μ E).trans le_self_add
    · rw [PMF.toOuterMeasure_pure_apply, ite_eq_right hb, zero_add]
      refine (μ.toOuterMeasure.mono fun x hx => ?_).trans h
      rw [Set.mem_compl_singleton_iff]
      rintro rfl
      exact hb hx

/-- If `ν` is within statistical distance `δ` of the uniform distribution on a finite nonempty
type `α`, every atom of `ν` has real probability at most `1 / Fintype.card α + δ`. -/
theorem CloseTo.toReal_apply_le_of_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α]
    {ν : PMF α} {δ : ℝ≥0} (h : CloseTo (PMF.uniformOfFintype α) ν δ) (a : α) :
    (ν a).toReal ≤ 1 / Fintype.card α + δ := by
  have ha := h.symm {a}
  rw [PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_apply_singleton,
    PMF.uniformOfFintype_apply] at ha
  ennreal_to_real at ha
  linarith [one_div (Fintype.card α : ℝ)]

end Cslib.Probability
