/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.GameTheory.Mechanism.OptimalAuction
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Myerson's optimal auction clients

The uniform distribution on `[0, 1]`: its density, regularity, virtual valuation and reserve price
`1/2`. Concrete payments of the Vickrey auction with reserve price `1/2`. The plain Vickrey auction
is not a virtual-welfare maximizer. Myerson's theorem compares Vickrey with and without reserve for
two i.i.d. uniform bidders, so its hypotheses are satisfiable. The rising density `2v` on `[0, 1]`
(`F(v) = v²`), which vanishes at `0` with `φ(v) → −∞` as `v → 0⁺`, satisfies `IsRegular` with
reserve price `1 / √3`, and its reserve auction is DSIC, IR and revenue-optimal despite the
division-by-zero value `φ(0) = 0`.
-/

namespace CslibFrontierTests.GameTheory.OptimalAuction

open MeasureTheory Set Cslib.GameTheory Cslib.GameTheory.SingleParameter
  Cslib.GameTheory.SingleParameter.Vickrey

/-- The uniform distribution on `[0, 1]`. -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Icc 0 1)

/-- The virtual valuation of the uniform distribution. -/
noncomputable abbrev unifVirtualValue : ℝ → ℝ := virtualValue unif fun _ => 1

instance : IsProbabilityMeasure unif :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

/-! ### The uniform distribution -/

/-- The uniform distribution has density `1` and is regular, `φ(3/4) = 1/2`, and the reserve price
is `1/2`. -/
example : HasValueDensity unif (fun _ => 1) 1 ∧ IsRegular unif (fun _ => 1) 1 ∧
    unifVirtualValue (3 / 4) = 1 / 2 ∧ reservePrice unifVirtualValue = 1 / 2 := by
  refine ⟨hasValueDensity_uniform, isRegular_uniform, ?_, reservePrice_uniform⟩
  have h : unifVirtualValue (3 / 4) = 2 * (3 / 4) - 1 :=
    virtualValue_uniform ⟨by norm_num, by norm_num⟩
  rw [h]
  norm_num

/-- `0` is not a reserve threshold: `φ(1/4) = -1/2 < 0`. -/
example : ¬ IsReserveThreshold unifVirtualValue 0 := by
  intro h
  have := isReserveThreshold_uniform.2.2 _ (by norm_num) (h.2.1 (1 / 4) (by norm_num))
  norm_num at this

/-! ### Vickrey with reserve price `1/2` -/

theorem unifVirtualValue_monotoneOn : MonotoneOn unifVirtualValue (Ioi 0) :=
  (isRegular_uniform.strictMonoOn_Ioi hasValueDensity_uniform).monotoneOn

/-- Bids `(0.3, 0.4)` are both below the reserve, so the item is not sold. -/
example : reserveAllocation unifVirtualValue ![(3 / 10 : ℝ), 2 / 5] 0 = 0 ∧
    reserveAllocation unifVirtualValue ![(3 / 10 : ℝ), 2 / 5] 1 = 0 := by
  refine ⟨reserveAllocation_eq_zero_iff.2 fun h => ?_, reserveAllocation_eq_zero_iff.2 fun h => ?_⟩
  · have := isReserveThreshold_uniform.2.2 _ h.2.1 h.2.2
    norm_num at this
  · have := isReserveThreshold_uniform.2.2 _ h.2.1 h.2.2
    norm_num at this

/-- Bids `(0.6, 0.2)`: bidder `0` wins and pays the reserve price `1/2`. -/
example : reserveAllocation unifVirtualValue ![(3 / 5 : ℝ), 1 / 5] 0 = 1 ∧
    myersonPayment (reserveAllocation unifVirtualValue) ![(3 / 5 : ℝ), 1 / 5] 0 = 1 / 2 := by
  have hw : Wins ![(3 / 5 : ℝ), 1 / 5] 0 := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · norm_num
  have hb : 0 ≤ ![(3 / 5 : ℝ), 1 / 5] := fun i => by fin_cases i <;> norm_num
  have h1 : reserveAllocation unifVirtualValue ![(3 / 5 : ℝ), 1 / 5] 0 = 1 :=
    reserveAllocation_eq_one_iff.2 ⟨hw, by norm_num, isReserveThreshold_uniform.2.1 _ (by norm_num)⟩
  refine ⟨h1, ?_⟩
  rw [myersonPayment_reserveAllocation unifVirtualValue_monotoneOn isReserveThreshold_uniform hb,
    h1, mul_one]
  refine max_eq_left (highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩)
  fin_cases j
  · exact absurd rfl hj
  · norm_num

/-- Bids `(0.7, 0.9)`: bidder `1` wins and pays the other bid `0.7`. Bidder `0` pays nothing. -/
example : reserveAllocation unifVirtualValue ![(7 / 10 : ℝ), 9 / 10] 1 = 1 ∧
    myersonPayment (reserveAllocation unifVirtualValue) ![(7 / 10 : ℝ), 9 / 10] 1 = 7 / 10 ∧
    myersonPayment (reserveAllocation unifVirtualValue) ![(7 / 10 : ℝ), 9 / 10] 0 = 0 := by
  have hw : Wins ![(7 / 10 : ℝ), 9 / 10] 1 := by
    intro j hj
    fin_cases j
    · norm_num
    · exact absurd rfl hj
  have hb : 0 ≤ ![(7 / 10 : ℝ), 9 / 10] := fun i => by fin_cases i <;> norm_num
  have h1 : reserveAllocation unifVirtualValue ![(7 / 10 : ℝ), 9 / 10] 1 = 1 :=
    reserveAllocation_eq_one_iff.2 ⟨hw, by norm_num, isReserveThreshold_uniform.2.1 _ (by norm_num)⟩
  have h0 : reserveAllocation unifVirtualValue ![(7 / 10 : ℝ), 9 / 10] 0 = 0 :=
    reserveAllocation_eq_zero_iff.2 fun h => absurd (h.1.unique hw) (by decide)
  have hsecond : highestOtherBid ![(7 / 10 : ℝ), 9 / 10] 1 = 7 / 10 := by
    refine le_antisymm (highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩) ?_
    · fin_cases j
      · norm_num
      · exact absurd rfl hj
    · exact le_of_eq_of_le (by norm_num)
        (le_highestOtherBid (b := ![(7 / 10 : ℝ), 9 / 10]) (i := 1) (j := 0) (by decide))
  refine ⟨h1, ?_, ?_⟩
  · rw [myersonPayment_reserveAllocation unifVirtualValue_monotoneOn isReserveThreshold_uniform hb,
      h1, mul_one, hsecond]
    norm_num
  · rw [myersonPayment_reserveAllocation unifVirtualValue_monotoneOn isReserveThreshold_uniform hb,
      h0, mul_zero]

/-- The plain Vickrey auction does not maximize virtual welfare for uniform bidders: on bids
`(1/4, 0)` it sells to bidder `0`, whose virtual valuation `-1/2` is negative. -/
example : ¬ IsVirtualWelfareMaximizing (fun _ => unifVirtualValue) singleItemFeasible
    (allocation (ι := Fin 2)) := by
  intro h
  have hb : 0 ≤ ![(1 / 4 : ℝ), 0] := fun i => by fin_cases i <;> norm_num
  have hw : Wins ![(1 / 4 : ℝ), 0] 0 := by
    intro j hj
    fin_cases j
    · exact absurd rfl hj
    · norm_num
  have hz : (0 : Fin 2 → ℝ) ∈ singleItemFeasible :=
    ⟨fun _ => Or.inl rfl, by simp only [Pi.zero_apply, Finset.sum_const_zero, zero_le_one]⟩
  have hle := (h _ hb).2 0 hz
  rw [Fin.sum_univ_two, Fin.sum_univ_two, allocation_eq_one_iff.2 hw,
    allocation_eq_zero_iff.2 fun h1 => absurd (h1.unique hw) (by decide)] at hle
  simp only [Pi.zero_apply, mul_zero, mul_one, add_zero] at hle
  have := isReserveThreshold_uniform.2.2 _ (by norm_num) hle
  norm_num at this

/-! ### Optimality -/

/-- **Myerson's theorem for two i.i.d. uniform bidders.** The Vickrey auction without reserve has
expected revenue at most that of the Vickrey auction with reserve price `1/2`. The hypotheses of
`integral_sum_payment_le_reserve`, and so of `integral_sum_payment_le_myerson`, are satisfiable. -/
example : ∫ v, ∑ i, (mechanism (ι := Fin 2)).payment v i ∂Measure.pi (fun _ => unif) ≤
    ∫ v, ∑ i, (myerson (reserveAllocation (ι := Fin 2) unifVirtualValue)).payment v i
      ∂Measure.pi (fun _ => unif) :=
  integral_sum_payment_le_reserve hasValueDensity_uniform isRegular_uniform mechanism_isDSIC
    mechanism_isIR (fun v _ => allocation_mem_singleItemFeasible v) measurable_allocation

/-! ### Rising density `f(v) = 2v` (`F(v) = v²`) with vanishing lower-endpoint density -/

/-- The rising density `f(v) = 2v`. -/
noncomputable def risingDensity (v : ℝ) : NNReal := Real.toNNReal (2 * v)

/-- The distribution on `[0, 1]` with density `2v`, so `F(v) = v²`. -/
noncomputable def rising : Measure ℝ :=
  (volume.restrict (Icc 0 1)).withDensity fun v => (risingDensity v : ENNReal)

/-- The virtual valuation of `rising`. -/
noncomputable abbrev risingVirtualValue : ℝ → ℝ := virtualValue rising risingDensity

/-- The tail measure of `rising` on `[0, 1]` is `ENNReal.ofReal (1 − v²)`. -/
theorem rising_Ioi {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    rising (Ioi v) = ENNReal.ofReal (1 - v ^ 2) := by
  have hset : Ioi v ∩ Icc (0 : ℝ) 1 = Ioc v 1 := by
    ext w
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hv0.trans h1.le, h3⟩⟩
  rw [rising, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    hset]
  change (∫⁻ a in Ioc v 1, ENNReal.ofReal (2 * a)) = _
  have hint : IntegrableOn (fun a : ℝ => 2 * a) (Ioc v 1) :=
    (continuous_const.mul continuous_id : Continuous fun a : ℝ => 2 * a).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc v 1)] fun a : ℝ => 2 * a :=
    ae_restrict_of_forall_mem measurableSet_Ioc fun a ha => by
      have := ha.1
      change (0 : ℝ) ≤ 2 * a
      linarith
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, ← intervalIntegral.integral_of_le hv1,
    intervalIntegral.integral_const_mul, integral_id]
  congr 1
  ring

/-- The real tail of `rising` is `1 − F(v) = 1 − v²` on `[0, 1]`. -/
theorem rising_real_Ioi {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    rising.real (Ioi v) = 1 - v ^ 2 := by
  rw [measureReal_def, rising_Ioi hv0 hv1, ENNReal.toReal_ofReal (by nlinarith)]

theorem hasValueDensity_rising : HasValueDensity rising risingDensity 1 where
  measurable := (measurable_const.mul measurable_id).real_toNNReal
  eq_withDensity := rfl
  pos := fun _ hv => Real.toNNReal_pos.2 (by linarith [hv.1])

instance : IsProbabilityMeasure rising := by
  refine ⟨?_⟩
  have hIoc : Ioi (0 : ℝ) ∩ Icc 0 1 = Ioc 0 1 := by
    ext w
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, h1.le, h3⟩⟩
  have h0 := rising_Ioi (v := 0) le_rfl zero_le_one
  rw [rising, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    hIoc] at h0
  rw [rising, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← setLIntegral_congr Ioc_ae_eq_Icc, h0]
  norm_num

/-- On `(0, 1]`, the virtual valuation of `rising` is `(3v² − 1) / (2v)`. -/
theorem virtualValue_rising {v : ℝ} (hv0 : 0 < v) (hv1 : v ≤ 1) :
    risingVirtualValue v = (3 * v ^ 2 - 1) / (2 * v) := by
  rw [risingVirtualValue, virtualValue, rising_real_Ioi hv0.le hv1, risingDensity,
    Real.coe_toNNReal _ (by linarith)]
  field_simp
  ring

/-- The rising density `2v` on `[0, 1]` is regular: `φ(v) = (3v² − 1) / (2v)` is strictly
increasing on `(0, 1)`. -/
theorem isRegular_rising : IsRegular rising risingDensity 1 := by
  intro a ha b hb hab
  rw [show virtualValue rising risingDensity a = (3 * a ^ 2 - 1) / (2 * a) from
      virtualValue_rising ha.1 ha.2.le,
    show virtualValue rising risingDensity b = (3 * b ^ 2 - 1) / (2 * b) from
      virtualValue_rising hb.1 hb.2.le,
    div_lt_div_iff₀ (by linarith [ha.1]) (by linarith [hb.1])]
  nlinarith [mul_pos ha.1 hb.1]

/-- The reserve threshold of `rising` is `1 / √3`. -/
theorem isReserveThreshold_rising : IsReserveThreshold risingVirtualValue (1 / Real.sqrt 3) := by
  have hr0 : 0 < 1 / Real.sqrt 3 := by positivity
  have hsq : (1 / Real.sqrt 3) ^ 2 = 1 / 3 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hφ : ∀ v : ℝ, 0 < v → (0 ≤ risingVirtualValue v ↔ 1 / Real.sqrt 3 ≤ v) := by
    intro v hv0
    rcases le_total v 1 with hv1 | hv1
    · rw [virtualValue_rising hv0 hv1, div_nonneg_iff]
      constructor
      · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
        · by_contra hlt
          nlinarith [not_le.1 hlt]
        · linarith
      · intro hrv
        exact Or.inl ⟨by nlinarith, by linarith⟩
    · rw [risingVirtualValue, hasValueDensity_rising.virtualValue_eq_self hv1]
      exact ⟨fun _ => (by nlinarith : 1 / Real.sqrt 3 ≤ 1).trans hv1, fun _ => hv0.le⟩
  exact ⟨hr0.le, fun v hv => (hφ v (hr0.trans hv)).2 hv.le, fun v hv0 hv => (hφ v hv0).1 hv⟩

/-- The Myerson reserve price for `F(v) = v²` on `[0, 1]` is `1 / √3`. -/
theorem reservePrice_rising : reservePrice risingVirtualValue = 1 / Real.sqrt 3 :=
  (isRegular_rising.isReserveThreshold hasValueDensity_rising).unique isReserveThreshold_rising

/-- Boundary check at `v = 0`: Lean's `/ 0 = 0` makes `risingVirtualValue 0 = 0` although
`risingVirtualValue (1/2) = -1/4 < 0`. On the all-zero profile, bidder `0` wins the tie with
virtual value `0`, so it passes the guard `Wins b i ∧ 0 ≤ φ (b i)` that omits the positive-bid
condition. `reserveAllocation` rejects the zero bid, so neither bidder is served, and
`myerson (reserveAllocation risingVirtualValue)` is DSIC and individually rational. -/
example : risingVirtualValue 0 = 0 ∧ risingVirtualValue (1 / 2) = -1 / 4 ∧
    (Wins ![(0 : ℝ), 0] 0 ∧ 0 ≤ risingVirtualValue (![(0 : ℝ), 0] 0)) ∧
    reserveAllocation risingVirtualValue ![(0 : ℝ), 0] 0 = 0 ∧
    reserveAllocation risingVirtualValue ![(0 : ℝ), 0] 1 = 0 ∧
    (myerson (reserveAllocation (ι := Fin 2) risingVirtualValue)).IsDSIC ∧
    (myerson (reserveAllocation (ι := Fin 2) risingVirtualValue)).IsIR := by
  have hφ0 : risingVirtualValue 0 = 0 := by
    rw [risingVirtualValue, virtualValue, risingDensity]
    norm_num
  refine ⟨hφ0, ?_, ⟨fun j hj => ?_, by simp [hφ0]⟩,
    reserveAllocation_eq_zero_iff.2 fun h => by norm_num at h,
    reserveAllocation_eq_zero_iff.2 fun h => by norm_num at h,
    myerson_isDSIC (isMonotone_reserveAllocation
      (isRegular_rising.strictMonoOn_Ioi hasValueDensity_rising).monotoneOn),
    myerson_isIR fun _ _ => reserveAllocation_nonneg _ _⟩
  · rw [virtualValue_rising (by norm_num) (by norm_num)]
    norm_num
  · fin_cases j
    · exact absurd rfl hj
    · norm_num

/-- **Myerson's optimal auction for two i.i.d. bidders with `F(v) = v²`.** Every DSIC, IR
single-item mechanism (here, plain Vickrey) has expected revenue at most that of the second-price
auction with reserve price `1 / √3`. -/
example : ∫ v, ∑ i, (mechanism (ι := Fin 2)).payment v i ∂Measure.pi (fun _ => rising) ≤
    ∫ v, ∑ i : Fin 2, max (1 / Real.sqrt 3) (highestOtherBid v i) *
      reserveAllocation risingVirtualValue v i ∂Measure.pi (fun _ => rising) := by
  rw [← reservePrice_rising]
  exact integral_sum_payment_le_secondPriceReserve hasValueDensity_rising isRegular_rising
    mechanism_isDSIC mechanism_isIR (fun v _ => allocation_mem_singleItemFeasible v)
    measurable_allocation

end CslibFrontierTests.GameTheory.OptimalAuction
