/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Mechanism.PostedPrice
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sequential posted-price auctions, single-sample pricing, and Bulow–Klemperer clients

This is a `module` importing only the public surface of
`CslibFrontier.GameTheory.Mechanism.PostedPrice` (and transitively `ProphetSample`), verifying that
ordinary clients can exercise the API without `import all`:

1. **Group strategy-proofness boundary at price indifference**: at `p = ![1, 1]` and `v = ![1, 5]`,
   bidder `0` has zero surplus (`1 - 1 = 0`) and can deviate to `0` so coalition `{0, 1}` strictly
   improves bidder `1` without hurting bidder `0`, showing the `v i ≠ p i` guard in
   `postedPrice_strongGroupStrategyProof` is needed, while `postedPrice_isGroupStrategyProof` still
   rules out making *every* coalition member strictly better off.
2. **Tight 2-box `0 / 2` & `1` instance (`tightBidderLaws 1`)**:
   - balanced price `E[max] / 2 = 3 / 4` and Samuel-Cahn median price `1` both achieve `≥ 1/2` of
     Vickrey welfare `3 / 2`;
   - no posted-price vector `p : Fin 2 → ℝ` in order `(0, 1)` achieves `0.51` of optimal welfare
     or optimal revenue (`exists_postedPrice_revenue_lt`), while reversing the arrival order to
     `(1, 0)` with prices `![2, 1]` extracts the full `3 / 2` revenue.
3. **Single-sample tie-breaking boundary**: on deterministic `PMF.pure 1`, naive strict comparison
   against `maxⱼ sⱼ` collects `0` (`expectedReward_strictSampleRule_pure_eq_zero`), whereas
   `singleSamplePostedPrice` is DSIC, IR, and collects `≥ 1/2` of Vickrey welfare `1`.
4. **Asymmetric non-i.i.d. regular revenue `1/2`-approximation**: on two non-identical regular
   bidders (`Uniform[0, 1]` and `Uniform[0, 2]`, with distinct densities and support bounds),
   `postedPrice (virtualPostedPrices ...)` achieves `≥ 1/2` of every DSIC, IR single-item
   mechanism's revenue.
5. **Bulow–Klemperer checks**: the `(n + 1)`-bidder prior-independent Vickrey auction with zero
   reserve beats Myerson's `n`-bidder optimal auction on `Uniform[0, 1]` (`n = 1`) and
   `Uniform[0, 2]` (`n = 2`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.PostedPrice

open MeasureTheory Set Cslib.Probability.PMF Cslib.Probability.OptimalStopping
  Cslib.Probability.OptimalStopping.Prophet Cslib.GameTheory
  Cslib.GameTheory.SingleParameter Cslib.GameTheory.SingleParameter.PostedPrice
open scoped ENNReal NNReal

/-! ### 1. Group strategy-proofness boundary at indifference ties -/

/-- At `p = ![1, 1]` and valuations `v = ![1, 5]`, bidder `0` is indifferent (`v 0 = p 0 = 1`) and
can step aside (`b = ![0, 5]`) so that bidder `0`'s utility stays `0` while bidder `1`'s utility
rises from `0` to `4`. Thus `v i ≠ p i` in `postedPrice_strongGroupStrategyProof` is essential. -/
example :
    let p : Fin 2 → ℝ := ![1, 1]
    let v : Fin 2 → ℝ := ![1, 5]
    let b : Fin 2 → ℝ := ![0, 5]
    (postedPrice p).utility 0 (v 0) v = 0 ∧
    (postedPrice p).utility 0 (v 0) b = 0 ∧
    (postedPrice p).utility 1 (v 1) v = 0 ∧
    (postedPrice p).utility 1 (v 1) b = 4 := by
  dsimp only
  have hw_v0 : AcceptWins (fun i z => (![(1 : ℝ), 1] i) ≤ z) ![1, 5] 0 :=
    ⟨by simp, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
  have hl_v1 : ¬ AcceptWins (fun i z => (![(1 : ℝ), 1] i) ≤ z) ![1, 5] 1 :=
    fun hw => hw.2 0 Fin.zero_lt_one (by simp)
  have hl_b0 : ¬ AcceptWins (fun i z => (![(1 : ℝ), 1] i) ≤ z) ![0, 5] 0 :=
    fun hw => by have := hw.1; norm_num at this
  have hw_b1 : AcceptWins (fun i z => (![(1 : ℝ), 1] i) ≤ z) ![0, 5] 1 := by
    refine ⟨by norm_num, fun j hj => ?_⟩
    fin_cases j
    · norm_num
    · exact absurd hj (lt_irrefl _)
  simp only [Mechanism.utility, postedPrice, acceptMechanism,
    acceptAllocation_eq_one_iff.mpr hw_v0, acceptAllocation_eq_zero_iff.mpr hl_v1,
    acceptAllocation_eq_zero_iff.mpr hl_b0, acceptAllocation_eq_one_iff.mpr hw_b1,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  norm_num

/-- Away from price ties (`v = ![2, 5]`, `p = ![1, 1]`), no coalition can improve any member without
strictly hurting another (`postedPrice_strongGroupStrategyProof`). -/
example {b : Fin 2 → ℝ}
    (hcoal : ∀ i ∈ (Finset.univ : Finset (Fin 2)),
      (postedPrice ![1, 1]).utility i (![(2 : ℝ), 5] i) ![2, 5] ≤
        (postedPrice ![1, 1]).utility i (![(2 : ℝ), 5] i) b) :
    ∀ i, (postedPrice ![1, 1]).utility i (![(2 : ℝ), 5] i) b =
      (postedPrice ![1, 1]).utility i (![(2 : ℝ), 5] i) ![2, 5] :=
  postedPrice_strongGroupStrategyProof ![1, 1] (S := Finset.univ)
    (fun i => by fin_cases i <;> norm_num) (fun j hj => absurd (Finset.mem_univ j) hj)
    (fun i _ => by fin_cases i <;> norm_num) hcoal

/-! ### 2. Tight 2-box `0 / 2` & `1` instance (`tightBidderLaws 1`) -/

/-- On `tightBidderLaws 1` (bidder `0` sure `1`; bidder `1` uniform on `{0, 2}`), Vickrey social
welfare is `3 / 2`, and the Kleinberg–Weinberg balanced posted price `3 / 4` achieves `≥ 1/2` of
Vickrey welfare. -/
example : expectedWelfare SingleParameter.Vickrey.allocation (tightBidderLaws 1) = 3 / 2 ∧
    expectedWelfare SingleParameter.Vickrey.allocation (tightBidderLaws 1) ≤
      2 * expectedWelfare (postedPrice (fun _ : Fin 2 => (3 / 4 : ℝ))).allocation
        (tightBidderLaws 1) := by
  have hmax : expectedMax (List.ofFn (tightBidderLaws 1)) = 3 / 2 := by
    rw [list_ofFn_tightBidderLaws, expectedMax_tightLaws]
    norm_num
  have hvick : expectedWelfare SingleParameter.Vickrey.allocation (tightBidderLaws 1) = 3 / 2 := by
    rw [expectedWelfare_vickrey_eq_expectedMax, hmax]
  refine ⟨hvick, ?_⟩
  have hkw := expectedWelfare_vickrey_le_two_mul_postedPrice_half (tightBidderLaws 1)
    (by rw [hmax]; finiteness)
  dsimp only at hkw
  have ht : (((expectedMax (List.ofFn (tightBidderLaws 1)) / 2).toNNReal : ℝ≥0) : ℝ) = 3 / 4 := by
    rw [hmax]
    change (ENNReal.toReal ((3 / 2 : ℝ≥0∞) / 2)) = 3 / 4
    norm_num [ENNReal.toReal_div]
  rwa [ht] at hkw

/-- Samuel-Cahn's unconditional median posted-price bound on `tightBidderLaws 1`. -/
example : ∃ m : ℝ≥0,
    expectedWelfare SingleParameter.Vickrey.allocation (tightBidderLaws 1) ≤
      2 * expectedWelfare (postedPrice (fun _ : Fin 2 => (m : ℝ))).allocation
        (tightBidderLaws 1) ∨
    expectedWelfare SingleParameter.Vickrey.allocation (tightBidderLaws 1) ≤
      2 * expectedWelfare (strictPostedPrice (fun _ : Fin 2 => (m : ℝ))).allocation
        (tightBidderLaws 1) :=
  exists_expectedWelfare_vickrey_le_two_mul_postedPrice (tightBidderLaws 1)

/-- Approaching the `0 / 2` bidder first at price `2` and then the sure-`1` bidder at price `1`
extracts expected revenue `3 / 2`, whereas no order-`(0, 1)` posted-price mechanism can guarantee
`51 / 100` of optimal revenue or welfare across the `tightBidderLaws` family. -/
example :
    expectedRevenuePMF (postedPrice ![(2 : ℝ), 1]) ![longShot 1, PMF.pure 1] = 3 / 2 ∧
    ∃ k, ∀ p : Fin 2 → ℝ,
      expectedRevenuePMF (postedPrice p) (tightBidderLaws k) <
        51 / 100 * expectedRevenuePMF (postedPrice ![(k + 1 : ℝ), 1]) ![longShot k, PMF.pure 1] ∧
      expectedWelfare (postedPrice p).allocation (tightBidderLaws k) <
        51 / 100 * expectedWelfare SingleParameter.Vickrey.allocation (tightBidderLaws k) := by
  refine ⟨?_, exists_postedPrice_revenue_lt (by
    rw [← ENNReal.toReal_lt_toReal (by simp) (by finiteness)]
    norm_num [ENNReal.toReal_div])⟩
  have h := expectedRevenuePMF_swapped_tightBidderLaws 1
  norm_num at h ⊢
  exact h

/-! ### 3. Single-sample tie-breaking witness on a point mass -/

/-- On a single deterministic bidder with value `1` (`PMF.pure 1`), naive strict comparison against
the sample maximum collects `0`, while `singleSamplePostedPrice` is DSIC, individually rational,
normalized, single-item feasible, and collects at least `1/2` of the Vickrey welfare `1`. -/
example :
    (∀ {n : ℕ} (s : Fin n → ℝ≥0) (π : Equiv.Perm (Fin (2 * n))),
      (singleSamplePostedPrice s π).IsDSIC ∧ (singleSamplePostedPrice s π).IsIR ∧
        (singleSamplePostedPrice s π).IsNormalized) ∧
    strictSampleExpectedReward (fun _ : Fin 1 => PMF.pure (1 : ℝ≥0)) = 0 ∧
    expectedWelfare SingleParameter.Vickrey.allocation (fun _ : Fin 1 => PMF.pure (1 : ℝ≥0)) = 1 ∧
    (1 : ℝ≥0∞) ≤ 2 * ∑' s, piFin (fun _ : Fin 1 => PMF.pure (1 : ℝ≥0)) s *
      ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * 1))) π *
        expectedWelfare (singleSamplePostedPrice s π).allocation
          (fun _ : Fin 1 => PMF.pure (1 : ℝ≥0)) := by
  have hvick :
      expectedWelfare SingleParameter.Vickrey.allocation
        (fun _ : Fin 1 => PMF.pure (1 : ℝ≥0)) = 1 := by
    rw [expectedWelfare_vickrey_eq_expectedMax]
    have hofFn : List.ofFn (fun _ : Fin 1 => PMF.pure (1 : ℝ≥0)) = [PMF.pure 1] := by simp
    rw [hofFn, expectedMax, tsum_jointLaw_cons_mul, tsum_pure_mul, tsum_jointLaw_nil_mul]
    simp [listMax]
  refine ⟨fun s π => ⟨singleSamplePostedPrice_isDSIC s π, singleSamplePostedPrice_isIR s π,
    singleSamplePostedPrice_isNormalized s π⟩,
    expectedReward_strictSampleRule_pure_eq_zero 1, hvick, ?_⟩
  rw [← hvick]
  exact expectedWelfare_vickrey_le_two_mul_singleSamplePostedPrice _

/-! ### 4. Asymmetric non-i.i.d. regular revenue `1/2`-approximation -/

section NonIID

/-- Uniform distribution on `[0, 1]`. -/
noncomputable abbrev unif : Measure ℝ := volume.restrict (Icc 0 1)

/-- Virtual valuation of `Uniform[0, 1]`. -/
noncomputable abbrev unifVirtualValue : ℝ → ℝ := virtualValue unif fun _ => 1

instance : IsProbabilityMeasure unif :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

theorem unifVirtualValue_monotoneOn : MonotoneOn unifVirtualValue (Ioi 0) :=
  (isRegular_uniform.strictMonoOn_Ioi hasValueDensity_uniform).monotoneOn

/-- Constant density `1/2` on `[0, 2]`. -/
noncomputable def unif2Density (_ : ℝ) : ℝ≥0 := 1 / 2

/-- Uniform distribution on `[0, 2]`. -/
noncomputable def unif2 : Measure ℝ :=
  (volume.restrict (Icc (0 : ℝ) 2)).withDensity fun v => (unif2Density v : ENNReal)

/-- Virtual valuation of `Uniform[0, 2]`. -/
noncomputable abbrev unif2VirtualValue : ℝ → ℝ := virtualValue unif2 unif2Density

theorem hasValueDensity_unif2 : HasValueDensity unif2 unif2Density 2 where
  measurable := measurable_const
  eq_withDensity := rfl
  pos := fun _ _ => by dsimp only [unif2Density]; positivity

instance : IsProbabilityMeasure unif2 := by
  refine ⟨?_⟩
  rw [unif2, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hconst : (fun v : ℝ => (unif2Density v : ENNReal)) = fun _ => ENNReal.ofReal (1 / 2) :=
    funext fun _ => by simp only [unif2Density, ← ENNReal.ofReal_coe_nnreal]; norm_num
  rw [hconst, setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

theorem unif2_real_Ioi {v : ℝ} (hv0 : 0 ≤ v) (hv2 : v ≤ 2) :
    unif2.real (Ioi v) = (2 - v) / 2 := by
  have hset : Ioi v ∩ Icc (0 : ℝ) 2 = Ioc v 2 := by
    ext w
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hv0.trans h1.le, h3⟩⟩
  rw [measureReal_def, unif2, withDensity_apply _ measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, hset]
  have hconst : (fun w : ℝ => (unif2Density w : ENNReal)) = fun _ => ENNReal.ofReal (1 / 2) :=
    funext fun _ => by simp only [unif2Density, ← ENNReal.ofReal_coe_nnreal]; norm_num
  rw [hconst, setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by norm_num),
    ENNReal.toReal_ofReal (by linarith)]
  ring

theorem virtualValue_unif2 {v : ℝ} (hv0 : 0 ≤ v) (hv2 : v ≤ 2) :
    unif2VirtualValue v = 2 * v - 2 := by
  rw [unif2VirtualValue, virtualValue, unif2_real_Ioi hv0 hv2, unif2Density]
  norm_num
  ring

theorem isRegular_unif2 : IsRegular unif2 unif2Density 2 := by
  intro a ha b hb hab
  change unif2VirtualValue a < unif2VirtualValue b
  rw [virtualValue_unif2 ha.1.le ha.2.le, virtualValue_unif2 hb.1.le hb.2.le]
  linarith

/-- Asymmetric two-bidder environment: bidder `0` is `Uniform[0, 1]` and bidder `1` is
`Uniform[0, 2]`. -/
noncomputable def asymMeasure : Fin 2 → Measure ℝ := ![unif, unif2]

/-- Densities for `asymMeasure`. -/
noncomputable def asymDensity : Fin 2 → ℝ → ℝ≥0 := ![fun _ => 1, unif2Density]

/-- Upper support bounds `[1, 2]` for `asymMeasure`. -/
def asymBound : Fin 2 → ℝ := ![1, 2]

instance (i : Fin 2) : IsProbabilityMeasure (asymMeasure i) := by
  fin_cases i
  · change IsProbabilityMeasure unif; infer_instance
  · change IsProbabilityMeasure unif2; infer_instance

theorem hasValueDensity_asym (i : Fin 2) :
    HasValueDensity (asymMeasure i) (asymDensity i) (asymBound i) := by
  fin_cases i
  · exact hasValueDensity_uniform
  · exact hasValueDensity_unif2

theorem isRegular_asym (i : Fin 2) : IsRegular (asymMeasure i) (asymDensity i) (asymBound i) := by
  fin_cases i
  · exact isRegular_uniform
  · exact isRegular_unif2

/-- **Non-vacuous non-i.i.d. check**: on the asymmetric `(Uniform[0, 1], Uniform[0, 2])` single-item
environment, the sequential posted-price mechanism `postedPrice (virtualPostedPrices ...)` is DSIC,
IR, and achieves at least `1/2` of the expected revenue of the Vickrey auction (and of every DSIC,
IR single-item mechanism). -/
example :
    (postedPrice (virtualPostedPrices asymMeasure asymDensity)).IsDSIC ∧
    (postedPrice (virtualPostedPrices asymMeasure asymDensity)).IsIR ∧
    ∫ v, ∑ i : Fin 2, (SingleParameter.Vickrey.mechanism (ι := Fin 2)).payment v i
        ∂Measure.pi asymMeasure ≤
      2 * ∫ v, ∑ i : Fin 2,
        (postedPrice (virtualPostedPrices asymMeasure asymDensity)).payment v i
        ∂Measure.pi asymMeasure :=
  ⟨postedPrice_isDSIC _, postedPrice_isIR _,
    integral_sum_payment_le_two_mul_virtualPostedPrices hasValueDensity_asym isRegular_asym
      SingleParameter.Vickrey.mechanism_isDSIC SingleParameter.Vickrey.mechanism_isIR
      (fun v _ => SingleParameter.Vickrey.allocation_mem_singleItemFeasible v)
      SingleParameter.Vickrey.measurable_allocation⟩

/-! ### 5. Bulow–Klemperer checks on `Uniform[0, 1]` and `Uniform[0, 2]` -/

/-- **Bulow–Klemperer for `n = 1` vs `2` `Uniform[0, 1]` bidders**: the `2`-bidder
prior-independent Vickrey auction with zero reserve beats Myerson's optimal `1`-bidder auction. -/
example :
    ∫ v, ∑ i : Fin 1,
        (myerson (SingleParameter.Vickrey.reserveAllocation (ι := Fin 1) unifVirtualValue)).payment
          v i ∂Measure.pi (fun _ : Fin 1 => unif) ≤
      ∫ v, ∑ j : Fin 2, (SingleParameter.Vickrey.mechanism (ι := Fin 2)).payment v j
        ∂Measure.pi (fun _ : Fin 2 => unif) :=
  Vickrey.integral_sum_payment_le_vickrey_succ hasValueDensity_uniform isRegular_uniform
    (myerson_isDSIC
      (SingleParameter.Vickrey.isMonotone_reserveAllocation unifVirtualValue_monotoneOn))
    (myerson_isIR fun v _ => SingleParameter.Vickrey.reserveAllocation_nonneg _ v)
    (fun v _ => SingleParameter.Vickrey.reserveAllocation_mem_singleItemFeasible _ v)
    (SingleParameter.Vickrey.measurable_reserveAllocation
      hasValueDensity_uniform.measurable_virtualValue)

/-- **Bulow–Klemperer for `n = 2` vs `3` `Uniform[0, 2]` bidders**: the `3`-bidder
prior-independent Vickrey auction with zero reserve beats Myerson's optimal `2`-bidder auction. -/
example :
    ∫ v, ∑ i : Fin 2,
        (myerson (SingleParameter.Vickrey.reserveAllocation (ι := Fin 2)
          unif2VirtualValue)).payment v i ∂Measure.pi (fun _ : Fin 2 => unif2) ≤
      ∫ v, ∑ j : Fin 3, (SingleParameter.Vickrey.mechanism (ι := Fin 3)).payment v j
        ∂Measure.pi (fun _ : Fin 3 => unif2) :=
  Vickrey.integral_sum_payment_le_vickrey_succ hasValueDensity_unif2 isRegular_unif2
    (myerson_isDSIC (SingleParameter.Vickrey.isMonotone_reserveAllocation
      (isRegular_unif2.strictMonoOn_Ioi hasValueDensity_unif2).monotoneOn))
    (myerson_isIR fun v _ => SingleParameter.Vickrey.reserveAllocation_nonneg _ v)
    (fun v _ => SingleParameter.Vickrey.reserveAllocation_mem_singleItemFeasible _ v)
    (SingleParameter.Vickrey.measurable_reserveAllocation
      hasValueDensity_unif2.measurable_virtualValue)

end NonIID

end CslibFrontierTests.GameTheory.PostedPrice
