/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Mechanism.Ironing
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Myerson ironing, discrete virtual valuations, monopoly pricing, and empirical Myerson: clients

Checked non-vacuous witnesses exercising `CslibFrontier.GameTheory.Mechanism.Ironing` as an ordinary
`module` client:

1. **Discrete 3-point irregular distributions** (`![2, 3, 10]` and `![4, 5, 12]` with probabilities
   `![1/2, 1/4, 1/4]`):
   * non-monotone discrete virtual valuations `![1, -4, 10]` and `![3, -2, 12]`;
   * discrete Lemma 13.12 converse (`not_monotone_virtualWelfareMaximizer_of_gt`);
   * concave-envelope discrete ironing at negative (`![-2/3, -2/3, 10]`) and **positive**
     (`![4/3, 4/3, 12]`) pooled virtual values;
   * 2-bidder i.i.d. single-item auction on `![4, 5, 12]` achieving optimal expected revenue `6`,
     strictly exceeding un-pooled Vickrey (`43/8`), verified via
     `expectedDiscreteSumPayment_le_ironed_of_isDiscreteIronedVirtualValue`.
2. **Continuous bimodal irregular density on `[0, 3]`**:
   * continuous positive density `bimodalDensity` (`2/3` on `[0, 1]`, cubic trough down to `2/27` at
     `v = 2`, rising linearly to a second mode `4/27` at `v = 3`);
   * failure of regularity (`¬ IsRegular`, since `φ(1) = 1/2 > 7/16 = φ(3/2)`) and
     non-implementability of every 2-bidder un-ironed single-item virtual-welfare maximizer
     (`not_isImplementable_iid_of_virtualValue_gt`);
   * explicit continuous ironed virtual valuation `bimodalIroned` pooling `[1, 2]` at `+1/2 > 0`,
     satisfying `IsIronedVirtualValue` (and negative witness showing un-ironed `φ` fails
     `IsIronedVirtualValue`);
   * instantiation of `Vickrey.integral_sum_payment_le_ironed_of_isIronedVirtualValue` and irregular
     digital-goods monopoly pricing `IsMonopolyPrice bimodal (3 / 4)`
     (`integral_sum_payment_le_postedPriceDigitalGoods`).
3. **Seller reservation value `v₀ = 1/3`** (Exercise 13.1): shifted reserve `2/3` on `U[0, 1]`
   (`Vickrey.integral_profit_le_sellerReserve`) and conditional ironed seller-reserve optimality on
   irregular `bimodal` (`Vickrey.integral_profit_le_ironed_sellerReserve_of_isIronedVirtualValue`).
4. **Empirical Myerson (`DOP` Example 13.23 and single-item `EM` Exercise 13.4)**:
   * `k = 10` instance of `dopBadBids` (`10` bids at `$10` and `90` bids at `$1`): optimal
     single-price revenue `100` vs. `DOP` profit `10`
     (`empiricalSinglePriceRevenue_dopBadBids_opt`, `dopMechanism_sum_payment_dopBadBids`);
   * `n = 3` single-item profiles (strict winner and exact tie) verifying
     `empiricalSingleItemMechanism_allocation` and `empiricalSingleItemMechanism_payment`.
-/

-- Downstream leaf test module intentionally keeps declarations non-public.
set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.IronedMyerson

open MeasureTheory Set Cslib.GameTheory Cslib.GameTheory.SingleParameter
  Cslib.GameTheory.SingleParameter.Vickrey

/-! ### 1. Discrete 3-point irregular witnesses (`![2, 3, 10]` and `![4, 5, 12]`) -/

/-- Three-point irregular prior `v = ![2, 3, 10]` with probabilities `![1/2, 1/4, 1/4]`. -/
noncomputable def discreteNegPool : DiscretePrior 2 where
  val := ![2, 3, 10]
  prob := ![1 / 2, 1 / 4, 1 / 4]
  strictMono i j hij := by
    fin_cases i <;> fin_cases j <;> (try exact absurd hij (by decide)) <;> norm_num
  val_zero_nonneg := by norm_num
  prob_pos k := by fin_cases k <;> norm_num
  sum_prob := by rw [Fin.sum_univ_three]; norm_num

/-- Its discrete virtual valuation is `![1, -4, 10]` (strictly non-monotone across `0`), so
single-bidder virtual-surplus maximization (`![1, 0, 1]`) is non-monotone and not
DSIC-implementable, whereas `![-2/3, -2/3, 10]` satisfies `IsDiscreteIronedVirtualValue`. -/
example : discreteNegPool.virtualValue = ![1, -4, 10] ∧
    (¬ Monotone (![1, 0, 1] : Fin 3 → ℝ) ∧
      ¬ ∃ p, discreteNegPool.IsDiscreteDSIC ![1, 0, 1] p) ∧
    IsDiscreteIronedVirtualValue discreteNegPool ![-2 / 3, -2 / 3, 10] := by
  have hvv : discreteNegPool.virtualValue = ![1, -4, 10] := by
    ext k
    fin_cases k
    · change discreteNegPool.virtualValue (0 : Fin 2).castSucc = 1
      rw [DiscretePrior.virtualValue_castSucc, Finset.sum_filter, Fin.sum_univ_three]
      simp only [discreteNegPool]
      norm_num
    · change discreteNegPool.virtualValue (1 : Fin 2).castSucc = -4
      rw [DiscretePrior.virtualValue_castSucc, Finset.sum_filter, Fin.sum_univ_three]
      simp only [discreteNegPool]
      norm_num
    · change discreteNegPool.virtualValue (Fin.last 2) = 10
      rw [DiscretePrior.virtualValue_last]
      rfl
  refine ⟨hvv, ?_, ?_⟩
  · have hnm : ¬ Monotone (![1, 0, 1] : Fin 3 → ℝ) := by
      refine discreteNegPool.not_monotone_virtualWelfareMaximizer_of_gt (j := 0) (k := 1) (c₀ := 0)
        (by decide) (by rw [hvv]; norm_num) (by rw [hvv]; norm_num)
        (fun r => by fin_cases r <;> norm_num) fun r y hy0 hy1 => ?_
      rw [hvv]
      fin_cases r <;> { dsimp; nlinarith }
    exact ⟨hnm, fun ⟨_, hp⟩ => hnm (hp.monotone discreteNegPool)⟩
  · refine ⟨fun i j hij => by
        fin_cases i <;> fin_cases j <;> (try exact absurd hij (by decide)) <;> norm_num,
      fun k => ?_, ?_, fun i hlt => ?_⟩
    · rw [hvv]
      fin_cases k <;>
        { rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_three, Fin.sum_univ_three]
          simp only [discreteNegPool]
          norm_num }
    · rw [hvv, Fin.sum_univ_three, Fin.sum_univ_three]
      simp only [discreteNegPool]
      norm_num
    · fin_cases i
      · rfl
      · exfalso
        rw [hvv, Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_three,
          Fin.sum_univ_three] at hlt
        revert hlt
        simp only [discreteNegPool]
        norm_num

/-- Three-point irregular prior `v = ![4, 5, 12]` with probabilities `![1/2, 1/4, 1/4]`, where
types `0` (`v = 4`) and `1` (`v = 5`) pool at **positive** ironed virtual value `+4/3 > 0`. -/
noncomputable def discretePosPool : DiscretePrior 2 where
  val := ![4, 5, 12]
  prob := ![1 / 2, 1 / 4, 1 / 4]
  strictMono i j hij := by
    fin_cases i <;> fin_cases j <;> (try exact absurd hij (by decide)) <;> norm_num
  val_zero_nonneg := by norm_num
  prob_pos k := by fin_cases k <;> norm_num
  sum_prob := by rw [Fin.sum_univ_three]; norm_num

theorem virtualValue_discretePosPool : discretePosPool.virtualValue = ![3, -2, 12] := by
  ext k
  fin_cases k
  · change discretePosPool.virtualValue (0 : Fin 2).castSucc = 3
    rw [DiscretePrior.virtualValue_castSucc, Finset.sum_filter, Fin.sum_univ_three]
    simp only [discretePosPool]
    norm_num
  · change discretePosPool.virtualValue (1 : Fin 2).castSucc = -2
    rw [DiscretePrior.virtualValue_castSucc, Finset.sum_filter, Fin.sum_univ_three]
    simp only [discretePosPool]
    norm_num
  · change discretePosPool.virtualValue (Fin.last 2) = 12
    rw [DiscretePrior.virtualValue_last]
    rfl

theorem isDiscreteIroned_discretePosPool :
    IsDiscreteIronedVirtualValue discretePosPool ![4 / 3, 4 / 3, 12] where
  monotone i j hij := by
    fin_cases i <;> fin_cases j <;> (try exact absurd hij (by decide)) <;> norm_num
  tail_le k := by
    rw [virtualValue_discretePosPool]
    fin_cases k <;>
      { rw [Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_three, Fin.sum_univ_three]
        simp only [discretePosPool]
        norm_num }
  sum_eq := by
    rw [virtualValue_discretePosPool, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [discretePosPool]
    norm_num
  eq_of_lt i hlt := by
    fin_cases i
    · rfl
    · exfalso
      rw [virtualValue_discretePosPool, Finset.sum_filter, Finset.sum_filter, Fin.sum_univ_three,
        Fin.sum_univ_three] at hlt
      revert hlt
      simp only [discretePosPool]
      norm_num

/-- Negative witness: the un-ironed virtual valuation `![3, -2, 12]` fails
`IsDiscreteIronedVirtualValue`. -/
example : ¬ IsDiscreteIronedVirtualValue discretePosPool discretePosPool.virtualValue := by
  intro h
  have h01 := h.monotone (show (0 : Fin 3) ≤ 1 by decide)
  rw [virtualValue_discretePosPool] at h01
  norm_num at h01

/-- Optimal 2-bidder i.i.d. ironed single-item allocation on `discretePosPool`: pools `{4, 5}` at
`+4/3 > 0` (ties to bidder `0`). -/
noncomputable def posPoolIronedAlloc (k : Fin 2 → Fin 3) : Fin 2 → ℝ :=
  if k 0 = 2 then ![1, 0] else if k 1 = 2 then ![0, 1] else ![1, 0]

/-- Un-pooled discrete Vickrey allocation (`VA_4`, distinguishing `4 < 5`, ties to bidder `0`). -/
noncomputable def posPoolVickreyAlloc (k : Fin 2 → Fin 3) : Fin 2 → ℝ :=
  if k 1 ≤ k 0 then ![1, 0] else ![0, 1]

private theorem sum_fin2_fin3 (F : (Fin 2 → Fin 3) → ℝ) :
    (∑ k : Fin 2 → Fin 3, F k) = ∑ a : Fin 3, ∑ b : Fin 3, F ![a, b] := by
  rw [← (piFinTwoEquiv fun _ => Fin 3).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => congrArg F ?_
  ext i
  fin_cases i <;> rfl

/-- Two-bidder i.i.d. auction on `![4, 5, 12]`: pooling `{4, 5}` at `+4/3 > 0` achieves expected
revenue `6`, strictly exceeding un-pooled Vickrey (`43/8`), and dominates every discrete DSIC, IR
single-item mechanism by `expectedDiscreteSumPayment_le_ironed_of_isDiscreteIronedVirtualValue`. -/
example :
    (∑ k : Fin 2 → Fin 3, (∏ j, discretePosPool.prob (k j)) *
        ∑ i, discretePosPool.envelopePayment
          (fun r => posPoolVickreyAlloc (Function.update k i r) i) (k i)) = 43 / 8 ∧
    (∑ k : Fin 2 → Fin 3, (∏ j, discretePosPool.prob (k j)) *
        ∑ i, discretePosPool.envelopePayment
          (fun r => posPoolIronedAlloc (Function.update k i r) i) (k i)) = 6 ∧
    (∑ k : Fin 2 → Fin 3, (∏ j, discretePosPool.prob (k j)) *
        ∑ i, discretePosPool.envelopePayment
          (fun r => posPoolVickreyAlloc (Function.update k i r) i) (k i)) ≤
      ∑ k : Fin 2 → Fin 3, (∏ j, discretePosPool.prob (k j)) *
        ∑ i, discretePosPool.envelopePayment
          (fun r => posPoolIronedAlloc (Function.update k i r) i) (k i) := by
  have hx_max : ∀ k : Fin 2 → Fin 3, posPoolIronedAlloc k ∈ singleItemFeasible ∧
      ∀ y ∈ singleItemFeasible,
        ∑ i : Fin 2, (![4 / 3, 4 / 3, 12] : Fin 3 → ℝ) (k i) * y i ≤
          ∑ i : Fin 2, (![4 / 3, 4 / 3, 12] : Fin 3 → ℝ) (k i) * posPoolIronedAlloc k i := by
    intro k
    refine ⟨⟨fun i => ?_, ?_⟩, fun y hy => ?_⟩
    · fin_cases i <;> { simp only [posPoolIronedAlloc]; split_ifs <;> simp }
    · simp only [Fin.sum_univ_two, posPoolIronedAlloc]
      split_ifs <;> norm_num
    · have hy0 : 0 ≤ y 0 := by rcases hy.1 0 with h | h <;> rw [h]; exact zero_le_one
      have hy1 : 0 ≤ y 1 := by rcases hy.1 1 with h | h <;> rw [h]; exact zero_le_one
      have hsum : y 0 + y 1 ≤ 1 := by simpa only [Fin.sum_univ_two] using hy.2
      simp only [Fin.sum_univ_two, posPoolIronedAlloc]
      rcases k 0 with ⟨_ | _ | _ | _, _⟩ <;> rcases k 1 with ⟨_ | _ | _ | _, _⟩ <;> try omega
      all_goals { dsimp; linarith }
  have hx_pool : ∀ (i : Fin 2) (k : Fin 2 → Fin 3) (r : Fin 2),
      (![4 / 3, 4 / 3, 12] : Fin 3 → ℝ) r.castSucc = (![4 / 3, 4 / 3, 12] : Fin 3 → ℝ) r.succ →
        posPoolIronedAlloc (Function.update k i r.castSucc) i =
          posPoolIronedAlloc (Function.update k i r.succ) i := by
    intro i k r heq
    fin_cases r
    · fin_cases i <;> rcases k 0 with ⟨_ | _ | _ | _, _⟩ <;>
        rcases k 1 with ⟨_ | _ | _ | _, _⟩ <;> try omega
      all_goals rfl
    · norm_num at heq
  have hv_mem : ∀ k, posPoolVickreyAlloc k ∈ singleItemFeasible := fun k => by
    refine ⟨fun i => ?_, ?_⟩
    · fin_cases i <;> { simp only [posPoolVickreyAlloc]; split_ifs <;> simp }
    · simp only [Fin.sum_univ_two, posPoolVickreyAlloc]
      split_ifs <;> norm_num
  have hv_mono : ∀ (i : Fin 2) (k : Fin 2 → Fin 3),
      Monotone (fun r => posPoolVickreyAlloc (Function.update k i r) i) := by
    intro i k a b hab
    fin_cases i
    · have h0 : ∀ r : Fin 3, posPoolVickreyAlloc (Function.update k 0 r) 0 =
          if k 1 ≤ r then 1 else 0 := fun r => by
        simp only [posPoolVickreyAlloc, Function.update_self,
          Function.update_of_ne (by decide : (1 : Fin 2) ≠ 0)]
        split_ifs <;> rfl
      change posPoolVickreyAlloc (Function.update k 0 a) 0 ≤
        posPoolVickreyAlloc (Function.update k 0 b) 0
      rw [h0, h0]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd (h1.trans hab) h2
      · norm_num
      · exact le_rfl
    · have h1 : ∀ r : Fin 3, posPoolVickreyAlloc (Function.update k 1 r) 1 =
          if r ≤ k 0 then 0 else 1 := fun r => by
        simp only [posPoolVickreyAlloc, Function.update_self,
          Function.update_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        split_ifs <;> rfl
      change posPoolVickreyAlloc (Function.update k 1 a) 1 ≤
        posPoolVickreyAlloc (Function.update k 1 b) 1
      rw [h1, h1]
      split_ifs with ha hb hb
      · exact le_rfl
      · norm_num
      · exact absurd (hab.trans hb) ha
      · exact le_rfl
  let pVick (k : Fin 2 → Fin 3) (i : Fin 2) : ℝ :=
    discretePosPool.envelopePayment (fun r => posPoolVickreyAlloc (Function.update k i r) i) (k i)
  have hpVick : ∀ (i : Fin 2) (k : Fin 2 → Fin 3),
      (fun r => pVick (Function.update k i r) i) =
        discretePosPool.envelopePayment fun r => posPoolVickreyAlloc (Function.update k i r) i := by
    intro i k
    ext r
    simp only [pVick, Function.update_self, Function.update_idem]
  have hv_dsic : ∀ i k, discretePosPool.IsDiscreteDSIC
      (fun r => posPoolVickreyAlloc (Function.update k i r) i)
      (fun r => pVick (Function.update k i r) i) := fun i k => by
    rw [hpVick]
    exact discretePosPool.envelopePayment_isDiscreteDSIC_iff.2 (hv_mono i k)
  have hv_ir : ∀ i k, discretePosPool.IsDiscreteIR
      (fun r => posPoolVickreyAlloc (Function.update k i r) i)
      (fun r => pVick (Function.update k i r) i) := fun i k => by
    rw [hpVick]
    exact discretePosPool.envelopePayment_isDiscreteIR fun r => by
      rcases (hv_mem (Function.update k i r)).1 i with h | h <;> rw [h]
      exact zero_le_one
  have hopt := expectedDiscreteSumPayment_le_ironed_of_isDiscreteIronedVirtualValue
    (fun _ : Fin 2 => discretePosPool) (fun _ => isDiscreteIroned_discretePosPool)
    hx_max hx_pool (p' := pVick) hv_mem hv_dsic hv_ir
  have hrev_v : (∑ k : Fin 2 → Fin 3, (∏ j, discretePosPool.prob (k j)) *
      ∑ i, pVick k i) = 43 / 8 := by
    rw [sum_fin2_fin3]
    simp only [Fin.sum_univ_three, Fin.prod_univ_two, Fin.sum_univ_two, pVick,
      DiscretePrior.envelopePayment, Finset.sum_filter, Fin.sum_univ_two, discretePosPool,
      posPoolVickreyAlloc]
    norm_num
  have hrev_ir : (∑ k : Fin 2 → Fin 3, (∏ j, discretePosPool.prob (k j)) *
      ∑ i, discretePosPool.envelopePayment
        (fun r => posPoolIronedAlloc (Function.update k i r) i) (k i)) = 6 := by
    rw [sum_fin2_fin3]
    simp only [Fin.sum_univ_three, Fin.prod_univ_two, Fin.sum_univ_two,
      DiscretePrior.envelopePayment, Finset.sum_filter, Fin.sum_univ_two, discretePosPool,
      posPoolIronedAlloc]
    norm_num
  exact ⟨hrev_v, hrev_ir, hopt⟩

/-! ### 2. Continuous bimodal irregular density on `[0, 3]` -/

/-- Positive continuous bimodal real density on `[0, 3]`: constant `2/3` on `[0, 1]`, cubic trough
`2/27 + (16/27)(2 − v)³` on `[1, 2]` down to `2/27` at `v = 2`, and rising `(2/27)(v − 1)` up to a
second mode `4/27` at `v = 3`. -/
noncomputable def bimodalDensityReal (v : ℝ) : ℝ :=
  2 / 27 + (16 / 27) * (max 0 (min 1 (2 - v))) ^ 3 + (2 / 27) * max 0 (v - 2)

noncomputable def bimodalDensity (v : ℝ) : NNReal :=
  Real.toNNReal (bimodalDensityReal v)

noncomputable def bimodal : Measure ℝ :=
  (volume.restrict (Icc 0 3)).withDensity fun v => (bimodalDensity v : ENNReal)

theorem continuous_bimodalDensityReal : Continuous bimodalDensityReal := by
  unfold bimodalDensityReal
  fun_prop

theorem bimodalDensityReal_pos (v : ℝ) : 0 < bimodalDensityReal v := by
  unfold bimodalDensityReal
  have h1 : 0 ≤ max 0 (min 1 (2 - v)) := le_max_left _ _
  have h2 : 0 ≤ max 0 (v - 2) := le_max_left _ _
  positivity

theorem continuous_bimodalDensity : Continuous bimodalDensity :=
  continuous_real_toNNReal.comp continuous_bimodalDensityReal

theorem hasValueDensity_bimodal : HasValueDensity bimodal bimodalDensity 3 where
  measurable := continuous_bimodalDensity.measurable
  eq_withDensity := rfl
  pos v _ := Real.toNNReal_pos.2 (bimodalDensityReal_pos v)

private theorem bimodalDensityReal_of_le_one {v : ℝ} (hv : v ≤ 1) :
    bimodalDensityReal v = 2 / 3 := by
  unfold bimodalDensityReal
  rw [min_eq_left (by linarith), max_eq_right zero_le_one, max_eq_left (by linarith)]
  norm_num

private theorem bimodalDensityReal_of_Icc_one_two {v : ℝ} (hv1 : 1 ≤ v) (hv2 : v ≤ 2) :
    bimodalDensityReal v = 2 / 27 + (16 / 27) * (2 - v) ^ 3 := by
  unfold bimodalDensityReal
  rw [min_eq_right (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]
  ring

private theorem bimodalDensityReal_of_two_le {v : ℝ} (hv : 2 ≤ v) :
    bimodalDensityReal v = (2 / 27) * (v - 1) := by
  unfold bimodalDensityReal
  rw [min_eq_right (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]
  ring

private theorem intervalIntegral_bimodal_two_three {v : ℝ} (hv2 : 2 ≤ v) (hv3 : v ≤ 3) :
    ∫ z in v..3, bimodalDensityReal z = (1 / 27) * (3 - v) * (v + 1) := by
  have hcongr : ∫ z in v..3, bimodalDensityReal z = ∫ z in v..3, (2 / 27) * (z - 1) := by
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le hv3] at hz
    exact bimodalDensityReal_of_two_le (hv2.trans hz.1)
  let F : ℝ → ℝ := fun z => -((1 / 27) * (3 - z) * (z + 1))
  have hderiv : ∀ z ∈ uIcc v 3, HasDerivAt F ((2 / 27) * (z - 1)) z := fun z _ => by
    have hd := (((hasDerivAt_const z (3 : ℝ)).sub (hasDerivAt_id z)).mul
      ((hasDerivAt_id z).add (hasDerivAt_const z 1)) |>.const_mul (1 / 27 : ℝ)).neg
    have hfun : HasDerivAt F _ z :=
      hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
        dsimp only [F, Pi.neg_apply, Pi.mul_apply, Pi.sub_apply, Pi.add_apply, id_eq]
        ring)
    convert hfun using 1
    dsimp only [Pi.add_apply, Pi.sub_apply, id_eq]
    ring
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)]
  simp only [F]
  ring

private theorem intervalIntegral_bimodal_one_two {v : ℝ} (hv1 : 1 ≤ v) (hv2 : v ≤ 2) :
    ∫ z in v..2, bimodalDensityReal z =
      1 / 9 + (2 / 27) * (2 - v) + (4 / 27) * (2 - v) ^ 4 - 1 / 9 := by
  have hcongr : ∫ z in v..2, bimodalDensityReal z =
      ∫ z in v..2, (2 / 27 + (16 / 27) * (2 - z) ^ 3) := by
    refine intervalIntegral.integral_congr fun z hz => ?_
    rw [uIcc_of_le hv2] at hz
    exact bimodalDensityReal_of_Icc_one_two (hv1.trans hz.1) hz.2
  let F : ℝ → ℝ := fun z => -(1 / 9 + (2 / 27) * (2 - z) + (4 / 27) * (2 - z) ^ 4)
  have hderiv : ∀ z ∈ uIcc v 2, HasDerivAt F (2 / 27 + (16 / 27) * (2 - z) ^ 3) z := fun z _ => by
    have hsub := (hasDerivAt_const z (2 : ℝ)).sub (hasDerivAt_id z)
    have hd := ((hasDerivAt_const z (1 / 9 : ℝ)).add (hsub.const_mul (2 / 27))).add
      ((hsub.pow 4).const_mul (4 / 27)) |>.neg
    have hfun : HasDerivAt F _ z :=
      hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => by
        dsimp only [F, Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.pow_apply, id_eq])
    convert hfun using 1
    dsimp only [Pi.sub_apply, id_eq]
    ring
  have hcont : Continuous fun z : ℝ => 2 / 27 + (16 / 27) * (2 - z) ^ 3 := by fun_prop
  rw [hcongr, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp only [F]
  ring

private theorem bimodal_Ioi_eq_ofReal {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    bimodal (Ioi v) = ENNReal.ofReal (∫ z in v..3, bimodalDensityReal z) := by
  have hset : Ioi v ∩ Icc (0 : ℝ) 3 = Ioc v 3 := by
    ext w
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hv0.trans h1.le, h3⟩⟩
  rw [bimodal, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    hset]
  have hcoe : (fun z => (bimodalDensity z : ENNReal)) =
      fun z => ENNReal.ofReal (bimodalDensityReal z) := by
    ext z
    rfl
  rw [hcoe]
  have hint : IntegrableOn bimodalDensityReal (Ioc v 3) :=
    continuous_bimodalDensityReal.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc v 3)] bimodalDensityReal :=
    Filter.Eventually.of_forall fun z => (bimodalDensityReal_pos z).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, intervalIntegral.integral_of_le hv3]

private theorem intervalIntegral_bimodal_zero_three {v : ℝ} (hv3 : v ≤ 3) :
    ∫ z in v..3, bimodalDensityReal z =
      if v ≤ 1 then 1 - (2 / 3) * v
      else if v ≤ 2 then 1 / 9 + (2 / 27) * (2 - v) + (4 / 27) * (2 - v) ^ 4
      else (1 / 27) * (3 - v) * (v + 1) := by
  have hint := fun a b : ℝ => continuous_bimodalDensityReal.intervalIntegrable (μ := volume) a b
  split_ifs with hv1 hv2
  · have h01 : ∫ z in v..1, bimodalDensityReal z = (2 / 3) * (1 - v) := by
      have hc : ∫ z in v..1, bimodalDensityReal z = ∫ _ in v..1, (2 / 3 : ℝ) := by
        refine intervalIntegral.integral_congr fun z hz => ?_
        rw [uIcc_of_le hv1] at hz
        exact bimodalDensityReal_of_le_one hz.2
      rw [hc, intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint v 1) (hint 1 3),
      ← intervalIntegral.integral_add_adjacent_intervals (hint 1 2) (hint 2 3),
      h01, intervalIntegral_bimodal_one_two le_rfl (by norm_num),
      intervalIntegral_bimodal_two_three le_rfl (by norm_num)]
    ring
  · push Not at hv1
    rw [← intervalIntegral.integral_add_adjacent_intervals (hint v 2) (hint 2 3),
      intervalIntegral_bimodal_one_two hv1.le hv2,
      intervalIntegral_bimodal_two_three le_rfl (by norm_num)]
    ring
  · push Not at hv2
    exact intervalIntegral_bimodal_two_three hv2.le hv3

instance : IsProbabilityMeasure bimodal := by
  refine ⟨?_⟩
  have hIoc : Ioi (0 : ℝ) ∩ Icc 0 3 = Ioc 0 3 := by
    ext w
    simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, h1.le, h3⟩⟩
  have h0 := bimodal_Ioi_eq_ofReal (v := 0) le_rfl (by norm_num)
  rw [intervalIntegral_bimodal_zero_three (by norm_num)] at h0
  rw [bimodal, withDensity_apply _ measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    hIoc] at h0
  rw [bimodal, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← setLIntegral_congr Ioc_ae_eq_Icc, h0]
  norm_num

theorem bimodal_real_Ioi {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    bimodal.real (Ioi v) =
      if v ≤ 1 then 1 - (2 / 3) * v
      else if v ≤ 2 then 1 / 9 + (2 / 27) * (2 - v) + (4 / 27) * (2 - v) ^ 4
      else (1 / 27) * (3 - v) * (v + 1) := by
  have hint_nonneg : 0 ≤ ∫ z in v..3, bimodalDensityReal z :=
    intervalIntegral.integral_nonneg hv3 fun z _ => (bimodalDensityReal_pos z).le
  rw [measureReal_def, bimodal_Ioi_eq_ofReal hv0 hv3, ENNReal.toReal_ofReal hint_nonneg,
    intervalIntegral_bimodal_zero_three hv3]

theorem virtualValue_bimodal_one : virtualValue bimodal bimodalDensity 1 = 1 / 2 := by
  rw [virtualValue, bimodal_real_Ioi (by norm_num) (by norm_num), bimodalDensity,
    Real.coe_toNNReal _ (bimodalDensityReal_pos 1).le, bimodalDensityReal_of_le_one le_rfl]
  norm_num

theorem virtualValue_bimodal_three_halves :
    virtualValue bimodal bimodalDensity (3 / 2) = 7 / 16 := by
  rw [virtualValue, bimodal_real_Ioi (by norm_num) (by norm_num), bimodalDensity,
    Real.coe_toNNReal _ (bimodalDensityReal_pos (3 / 2)).le,
    bimodalDensityReal_of_Icc_one_two (by norm_num) (by norm_num)]
  norm_num

/-- **Irregularity witness:** `bimodal` is **not** regular (`φ(1) = 1/2 > 7/16 = φ(3/2)`). -/
theorem not_isRegular_bimodal : ¬ IsRegular bimodal bimodalDensity 3 := by
  intro hreg
  have hlt := hreg (show (1 : ℝ) ∈ Ioo 0 3 by norm_num) (show (3 / 2 : ℝ) ∈ Ioo 0 3 by norm_num)
    (by norm_num)
  rw [virtualValue_bimodal_one, virtualValue_bimodal_three_halves] at hlt
  norm_num at hlt

/-- **Continuous Lemma 13.12 necessity witness:** for 2 i.i.d. `bimodal` bidders, **no** un-ironed
single-item virtual-welfare maximizer is implementable (`¬ IsImplementable x`). -/
example {x : (Fin 2 → ℝ) → Fin 2 → ℝ}
    (hx : IsVirtualWelfareMaximizing (fun _ => virtualValue bimodal bimodalDensity)
      singleItemFeasible x) : ¬ IsImplementable x := by
  have hcont : ContinuousOn (virtualValue bimodal bimodalDensity) (Icc (3 / 2) 3) := by
    have htail_cont : ContinuousOn (fun v : ℝ => bimodal.real (Ioi v)) (Icc (3 / 2) 3) := by
      have heq : EqOn (fun v : ℝ =>
          if v ≤ 2 then 1 / 9 + (2 / 27) * (2 - v) + (4 / 27) * (2 - v) ^ 4
          else (1 / 27) * (3 - v) * (v + 1))
          (fun v : ℝ => bimodal.real (Ioi v)) (Icc (3 / 2) 3) := by
        intro v hv
        dsimp only
        have hv1 : ¬ v ≤ 1 := by linarith [hv.1]
        rw [bimodal_real_Ioi (by linarith [hv.1]) hv.2]
        simp only [hv1, ↓reduceIte]
      have hpiece : Continuous fun v : ℝ =>
          if v ≤ 2 then 1 / 9 + (2 / 27) * (2 - v) + (4 / 27) * (2 - v) ^ 4
          else (1 / 27) * (3 - v) * (v + 1) := by
        refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
          fun v hv => ?_
        subst hv
        norm_num
      exact hpiece.continuousOn.congr heq.symm
    have hf_cont : ContinuousOn (fun v : ℝ => (bimodalDensity v : ℝ)) (Icc (3 / 2) 3) :=
      (NNReal.continuous_coe.comp continuous_bimodalDensity).continuousOn
    exact continuousOn_id.sub (htail_cont.div hf_cont fun v _ =>
      by rw [bimodalDensity, Real.coe_toNNReal _ (bimodalDensityReal_pos v).le]
         exact (bimodalDensityReal_pos v).ne')
  refine not_isImplementable_iid_of_virtualValue_gt (ι := Fin 2) (by decide)
    (v₁ := 1) (v₂ := 3 / 2) (h := 3) (by norm_num) (by norm_num) (by norm_num) hcont
    (virtualValue_le _ _ 0) ?_ ?_ ?_ hx
  · rw [virtualValue_bimodal_one, hasValueDensity_bimodal.virtualValue_eq_self le_rfl]
    norm_num
  · rw [virtualValue_bimodal_one, virtualValue_bimodal_three_halves]
    norm_num
  · rw [virtualValue_bimodal_one]
    norm_num

/-- Explicit continuous ironed virtual valuation on `ℝ` for `bimodal`, pooling `[1, 2]` at
`+1/2 > 0`. -/
noncomputable def bimodalIroned (v : ℝ) : ℝ :=
  if v ≤ 1 then 2 * v - 3 / 2
  else if v ≤ 2 then 1 / 2
  else if v ≤ 3 then (3 / 2) * v - 1 / 2 - 2 / (v - 1)
  else v

theorem continuous_bimodalIroned : Continuous bimodalIroned := by
  have hc23 : Continuous fun v : ℝ =>
      if v ≤ 3 then (3 / 2) * v - 1 / 2 - 2 / max 1 (v - 1) else v := by
    refine Continuous.if_le ?_ continuous_id continuous_id continuous_const fun v hv => ?_
    · refine ((continuous_const.mul continuous_id).sub continuous_const).sub
        (continuous_const.div (continuous_const.max (continuous_id.sub continuous_const)) fun z =>
          ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    · subst hv
      norm_num
  have hc13 : Continuous fun v : ℝ =>
      if v ≤ 2 then (1 / 2 : ℝ)
      else if v ≤ 3 then (3 / 2) * v - 1 / 2 - 2 / max 1 (v - 1) else v := by
    refine Continuous.if_le continuous_const hc23 continuous_id continuous_const fun v hv => ?_
    subst hv
    norm_num
  have hc_all : Continuous fun v : ℝ =>
      if v ≤ 1 then 2 * v - 3 / 2
      else if v ≤ 2 then (1 / 2 : ℝ)
      else if v ≤ 3 then (3 / 2) * v - 1 / 2 - 2 / max 1 (v - 1) else v := by
    refine Continuous.if_le (by fun_prop) hc13 continuous_id continuous_const fun v hv => ?_
    subst hv
    norm_num
  refine hc_all.congr fun v => ?_
  dsimp only [bimodalIroned]
  split_ifs with h1 h2 h3
  · rfl
  · rfl
  · rw [max_eq_right (by linarith)]
  · rfl

theorem monotone_bimodalIroned : Monotone bimodalIroned := by
  have h23_lo : ∀ x : ℝ, 2 < x → 1 / 2 ≤ (3 / 2) * x - 1 / 2 - 2 / (x - 1) := fun x hx => by
    have hd : 2 / (x - 1) ≤ 2 / 1 :=
      div_le_div_of_nonneg_left (by norm_num) zero_lt_one (by linarith)
    linarith
  have h23_hi : ∀ x : ℝ, 2 < x → x ≤ 3 → (3 / 2) * x - 1 / 2 - 2 / (x - 1) ≤ 3 :=
    fun x hx2 hx3 => by
      have hd : 2 / 2 ≤ 2 / (x - 1) :=
        div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
      linarith
  intro a b hab
  dsimp only [bimodalIroned]
  split_ifs with ha1 hb1 hb2 hb3 ha2 hb1 hb2 hb3 ha3 hb1 hb2 hb3 hb1 hb2 hb3
  · linarith
  · linarith
  · linarith [h23_lo b (by linarith)]
  · linarith
  · linarith
  · exact le_rfl
  · exact h23_lo b (by linarith)
  · linarith
  · linarith
  · linarith
  · have hd : 2 / (b - 1) ≤ 2 / (a - 1) :=
      div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    linarith
  · linarith [h23_hi a (by linarith) ha3]
  · linarith
  · linarith
  · linarith
  · exact hab

private theorem virtualValue_bimodal_eq_ironed_of_Icc_zero_one {z : ℝ} (hz0 : 0 ≤ z)
    (hz1 : z ≤ 1) : virtualValue bimodal bimodalDensity z = bimodalIroned z := by
  rw [virtualValue, bimodalIroned, bimodal_real_Ioi hz0 (by linarith), bimodalDensity,
    Real.coe_toNNReal _ (bimodalDensityReal_pos z).le, bimodalDensityReal_of_le_one hz1]
  simp only [hz1, ↓reduceIte]
  ring

private theorem virtualValue_bimodal_eq_ironed_of_Ioc_two_three {z : ℝ} (hz2 : 2 < z)
    (hz3 : z ≤ 3) : virtualValue bimodal bimodalDensity z = bimodalIroned z := by
  have hz1 : ¬ z ≤ 1 := by linarith
  have hz2' : ¬ z ≤ 2 := by linarith
  have hzne : z - 1 ≠ 0 := by linarith
  rw [virtualValue, bimodalIroned, bimodal_real_Ioi (by linarith) hz3, bimodalDensity,
    Real.coe_toNNReal _ (bimodalDensityReal_pos z).le, bimodalDensityReal_of_two_le hz2.le]
  simp only [hz1, hz2', hz3, ↓reduceIte]
  field_simp
  ring

private theorem integrable_bimodalIroned : Integrable bimodalIroned bimodal := by
  refine Integrable.of_bound continuous_bimodalIroned.measurable.aestronglyMeasurable 3 ?_
  filter_upwards [hasValueDensity_bimodal.ae_mem] with z hz
  have hlo : -3 / 2 ≤ bimodalIroned z := by
    have h0 : bimodalIroned 0 = -3 / 2 := by unfold bimodalIroned; norm_num
    linarith [monotone_bimodalIroned hz.1]
  have hhi : bimodalIroned z ≤ 3 := by
    have h3 : bimodalIroned 3 = 3 := by unfold bimodalIroned; norm_num
    linarith [monotone_bimodalIroned hz.2]
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, hhi⟩

private theorem setIntegral_Ioi_bimodalIroned {v : ℝ} (hv0 : 0 ≤ v) (hv3 : v ≤ 3) :
    ∫ z in Ioi v, bimodalIroned z ∂bimodal =
      if v ≤ 1 then ∫ z in Ioi v, virtualValue bimodal bimodalDensity z ∂bimodal
      else if v ≤ 2 then (1 / 2) * bimodal.real (Ioi v) + 1 / 6
      else ∫ z in Ioi v, virtualValue bimodal bimodalDensity z ∂bimodal := by
  have hge2 : ∀ w : ℝ, 2 ≤ w → w ≤ 3 →
      ∫ z in Ioi w, bimodalIroned z ∂bimodal =
        ∫ z in Ioi w, virtualValue bimodal bimodalDensity z ∂bimodal := fun w hw2 hw3 => by
    refine setIntegral_congr_ae measurableSet_Ioi ?_
    filter_upwards [hasValueDensity_bimodal.ae_mem] with z hz hzw
    exact (virtualValue_bimodal_eq_ironed_of_Ioc_two_three (hw2.trans_lt hzw) hz.2).symm
  have h2_val : ∫ z in Ioi (2 : ℝ), bimodalIroned z ∂bimodal = 2 / 9 := by
    rw [hge2 2 le_rfl (by norm_num),
      hasValueDensity_bimodal.setIntegral_Ioi_virtualValue_eq (by norm_num),
      bimodal_real_Ioi (by norm_num) (by norm_num)]
    norm_num
  have h12 : ∀ w : ℝ, 1 ≤ w → w ≤ 2 →
      ∫ z in Ioi w, bimodalIroned z ∂bimodal = (1 / 2) * bimodal.real (Ioi w) + 1 / 6 :=
    fun w hw1 hw2 => by
      have hunion : Ioi w = Ioc w 2 ∪ Ioi 2 := by
        ext z
        simp only [mem_Ioi, mem_union, mem_Ioc]
        constructor
        · intro h
          rcases le_or_gt z 2 with h2 | h2
          · exact Or.inl ⟨h, h2⟩
          · exact Or.inr h2
        · intro h
          exact h.elim (fun h1 => h1.1) (fun h2 => hw2.trans_lt h2)
      have hdisj : Disjoint (Ioc w 2) (Ioi 2) :=
        disjoint_left.2 fun z hz1 hz2 => not_lt.2 hz1.2 hz2
      have hIoc : ∫ z in Ioc w 2, bimodalIroned z ∂bimodal = (1 / 2) * bimodal.real (Ioc w 2) := by
        have hc : ∫ z in Ioc w 2, bimodalIroned z ∂bimodal =
            ∫ _ in Ioc w 2, (1 / 2 : ℝ) ∂bimodal := by
          refine setIntegral_congr_fun measurableSet_Ioc fun z hz => ?_
          have hz1 : ¬ z ≤ 1 := by linarith [hz.1]
          simp only [bimodalIroned, hz1, hz.2, ↓reduceIte]
        rw [hc, setIntegral_const, smul_eq_mul, mul_comm]
      have hmeas : bimodal.real (Ioi w) = bimodal.real (Ioc w 2) + bimodal.real (Ioi 2) := by
        conv_lhs => rw [hunion]
        exact measureReal_union hdisj measurableSet_Ioi
      have hm2 : bimodal.real (Ioi (2 : ℝ)) = 1 / 9 := by
        rw [bimodal_real_Ioi (by norm_num) (by norm_num)]
        norm_num
      conv_lhs => rw [hunion]
      rw [setIntegral_union hdisj measurableSet_Ioi integrable_bimodalIroned.integrableOn
        integrable_bimodalIroned.integrableOn, hIoc, h2_val]
      linarith
  split_ifs with hv1 hv2
  · have h1_eq : ∫ z in Ioi (1 : ℝ), bimodalIroned z ∂bimodal =
        ∫ z in Ioi (1 : ℝ), virtualValue bimodal bimodalDensity z ∂bimodal := by
      rw [h12 1 le_rfl (by norm_num),
        hasValueDensity_bimodal.setIntegral_Ioi_virtualValue_eq (by norm_num),
        bimodal_real_Ioi (by norm_num) (by norm_num)]
      norm_num
    have hunion : Ioi v = Ioc v 1 ∪ Ioi 1 := by
      ext z
      simp only [mem_Ioi, mem_union, mem_Ioc]
      constructor
      · intro h
        rcases le_or_gt z 1 with h1 | h1
        · exact Or.inl ⟨h, h1⟩
        · exact Or.inr h1
      · intro h
        exact h.elim (fun h1 => h1.1) (fun h1 => hv1.trans_lt h1)
    have hdisj : Disjoint (Ioc v 1) (Ioi 1) :=
      disjoint_left.2 fun z hz1 hz2 => not_lt.2 hz1.2 hz2
    have hIoc : ∫ z in Ioc v 1, bimodalIroned z ∂bimodal =
        ∫ z in Ioc v 1, virtualValue bimodal bimodalDensity z ∂bimodal :=
      setIntegral_congr_fun measurableSet_Ioc fun z hz =>
        (virtualValue_bimodal_eq_ironed_of_Icc_zero_one (hv0.trans hz.1.le) hz.2).symm
    rw [hunion, setIntegral_union hdisj measurableSet_Ioi integrable_bimodalIroned.integrableOn
        integrable_bimodalIroned.integrableOn,
      setIntegral_union hdisj measurableSet_Ioi
        hasValueDensity_bimodal.integrable_virtualValue.integrableOn
        hasValueDensity_bimodal.integrable_virtualValue.integrableOn,
      hIoc, h1_eq]
  · exact h12 v (le_of_not_ge hv1) hv2
  · exact hge2 v (le_of_not_ge hv2) hv3

/-- **Continuous `IsIronedVirtualValue` witness:** `bimodalIroned` satisfies every field of
`IsIronedVirtualValue bimodal bimodalDensity 3` (including positive pooling on `[1, 2]`). -/
theorem isIronedVirtualValue_bimodal :
    IsIronedVirtualValue bimodal bimodalDensity 3 bimodalIroned where
  measurable := continuous_bimodalIroned.measurable
  integrable := integrable_bimodalIroned
  monotoneOn := monotone_bimodalIroned.monotoneOn _
  setIntegral_Ioi_le v hv := by
    rw [setIntegral_Ioi_bimodalIroned hv.1 hv.2]
    split_ifs with hv1 hv2
    · exact le_rfl
    · rw [hasValueDensity_bimodal.setIntegral_Ioi_virtualValue_eq hv.1,
        bimodal_real_Ioi hv.1 hv.2]
      simp only [hv1, hv2, ↓reduceIte]
      have hfac : ((1 / 2) * (1 / 9 + (2 / 27) * (2 - v) + (4 / 27) * (2 - v) ^ 4) + 1 / 6) -
          v * (1 / 9 + (2 / 27) * (2 - v) + (4 / 27) * (2 - v) ^ 4) =
          (2 / 27) * (2 - v) ^ 2 * (v - 1) ^ 2 * (5 - 2 * v) := by ring
      have h5 : 0 ≤ 5 - 2 * v := by linarith
      have hnn : 0 ≤ (2 / 27) * (2 - v) ^ 2 * (v - 1) ^ 2 * (5 - 2 * v) := by positivity
      linarith
    · exact le_rfl
  integral_eq := by
    have h1 : ∫ z, virtualValue bimodal bimodalDensity z ∂bimodal =
        ∫ z in Ioi (0 : ℝ), virtualValue bimodal bimodalDensity z ∂bimodal := by
      rw [← integral_indicator measurableSet_Ioi]
      exact integral_congr_ae
        (hasValueDensity_bimodal.ae_pos.mono fun z hz => (indicator_of_mem hz _).symm)
    have h2 : ∫ z, bimodalIroned z ∂bimodal =
        ∫ z in Ioi (0 : ℝ), bimodalIroned z ∂bimodal := by
      rw [← integral_indicator measurableSet_Ioi]
      exact integral_congr_ae
        (hasValueDensity_bimodal.ae_pos.mono fun z hz => (indicator_of_mem hz _).symm)
    rw [h1, h2, setIntegral_Ioi_bimodalIroned le_rfl (by norm_num)]
    norm_num
  locallyConstant_of_lt v hv hlt := by
    rw [setIntegral_Ioi_bimodalIroned hv.1.le hv.2.le] at hlt
    have hv1 : ¬ v ≤ 1 := fun h1 => by simp only [h1, ↓reduceIte, lt_self_iff_false] at hlt
    have hv2 : v < 2 := by
      by_contra hge2
      have hge2' : 2 ≤ v := le_of_not_gt hge2
      rcases hge2'.eq_or_lt with rfl | hgt2
      · rw [hasValueDensity_bimodal.setIntegral_Ioi_virtualValue_eq (by norm_num),
          bimodal_real_Ioi (by norm_num) (by norm_num)] at hlt
        norm_num at hlt
      · have hn2 : ¬ v ≤ 2 := not_le.2 hgt2
        simp only [hv1, hn2, ↓reduceIte, lt_self_iff_false] at hlt
    have hv1' : 1 < v := lt_of_not_ge hv1
    refine ⟨min (v - 1) (2 - v), lt_min (by linarith) (by linarith), fun z _ hzv => ?_⟩
    rw [abs_lt] at hzv
    have hz1 : ¬ z ≤ 1 := by linarith [min_le_left (v - 1) (2 - v)]
    have hz2 : z ≤ 2 := by linarith [min_le_right (v - 1) (2 - v)]
    simp only [bimodalIroned, hz1, hz2, hv1, hv2.le, ↓reduceIte]

/-- Negative witness: the un-ironed virtual valuation fails `IsIronedVirtualValue`. -/
example : ¬ IsIronedVirtualValue bimodal bimodalDensity 3
    (virtualValue bimodal bimodalDensity) := by
  intro h
  have hle := h.monotoneOn (show (1 : ℝ) ∈ Ioc 0 3 by norm_num)
    (show (3 / 2 : ℝ) ∈ Ioc 0 3 by norm_num) (by norm_num)
  rw [virtualValue_bimodal_one, virtualValue_bimodal_three_halves] at hle
  norm_num at hle

/-- **Optimal irregular single-item auction witness:** for 2 i.i.d. `bimodal` bidders, the ironed
Myerson auction `myerson (Vickrey.ironedAllocation (fun _ => bimodalIroned))` is DSIC, IR, and
achieves at least the expected revenue of `Vickrey.mechanism` (and every DSIC, IR single-item
mechanism). -/
example :
    (myerson (Vickrey.ironedAllocation (fun _ : Fin 2 => bimodalIroned))).IsDSIC ∧
      (myerson (Vickrey.ironedAllocation (fun _ : Fin 2 => bimodalIroned))).IsIR ∧
      ∫ v, ∑ i, (Vickrey.mechanism (ι := Fin 2)).payment v i ∂Measure.pi (fun _ => bimodal) ≤
        ∫ v, ∑ i, (myerson (Vickrey.ironedAllocation (fun _ : Fin 2 => bimodalIroned))).payment v i
          ∂Measure.pi (fun _ => bimodal) := by
  refine ⟨myerson_isDSIC (Vickrey.isMonotone_ironedAllocation fun _ =>
      monotone_bimodalIroned.monotoneOn _),
    myerson_isIR (fun b _ i => by
      change (0 : ℝ) ≤ _
      rcases (Vickrey.ironedAllocation_mem_singleItemFeasible
        (fun _ : Fin 2 => bimodalIroned) b).1 i with h | h <;> rw [h]
      exact zero_le_one),
    Vickrey.integral_sum_payment_le_ironed_of_isIronedVirtualValue
      (fun _ => hasValueDensity_bimodal)
      (fun _ => isIronedVirtualValue_bimodal) (fun _ => monotone_bimodalIroned.monotoneOn _)
      mechanism_isDSIC mechanism_isIR (fun v _ => allocation_mem_singleItemFeasible v)
      measurable_allocation⟩

/-- **Monopoly sale price for irregular `bimodal`:** `opt(bimodal) = 3 / 4` (with single-buyer
revenue `3 / 8`), even though `bimodal` is irregular with a second mode at `v = 3`. -/
theorem isMonopolyPrice_bimodal : IsMonopolyPrice bimodal (3 / 4) := by
  have := hasValueDensity_bimodal.nullSingletonClass
  have h34 : (3 / 4 : ℝ) * bimodal.real (Ici (3 / 4)) = 3 / 8 := by
    rw [measureReal_congr (Ioi_ae_eq_Ici (μ := bimodal) (a := 3 / 4)).symm,
      bimodal_real_Ioi (by norm_num) (by norm_num)]
    norm_num
  refine ⟨by norm_num, fun p hp => ?_⟩
  rw [h34, measureReal_congr (Ioi_ae_eq_Ici (μ := bimodal) (a := p)).symm]
  rcases lt_or_ge 3 p with hp3 | hp3
  · rw [measureReal_def, hasValueDensity_bimodal.measure_Ioi_eq_zero hp3.le, ENNReal.toReal_zero,
      mul_zero]
    norm_num
  · rcases le_or_gt p 1 with hp1 | hp1
    · rw [bimodal_real_Ioi hp hp3]
      simp only [hp1, ↓reduceIte]
      nlinarith [sq_nonneg (p - 3 / 4)]
    · rcases le_or_gt p 2 with hp2 | hp2
      · have hle_iron := isIronedVirtualValue_bimodal.setIntegral_Ioi_le p ⟨hp, hp3⟩
        rw [hasValueDensity_bimodal.setIntegral_Ioi_virtualValue_eq hp,
          setIntegral_Ioi_bimodalIroned hp hp3] at hle_iron
        have hn1 : ¬ p ≤ 1 := not_le.2 hp1
        simp only [hn1, hp2, ↓reduceIte] at hle_iron
        have hmono : bimodal.real (Ioi p) ≤ bimodal.real (Ioi 1) :=
          measureReal_mono (Ioi_subset_Ioi hp1.le)
        have hm1 : bimodal.real (Ioi (1 : ℝ)) = 1 / 3 := by
          rw [bimodal_real_Ioi (by norm_num) (by norm_num)]
          norm_num
        linarith
      · have hmono : bimodal.real (Ioi p) ≤ bimodal.real (Ioi 2) :=
          measureReal_mono (Ioi_subset_Ioi hp2.le)
        have hm2 : bimodal.real (Ioi (2 : ℝ)) = 1 / 9 := by
          rw [bimodal_real_Ioi (by norm_num) (by norm_num)]
          norm_num
        nlinarith [measureReal_nonneg (μ := bimodal) (s := Ioi p)]

/-- **Theorem 13.18 witness without regularity:** for 2 i.i.d. `bimodal` bidders, offering fixed
monopoly price `3 / 4` (`postedPriceDigitalGoods (fun _ => 3 / 4)`) dominates offering price `1`
(and every DSIC, IR digital-goods mechanism). -/
example :
    ∫ v, ∑ i, (postedPriceDigitalGoods (fun _ : Fin 2 => (1 : ℝ))).payment v i
        ∂Measure.pi (fun _ => bimodal) ≤
      ∫ v, ∑ i, (postedPriceDigitalGoods (fun _ : Fin 2 => (3 / 4 : ℝ))).payment v i
        ∂Measure.pi (fun _ => bimodal) :=
  integral_sum_payment_le_postedPriceDigitalGoods (fun _ => hasValueDensity_bimodal.ae_mem)
    (fun _ => isMonopolyPrice_bimodal) (postedPriceDigitalGoods_isDSIC _)
    (postedPriceDigitalGoods_isIR _)
    (fun v _ => postedPriceDigitalGoods_mem_digitalGoodsFeasible _ v)
    (measurable_postedPriceDigitalGoods_allocation _)

/-! ### 3. Seller reservation value `v₀ = 1/3` (Exercise 13.1) -/

noncomputable abbrev unif : Measure ℝ := volume.restrict (Icc 0 1)

instance : IsProbabilityMeasure unif :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

/-- Regular monopoly price witness: `opt(U[0, 1]) = 1 / 2` via
`IsRegular.isMonopolyPrice_reservePrice`. -/
example : IsMonopolyPrice unif (1 / 2) := by
  simpa only [reservePrice_uniform] using
    isRegular_uniform.isMonopolyPrice_reservePrice hasValueDensity_uniform

/-- **Exercise 13.1 witness on `U[0, 1]` with seller value `v₀ = 1 / 3`:** the shifted virtual
reserve `φ⁻¹(1/3)` equals `2 / 3`, and `VA_{2/3}` dominates reserve-free Vickrey in expected seller
profit. -/
example :
    reservePrice (fun z => virtualValue unif (fun _ => 1) z - 1 / 3) = 2 / 3 ∧
      ∫ v : Fin 2 → ℝ, ((∑ i, Vickrey.mechanism.payment v i) -
          (1 / 3) * ∑ i, Vickrey.mechanism.allocation v i)
          ∂Measure.pi (fun _ => unif) ≤
        ∫ v : Fin 2 → ℝ,
          ((∑ i, max (reservePrice fun z => virtualValue unif (fun _ => 1) z - 1 / 3)
              (highestOtherBid v i) *
            reserveAllocation (fun z => virtualValue unif (fun _ => 1) z - 1 / 3) v i) -
          (1 / 3) * ∑ i, reserveAllocation (fun z => virtualValue unif (fun _ => 1) z - 1 / 3) v i)
          ∂Measure.pi (fun _ => unif) := by
  set φ₀ : ℝ → ℝ := fun z => virtualValue unif (fun _ => 1) z - 1 / 3
  have hmono : MonotoneOn φ₀ (Ioi 0) := fun a ha b hb hab =>
    sub_le_sub_right ((isRegular_uniform.strictMonoOn_Ioi hasValueDensity_uniform).monotoneOn
      ha hb hab) (1 / 3)
  have hthresh23 : IsReserveThreshold φ₀ (2 / 3) := by
    have hiff : ∀ v : ℝ, 0 ≤ v → (0 ≤ φ₀ v ↔ 2 / 3 ≤ v) := fun v hv => by
      rcases le_total v 1 with hv1 | hv1
      · dsimp only [φ₀]
        rw [virtualValue_uniform ⟨hv, hv1⟩]
        constructor <;> intro _ <;> linarith
      · dsimp only [φ₀]
        rw [hasValueDensity_uniform.virtualValue_eq_self hv1]
        constructor <;> intro _ <;> linarith
    exact ⟨by norm_num, fun v hv => (hiff v (by linarith)).2 hv.le,
      fun v hv0 hv => (hiff v hv0.le).1 hv⟩
  have hr : reservePrice φ₀ = 2 / 3 :=
    (isReserveThreshold_reservePrice hmono ⟨2, by norm_num, hthresh23.2.1 2 (by norm_num)⟩).unique
      hthresh23
  exact ⟨hr, Vickrey.integral_profit_le_sellerReserve (ι := Fin 2) hasValueDensity_uniform
    isRegular_uniform (by norm_num) mechanism_isDSIC mechanism_isIR
    (fun v _ => allocation_mem_singleItemFeasible v) measurable_allocation⟩

/-- **Irregular Exercise 13.1 witness on `bimodal` with seller value `v₀ = 1 / 3`:** instantiating
`Vickrey.integral_profit_le_ironed_sellerReserve_of_isIronedVirtualValue`. -/
example :
    ∫ v, ((∑ i, (Vickrey.mechanism (ι := Fin 2)).payment v i) -
        (1 / 3) * ∑ i, (Vickrey.mechanism (ι := Fin 2)).allocation v i)
        ∂Measure.pi (fun _ => bimodal) ≤
      ∫ v, ((∑ i, (myerson (Vickrey.ironedAllocation
            fun _ : Fin 2 => fun z => bimodalIroned z - 1 / 3)).payment v i) -
        (1 / 3) * ∑ i, Vickrey.ironedAllocation
          (fun _ : Fin 2 => fun z => bimodalIroned z - 1 / 3) v i)
        ∂Measure.pi (fun _ => bimodal) :=
  Vickrey.integral_profit_le_ironed_sellerReserve_of_isIronedVirtualValue
    (fun _ => hasValueDensity_bimodal)
    (fun _ => isIronedVirtualValue_bimodal) (fun _ => monotone_bimodalIroned.monotoneOn _)
    (by norm_num) mechanism_isDSIC mechanism_isIR
    (fun v _ => allocation_mem_singleItemFeasible v) measurable_allocation

/-! ### 4. Empirical Myerson: `DOP` (Example 13.23) and single-item `EM` (Exercise 13.4) -/

/-- **Example 13.23 client check (`k = 10` of `dopBadBids`):** `DOP` is DSIC and IR, optimal
single-price revenue on `dopBadBids 10` (`10` bids at `$10` and `90` bids at `$1`) is `100`, and
`DOP` total revenue is `10`. -/
example :
    (dopMechanism (ι := Fin (10 ^ 2))).IsDSIC ∧
      (dopMechanism (ι := Fin (10 ^ 2))).IsIR ∧
      empiricalSinglePriceRevenue Finset.univ (dopBadBids 10)
        (empiricalMonopolyPriceOn Finset.univ (dopBadBids 10)) = 100 ∧
      ∑ i : Fin (10 ^ 2), dopMechanism.payment (dopBadBids 10) i = 10 :=
  ⟨dopMechanism_isDSIC, dopMechanism_isIR,
    by rw [empiricalSinglePriceRevenue_dopBadBids_opt (by decide)]; norm_num,
    by rw [dopMechanism_sum_payment_dopBadBids (by decide)]; norm_num⟩

/-- **Exercise 13.4 client check on `n = 3` (strict winner `![10, 1, 8]` and exact tie
`![8, 8, 2]`):** `empiricalSingleItemMechanism` matches `Vickrey.mechanism` in allocation and
payment, awarding the item to bidder `0` at price `8` in both cases. -/
example :
    empiricalSingleItemMechanism.allocation ![(10 : ℝ), 1, 8] = ![1, 0, 0] ∧
      empiricalSingleItemMechanism.payment ![(10 : ℝ), 1, 8] = ![8, 0, 0] ∧
      empiricalSingleItemMechanism.allocation ![(8 : ℝ), 8, 2] = ![1, 0, 0] ∧
      empiricalSingleItemMechanism.payment ![(8 : ℝ), 8, 2] = ![8, 0, 0] := by
  have hb1 : (0 : Fin 3 → ℝ) ≤ ![(10 : ℝ), 1, 8] := fun i => by fin_cases i <;> norm_num
  have hb2 : (0 : Fin 3 → ℝ) ≤ ![(8 : ℝ), 8, 2] := fun i => by fin_cases i <;> norm_num
  rw [empiricalSingleItemMechanism_allocation hb1, empiricalSingleItemMechanism_payment hb1,
    empiricalSingleItemMechanism_allocation hb2, empiricalSingleItemMechanism_payment hb2]
  have hw1 : Wins ![(10 : ℝ), 1, 8] 0 := fun j hj => by
    fin_cases j
    · exact absurd rfl hj
    · norm_num
    · norm_num
  have hw2 : Wins ![(8 : ℝ), 8, 2] 0 := fun j hj => by
    fin_cases j
    · exact absurd rfl hj
    · exact ⟨by norm_num, fun hlt => absurd hlt (by decide)⟩
    · norm_num
  have halloc1 : Vickrey.mechanism.allocation ![(10 : ℝ), 1, 8] = ![1, 0, 0] := by
    ext i
    fin_cases i
    · exact allocation_eq_one_iff.2 hw1
    · exact allocation_eq_zero_iff.2 fun h => absurd (h.unique hw1) (by decide)
    · exact allocation_eq_zero_iff.2 fun h => absurd (h.unique hw1) (by decide)
  have halloc2 : Vickrey.mechanism.allocation ![(8 : ℝ), 8, 2] = ![1, 0, 0] := by
    ext i
    fin_cases i
    · exact allocation_eq_one_iff.2 hw2
    · exact allocation_eq_zero_iff.2 fun h => absurd (h.unique hw2) (by decide)
    · exact allocation_eq_zero_iff.2 fun h => absurd (h.unique hw2) (by decide)
  have hhob1 : highestOtherBid ![(10 : ℝ), 1, 8] 0 = 8 := by
    refine le_antisymm (highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩) ?_
    · fin_cases j
      · exact absurd rfl hj
      · norm_num
      · norm_num
    · exact le_of_eq_of_le (by norm_num)
        (le_highestOtherBid (b := ![(10 : ℝ), 1, 8]) (i := 0) (j := 2) (by decide))
  have hhob2 : highestOtherBid ![(8 : ℝ), 8, 2] 0 = 8 := by
    refine le_antisymm (highestOtherBid_le_iff.2 ⟨by norm_num, fun j hj => ?_⟩) ?_
    · fin_cases j
      · exact absurd rfl hj
      · norm_num
      · norm_num
    · exact le_of_eq_of_le (by norm_num)
        (le_highestOtherBid (b := ![(8 : ℝ), 8, 2]) (i := 0) (j := 1) (by decide))
  refine ⟨halloc1, ?_, halloc2, ?_⟩
  · ext i
    change highestOtherBid ![(10 : ℝ), 1, 8] i * Vickrey.mechanism.allocation ![(10 : ℝ), 1, 8] i =
      (![8, 0, 0] : Fin 3 → ℝ) i
    rw [halloc1]
    fin_cases i
    · dsimp
      rw [hhob1, mul_one]
    · dsimp
      rw [mul_zero]
    · dsimp
      rw [mul_zero]
  · ext i
    change highestOtherBid ![(8 : ℝ), 8, 2] i * Vickrey.mechanism.allocation ![(8 : ℝ), 8, 2] i =
      (![8, 0, 0] : Fin 3 → ℝ) i
    rw [halloc2]
    fin_cases i
    · dsimp
      rw [hhob2, mul_one]
    · dsimp
      rw [mul_zero]
    · dsimp
      rw [mul_zero]

end CslibFrontierTests.GameTheory.IronedMyerson
