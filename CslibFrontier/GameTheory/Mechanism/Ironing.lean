/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.OptimalAuction
import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import CslibFrontier.Foundations.Data.Finset.ApplyUpdate
import CslibFrontier.Foundations.MeasureTheory.Integral.IntervalPrimitive
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Myerson ironing, discrete virtual valuations, monopoly pricing, and empirical Myerson

When a valuation distribution is irregular (`¬ IsRegular μ f h`), pointwise maximization of
virtual welfare `∑ᵢ φᵢ(bᵢ) xᵢ` fails to produce a monotone allocation rule and therefore cannot be
implemented truthfully ([HartlineKarlin2007], Lemma 13.12, p. 337). Myerson's ironing construction
([Myerson1981]; [HartlineKarlin2007], §13.2.2, p. 337) replaces each virtual valuation `φᵢ` with a
monotone *ironed virtual valuation* `φ̄ᵢ` whose cumulative tail integrals dominate those of `φᵢ`,
with equality at `0` and local constancy wherever cumulative slack is positive.

This module develops five parts extending `CslibFrontier/GameTheory/Mechanism/OptimalAuction.lean`:

1. **Continuous Myerson ironing and conditional optimality step** (`IsIronedVirtualValue`,
   `IsIronedVirtualValue.integral_virtualValue_mul_le`,
   `IsIronedVirtualValue.integral_virtualValue_mul_eq`,
   `integral_sum_payment_le_ironed_myerson_of_isIronedVirtualValue`,
   `Vickrey.integral_sum_payment_le_ironed_of_isIronedVirtualValue`): via a layer-cake and Fubini
   representation of arbitrary measurable monotone allocation curves, every monotone curve has
   expected virtual surplus at most its expected ironed virtual surplus, with equality whenever the
   allocation rule is constant across pooled intervals. Given caller-supplied ironed virtual
   valuations `φBarᵢ` (constructive convex-hull existence of `IsIronedVirtualValue` from arbitrary
   `HasValueDensity` is tracked in #7789), maximizing ironed virtual welfare with
   ironed-bid-dependent tie-breaking is monotone, DSIC, individually rational, and maximizes
   expected seller revenue among all DSIC, IR mechanisms.
2. **Necessity of monotone virtual valuations** (`isMonotone_virtualSurplusMaximizer_iff`,
   `not_isImplementable_of_isVirtualWelfareMaximizing`,
   `not_isImplementable_iid_of_virtualValue_gt`): the converse direction of
   [HartlineKarlin2007], Lemma 13.12 (p. 337), both across linear seller-cost environments and in
   zero-cost single-item auctions.
3. **Seller production costs and reservation value `v₀ ≥ 0`**
   (`Mechanism.IsDSIC.integral_profit_le_virtualSurplus_sub_cost`,
   `Vickrey.integral_profit_le_sellerReserve`,
   `Vickrey.integral_profit_le_ironed_sellerReserve_of_isIronedVirtualValue`):
   [HartlineKarlin2007], Definition 13.9, Theorem 13.10 (p. 336), and Exercise 13.1 (p. 360),
   showing that for i.i.d. regular bidders and seller valuation `v₀ ≥ 0`, `VA_{φ⁻¹(v₀)}` maximizes
   expected seller profit, together with the conditional irregular optimality step given ironed
   virtual valuations.
4. **Monopoly pricing `opt(F)` and optimal Bayesian digital goods without regularity**
   (`IsMonopolyPrice`, `postedPriceDigitalGoods`,
   `integral_sum_payment_le_postedPriceDigitalGoods`): [HartlineKarlin2007], Definition 13.17 and
   Theorem 13.18 (p. 338), proved for arbitrary probability measures concentrated on `[0, hᵢ]`
   without regularity or density assumptions, together with `opt(F) = φ⁻¹(0)` for regular
   densities (`IsRegular.isMonopolyPrice_reservePrice`).
5. **Discrete finite-support virtual valuations, discrete ironing, `DOP`, and single-item `EM`**
   (`DiscretePrior`, `DiscretePrior.virtualValue`, `IsDiscreteIronedVirtualValue`,
   `expectedDiscreteSumPayment_le_ironed_of_isDiscreteIronedVirtualValue`,
   `empiricalMonopolyPrice`, `dopMechanism`, `dopBadBids`, `empiricalSingleItemMechanism`):
   [HartlineKarlin2007], Exercise 13.3 (p. 360) via summation by parts, discrete ironing inequality
   and conditional optimality step via Abel summation (discrete concave-envelope existence tracked
   in #7789), Definitions 13.19–13.21 and the parametric `k²`-bidder generalization of
   Example 13.23 (pp. 339–340) proving unbounded `k` vs. `k²` gap for `DOP`, and Exercise 13.4
   (p. 360) showing that single-item `EM` (`VA_{opt(F_{b₋ᵢ})}`) collapses identically to the
   reserve-free Vickrey auction.

## Main definitions

* `SingleParameter.IsIronedVirtualValue`: Myerson's ironed virtual valuation on `[0, h]`.
* `SingleParameter.ironedAllocation`, `SingleParameter.Vickrey.ironedAllocation`: pooling-invariant
  allocation rules factoring through ironed virtual bids.
* `SingleParameter.digitalGoodsFeasible`, `SingleParameter.IsMonopolyPrice`,
  `SingleParameter.postedPriceDigitalGoods`: digital-goods feasibility `[0, 1]^ι`, monopoly sale
  price `opt(F)`, and fixed posted-price digital goods auction ([HartlineKarlin2007],
  Definition 13.17).
* `SingleParameter.DiscretePrior`, `SingleParameter.DiscretePrior.virtualValue`,
  `SingleParameter.IsDiscreteIronedVirtualValue`: discrete finite-support priors, virtual
  valuations, and discrete ironed virtual valuations ([HartlineKarlin2007], Exercise 13.3).
* `SingleParameter.empiricalMonopolyPrice`, `SingleParameter.dopMechanism`,
  `SingleParameter.dopBadBids`, `SingleParameter.empiricalSingleItemMechanism`: empirical monopoly
  price `opt(F_{b₋ᵢ})`, `DOP`, its parametric `k²`-bidder worst-case family, and single-item `EM`
  ([HartlineKarlin2007], Definitions 13.19–13.21, Example 13.23).

## Main results

* `SingleParameter.HasValueDensity.setIntegral_Ioi_virtualValue_eq`: Bulow–Roberts tail identity
  `∫_{z > p} φ(z) dμ(z) = p · μ((p, ∞))` for `p ≥ 0`.
* `SingleParameter.IsIronedVirtualValue.integral_virtualValue_mul_le`,
  `SingleParameter.IsIronedVirtualValue.integral_virtualValue_mul_eq`: Myerson's continuous ironing
  inequality and pooling complementary-slackness equality.
* `SingleParameter.integral_sum_payment_le_ironed_myerson_of_isIronedVirtualValue`,
  `SingleParameter.Vickrey.integral_sum_payment_le_ironed_of_isIronedVirtualValue`: conditional
  optimality steps of [Myerson1981] given caller-supplied ironed virtual valuations (convex-hull
  existence tracked in #7789).
* `SingleParameter.isMonotone_virtualSurplusMaximizer_iff`,
  `SingleParameter.not_isImplementable_iid_of_virtualValue_gt`: necessity of monotone virtual
  valuations ([HartlineKarlin2007], Lemma 13.12).
* `SingleParameter.Vickrey.integral_profit_le_sellerReserve`,
  `SingleParameter.Vickrey.integral_profit_le_ironed_sellerReserve_of_isIronedVirtualValue`: optimal
  single-item auction with seller reservation value `v₀ ≥ 0` for regular distributions
  ([HartlineKarlin2007], Exercise 13.1), and conditional irregular optimality step given ironed
  virtual valuations.
* `SingleParameter.integral_sum_payment_le_postedPriceDigitalGoods`: optimal Bayesian digital goods
  auction via monopoly pricing without regularity ([HartlineKarlin2007], Theorem 13.18).
* `SingleParameter.DiscretePrior.expectedEnvelopePayment_eq_expectedVirtualSurplus`,
  `SingleParameter.IsDiscreteIronedVirtualValue.sum_virtualValue_mul_le`,
  `SingleParameter.expectedDiscreteSumPayment_le_ironed_of_isDiscreteIronedVirtualValue`: discrete
  virtual-surplus identity ([HartlineKarlin2007], Exercise 13.3), discrete ironing inequality, and
  conditional multi-bidder optimality step given discrete ironed virtual valuations.
* `SingleParameter.empiricalSingleItemMechanism_allocation`,
  `SingleParameter.empiricalSingleItemMechanism_payment`: single-item `EM` equals Vickrey on all
  nonnegative bid profiles ([HartlineKarlin2007], Exercise 13.4).
* `SingleParameter.empiricalSinglePriceRevenue_dopBadBids_opt`,
  `SingleParameter.dopMechanism_sum_payment_dopBadBids`: for every `k ≥ 2`, `DOP` collects revenue
  `k` against optimal single-price revenue `k²` on `dopBadBids k` (parametric generalization of
  [HartlineKarlin2007], Example 13.23).

## References

* [J. D. Hartline and A. R. Karlin, *Profit Maximization in Mechanism Design*][HartlineKarlin2007]
* [R. B. Myerson, *Optimal Auction Design*][Myerson1981]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.SingleParameter

/-! ### Bulow–Roberts tail identity and continuous Myerson ironing -/

namespace HasValueDensity

variable {μ : Measure ℝ} {f : ℝ → NNReal} {h : ℝ}

/-- The interval `(0, ∞)` has full `μ`-measure whenever `μ` has a value density on `[0, h]`, since
`μ` is concentrated on `[0, h]` and `{0}` is `μ`-null. -/
theorem ae_pos (hμ : HasValueDensity μ f h) : ∀ᵐ v ∂μ, 0 < v := by
  have := hμ.nullSingletonClass
  filter_upwards [hμ.ae_mem, μ.ae_ne 0] with v hv hv0
  exact lt_of_le_of_ne hv.1 hv0.symm

/-- **Bulow–Roberts tail identity.** For a valuation distribution `μ` with density `f` on `[0, h]`
and any threshold `p ≥ 0`, the tail integral of the virtual valuation over `(p, ∞)` equals the
posted-price revenue `p · μ((p, ∞))`: applying the one-dimensional revenue identity to the strict
threshold curve `𝟏_{(p, ∞)}` evaluates the Myerson payment to `p` above `p` and `0` elsewhere. -/
theorem setIntegral_Ioi_virtualValue_eq [IsFiniteMeasure μ] (hμ : HasValueDensity μ f h)
    {p : ℝ} (hp : 0 ≤ p) :
    ∫ z in Ioi p, virtualValue μ f z ∂μ = p * μ.real (Ioi p) := by
  set g : ℝ → ℝ := (Ioi p).indicator fun _ => (1 : ℝ) with hg_def
  have hg_meas : Measurable g := measurable_const.indicator measurableSet_Ioi
  have hg_bound : ∀ v ∈ Icc 0 h, |g v| ≤ 1 := fun v _ => by
    by_cases hv : p < v <;> simp [hg_def, hv]
  have hid := hμ.integral_payment_eq_integral_virtualValue_mul hg_meas hg_bound
  have hLHS : ∀ᵐ v ∂μ, v * g v - (∫ z in (0 : ℝ)..v, g z) =
      (Ioi p).indicator (fun _ => p) v := by
    filter_upwards [hμ.ae_mem] with v hv
    rw [intervalIntegral.integral_of_le hv.1, hg_def, integral_indicator_const _ measurableSet_Ioi,
      measureReal_restrict_apply measurableSet_Ioi, inter_comm, Ioc_inter_Ioi, max_eq_right hp,
      Real.volume_real_Ioc, smul_eq_mul, mul_one]
    by_cases hpv : p < v
    · rw [indicator_of_mem hpv, indicator_of_mem hpv, max_eq_left (sub_nonneg.2 hpv.le)]
      ring
    · rw [indicator_of_notMem hpv, indicator_of_notMem hpv,
        max_eq_right (sub_nonpos.2 (not_lt.1 hpv))]
      ring
  have hRHS : (fun v => virtualValue μ f v * g v) = (Ioi p).indicator (virtualValue μ f) :=
    funext fun v => by by_cases hpv : p < v <;> simp [hg_def, hpv]
  rw [integral_congr_ae hLHS, hRHS, integral_indicator measurableSet_Ioi,
    integral_indicator measurableSet_Ioi, setIntegral_const, smul_eq_mul, mul_comm] at hid
  exact hid.symm

end HasValueDensity

/-- `φBar` is an **ironed virtual valuation** for a distribution `μ` with density `f` on `[0, h]`
([Myerson1981]; [HartlineKarlin2007], §13.2.2, p. 337):

* `φBar` is measurable, `μ`-integrable, and monotone nondecreasing on `(0, h]`;
* its cumulative tail integrals dominate those of `virtualValue μ f` on `[0, h]`, with equality of
  the full integral over `μ`;
* *pooling flatness* (complementary slackness): at every interior valuation `v ∈ (0, h)` where the
  tail integral of `φBar` strictly exceeds that of `virtualValue μ f`, `φBar` is locally constant
  around `v`. -/
structure IsIronedVirtualValue (μ : Measure ℝ) (f : ℝ → NNReal) (h : ℝ) (φBar : ℝ → ℝ) :
    Prop where
  /-- The ironed virtual valuation is measurable. -/
  measurable : Measurable φBar
  /-- The ironed virtual valuation is integrable against `μ`. -/
  integrable : Integrable φBar μ
  /-- The ironed virtual valuation is nondecreasing on `(0, h]`. -/
  monotoneOn : MonotoneOn φBar (Ioc 0 h)
  /-- Cumulative tail dominance on `[0, h]`. -/
  setIntegral_Ioi_le : ∀ v ∈ Icc 0 h,
    ∫ z in Ioi v, virtualValue μ f z ∂μ ≤ ∫ z in Ioi v, φBar z ∂μ
  /-- Total integral preservation across the support. -/
  integral_eq : ∫ z, virtualValue μ f z ∂μ = ∫ z, φBar z ∂μ
  /-- Complementary slackness: wherever cumulative tail dominance is strict on `(0, h)`, `φBar` is
  locally constant. -/
  locallyConstant_of_lt : ∀ v ∈ Ioo 0 h,
    ∫ z in Ioi v, virtualValue μ f z ∂μ < ∫ z in Ioi v, φBar z ∂μ →
      ∃ δ > 0, ∀ z ∈ Ioc 0 h, |z - v| < δ → φBar z = φBar v

/-- Every regular distribution is already ironed: its virtual valuation satisfies
`IsIronedVirtualValue` without modification. -/
theorem IsRegular.isIronedVirtualValue {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → NNReal}
    {h : ℝ} (hreg : IsRegular μ f h) (hμ : HasValueDensity μ f h) :
    IsIronedVirtualValue μ f h (virtualValue μ f) where
  measurable := hμ.measurable_virtualValue
  integrable := hμ.integrable_virtualValue
  monotoneOn := (hreg.strictMonoOn_Ioi hμ).monotoneOn.mono Ioc_subset_Ioi_self
  setIntegral_Ioi_le _ _ := le_rfl
  integral_eq := rfl
  locallyConstant_of_lt _ _ hlt := absurd hlt (lt_irrefl _)

private theorem Iic_inter_Ioc_eq {a b c : ℝ} (hac : a ≤ c) :
    Iic a ∩ Ioc b c = Ioc b a := by
  ext t
  simp only [mem_inter_iff, mem_Iic, mem_Ioc]
  exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hac⟩⟩

namespace IsIronedVirtualValue

section OneDim

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → NNReal} {h : ℝ} {φBar : ℝ → ℝ}

/-- Layer-cake Fubini representation of the ironing gap: for any measurable curve `g` that is
nondecreasing on `[0, h]` (`0 ≤ h`), `∫ φ̄ g dμ − ∫ φ g dμ` equals the integral over thresholds
`t ∈ (g(0), g(h)]` of the cumulative tail slack at the entry point `inf {z ∈ [0, h] | g(z) ≥ t}`. -/
private theorem integral_mul_sub_eq_setIntegral_tail (hμ : HasValueDensity μ f h) (hh : 0 ≤ h)
    (hφ : IsIronedVirtualValue μ f h φBar) {g : ℝ → ℝ} (hg : Measurable g)
    (hgm : MonotoneOn g (Icc 0 h)) :
    ∫ z, φBar z * g z ∂μ - ∫ z, virtualValue μ f z * g z ∂μ =
      ∫ t in Ioc (g 0) (g h),
        (∫ z in Ioi (sInf {z ∈ Icc 0 h | t ≤ g z}), φBar z ∂μ -
          ∫ z in Ioi (sInf {z ∈ Icc 0 h | t ≤ g z}), virtualValue μ f z ∂μ) := by
  have hnull := hμ.nullSingletonClass
  set ψ : ℝ → ℝ := fun z => φBar z - virtualValue μ f z with hψ_def
  have hψ_meas : Measurable ψ := hφ.measurable.sub hμ.measurable_virtualValue
  have hψ_int : Integrable ψ μ := hφ.integrable.sub hμ.integrable_virtualValue
  have hC : ∀ z ∈ Icc 0 h, |g z| ≤ max |g 0| |g h| := fun z hz =>
    abs_le.2 ⟨by linarith [hgm ⟨le_rfl, hh⟩ hz hz.1, neg_abs_le (g 0), le_max_left |g 0| |g h|],
      by linarith [hgm hz ⟨hh, le_rfl⟩ hz.2, le_abs_self (g h), le_max_right |g 0| |g h|]⟩
  have hint_mul : ∀ {ω : ℝ → ℝ}, Measurable ω → Integrable ω μ →
      Integrable (fun z => ω z * g z) μ := fun hωm hωi => by
    refine Integrable.mono' (hωi.norm.mul_const (max |g 0| |g h|))
      (hωm.mul hg).aestronglyMeasurable ?_
    filter_upwards [hμ.ae_mem] with z hz
    rw [norm_mul, Real.norm_eq_abs (g z)]
    exact mul_le_mul_of_nonneg_left (hC z hz) (norm_nonneg _)
  have hint_bar : Integrable (fun z => φBar z * g z) μ := hint_mul hφ.measurable hφ.integrable
  have hint_vv : Integrable (fun z => virtualValue μ f z * g z) μ :=
    hint_mul hμ.measurable_virtualValue hμ.integrable_virtualValue
  set ν : Measure ℝ := volume.restrict (Ioc (g 0) (g h)) with hν_def
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set S : Set (ℝ × ℝ) := {p | p.2 ≤ g p.1} with hS_def
  have hS_meas : MeasurableSet S := measurableSet_le measurable_snd (hg.comp measurable_fst)
  set F : ℝ × ℝ → ℝ := S.indicator (fun p => ψ p.1) with hF_def
  have hF_int : Integrable F (μ.prod ν) := by
    refine Integrable.mono' (g := fun p : ℝ × ℝ => ‖ψ p.1‖ * 1)
      (hψ_int.norm.mul_prod (integrable_const (1 : ℝ)))
      ((hψ_meas.comp measurable_fst).indicator hS_meas).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by
      rw [mul_one, hF_def]
      exact norm_indicator_le_norm_self _ _
  have hswap := integral_integral_swap (μ := μ) (ν := ν) (f := fun z t => F (z, t)) hF_int
  have hL : ∀ᵐ z ∂μ, ∫ t, F (z, t) ∂ν = ψ z * g z - ψ z * g 0 := by
    filter_upwards [hμ.ae_mem] with z hz
    have hlow : g 0 ≤ g z := hgm ⟨le_rfl, hh⟩ hz hz.1
    have hhigh : g z ≤ g h := hgm hz ⟨hh, le_rfl⟩ hz.2
    have hFz : (fun t => F (z, t)) = (Iic (g z)).indicator fun _ => ψ z := rfl
    rw [hFz, hν_def, integral_indicator measurableSet_Iic,
      Measure.restrict_restrict measurableSet_Iic,
      Iic_inter_Ioc_eq hhigh, setIntegral_const, Real.volume_real_Ioc_of_le hlow, smul_eq_mul]
    ring
  have hψg : (fun z => ψ z * g z) = fun z => φBar z * g z - virtualValue μ f z * g z :=
    funext fun _ => sub_mul _ _ _
  have hψ0 : ∫ z, ψ z ∂μ = 0 := by
    rw [hψ_def, integral_sub hφ.integrable hμ.integrable_virtualValue, hφ.integral_eq, sub_self]
  have hLHS_eq : ∫ z, (∫ t, F (z, t) ∂ν) ∂μ =
      ∫ z, φBar z * g z ∂μ - ∫ z, virtualValue μ f z * g z ∂μ := by
    rw [integral_congr_ae hL, integral_sub (hψg ▸ hint_bar.sub hint_vv) (hψ_int.mul_const (g 0)),
      integral_mul_const, hψ0, zero_mul, sub_zero, hψg, integral_sub hint_bar hint_vv]
  rw [← hLHS_eq, hswap, hν_def]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  set U : Set ℝ := {z ∈ Icc 0 h | t ≤ g z} with hU_def
  set vt : ℝ := sInf U with hvt_def
  have hU_ne : U.Nonempty := ⟨h, ⟨hh, le_rfl⟩, ht.2⟩
  have hU_bdd : BddBelow U := ⟨0, fun _ hz => hz.1.1⟩
  have hae_ind : (fun z => F (z, t)) =ᵐ[μ] (Ioi vt).indicator ψ := by
    filter_upwards [hμ.ae_mem, μ.ae_ne vt] with z hz hzne
    rcases lt_or_gt_of_ne hzne with hlt | hgt
    · have hnotU : z ∉ U := fun hzU => absurd (csInf_le hU_bdd hzU) (not_le.2 hlt)
      have hnotle : ¬ t ≤ g z := fun htle => hnotU ⟨hz, htle⟩
      have hnotIoi : z ∉ Ioi vt := not_lt.2 hlt.le
      rw [hF_def, indicator_of_notMem (show (z, t) ∉ S from hnotle), indicator_of_notMem hnotIoi]
    · obtain ⟨w, hwU, hwz⟩ := exists_lt_of_csInf_lt hU_ne hgt
      have htle : t ≤ g z := hwU.2.trans (hgm hwU.1 hz hwz.le)
      rw [hF_def, indicator_of_mem (show (z, t) ∈ S from htle),
        indicator_of_mem (show z ∈ Ioi vt from hgt)]
  rw [integral_congr_ae hae_ind, integral_indicator measurableSet_Ioi, hψ_def,
    integral_sub hφ.integrable.integrableOn hμ.integrable_virtualValue.integrableOn]

omit [IsFiniteMeasure μ] in
private theorem measure_eq_zero_of_lt (hμ : HasValueDensity μ f h) (hh : h < 0) : μ = 0 := by
  rw [hμ.eq_withDensity, Icc_eq_empty (not_le.2 hh), Measure.restrict_empty]
  ext s hs
  simp

/-- **Myerson's continuous ironing inequality** ([Myerson1981]; [HartlineKarlin2007], §13.2.2,
p. 337). For every measurable allocation curve `g` that is nondecreasing on `[0, h]`, expected
virtual surplus is at most expected ironed virtual surplus. -/
theorem integral_virtualValue_mul_le (hμ : HasValueDensity μ f h)
    (hφ : IsIronedVirtualValue μ f h φBar) {g : ℝ → ℝ} (hg : Measurable g)
    (hgm : MonotoneOn g (Icc 0 h)) :
    ∫ z, virtualValue μ f z * g z ∂μ ≤ ∫ z, φBar z * g z ∂μ := by
  rcases lt_or_ge h 0 with hh | hh
  · rw [measure_eq_zero_of_lt hμ hh, integral_zero_measure, integral_zero_measure]
  · rw [← sub_nonneg, integral_mul_sub_eq_setIntegral_tail hμ hh hφ hg hgm]
    refine setIntegral_nonneg measurableSet_Ioc fun t ht => ?_
    have hU_ne : ({z ∈ Icc 0 h | t ≤ g z}).Nonempty := ⟨h, ⟨hh, le_rfl⟩, ht.2⟩
    have hU_bdd : BddBelow {z ∈ Icc 0 h | t ≤ g z} := ⟨0, fun _ hz => hz.1.1⟩
    have hvt_mem : sInf {z ∈ Icc 0 h | t ≤ g z} ∈ Icc 0 h :=
      ⟨le_csInf hU_ne fun _ hz => hz.1.1, csInf_le hU_bdd ⟨⟨hh, le_rfl⟩, ht.2⟩⟩
    exact sub_nonneg.2 (hφ.setIntegral_Ioi_le _ hvt_mem)

/-- **Myerson's pooling equality (complementary slackness).** If `g` is measurable, nondecreasing
on `[0, h]`, and constant across every flat of `φBar` on `(0, h]` (i.e. `φBar z₁ = φBar z₂` implies
`g z₁ = g z₂` for `z₁, z₂ ∈ (0, h]`), then expected virtual surplus equals expected ironed virtual
surplus. -/
theorem integral_virtualValue_mul_eq (hμ : HasValueDensity μ f h)
    (hφ : IsIronedVirtualValue μ f h φBar) {g : ℝ → ℝ} (hg : Measurable g)
    (hgm : MonotoneOn g (Icc 0 h))
    (hpool : ∀ z₁ ∈ Ioc 0 h, ∀ z₂ ∈ Ioc 0 h, φBar z₁ = φBar z₂ → g z₁ = g z₂) :
    ∫ z, virtualValue μ f z * g z ∂μ = ∫ z, φBar z * g z ∂μ := by
  rcases lt_or_ge h 0 with hh | hh
  · rw [measure_eq_zero_of_lt hμ hh, integral_zero_measure, integral_zero_measure]
  · symm
    rw [← sub_eq_zero, integral_mul_sub_eq_setIntegral_tail hμ hh hφ hg hgm]
    refine setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    set U : Set ℝ := {z ∈ Icc 0 h | t ≤ g z}
    set vt : ℝ := sInf U
    have hU_ne : U.Nonempty := ⟨h, ⟨hh, le_rfl⟩, ht.2⟩
    have hU_bdd : BddBelow U := ⟨0, fun _ hz => hz.1.1⟩
    have hvt0 : 0 ≤ vt := le_csInf hU_ne fun _ hz => hz.1.1
    have hvth : vt ≤ h := csInf_le hU_bdd ⟨⟨hh, le_rfl⟩, ht.2⟩
    rcases hvt0.eq_or_lt with hvt0_eq | hvt_pos
    · rw [← hvt0_eq, Measure.restrict_eq_self_of_ae_mem (s := Ioi 0) hμ.ae_pos, hφ.integral_eq,
        sub_self]
    · rcases hvth.eq_or_lt with hvth_eq | hvt_lt
      · rw [hvth_eq]
        have h0 : μ.restrict (Ioi h) = 0 :=
          Measure.restrict_eq_zero.2 (hμ.measure_Ioi_eq_zero le_rfl)
        rw [h0, integral_zero_measure, integral_zero_measure, sub_self]
      · have hle := hφ.setIntegral_Ioi_le vt ⟨hvt0, hvth⟩
        rcases hle.eq_or_lt with heq | hlt
        · linarith
        · exfalso
          obtain ⟨δ, hδ, hconst⟩ := hφ.locallyConstant_of_lt vt ⟨hvt_pos, hvt_lt⟩ hlt
          set ε : ℝ := min (δ / 2) (vt / 2)
          have hε_pos : 0 < ε := lt_min (half_pos hδ) (half_pos hvt_pos)
          have hzl_mem : vt - ε ∈ Ioc 0 h :=
            ⟨by linarith [min_le_right (δ / 2) (vt / 2)], by linarith⟩
          have hzl_dist : |(vt - ε) - vt| < δ := by
            rw [show (vt - ε) - vt = -ε by ring, abs_neg, abs_of_pos hε_pos]
            linarith [min_le_left (δ / 2) (vt / 2)]
          obtain ⟨zr, hzrU, hzr_lt⟩ :=
            exists_lt_of_csInf_lt hU_ne (show vt < vt + δ / 2 by linarith)
          have hvt_le_zr : vt ≤ zr := csInf_le hU_bdd hzrU
          have hzr_mem : zr ∈ Ioc 0 h := ⟨hvt_pos.trans_le hvt_le_zr, hzrU.1.2⟩
          have hzr_dist : |zr - vt| < δ := by
            rw [abs_of_nonneg (sub_nonneg.2 hvt_le_zr)]
            linarith
          have hφ_eq : φBar (vt - ε) = φBar zr :=
            (hconst (vt - ε) hzl_mem hzl_dist).trans (hconst zr hzr_mem hzr_dist).symm
          have hgzl : t ≤ g (vt - ε) :=
            hzrU.2.trans_eq (hpool (vt - ε) hzl_mem zr hzr_mem hφ_eq).symm
          have hle_csInf : vt ≤ vt - ε := csInf_le hU_bdd ⟨⟨hzl_mem.1.le, hzl_mem.2⟩, hgzl⟩
          linarith

end OneDim

end IsIronedVirtualValue

/-! ### Multi-bidder optimal irregular auctions -/

section IrregularAuction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : ι → Measure ℝ}
  [∀ i, IsProbabilityMeasure (μ i)] {f : ι → ℝ → NNReal} {h : ι → ℝ} {φBar : ι → ℝ → ℝ}

omit [DecidableEq ι] in
theorem integrable_ironed_mul (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hφ : ∀ i, IsIronedVirtualValue (μ i) (f i) (h i) (φBar i)) (i : ι)
    {x : (ι → ℝ) → ι → ℝ} {B : ℝ} (hx : Measurable fun v => x v i)
    (hB : ∀ v, 0 ≤ v → |x v i| ≤ B) :
    Integrable (fun v => φBar i (v i) * x v i) (Measure.pi μ) := by
  have hφi : Integrable (fun v : ι → ℝ => φBar i (v i)) (Measure.pi μ) :=
    integrable_comp_eval (hφ i).integrable
  refine Integrable.mono' (hφi.norm.mul_const B)
    (((hφ i).measurable.comp (measurable_pi_apply i)).mul hx).aestronglyMeasurable ?_
  filter_upwards [ae_nonneg hμ] with v hv
  rw [norm_mul, Real.norm_eq_abs (x v i)]
  exact mul_le_mul_of_nonneg_left (hB v hv) (norm_nonneg _)

/-- **Expected revenue of any DSIC, IR mechanism is at most expected ironed virtual welfare.** -/
theorem Mechanism.IsDSIC.integral_sum_payment_le_ironed {M : Mechanism ι} (hM : M.IsDSIC)
    (hIR : M.IsIR) (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hφ : ∀ i, IsIronedVirtualValue (μ i) (f i) (h i) (φBar i)) {B : ℝ}
    (hx : ∀ i, Measurable fun v => M.allocation v i)
    (hB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ B) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤
      ∫ v, ∑ i, φBar i (v i) * M.allocation v i ∂Measure.pi μ := by
  refine (hM.integral_sum_payment_le hIR hμ hx hB).trans ?_
  have hint_vv (i : ι) := integrable_virtualValue_mul hμ i (hx i) fun v hv => hB v hv i
  have hint_ir (i : ι) := integrable_ironed_mul hμ hφ i (hx i) fun v hv => hB v hv i
  rw [integral_finsetSum _ fun i _ => hint_vv i, integral_finsetSum _ fun i _ => hint_ir i]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← integral_integral_update μ (hint_vv i) i, ← integral_integral_update μ (hint_ir i) i]
  refine integral_mono_ae
    (integrable_integral_update_measure μ i (μ i)
      (by simpa only [Function.update_eq_self] using hint_vv i))
    (integrable_integral_update_measure μ i (μ i)
      (by simpa only [Function.update_eq_self] using hint_ir i)) ?_
  filter_upwards [ae_nonneg hμ] with v hv
  simp only [Function.update_self]
  exact (hφ i).integral_virtualValue_mul_le (hμ i)
    (g := fun z => M.allocation (Function.update v i z) i)
    ((hx i).comp (measurable_update v))
    ((hM.isMonotone i v hv).mono fun _ hz => hz.1)

/-- **Expected Myerson revenue of a monotone pooling-invariant rule equals its expected ironed
virtual welfare.** -/
theorem integral_sum_myersonPayment_eq_ironed (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hφ : ∀ i, IsIronedVirtualValue (μ i) (f i) (h i) (φBar i)) {x : (ι → ℝ) → ι → ℝ} {B : ℝ}
    (hmono : IsMonotone x) (hx : ∀ i, Measurable fun v => x v i)
    (hB : ∀ v, 0 ≤ v → ∀ i, |x v i| ≤ B)
    (hpool : ∀ i v, 0 ≤ v → ∀ z₁ ∈ Ioc 0 (h i), ∀ z₂ ∈ Ioc 0 (h i),
      φBar i z₁ = φBar i z₂ → x (Function.update v i z₁) i = x (Function.update v i z₂) i) :
    ∫ v, ∑ i, myersonPayment x v i ∂Measure.pi μ =
      ∫ v, ∑ i, φBar i (v i) * x v i ∂Measure.pi μ := by
  have hint_vv (i : ι) := integrable_virtualValue_mul hμ i (hx i) fun v hv => hB v hv i
  have hint_ir (i : ι) := integrable_ironed_mul hμ hφ i (hx i) fun v hv => hB v hv i
  rw [integral_sum_myersonPayment_eq hμ hx hB,
    integral_finsetSum _ fun i _ => hint_vv i, integral_finsetSum _ fun i _ => hint_ir i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← integral_integral_update μ (hint_vv i) i, ← integral_integral_update μ (hint_ir i) i]
  refine integral_congr_ae ?_
  filter_upwards [ae_nonneg hμ] with v hv
  simp only [Function.update_self]
  exact (hφ i).integral_virtualValue_mul_eq (hμ i)
    (g := fun z => x (Function.update v i z) i)
    ((hx i).comp (measurable_update v))
    ((hmono i v hv).mono fun _ hz => hz.1) (hpool i v hv)

/-- Conditional optimality step (not the unconditional irregular-auction existence theorem) of
[Myerson1981] and [HartlineKarlin2007], §13.2.2, p. 337, taking caller-supplied ironed virtual
valuations `φBarᵢ` (constructive convex-hull existence of `IsIronedVirtualValue` from arbitrary
`HasValueDensity` is tracked in #7789).

Given independent (not necessarily regular or identical) valuation distributions `(μᵢ, fᵢ, hᵢ)` and
ironed virtual valuations `φBarᵢ`, if `x` is a monotone, measurable allocation rule that maximizes
ironed virtual welfare `∑ᵢ φBarᵢ(vᵢ) yᵢ` over `X ⊆ [0, 1]^ι` and is constant across every flat of
`φBarᵢ` on `(0, hᵢ]`, then `myerson x` achieves at least the expected revenue of every DSIC,
individually rational mechanism with allocations in `X`. -/
theorem integral_sum_payment_le_ironed_myerson_of_isIronedVirtualValue
    (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hφ : ∀ i, IsIronedVirtualValue (μ i) (f i) (h i) (φBar i))
    {X : Set (ι → ℝ)} (hX : ∀ y ∈ X, ∀ i, 0 ≤ y i ∧ y i ≤ 1) {x : (ι → ℝ) → ι → ℝ}
    (hx : IsVirtualWelfareMaximizing φBar X x) (hmono : IsMonotone x)
    (hxm : ∀ i, Measurable fun v => x v i)
    (hpool : ∀ i v, 0 ≤ v → ∀ z₁ ∈ Ioc 0 (h i), ∀ z₂ ∈ Ioc 0 (h i),
      φBar i z₁ = φBar i z₂ → x (Function.update v i z₁) i = x (Function.update v i z₂) i)
    {M : Mechanism ι} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ X) (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤ ∫ v, ∑ i, (myerson x).payment v i ∂Measure.pi μ := by
  have hbound : ∀ y ∈ X, ∀ i, |y i| ≤ 1 := fun y hy i => by
    rw [abs_of_nonneg (hX y hy i).1]
    exact (hX y hy i).2
  have hMB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ 1 := fun v hv => hbound _ (hMX v hv)
  have hxB : ∀ v, 0 ≤ v → ∀ i, |x v i| ≤ 1 := fun v hv => hbound _ (hx v hv).1
  refine (hM.integral_sum_payment_le_ironed hIR hμ hφ hMm hMB).trans ?_
  change _ ≤ ∫ v, ∑ i, myersonPayment x v i ∂Measure.pi μ
  rw [integral_sum_myersonPayment_eq_ironed hμ hφ hmono hxm hxB hpool]
  refine integral_mono_ae
    (integrable_finsetSum _ fun i _ => integrable_ironed_mul hμ hφ i (hMm i) fun v hv => hMB v hv i)
    (integrable_finsetSum _ fun i _ => integrable_ironed_mul hμ hφ i (hxm i) fun v hv => hxB v hv i)
    ?_
  filter_upwards [ae_nonneg hμ] with v hv
  exact (hx v hv).2 _ (hMX v hv)

end IrregularAuction

/-- Composing a real-weight welfare maximizer `xHat` with ironed virtual bids `i ↦ φBar i (b i)`
produces an allocation rule that depends on each bid solely through its ironed virtual value. -/
@[expose] def ironedAllocation {ι : Type*} (φBar : ι → ℝ → ℝ) (xHat : (ι → ℝ) → ι → ℝ)
    (b : ι → ℝ) : ι → ℝ :=
  xHat fun i => φBar i (b i)

theorem isVirtualWelfareMaximizing_ironedAllocation {ι : Type*} [Fintype ι] {φBar : ι → ℝ → ℝ}
    {X : Set (ι → ℝ)} {xHat : (ι → ℝ) → ι → ℝ}
    (hxHat : ∀ w : ι → ℝ, xHat w ∈ X ∧ ∀ y ∈ X, ∑ i, w i * y i ≤ ∑ i, w i * xHat w i) :
    IsVirtualWelfareMaximizing φBar X (ironedAllocation φBar xHat) :=
  fun b _ => hxHat fun i => φBar i (b i)

/-- **Ironed virtual-welfare maximization is monotone** whenever `xHat` maximizes `∑ᵢ wᵢ yᵢ` over
all real weight vectors `w` and each `φBarᵢ` is nondecreasing on `[0, ∞)`: equal virtual bids pass
identical inputs to `xHat`, while strictly higher virtual bids force a weakly higher coordinate by
the standard two-profile optimality comparison. -/
theorem isMonotone_ironedAllocation {ι : Type*} [Fintype ι] [DecidableEq ι] {φBar : ι → ℝ → ℝ}
    {X : Set (ι → ℝ)} {xHat : (ι → ℝ) → ι → ℝ}
    (hxHat : ∀ w : ι → ℝ, xHat w ∈ X ∧ ∀ y ∈ X, ∑ i, w i * y i ≤ ∑ i, w i * xHat w i)
    (hφ : ∀ i, MonotoneOn (φBar i) (Ici 0)) :
    IsMonotone (ironedAllocation φBar xHat) := by
  intro i b _ z hz z' hz' hzz'
  change xHat (fun j => φBar j (Function.update b i z j)) i ≤
    xHat (fun j => φBar j (Function.update b i z' j)) i
  rcases (hφ i hz hz' hzz').eq_or_lt with heq | hlt
  · refine le_of_eq (congrArg (xHat · i) (funext fun j => ?_))
    rcases eq_or_ne j i with rfl | hj
    · simp only [Function.update_self, heq]
    · simp only [Function.update_of_ne hj]
  · set w := fun j => φBar j (Function.update b i z j)
    set w' := fun j => φBar j (Function.update b i z' j)
    have hw_eq : w' = Function.update w i (φBar i z') :=
      funext fun j => by rcases eq_or_ne j i with rfl | hj <;> simp [w, w', *]
    have key : ∀ y : ι → ℝ, ∑ j, w' j * y j = (φBar i z' - φBar i z) * y i + ∑ j, w j * y j :=
      fun y => by
        rw [hw_eq, Finset.sum_apply_update_of_mem (Finset.mem_univ i) (fun j c => c * y j),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        simp only [w, Function.update_self]
        ring
    have h1 := (hxHat w).2 (xHat w') (hxHat w').1
    have h2 := (hxHat w').2 (xHat w) (hxHat w).1
    rw [key, key] at h2
    nlinarith

theorem ironedAllocation_eq_of_eq {ι : Type*} [DecidableEq ι] (φBar : ι → ℝ → ℝ)
    (xHat : (ι → ℝ) → ι → ℝ) (b : ι → ℝ) (i : ι) {z₁ z₂ : ℝ} (h : φBar i z₁ = φBar i z₂) :
    ironedAllocation φBar xHat (Function.update b i z₁) =
      ironedAllocation φBar xHat (Function.update b i z₂) := by
  refine congrArg xHat (funext fun j => ?_)
  rcases eq_or_ne j i with rfl | hj <;> simp [*]

namespace Vickrey

section AsymmetricIroned

variable {ι : Type*} [LinearOrder ι]

open Classical in
/-- Canonical single-item real-weight welfare maximizer: awards the item to the smallest-index
bidder achieving the highest nonnegative virtual weight, and withholds the item if all virtual
weights are negative. -/
@[expose] noncomputable def virtualWinnerAllocation (w : ι → ℝ) (i : ι) : ℝ :=
  if Wins w i ∧ 0 ≤ w i then 1 else 0

/-- Single-item ironed allocation rule for (possibly non-identical, irregular) ironed virtual
valuations `φBar`: evaluates `virtualWinnerAllocation` on the ironed virtual bids
`j ↦ φBar j (b j)`. -/
@[expose] noncomputable def ironedAllocation (φBar : ι → ℝ → ℝ) (b : ι → ℝ) : ι → ℝ :=
  SingleParameter.ironedAllocation φBar virtualWinnerAllocation b

theorem virtualWinnerAllocation_binary (w : ι → ℝ) (i : ι) :
    virtualWinnerAllocation w i = 0 ∨ virtualWinnerAllocation w i = 1 := by
  unfold virtualWinnerAllocation
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

open Classical in
theorem measurable_ironedAllocation [Countable ι] {φBar : ι → ℝ → ℝ}
    (hφ : ∀ j, Measurable (φBar j)) (i : ι) :
    Measurable fun b : ι → ℝ => ironedAllocation φBar b i := by
  have hcomp : Measurable fun b : ι → ℝ => fun j => φBar j (b j) :=
    Measurable.of_eval fun j => (hφ j).comp (measurable_pi_apply j)
  have hW : MeasurableSet {b : ι → ℝ | Wins (fun j => φBar j (b j)) i} :=
    hcomp (measurableSet_wins i)
  have hN : MeasurableSet {b : ι → ℝ | 0 ≤ φBar i (b i)} :=
    measurableSet_le measurable_const ((hφ i).comp (measurable_pi_apply i))
  change Measurable fun b : ι → ℝ =>
    if Wins (fun j => φBar j (b j)) i ∧ 0 ≤ φBar i (b i) then (1 : ℝ) else 0
  exact Measurable.ite (hW.inter hN) measurable_const measurable_const

private theorem virtualWinnerAllocation_mem_and_max [Fintype ι] (w : ι → ℝ) :
    virtualWinnerAllocation w ∈ singleItemFeasible ∧
      ∀ y ∈ singleItemFeasible, ∑ i, w i * y i ≤ ∑ i, w i * virtualWinnerAllocation w i := by
  have hmem : virtualWinnerAllocation w ∈ singleItemFeasible := by
    refine ⟨virtualWinnerAllocation_binary w, ?_⟩
    have hle : ∀ i, virtualWinnerAllocation w i ≤ allocation w i := fun i => by
      unfold virtualWinnerAllocation allocation
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd h1.1 h2
      · exact zero_le_one
      · exact le_rfl
    exact (Finset.sum_le_sum fun i _ => hle i).trans (allocation_mem_singleItemFeasible w).2
  refine ⟨hmem, fun y hy => ?_⟩
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, le_refl]
  obtain ⟨k, hk⟩ := exists_wins w
  have hy0 : ∀ j, 0 ≤ y j := fun j => by
    rcases hy.1 j with h | h <;> rw [h]
    exact zero_le_one
  have hle_max : ∀ j, w j ≤ max 0 (w k) := fun j => by
    by_cases hj : j = k
    · subst hj
      exact le_max_right _ _
    · exact (hk j hj).1.trans (le_max_right _ _)
  have hL : ∑ j, w j * y j ≤ max 0 (w k) :=
    calc ∑ j, w j * y j ≤ ∑ j, max 0 (w k) * y j :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hle_max j) (hy0 j)
      _ = max 0 (w k) * ∑ j, y j := by rw [Finset.mul_sum]
      _ ≤ max 0 (w k) * 1 := mul_le_mul_of_nonneg_left hy.2 (le_max_left _ _)
      _ = max 0 (w k) := mul_one _
  have hoff : ∀ j, j ≠ k → virtualWinnerAllocation w j = 0 := fun j hj => by
    unfold virtualWinnerAllocation
    split_ifs with h
    · exact absurd (h.1.unique hk) hj
    · rfl
  have hR : ∑ i, w i * virtualWinnerAllocation w i = max 0 (w k) := by
    rw [Fintype.sum_eq_single k (fun j hj => by rw [hoff j hj, mul_zero])]
    unfold virtualWinnerAllocation
    split_ifs with h
    · rw [mul_one, max_eq_right h.2]
    · have hwk : w k ≤ 0 := le_of_not_ge fun h0 => h ⟨hk, h0⟩
      rw [mul_zero, max_eq_left hwk]
  rw [hR]
  exact hL

theorem ironedAllocation_mem_singleItemFeasible [Fintype ι] (φBar : ι → ℝ → ℝ) (b : ι → ℝ) :
    ironedAllocation φBar b ∈ singleItemFeasible :=
  (virtualWinnerAllocation_mem_and_max _).1

theorem isMonotone_ironedAllocation [Finite ι] {φBar : ι → ℝ → ℝ}
    (hmono : ∀ i, MonotoneOn (φBar i) (Ici 0)) :
    IsMonotone (ironedAllocation φBar) := by
  cases nonempty_fintype ι
  exact SingleParameter.isMonotone_ironedAllocation virtualWinnerAllocation_mem_and_max hmono

/-- Single-item specialization of the conditional optimality step of [Myerson1981] (not the
unconditional irregular single-item theorem; convex-hull existence of `IsIronedVirtualValue` is
tracked in #7789): given independent distributions `(μᵢ, fᵢ, hᵢ)` and caller-supplied ironed
virtual valuations `φBarᵢ` that are nondecreasing on `[0, ∞)`,
`myerson (Vickrey.ironedAllocation φBar)` achieves at least the expected revenue of every DSIC, IR
single-item mechanism. -/
theorem integral_sum_payment_le_ironed_of_isIronedVirtualValue [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)] {f : ι → ℝ → NNReal} {h : ι → ℝ} {φBar : ι → ℝ → ℝ}
    (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hφ : ∀ i, IsIronedVirtualValue (μ i) (f i) (h i) (φBar i))
    (hmono : ∀ i, MonotoneOn (φBar i) (Ici 0)) {M : Mechanism ι}
    (hM : M.IsDSIC) (hIR : M.IsIR) (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ singleItemFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤
      ∫ v, ∑ i, (myerson (ironedAllocation φBar)).payment v i ∂Measure.pi μ :=
  integral_sum_payment_le_ironed_myerson_of_isIronedVirtualValue hμ hφ
    (fun y hy i => by rcases hy.1 i with h0 | h1 <;> [rw [h0]; rw [h1]] <;> norm_num)
    (isVirtualWelfareMaximizing_ironedAllocation virtualWinnerAllocation_mem_and_max)
    (isMonotone_ironedAllocation hmono)
    (fun i => measurable_ironedAllocation (fun j => (hφ j).measurable) i)
    (fun i v _ z₁ _ z₂ _ heq =>
      congrFun (ironedAllocation_eq_of_eq φBar virtualWinnerAllocation v i heq) i)
    hM hIR hMX hMm

end AsymmetricIroned

end Vickrey

/-! ### Necessity of monotone virtual valuations (Lemma 13.12) -/

/-- Feasible allocations in a single-parameter digital goods auction ([HartlineKarlin2007],
Example 13.2, p. 332): unlimited supply with zero marginal cost, so each bidder independently
receives an allocation in `[0, 1]`. -/
@[expose] def digitalGoodsFeasible {ι : Type*} : Set (ι → ℝ) :=
  {y | ∀ i, 0 ≤ y i ∧ y i ≤ 1}

/-- **Truthfulness of virtual-surplus maximization across seller-cost environments**
([HartlineKarlin2007], Lemma 13.12, p. 337).

For virtual valuations `φ : ι → ℝ → ℝ` on a nonempty bidder set, maximizing virtual surplus
`∑ᵢ φᵢ(bᵢ) yᵢ − c₀ ∑ᵢ yᵢ` over `digitalGoodsFeasible` (`[0, 1]^ι`) yields a monotone allocation
rule for every per-unit seller cost `c₀ ∈ ℝ` (and arbitrary tie-breaking, or even for some
tie-breaking per `c₀`) if and only if every `φᵢ` is monotone nondecreasing on `[0, ∞)`. -/
theorem isMonotone_virtualSurplusMaximizer_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → ℝ → ℝ) :
    (∀ c₀ : ℝ, ∃ x : (ι → ℝ) → ι → ℝ,
      IsVirtualWelfareMaximizing (fun i v => φ i v - c₀) digitalGoodsFeasible x ∧
        IsMonotone x) ↔
      ∀ i, MonotoneOn (φ i) (Ici 0) := by
  constructor
  · intro h i v₁ hv₁ v₂ hv₂ hv12
    by_contra hcon
    have hlt : φ i v₂ < φ i v₁ := lt_of_not_ge hcon
    set c₀ : ℝ := (φ i v₁ + φ i v₂) / 2
    obtain ⟨x, hx_max, hx_mono⟩ := h c₀
    set b₁ : ι → ℝ := Function.update 0 i v₁
    set b₂ : ι → ℝ := Function.update 0 i v₂
    have hb₁ : 0 ≤ b₁ := update_nonneg le_rfl i hv₁
    have hb₂ : 0 ≤ b₂ := update_nonneg le_rfl i hv₂
    obtain ⟨hx1_mem, hx1_opt⟩ := hx_max b₁ hb₁
    obtain ⟨hx2_mem, hx2_opt⟩ := hx_max b₂ hb₂
    have hy1_mem : Function.update (x b₁) i 1 ∈ digitalGoodsFeasible := fun j => by
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact ⟨zero_le_one, le_rfl⟩
      · rw [Function.update_of_ne hj]; exact hx1_mem j
    have hy2_mem : Function.update (x b₂) i 0 ∈ digitalGoodsFeasible := fun j => by
      by_cases hj : j = i
      · subst hj; rw [Function.update_self]; exact ⟨le_rfl, zero_le_one⟩
      · rw [Function.update_of_ne hj]; exact hx2_mem j
    have hopt1 := hx1_opt _ hy1_mem
    have hopt2 := hx2_opt _ hy2_mem
    rw [Finset.sum_apply_update_of_mem (Finset.mem_univ i)
        (fun j val => (φ j (b₁ j) - c₀) * val),
       ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hopt1
    rw [Finset.sum_apply_update_of_mem (Finset.mem_univ i)
        (fun j val => (φ j (b₂ j) - c₀) * val),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hopt2
    simp only [b₁, b₂, c₀, Function.update_self] at hopt1 hopt2
    have hxi1 : x b₁ i = 1 := by
      have := (hx1_mem i).2
      nlinarith
    have hxi2 : x b₂ i = 0 := by
      have := (hx2_mem i).1
      nlinarith
    have hmono := hx_mono i 0 le_rfl hv₁ hv₂ hv12
    change x b₁ i ≤ x b₂ i at hmono
    linarith
  · intro hφ c₀
    let xHat : (ι → ℝ) → ι → ℝ := fun w i => if 0 ≤ w i then 1 else 0
    have hxHat : ∀ w : ι → ℝ, xHat w ∈ digitalGoodsFeasible ∧
        ∀ y ∈ digitalGoodsFeasible, ∑ i, w i * y i ≤ ∑ i, w i * xHat w i := by
      intro w
      refine ⟨fun i => by simp only [xHat]; split_ifs <;> norm_num, fun y hy => ?_⟩
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [xHat]
      split_ifs with hw
      · rw [mul_one]
        exact mul_le_of_le_one_right hw (hy i).2
      · rw [mul_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hw) (hy i).1
    exact ⟨ironedAllocation (fun i v => φ i v - c₀) xHat,
      isVirtualWelfareMaximizing_ironedAllocation hxHat,
      isMonotone_ironedAllocation hxHat fun i _ ha _ hb hab => sub_le_sub_right (hφ i ha hb hab) c₀⟩

private theorem zero_mem_singleItemFeasible {ι : Type*} [Fintype ι] :
    (0 : ι → ℝ) ∈ Vickrey.singleItemFeasible :=
  ⟨fun _ => Or.inl rfl, by simp only [Pi.zero_apply, Finset.sum_const_zero, zero_le_one]⟩

/-- In a zero-cost single-item auction (`singleItemFeasible`), if bidder `i` has `0 ≤ v₁ < v₂` with
`φᵢ(v₂) < φᵢ(v₁)` and `0 < φᵢ(v₁)`, and there is a nonnegative opponent profile `b` whose maximum
other virtual valuation lies strictly between `φᵢ(v₂)` and `φᵢ(v₁)` (or all opponents have
nonpositive virtual valuations while `φᵢ(v₂) < 0`), then **no** virtual-welfare maximizer is
implementable (`¬ IsImplementable x`). -/
theorem not_isImplementable_of_isVirtualWelfareMaximizing {ι : Type*} [Fintype ι] [DecidableEq ι]
    {φ : ι → ℝ → ℝ} {x : (ι → ℝ) → ι → ℝ}
    (hx : IsVirtualWelfareMaximizing φ Vickrey.singleItemFeasible x)
    {i : ι} {b : ι → ℝ} (hb : 0 ≤ b) {v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv12 : v₁ < v₂)
    (hpos : 0 < φ i v₁) (hother_le : ∀ j, j ≠ i → φ j (b j) < φ i v₁)
    (hbeat : φ i v₂ < 0 ∨ ∃ j, j ≠ i ∧ 0 < φ j (b j) ∧ φ i v₂ < φ j (b j)) :
    ¬ IsImplementable x := by
  intro himp
  have hmono := himp.isMonotone i b hb hv₁ (hv₁.trans hv12.le) hv12.le
  set b₁ := Function.update b i v₁
  set b₂ := Function.update b i v₂
  obtain ⟨hx1_mem, hx1_opt⟩ := hx b₁ (update_nonneg hb i hv₁)
  obtain ⟨hx2_mem, hx2_opt⟩ := hx b₂ (update_nonneg hb i (hv₁.trans hv12.le))
  have hunit : ∀ q : ι, Function.update (0 : ι → ℝ) q 1 ∈ Vickrey.singleItemFeasible := fun q => by
    refine ⟨fun k => ?_, ?_⟩
    · by_cases hkq : k = q
      · subst hkq; exact Or.inr (by simp only [Function.update_self])
      · exact Or.inl (by simp only [Function.update_of_ne hkq, Pi.zero_apply])
    · rw [Fintype.sum_eq_single q
          (fun k hk => by simp only [Function.update_of_ne hk, Pi.zero_apply])]
      simp only [Function.update_self, le_refl]
  have hx1_eq : x b₁ i = 1 := by
    rcases hx1_mem.1 i with h0 | h1
    · exfalso
      have hsum_le : ∑ j, φ j (b₁ j) * x b₁ j ≤ max 0 (Finset.fold max (φ i v₁ - 1)
          (fun j => φ j (b j)) (Finset.univ.erase i)) := by
        have hall : ∀ j, φ j (b₁ j) * x b₁ j ≤
            max 0 (Finset.fold max (φ i v₁ - 1) (fun k => φ k (b k)) (Finset.univ.erase i)) *
              x b₁ j := fun j => by
          rcases hx1_mem.1 j with hj0 | hj1
          · rw [hj0, mul_zero, mul_zero]
          · by_cases hji : j = i
            · subst hji; rw [h0] at hj1; norm_num at hj1
            · rw [hj1, mul_one, mul_one]
              have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hji, Finset.mem_univ j⟩
              have hfold : φ j (b j) ≤ Finset.fold max (φ i v₁ - 1) (fun k => φ k (b k))
                  (Finset.univ.erase i) :=
                (Finset.le_fold_max _).2 (Or.inr ⟨j, hmem, le_rfl⟩)
              simpa only [b₁, Function.update_of_ne hji] using hfold.trans (le_max_right _ _)
        calc ∑ j, φ j (b₁ j) * x b₁ j ≤ _ := Finset.sum_le_sum fun j _ => hall j
          _ = _ * ∑ j, x b₁ j := (Finset.mul_sum _ _ _).symm
          _ ≤ _ * 1 := mul_le_mul_of_nonneg_left hx1_mem.2 (le_max_left _ _)
          _ = _ := mul_one _
      have hstrict : max 0 (Finset.fold max (φ i v₁ - 1) (fun j => φ j (b j))
          (Finset.univ.erase i)) < φ i v₁ := by
        refine max_lt hpos ?_
        rw [Finset.fold_max_lt]
        exact ⟨by linarith, fun j hj => hother_le j (Finset.ne_of_mem_erase hj)⟩
      have hcmp := hx1_opt _ (hunit i)
      rw [Fintype.sum_eq_single i
          (fun j hj => by simp only [Function.update_of_ne hj, Pi.zero_apply, mul_zero])] at hcmp
      simp only [b₁, Function.update_self, mul_one] at hcmp
      linarith
    · exact h1
  have hx2_eq : x b₂ i = 0 := by
    rcases hx2_mem.1 i with h0 | h1
    · exact h0
    · exfalso
      have hall0 (j : ι) (hj : j ≠ i) : x b₂ j = 0 :=
        (hx2_mem.1 j).resolve_right fun hj1 => by
          have hsub : ({i, j} : Finset ι).sum (x b₂) ≤ ∑ k, x b₂ k :=
            Finset.sum_le_univ_sum_of_nonneg fun k => by rcases hx2_mem.1 k with h | h <;> simp [h]
          rw [Finset.sum_pair hj.symm, h1, hj1] at hsub
          linarith [hx2_mem.2]
      have hsum2 : ∑ k, φ k (b₂ k) * x b₂ k = φ i v₂ := by
        rw [Fintype.sum_eq_single i (fun k hk => by rw [hall0 k hk, mul_zero]), h1, mul_one]
        simp only [b₂, Function.update_self]
      rcases hbeat with hneg | ⟨j, hji, _, hlt_j⟩
      · have hcmp := hx2_opt 0 zero_mem_singleItemFeasible
        simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, hsum2] at hcmp
        linarith
      · have hcmp := hx2_opt _ (hunit j)
        rw [Fintype.sum_eq_single j
            (fun k hk => by simp only [Function.update_of_ne hk, Pi.zero_apply, mul_zero]),
          hsum2] at hcmp
        simp only [b₂, Function.update_of_ne hji, Function.update_self, mul_one] at hcmp
        linarith
  change x b₁ i ≤ x b₂ i at hmono
  linarith

/-- For at least two i.i.d. bidders with a continuous virtual valuation `φ` on `[v₂, h]` satisfying
`φ(0) ≤ 0` and `φ(v₁) < φ(h)` (which holds automatically when `φ(v₁) ≤ v₁ < v₂ ≤ h = φ(h)`), any
non-monotonicity `0 ≤ v₁ < v₂ ≤ h` with `φ(v₂) < φ(v₁)` and `0 < φ(v₁)` makes **every** single-item
virtual-welfare maximizer non-implementable ([HartlineKarlin2007], Lemma 13.12, p. 337). -/
theorem not_isImplementable_iid_of_virtualValue_gt {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : 2 ≤ Fintype.card ι) {φ : ℝ → ℝ} {h v₁ v₂ : ℝ} (hv₁ : 0 ≤ v₁) (hv12 : v₁ < v₂)
    (hv₂h : v₂ ≤ h) (hcont : ContinuousOn φ (Icc v₂ h)) (hφ0 : φ 0 ≤ 0) (hφh : φ v₁ ≤ φ h)
    (hlt : φ v₂ < φ v₁) (hpos : 0 < φ v₁) {x : (ι → ℝ) → ι → ℝ}
    (hx : IsVirtualWelfareMaximizing (fun _ => φ) Vickrey.singleItemFeasible x) :
    ¬ IsImplementable x := by
  have h1lt : 1 < Fintype.card ι := lt_of_lt_of_le Nat.one_lt_two hcard
  obtain ⟨i, j, hij⟩ := Fintype.exists_pair_of_one_lt_card h1lt
  set target : ℝ := (max 0 (φ v₂) + φ v₁) / 2
  have htarget_mem : target ∈ Icc (φ v₂) (φ h) := by
    refine ⟨?_, ?_⟩ <;> dsimp only [target]
    · linarith [le_max_right 0 (φ v₂)]
    · linarith [max_lt hpos hlt]
  obtain ⟨w, hw_mem, hφw⟩ := intermediate_value_Icc hv₂h hcont htarget_mem
  have hw0 : 0 ≤ w := hv₁.trans (hv12.le.trans hw_mem.1)
  refine not_isImplementable_of_isVirtualWelfareMaximizing hx (i := i)
    (b := Function.update 0 j w) (update_nonneg le_rfl j hw0) hv₁ hv12 hpos (fun k _ => ?_)
    (Or.inr ⟨j, hij.symm, ?_, ?_⟩)
  · by_cases hkj : k = j
    · subst hkj
      rw [Function.update_self, hφw]
      dsimp only [target]
      linarith [max_lt hpos hlt]
    · rw [Function.update_of_ne hkj]
      exact hφ0.trans_lt hpos
  · rw [Function.update_self, hφw]
    dsimp only [target]
    linarith [le_max_left 0 (φ v₂)]
  · rw [Function.update_self, hφw]
    dsimp only [target]
    linarith [le_max_right 0 (φ v₂)]

/-! ### Seller production costs and reservation value `v₀ ≥ 0` (Theorem 13.10 & Exercise 13.1) -/

section SellerCost

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {μ : ι → Measure ℝ}
  [∀ i, IsProbabilityMeasure (μ i)] {f : ι → ℝ → NNReal} {h : ι → ℝ}

/-- **Expected profit equals expected virtual surplus** with a finite seller cost function `c(x)`
([HartlineKarlin2007], Definition 13.9 and Theorem 13.10, p. 336): for any normalized DSIC
mechanism `M` with measurable bounded allocations and integrable cost `v ↦ c (M.allocation v)`,
`E[∑ᵢ pᵢ(v) − c(x(v))] = E[∑ᵢ φᵢ(vᵢ) xᵢ(v) − c(x(v))]`. -/
theorem Mechanism.IsDSIC.integral_profit_eq_virtualSurplus_sub_cost {M : Mechanism ι}
    (hM : M.IsDSIC) (hN : M.IsNormalized) (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) {B : ℝ}
    (hx : ∀ i, Measurable fun v => M.allocation v i)
    (hB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ B) {c : (ι → ℝ) → ℝ}
    (hc : Integrable (fun v => c (M.allocation v)) (Measure.pi μ)) :
    ∫ v, ((∑ i, M.payment v i) - c (M.allocation v)) ∂Measure.pi μ =
      ∫ v, ((∑ i, virtualValue (μ i) (f i) (v i) * M.allocation v i) - c (M.allocation v))
        ∂Measure.pi μ := by
  have hint_pay : Integrable (fun v => ∑ i, M.payment v i) (Measure.pi μ) := by
    refine (integrable_finsetSum Finset.univ fun i _ =>
      integrable_myersonPayment hμ i (hx i) fun v hv => hB v hv i).congr ?_
    filter_upwards [ae_nonneg hμ] with v hv
    exact Finset.sum_congr rfl fun i _ => (hM.payment_eq_myersonPayment hN i hv).symm
  have hint_vv : Integrable (fun v => ∑ i, virtualValue (μ i) (f i) (v i) * M.allocation v i)
      (Measure.pi μ) :=
    integrable_finsetSum _ fun i _ => integrable_virtualValue_mul hμ i (hx i) fun v hv => hB v hv i
  rw [integral_sub hint_pay hc, integral_sub hint_vv hc, hM.integral_sum_payment_eq hN hμ hx hB]

/-- **Expected profit upper bound with seller cost `c(x)`** ([HartlineKarlin2007], Theorem 13.10,
p. 336): for every DSIC, IR mechanism `M` with integrable payments and integrable seller cost
`v ↦ c (M.allocation v)`, expected seller profit is at most expected virtual surplus minus seller
cost. -/
theorem Mechanism.IsDSIC.integral_profit_le_virtualSurplus_sub_cost {M : Mechanism ι}
    (hM : M.IsDSIC) (hIR : M.IsIR) (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) {B : ℝ}
    (hx : ∀ i, Measurable fun v => M.allocation v i)
    (hB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ B)
    (hp : Integrable (fun v => ∑ i, M.payment v i) (Measure.pi μ)) {c : (ι → ℝ) → ℝ}
    (hc : Integrable (fun v => c (M.allocation v)) (Measure.pi μ)) :
    ∫ v, ((∑ i, M.payment v i) - c (M.allocation v)) ∂Measure.pi μ ≤
      ∫ v, ((∑ i, virtualValue (μ i) (f i) (v i) * M.allocation v i) - c (M.allocation v))
        ∂Measure.pi μ := by
  have hint_vv : Integrable (fun v => ∑ i, virtualValue (μ i) (f i) (v i) * M.allocation v i)
      (Measure.pi μ) :=
    integrable_finsetSum _ fun i _ => integrable_virtualValue_mul hμ i (hx i) fun v hv => hB v hv i
  rw [integral_sub hp hc, integral_sub hint_vv hc]
  exact sub_le_sub_right (hM.integral_sum_payment_le hIR hμ hx hB) _

end SellerCost

namespace Vickrey

private theorem abs_le_one_of_mem_singleItemFeasible {ι : Type*} [Fintype ι] {y : ι → ℝ}
    (hy : y ∈ singleItemFeasible) (i : ι) : |y i| ≤ 1 := by
  obtain h | h := hy.1 i <;> simp [h]

private theorem sum_mul_sub_const_mul_sum {ι : Type*} [Fintype ι] (ψ y : ι → ℝ) (v₀ : ℝ) :
    (∑ i, ψ i * y i) - v₀ * ∑ i, y i = ∑ i, (ψ i - v₀) * y i := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem integrable_sellerCost {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ}
    [∀ i, IsProbabilityMeasure (μ i)] {f : ι → ℝ → NNReal} {h : ι → ℝ}
    (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) {v₀ : ℝ} (hv₀ : 0 ≤ v₀)
    {x : (ι → ℝ) → ι → ℝ} (hx : ∀ i, Measurable fun v => x v i)
    (hB : ∀ v, 0 ≤ v → ∀ i, |x v i| ≤ 1) :
    Integrable (fun v : ι → ℝ => v₀ * ∑ i, x v i) (Measure.pi μ) := by
  refine Integrable.of_bound
    (measurable_const.mul (Finset.measurable_sum _ fun i _ => hx i)).aestronglyMeasurable
    (v₀ * Fintype.card ι) ?_
  filter_upwards [ae_nonneg hμ] with v hv
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hv₀]
  refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans ?_) hv₀
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] using
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hB v hv i

/-- **Optimal single-item auction with seller reservation value `v₀ ≥ 0` under regularity**
([HartlineKarlin2007], Exercise 13.1, p. 360).

When bidders are i.i.d. with a regular distribution `(μ, f, h)` and the seller values keeping the
item at `v₀ ≥ 0` (so seller profit is `∑ᵢ pᵢ(v) − v₀ ∑ᵢ xᵢ(v)`), the Vickrey auction with shifted
reserve `r = reservePrice (fun z => virtualValue μ f z - v₀)` (`VA_{φ⁻¹(v₀)}`) is DSIC, IR, charges
winners `max(r, highestOtherBid b i)`, and achieves expected seller profit at least that of every
DSIC, IR single-item mechanism. For irregular or asymmetric distributions, see
`integral_profit_le_ironed_sellerReserve`. -/
theorem integral_profit_le_sellerReserve {ι : Type*} [Fintype ι] [LinearOrder ι]
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → NNReal} {h v₀ : ℝ}
    (hμ : HasValueDensity μ f h) (hreg : IsRegular μ f h) (hv₀ : 0 ≤ v₀)
    {M : Mechanism ι} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ singleItemFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ((∑ i, M.payment v i) - v₀ * ∑ i, M.allocation v i) ∂Measure.pi (fun _ : ι => μ) ≤
      ∫ v, ((∑ i, max (reservePrice fun z => virtualValue μ f z - v₀) (highestOtherBid v i) *
          reserveAllocation (fun z => virtualValue μ f z - v₀) v i) -
        v₀ * ∑ i, reserveAllocation (fun z => virtualValue μ f z - v₀) v i)
        ∂Measure.pi (fun _ : ι => μ) := by
  set φ₀ : ℝ → ℝ := fun z => virtualValue μ f z - v₀
  have hφ₀_mono : MonotoneOn φ₀ (Ioi 0) := fun a ha b hb hab =>
    sub_le_sub_right ((hreg.strictMonoOn_Ioi hμ).monotoneOn ha hb hab) v₀
  have hφ₀_zero : φ₀ 0 ≤ 0 := by linarith [virtualValue_le μ f 0]
  have hφ₀_ne : ∃ z, 0 < z ∧ 0 ≤ φ₀ z := by
    refine ⟨max h 1 + v₀, by positivity, ?_⟩
    have hh_le : h ≤ max h 1 + v₀ := by linarith [le_max_left h 1]
    simp only [φ₀, hμ.virtualValue_eq_self hh_le]
    linarith [le_max_right h 1]
  have hthresh : IsReserveThreshold φ₀ (reservePrice φ₀) :=
    isReserveThreshold_reservePrice hφ₀_mono hφ₀_ne
  have hB_M : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ 1 :=
    fun v hv => abs_le_one_of_mem_singleItemFeasible (hMX v hv)
  have hB_R : ∀ v, 0 ≤ v → ∀ i : ι, |reserveAllocation φ₀ v i| ≤ 1 := fun v _ i => by
    obtain h | h := reserveAllocation_binary φ₀ v i <;> simp [h]
  have hc_M := integrable_sellerCost (fun _ : ι => hμ) hv₀ hMm hB_M
  have hRm : ∀ i : ι, Measurable fun v : ι → ℝ => reserveAllocation φ₀ v i :=
    fun i => measurable_reserveAllocation (hμ.measurable_virtualValue.sub measurable_const) i
  have hc_R := integrable_sellerCost (fun _ : ι => hμ) hv₀ hRm hB_R
  have hdsic_R := myerson_isDSIC (isMonotone_reserveAllocation (ι := ι) hφ₀_mono)
  have heq_R := hdsic_R.integral_profit_eq_virtualSurplus_sub_cost
    (myerson_isNormalized _) (fun _ => hμ) hRm hB_R (c := fun y => v₀ * ∑ i, y i) hc_R
  dsimp only [myerson] at heq_R
  have hpay_eq : ∫ v, ((∑ i, max (reservePrice φ₀) (highestOtherBid v i) *
        reserveAllocation φ₀ v i) - v₀ * ∑ i, reserveAllocation φ₀ v i)
        ∂Measure.pi (fun _ : ι => μ) =
      ∫ v, ((∑ i, myersonPayment (reserveAllocation φ₀) v i) -
        v₀ * ∑ i, reserveAllocation φ₀ v i) ∂Measure.pi (fun _ : ι => μ) := by
    refine integral_congr_ae ?_
    filter_upwards [ae_nonneg fun _ : ι => hμ] with v hv
    congr 1
    exact Finset.sum_congr rfl fun i _ =>
      (myersonPayment_reserveAllocation hφ₀_mono hthresh hv i).symm
  rw [hpay_eq, heq_R]
  by_cases hp : Integrable (fun v => ∑ i, M.payment v i) (Measure.pi fun _ : ι => μ)
  · have hle1 := hM.integral_profit_le_virtualSurplus_sub_cost hIR (fun _ => hμ) hMm hB_M hp
      (c := fun y => v₀ * ∑ i, y i) hc_M
    refine hle1.trans (integral_mono_ae ?_ ?_ ?_)
    · exact (integrable_finsetSum _ fun i _ =>
        integrable_virtualValue_mul (fun _ => hμ) i (hMm i) fun v hv => hB_M v hv i).sub hc_M
    · exact (integrable_finsetSum _ fun i _ =>
        integrable_virtualValue_mul (fun _ => hμ) i (hRm i) fun v hv => hB_R v hv i).sub hc_R
    · filter_upwards [ae_nonneg fun _ : ι => hμ] with v hv
      rw [sum_mul_sub_const_mul_sum, sum_mul_sub_const_mul_sum]
      exact (isVirtualWelfareMaximizing_reserveAllocation (ι := ι) hφ₀_mono hφ₀_zero v hv).2 _
        (hMX v hv)
  · have hnot_int : ¬ Integrable (fun v => (∑ i, M.payment v i) - v₀ * ∑ i, M.allocation v i)
        (Measure.pi fun _ : ι => μ) :=
      fun hsub => hp ((hsub.add hc_M).congr
        (Filter.Eventually.of_forall fun _ => sub_add_cancel _ _))
    rw [integral_undef hnot_int]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_nonneg fun _ : ι => hμ] with v hv
    have h0 := (isVirtualWelfareMaximizing_reserveAllocation (ι := ι) hφ₀_mono hφ₀_zero v hv).2 0
      zero_mem_singleItemFeasible
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h0
    rwa [sum_mul_sub_const_mul_sum]

/-- Conditional seller-reserve optimality step after [Myerson1981] and [HartlineKarlin2007],
Exercise 13.1, p. 360 (not an unconditional irregular theorem; convex-hull existence of
`IsIronedVirtualValue` is tracked in #7789).

Given independent (possibly irregular and non-identical) distributions `(μᵢ, fᵢ, hᵢ)`,
caller-supplied ironed virtual valuations `φBarᵢ` nondecreasing on `[0, ∞)`, and seller valuation
`v₀ ≥ 0`, maximizing shifted ironed virtual welfare `∑ᵢ (φBarᵢ(vᵢ) − v₀) xᵢ` via
`myerson (ironedAllocation (fun i z => φBar i z - v₀))` achieves at least the expected seller
profit of every DSIC, IR single-item mechanism. -/
theorem integral_profit_le_ironed_sellerReserve_of_isIronedVirtualValue
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)] {f : ι → ℝ → NNReal} {h : ι → ℝ}
    {φBar : ι → ℝ → ℝ} {v₀ : ℝ} (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hφ : ∀ i, IsIronedVirtualValue (μ i) (f i) (h i) (φBar i))
    (hmono : ∀ i, MonotoneOn (φBar i) (Ici 0)) (hv₀ : 0 ≤ v₀)
    {M : Mechanism ι} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ singleItemFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ((∑ i, M.payment v i) - v₀ * ∑ i, M.allocation v i) ∂Measure.pi μ ≤
      ∫ v, ((∑ i, (myerson (ironedAllocation fun i z => φBar i z - v₀)).payment v i) -
        v₀ * ∑ i, ironedAllocation (fun i z => φBar i z - v₀) v i) ∂Measure.pi μ := by
  set φ₀ : ι → ℝ → ℝ := fun i z => φBar i z - v₀
  have hmono₀ : ∀ i, MonotoneOn (φ₀ i) (Ici 0) := fun i _ ha _ hb hab =>
    sub_le_sub_right (hmono i ha hb hab) v₀
  have hB_M : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ 1 :=
    fun v hv => abs_le_one_of_mem_singleItemFeasible (hMX v hv)
  have hB_I : ∀ v, 0 ≤ v → ∀ i : ι, |ironedAllocation φ₀ v i| ≤ 1 :=
    fun v _ => abs_le_one_of_mem_singleItemFeasible (ironedAllocation_mem_singleItemFeasible φ₀ v)
  have hIm : ∀ i : ι, Measurable fun v : ι → ℝ => ironedAllocation φ₀ v i :=
    fun i => measurable_ironedAllocation (fun j => ((hφ j).measurable.sub measurable_const)) i
  have hc_M := integrable_sellerCost hμ hv₀ hMm hB_M
  have hc_I := integrable_sellerCost hμ hv₀ hIm hB_I
  have hint_pay_I : Integrable (fun v => ∑ i, myersonPayment (ironedAllocation φ₀) v i)
      (Measure.pi μ) :=
    integrable_finsetSum _ fun i _ => integrable_myersonPayment hμ i (hIm i) fun v hv => hB_I v hv i
  have hint_ir_I : Integrable (fun v => ∑ i, φBar i (v i) * ironedAllocation φ₀ v i)
      (Measure.pi μ) :=
    integrable_finsetSum _ fun i _ => integrable_ironed_mul hμ hφ i (hIm i) fun v hv => hB_I v hv i
  have hpool : ∀ i v, 0 ≤ v → ∀ z₁ ∈ Ioc 0 (h i), ∀ z₂ ∈ Ioc 0 (h i),
      φBar i z₁ = φBar i z₂ →
        ironedAllocation φ₀ (Function.update v i z₁) i =
          ironedAllocation φ₀ (Function.update v i z₂) i := fun i v _ z₁ _ z₂ _ heq =>
    congrFun (ironedAllocation_eq_of_eq φ₀ virtualWinnerAllocation v i
      (by simp only [φ₀, heq])) i
  have hRHS_eq : ∫ v, ((∑ i, (myerson (ironedAllocation φ₀)).payment v i) -
        v₀ * ∑ i, ironedAllocation φ₀ v i) ∂Measure.pi μ =
      ∫ v, ((∑ i, φBar i (v i) * ironedAllocation φ₀ v i) -
        v₀ * ∑ i, ironedAllocation φ₀ v i) ∂Measure.pi μ := by
    change ∫ v, ((∑ i, myersonPayment (ironedAllocation φ₀) v i) - _) ∂Measure.pi μ = _
    rw [integral_sub hint_pay_I hc_I, integral_sub hint_ir_I hc_I,
      integral_sum_myersonPayment_eq_ironed hμ hφ (isMonotone_ironedAllocation hmono₀) hIm hB_I
        hpool]
  rw [hRHS_eq]
  by_cases hp : Integrable (fun v => ∑ i, M.payment v i) (Measure.pi μ)
  · have hint_ir_M : Integrable (fun v => ∑ i, φBar i (v i) * M.allocation v i) (Measure.pi μ) :=
      integrable_finsetSum _ fun i _ =>
        integrable_ironed_mul hμ hφ i (hMm i) fun v hv => hB_M v hv i
    have hLHS_le : ∫ v, ((∑ i, M.payment v i) - v₀ * ∑ i, M.allocation v i) ∂Measure.pi μ ≤
        ∫ v, ((∑ i, φBar i (v i) * M.allocation v i) -
          v₀ * ∑ i, M.allocation v i) ∂Measure.pi μ := by
      rw [integral_sub hp hc_M, integral_sub hint_ir_M hc_M]
      exact sub_le_sub_right (hM.integral_sum_payment_le_ironed hIR hμ hφ hMm hB_M) _
    refine hLHS_le.trans (integral_mono_ae (hint_ir_M.sub hc_M) (hint_ir_I.sub hc_I) ?_)
    filter_upwards [ae_nonneg hμ] with v hv
    rw [sum_mul_sub_const_mul_sum, sum_mul_sub_const_mul_sum]
    exact (virtualWinnerAllocation_mem_and_max (fun i => φ₀ i (v i))).2 _ (hMX v hv)
  · have hnot_int : ¬ Integrable (fun v => (∑ i, M.payment v i) - v₀ * ∑ i, M.allocation v i)
        (Measure.pi μ) :=
      fun hsub => hp ((hsub.add hc_M).congr
        (Filter.Eventually.of_forall fun _ => sub_add_cancel _ _))
    rw [integral_undef hnot_int]
    refine integral_nonneg_of_ae ?_
    filter_upwards [ae_nonneg hμ] with v _
    have h0 := (virtualWinnerAllocation_mem_and_max (fun i => φ₀ i (v i))).2 0
      zero_mem_singleItemFeasible
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at h0
    rwa [sum_mul_sub_const_mul_sum]

end Vickrey

/-! ### Monopoly pricing `opt(F)` and Bayesian digital goods without regularity (Theorem 13.18) -/

/-- `pStar ≥ 0` is a **monopoly sale price** (`opt(F)`) for a valuation measure `μ`
([HartlineKarlin2007], Definition 13.17, p. 338) if `pStar · μ([pStar, ∞))` maximizes the
single-buyer posted-price revenue `p · μ([p, ∞))` over all nonnegative prices `p ≥ 0`. Under a
density (`HasValueDensity`), `μ([p, ∞)) = μ((p, ∞)) = 1 − F(p)`. -/
@[expose] def IsMonopolyPrice (μ : Measure ℝ) (pStar : ℝ) : Prop :=
  0 ≤ pStar ∧ ∀ p, 0 ≤ p → p * μ.real (Ici p) ≤ pStar * μ.real (Ici pStar)

/-- For a regular distribution with density `f` on `[0, h]`, the virtual-valuation reserve price
`reservePrice (virtualValue μ f)` (`φ⁻¹(0)`) is a monopoly sale price ([HartlineKarlin2007],
Example 13.16 and Theorem 13.18, p. 338: `opt(F) = φ⁻¹(0)`). -/
theorem IsRegular.isMonopolyPrice_reservePrice {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → NNReal}
    {h : ℝ} (hreg : IsRegular μ f h) (hμ : HasValueDensity μ f h) :
    IsMonopolyPrice μ (reservePrice (virtualValue μ f)) := by
  have hnull := hμ.nullSingletonClass
  set r := reservePrice (virtualValue μ f)
  have hr : IsReserveThreshold (virtualValue μ f) r := hreg.isReserveThreshold hμ
  refine ⟨hr.1, fun p hp => ?_⟩
  rw [measureReal_congr (Ioi_ae_eq_Ici (μ := μ) (a := p)).symm,
    measureReal_congr (Ioi_ae_eq_Ici (μ := μ) (a := r)).symm,
    ← hμ.setIntegral_Ioi_virtualValue_eq hp, ← hμ.setIntegral_Ioi_virtualValue_eq hr.1,
    ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  refine integral_mono_ae
    (hμ.integrable_virtualValue.integrableOn.integrable_indicator measurableSet_Ioi)
    (hμ.integrable_virtualValue.integrableOn.integrable_indicator measurableSet_Ioi) ?_
  filter_upwards [hμ.ae_pos, μ.ae_ne r] with z hz0 hzr
  by_cases hpz : p < z <;> by_cases hrz : r < z
  · rw [indicator_of_mem (show z ∈ Ioi p from hpz), indicator_of_mem (show z ∈ Ioi r from hrz)]
  · rw [indicator_of_mem (show z ∈ Ioi p from hpz), indicator_of_notMem (show z ∉ Ioi r from hrz)]
    by_contra hpos
    have hlt_r : z < r := lt_of_le_of_ne (not_lt.1 hrz) hzr
    exact absurd (hr.2.2 z hz0 (le_of_lt (not_le.1 hpos))) (not_le.2 hlt_r)
  · rw [indicator_of_notMem (show z ∉ Ioi p from hpz), indicator_of_mem (show z ∈ Ioi r from hrz)]
    exact hr.2.1 z hrz
  · rw [indicator_of_notMem (show z ∉ Ioi p from hpz),
      indicator_of_notMem (show z ∉ Ioi r from hrz)]

open Classical in
/-- Fixed posted-price digital goods mechanism offering each bidder `i` take-it-or-leave-it price
`p i` ([HartlineKarlin2007], Example 13.16 and Theorem 13.18, p. 338). -/
@[expose] noncomputable def postedPriceDigitalGoods {ι : Type*} (p : ι → ℝ) : Mechanism ι where
  allocation b i := if p i ≤ b i then 1 else 0
  payment b i := if p i ≤ b i then p i else 0

theorem postedPriceDigitalGoods_mem_digitalGoodsFeasible {ι : Type*} (p : ι → ℝ) (b : ι → ℝ) :
    (postedPriceDigitalGoods p).allocation b ∈ digitalGoodsFeasible := fun i => by
  simp only [postedPriceDigitalGoods]
  split_ifs <;> norm_num

theorem postedPriceDigitalGoods_isDSIC {ι : Type*} [DecidableEq ι] (p : ι → ℝ) :
    (postedPriceDigitalGoods p).IsDSIC := by
  intro i b v _ _
  simp only [Mechanism.utility, postedPriceDigitalGoods, Function.update_self]
  split_ifs with h1 h2 h2 <;> linarith

theorem postedPriceDigitalGoods_isIR {ι : Type*} (p : ι → ℝ) :
    (postedPriceDigitalGoods p).IsIR := by
  intro i b _
  simp only [Mechanism.utility, postedPriceDigitalGoods]
  split_ifs with h <;> linarith

theorem postedPriceDigitalGoods_isNormalized {ι : Type*} [DecidableEq ι] {p : ι → ℝ}
    (hp : 0 ≤ p) : (postedPriceDigitalGoods p).IsNormalized := by
  intro i b _
  simp only [postedPriceDigitalGoods, Function.update_self]
  split_ifs with h
  · exact le_antisymm h (hp i)
  · rfl

theorem measurable_postedPriceDigitalGoods_allocation {ι : Type*} (p : ι → ℝ) (i : ι) :
    Measurable fun v : ι → ℝ => (postedPriceDigitalGoods p).allocation v i := by
  simp only [postedPriceDigitalGoods]
  exact Measurable.ite (measurableSet_le measurable_const (measurable_pi_apply i))
    measurable_const measurable_const

private theorem integrable_postedPriceDigitalGoods_payment {ι : Type*} [Fintype ι]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)] (p : ι → ℝ) (i : ι) :
    Integrable (fun v : ι → ℝ => (postedPriceDigitalGoods p).payment v i) (Measure.pi μ) := by
  simp only [postedPriceDigitalGoods]
  refine Integrable.of_bound (Measurable.ite (measurableSet_le measurable_const
    (measurable_pi_apply i)) measurable_const measurable_const).aestronglyMeasurable |p i|
    (Filter.Eventually.of_forall fun v => ?_)
  split_ifs <;> simp

theorem integral_postedPriceDigitalGoods_payment {ι : Type*} [Fintype ι]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)] (p : ι → ℝ) (i : ι) :
    ∫ v, (postedPriceDigitalGoods p).payment v i ∂Measure.pi μ = p i * (μ i).real (Ici (p i)) := by
  classical
  rw [← integral_integral_update μ (integrable_postedPriceDigitalGoods_payment p i) i]
  have hinner : ∀ v : ι → ℝ, ∫ z, (postedPriceDigitalGoods p).payment (Function.update v i z) i
      ∂μ i = p i * (μ i).real (Ici (p i)) := fun v => by
    have hfun : (fun z => (postedPriceDigitalGoods p).payment (Function.update v i z) i) =
        (Ici (p i)).indicator fun _ => p i := by
      ext z
      by_cases hz : p i ≤ z <;> simp [postedPriceDigitalGoods, hz]
    rw [hfun, integral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul, mul_comm]
  simp_rw [hinner, integral_const, probReal_univ, one_smul]

/-- One-dimensional monopoly-price upper bound without regularity or density: for any probability
measure `μ` concentrated on `[0, h]`, any monopoly price `pStar`, and any `[0, 1]`-valued
monotone allocation curve `g`, the expected Myerson payment is at most `pStar · μ([pStar, ∞))`. -/
private theorem integral_myersonCurve_le_monopolyPrice {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {h pStar : ℝ} (hμ : ∀ᵐ v ∂μ, v ∈ Icc 0 h) (hpStar : IsMonopolyPrice μ pStar) {g : ℝ → ℝ}
    (hg : Measurable g) (hgm : MonotoneOn g (Ici 0)) (hg01 : ∀ z, 0 ≤ z → 0 ≤ g z ∧ g z ≤ 1) :
    ∫ v, (v * g v - ∫ z in (0 : ℝ)..v, g z) ∂μ ≤ pStar * μ.real (Ici pStar) := by
  have hh : 0 ≤ h := by
    obtain ⟨v, hv⟩ := hμ.exists
    exact hv.1.trans hv.2
  set θ : ℝ → ℝ := fun u => if u ≤ g h then sInf {w ∈ Icc 0 h | u ≤ g w} else h with hθ_def
  have hθ_mono : Monotone θ := by
    intro u₁ u₂ hu
    dsimp only [θ]
    split_ifs with h1 h2 h2
    · exact csInf_le_csInf ⟨0, fun _ hw => hw.1.1⟩ ⟨h, ⟨hh, le_rfl⟩, h2⟩
        fun w hw => ⟨hw.1, hu.trans hw.2⟩
    · exact csInf_le ⟨0, fun _ hw => hw.1.1⟩ ⟨⟨hh, le_rfl⟩, h1⟩
    · exact absurd (hu.trans h2) h1
    · exact le_rfl
  have hθ_nonneg : ∀ u, 0 ≤ θ u := fun u => by
    dsimp only [θ]
    split_ifs with h1
    · exact le_csInf ⟨h, ⟨hh, le_rfl⟩, h1⟩ fun _ hw => hw.1.1
    · exact hh
  have hθ_le_h : ∀ u, θ u ≤ h := fun u => by
    dsimp only [θ]
    split_ifs with h1
    · exact csInf_le ⟨0, fun _ hw => hw.1.1⟩ ⟨⟨hh, le_rfl⟩, h1⟩
    · exact le_rfl
  have hcurve : ∀ v ∈ Icc 0 h,
      v * g v - (∫ z in (0 : ℝ)..v, g z) =
        ∫ u in Ioc (0 : ℝ) 1, (if u ≤ g v then θ u else 0) := by
    intro v hv
    have hgv01 := hg01 v hv.1
    set νz : Measure ℝ := volume.restrict (Ioc 0 v)
    set νu : Measure ℝ := volume.restrict (Ioc 0 1)
    have : IsFiniteMeasure νz := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    have : IsFiniteMeasure νu := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
    set T : Set (ℝ × ℝ) := {p | g p.1 < p.2 ∧ p.2 ≤ g v} with hT_def
    have hT_meas : MeasurableSet T :=
      (measurableSet_lt (hg.comp measurable_fst) measurable_snd).inter
        (measurableSet_le measurable_snd measurable_const)
    set G : ℝ × ℝ → ℝ := T.indicator fun _ => (1 : ℝ) with hG_def
    have hG_int : Integrable G (νz.prod νu) := (integrable_const (1 : ℝ)).indicator hT_meas
    have hswap := integral_integral_swap (μ := νz) (ν := νu) (f := fun z u => G (z, u)) hG_int
    have hL : ∫ z, (∫ u, G (z, u) ∂νu) ∂νz = v * g v - ∫ z in (0 : ℝ)..v, g z := by
      have hin : ∀ z ∈ Ioc 0 v, ∫ u, G (z, u) ∂νu = g v - g z := fun z hz => by
        have hgz01 := hg01 z hz.1.le
        have hgz_le : g z ≤ g v := hgm hz.1.le hv.1 hz.2
        have hGz : (fun u => G (z, u)) = (Ioc (g z) (g v)).indicator fun _ => (1 : ℝ) := rfl
        have hinter : Ioc (g z) (g v) ∩ Ioc 0 1 = Ioc (g z) (g v) :=
          inter_eq_left.2 (Ioc_subset_Ioc hgz01.1 hgv01.2)
        rw [hGz, integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
          hinter, setIntegral_const, Real.volume_real_Ioc_of_le hgz_le, smul_eq_mul, mul_one]
      have hg_int : IntegrableOn g (Ioc 0 v) := by
        refine Integrable.of_bound hg.aestronglyMeasurable 1 ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
        rw [Real.norm_eq_abs, abs_of_nonneg (hg01 z hz.1.le).1]
        exact (hg01 z hz.1.le).2
      rw [setIntegral_congr_fun measurableSet_Ioc hin,
        integral_sub (integrableOn_const measure_Ioc_lt_top.ne) hg_int,
        setIntegral_const, Real.volume_real_Ioc_of_le hv.1, sub_zero, smul_eq_mul,
        intervalIntegral.integral_of_le hv.1]
    have hR : ∫ u, (∫ z, G (z, u) ∂νz) ∂νu =
        ∫ u in Ioc (0 : ℝ) 1, (if u ≤ g v then θ u else 0) := by
      refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
      by_cases huv : u ≤ g v
      · simp only [huv, ↓reduceIte]
        have huh : u ≤ g h := huv.trans (hgm hv.1 hh hv.2)
        have hθu : θ u = sInf {w ∈ Icc 0 h | u ≤ g w} := by
          dsimp only [θ]
          simp only [huh, ↓reduceIte]
        have hU_ne : ({w ∈ Icc 0 h | u ≤ g w}).Nonempty := ⟨v, hv, huv⟩
        have hU_bdd : BddBelow {w ∈ Icc 0 h | u ≤ g w} := ⟨0, fun _ hw => hw.1.1⟩
        have hθ_le_v : θ u ≤ v := by rw [hθu]; exact csInf_le hU_bdd ⟨hv, huv⟩
        have hae_G : (fun z => G (z, u)) =ᵐ[νz] (Iic (θ u)).indicator fun _ => (1 : ℝ) := by
          filter_upwards [ae_restrict_mem measurableSet_Ioc,
            ae_restrict_of_ae (volume.ae_ne (θ u))] with z hz hzne
          rcases lt_or_gt_of_ne hzne with hlt | hgt
          · rw [hθu] at hlt
            have hnot : z ∉ {w ∈ Icc 0 h | u ≤ g w} :=
              fun hw => absurd (csInf_le hU_bdd hw) (not_le.2 hlt)
            have hgu : g z < u := lt_of_not_ge fun hle => hnot ⟨⟨hz.1.le, hz.2.trans hv.2⟩, hle⟩
            have hle_θ : z ≤ θ u := by rw [hθu]; exact hlt.le
            rw [hG_def, indicator_of_mem (show (z, u) ∈ T from ⟨hgu, huv⟩),
              indicator_of_mem (show z ∈ Iic (θ u) from hle_θ)]
          · rw [hθu] at hgt
            obtain ⟨w, hwU, hwz⟩ := exists_lt_of_csInf_lt hU_ne hgt
            have hnotlt : ¬ g z < u := not_lt.2 (hwU.2.trans (hgm hwU.1.1 hz.1.le hwz.le))
            have hnotle : ¬ z ≤ θ u := not_le.2 (by rwa [hθu])
            rw [hG_def, indicator_of_notMem (show (z, u) ∉ T from fun hT => hnotlt hT.1),
              indicator_of_notMem (show z ∉ Iic (θ u) from hnotle)]
        rw [integral_congr_ae hae_G, integral_indicator measurableSet_Iic,
          Measure.restrict_restrict measurableSet_Iic, Iic_inter_Ioc_eq hθ_le_v, setIntegral_const,
          Real.volume_real_Ioc_of_le (hθ_nonneg u), sub_zero, smul_eq_mul, mul_one]
      · simp only [huv, ↓reduceIte]
        have h0 : (fun z => G (z, u)) = fun _ => 0 := by
          ext z
          exact indicator_of_notMem (show (z, u) ∉ T from fun hT => huv hT.2) _
        rw [h0, integral_zero]
    rw [← hL, hswap, hR]
  set νu : Measure ℝ := volume.restrict (Ioc 0 1)
  have : IsFiniteMeasure νu := isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  set H : ℝ × ℝ → ℝ := {p | p.2 ≤ g p.1}.indicator fun p => θ p.2 with hH_def
  have hH_meas : Measurable H :=
    (hθ_mono.measurable.comp measurable_snd).indicator
      (measurableSet_le measurable_snd (hg.comp measurable_fst))
  have hH_int : Integrable H (μ.prod νu) := by
    refine Integrable.of_bound hH_meas.aestronglyMeasurable h
      (Filter.Eventually.of_forall fun p => ?_)
    by_cases hp : p.2 ≤ g p.1
    · rw [hH_def, indicator_of_mem hp, Real.norm_eq_abs, abs_of_nonneg (hθ_nonneg p.2)]
      exact hθ_le_h p.2
    · rw [hH_def, indicator_of_notMem hp, Real.norm_eq_abs, abs_zero]
      exact hh
  have hLHS : ∫ v, (v * g v - ∫ z in (0 : ℝ)..v, g z) ∂μ = ∫ v, (∫ u, H (v, u) ∂νu) ∂μ := by
    refine integral_congr_ae (hμ.mono fun v hv => ?_)
    dsimp only
    rw [hcurve v hv]
    refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
    by_cases huv : u ≤ g v <;> simp [hH_def, huv]
  rw [hLHS, integral_integral_swap (μ := μ) (ν := νu) (f := fun v u => H (v, u)) hH_int]
  have h_ub : ∀ u ∈ Ioc (0 : ℝ) 1, ∫ v, H (v, u) ∂μ ≤ pStar * μ.real (Ici pStar) := by
    intro u _
    have hHu : (fun v => H (v, u)) = ({v | u ≤ g v}).indicator fun _ => θ u := rfl
    rw [hHu, integral_indicator (measurableSet_le measurable_const hg), setIntegral_const,
      smul_eq_mul, mul_comm]
    have hsub_ae : ({v | u ≤ g v} : Set ℝ) ≤ᵐ[μ] Ici (θ u) := by
      filter_upwards [hμ] with v hv huv
      have huh : u ≤ g h := huv.trans (hgm hv.1 hh hv.2)
      change θ u ≤ v
      dsimp only [θ]
      simp only [huh, ↓reduceIte]
      exact csInf_le ⟨0, fun _ hw => hw.1.1⟩ ⟨hv, huv⟩
    have hmeas_le : μ.real {v | u ≤ g v} ≤ μ.real (Ici (θ u)) := by
      rw [measureReal_def, measureReal_def]
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub_ae)
    exact (mul_le_mul_of_nonneg_left hmeas_le (hθ_nonneg u)).trans (hpStar.2 (θ u) (hθ_nonneg u))
  refine (setIntegral_mono_on hH_int.integral_prod_right
    (integrableOn_const measure_Ioc_lt_top.ne) measurableSet_Ioc h_ub).trans ?_
  rw [setIntegral_const, Real.volume_real_Ioc_of_le zero_le_one, sub_zero, smul_eq_mul, one_mul]

/-- **Optimal Bayesian digital goods auction without regularity** ([HartlineKarlin2007],
Definition 13.17 and Theorem 13.18, p. 338).

For independent (not necessarily identical, regular, or continuous) valuation distributions `μᵢ`
concentrated on `[0, hᵢ]`, if `pStarᵢ` is a monopoly sale price (`IsMonopolyPrice (μ i) (pStar i)`)
for each bidder `i`, then offering each bidder the fixed take-it-or-leave-it price `pStarᵢ`
(`postedPriceDigitalGoods pStar`) is DSIC, individually rational, normalized, and achieves at least
the expected revenue of **every** DSIC, individually rational digital-goods mechanism. -/
theorem integral_sum_payment_le_postedPriceDigitalGoods {ι : Type*} [Fintype ι] [DecidableEq ι]
    {μ : ι → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)] {h pStar : ι → ℝ}
    (hμ : ∀ i, ∀ᵐ v ∂μ i, v ∈ Icc 0 (h i)) (hpStar : ∀ i, IsMonopolyPrice (μ i) (pStar i))
    {M : Mechanism ι} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ digitalGoodsFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤
      ∫ v, ∑ i, (postedPriceDigitalGoods pStar).payment v i ∂Measure.pi μ := by
  have hae_box : ∀ᵐ v ∂Measure.pi μ, ∀ i, v i ∈ Icc 0 (h i) := by
    rw [ae_all_iff]
    exact fun i => (Measure.quasiMeasurePreserving_eval μ i).ae (hμ i)
  have hae_nn : ∀ᵐ v ∂Measure.pi μ, 0 ≤ v := hae_box.mono fun _ hv i => (hv i).1
  have hint_mye : ∀ i, Integrable (fun v => myersonPayment M.allocation v i) (Measure.pi μ) := by
    intro i
    refine Integrable.of_bound (measurable_myersonPayment i (hMm i)).aestronglyMeasurable
      (max 0 (h i) + max 0 (h i)) ?_
    filter_upwards [hae_box] with v hv
    have hv0 : 0 ≤ v := fun j => (hv j).1
    have hhi : 0 ≤ max 0 (h i) := le_max_left _ _
    have hvi : v i ≤ max 0 (h i) := (hv i).2.trans (le_max_right _ _)
    have h1 : ‖v i * M.allocation v i‖ ≤ max 0 (h i) := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hv i).1,
        abs_of_nonneg (hMX v hv0 i).1]
      exact (mul_le_of_le_one_right (hv i).1 (hMX v hv0 i).2).trans hvi
    have h2 : ‖∫ z in (0 : ℝ)..v i, M.allocation (Function.update v i z) i‖ ≤ 1 * |v i - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun z hz => by
        rw [uIoc_of_le (hv i).1] at hz
        have h01 := hMX _ (update_nonneg hv0 i hz.1.le) i
        rw [Real.norm_eq_abs, abs_of_nonneg h01.1]
        exact h01.2
    rw [one_mul, sub_zero, abs_of_nonneg (hv i).1] at h2
    exact (norm_sub_le _ _).trans (add_le_add h1 (h2.trans hvi))
  have hle_mye : ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤
      ∑ i, ∫ v, myersonPayment M.allocation v i ∂Measure.pi μ := by
    rw [← integral_finsetSum _ fun i _ => hint_mye i]
    by_cases hint : Integrable (fun v => ∑ i, M.payment v i) (Measure.pi μ)
    · refine integral_mono_ae hint (integrable_finsetSum _ fun i _ => hint_mye i) ?_
      filter_upwards [hae_nn] with v hv
      refine Finset.sum_le_sum fun i _ => ?_
      rw [hM.payment_eq i hv]
      linarith [hIR.payment_update_zero_nonpos i hv]
    · rw [integral_undef hint]
      refine integral_nonneg_of_ae ?_
      filter_upwards [hae_nn] with v hv
      exact Finset.sum_nonneg fun i _ => myersonPayment_nonneg hM.isMonotone hv i
  rw [integral_finsetSum _ fun i _ => integrable_postedPriceDigitalGoods_payment pStar i]
  refine hle_mye.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [integral_postedPriceDigitalGoods_payment pStar i, ← integral_integral_update μ (hint_mye i) i]
  refine (integral_mono_ae
    (integrable_integral_update_measure μ i (μ i)
      (by simpa only [Function.update_eq_self] using hint_mye i))
    (integrable_const (pStar i * (μ i).real (Ici (pStar i)))) ?_).trans_eq ?_
  · filter_upwards [hae_nn] with v hv
    have hcurve := integral_myersonCurve_le_monopolyPrice (hμ i) (hpStar i)
      (g := fun z => M.allocation (Function.update v i z) i)
      ((hMm i).comp (measurable_update v)) (hM.isMonotone i v hv)
      (fun z hz => hMX _ (update_nonneg hv i hz) i)
    simpa only [myersonPayment, Function.update_self, Function.update_idem] using hcurve
  · rw [integral_const, probReal_univ, one_smul]

/-! ### Discrete finite-support virtual valuations and discrete ironing (Exercise 13.3) -/

/-- A finite-support discrete single-parameter prior on `m + 1` strictly ordered nonnegative
valuations `v₀ < v₁ < ⋯ < vₘ` with positive probabilities `fₖ > 0` summing to `1`
([HartlineKarlin2007], Exercise 13.3, p. 360). -/
structure DiscretePrior (m : ℕ) where
  /-- Ordered valuation grid `v₀ < v₁ < ⋯ < vₘ`. -/
  val : Fin (m + 1) → ℝ
  /-- Probability mass `fₖ = Pr[V = vₖ]` at each grid index. -/
  prob : Fin (m + 1) → ℝ
  /-- Grid valuations are strictly increasing. -/
  strictMono : StrictMono val
  /-- Every grid valuation is nonnegative (`0 ≤ v₀`). -/
  val_zero_nonneg : 0 ≤ val 0
  /-- Every grid valuation has positive probability. -/
  prob_pos : ∀ k, 0 < prob k
  /-- Total probability mass equals `1`. -/
  sum_prob : ∑ k, prob k = 1

namespace DiscretePrior

variable {m : ℕ} (D : DiscretePrior m)

theorem val_nonneg (k : Fin (m + 1)) : 0 ≤ D.val k :=
  D.val_zero_nonneg.trans (D.strictMono.monotone (Fin.zero_le k))

/-- **Discrete virtual valuation** ([HartlineKarlin2007], Exercise 13.3, p. 360):
`φ(vₖ) = vₖ − (vₖ₊₁ − vₖ) · (∑_{j > k} fⱼ) / fₖ` for `k < m`, and `φ(vₘ) = vₘ` at the top grid
point. -/
@[expose] noncomputable def virtualValue (k : Fin (m + 1)) : ℝ :=
  if hk : k.1 < m then
    D.val k - (D.val ⟨k.1 + 1, Nat.succ_lt_succ hk⟩ - D.val k) *
      (∑ j with k < j, D.prob j) / D.prob k
  else
    D.val k

@[simp]
theorem virtualValue_castSucc (i : Fin m) :
    D.virtualValue i.castSucc =
      D.val i.castSucc - (D.val i.succ - D.val i.castSucc) *
        (∑ j with i.castSucc < j, D.prob j) / D.prob i.castSucc := by
  simp only [virtualValue, Fin.val_castSucc, i.isLt, ↓reduceDIte]
  rfl

@[simp]
theorem virtualValue_last : D.virtualValue (Fin.last m) = D.val (Fin.last m) := by
  simp only [virtualValue, Fin.val_last, lt_irrefl, ↓reduceDIte]

/-- Discrete envelope payment formula on the valuation grid `D.val`, obtained by binding
individual rationality at `v₀` and downward local incentive constraints
`p_{i+1} − p_i = v_{i+1}(x_{i+1} − x_i)`: `pₖ = vₖ xₖ − ∑_{i < k} (v_{i+1} − v_i) x_i`. -/
@[expose] def envelopePayment (x : Fin (m + 1) → ℝ) (k : Fin (m + 1)) : ℝ :=
  D.val k * x k -
    ∑ i : Fin m with i.succ ≤ k, (D.val i.succ - D.val i.castSucc) * x i.castSucc

/-- Dominant-strategy incentive compatibility on the discrete valuation grid `D.val`. -/
@[expose] def IsDiscreteDSIC (x p : Fin (m + 1) → ℝ) : Prop :=
  ∀ k l : Fin (m + 1), D.val k * x l - p l ≤ D.val k * x k - p k

/-- Individual rationality on the discrete valuation grid `D.val`. -/
@[expose] def IsDiscreteIR (x p : Fin (m + 1) → ℝ) : Prop :=
  ∀ k : Fin (m + 1), 0 ≤ D.val k * x k - p k

theorem IsDiscreteDSIC.monotone {x p : Fin (m + 1) → ℝ} (hdsic : D.IsDiscreteDSIC x p) :
    Monotone x := by
  intro k l hkl
  rcases hkl.eq_or_lt with rfl | hlt
  · exact le_rfl
  · have h1 := hdsic k l
    have h2 := hdsic l k
    have hv : D.val k < D.val l := D.strictMono hlt
    by_contra hcon
    nlinarith [lt_of_not_ge hcon]

private theorem sum_filter_succ_le_succ {n : ℕ} (g : Fin n → ℝ) (r : Fin n) :
    (∑ j : Fin n with j.succ ≤ r.succ, g j) =
      g r + ∑ j : Fin n with j.succ ≤ r.castSucc, g j := by
  have hfilt : (Finset.univ.filter fun j : Fin n => j.succ ≤ r.succ) =
      insert r (Finset.univ.filter fun j : Fin n => j.succ ≤ r.castSucc) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
    omega
  have hnotmem : r ∉ Finset.univ.filter fun j : Fin n => j.succ ≤ r.castSucc := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.val_succ,
      Fin.val_castSucc]
    omega
  rw [hfilt, Finset.sum_insert hnotmem]

private theorem filter_succ_le_zero {n : ℕ} :
    (Finset.univ.filter fun i : Fin n => i.succ ≤ (0 : Fin (n + 1))) = ∅ :=
  Finset.filter_eq_empty_iff.2 fun i _ => not_le.2 i.succ_pos

private theorem envelopePayment_succ_sub (x : Fin (m + 1) → ℝ) (i : Fin m) :
    D.envelopePayment x i.succ - D.envelopePayment x i.castSucc =
      D.val i.succ * (x i.succ - x i.castSucc) := by
  simp only [envelopePayment, sum_filter_succ_le_succ]
  ring

/-- Every discrete DSIC, IR mechanism charges at most the discrete envelope payment at every grid
point. -/
theorem payment_le_envelopePayment {x p : Fin (m + 1) → ℝ} (hdsic : D.IsDiscreteDSIC x p)
    (hir : D.IsDiscreteIR x p) (k : Fin (m + 1)) :
    p k ≤ D.envelopePayment x k := by
  induction k using Fin.induction with
  | zero =>
    simp only [envelopePayment, filter_succ_le_zero, Finset.sum_empty, sub_zero]
    linarith [hir 0]
  | succ i ih =>
    have hic := hdsic i.succ i.castSucc
    have hstep := D.envelopePayment_succ_sub x i
    linarith

/-- Pairing a grid allocation rule `x` with `D.envelopePayment x` is DSIC on `D` if and only if
`x` is monotone. -/
theorem envelopePayment_isDiscreteDSIC_iff {x : Fin (m + 1) → ℝ} :
    D.IsDiscreteDSIC x (D.envelopePayment x) ↔ Monotone x := by
  refine ⟨IsDiscreteDSIC.monotone D, fun hx k l => ?_⟩
  set u : Fin (m + 1) → ℝ := fun j => D.val k * x j - D.envelopePayment x j
  have hstep : ∀ i : Fin m, u i.succ - u i.castSucc =
      (D.val k - D.val i.succ) * (x i.succ - x i.castSucc) := fun i => by
    have := D.envelopePayment_succ_sub x i
    dsimp only [u]
    linarith
  have hup : ∀ j : Fin (m + 1), j ≤ k → u j ≤ u k := by
    intro j hjk
    obtain ⟨d, hd⟩ : ∃ d, k.1 - j.1 = d := ⟨_, rfl⟩
    induction d generalizing j with
    | zero =>
      have hjk_eq : j = k := Fin.ext (by omega)
      rw [hjk_eq]
    | succ d ih =>
      have hjlt : j.1 < m := lt_of_lt_of_le (by omega) (Nat.le_of_lt_succ k.isLt)
      let i : Fin m := ⟨j.1, hjlt⟩
      have hi_val : i.1 = j.1 := rfl
      have hj_eq : j = i.castSucc := rfl
      have hisucc_le : i.succ ≤ k := by
        rw [Fin.le_def, Fin.val_succ, hi_val]
        omega
      have hdiff := hstep i
      have hnonneg : 0 ≤ (D.val k - D.val i.succ) * (x i.succ - x i.castSucc) :=
        mul_nonneg (sub_nonneg.2 (D.strictMono.monotone hisucc_le))
          (sub_nonneg.2 (hx i.castSucc_le_succ))
      have h1 : u j ≤ u i.succ := by rw [hj_eq]; linarith
      exact h1.trans (ih i.succ hisucc_le (by rw [Fin.val_succ, hi_val]; omega))
  have hdown : ∀ j : Fin (m + 1), k ≤ j → u j ≤ u k := by
    intro j hkj
    induction j using Fin.induction with
    | zero =>
      have hk0 : k = 0 := Fin.ext (Nat.eq_zero_of_le_zero hkj)
      rw [hk0]
    | succ i ih =>
      rcases hkj.eq_or_lt with hkeq | hklt
      · rw [hkeq]
      · have hk_le : k ≤ i.castSucc := by
          rw [Fin.lt_def, Fin.val_succ] at hklt
          rw [Fin.le_def, Fin.val_castSucc]
          omega
        have hdiff := hstep i
        have hnonpos : (D.val k - D.val i.succ) * (x i.succ - x i.castSucc) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (D.strictMono hklt).le)
            (sub_nonneg.2 (hx i.castSucc_le_succ))
        exact (by linarith : u i.succ ≤ u i.castSucc).trans (ih hk_le)
  rcases le_total l k with hlk | hkl
  · exact hup l hlk
  · exact hdown l hkl

/-- With nonnegative allocations, the discrete envelope payment rule is individually rational. -/
theorem envelopePayment_isDiscreteIR {x : Fin (m + 1) → ℝ} (hx : ∀ k, 0 ≤ x k) :
    D.IsDiscreteIR x (D.envelopePayment x) := fun k => by
  simp only [envelopePayment]
  have hsum : 0 ≤ ∑ i : Fin m with i.succ ≤ k, (D.val i.succ - D.val i.castSucc) * x i.castSucc :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (sub_nonneg.2 (D.strictMono i.castSucc_lt_succ).le) (hx i.castSucc)
  linarith

/-- **Discrete revenue equals expected discrete virtual surplus** ([HartlineKarlin2007],
Exercise 13.3, p. 360): for any allocation curve `x` on the grid `D.val`, summation by parts
identifies expected envelope payment with expected discrete virtual surplus. -/
theorem expectedEnvelopePayment_eq_expectedVirtualSurplus (x : Fin (m + 1) → ℝ) :
    ∑ k, D.prob k * D.envelopePayment x k = ∑ k, D.prob k * D.virtualValue k * x k := by
  have hsub : ∑ k, D.prob k * D.envelopePayment x k =
      (∑ k, D.prob k * D.val k * x k) -
        ∑ k : Fin (m + 1), ∑ i : Fin m with i.succ ≤ k,
          D.prob k * ((D.val i.succ - D.val i.castSucc) * x i.castSucc) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [envelopePayment, mul_sub, Finset.mul_sum, mul_assoc]
  have hswap : (∑ k : Fin (m + 1), ∑ i : Fin m with i.succ ≤ k,
        D.prob k * ((D.val i.succ - D.val i.castSucc) * x i.castSucc)) =
      ∑ i : Fin m, (D.val i.succ - D.val i.castSucc) *
        (∑ k : Fin (m + 1) with i.castSucc < k, D.prob k) * x i.castSucc := by
    have h1 : (∑ k : Fin (m + 1), ∑ i : Fin m with i.succ ≤ k,
          D.prob k * ((D.val i.succ - D.val i.castSucc) * x i.castSucc)) =
        ∑ k : Fin (m + 1), ∑ i : Fin m,
          if i.succ ≤ k then D.prob k * ((D.val i.succ - D.val i.castSucc) * x i.castSucc) else 0 :=
      Finset.sum_congr rfl fun k _ => by rw [Finset.sum_filter]
    rw [h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hiff : ∀ k : Fin (m + 1), i.succ ≤ k ↔ i.castSucc < k := fun k => by
      simp only [Fin.le_def, Fin.lt_def, Fin.val_succ, Fin.val_castSucc]
      omega
    simp_rw [hiff]
    rw [← Finset.sum_filter, ← Finset.sum_mul]
    ring
  rw [hsub, hswap,
    Fin.sum_univ_castSucc (f := fun k : Fin (m + 1) => D.prob k * D.val k * x k),
    Fin.sum_univ_castSucc (f := fun k : Fin (m + 1) => D.prob k * D.virtualValue k * x k)]
  rw [virtualValue_last]
  have hmerge : (∑ i : Fin m, D.prob i.castSucc * D.val i.castSucc * x i.castSucc +
        D.prob (Fin.last m) * D.val (Fin.last m) * x (Fin.last m)) -
      (∑ i : Fin m, (D.val i.succ - D.val i.castSucc) *
        (∑ k with i.castSucc < k, D.prob k) * x i.castSucc) =
      (∑ i : Fin m, (D.prob i.castSucc * D.val i.castSucc * x i.castSucc -
        (D.val i.succ - D.val i.castSucc) * (∑ k with i.castSucc < k, D.prob k) * x i.castSucc)) +
        D.prob (Fin.last m) * D.val (Fin.last m) * x (Fin.last m) := by
    rw [Finset.sum_sub_distrib]
    ring
  rw [hmerge]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [virtualValue_castSucc]
  have hfpos : D.prob i.castSucc ≠ 0 := (D.prob_pos i.castSucc).ne'
  field_simp

/-- Every discrete DSIC, IR mechanism has expected payment at most its expected discrete virtual
surplus. -/
theorem expectedPayment_le_expectedVirtualSurplus {x p : Fin (m + 1) → ℝ}
    (hdsic : D.IsDiscreteDSIC x p) (hir : D.IsDiscreteIR x p) :
    ∑ k, D.prob k * p k ≤ ∑ k, D.prob k * D.virtualValue k * x k := by
  rw [← D.expectedEnvelopePayment_eq_expectedVirtualSurplus x]
  exact Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left (D.payment_le_envelopePayment hdsic hir k) (D.prob_pos k).le

/-- **Discrete converse of Lemma 13.12** ([HartlineKarlin2007], Lemma 13.12, p. 337): if discrete
virtual valuations fail monotonicity (`j < k` with `φ(vₖ) < c₀ < φ(vⱼ)` against a reserve or
competitor virtual value `c₀`), any `[0, 1]`-valued rule `x` maximizing `(φ(vᵣ) − c₀) y` at each
grid point is non-monotone (`¬ Monotone x`), and hence by `IsDiscreteDSIC.monotone` cannot be
implemented as a discrete DSIC mechanism. -/
theorem not_monotone_virtualWelfareMaximizer_of_gt {j k : Fin (m + 1)} (hjk : j < k)
    {c₀ : ℝ} (hk : D.virtualValue k < c₀) (hj : c₀ < D.virtualValue j)
    {x : Fin (m + 1) → ℝ}
    (hx01 : ∀ r, 0 ≤ x r ∧ x r ≤ 1)
    (hmax : ∀ r y, 0 ≤ y → y ≤ 1 →
      (D.virtualValue r - c₀) * y ≤ (D.virtualValue r - c₀) * x r) :
    ¬ Monotone x := by
  intro hmono
  have h1 := hmax j 1 zero_le_one le_rfl
  have h2 := hmax k 0 le_rfl zero_le_one
  have hxj : x j = 1 := by nlinarith [(hx01 j).2]
  have hxk : x k = 0 := by nlinarith [(hx01 k).1]
  have hle := hmono hjk.le
  linarith

end DiscretePrior

/-- `φBar` is a **discrete ironed virtual valuation** for `D : DiscretePrior m`:

* `φBar` is monotone nondecreasing on `Fin (m + 1)`;
* every upper tail sum `∑_{j ≥ k} fⱼ φ̄ⱼ` dominates `∑_{j ≥ k} fⱼ φⱼ`, with equality at `k = 0`
  (the full sum);
* *discrete complementary slackness*: wherever strict tail slack occurs at `i.succ`, `φBar` pools
  adjacent grid points `i.castSucc` and `i.succ` (`φBar i.castSucc = φBar i.succ`). -/
structure IsDiscreteIronedVirtualValue {m : ℕ} (D : DiscretePrior m)
    (φBar : Fin (m + 1) → ℝ) : Prop where
  /-- Monotonicity of the ironed virtual valuation across the grid. -/
  monotone : Monotone φBar
  /-- Upper-tail dominance at every grid point. -/
  tail_le : ∀ k : Fin (m + 1),
    ∑ j with k ≤ j, D.prob j * D.virtualValue j ≤ ∑ j with k ≤ j, D.prob j * φBar j
  /-- Total expectation preservation across `Fin (m + 1)`. -/
  sum_eq : ∑ j, D.prob j * D.virtualValue j = ∑ j, D.prob j * φBar j
  /-- Pooling flatness across adjacent types whenever cumulative tail slack is positive. -/
  eq_of_lt : ∀ i : Fin m,
    ∑ j with i.succ ≤ j, D.prob j * D.virtualValue j <
      ∑ j with i.succ ≤ j, D.prob j * φBar j →
        φBar i.castSucc = φBar i.succ

namespace IsDiscreteIronedVirtualValue

variable {m : ℕ} {D : DiscretePrior m} {φBar : Fin (m + 1) → ℝ}

private theorem sum_ironed_sub_virtualValue_mul (hφ : IsDiscreteIronedVirtualValue D φBar)
    (x : Fin (m + 1) → ℝ) :
    (∑ j, D.prob j * φBar j * x j) - (∑ j, D.prob j * D.virtualValue j * x j) =
      ∑ i : Fin m, (x i.succ - x i.castSucc) *
        ((∑ j with i.succ ≤ j, D.prob j * φBar j) -
          ∑ j with i.succ ≤ j, D.prob j * D.virtualValue j) := by
  rw [← Finset.sum_sub_distrib]
  have hrew : (∑ j, (D.prob j * φBar j * x j - D.prob j * D.virtualValue j * x j)) =
      ∑ j, (D.prob j * φBar j - D.prob j * D.virtualValue j) * x j :=
    Finset.sum_congr rfl fun j _ => by ring
  have hab := Fin.sum_univ_smul_by_parts_tail
    (fun j => D.prob j * φBar j - D.prob j * D.virtualValue j) x
  simp only [smul_eq_mul] at hab
  rw [hrew, hab, Finset.sum_sub_distrib, hφ.sum_eq, sub_self, zero_mul, zero_add]
  exact Finset.sum_congr rfl fun i _ => by
    simp only [← Finset.filter_le_eq_Ici, Finset.sum_sub_distrib, mul_comm]

/-- **Discrete Myerson ironing inequality.** For every monotone allocation curve `x` on the grid,
expected discrete virtual surplus is at most expected discrete ironed virtual surplus. -/
theorem sum_virtualValue_mul_le (hφ : IsDiscreteIronedVirtualValue D φBar)
    {x : Fin (m + 1) → ℝ} (hx : Monotone x) :
    ∑ j, D.prob j * D.virtualValue j * x j ≤ ∑ j, D.prob j * φBar j * x j := by
  rw [← sub_nonneg, hφ.sum_ironed_sub_virtualValue_mul]
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (sub_nonneg.2 (hx i.castSucc_le_succ)) (sub_nonneg.2 (hφ.tail_le i.succ))

/-- **Discrete pooling equality.** If `x` is constant across adjacent pooled types where `φBar` is
flat, expected discrete virtual surplus equals expected discrete ironed virtual surplus. -/
theorem sum_virtualValue_mul_eq (hφ : IsDiscreteIronedVirtualValue D φBar)
    {x : Fin (m + 1) → ℝ}
    (hpool : ∀ i : Fin m, φBar i.castSucc = φBar i.succ → x i.castSucc = x i.succ) :
    ∑ j, D.prob j * D.virtualValue j * x j = ∑ j, D.prob j * φBar j * x j := by
  symm
  rw [← sub_eq_zero, hφ.sum_ironed_sub_virtualValue_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases (hφ.tail_le i.succ).eq_or_lt with heq | hlt
  · rw [heq, sub_self, mul_zero]
  · rw [hpool i (hφ.eq_of_lt i hlt), sub_self, zero_mul]

end IsDiscreteIronedVirtualValue

/-- Conditional discrete optimality step after [Myerson1981] and [HartlineKarlin2007],
Exercise 13.3, p. 360 (not an unconditional discrete irregular-auction theorem; concave-envelope
existence of `IsDiscreteIronedVirtualValue` from arbitrary `DiscretePrior` is tracked in #7789).

Given independent finite-support priors `D : ∀ i, DiscretePrior (m i)` and caller-supplied discrete
ironed virtual valuations `φBar i`, if `x : (∀ i, Fin (m i + 1)) → ι → ℝ` maximizes
`∑ᵢ φBarᵢ(kᵢ) yᵢ` over `X` at every grid profile `k` and is constant across every pooled adjacent
step of `φBarᵢ`, then pairing `x` with coordinatewise discrete envelope payments achieves at least
the expected revenue of every discrete DSIC, IR feasible mechanism `(x', p')`. -/
theorem expectedDiscreteSumPayment_le_ironed_of_isDiscreteIronedVirtualValue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : ι → ℕ} (D : ∀ i, DiscretePrior (m i))
    {φBar : ∀ i, Fin (m i + 1) → ℝ}
    (hφ : ∀ i, IsDiscreteIronedVirtualValue (D i) (φBar i))
    {X : Set (ι → ℝ)} {x : (∀ i, Fin (m i + 1)) → ι → ℝ}
    (hx_max : ∀ k, x k ∈ X ∧ ∀ y ∈ X, ∑ i, φBar i (k i) * y i ≤ ∑ i, φBar i (k i) * x k i)
    (hx_pool : ∀ i k (r : Fin (m i)), φBar i r.castSucc = φBar i r.succ →
      x (Function.update k i r.castSucc) i = x (Function.update k i r.succ) i)
    {x' p' : (∀ i, Fin (m i + 1)) → ι → ℝ}
    (hx'_mem : ∀ k, x' k ∈ X)
    (hdsic : ∀ i k, (D i).IsDiscreteDSIC (fun r => x' (Function.update k i r) i)
      (fun r => p' (Function.update k i r) i))
    (hir : ∀ i k, (D i).IsDiscreteIR (fun r => x' (Function.update k i r) i)
      (fun r => p' (Function.update k i r) i)) :
    (∑ k : ∀ i, Fin (m i + 1), (∏ j, (D j).prob (k j)) * ∑ i, p' k i) ≤
      ∑ k : ∀ i, Fin (m i + 1), (∏ j, (D j).prob (k j)) *
        ∑ i, (D i).envelopePayment (fun r => x (Function.update k i r) i) (k i) := by
  have hsum_coord : ∀ (i : ι) (G : (∀ j, Fin (m j + 1)) → Fin (m i + 1) → ℝ),
      (∑ k : ∀ j, Fin (m j + 1), (∏ j, (D j).prob (k j)) * G k (k i)) =
        ∑ k : ∀ j, Fin (m j + 1), (∏ j, (D j).prob (k j)) *
          ∑ r : Fin (m i + 1), (D i).prob r * G (Function.update k i r) r := by
    intro i G
    -- Split k into (k i, k_{-i}) by summing over r' = k i on LHS!
    -- Equivalently, introduce `x.2` via `(D i).sum_prob = 1` and swap `(x.1 i, x.2)`.
    have hinv : Function.Involutive fun x : (∀ j, Fin (m j + 1)) × Fin (m i + 1) =>
        (Function.update x.1 i x.2, x.1 i) := fun x => by simp
    calc ∑ k : ∀ j, Fin (m j + 1), (∏ j, (D j).prob (k j)) * G k (k i)
        = ∑ x : (∀ j, Fin (m j + 1)) × Fin (m i + 1),
            (∏ j, (D j).prob (x.1 j)) * (D i).prob x.2 * G x.1 (x.1 i) := by
          simp only [Fintype.sum_prod_type, ← Finset.sum_mul, ← Finset.mul_sum, (D i).sum_prob,
            mul_one]
      _ = ∑ x : (∀ j, Fin (m j + 1)) × Fin (m i + 1),
            (∏ j, (D j).prob (x.1 j)) *
              ((D i).prob x.2 * G (Function.update x.1 i x.2) x.2) := by
          refine (Fintype.sum_equiv (Function.Involutive.toPerm _ hinv) _ _ fun x => ?_).symm
          simp only [Function.Involutive.coe_toPerm, Function.update_self,
            Finset.prod_apply_update_of_mem (Finset.mem_univ i) (fun j a => (D j).prob a)]
          rw [← Finset.mul_prod_erase _ (fun j => (D j).prob (x.1 j)) (Finset.mem_univ i)]
          ring
      _ = _ := by simp only [Fintype.sum_prod_type, Finset.mul_sum]
  have hLHS_le : (∑ k : ∀ j, Fin (m j + 1), (∏ j, (D j).prob (k j)) * ∑ i, p' k i) ≤
      ∑ k : ∀ j, Fin (m j + 1), (∏ j, (D j).prob (k j)) *
        ∑ i, φBar i (k i) * x' k i := by
    simp_rw [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [hsum_coord i (fun k _ => p' k i), hsum_coord i (fun k r => φBar i r * x' k i)]
    refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left ?_
      (Finset.prod_nonneg fun j _ => ((D j).prob_pos (k j)).le)
    simp_rw [← mul_assoc]
    exact ((D i).expectedPayment_le_expectedVirtualSurplus (hdsic i k) (hir i k)).trans
      ((hφ i).sum_virtualValue_mul_le ((hdsic i k).monotone (D i)))
  have hRHS_eq : (∑ k : ∀ j, Fin (m j + 1), (∏ j, (D j).prob (k j)) *
        ∑ i, (D i).envelopePayment (fun r => x (Function.update k i r) i) (k i)) =
      ∑ k : ∀ j, Fin (m j + 1), (∏ j, (D j).prob (k j)) *
        ∑ i, φBar i (k i) * x k i := by
    simp_rw [Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hsum_coord i (fun k r => (D i).envelopePayment (fun s => x (Function.update k i s) i) r),
      hsum_coord i (fun k r => φBar i r * x k i)]
    simp only [Function.update_idem]
    refine Finset.sum_congr rfl fun k _ => congrArg ((∏ j, (D j).prob (k j)) * ·) ?_
    simp_rw [← mul_assoc]
    exact ((D i).expectedEnvelopePayment_eq_expectedVirtualSurplus _).trans
      ((hφ i).sum_virtualValue_mul_eq (hx_pool i k))
  rw [hRHS_eq]
  exact hLHS_le.trans (Finset.sum_le_sum fun k _ =>
    mul_le_mul_of_nonneg_left ((hx_max k).2 _ (hx'_mem k))
      (Finset.prod_nonneg fun j _ => ((D j).prob_pos (k j)).le))

/-! ### Empirical monopoly pricing, `DOP`, Example 13.23, and single-item `EM` (Exercise 13.4) -/

section EmpiricalMyerson

open Classical in
/-- Total revenue `p · |{j ∈ S : bⱼ ≥ p}|` obtained from a subset of bidders `S` at uniform offer
price `p` ([HartlineKarlin2007], Definitions 13.19 and 13.21, pp. 339–340). -/
@[expose] noncomputable def empiricalSinglePriceRevenue {ι : Type*} (S : Finset ι) (b : ι → ℝ)
    (p : ℝ) : ℝ :=
  p * ((S.filter fun j => p ≤ b j).card : ℝ)

open Classical in
/-- Nonnegative candidate prices `{0} ∪ {bⱼ ≥ 0 | j ∈ S}` for maximizing empirical single-price
revenue on `S`. -/
noncomputable def empiricalCandidatePrices {ι : Type*} (S : Finset ι) (b : ι → ℝ) : Finset ℝ :=
  insert 0 ((S.filter fun j => 0 ≤ b j).image b)

private theorem zero_mem_empiricalCandidatePrices {ι : Type*} (S : Finset ι) (b : ι → ℝ) :
    (0 : ℝ) ∈ empiricalCandidatePrices S b := by
  classical
  exact Finset.mem_insert_self 0 _

open Classical in
/-- Optimal single sale price `opt(F_S)` on bid subset `S`, breaking ties in favour of the smallest
optimal nonnegative candidate price ([HartlineKarlin2007], Definitions 13.17 and 13.19,
pp. 338–339). -/
noncomputable def empiricalMonopolyPriceOn {ι : Type*} (S : Finset ι) (b : ι → ℝ) : ℝ :=
  let C := empiricalCandidatePrices S b
  let maxR := C.sup' ⟨0, zero_mem_empiricalCandidatePrices S b⟩ (empiricalSinglePriceRevenue S b)
  let optC := C.filter fun p => empiricalSinglePriceRevenue S b p = maxR
  have hne : optC.Nonempty := by
    obtain ⟨p, hpC, hpmax⟩ :=
      Finset.exists_mem_eq_sup' ⟨0, zero_mem_empiricalCandidatePrices S b⟩
        (empiricalSinglePriceRevenue S b)
    exact ⟨p, Finset.mem_filter.2 ⟨hpC, hpmax.symm⟩⟩
  optC.min' hne

/-- **Empirical monopoly price** `opt(F_{b₋ᵢ})` offered to bidder `i` from the empirical
distribution of the other bids `b₋ᵢ` ([HartlineKarlin2007], Definitions 13.19 and 13.21,
pp. 339–340). -/
@[expose] noncomputable def empiricalMonopolyPrice {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ι → ℝ) (i : ι) : ℝ :=
  empiricalMonopolyPriceOn (Finset.univ.erase i) b

theorem empiricalMonopolyPriceOn_mem_candidates {ι : Type*} (S : Finset ι) (b : ι → ℝ) :
    empiricalMonopolyPriceOn S b ∈ empiricalCandidatePrices S b := by
  classical
  unfold empiricalMonopolyPriceOn
  exact (Finset.mem_filter.1 (Finset.min'_mem _ _)).1

theorem empiricalMonopolyPriceOn_nonneg {ι : Type*} (S : Finset ι) (b : ι → ℝ) :
    0 ≤ empiricalMonopolyPriceOn S b := by
  classical
  have hmem := empiricalMonopolyPriceOn_mem_candidates S b
  simp only [empiricalCandidatePrices, Finset.mem_insert, Finset.mem_image,
    Finset.mem_filter] at hmem
  rcases hmem with h0 | ⟨_, ⟨_, hbj⟩, heq⟩
  · exact h0.ge
  · exact heq ▸ hbj

/-- `empiricalMonopolyPriceOn S b` maximizes `empiricalSinglePriceRevenue S b p` over **all** real
prices `p : ℝ`. -/
theorem empiricalSinglePriceRevenue_le_empiricalMonopolyPriceOn {ι : Type*} (S : Finset ι)
    (b : ι → ℝ) (p : ℝ) :
    empiricalSinglePriceRevenue S b p ≤
      empiricalSinglePriceRevenue S b (empiricalMonopolyPriceOn S b) := by
  classical
  have hopt_mem : empiricalMonopolyPriceOn S b ∈
      (empiricalCandidatePrices S b).filter (fun q =>
        empiricalSinglePriceRevenue S b q =
          (empiricalCandidatePrices S b).sup' ⟨0, zero_mem_empiricalCandidatePrices S b⟩
            (empiricalSinglePriceRevenue S b)) := by
    unfold empiricalMonopolyPriceOn
    exact Finset.min'_mem _ _
  have hopt_eq : empiricalSinglePriceRevenue S b (empiricalMonopolyPriceOn S b) =
      (empiricalCandidatePrices S b).sup' ⟨0, zero_mem_empiricalCandidatePrices S b⟩
        (empiricalSinglePriceRevenue S b) := (Finset.mem_filter.1 hopt_mem).2
  rw [hopt_eq]
  have h0_le : 0 ≤ (empiricalCandidatePrices S b).sup' ⟨0, zero_mem_empiricalCandidatePrices S b⟩
      (empiricalSinglePriceRevenue S b) := by
    simpa only [empiricalSinglePriceRevenue, zero_mul] using
      Finset.le_sup' (empiricalSinglePriceRevenue S b) (zero_mem_empiricalCandidatePrices S b)
  rcases le_or_gt p 0 with hp0 | hp_pos
  · exact (mul_nonpos_of_nonpos_of_nonneg hp0 (Nat.cast_nonneg _)).trans h0_le
  · by_cases hW : (S.filter fun j => p ≤ b j).Nonempty
    · obtain ⟨j₀, hj₀, hmin⟩ := (S.filter fun j => p ≤ b j).exists_min_image b hW
      have hj₀S : j₀ ∈ S := (Finset.mem_filter.1 hj₀).1
      have hp_le_bj₀ : p ≤ b j₀ := (Finset.mem_filter.1 hj₀).2
      have hbj₀_cand : b j₀ ∈ empiricalCandidatePrices S b := by
        simp only [empiricalCandidatePrices, Finset.mem_insert, Finset.mem_image, Finset.mem_filter]
        exact Or.inr ⟨j₀, ⟨hj₀S, hp_pos.le.trans hp_le_bj₀⟩, rfl⟩
      have hsub : (S.filter fun j => p ≤ b j) ⊆ S.filter fun j => b j₀ ≤ b j := fun j hj =>
        Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj).1, hmin j hj⟩
      have hcard : ((S.filter fun j => p ≤ b j).card : ℝ) ≤
          ((S.filter fun j => b j₀ ≤ b j).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have hstep : empiricalSinglePriceRevenue S b p ≤ empiricalSinglePriceRevenue S b (b j₀) := by
        simp only [empiricalSinglePriceRevenue]
        exact mul_le_mul hp_le_bj₀ hcard (Nat.cast_nonneg _) (hp_pos.le.trans hp_le_bj₀)
      exact hstep.trans (Finset.le_sup' (empiricalSinglePriceRevenue S b) hbj₀_cand)
    · rw [Finset.not_nonempty_iff_eq_empty] at hW
      simpa only [empiricalSinglePriceRevenue, hW, Finset.card_empty, Nat.cast_zero, mul_zero] using
        h0_le

theorem empiricalMonopolyPrice_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℝ)
    (i : ι) : 0 ≤ empiricalMonopolyPrice b i :=
  empiricalMonopolyPriceOn_nonneg _ _

@[simp]
theorem empiricalMonopolyPrice_update {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℝ)
    (i : ι) (z : ℝ) :
    empiricalMonopolyPrice (Function.update b i z) i = empiricalMonopolyPrice b i := by
  classical
  have hb : ∀ j ∈ Finset.univ.erase i, Function.update b i z j = b j :=
    fun j hj => Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
  have hcand : empiricalCandidatePrices (Finset.univ.erase i) (Function.update b i z) =
      empiricalCandidatePrices (Finset.univ.erase i) b := by
    simp only [empiricalCandidatePrices]
    rw [Finset.filter_congr fun j hj => by rw [hb j hj],
      Finset.image_congr fun j hj => hb j (Finset.mem_filter.1 hj).1]
  have hrev : ∀ p, empiricalSinglePriceRevenue (Finset.univ.erase i) (Function.update b i z) p =
      empiricalSinglePriceRevenue (Finset.univ.erase i) b p := fun p => by
    simp only [empiricalSinglePriceRevenue]
    rw [Finset.filter_congr fun j hj => by rw [hb j hj]]
  unfold empiricalMonopolyPrice empiricalMonopolyPriceOn
  simp_rw [hcand, hrev]

/-- Key observation for Exercise 13.4: the empirical monopoly price `opt(F_{b₋ᵢ})` never exceeds
the highest other bid `maxⱼ≠ᵢ bⱼ` (since every candidate price is either `0` or `bⱼ` for some
`j ≠ i`). -/
theorem empiricalMonopolyPrice_le_highestOtherBid {ι : Type*} [Fintype ι] [LinearOrder ι]
    (b : ι → ℝ) (i : ι) :
    empiricalMonopolyPrice b i ≤ Vickrey.highestOtherBid b i := by
  classical
  unfold empiricalMonopolyPrice
  have hmem := empiricalMonopolyPriceOn_mem_candidates (Finset.univ.erase i) b
  simp only [empiricalCandidatePrices, Finset.mem_insert, Finset.mem_image, Finset.mem_filter,
    Finset.mem_erase, Finset.mem_univ, and_true] at hmem
  rcases hmem with h0 | ⟨j, ⟨hji, _⟩, heq⟩
  · exact h0 ▸ Vickrey.highestOtherBid_nonneg b i
  · exact heq ▸ Vickrey.le_highestOtherBid hji

open Classical in
/-- **Deterministic Optimal Price auction (`DOP`)** ([HartlineKarlin2007], Definition 13.21,
p. 340): empirical Myerson applied to digital goods, offering each bidder `i` the bid-independent
price `opt(F_{b₋ᵢ})`. -/
@[expose] noncomputable def dopMechanism {ι : Type*} [Fintype ι] [DecidableEq ι] : Mechanism ι where
  allocation b i := if empiricalMonopolyPrice b i ≤ b i then 1 else 0
  payment b i := if empiricalMonopolyPrice b i ≤ b i then empiricalMonopolyPrice b i else 0

theorem dopMechanism_isDSIC {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (dopMechanism (ι := ι)).IsDSIC := by
  intro i b v _ _
  simp only [Mechanism.utility, dopMechanism, empiricalMonopolyPrice_update, Function.update_self]
  split_ifs <;> linarith

theorem dopMechanism_isIR {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (dopMechanism (ι := ι)).IsIR := by
  intro i b _
  simp only [Mechanism.utility, dopMechanism]
  split_ifs <;> linarith

theorem dopMechanism_isNormalized {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (dopMechanism (ι := ι)).IsNormalized := by
  intro i b _
  simp only [dopMechanism, empiricalMonopolyPrice_update, Function.update_self]
  split_ifs with h
  · exact le_antisymm h (empiricalMonopolyPrice_nonneg b i)
  · rfl

/-- Parametric `k²`-bidder worst-case bid family generalizing [HartlineKarlin2007], Example 13.23
(p. 340, `k = 10`): among `k²` bidders, the first `k` bid `k` and the remaining `k² − k` bid `1`. -/
def dopBadBids (k : ℕ) (i : Fin (k ^ 2)) : ℝ :=
  if i.1 < k then k else 1

private theorem mem_empiricalCandidatePrices_dopBadBids {k : ℕ} {S : Finset (Fin (k ^ 2))} {p : ℝ}
    (hp : p ∈ empiricalCandidatePrices S (dopBadBids k)) :
    p = 0 ∨ p = 1 ∨ p = k := by
  classical
  simp only [empiricalCandidatePrices, Finset.mem_insert, Finset.mem_image, Finset.mem_filter] at hp
  rcases hp with rfl | ⟨j, _, rfl⟩
  · exact Or.inl rfl
  · simp only [dopBadBids]
    split_ifs
    · exact Or.inr (Or.inr rfl)
    · exact Or.inr (Or.inl rfl)

private theorem filter_one_le_dopBadBids {k : ℕ} (hk : 1 ≤ k) (S : Finset (Fin (k ^ 2)))
    (inst : DecidablePred fun j : Fin (k ^ 2) => (1 : ℝ) ≤ dopBadBids k j) :
    @Finset.filter _ _ inst S = S :=
  (@Finset.filter_eq_self _ _ inst S).2 fun j _ => by
    simp only [dopBadBids]
    split_ifs
    · exact_mod_cast hk
    · exact le_rfl

private theorem filter_univ_coe_le_dopBadBids {k : ℕ} (hk : 2 ≤ k) (hk_sq : k < k ^ 2)
    (inst : DecidablePred fun j : Fin (k ^ 2) => (k : ℝ) ≤ dopBadBids k j) :
    @Finset.filter _ _ inst Finset.univ = Finset.Iio ⟨k, hk_sq⟩ := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  ext j
  rw [@Finset.mem_filter _ _ inst]
  simp only [Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def, dopBadBids]
  split_ifs with hj
  · exact ⟨fun _ => hj, fun _ => le_rfl⟩
  · exact ⟨fun h => absurd h (not_le.2 hk1), fun h => absurd h hj⟩

/-- For every `k ≥ 2`, the optimal single-price revenue `max_p p · |{i : bᵢ ≥ p}|` on `dopBadBids k`
is `k²` (achieved at both `p = 1` and `p = k`, generalizing [HartlineKarlin2007], Example 13.23,
p. 340). -/
theorem empiricalSinglePriceRevenue_dopBadBids_opt {k : ℕ} (hk : 2 ≤ k) :
    empiricalSinglePriceRevenue Finset.univ (dopBadBids k)
      (empiricalMonopolyPriceOn Finset.univ (dopBadBids k)) = (k : ℝ) ^ 2 := by
  have hrev_k : empiricalSinglePriceRevenue Finset.univ (dopBadBids k) k = (k : ℝ) ^ 2 := by
    simp only [empiricalSinglePriceRevenue, filter_univ_coe_le_dopBadBids hk (by nlinarith),
      Fin.card_Iio]
    ring
  have hrev_1 : empiricalSinglePriceRevenue Finset.univ (dopBadBids k) 1 = (k : ℝ) ^ 2 := by
    simp only [empiricalSinglePriceRevenue, filter_one_le_dopBadBids (by omega : 1 ≤ k),
      Finset.card_univ, Fintype.card_fin, one_mul, Nat.cast_pow]
  refine le_antisymm ?_ ?_
  · rcases mem_empiricalCandidatePrices_dopBadBids
        (empiricalMonopolyPriceOn_mem_candidates Finset.univ (dopBadBids k)) with
      h0 | h1 | hk'
    · rw [h0, empiricalSinglePriceRevenue, zero_mul]
      positivity
    · rw [h1, hrev_1]
    · rw [hk', hrev_k]
  · simpa only [hrev_1] using
      empiricalSinglePriceRevenue_le_empiricalMonopolyPriceOn Finset.univ (dopBadBids k) 1

/-- **Unbounded worst-case competitive ratio of `DOP`** (parametric generalization of
[HartlineKarlin2007], Example 13.23, p. 340): for every `k ≥ 2`, on `dopBadBids k` (where optimal
single-price revenue is `k²`), `DOP` offers price `1` to each of the `k` high bidders
(`k² − 1 > k(k − 1)`) and price `k` to each of the `k² − k` low bidders (`k² > k² − 1`),
collecting total revenue `k`. -/
theorem dopMechanism_sum_payment_dopBadBids {k : ℕ} (hk : 2 ≤ k) :
    ∑ i : Fin (k ^ 2), dopMechanism.payment (dopBadBids k) i = k := by
  have hk_lt_sq : k < k ^ 2 := by nlinarith
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hsq_pos : 1 ≤ k ^ 2 := by nlinarith
  have hk_pos : 1 ≤ k := by omega
  let cut : Fin (k ^ 2) := ⟨k, hk_lt_sq⟩
  have herase_1 : ∀ i : Fin (k ^ 2),
      empiricalSinglePriceRevenue (Finset.univ.erase i) (dopBadBids k) 1 = (k : ℝ) ^ 2 - 1 :=
    fun i => by
      simp only [empiricalSinglePriceRevenue, filter_one_le_dopBadBids hk_pos,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin, one_mul,
        Nat.cast_sub hsq_pos, Nat.cast_pow, Nat.cast_one]
  have herase_k : ∀ i : Fin (k ^ 2),
      empiricalSinglePriceRevenue (Finset.univ.erase i) (dopBadBids k) k =
        if i.1 < k then (k : ℝ) * (k - 1) else (k : ℝ) ^ 2 := fun i => by
    simp only [empiricalSinglePriceRevenue, Finset.filter_erase,
      filter_univ_coe_le_dopBadBids hk hk_lt_sq]
    by_cases hi : i.1 < k
    · have himem : i ∈ Finset.Iio cut := Finset.mem_Iio.2 hi
      simp only [hi, ↓reduceIte, Finset.card_erase_of_mem himem, Fin.card_Iio, cut,
        Nat.cast_sub hk_pos, Nat.cast_one]
    · have hinot : i ∉ Finset.Iio cut := by simpa only [Finset.mem_Iio, Fin.lt_def] using hi
      simp only [hi, ↓reduceIte, Finset.erase_eq_of_notMem hinot, Fin.card_Iio, cut]
      ring
  have hemp_lt : ∀ i : Fin (k ^ 2), i.1 < k → empiricalMonopolyPrice (dopBadBids k) i = 1 := by
    intro i hi
    have hmem := empiricalMonopolyPriceOn_mem_candidates (Finset.univ.erase i) (dopBadBids k)
    have hge1 := empiricalSinglePriceRevenue_le_empiricalMonopolyPriceOn
      (Finset.univ.erase i) (dopBadBids k) 1
    rw [herase_1 i] at hge1
    rcases mem_empiricalCandidatePrices_dopBadBids hmem with h0 | h1 | hk'
    · rw [h0, empiricalSinglePriceRevenue, zero_mul] at hge1; nlinarith
    · exact h1
    · rw [hk', herase_k i, ite_eq_left hi] at hge1; nlinarith
  have hemp_ge : ∀ i : Fin (k ^ 2), ¬ i.1 < k → empiricalMonopolyPrice (dopBadBids k) i = k := by
    intro i hi
    have hmem := empiricalMonopolyPriceOn_mem_candidates (Finset.univ.erase i) (dopBadBids k)
    have hgek := empiricalSinglePriceRevenue_le_empiricalMonopolyPriceOn
      (Finset.univ.erase i) (dopBadBids k) k
    rw [herase_k i, ite_eq_right hi] at hgek
    rcases mem_empiricalCandidatePrices_dopBadBids hmem with h0 | h1 | hk'
    · rw [h0, empiricalSinglePriceRevenue, zero_mul] at hgek; nlinarith
    · rw [h1, herase_1 i] at hgek; linarith
    · exact hk'
  have hpay : ∀ i : Fin (k ^ 2), dopMechanism.payment (dopBadBids k) i =
      if i ∈ Finset.Iio cut then 1 else 0 := fun i => by
    by_cases hi : i.1 < k
    · have himem : i ∈ Finset.Iio cut := Finset.mem_Iio.2 hi
      simp only [himem, ↓reduceIte, dopMechanism, hemp_lt i hi, dopBadBids, hi, hk1.le]
    · have hinot : i ∉ Finset.Iio cut := by simpa only [Finset.mem_Iio, Fin.lt_def] using hi
      simp only [hinot, ↓reduceIte, dopMechanism, hemp_ge i hi, dopBadBids, hi, not_le.2 hk1]
  simp_rw [hpay]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, Fin.card_Iio]
  simp only [cut, nsmul_eq_mul, mul_one]

open Classical in
/-- **Empirical Myerson single-item mechanism (`EM`)** ([HartlineKarlin2007], Definition 13.20,
Theorem 13.15, Theorem 13.18, and Exercise 13.4, pp. 338–339, 360): instantiates the i.i.d.
optimal single-item reserve-price auction `VA_{opt(F_{b₋ᵢ})}` for each bidder `i` using the
empirical monopoly price `opt(F_{b₋ᵢ})` of the other bids.

In any discrete distribution on `v₀ < ⋯ < vₘ` (`n ≥ 2`), the top support point `vₘ = maxⱼ≠ᵢ bⱼ` is
an extreme vertex of the quantile revenue curve `(0, 0) → (fₘ, fₘ vₘ)` (since `vₖ q < vₘ q` for
all `k < m`), so `vₘ` is never pooled downward under discrete ironing and retains ironed virtual
valuation `vₘ ≥ 0` while all lower support points have ironed virtual valuation `< vₘ`; thus bidder
`i` still beats the existing `vₘ` bidder in `b₋ᵢ` only above `maxⱼ≠ᵢ bⱼ` and pays `maxⱼ≠ᵢ bⱼ`
(formalizing general multi-environment `EM` simulation over arbitrary cost functions `c` is tracked
in #7789). -/
@[expose] noncomputable def empiricalSingleItemMechanism {ι : Type*} [Fintype ι] [LinearOrder ι] :
    Mechanism ι where
  allocation b i := if Vickrey.Wins b i ∧ empiricalMonopolyPrice b i ≤ b i then 1 else 0
  payment b i :=
    max (empiricalMonopolyPrice b i) (Vickrey.highestOtherBid b i) *
      if Vickrey.Wins b i ∧ empiricalMonopolyPrice b i ≤ b i then 1 else 0

/-- **Single-item `EM` has the exact Vickrey allocation** on every nonnegative bid profile `b ≥ 0`
([HartlineKarlin2007], Exercise 13.4, p. 360), since `opt(F_{b₋ᵢ}) ≤ maxⱼ≠ᵢ bⱼ`. -/
theorem empiricalSingleItemMechanism_allocation {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : ι → ℝ} (hb : 0 ≤ b) :
    empiricalSingleItemMechanism.allocation b = Vickrey.mechanism.allocation b := by
  funext i
  have hle_high := empiricalMonopolyPrice_le_highestOtherBid b i
  simp only [empiricalSingleItemMechanism, Vickrey.mechanism, Vickrey.allocation]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.1 h2
  · exact absurd ⟨h2, hle_high.trans
      (Vickrey.highestOtherBid_le_iff.2 ⟨hb i, fun j hj => (h2 j hj).1⟩)⟩ h1
  · rfl

/-- **Single-item `EM` has the exact Vickrey payment** on every nonnegative bid profile `b ≥ 0`
([HartlineKarlin2007], Exercise 13.4, p. 360), since `max(opt(F_{b₋ᵢ}), maxⱼ≠ᵢ bⱼ) = maxⱼ≠ᵢ bⱼ`. -/
theorem empiricalSingleItemMechanism_payment {ι : Type*} [Fintype ι] [LinearOrder ι]
    {b : ι → ℝ} (hb : 0 ≤ b) :
    empiricalSingleItemMechanism.payment b = Vickrey.mechanism.payment b := by
  funext i
  have hmax : max (empiricalMonopolyPrice b i) (Vickrey.highestOtherBid b i) =
      Vickrey.highestOtherBid b i :=
    max_eq_right (empiricalMonopolyPrice_le_highestOtherBid b i)
  have halloc := congrFun (empiricalSingleItemMechanism_allocation hb) i
  change max (empiricalMonopolyPrice b i) (Vickrey.highestOtherBid b i) *
      empiricalSingleItemMechanism.allocation b i =
    Vickrey.highestOtherBid b i * Vickrey.mechanism.allocation b i
  rw [hmax, halloc]

theorem empiricalSingleItemMechanism_isDSIC {ι : Type*} [Fintype ι] [LinearOrder ι] :
    (empiricalSingleItemMechanism (ι := ι)).IsDSIC :=
  Vickrey.mechanism_isDSIC.congr fun _ hb =>
    ⟨(empiricalSingleItemMechanism_allocation hb).symm,
      (empiricalSingleItemMechanism_payment hb).symm⟩

theorem empiricalSingleItemMechanism_isIR {ι : Type*} [Fintype ι] [LinearOrder ι] :
    (empiricalSingleItemMechanism (ι := ι)).IsIR :=
  Vickrey.mechanism_isIR.congr fun _ hb =>
    ⟨(empiricalSingleItemMechanism_allocation hb).symm,
      (empiricalSingleItemMechanism_payment hb).symm⟩

end EmpiricalMyerson

end Cslib.GameTheory.SingleParameter

