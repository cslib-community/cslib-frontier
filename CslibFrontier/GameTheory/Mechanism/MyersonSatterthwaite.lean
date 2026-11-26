/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Bayesian
public import CslibFrontier.GameTheory.Mechanism.VirtualValue
public import Mathlib.MeasureTheory.Measure.Prod
import CslibFrontier.Foundations.MeasureTheory.Integral.IntervalPrimitive
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The Myerson–Satterthwaite impossibility theorem

In bilateral trade, a buyer with private valuation `v_b` and a seller with private cost `v_s`
independently draw their types from distributions `μ_b` on `[a_b, b_b]` and `μ_s` on `[a_s, b_s]`.
A direct-revelation bilateral trade mechanism (`BilateralTrade.Mechanism`) maps reported types
`(v_b, v_s)` to a trade probability `trade v_b v_s` and expected transfers `buyerPayment v_b v_s`
(paid by the buyer) and `sellerPayment v_b v_s` (received by the seller). The buyer's quasilinear
utility is `v_b · q − p_b` and the seller's net utility over retaining the item is `p_s − v_s · q`.

The **Myerson–Satterthwaite impossibility theorem** ([MyersonSatterthwaite1983], Theorem 1; locator
not re-verified against primary PDF) states that whenever the supports have overlapping open
interiors (`max a_b a_s < min b_b b_s`) and positive densities on their interiors, no Bayesian
incentive-compatible (`IsBIC`), interim individually rational (`IsInterimIR`), ex-post efficient
(`IsExPostEfficient`) bilateral trade mechanism can be ex-ante weakly budget-balanced
(`IsExAnteBudgetBalanced`, i.e., `E[p_b − p_s] ≥ 0`).

The proof uses Myerson's interim revenue-equivalence identity on arbitrary intervals `[a, b]`
(derived from `SingleParameter.IsTruthfulOn.payment_eq` by translation) together with Fubini's
theorem on the upper/lower tails and the layer-cake identity for expected gains from trade:
for any atomless distributions supported on `[a_b, b_b]` and `[a_s, b_s]` with
`max a_b a_s ≤ min b_b b_s`, every BIC, ex-post efficient mechanism satisfies the exact identity
```
  E[p_b − p_s] + U_b(a_b) + U_s(b_s)
    = − ∫ t in (max a_b a_s, min b_b b_s], μ_b([t, ∞)) · μ_s((−∞, t]) dt.
```
When the densities are positive on `(a_b, b_b)` and `(a_s, b_s)` and `max a_b a_s < min b_b b_s`,
the integral on the right is strictly positive, so interim individual rationality
(`U_b(a_b) ≥ 0`, `U_s(b_s) ≥ 0`) forces strictly negative expected budget surplus
`E[p_b − p_s] < 0`. For independent `Uniform[0, 1]` types, the deficit is at least `1/6`
(`E[p_b − p_s] ≤ −1/6`).

Conversely, when the supports do not overlap (`b_s ≤ c ≤ a_b`), the posted-price mechanism
`BilateralTrade.fixedPrice c` is BIC, interim IR, ex-post efficient, and strictly budget-balanced
(`E[p_b − p_s] = 0`).

## Main definitions

* `BilateralTrade.HasValueDensityOn`: valuation distribution on `[a, b]` with interior-positive
  density `f`.
* `BilateralTrade.Mechanism`: bilateral trade allocation and transfer rules.
* `BilateralTrade.Mechanism.IsBIC`, `IsInterimIR`, `IsExPostEfficient`, `IsExAnteBudgetBalanced`.
* `BilateralTrade.fixedPrice`: posted-price trade mechanism at price `c`.

## Main results

* `BilateralTrade.Mechanism.IsBIC.budget_surplus_eq_of_isExPostEfficient`: exact budget surplus
  identity for atomless overlapping distributions.
* `BilateralTrade.Mechanism.not_isExAnteBudgetBalanced_of_hasValueDensityOn`:
  **Myerson–Satterthwaite impossibility theorem** for general positive-density distributions on
  overlapping intervals `[a_b, b_b]` and `[a_s, b_s]`.
* `BilateralTrade.Mechanism.budget_surplus_uniform_eq`,
  `BilateralTrade.Mechanism.budget_surplus_uniform_le_neg_one_sixth`,
  `BilateralTrade.Mechanism.not_isExAnteBudgetBalanced_uniform`: explicit `Uniform[0, 1]` deficit
  `−1/6`.
* `BilateralTrade.fixedPrice_isBIC_and_isInterimIR`,
  `BilateralTrade.fixedPrice_isExPostEfficient`, `BilateralTrade.fixedPrice_isExAnteBudgetBalanced`:
  feasibility on non-overlapping supports `b_s ≤ c ≤ a_b`.

## References

* [R. B. Myerson, M. A. Satterthwaite, *Efficient mechanisms for bilateral
  trading*][MyersonSatterthwaite1983]
* [R. B. Myerson, *Optimal auction design*][Myerson1981]
* [N. Nisan, *Introduction to Mechanism Design (for Computer Scientists)*][Nisan2007]
-/

open MeasureTheory Set

public section

namespace Cslib.GameTheory.BilateralTrade

/-! ### Value distributions on `[a, b]` -/

/-- `μ` is a valuation distribution on `[a, b]` with measurable density `f`, positive on the
open interior `(a, b)`. Generalizes `SingleParameter.HasValueDensity` from `[0, h]` to `[a, b]`. -/
structure HasValueDensityOn (μ : Measure ℝ) (f : ℝ → NNReal) (a b : ℝ) : Prop where
  /-- The density is measurable. -/
  measurable : Measurable f
  /-- `μ` is Lebesgue measure on `[a, b]` weighted by `f`. -/
  eq_withDensity : μ = (volume.restrict (Icc a b)).withDensity fun v => (f v : ENNReal)
  /-- The density is positive on the open interior `(a, b)`. -/
  pos : ∀ v ∈ Ioo a b, 0 < f v

/-- Every `SingleParameter.HasValueDensity μ f h` is a `HasValueDensityOn μ f 0 h`. -/
theorem hasValueDensityOn_of_hasValueDensity {μ : Measure ℝ} {f : ℝ → NNReal} {h : ℝ}
    (hμ : SingleParameter.HasValueDensity μ f h) : HasValueDensityOn μ f 0 h where
  measurable := hμ.measurable
  eq_withDensity := hμ.eq_withDensity
  pos := hμ.pos

namespace HasValueDensityOn

variable {μ : Measure ℝ} {f : ℝ → NNReal} {a b : ℝ}

theorem absolutelyContinuous (hμ : HasValueDensityOn μ f a b) : μ ≪ volume := by
  rw [hμ.eq_withDensity]
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- Almost every draw lies in `[a, b]`. -/
theorem ae_mem (hμ : HasValueDensityOn μ f a b) : ∀ᵐ v ∂μ, v ∈ Icc a b := by
  rw [hμ.eq_withDensity]
  exact (withDensity_absolutelyContinuous _ _) (ae_restrict_mem measurableSet_Icc)

/-- A distribution with a density has no atoms. -/
theorem nullSingletonClass (hμ : HasValueDensityOn μ f a b) : NullSingletonClass μ :=
  ⟨fun x => hμ.absolutelyContinuous (measure_singleton x)⟩

private theorem measure_Ioo_pos (hμ : HasValueDensityOn μ f a b) {c d : ℝ}
    (hac : a ≤ c) (hcd : c < d) (hdb : d ≤ b) : 0 < μ (Ioo c d) := by
  rw [hμ.eq_withDensity, withDensity_apply _ measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo,
    (inter_eq_left (s := Ioo c d) (t := Icc a b)).2 fun x hx =>
      ⟨hac.trans hx.1.le, hx.2.le.trans hdb⟩]
  refine (lintegral_pos_iff_support hμ.measurable.coe_nnreal_ennreal).2 ?_
  have hsupp : Ioo c d ⊆ Function.support (fun v => (f v : ENNReal)) := fun v hv =>
    ENNReal.coe_ne_zero.2 (hμ.pos v ⟨hac.trans_lt hv.1, hv.2.trans_le hdb⟩).ne'
  refine (lt_of_lt_of_eq (ENNReal.ofReal_pos.2 (sub_pos.2 hcd)) ?_).trans_le (measure_mono hsupp)
  rw [Measure.restrict_apply measurableSet_Ioo, inter_self, Real.volume_Ioo]

/-- Every interior point `t ∈ (a, b)` has strictly positive upper tail `μ([t, ∞)) > 0`. -/
theorem measureReal_Ici_pos [IsFiniteMeasure μ] (hμ : HasValueDensityOn μ f a b)
    {t : ℝ} (ht : t ∈ Ioo a b) : 0 < μ.real (Ici t) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (((hμ.measure_Ioo_pos ht.1.le ht.2 le_rfl).trans_le
    (measure_mono fun _ hx => hx.1.le)).ne') (measure_ne_top μ _)

/-- Every interior point `t ∈ (a, b)` has strictly positive lower tail `μ((−∞, t]) > 0`. -/
theorem measureReal_Iic_pos [IsFiniteMeasure μ] (hμ : HasValueDensityOn μ f a b)
    {t : ℝ} (ht : t ∈ Ioo a b) : 0 < μ.real (Iic t) := by
  rw [measureReal_def]
  exact ENNReal.toReal_pos (((hμ.measure_Ioo_pos le_rfl ht.1 ht.2.le).trans_le
    (measure_mono fun _ hx => hx.2.le)).ne') (measure_ne_top μ _)

end HasValueDensityOn

/-! ### Bilateral trade mechanisms -/

/-- A direct-revelation **bilateral trade mechanism**: given reported buyer valuation `v_b` and
seller cost `v_s`, it chooses a trade probability `trade v_b v_s`, charges the buyer
`buyerPayment v_b v_s`, and pays the seller `sellerPayment v_b v_s`. -/
structure Mechanism where
  /-- Probability (or quantity) of trade `q(v_b, v_s)`. -/
  trade : ℝ → ℝ → ℝ
  /-- Expected payment from the buyer `p_b(v_b, v_s)`. -/
  buyerPayment : ℝ → ℝ → ℝ
  /-- Expected payment to the seller `p_s(v_b, v_s)`. -/
  sellerPayment : ℝ → ℝ → ℝ

namespace Mechanism

/-- The buyer's interim trade probability `Q_b(v_b) = E_{v_s}[q(v_b, v_s)]`. -/
@[expose] noncomputable def interimBuyerTrade (M : Mechanism) (μ_s : Measure ℝ) (v_b : ℝ) : ℝ :=
  ∫ v_s, M.trade v_b v_s ∂μ_s

/-- The buyer's interim expected payment `P_b(v_b) = E_{v_s}[p_b(v_b, v_s)]`. -/
@[expose] noncomputable def interimBuyerPayment (M : Mechanism) (μ_s : Measure ℝ) (v_b : ℝ) : ℝ :=
  ∫ v_s, M.buyerPayment v_b v_s ∂μ_s

/-- The buyer's interim expected utility `U_b(v_b) = v_b Q_b(v_b) − P_b(v_b)`. -/
@[expose] noncomputable def interimBuyerUtility (M : Mechanism) (μ_s : Measure ℝ) (v_b : ℝ) : ℝ :=
  v_b * M.interimBuyerTrade μ_s v_b - M.interimBuyerPayment μ_s v_b

/-- The seller's interim trade probability `Q_s(v_s) = E_{v_b}[q(v_b, v_s)]`. -/
@[expose] noncomputable def interimSellerTrade (M : Mechanism) (μ_b : Measure ℝ) (v_s : ℝ) : ℝ :=
  ∫ v_b, M.trade v_b v_s ∂μ_b

/-- The seller's interim expected payment received `P_s(v_s) = E_{v_b}[p_s(v_b, v_s)]`. -/
@[expose] noncomputable def interimSellerPayment (M : Mechanism) (μ_b : Measure ℝ) (v_s : ℝ) : ℝ :=
  ∫ v_b, M.sellerPayment v_b v_s ∂μ_b

/-- The seller's interim expected net utility `U_s(v_s) = P_s(v_s) − v_s Q_s(v_s)`. -/
@[expose] noncomputable def interimSellerUtility (M : Mechanism) (μ_b : Measure ℝ) (v_s : ℝ) : ℝ :=
  M.interimSellerPayment μ_b v_s - v_s * M.interimSellerTrade μ_b v_s

/-- **Bayesian incentive compatibility (BIC)** on buyer types `[a_b, b_b]` and seller types
`[a_s, b_s]`: truthful reporting maximizes both agents' interim expected utilities. -/
@[expose] def IsBIC (M : Mechanism) (μ_b μ_s : Measure ℝ) (a_b b_b a_s b_s : ℝ) : Prop :=
  SingleParameter.IsTruthfulOn (M.interimBuyerTrade μ_s) (M.interimBuyerPayment μ_s)
      (Icc a_b b_b) ∧
    ∀ v ∈ Icc a_s b_s, ∀ w ∈ Icc a_s b_s,
      M.interimSellerPayment μ_b w - v * M.interimSellerTrade μ_b w ≤
        M.interimSellerPayment μ_b v - v * M.interimSellerTrade μ_b v

/-- **Interim individual rationality (IR)**: every buyer type in `[a_b, b_b]` and every seller type
in `[a_s, b_s]` obtains nonnegative interim expected utility from truthful participation. -/
@[expose] def IsInterimIR (M : Mechanism) (μ_b μ_s : Measure ℝ) (a_b b_b a_s b_s : ℝ) : Prop :=
  (∀ v_b ∈ Icc a_b b_b, 0 ≤ M.interimBuyerUtility μ_s v_b) ∧
    (∀ v_s ∈ Icc a_s b_s, 0 ≤ M.interimSellerUtility μ_b v_s)

/-- **Ex-post efficiency**: trade takes place with probability `1` whenever `v_s < v_b` and with
probability `0` whenever `v_b < v_s`. Tie-breaking on the diagonal `v_b = v_s` is unrestricted. -/
@[expose] def IsExPostEfficient (M : Mechanism) : Prop :=
  ∀ v_b v_s, (v_s < v_b → M.trade v_b v_s = 1) ∧ (v_b < v_s → M.trade v_b v_s = 0)

/-- **Ex-ante weak budget balance**: the expected budget surplus `E[p_b − p_s]` is nonnegative
(the mechanism does not require an outside subsidy in expectation). -/
@[expose] def IsExAnteBudgetBalanced (M : Mechanism) (μ_b μ_s : Measure ℝ) : Prop :=
  0 ≤ ∫ p, (M.buyerPayment p.1 p.2 - M.sellerPayment p.1 p.2) ∂(μ_b.prod μ_s)

/-! ### Shifted interval payment identities and Fubini tail formulas -/

/-- Payment identity on an arbitrary closed interval `[a, b]`: derived from
`SingleParameter.IsTruthfulOn.payment_eq` by translating `v ↦ v − a`. -/
private theorem isTruthfulOn_utility_eq {X P : ℝ → ℝ} {a b v : ℝ}
    (hT : SingleParameter.IsTruthfulOn X P (Icc a b)) (hv : v ∈ Icc a b) :
    v * X v - P v = (a * X a - P a) + ∫ t in a..v, X t := by
  let X' : ℝ → ℝ := fun u => X (a + u)
  let P' : ℝ → ℝ := fun u => P (a + u) - a * X (a + u)
  have hT' : SingleParameter.IsTruthfulOn X' P' (Icc 0 (b - a)) := fun u hu w hw => by
    have hu' : a + u ∈ Icc a b := ⟨le_add_of_nonneg_right hu.1, le_sub_iff_add_le'.1 hu.2⟩
    have hw' : a + w ∈ Icc a b := ⟨le_add_of_nonneg_right hw.1, le_sub_iff_add_le'.1 hw.2⟩
    have h := hT (a + u) hu' (a + w) hw'
    simp only [X', P']
    linarith
  have hpay := hT'.payment_eq (v := v - a) ⟨sub_nonneg.2 hv.1, sub_le_sub_right hv.2 a⟩
  simp only [X', P', add_zero, add_sub_cancel, intervalIntegral.integral_comp_add_left] at hpay
  linarith

/-- Seller interim utility identity on `[a_s, b_s]`:
`U_s(v) = U_s(b_s) + ∫ t in v..b_s, Q_s(t)`. -/
private theorem IsBIC.interimSellerUtility_eq {M : Mechanism} {μ_b μ_s : Measure ℝ}
    {a_b b_b a_s b_s v : ℝ} (hBIC : M.IsBIC μ_b μ_s a_b b_b a_s b_s) (hv : v ∈ Icc a_s b_s) :
    M.interimSellerUtility μ_b v =
      M.interimSellerUtility μ_b b_s + ∫ t in v..b_s, M.interimSellerTrade μ_b t := by
  have hT : SingleParameter.IsTruthfulOn (fun t => -M.interimSellerTrade μ_b t)
      (fun t => -M.interimSellerPayment μ_b t) (Icc a_s b_s) := by
    intro x hx y hy
    have h := hBIC.2 x hx y hy
    linarith
  have hU_v := isTruthfulOn_utility_eq hT hv
  have hU_b := isTruthfulOn_utility_eq hT ⟨hv.1.trans hv.2, le_rfl⟩
  have hmono : MonotoneOn (fun t => -M.interimSellerTrade μ_b t) (Icc a_s b_s) := hT.monotoneOn
  have hi1 : IntervalIntegrable (fun t => -M.interimSellerTrade μ_b t) volume a_s v :=
    (hmono.mono fun t ht => by
      rw [uIcc_of_le hv.1] at ht; exact ⟨ht.1, ht.2.trans hv.2⟩).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t => -M.interimSellerTrade μ_b t) volume v b_s :=
    (hmono.mono fun t ht => by
      rw [uIcc_of_le hv.2] at ht; exact ⟨hv.1.trans ht.1, ht.2⟩).intervalIntegrable
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
  simp only [intervalIntegral.integral_neg] at hsplit hU_v hU_b
  simp only [interimSellerUtility]
  linarith

/-- Buyer interim utility identity on `[a_b, b_b]`:
`U_b(v) = U_b(a_b) + ∫ t in a_b..v, Q_b(t)`. -/
private theorem IsBIC.interimBuyerUtility_eq {M : Mechanism} {μ_b μ_s : Measure ℝ}
    {a_b b_b a_s b_s v : ℝ} (hBIC : M.IsBIC μ_b μ_s a_b b_b a_s b_s) (hv : v ∈ Icc a_b b_b) :
    M.interimBuyerUtility μ_s v =
      M.interimBuyerUtility μ_s a_b + ∫ t in a_b..v, M.interimBuyerTrade μ_s t :=
  isTruthfulOn_utility_eq hBIC.1 hv

/-- Upper-tail Fubini formula on `[a, b]`:
`∫ v, (∫ t in a..v, g t) ∂μ = ∫ t in Ioc a b, μ.real (Ici t) * g t`. -/
private theorem integral_intervalIntegral_left_eq {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hμ : ∀ᵐ v ∂μ, v ∈ Icc a b) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc a b)) :
    ∫ v, (∫ t in a..v, g t) ∂μ = ∫ t in Ioc a b, μ.real (Ici t) * g t := by
  set S : Set (ℝ × ℝ) := {p | p.2 ≤ p.1}
  have hSm : MeasurableSet S := measurableSet_le measurable_snd measurable_fst
  set G : ℝ × ℝ → ℝ := S.indicator (fun p => g p.2)
  have hGint : Integrable G (μ.prod (volume.restrict (Ioc a b))) := (hg.comp_snd μ).indicator hSm
  have hL : ∀ᵐ v ∂μ, ∫ t in Ioc a b, G (v, t) = ∫ t in a..v, g t := by
    filter_upwards [hμ] with v hv
    have hfun : (fun t => G (v, t)) = (Iic v).indicator g :=
      funext fun t => by simp [G, S, indicator_apply]
    have hset : Iic v ∩ Ioc a b = Ioc a v := by
      ext t
      exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans hv.2⟩⟩
    rw [hfun, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      hset, intervalIntegral.integral_of_le hv.1]
  have hR : ∀ t, ∫ v, G (v, t) ∂μ = μ.real (Ici t) * g t := fun t => by
    have hfun : (fun v => G (v, t)) = (Ici t).indicator (fun _ => g t) :=
      funext fun v => by simp [G, S, indicator_apply]
    rw [hfun, integral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul]
  rw [← integral_congr_ae hL,
    integral_integral_swap (μ := μ) (ν := volume.restrict (Ioc a b)) (f := fun v t => G (v, t))
      hGint]
  exact setIntegral_congr_fun measurableSet_Ioc fun t _ => hR t

/-- Lower-tail Fubini formula on `[a, b]`:
`∫ v, (∫ t in v..b, g t) ∂μ = ∫ t in Ioc a b, μ.real (Iic t) * g t`. -/
private theorem integral_intervalIntegral_right_eq {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} (hμ : ∀ᵐ v ∂μ, v ∈ Icc a b) {g : ℝ → ℝ} (hg : IntegrableOn g (Ioc a b)) :
    ∫ v, (∫ t in v..b, g t) ∂μ = ∫ t in Ioc a b, μ.real (Iic t) * g t := by
  set S : Set (ℝ × ℝ) := {p | p.1 ≤ p.2}
  have hSm : MeasurableSet S := measurableSet_le measurable_fst measurable_snd
  set G : ℝ × ℝ → ℝ := S.indicator (fun p => g p.2)
  have hGint : Integrable G (μ.prod (volume.restrict (Ioc a b))) := (hg.comp_snd μ).indicator hSm
  have hL : ∀ᵐ v ∂μ, ∫ t in Ioc a b, G (v, t) = ∫ t in v..b, g t := by
    filter_upwards [hμ] with v hv
    have hfun : (fun t => G (v, t)) = (Ici v).indicator g :=
      funext fun t => by simp [G, S, indicator_apply]
    rw [hfun, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
      intervalIntegral.integral_of_le hv.2]
    rcases eq_or_lt_of_le hv.1 with rfl | hav
    · rw [inter_eq_right.2 fun t (ht : t ∈ Ioc a b) => ht.1.le]
    · have hset : Ici v ∩ Ioc a b = Icc v b := by
        ext t
        exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, hav.trans_le h1, h2⟩⟩
      rw [hset, integral_Icc_eq_integral_Ioc]
  have hR : ∀ t, ∫ v, G (v, t) ∂μ = μ.real (Iic t) * g t := fun t => by
    have hfun : (fun v => G (v, t)) = (Iic t).indicator (fun _ => g t) :=
      funext fun v => by simp [G, S, indicator_apply]
    rw [hfun, integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul]
  rw [← integral_congr_ae hL,
    integral_integral_swap (μ := μ) (ν := volume.restrict (Ioc a b)) (f := fun v t => G (v, t))
      hGint]
  exact setIntegral_congr_fun measurableSet_Ioc fun t _ => hR t

/-- Layer-cake identity for expected gains from trade:
`E[(v_b − v_s) · 1_{v_s ≤ v_b}] = ∫_{min a_b a_s}^{max b_b b_s} μ_b([t, ∞)) · μ_s((−∞, t]) dt`. -/
private theorem integral_gains_from_trade {μ_b μ_s : Measure ℝ}
    [IsProbabilityMeasure μ_b] [IsProbabilityMeasure μ_s] {a_b b_b a_s b_s : ℝ}
    (hb : ∀ᵐ v ∂μ_b, v ∈ Icc a_b b_b) (hs : ∀ᵐ v ∂μ_s, v ∈ Icc a_s b_s) :
    ∫ p : ℝ × ℝ, (if p.2 ≤ p.1 then p.1 - p.2 else 0) ∂(μ_b.prod μ_s) =
      ∫ t in Ioc (min a_b a_s) (max b_b b_s), μ_b.real (Ici t) * μ_s.real (Iic t) := by
  set L := min a_b a_s
  set U := max b_b b_s
  set S : Set ((ℝ × ℝ) × ℝ) := {q | q.1.2 ≤ q.2 ∧ q.2 ≤ q.1.1}
  have hSm : MeasurableSet S :=
    (measurableSet_le (measurable_snd.comp measurable_fst) measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  set G : (ℝ × ℝ) × ℝ → ℝ := S.indicator 1 with hG
  have hGint : Integrable G ((μ_b.prod μ_s).prod (volume.restrict (Ioc L U))) :=
    Integrable.of_bound (measurable_const.indicator hSm).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun q => by
        simp only [hG, indicator_apply, Pi.one_apply]
        split_ifs <;> norm_num)
  have hL : ∀ᵐ p ∂(μ_b.prod μ_s),
      ∫ t in Ioc L U, G (p, t) = if p.2 ≤ p.1 then p.1 - p.2 else 0 := by
    have hbox : ∀ᵐ p ∂(μ_b.prod μ_s), p.1 ∈ Icc a_b b_b ∧ p.2 ∈ Icc a_s b_s :=
      ((Measure.quasiMeasurePreserving_fst (μ := μ_b) (ν := μ_s)).ae hb).and
        ((Measure.quasiMeasurePreserving_snd (μ := μ_b) (ν := μ_s)).ae hs)
    filter_upwards [hbox] with p ⟨hp1, hp2⟩
    by_cases hle : p.2 ≤ p.1
    · rw [ite_eq_left hle]
      have hfun : (fun t => G (p, t)) = (Icc p.2 p.1).indicator 1 := by
        ext t
        simp only [hG, S, indicator_apply, mem_ofPred_eq, mem_Icc, Pi.one_apply]
      have hdiff : Icc p.2 p.1 \ (Icc p.2 p.1 ∩ Ioc L U) ⊆ {L} := fun t ⟨ht1, ht2⟩ => by
        rcases eq_or_lt_of_le ((min_le_right a_b a_s).trans (hp2.1.trans ht1.1)) with hEq | hLt
        · exact hEq.symm
        · exact absurd ⟨ht1, hLt, ht1.2.trans (hp1.2.trans (le_max_left b_b b_s))⟩ ht2
      rw [hfun, integral_indicator_one measurableSet_Icc, measureReal_def,
        Measure.restrict_apply measurableSet_Icc, measure_eq_measure_of_null_sdiff
          inter_subset_left (measure_mono_null hdiff Real.volume_singleton),
        Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hle)]
    · rw [ite_eq_right hle]
      have hfun : (fun t => G (p, t)) = fun _ => 0 :=
        funext fun t => indicator_of_notMem (fun h : (p, t) ∈ S => hle (h.1.trans h.2)) _
      rw [hfun, integral_zero]
  have hR : ∀ t, ∫ p, G (p, t) ∂(μ_b.prod μ_s) = μ_b.real (Ici t) * μ_s.real (Iic t) := fun t => by
    have hfun : (fun p : ℝ × ℝ => G (p, t)) = (Ici t ×ˢ Iic t).indicator 1 := by
      ext p
      simp only [hG, S, indicator_apply, mem_ofPred_eq, mem_prod, mem_Ici, mem_Iic,
        and_comm, Pi.one_apply]
    rw [hfun, integral_indicator_one (measurableSet_Ici.prod measurableSet_Iic),
      measureReal_def, Measure.prod_prod, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def]
  rw [← integral_congr_ae hL,
    integral_integral_swap (μ := μ_b.prod μ_s) (ν := volume.restrict (Ioc L U))
      (f := fun p t => G (p, t)) hGint]
  exact setIntegral_congr_fun measurableSet_Ioc fun t _ => hR t

/-! ### Exact budget surplus identity and Myerson–Satterthwaite impossibility -/

/-- Under atomless `μ_s` and ex-post efficiency, the buyer's interim trade probability is
`Q_b(v_b) = μ_s((−∞, v_b])`. -/
private theorem IsExPostEfficient.interimBuyerTrade_eq {M : Mechanism} {μ_s : Measure ℝ}
    [NullSingletonClass μ_s] (heff : M.IsExPostEfficient) (v_b : ℝ) :
    M.interimBuyerTrade μ_s v_b = μ_s.real (Iic v_b) := by
  have hae : (fun v_s => M.trade v_b v_s) =ᵐ[μ_s] (Iic v_b).indicator 1 := by
    have hne : ∀ᵐ v_s ∂μ_s, v_s ≠ v_b := by
      rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
    filter_upwards [hne] with v_s hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [(heff v_b v_s).1 hlt, indicator_of_mem (s := Iic v_b) hlt.le, Pi.one_apply]
    · rw [(heff v_b v_s).2 hgt, indicator_of_notMem (s := Iic v_b) (not_le.2 hgt)]
  rw [interimBuyerTrade, integral_congr_ae hae, integral_indicator_one measurableSet_Iic]

/-- Under atomless `μ_b` and ex-post efficiency, the seller's interim trade probability is
`Q_s(v_s) = μ_b([v_s, ∞))`. -/
private theorem IsExPostEfficient.interimSellerTrade_eq {M : Mechanism} {μ_b : Measure ℝ}
    [NullSingletonClass μ_b] (heff : M.IsExPostEfficient) (v_s : ℝ) :
    M.interimSellerTrade μ_b v_s = μ_b.real (Ici v_s) := by
  have hae : (fun v_b => M.trade v_b v_s) =ᵐ[μ_b] (Ici v_s).indicator 1 := by
    have hne : ∀ᵐ v_b ∂μ_b, v_b ≠ v_s := by
      rw [ae_iff]; simp only [ne_eq, not_not, ofPred_eq_eq_singleton, measure_singleton]
    filter_upwards [hne] with v_b hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [(heff v_b v_s).2 hlt, indicator_of_notMem (s := Ici v_s) (not_le.2 hlt)]
    · rw [(heff v_b v_s).1 hgt, indicator_of_mem (s := Ici v_s) hgt.le, Pi.one_apply]
  rw [interimSellerTrade, integral_congr_ae hae, integral_indicator_one measurableSet_Ici]

private theorem measurable_measureReal_Iic (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable fun t => μ.real (Iic t) :=
  Monotone.measurable fun _ _ h => measureReal_mono (Iic_subset_Iic.2 h)

private theorem measurable_measureReal_Ici (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Measurable fun t => μ.real (Ici t) :=
  Antitone.measurable fun _ _ h => measureReal_mono (Ici_subset_Ici.2 h)

private theorem integrableOn_Ioc_of_unit {f : ℝ → ℝ} (hf : Measurable f)
    (h0 : ∀ t, 0 ≤ f t) (h1 : ∀ t, f t ≤ 1) (a b : ℝ) : IntegrableOn f (Ioc a b) :=
  Integrable.of_bound hf.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 t)]
    exact h1 t)

private theorem abs_le_max_of_mem_Icc {a b v : ℝ} (hv : v ∈ Icc a b) :
    |v| ≤ max |a| |b| :=
  abs_le.2 ⟨by linarith [neg_le_abs a, le_max_left |a| |b|, hv.1],
    hv.2.trans ((le_abs_self b).trans (le_max_right |a| |b|))⟩

private theorem integrableOn_Ici_mul_Iic (μ_b μ_s : Measure ℝ)
    [IsProbabilityMeasure μ_b] [IsProbabilityMeasure μ_s] (c d : ℝ) :
    IntegrableOn (fun t => μ_b.real (Ici t) * μ_s.real (Iic t)) (Ioc c d) :=
  integrableOn_Ioc_of_unit
    ((measurable_measureReal_Ici μ_b).mul (measurable_measureReal_Iic μ_s))
    (fun _ => mul_nonneg measureReal_nonneg measureReal_nonneg)
    (fun _ => (mul_le_of_le_one_right measureReal_nonneg measureReal_le_one).trans
      measureReal_le_one)
    c d

/-- **Exact budget surplus identity for ex-post efficient bilateral trade**
([MyersonSatterthwaite1983], Theorem 1; locator not re-verified against primary PDF): for
independent atomless probability measures `μ_b` supported on `[a_b, b_b]` and `μ_s` supported on
`[a_s, b_s]` with `max a_b a_s ≤ min b_b b_s`, every BIC, ex-post efficient mechanism with
integrable payments satisfies
`E[p_b − p_s] + U_b(a_b) + U_s(b_s) = − ∫_{max a_b a_s}^{min b_b b_s} μ_b([t, ∞)) μ_s((−∞, t])`. -/
theorem IsBIC.budget_surplus_eq_of_isExPostEfficient {M : Mechanism}
    {μ_b μ_s : Measure ℝ} [IsProbabilityMeasure μ_b] [IsProbabilityMeasure μ_s]
    [NullSingletonClass μ_b] [NullSingletonClass μ_s] {a_b b_b a_s b_s : ℝ}
    (hb_supp : ∀ᵐ v ∂μ_b, v ∈ Icc a_b b_b) (hs_supp : ∀ᵐ v ∂μ_s, v ∈ Icc a_s b_s)
    (hover : max a_b a_s ≤ min b_b b_s)
    (hBIC : M.IsBIC μ_b μ_s a_b b_b a_s b_s) (heff : M.IsExPostEfficient)
    (hpb : Integrable (Function.uncurry M.buyerPayment) (μ_b.prod μ_s))
    (hps : Integrable (Function.uncurry M.sellerPayment) (μ_b.prod μ_s)) :
    ∫ p, (M.buyerPayment p.1 p.2 - M.sellerPayment p.1 p.2) ∂(μ_b.prod μ_s) +
      M.interimBuyerUtility μ_s a_b + M.interimSellerUtility μ_b b_s =
      - ∫ t in Ioc (max a_b a_s) (min b_b b_s), μ_b.real (Ici t) * μ_s.real (Iic t) := by
  have hm_Fs : Measurable fun t => μ_s.real (Iic t) := measurable_measureReal_Iic μ_s
  have hm_Fb : Measurable fun t => μ_b.real (Ici t) := measurable_measureReal_Ici μ_b
  have hFs_int : IntegrableOn (fun t => μ_s.real (Iic t)) (Ioc a_b b_b) :=
    integrableOn_Ioc_of_unit hm_Fs (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
      a_b b_b
  have hFb_int : IntegrableOn (fun t => μ_b.real (Ici t)) (Ioc a_s b_s) :=
    integrableOn_Ioc_of_unit hm_Fb (fun _ => measureReal_nonneg) (fun _ => measureReal_le_one)
      a_s b_s
  -- Buyer expected payment: E[p_b] = E[v_b 1_{v_s ≤ v_b}] - U_b(a_b) - ∫_{a_b}^{b_b} (1-F_b) F_s
  have hEb : ∫ p, M.buyerPayment p.1 p.2 ∂(μ_b.prod μ_s) =
      (∫ v_b, v_b * μ_s.real (Iic v_b) ∂μ_b) - M.interimBuyerUtility μ_s a_b -
        ∫ t in Ioc a_b b_b, μ_b.real (Ici t) * μ_s.real (Iic t) := by
    rw [integral_prod (f := fun p : ℝ × ℝ => M.buyerPayment p.1 p.2) hpb]
    have hPae : (fun v_b => M.interimBuyerPayment μ_s v_b) =ᵐ[μ_b]
        fun v_b => (v_b * μ_s.real (Iic v_b) - M.interimBuyerUtility μ_s a_b) -
          ∫ t in a_b..v_b, μ_s.real (Iic t) := by
      filter_upwards [hb_supp] with v_b hv
      have hu := hBIC.interimBuyerUtility_eq hv
      rw [interimBuyerUtility, heff.interimBuyerTrade_eq v_b,
        intervalIntegral.integral_congr fun t _ => heff.interimBuyerTrade_eq t] at hu
      linarith
    have hi1 : Integrable (fun v_b => v_b * μ_s.real (Iic v_b)) μ_b :=
      Integrable.of_bound (measurable_id.mul hm_Fs).aestronglyMeasurable (max |a_b| |b_b|)
        (hb_supp.mono fun v_b hv => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
          exact (mul_le_of_le_one_right (abs_nonneg _) measureReal_le_one).trans
            (abs_le_max_of_mem_Icc hv))
    have hi2 : Integrable (fun v_b => ∫ t in a_b..v_b, μ_s.real (Iic t)) μ_b := by
      refine Integrable.of_bound
        (MeasureTheory.measurable_intervalIntegral (G := fun (_ : ℝ) t => μ_s.real (Iic t))
          (hm_Fs.comp measurable_snd) measurable_const measurable_id).aestronglyMeasurable
        (max (b_b - a_b) 0) ?_
      filter_upwards [hb_supp] with v_b hv
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) fun t _ => ?_).trans ?_
      · simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using measureReal_le_one
      · simpa only [one_mul, abs_of_nonneg (sub_nonneg.2 hv.1)] using
          (sub_le_sub_right hv.2 a_b).trans (le_max_left _ _)
    have hi1' : Integrable
        (fun v_b => v_b * μ_s.real (Iic v_b) - M.interimBuyerUtility μ_s a_b) μ_b :=
      hi1.sub (integrable_const _)
    change ∫ v_b, M.interimBuyerPayment μ_s v_b ∂μ_b = _
    rw [integral_congr_ae hPae, integral_sub hi1' hi2,
      integral_sub hi1 (integrable_const _), integral_const, probReal_univ, one_smul,
      integral_intervalIntegral_left_eq hb_supp hFs_int]
  -- Seller expected payment: E[p_s] = E[v_s 1_{v_s ≤ v_b}] + U_s(b_s) + ∫_{a_s}^{b_s} F_s (1-F_b)
  have hEs : ∫ p, M.sellerPayment p.1 p.2 ∂(μ_b.prod μ_s) =
      (∫ v_s, v_s * μ_b.real (Ici v_s) ∂μ_s) + M.interimSellerUtility μ_b b_s +
        ∫ t in Ioc a_s b_s, μ_b.real (Ici t) * μ_s.real (Iic t) := by
    rw [integral_prod_symm (f := fun p : ℝ × ℝ => M.sellerPayment p.1 p.2) hps]
    have hPae : (fun v_s => M.interimSellerPayment μ_b v_s) =ᵐ[μ_s]
        fun v_s => (v_s * μ_b.real (Ici v_s) + M.interimSellerUtility μ_b b_s) +
          ∫ t in v_s..b_s, μ_b.real (Ici t) := by
      filter_upwards [hs_supp] with v_s hv
      have hu := hBIC.interimSellerUtility_eq hv
      rw [interimSellerUtility, heff.interimSellerTrade_eq v_s,
        intervalIntegral.integral_congr fun t _ => heff.interimSellerTrade_eq t] at hu
      linarith
    have hi1 : Integrable (fun v_s => v_s * μ_b.real (Ici v_s)) μ_s :=
      Integrable.of_bound (measurable_id.mul hm_Fb).aestronglyMeasurable (max |a_s| |b_s|)
        (hs_supp.mono fun v_s hv => by
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg measureReal_nonneg]
          exact (mul_le_of_le_one_right (abs_nonneg _) measureReal_le_one).trans
            (abs_le_max_of_mem_Icc hv))
    have hi2 : Integrable (fun v_s => ∫ t in v_s..b_s, μ_b.real (Ici t)) μ_s := by
      refine Integrable.of_bound
        (MeasureTheory.measurable_intervalIntegral (G := fun (_ : ℝ) t => μ_b.real (Ici t))
          (hm_Fb.comp measurable_snd) measurable_id measurable_const).aestronglyMeasurable
        (max (b_s - a_s) 0) ?_
      filter_upwards [hs_supp] with v_s hv
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 1) fun t _ => ?_).trans ?_
      · simpa only [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg] using measureReal_le_one
      · simpa only [one_mul, abs_of_nonneg (sub_nonneg.2 hv.2)] using
          (sub_le_sub_left hv.1 b_s).trans (le_max_left _ _)
    have hi1' : Integrable
        (fun v_s => v_s * μ_b.real (Ici v_s) + M.interimSellerUtility μ_b b_s) μ_s :=
      hi1.add (integrable_const _)
    change ∫ v_s, M.interimSellerPayment μ_b v_s ∂μ_s = _
    rw [integral_congr_ae hPae, integral_add hi1' hi2,
      integral_add hi1 (integrable_const _), integral_const, probReal_univ, one_smul,
      integral_intervalIntegral_right_eq hs_supp hFb_int]
    exact congrArg (_ + ·) (setIntegral_congr_fun measurableSet_Ioc fun _ _ => mul_comm _ _)
  -- Relate E[v_b 1_{v_s ≤ v_b}] - E[v_s 1_{v_s ≤ v_b}] to expected gains from trade
  have hGFT : (∫ v_b, v_b * μ_s.real (Iic v_b) ∂μ_b) - (∫ v_s, v_s * μ_b.real (Ici v_s) ∂μ_s) =
      ∫ t in Ioc (min a_b a_s) (max b_b b_s), μ_b.real (Ici t) * μ_s.real (Iic t) := by
    have hsm : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
      measurableSet_le measurable_snd measurable_fst
    have hint_ite {f : ℝ × ℝ → ℝ} {a b : ℝ} (hf : Measurable f)
        (hsupp : ∀ᵐ p ∂(μ_b.prod μ_s), f p ∈ Icc a b) :
        Integrable (fun p : ℝ × ℝ => if p.2 ≤ p.1 then f p else 0) (μ_b.prod μ_s) := by
      refine Integrable.of_bound (Measurable.ite hsm hf measurable_const).aestronglyMeasurable
        (max |a| |b|) (hsupp.mono fun p hp => ?_)
      split_ifs
      · simpa only [Real.norm_eq_abs] using abs_le_max_of_mem_Icc hp
      · simp only [norm_zero, le_max_iff, abs_nonneg, or_self]
    have h1int := hint_ite measurable_fst
      ((Measure.quasiMeasurePreserving_fst (μ := μ_b) (ν := μ_s)).ae hb_supp)
    have h2int := hint_ite measurable_snd
      ((Measure.quasiMeasurePreserving_snd (μ := μ_b) (ν := μ_s)).ae hs_supp)
    have h1eq : ∫ p : ℝ × ℝ, (if p.2 ≤ p.1 then p.1 else 0) ∂(μ_b.prod μ_s) =
        ∫ v_b, v_b * μ_s.real (Iic v_b) ∂μ_b := by
      rw [integral_prod _ h1int]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v_b => ?_)
      dsimp only
      have h : (fun v_s => if v_s ≤ v_b then v_b else 0) = (Iic v_b).indicator (fun _ => v_b) :=
        funext fun _ => by simp [indicator_apply]
      rw [h, integral_indicator measurableSet_Iic, setIntegral_const, smul_eq_mul, mul_comm]
    have h2eq : ∫ p : ℝ × ℝ, (if p.2 ≤ p.1 then p.2 else 0) ∂(μ_b.prod μ_s) =
        ∫ v_s, v_s * μ_b.real (Ici v_s) ∂μ_s := by
      rw [integral_prod_symm _ h2int]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v_s => ?_)
      dsimp only
      have h : (fun v_b => if v_s ≤ v_b then v_s else 0) = (Ici v_s).indicator (fun _ => v_s) :=
        funext fun _ => by simp [indicator_apply]
      rw [h, integral_indicator measurableSet_Ici, setIntegral_const, smul_eq_mul, mul_comm]
    rw [← h1eq, ← h2eq, ← integral_sub h1int h2int]
    have hsub : (fun p : ℝ × ℝ => (if p.2 ≤ p.1 then p.1 else 0) -
        (if p.2 ≤ p.1 then p.2 else 0)) = fun p => if p.2 ≤ p.1 then p.1 - p.2 else 0 :=
      funext fun p => by split_ifs <;> ring
    rw [hsub, integral_gains_from_trade hb_supp hs_supp]
  -- Combine the three integrals over Ioc (min a_b a_s) (max b_b b_s)
  set L := min a_b a_s
  set U := max b_b b_s
  set g : ℝ → ℝ := fun t => μ_b.real (Ici t) * μ_s.real (Iic t)
  have hg_int : IntegrableOn g (Ioc L U) := integrableOn_Ici_mul_Iic μ_b μ_s L U
  have hI {c d : ℝ} (hsub : Ioc c d ⊆ Ioc L U) :
      ∫ t in Ioc c d, g t = ∫ t in Ioc L U, (Ioc c d).indicator g t := by
    rw [integral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.2 hsub]
  have hpt : ∀ t ∈ Ioc L U,
      g t - (Ioc a_b b_b).indicator g t - (Ioc a_s b_s).indicator g t =
        - (Ioc (max a_b a_s) (min b_b b_s)).indicator g t := by
    intro t _
    by_cases hta : t ≤ a_s
    · have h0 : μ_s (Iic t) = 0 :=
        measure_mono_null (fun v hv => lt_or_eq_of_le (hv.trans hta))
          (measure_union_null (measure_mono_null (s := Iio a_s) (t := {v | v ∉ Icc a_s b_s})
            (fun v hv hv' => not_lt.2 hv'.1 hv) (ae_iff.1 hs_supp)) (measure_singleton a_s))
      simp only [g, indicator_apply, measureReal_def, h0, ENNReal.toReal_zero, mul_zero,
        ite_self, sub_zero, neg_zero]
    · push Not at hta
      by_cases htb : b_b < t
      · have h0 : μ_b (Ici t) = 0 :=
          measure_mono_null (t := {v | v ∉ Icc a_b b_b})
            (fun v (hv : t ≤ v) hv' => not_lt.2 hv'.2 (htb.trans_le hv)) (ae_iff.1 hb_supp)
        simp only [g, indicator_apply, measureReal_def, h0, ENNReal.toReal_zero, zero_mul,
          ite_self, sub_zero, neg_zero]
      · push Not at htb
        by_cases h1 : a_b < t <;> by_cases h2 : t ≤ b_s
        · rw [indicator_of_mem (s := Ioc a_b b_b) ⟨h1, htb⟩,
            indicator_of_mem (s := Ioc a_s b_s) ⟨hta, h2⟩,
            indicator_of_mem (s := Ioc (max a_b a_s) (min b_b b_s)) ⟨max_lt h1 hta, le_min htb h2⟩]
          ring
        · rw [indicator_of_mem (s := Ioc a_b b_b) ⟨h1, htb⟩,
            indicator_of_notMem (s := Ioc a_s b_s) fun h => h2 h.2,
            indicator_of_notMem (s := Ioc (max a_b a_s) (min b_b b_s))
              fun h => h2 (h.2.trans (min_le_right _ _))]
          ring
        · rw [indicator_of_notMem (s := Ioc a_b b_b) fun h => h1 h.1,
            indicator_of_mem (s := Ioc a_s b_s) ⟨hta, h2⟩,
            indicator_of_notMem (s := Ioc (max a_b a_s) (min b_b b_s))
              fun h => h1 ((le_max_left _ _).trans_lt h.1)]
          ring
        · linarith [(le_max_left a_b a_s).trans (hover.trans (min_le_right b_b b_s)),
            not_lt.mp h1, not_le.mp h2]
  have hcomb : (∫ t in Ioc L U, g t) - (∫ t in Ioc a_b b_b, g t) - (∫ t in Ioc a_s b_s, g t) =
      - ∫ t in Ioc (max a_b a_s) (min b_b b_s), g t := by
    have hsub1 : IntegrableOn (fun t => g t - (Ioc a_b b_b).indicator g t) (Ioc L U) :=
      hg_int.sub (hg_int.indicator measurableSet_Ioc)
    rw [hI (Ioc_subset_Ioc (min_le_left a_b a_s) (le_max_left b_b b_s)),
      hI (Ioc_subset_Ioc (min_le_right a_b a_s) (le_max_right b_b b_s)),
      hI (Ioc_subset_Ioc ((min_le_left _ _).trans (le_max_left _ _))
        ((min_le_left _ _).trans (le_max_left _ _))),
      ← integral_sub hg_int (hg_int.indicator measurableSet_Ioc),
      ← integral_sub hsub1 (hg_int.indicator measurableSet_Ioc), ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Ioc hpt
  rw [integral_sub (f := fun p : ℝ × ℝ => M.buyerPayment p.1 p.2)
    (g := fun p : ℝ × ℝ => M.sellerPayment p.1 p.2) hpb hps, hEb, hEs]
  linarith [hGFT, hcomb]

/-- **Myerson–Satterthwaite impossibility theorem** ([MyersonSatterthwaite1983], Theorem 1;
locator not re-verified against primary PDF): for independent buyer and seller distributions with
positive densities on intervals `[a_b, b_b]` and `[a_s, b_s]` whose open interiors overlap
(`max a_b a_s < min b_b b_s`), every BIC, interim individually rational, ex-post efficient
bilateral trade mechanism with integrable payments has strictly negative expected budget surplus. -/
theorem budget_surplus_neg_of_hasValueDensityOn {M : Mechanism}
    {μ_b μ_s : Measure ℝ} [IsProbabilityMeasure μ_b] [IsProbabilityMeasure μ_s]
    {f_b f_s : ℝ → NNReal} {a_b b_b a_s b_s : ℝ}
    (hμ_b : HasValueDensityOn μ_b f_b a_b b_b) (hμ_s : HasValueDensityOn μ_s f_s a_s b_s)
    (hover : max a_b a_s < min b_b b_s)
    (hBIC : M.IsBIC μ_b μ_s a_b b_b a_s b_s) (hIR : M.IsInterimIR μ_b μ_s a_b b_b a_s b_s)
    (heff : M.IsExPostEfficient)
    (hpb : Integrable (Function.uncurry M.buyerPayment) (μ_b.prod μ_s))
    (hps : Integrable (Function.uncurry M.sellerPayment) (μ_b.prod μ_s)) :
    ∫ p, (M.buyerPayment p.1 p.2 - M.sellerPayment p.1 p.2) ∂(μ_b.prod μ_s) < 0 := by
  have := hμ_b.nullSingletonClass
  have := hμ_s.nullSingletonClass
  have heq := hBIC.budget_surplus_eq_of_isExPostEfficient hμ_b.ae_mem hμ_s.ae_mem hover.le
    heff hpb hps
  have hab : a_b ≤ b_b := (le_max_left a_b a_s).trans (hover.le.trans (min_le_left b_b b_s))
  have has : a_s ≤ b_s := (le_max_right a_b a_s).trans (hover.le.trans (min_le_right b_b b_s))
  have hUb : 0 ≤ M.interimBuyerUtility μ_s a_b := hIR.1 a_b ⟨le_rfl, hab⟩
  have hUs : 0 ≤ M.interimSellerUtility μ_b b_s := hIR.2 b_s ⟨has, le_rfl⟩
  set g : ℝ → ℝ := fun t => μ_b.real (Ici t) * μ_s.real (Iic t)
  have hg_pos : 0 < ∫ t in Ioc (max a_b a_s) (min b_b b_s), g t := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (Filter.Eventually.of_forall fun _ => mul_nonneg measureReal_nonneg measureReal_nonneg)
      (integrableOn_Ici_mul_Iic μ_b μ_s (max a_b a_s) (min b_b b_s))]
    have hsub : Ioo (max a_b a_s) (min b_b b_s) ⊆
        Function.support g ∩ Ioc (max a_b a_s) (min b_b b_s) := fun t ht =>
      ⟨(mul_pos (hμ_b.measureReal_Ici_pos
          ⟨(le_max_left a_b a_s).trans_lt ht.1, ht.2.trans_le (min_le_left b_b b_s)⟩)
        (hμ_s.measureReal_Iic_pos
          ⟨(le_max_right a_b a_s).trans_lt ht.1, ht.2.trans_le (min_le_right b_b b_s)⟩)).ne',
        ht.1, ht.2.le⟩
    exact (Real.volume_Ioo ▸ ENNReal.ofReal_pos.2 (sub_pos.2 hover)).trans_le (measure_mono hsub)
  linarith

/-- **Myerson–Satterthwaite impossibility theorem** ([MyersonSatterthwaite1983], Theorem 1;
locator not re-verified against primary PDF): no BIC, interim IR, ex-post efficient bilateral trade
mechanism with integrable payments is ex-ante weakly budget-balanced when buyer and seller
distributions have positive densities on overlapping intervals. -/
theorem not_isExAnteBudgetBalanced_of_hasValueDensityOn {M : Mechanism}
    {μ_b μ_s : Measure ℝ} [IsProbabilityMeasure μ_b] [IsProbabilityMeasure μ_s]
    {f_b f_s : ℝ → NNReal} {a_b b_b a_s b_s : ℝ}
    (hμ_b : HasValueDensityOn μ_b f_b a_b b_b) (hμ_s : HasValueDensityOn μ_s f_s a_s b_s)
    (hover : max a_b a_s < min b_b b_s)
    (hBIC : M.IsBIC μ_b μ_s a_b b_b a_s b_s) (hIR : M.IsInterimIR μ_b μ_s a_b b_b a_s b_s)
    (heff : M.IsExPostEfficient)
    (hpb : Integrable (Function.uncurry M.buyerPayment) (μ_b.prod μ_s))
    (hps : Integrable (Function.uncurry M.sellerPayment) (μ_b.prod μ_s)) :
    ¬ M.IsExAnteBudgetBalanced μ_b μ_s :=
  not_le.2 (budget_surplus_neg_of_hasValueDensityOn hμ_b hμ_s hover hBIC hIR heff hpb hps)

/-! ### Explicit `Uniform[0, 1]` calculation (`−1/6` deficit) -/

private theorem unif_isProb : IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]⟩

private theorem unif_real_Iic {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (Iic t) = t := by
  have hset : Iic t ∩ Icc (0 : ℝ) 1 = Icc 0 t := by
    ext x; simp only [mem_inter_iff, mem_Iic, mem_Icc]
    exact ⟨fun ⟨h1, h2, _⟩ => ⟨h2, h1⟩, fun ⟨h1, h2⟩ => ⟨h2, h1, h2.trans ht.2⟩⟩
  rw [measureReal_def, Measure.restrict_apply measurableSet_Iic, hset, Real.volume_Icc, sub_zero,
    ENNReal.toReal_ofReal ht.1]

private theorem unif_real_Ici {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (volume.restrict (Icc (0 : ℝ) 1)).real (Ici t) = 1 - t := by
  have hset : Ici t ∩ Icc (0 : ℝ) 1 = Icc t 1 := by
    ext x; simp only [mem_inter_iff, mem_Ici, mem_Icc]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h2⟩ => ⟨h1, ht.1.trans h1, h2⟩⟩
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ici, hset, Real.volume_Icc,
    ENNReal.toReal_ofReal (sub_nonneg.2 ht.2)]

/-- **Exact `Uniform[0, 1]` bilateral trade budget identity**: for independent `Uniform[0, 1]`
buyer and seller valuations, every BIC, ex-post efficient mechanism satisfies
`E[p_b − p_s] + U_b(0) + U_s(1) = −1/6`. -/
theorem budget_surplus_uniform_eq {M : Mechanism}
    (hBIC : M.IsBIC (volume.restrict (Icc 0 1)) (volume.restrict (Icc 0 1)) 0 1 0 1)
    (heff : M.IsExPostEfficient)
    (hpb : Integrable (Function.uncurry M.buyerPayment)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc 0 1))))
    (hps : Integrable (Function.uncurry M.sellerPayment)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc 0 1)))) :
    ∫ p, (M.buyerPayment p.1 p.2 - M.sellerPayment p.1 p.2)
        ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc 0 1))) +
      M.interimBuyerUtility (volume.restrict (Icc 0 1)) 0 +
      M.interimSellerUtility (volume.restrict (Icc 0 1)) 1 = -(1 / 6) := by
  have := unif_isProb
  have hdens := hasValueDensityOn_of_hasValueDensity SingleParameter.hasValueDensity_uniform
  have := hdens.nullSingletonClass
  have heq := hBIC.budget_surplus_eq_of_isExPostEfficient hdens.ae_mem hdens.ae_mem
    (by norm_num) heff hpb hps
  simp only [max_self, min_self] at heq
  rw [heq]
  apply congrArg Neg.neg
  trans ∫ t in Ioc (0 : ℝ) 1, (t - t ^ 2)
  · refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [unif_real_Ici (Ioc_subset_Icc_self ht), unif_real_Iic (Ioc_subset_Icc_self ht)]
    ring
  · rw [← intervalIntegral.integral_of_le zero_le_one,
      intervalIntegral.integral_sub (f := fun t : ℝ => t) (g := fun t : ℝ => t ^ 2)
        (continuous_id.intervalIntegrable 0 1) ((continuous_pow 2).intervalIntegrable 0 1),
      integral_id, integral_pow]
    norm_num

/-- **Explicit `Uniform[0, 1]` Myerson–Satterthwaite deficit**: every BIC, interim IR, ex-post
efficient bilateral trade mechanism for independent `Uniform[0, 1]` types runs an expected deficit
of at least `1/6` (`E[p_b − p_s] ≤ −1/6`). -/
theorem budget_surplus_uniform_le_neg_one_sixth {M : Mechanism}
    (hBIC : M.IsBIC (volume.restrict (Icc 0 1)) (volume.restrict (Icc 0 1)) 0 1 0 1)
    (hIR : M.IsInterimIR (volume.restrict (Icc 0 1)) (volume.restrict (Icc 0 1)) 0 1 0 1)
    (heff : M.IsExPostEfficient)
    (hpb : Integrable (Function.uncurry M.buyerPayment)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc 0 1))))
    (hps : Integrable (Function.uncurry M.sellerPayment)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc 0 1)))) :
    ∫ p, (M.buyerPayment p.1 p.2 - M.sellerPayment p.1 p.2)
        ∂((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc 0 1))) ≤ -(1 / 6) := by
  linarith [budget_surplus_uniform_eq hBIC heff hpb hps,
    hIR.1 0 ⟨le_rfl, zero_le_one⟩, hIR.2 1 ⟨zero_le_one, le_rfl⟩]

/-- On `Uniform[0, 1] × Uniform[0, 1]`, no BIC, interim IR, ex-post efficient bilateral trade
mechanism with integrable payments is ex-ante weakly budget-balanced. -/
theorem not_isExAnteBudgetBalanced_uniform {M : Mechanism}
    (hBIC : M.IsBIC (volume.restrict (Icc 0 1)) (volume.restrict (Icc 0 1)) 0 1 0 1)
    (hIR : M.IsInterimIR (volume.restrict (Icc 0 1)) (volume.restrict (Icc 0 1)) 0 1 0 1)
    (heff : M.IsExPostEfficient)
    (hpb : Integrable (Function.uncurry M.buyerPayment)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc 0 1))))
    (hps : Integrable (Function.uncurry M.sellerPayment)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc 0 1)))) :
    ¬ M.IsExAnteBudgetBalanced (volume.restrict (Icc 0 1)) (volume.restrict (Icc 0 1)) := by
  intro hBB
  exact absurd (hBB.trans (budget_surplus_uniform_le_neg_one_sixth hBIC hIR heff hpb hps))
    (by norm_num)

end Mechanism

/-! ### Boundary check: posted-price trade on non-overlapping supports -/

/-- The posted-price bilateral trade mechanism at fixed price `c`: trade occurs whenever
`v_s ≤ v_b`, with the buyer paying `c` directly to the seller. -/
@[expose] noncomputable def fixedPrice (c : ℝ) : Mechanism where
  trade v_b v_s := if v_s ≤ v_b then 1 else 0
  buyerPayment v_b v_s := if v_s ≤ v_b then c else 0
  sellerPayment v_b v_s := if v_s ≤ v_b then c else 0

theorem fixedPrice_isExPostEfficient (c : ℝ) : (fixedPrice c).IsExPostEfficient :=
  fun _ _ => ⟨fun h => ite_eq_left h.le, fun h => ite_eq_right (not_le.2 h)⟩

theorem fixedPrice_isExAnteBudgetBalanced (c : ℝ) (μ_b μ_s : Measure ℝ) :
    (fixedPrice c).IsExAnteBudgetBalanced μ_b μ_s := by
  simp only [Mechanism.IsExAnteBudgetBalanced, fixedPrice, sub_self, integral_zero, le_refl]

/-- When supports are separated by `c` (`b_s ≤ c ≤ a_b`), `fixedPrice c` always trades on the
support and is BIC and interim IR (as well as ex-post efficient and strictly budget-balanced). -/
theorem fixedPrice_isBIC_and_isInterimIR {μ_b μ_s : Measure ℝ}
    [IsProbabilityMeasure μ_b] [IsProbabilityMeasure μ_s]
    {a_b b_b a_s b_s c : ℝ} (hbc : b_s ≤ c) (hca : c ≤ a_b)
    (hb_supp : ∀ᵐ v ∂μ_b, v ∈ Icc a_b b_b) (hs_supp : ∀ᵐ v ∂μ_s, v ∈ Icc a_s b_s) :
    (fixedPrice c).IsBIC μ_b μ_s a_b b_b a_s b_s ∧
      (fixedPrice c).IsInterimIR μ_b μ_s a_b b_b a_s b_s := by
  have hconst {ν : Measure ℝ} [IsProbabilityMeasure ν] {c₀ : ℝ} {f : ℝ → ℝ}
      (hf : ∀ᵐ x ∂ν, f x = c₀) : ∫ x, f x ∂ν = c₀ := by
    rw [integral_congr_ae hf, integral_const, probReal_univ, one_smul]
  have hQb : ∀ v_b ∈ Icc a_b b_b, (fixedPrice c).interimBuyerTrade μ_s v_b = 1 := fun v_b hv =>
    hconst (hs_supp.mono fun _ hvs => ite_eq_left (hvs.2.trans (hbc.trans (hca.trans hv.1))))
  have hPb : ∀ v_b ∈ Icc a_b b_b, (fixedPrice c).interimBuyerPayment μ_s v_b = c := fun v_b hv =>
    hconst (hs_supp.mono fun _ hvs => ite_eq_left (hvs.2.trans (hbc.trans (hca.trans hv.1))))
  have hQs : ∀ v_s ∈ Icc a_s b_s, (fixedPrice c).interimSellerTrade μ_b v_s = 1 := fun v_s hv =>
    hconst (hb_supp.mono fun _ hvb => ite_eq_left (hv.2.trans (hbc.trans (hca.trans hvb.1))))
  have hPs : ∀ v_s ∈ Icc a_s b_s, (fixedPrice c).interimSellerPayment μ_b v_s = c := fun v_s hv =>
    hconst (hb_supp.mono fun _ hvb => ite_eq_left (hv.2.trans (hbc.trans (hca.trans hvb.1))))
  refine ⟨⟨fun v hv w hw => ?_, fun v hv w hw => ?_⟩, ⟨fun v hv => ?_, fun v hv => ?_⟩⟩
  · rw [hQb v hv, hQb w hw, hPb v hv, hPb w hw]
  · rw [hQs v hv, hQs w hw, hPs v hv, hPs w hw]
  · rw [Mechanism.interimBuyerUtility, hQb v hv, hPb v hv]; linarith [hv.1]
  · rw [Mechanism.interimSellerUtility, hQs v hv, hPs v hv]; linarith [hv.2]

end Cslib.GameTheory.BilateralTrade
