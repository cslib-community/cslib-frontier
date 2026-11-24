/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.OptimalAuction
public import CslibFrontier.Probability.OptimalStopping.ProphetSample
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sequential posted-price mechanisms, prophet auctions, and Bulow–Klemperer

A *sequential posted-price mechanism* (SPM, or *order-oblivious posted-price mechanism* when the
arrival order is adversarial; [ChawlaHartlineMalecSivan2010], §1–§2.2, pp. 1–4;
[Roughgarden2013CS364A], Lecture 6, §2–§3) sells a single item by approaching bidders in the linear
order of `ι` and offering bidder `i` a take-it-or-leave-it price `p i ≥ 0`. The first bidder who
accepts wins the item and pays `p i`; all other bidders receive and pay nothing.

This module develops four main pillars connecting prophet inequalities and simple near-optimal
auctions:

1. **Incentives and group strategy-proofness** (`PostedPrice.acceptMechanism`,
   `PostedPrice.postedPrice`, `PostedPrice.strictPostedPrice`): every sequential posted-price
   mechanism with nonnegative prices is single-item feasible, DSIC, individually rational,
   normalized, weakly group strategy-proof (`acceptMechanism_isGroupStrategyProof`: no nonempty
   coalition can strictly improve all of its members), and strongly group strategy-proof whenever no
   coalition member is indifferent at its posted price (`acceptMechanism_strongGroupStrategyProof`,
   matching [ChawlaHartlineMalecSivan2010], §2.2, p. 4; at exact price indifference a zero-surplus
   bidder can step aside to benefit a later bidder, verified in the test suite).
2. **Welfare `1/2`-approximations and prior-independent single-sample pricing** (`PMF ℝ≥0`):
   - With known priors, posting the Kleinberg–Weinberg balanced price `E[maxᵢ vᵢ] / 2`
     (`expectedWelfare_vickrey_le_two_mul_postedPrice_half`) or a Samuel-Cahn median price
     (`exists_expectedWelfare_vickrey_le_two_mul_postedPrice`) achieves at least `1/2` of the
     expected Vickrey (optimal) social welfare ([Roughgarden2013CS364A], Lecture 6, Theorem 2.1).
   - With unknown priors and one offline sample `sᵢ ~ μᵢ` per bidder, `singleSamplePostedPrice s π`
     posts the maximum sample `maxⱼ sⱼ` (breaking exact ties via `π`) as a DSIC, IR mechanism whose
     expected welfare is at least `1/2` of Vickrey welfare
     (`expectedWelfare_vickrey_le_two_mul_singleSamplePostedPrice`, from
     [RubinsteinWangWeinberg2020], Theorem 1).
   - No fixed-order posted-price mechanism achieves a factor above `1/2` for either social welfare
     or expected revenue (`exists_postedPrice_revenue_lt`, formalizing the 2-bidder gap-of-2
     instance of [ChawlaHartlineMalecSivan2010], Appendix D.2, p. 19).
3. **Non-i.i.d. regular revenue `1/2`-approximation**
   (`integral_sum_payment_le_two_mul_virtualPostedPrices`, [ChawlaHartlineMalecSivan2010],
   Theorem 10 (`k = 1`), p. 9 and Appendix D.2, p. 19; [Roughgarden2013CS364A], Lecture 6, §3,
   pp. 4–5): for independent, *non-identical* regular distributions `(μᵢ, fᵢ, hᵢ)` with densities,
   inverting each virtual valuation at `t = E[maxᵢ φᵢ(vᵢ)⁺] / 2` via `reservePrice` yields a DSIC,
   IR sequential posted-price mechanism whose expected revenue is at least `1/2` of *every* DSIC, IR
   single-item mechanism (including Myerson's asymmetric optimal auction).
4. **The Bulow–Klemperer theorem** (`bulow_klemperer`, [BulowKlemperer1996];
   [Roughgarden2013CS364A], Lecture 6, Theorem 4.1, p. 6): for `n` i.i.d. regular bidders, the
   prior-independent `(n + 1)`-bidder Vickrey auction with zero reserve achieves expected revenue at
   least that of *every* DSIC, IR `n`-bidder single-item mechanism.

## Main definitions

* `SingleParameter.PostedPrice.acceptMechanism`, `SingleParameter.PostedPrice.postedPrice`,
  `SingleParameter.PostedPrice.strictPostedPrice`: sequential posted-price mechanisms.
* `SingleParameter.PostedPrice.singleSamplePostedPrice`: single-sample posted-price mechanism.
* `SingleParameter.PostedPrice.expectedWelfare`, `SingleParameter.PostedPrice.expectedRevenuePMF`:
  discrete-prior expected welfare and revenue on `Fin n`.
* `SingleParameter.PostedPrice.posVirtualSurplus`,
  `SingleParameter.PostedPrice.virtualPostedPrices`: non-i.i.d. virtual-valuation posted prices.

## Main results

* `SingleParameter.PostedPrice.postedPrice_isDSIC`, `SingleParameter.PostedPrice.postedPrice_isIR`,
  `SingleParameter.PostedPrice.postedPrice_isNormalized`,
  `SingleParameter.PostedPrice.postedPrice_isGroupStrategyProof`,
  `SingleParameter.PostedPrice.postedPrice_strongGroupStrategyProof`: incentive properties of SPMs.
* `SingleParameter.PostedPrice.expectedWelfare_vickrey_le_two_mul_postedPrice_half`,
  `SingleParameter.PostedPrice.exists_expectedWelfare_vickrey_le_two_mul_postedPrice`: known-prior
  welfare `1/2`-approximations.
* `SingleParameter.PostedPrice.expectedWelfare_vickrey_le_two_mul_singleSamplePostedPrice`:
  single-sample prior-independent welfare `1/2`-approximation.
* `SingleParameter.PostedPrice.exists_postedPrice_revenue_lt`: tight `1/2` barrier for fixed-order
  posted-price revenue and welfare.
* `SingleParameter.PostedPrice.integral_sum_payment_le_two_mul_virtualPostedPrices`: non-i.i.d.
  regular revenue `1/2`-approximation by sequential posted pricing.
* `SingleParameter.HasValueDensity.integral_virtualValue_eq_zero`,
  `SingleParameter.PostedPrice.bulow_klemperer`: **the Bulow–Klemperer theorem**.

## References

* [S. Chawla, J. D. Hartline, D. L. Malec, B. Sivan, *Multi-parameter mechanism design and
  sequential posted pricing*][ChawlaHartlineMalecSivan2010]
* [J. Bulow, P. Klemperer, *Auctions versus negotiations*][BulowKlemperer1996]
* [A. Rubinstein, J. Z. Wang, S. M. Weinberg, *Optimal single-choice prophet inequalities from
  samples*][RubinsteinWangWeinberg2020]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A],
  Lecture 6
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016], Lecture 6
-/

open MeasureTheory Set
open scoped ENNReal NNReal

public section

namespace Cslib.GameTheory.SingleParameter

/-! ### Mean-zero virtual valuation -/

/-- Under a valuation distribution with density `f` on `[0, h]`, the expected virtual valuation is
`0`: applying the one-dimensional Myerson identity to the constant allocation `g ≡ 1` equates
`∫ φ(v) ∂μ` to `∫ (v · 1 − ∫₀ᵛ 1) ∂μ = 0`. -/
theorem HasValueDensity.integral_virtualValue_eq_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    {f : ℝ → NNReal} {h : ℝ} (hμ : HasValueDensity μ f h) :
    ∫ v, virtualValue μ f v ∂μ = 0 := by
  have h1 := hμ.integral_payment_eq_integral_virtualValue_mul (g := fun _ => (1 : ℝ))
    measurable_const (B := 1) fun _ _ => by norm_num
  simp only [mul_one, intervalIntegral.integral_const, sub_zero, smul_eq_mul, sub_self,
    integral_zero] at h1
  exact h1.symm

namespace PostedPrice

/-! ### Sequential posted-price mechanisms -/

section LinearOrder

variable {ι : Type*} [LinearOrder ι]

/-- Bidder `i` wins under per-bidder acceptance predicates `accept` when `i` accepts its offer and
every earlier bidder `j < i` rejects. -/
@[expose] def AcceptWins (accept : ι → ℝ → Prop) (b : ι → ℝ) (i : ι) : Prop :=
  accept i (b i) ∧ ∀ j < i, ¬ accept j (b j)

open Classical in
/-- The 0-1 sequential posted-price allocation rule for acceptance predicates `accept`. -/
@[expose] noncomputable def acceptAllocation (accept : ι → ℝ → Prop) (b : ι → ℝ) (i : ι) : ℝ :=
  if AcceptWins accept b i then 1 else 0

/-- Sequential posted-price mechanism with prices `p` and acceptance predicates `accept`: the first
accepting bidder gets the item and pays its posted price `p i`. -/
@[expose] noncomputable def acceptMechanism (p : ι → ℝ) (accept : ι → ℝ → Prop) : Mechanism ι where
  allocation := acceptAllocation accept
  payment b i := p i * acceptAllocation accept b i

/-- Sequential posted-price mechanism (`p i ≤ b i` accepts ties). -/
@[expose] noncomputable def postedPrice (p : ι → ℝ) : Mechanism ι :=
  acceptMechanism p fun i z => p i ≤ z

/-- Strict sequential posted-price mechanism (`p i < b i` rejects ties). -/
@[expose] noncomputable def strictPostedPrice (p : ι → ℝ) : Mechanism ι :=
  acceptMechanism p fun i z => p i < z

theorem AcceptWins.unique {accept : ι → ℝ → Prop} {b : ι → ℝ} {i j : ι}
    (hi : AcceptWins accept b i) (hj : AcceptWins accept b j) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact absurd hi.1 (hj.2 i hlt)
  · exact absurd hj.1 (hi.2 j hgt)

theorem acceptAllocation_binary (accept : ι → ℝ → Prop) (b : ι → ℝ) (i : ι) :
    acceptAllocation accept b i = 0 ∨ acceptAllocation accept b i = 1 := by
  unfold acceptAllocation
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem acceptAllocation_eq_one_iff {accept : ι → ℝ → Prop} {b : ι → ℝ} {i : ι} :
    acceptAllocation accept b i = 1 ↔ AcceptWins accept b i := by
  unfold acceptAllocation
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false zero_ne_one h

theorem acceptAllocation_eq_zero_iff {accept : ι → ℝ → Prop} {b : ι → ℝ} {i : ι} :
    acceptAllocation accept b i = 0 ↔ ¬ AcceptWins accept b i := by
  unfold acceptAllocation
  split_ifs with h
  · exact iff_of_false one_ne_zero (not_not_intro h)
  · exact iff_of_true rfl h

theorem acceptAllocation_nonneg (accept : ι → ℝ → Prop) (b : ι → ℝ) (i : ι) :
    0 ≤ acceptAllocation accept b i := by
  rcases acceptAllocation_binary accept b i with h | h
  · rw [h]
  · rw [h]; exact zero_le_one

theorem acceptAllocation_mem_singleItemFeasible [Fintype ι] (accept : ι → ℝ → Prop) (b : ι → ℝ) :
    acceptAllocation accept b ∈ Vickrey.singleItemFeasible := by
  refine ⟨acceptAllocation_binary accept b, ?_⟩
  by_cases h : ∃ i, AcceptWins accept b i
  · obtain ⟨i, hi⟩ := h
    rw [Finset.sum_eq_single i
      (fun j _ hj => acceptAllocation_eq_zero_iff.mpr fun hjw => hj (hjw.unique hi))
      (fun hm => absurd (Finset.mem_univ i) hm), acceptAllocation_eq_one_iff.mpr hi]
  · push Not at h
    have hz : ∀ j, acceptAllocation accept b j = 0 := fun j =>
      acceptAllocation_eq_zero_iff.mpr (h j)
    simp only [hz, Finset.sum_const_zero, zero_le_one]

theorem postedPrice_mem_singleItemFeasible [Fintype ι] (p b : ι → ℝ) :
    (postedPrice p).allocation b ∈ Vickrey.singleItemFeasible :=
  acceptAllocation_mem_singleItemFeasible _ b

theorem strictPostedPrice_mem_singleItemFeasible [Fintype ι] (p b : ι → ℝ) :
    (strictPostedPrice p).allocation b ∈ Vickrey.singleItemFeasible :=
  acceptAllocation_mem_singleItemFeasible _ b

/-- A sequential posted-price mechanism whose acceptance predicate accepts bids strictly above
`p i` and rejects nonnegative bids strictly below `p i` is DSIC. -/
theorem acceptMechanism_isDSIC {p : ι → ℝ} {accept : ι → ℝ → Prop}
    (hlt : ∀ i z, p i < z → accept i z)
    (hle : ∀ i z, 0 ≤ z → accept i z → p i ≤ z) :
    (acceptMechanism p accept).IsDSIC := by
  intro i b v _ hv
  simp only [Mechanism.utility, acceptMechanism]
  by_cases hprev : ∀ j < i, ¬ accept j (b j)
  · have hprev_upd : ∀ j < i, ¬ accept j (Function.update b i v j) := by
      intro j hj
      rw [Function.update_of_ne hj.ne]
      exact hprev j hj
    by_cases hav : accept i v
    · have hwin_v : AcceptWins accept (Function.update b i v) i := by
        refine ⟨?_, hprev_upd⟩
        rw [Function.update_self]
        exact hav
      rw [acceptAllocation_eq_one_iff.mpr hwin_v, mul_one, mul_one]
      have hpv : p i ≤ v := hle i v hv hav
      rcases acceptAllocation_binary accept b i with hb0 | hb1
      · rw [hb0, mul_zero, mul_zero, sub_zero]
        linarith
      · rw [hb1, mul_one, mul_one]
    · have hvp : v ≤ p i := not_lt.mp fun hgt => hav (hlt i v hgt)
      have hlose_v : ¬ AcceptWins accept (Function.update b i v) i := by
        intro hw
        have := hw.1
        rw [Function.update_self] at this
        exact hav this
      rw [acceptAllocation_eq_zero_iff.mpr hlose_v, mul_zero, mul_zero, sub_zero]
      rcases acceptAllocation_binary accept b i with hb0 | hb1
      · rw [hb0, mul_zero, mul_zero, sub_zero]
      · rw [hb1, mul_one, mul_one]
        linarith
  · have hlose_b : ¬ AcceptWins accept b i := fun hw => hprev hw.2
    have hlose_v : ¬ AcceptWins accept (Function.update b i v) i := by
      intro hw
      refine hprev fun j hj => ?_
      have := hw.2 j hj
      rwa [Function.update_of_ne hj.ne] at this
    rw [acceptAllocation_eq_zero_iff.mpr hlose_b, acceptAllocation_eq_zero_iff.mpr hlose_v]

/-- A sequential posted-price mechanism whose acceptance predicate implies `p i ≤ z` on nonnegative
bids is individually rational. -/
theorem acceptMechanism_isIR {p : ι → ℝ} {accept : ι → ℝ → Prop}
    (hle : ∀ i z, 0 ≤ z → accept i z → p i ≤ z) :
    (acceptMechanism p accept).IsIR := by
  intro i b hb
  simp only [Mechanism.utility, acceptMechanism]
  rcases acceptAllocation_binary accept b i with h0 | h1
  · rw [h0, mul_zero, mul_zero, sub_zero]
  · have hw := acceptAllocation_eq_one_iff.mp h1
    have hp := hle i (b i) (hb i) hw.1
    rw [h1, mul_one, mul_one]
    linarith

/-- With nonnegative prices `0 ≤ p`, a bidder who bids `0` pays `0` (even if `p i = 0` and the
bidder wins, its price is `0`). -/
theorem acceptMechanism_isNormalized {p : ι → ℝ} {accept : ι → ℝ → Prop} (hp : 0 ≤ p)
    (hle : ∀ i z, 0 ≤ z → accept i z → p i ≤ z) :
    (acceptMechanism p accept).IsNormalized := by
  intro i b _
  simp only [acceptMechanism]
  rcases acceptAllocation_binary accept (Function.update b i 0) i with h0 | h1
  · rw [h0, mul_zero]
  · have hw := acceptAllocation_eq_one_iff.mp h1
    have h0' := hw.1
    rw [Function.update_self] at h0'
    have hp0 : p i = 0 := le_antisymm (hle i 0 le_rfl h0') (hp i)
    rw [hp0, zero_mul]

theorem postedPrice_isDSIC (p : ι → ℝ) : (postedPrice p).IsDSIC :=
  acceptMechanism_isDSIC (fun _ _ h => h.le) (fun _ _ _ h => h)

theorem postedPrice_isIR (p : ι → ℝ) : (postedPrice p).IsIR :=
  acceptMechanism_isIR fun _ _ _ h => h

theorem postedPrice_isNormalized {p : ι → ℝ} (hp : 0 ≤ p) : (postedPrice p).IsNormalized :=
  acceptMechanism_isNormalized hp fun _ _ _ h => h

theorem strictPostedPrice_isDSIC (p : ι → ℝ) : (strictPostedPrice p).IsDSIC :=
  acceptMechanism_isDSIC (fun _ _ h => h) (fun _ _ _ h => h.le)

theorem strictPostedPrice_isIR (p : ι → ℝ) : (strictPostedPrice p).IsIR :=
  acceptMechanism_isIR fun _ _ _ h => h.le

theorem strictPostedPrice_isNormalized {p : ι → ℝ} (hp : 0 ≤ p) :
    (strictPostedPrice p).IsNormalized :=
  acceptMechanism_isNormalized hp fun _ _ _ h => h.le

/-- **Group strategy-proofness of sequential posted pricing** ([ChawlaHartlineMalecSivan2010],
§2.2, p. 4): no nonempty coalition `S` can deviate from truthful nonnegative valuations `v` to a
nonnegative profile `b` (agreeing with `v` outside `S`) so as to strictly increase the utility of
*every* member of `S`. -/
theorem acceptMechanism_isGroupStrategyProof [Finite ι] {p : ι → ℝ} {accept : ι → ℝ → Prop}
    (hlt : ∀ i z, p i < z → accept i z)
    (hle : ∀ i z, 0 ≤ z → accept i z → p i ≤ z)
    {S : Finset ι} (hS : S.Nonempty) {v b : ι → ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hout : ∀ j ∉ S, b j = v j) :
    ∃ i ∈ S, (acceptMechanism p accept).utility i (v i) b ≤
      (acceptMechanism p accept).utility i (v i) v := by
  classical
  have := Fintype.ofFinite ι
  set D := Finset.univ.filter fun k : ι => ¬ (accept k (v k) ↔ accept k (b k))
  by_cases hD : D.Nonempty
  · let k := D.min' hD
    have hkD : k ∈ D := Finset.min'_mem D hD
    have hk_diff : ¬ (accept k (v k) ↔ accept k (b k)) := (Finset.mem_filter.mp hkD).2
    have hkS : k ∈ S := by
      by_contra hnotS
      rw [hout k hnotS] at hk_diff
      exact hk_diff Iff.rfl
    have hbefore : ∀ j < k, (accept j (v j) ↔ accept j (b j)) := by
      intro j hj
      by_contra hj_diff
      exact not_le.mpr hj (Finset.min'_le D j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_diff⟩))
    have hwin_eq : AcceptWins accept b k ↔ AcceptWins accept (Function.update v k (b k)) k := by
      simp only [AcceptWins, Function.update_self]
      refine and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj => ?_
      rw [Function.update_of_ne hj.ne, hbefore j hj]
    have halloc_eq : acceptAllocation accept b k =
        acceptAllocation accept (Function.update v k (b k)) k := by
      by_cases hw : AcceptWins accept b k
      · rw [acceptAllocation_eq_one_iff.mpr hw, acceptAllocation_eq_one_iff.mpr (hwin_eq.mp hw)]
      · rw [acceptAllocation_eq_zero_iff.mpr hw,
          acceptAllocation_eq_zero_iff.mpr (mt hwin_eq.mpr hw)]
    have hutil_eq : (acceptMechanism p accept).utility k (v k) b =
        (acceptMechanism p accept).utility k (v k) (Function.update v k (b k)) := by
      simp only [Mechanism.utility, acceptMechanism, halloc_eq]
    refine ⟨k, hkS, ?_⟩
    rw [hutil_eq]
    have hdsic := acceptMechanism_isDSIC hlt hle k (Function.update v k (b k)) (v k)
      (update_nonneg hv k (hb k)) (hv k)
    simpa only [Function.update_idem, Function.update_eq_self] using hdsic
  · obtain ⟨i, hiS⟩ := hS
    have hall : ∀ k, accept k (v k) ↔ accept k (b k) := by
      intro k
      by_contra hk
      exact hD ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    have hwin : AcceptWins accept b i ↔ AcceptWins accept v i := by
      simp only [AcceptWins, hall]
    have halloc : acceptAllocation accept b i = acceptAllocation accept v i := by
      by_cases hw : AcceptWins accept b i
      · rw [acceptAllocation_eq_one_iff.mpr hw, acceptAllocation_eq_one_iff.mpr (hwin.mp hw)]
      · rw [acceptAllocation_eq_zero_iff.mpr hw,
          acceptAllocation_eq_zero_iff.mpr (mt hwin.mpr hw)]
    exact ⟨i, hiS, le_of_eq (by simp only [Mechanism.utility, acceptMechanism, halloc])⟩

/-- **Strong group strategy-proofness away from indifference ties**: when no member `i ∈ S` has
valuation equal to its posted price `p i`, if a coalition `S` does not hurt any of its members
(`∀ i ∈ S, utility i (v i) v ≤ utility i (v i) b`), then *every* bidder's utility is unchanged. -/
theorem acceptMechanism_strongGroupStrategyProof [Finite ι] {p : ι → ℝ} {accept : ι → ℝ → Prop}
    (hlt : ∀ i z, p i < z → accept i z)
    (hle : ∀ i z, 0 ≤ z → accept i z → p i ≤ z)
    {S : Finset ι} {v b : ι → ℝ} (hv : 0 ≤ v)
    (hout : ∀ j ∉ S, b j = v j) (hno_tie : ∀ i ∈ S, v i ≠ p i)
    (hcoal : ∀ i ∈ S, (acceptMechanism p accept).utility i (v i) v ≤
      (acceptMechanism p accept).utility i (v i) b) :
    ∀ i, (acceptMechanism p accept).utility i (v i) b =
      (acceptMechanism p accept).utility i (v i) v := by
  classical
  have := Fintype.ofFinite ι
  -- Consider the first bidder whose winning status changes between `v` and `b`.
  set W := Finset.univ.filter fun k : ι => ¬ (AcceptWins accept v k ↔ AcceptWins accept b k)
  by_cases hW : W.Nonempty
  · exfalso
    let k := W.min' hW
    have hkW : k ∈ W := Finset.min'_mem W hW
    have hk_diff : ¬ (AcceptWins accept v k ↔ AcceptWins accept b k) :=
      (Finset.mem_filter.mp hkW).2
    -- Can any `j < k` accept under `v` or `b`? Its earliest accepting `r < k` would win under
    -- both `v` and `b` (since `r ∉ W`), making `k` lose under both, contradicting `hk_diff`.
    have hr_iff : ∀ r < k, AcceptWins accept v r ↔ AcceptWins accept b r := by
      intro r hr
      by_contra hrW
      exact not_le.mpr hr (Finset.min'_le W r (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrW⟩))
    have hno_prev : ∀ (u : ι → ℝ),
        (∀ r < k, AcceptWins accept u r → AcceptWins accept v r ∧ AcceptWins accept b r) →
        ∀ j < k, ¬ accept j (u j) := by
      intro u hu j hj hacc
      set A := Finset.univ.filter fun r : ι => accept r (u r)
      have hAne : A.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc⟩⟩
      let r := A.min' hAne
      have hrlt : r < k :=
        (Finset.min'_le A j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hacc⟩)).trans_lt hj
      have hr_win : AcceptWins accept u r :=
        ⟨(Finset.mem_filter.mp (Finset.min'_mem A hAne)).2,
          fun m hm hma =>
            not_le.mpr hm (Finset.min'_le A m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hma⟩))⟩
      have hr_both := hu r hrlt hr_win
      exact hk_diff (iff_of_false (fun hw => hw.2 r hrlt hr_both.1.1)
        (fun hw => hw.2 r hrlt hr_both.2.1))
    have hno_prev_v : ∀ j < k, ¬ accept j (v j) :=
      hno_prev v fun r hr hw => ⟨hw, (hr_iff r hr).mp hw⟩
    have hno_prev_b : ∀ j < k, ¬ accept j (b j) :=
      hno_prev b fun r hr hw => ⟨(hr_iff r hr).mpr hw, hw⟩
    have hk_acc_diff : ¬ (accept k (v k) ↔ accept k (b k)) := by
      intro hiff
      exact hk_diff ⟨fun h => ⟨hiff.mp h.1, hno_prev_b⟩, fun h => ⟨hiff.mpr h.1, hno_prev_v⟩⟩
    have hkS : k ∈ S := by
      by_contra hnotS
      rw [hout k hnotS] at hk_acc_diff
      exact hk_acc_diff Iff.rfl
    have hle_u := hcoal k hkS
    have hne_tie := hno_tie k hkS
    simp only [Mechanism.utility, acceptMechanism] at hle_u
    by_cases hav : accept k (v k)
    · have hab : ¬ accept k (b k) := fun hb' => hk_acc_diff (iff_of_true hav hb')
      have hwv : AcceptWins accept v k := ⟨hav, hno_prev_v⟩
      have hwb : ¬ AcceptWins accept b k := fun hw => hab hw.1
      rw [acceptAllocation_eq_one_iff.mpr hwv, acceptAllocation_eq_zero_iff.mpr hwb] at hle_u
      have hpv : p k ≤ v k := hle k (v k) (hv k) hav
      have heq : v k = p k := by linarith
      exact hne_tie heq
    · have hab : accept k (b k) := by
        by_contra hb'
        exact hk_acc_diff (iff_of_false hav hb')
      have hwv : ¬ AcceptWins accept v k := fun hw => hav hw.1
      have hwb : AcceptWins accept b k := ⟨hab, hno_prev_b⟩
      rw [acceptAllocation_eq_zero_iff.mpr hwv, acceptAllocation_eq_one_iff.mpr hwb] at hle_u
      have hvp : v k ≤ p k := not_lt.mp fun hgt => hav (hlt k (v k) hgt)
      have heq : v k = p k := by linarith
      exact hne_tie heq
  · intro i
    have hiff : AcceptWins accept v i ↔ AcceptWins accept b i := by
      by_contra hi
      exact hW ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    have halloc : acceptAllocation accept b i = acceptAllocation accept v i := by
      by_cases hw : AcceptWins accept b i
      · rw [acceptAllocation_eq_one_iff.mpr hw, acceptAllocation_eq_one_iff.mpr (hiff.mpr hw)]
      · rw [acceptAllocation_eq_zero_iff.mpr hw,
          acceptAllocation_eq_zero_iff.mpr (mt hiff.mp hw)]
    simp only [Mechanism.utility, acceptMechanism, halloc]

theorem postedPrice_isGroupStrategyProof [Finite ι] (p : ι → ℝ) {S : Finset ι} (hS : S.Nonempty)
    {v b : ι → ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hout : ∀ j ∉ S, b j = v j) :
    ∃ i ∈ S, (postedPrice p).utility i (v i) b ≤ (postedPrice p).utility i (v i) v :=
  acceptMechanism_isGroupStrategyProof (fun _ _ h => h.le) (fun _ _ _ h => h) hS hv hb hout

theorem postedPrice_strongGroupStrategyProof [Finite ι] (p : ι → ℝ) {S : Finset ι}
    {v b : ι → ℝ} (hv : 0 ≤ v) (hout : ∀ j ∉ S, b j = v j)
    (hno_tie : ∀ i ∈ S, v i ≠ p i)
    (hcoal : ∀ i ∈ S, (postedPrice p).utility i (v i) v ≤ (postedPrice p).utility i (v i) b) :
    ∀ i, (postedPrice p).utility i (v i) b = (postedPrice p).utility i (v i) v :=
  acceptMechanism_strongGroupStrategyProof (fun _ _ h => h.le) (fun _ _ _ h => h)
    hv hout hno_tie hcoal

open Classical in
/-- The allocation rule of `postedPrice p` is measurable in the bid profile. -/
theorem measurable_postedPrice_allocation [Countable ι] (p : ι → ℝ) (i : ι) :
    Measurable fun b : ι → ℝ => (postedPrice p).allocation b i := by
  have h1 : MeasurableSet {b : ι → ℝ | p i ≤ b i} :=
    measurableSet_le measurable_const (measurable_pi_apply i)
  have h2 : MeasurableSet {b : ι → ℝ | ∀ j, j < i → ¬ p j ≤ b j} :=
    (Measurable.forall fun j => Measurable.imp measurable_const
      (measurableSet_le measurable_const (measurable_pi_apply j)).compl.mem).setOf
  unfold postedPrice acceptMechanism acceptAllocation AcceptWins
  exact Measurable.ite (h1.inter h2) measurable_const measurable_const

end LinearOrder

/-! ### Prophet welfare `1/2`-approximations and single-sample posted pricing (`PMF ℝ≥0`) -/

section ProphetWelfare

open Cslib.Probability.PMF Cslib.Probability.OptimalStopping
  Cslib.Probability.OptimalStopping.Prophet

/-- Expected social welfare of an allocation rule `x` on `n` independent `ℝ≥0`-valued bidder
distributions `μ`. -/
noncomputable def expectedWelfare {n : ℕ} (x : (Fin n → ℝ) → Fin n → ℝ)
    (μ : Fin n → PMF ℝ≥0) : ℝ≥0∞ :=
  ∑' v, piFin μ v * ENNReal.ofReal (∑ i : Fin n, (v i : ℝ) * x (fun j => (v j : ℝ)) i)

/-- Expected total payment of a mechanism `M` on `n` independent `ℝ≥0`-valued bidder distributions
`μ`. -/
noncomputable def expectedRevenuePMF {n : ℕ} (M : Mechanism (Fin n))
    (μ : Fin n → PMF ℝ≥0) : ℝ≥0∞ :=
  ∑' v, piFin μ v * ENNReal.ofReal (∑ i : Fin n, M.payment (fun j => (v j : ℝ)) i)

/-- Every single-item-feasible allocation rule has expected social welfare at most that of the
Vickrey auction. -/
theorem expectedWelfare_le_vickrey {n : ℕ} {x : (Fin n → ℝ) → Fin n → ℝ}
    (hx : ∀ b, 0 ≤ b → x b ∈ Vickrey.singleItemFeasible) (μ : Fin n → PMF ℝ≥0) :
    expectedWelfare x μ ≤ expectedWelfare Vickrey.allocation μ := by
  refine tsum_le_tsum fun v => mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  have hv : 0 ≤ (fun j : Fin n => (v j : ℝ)) := fun j => NNReal.coe_nonneg _
  exact (Vickrey.isWelfareMaximizing_allocation _ hv).2 _ (hx _ hv)

/-- Expected social welfare of the Vickrey auction equals `expectedMax (List.ofFn μ)`. -/
theorem expectedWelfare_vickrey_eq_expectedMax {n : ℕ} (μ : Fin n → PMF ℝ≥0) :
    expectedWelfare Vickrey.allocation μ = expectedMax (List.ofFn μ) := by
  rw [expectedWelfare, expectedMax, tsum_jointLaw_ofFn_mul]
  refine tsum_congr fun v => ?_
  congr 1
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [listMax]
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨w, hw⟩ := Vickrey.exists_wins (fun j : Fin n => (v j : ℝ))
  have hsum : ∑ i : Fin n, (v i : ℝ) * Vickrey.allocation (fun j => (v j : ℝ)) i = v w := by
    rw [Finset.sum_eq_single w
      (fun j _ hj => by
        rw [Vickrey.allocation_eq_zero_iff.mpr fun hjw => hj (hjw.unique hw), mul_zero])
      (fun hm => absurd (Finset.mem_univ w) hm),
      Vickrey.allocation_eq_one_iff.mpr hw, mul_one]
  have hmax : listMax (List.ofFn v) = v w := by
    apply le_antisymm
    · rw [listMax_le_iff]
      intro y hy
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
      rcases eq_or_ne j w with rfl | hj
      · exact le_rfl
      · exact_mod_cast (hw j hj).1
    · by_contra hlt
      have := (listMax_le_iff _ _).mp le_rfl (v w) (List.mem_ofFn.mpr ⟨w, rfl⟩)
      exact hlt this
  rw [hsum, hmax, ENNReal.ofReal_coe_nnreal]

private theorem payoff_acceptRule_ofFn {n : ℕ} (a : ℝ≥0 → Bool) (accept : Fin n → ℝ → Prop)
    (hacc : ∀ (i : Fin n) (z : ℝ≥0), a z = true ↔ accept i (z : ℝ)) (v : Fin n → ℝ≥0) :
    ENNReal.ofReal (∑ i : Fin n, (v i : ℝ) * acceptAllocation accept (fun j => (v j : ℝ)) i) =
      payoff (acceptRule a) reward [] (List.ofFn v) := by
  induction n with
  | zero => simp [payoff_nil]
  | succ m ih =>
      rw [List.ofFn_succ, payoff_cons, Fin.sum_univ_succ]
      by_cases h0 : a (v 0) = true
      · have hw0 : AcceptWins accept (fun j => (v j : ℝ)) 0 :=
          ⟨(hacc 0 (v 0)).mp h0, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
        have hlose : ∀ k : Fin m,
            acceptAllocation accept (fun j => (v j : ℝ)) k.succ = 0 := fun k =>
          acceptAllocation_eq_zero_iff.mpr fun hw => hw.2 0 (Fin.succ_pos k) hw0.1
        simp only [acceptRule, h0, ↓reduceIte, reward, acceptAllocation_eq_one_iff.mpr hw0,
          mul_one, hlose, mul_zero, Finset.sum_const_zero, add_zero, ENNReal.ofReal_coe_nnreal]
      · have h0f : ¬ accept 0 (v 0 : ℝ) := mt (hacc 0 (v 0)).mpr h0
        have hlose0 : acceptAllocation accept (fun j => (v j : ℝ)) 0 = 0 :=
          acceptAllocation_eq_zero_iff.mpr fun hw => h0f hw.1
        have hsucc : ∀ k : Fin m,
            acceptAllocation accept (fun j => (v j : ℝ)) k.succ =
              acceptAllocation (fun k' z => accept k'.succ z) (fun j => (v j.succ : ℝ)) k := by
          intro k
          have hiff : AcceptWins accept (fun j => (v j : ℝ)) k.succ ↔
              AcceptWins (fun k' z => accept k'.succ z) (fun j => (v j.succ : ℝ)) k := by
            simp only [AcceptWins]
            refine and_congr_right fun _ =>
              ⟨fun h j hj => h j.succ (Fin.succ_lt_succ_iff.mpr hj), fun h j hj => ?_⟩
            cases j using Fin.cases with
            | zero => exact h0f
            | succ j' => exact h j' (Fin.succ_lt_succ_iff.mp hj)
          by_cases hw : AcceptWins accept (fun j => (v j : ℝ)) k.succ
          · rw [acceptAllocation_eq_one_iff.mpr hw,
              acceptAllocation_eq_one_iff.mpr (hiff.mp hw)]
          · rw [acceptAllocation_eq_zero_iff.mpr hw,
              acceptAllocation_eq_zero_iff.mpr (mt hiff.mpr hw)]
        have ha0 : acceptRule a [v 0] = false := Bool.eq_false_iff.mpr h0
        rw [ha0]
        simp only [Bool.false_eq_true, ↓reduceIte, hlose0, mul_zero, zero_add]
        have hpay : ∀ (xs : List ℝ≥0) (p₁ p₂ : List ℝ≥0),
            payoff (acceptRule a) reward p₁ xs = payoff (acceptRule a) reward p₂ xs := by
          intro xs
          induction xs with
          | nil => intros; rfl
          | cons y ys ihy =>
              intro p₁ p₂
              simp only [payoff_cons, acceptRule, reward]
              by_cases hy : a y = true
              · simp only [hy, ↓reduceIte]
              · simp only [hy]
                exact ihy _ _
        rw [hpay _ [v 0] [], ← ih (fun k' z => accept k'.succ z) (fun i z => hacc i.succ z)
          (fun j => v j.succ)]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsucc k]

/-- At a uniform posted price `t : ℝ≥0`, the expected social welfare of `postedPrice` equals
`expectedReward (thresholdRule t) (List.ofFn μ)`. -/
theorem expectedWelfare_postedPrice_const {n : ℕ} (t : ℝ≥0) (μ : Fin n → PMF ℝ≥0) :
    expectedWelfare (postedPrice (fun _ : Fin n => (t : ℝ))).allocation μ =
      expectedReward (thresholdRule t) (List.ofFn μ) := by
  rw [expectedWelfare, expectedReward, tsum_jointLaw_ofFn_mul]
  refine tsum_congr fun v => ?_
  congr 1
  exact payoff_acceptRule_ofFn (fun x => decide (t ≤ x)) (fun _ z => (t : ℝ) ≤ z)
    (fun _ z => by simp [NNReal.coe_le_coe]) v

/-- At a uniform posted price `t : ℝ≥0`, the expected social welfare of `strictPostedPrice` equals
`expectedReward (strictThresholdRule t) (List.ofFn μ)`. -/
theorem expectedWelfare_strictPostedPrice_const {n : ℕ} (t : ℝ≥0) (μ : Fin n → PMF ℝ≥0) :
    expectedWelfare (strictPostedPrice (fun _ : Fin n => (t : ℝ))).allocation μ =
      expectedReward (strictThresholdRule t) (List.ofFn μ) := by
  rw [expectedWelfare, expectedReward, tsum_jointLaw_ofFn_mul]
  refine tsum_congr fun v => ?_
  congr 1
  exact payoff_acceptRule_ofFn (fun x => decide (t < x)) (fun _ z => (t : ℝ) < z)
    (fun _ z => by simp [NNReal.coe_lt_coe]) v

/-- **Posted-price welfare `1/2`-approximation via balanced threshold**
([Roughgarden2013CS364A], Lecture 6, Theorem 2.1, pp. 2–4; [Roughgarden2016], Lecture 6,
Theorem 6.1): when `expectedMax (List.ofFn μ)` is finite, posting the uniform price
`t = E[maxᵢ vᵢ] / 2` to all bidders achieves at least half of the Vickrey auction's expected social
welfare. -/
theorem expectedWelfare_vickrey_le_two_mul_postedPrice_half {n : ℕ} (μ : Fin n → PMF ℝ≥0)
    (hM : expectedMax (List.ofFn μ) ≠ ⊤) :
    let t := (expectedMax (List.ofFn μ) / 2).toNNReal
    expectedWelfare Vickrey.allocation μ ≤
      2 * expectedWelfare (postedPrice (fun _ : Fin n => (t : ℝ))).allocation μ := by
  intro t
  rw [expectedWelfare_vickrey_eq_expectedMax, expectedWelfare_postedPrice_const]
  exact expectedMax_le_two_mul_expectedReward_half (List.ofFn μ) hM

/-- **Posted-price welfare `1/2`-approximation via Samuel-Cahn median price**
([SamuelCahn1984]; [Roughgarden2013CS364A], Lecture 6, §2): for any `n` independent `ℝ≥0`-valued
valuation distributions `μ` (even with `E[maxᵢ vᵢ] = ⊤`), there exists a single posted price `m`
such that either `postedPrice` or `strictPostedPrice` at uniform price `m` achieves at least half
of the Vickrey auction's expected social welfare. -/
theorem exists_expectedWelfare_vickrey_le_two_mul_postedPrice {n : ℕ} (μ : Fin n → PMF ℝ≥0) :
    ∃ m : ℝ≥0,
      expectedWelfare Vickrey.allocation μ ≤
        2 * expectedWelfare (postedPrice (fun _ : Fin n => (m : ℝ))).allocation μ ∨
      expectedWelfare Vickrey.allocation μ ≤
        2 * expectedWelfare (strictPostedPrice (fun _ : Fin n => (m : ℝ))).allocation μ := by
  obtain ⟨m, hm⟩ := exists_expectedMax_le_two_mul_expectedReward (List.ofFn μ)
  refine ⟨m, ?_⟩
  rwa [expectedWelfare_vickrey_eq_expectedMax, expectedWelfare_postedPrice_const,
    expectedWelfare_strictPostedPrice_const]

/-- Maximum of an offline sample vector `s : Fin n → ℝ≥0`, cast to `ℝ` (`0` when `n = 0`). -/
noncomputable def sampleMaxPrice {n : ℕ} (s : Fin n → ℝ≥0) : ℝ :=
  ((Finset.univ.fold max (0 : ℝ≥0) s : ℝ≥0) : ℝ)

/-- Single-sample acceptance predicate at bidder `i` with offline samples `s` and tie-breaker `π`.
-/
def singleSampleAccept {n : ℕ} (s : Fin n → ℝ≥0) (π : Equiv.Perm (Fin (2 * n)))
    (i : Fin n) (z : ℝ) : Prop :=
  0 ≤ z ∧ ∀ j : Fin n, sampleTag s π j < onlineTag z.toNNReal π i

/-- **The single-sample posted-price mechanism**: post the uniform price `sampleMaxPrice s`
(`maxⱼ sⱼ`) and break exact ties at `sampleMaxPrice s` using `π`. -/
noncomputable def singleSamplePostedPrice {n : ℕ} (s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) : Mechanism (Fin n) :=
  acceptMechanism (fun _ => sampleMaxPrice s) (singleSampleAccept s π)

private theorem sampleMaxPrice_lt_imp {n : ℕ} (s : Fin n → ℝ≥0) (π : Equiv.Perm (Fin (2 * n)))
    (i : Fin n) {z : ℝ} (hz : sampleMaxPrice s < z) : singleSampleAccept s π i z := by
  have hs0 : 0 ≤ sampleMaxPrice s := NNReal.coe_nonneg _
  have hz0 : 0 ≤ z := hs0.trans hz.le
  refine ⟨hz0, fun j => ?_⟩
  have hle_j : (s j : ℝ) ≤ sampleMaxPrice s :=
    NNReal.coe_le_coe.mpr ((Finset.le_fold_max _).mpr (Or.inr ⟨j, Finset.mem_univ j, le_rfl⟩))
  have hlt_j : s j < z.toNNReal :=
    Real.lt_toNNReal_iff_coe_lt.mpr (hle_j.trans_lt hz)
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hlt_j)

private theorem singleSampleAccept_le {n : ℕ} (s : Fin n → ℝ≥0) (π : Equiv.Perm (Fin (2 * n)))
    (i : Fin n) {z : ℝ} (hz : 0 ≤ z) (ha : singleSampleAccept s π i z) :
    sampleMaxPrice s ≤ z := by
  have hfold : Finset.univ.fold max (0 : ℝ≥0) s ≤ z.toNNReal := by
    refine (Finset.fold_max_le z.toNNReal).mpr ⟨zero_le, fun j _ => ?_⟩
    exact Prod.Lex.monotone_fst _ _ (ha.2 j).le
  have := NNReal.coe_le_coe.mpr hfold
  rwa [Real.coe_toNNReal z hz] at this

theorem singleSamplePostedPrice_isDSIC {n : ℕ} (s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) : (singleSamplePostedPrice s π).IsDSIC :=
  acceptMechanism_isDSIC (fun i _ hz => sampleMaxPrice_lt_imp s π i hz)
    (fun i _ hz ha => singleSampleAccept_le s π i hz ha)

theorem singleSamplePostedPrice_isIR {n : ℕ} (s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) : (singleSamplePostedPrice s π).IsIR :=
  acceptMechanism_isIR fun i _ hz ha => singleSampleAccept_le s π i hz ha

theorem singleSamplePostedPrice_isNormalized {n : ℕ} (s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) : (singleSamplePostedPrice s π).IsNormalized :=
  acceptMechanism_isNormalized (fun _ => NNReal.coe_nonneg _)
    (fun i _ hz ha => singleSampleAccept_le s π i hz ha)

theorem singleSamplePostedPrice_mem_singleItemFeasible {n : ℕ} (s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) (b : Fin n → ℝ) :
    (singleSamplePostedPrice s π).allocation b ∈ Vickrey.singleItemFeasible :=
  acceptAllocation_mem_singleItemFeasible _ b

/-- For fixed `(s, π)`, the social welfare of `singleSamplePostedPrice s π` equals
`expectedReward (singleSampleRule s π) (List.ofFn μ)`. -/
theorem expectedWelfare_singleSamplePostedPrice {n : ℕ} (s : Fin n → ℝ≥0)
    (π : Equiv.Perm (Fin (2 * n))) (μ : Fin n → PMF ℝ≥0) :
    expectedWelfare (singleSamplePostedPrice s π).allocation μ =
      expectedReward (singleSampleRule s π) (List.ofFn μ) := by
  rw [expectedWelfare, expectedReward, tsum_jointLaw_ofFn_mul]
  refine tsum_congr fun v => ?_
  congr 1
  rw [payoff_singleSampleRule_ofFn]
  -- Compare the first index in `Fin n` where `singleSampleAccept` holds with `firstBeatReward`.
  have hacc : ∀ i : Fin n, singleSampleAccept s π i (v i : ℝ) ↔
      ∀ j : Fin n, sampleTag s π j < onlineTag (v i) π i := by
    intro i
    simp [singleSampleAccept]
  set W := Finset.univ.filter fun i : Fin n => ∀ j : Fin n, sampleTag s π j < onlineTag (v i) π i
  by_cases hW : W.Nonempty
  · let w := W.min' hW
    have hwW : w ∈ W := Finset.min'_mem W hW
    have hwin : AcceptWins (singleSampleAccept s π) (fun j => (v j : ℝ)) w := by
      refine ⟨(hacc w).mpr (Finset.mem_filter.mp hwW).2, fun j hj hja => ?_⟩
      exact not_le.mpr hj
        (Finset.min'_le W j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hacc j).mp hja⟩))
    have hsum : ∑ i : Fin n, (v i : ℝ) *
        (singleSamplePostedPrice s π).allocation (fun j => (v j : ℝ)) i = v w := by
      simp only [singleSamplePostedPrice, acceptMechanism]
      rw [Finset.sum_eq_single w
        (fun j _ hj => by
          rw [acceptAllocation_eq_zero_iff.mpr fun hjw => hj (hjw.unique hwin), mul_zero])
        (fun hm => absurd (Finset.mem_univ w) hm),
        acceptAllocation_eq_one_iff.mpr hwin, mul_one]
    rw [hsum]
    unfold firstBeatReward
    simp [W, hW, w, ENNReal.ofReal_coe_nnreal]
  · have hlose : ∀ i : Fin n,
        (singleSamplePostedPrice s π).allocation (fun j => (v j : ℝ)) i = 0 := by
      intro i
      exact acceptAllocation_eq_zero_iff.mpr fun hw =>
        hW ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hacc i).mp hw.1⟩⟩
    unfold firstBeatReward
    simp [W, hW, hlose]

/-- **Prior-independent single-sample posted-price welfare `1/2`-approximation**
([RubinsteinWangWeinberg2020], Theorem 1; [Roughgarden2013CS364A], Lecture 6): drawing one sample
vector `s ~ piFin μ` and uniform tie-breaker `π` gives a DSIC, individually rational posted-price
mechanism `singleSamplePostedPrice s π` whose expected social welfare is at least `1/2` of the
Vickrey auction's expected social welfare. -/
theorem expectedWelfare_vickrey_le_two_mul_singleSamplePostedPrice {n : ℕ}
    (μ : Fin n → PMF ℝ≥0) :
    expectedWelfare Vickrey.allocation μ ≤
      2 * ∑' s, piFin μ s *
        ∑' π, uniformOfFintype (Equiv.Perm (Fin (2 * n))) π *
          expectedWelfare (singleSamplePostedPrice s π).allocation μ := by
  rw [expectedWelfare_vickrey_eq_expectedMax]
  simp_rw [expectedWelfare_singleSamplePostedPrice]
  rw [← singleSampleExpectedReward_eq]
  exact expectedMax_le_two_mul_singleSampleExpectedReward μ

/-! ### Tight `1/2` barrier for fixed-order posted-price revenue and welfare -/

/-- Two-bidder laws for the gap-of-2 witness ([ChawlaHartlineMalecSivan2010], Appendix D.2, p. 19):
bidder `0` has sure value `1`, and bidder `1` has value `k + 1` with probability `1 / (k + 1)` and
`0` otherwise. -/
noncomputable def tightBidderLaws (k : ℕ) : Fin 2 → PMF ℝ≥0 :=
  ![PMF.pure 1, longShot k]

/-- Converting `tightBidderLaws k` to a list recovers `tightLaws k`. -/
theorem list_ofFn_tightBidderLaws (k : ℕ) : List.ofFn (tightBidderLaws k) = tightLaws k := by
  simp [tightBidderLaws, tightLaws_eq]

/-- For an individually rational mechanism, expected revenue never exceeds expected social welfare.
-/
theorem expectedRevenuePMF_le_expectedWelfare {n : ℕ} {M : Mechanism (Fin n)} (hIR : M.IsIR)
    (μ : Fin n → PMF ℝ≥0) :
    expectedRevenuePMF M μ ≤ expectedWelfare M.allocation μ := by
  refine tsum_le_tsum fun v => mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  have hv : 0 ≤ (fun j : Fin n => (v j : ℝ)) := fun j => NNReal.coe_nonneg _
  refine Finset.sum_le_sum fun i _ => ?_
  have hir := hIR i _ hv
  simp only [Mechanism.utility] at hir
  linarith

/-- On `tightBidderLaws k`, *every* posted-price mechanism in arrival order `(0, 1)` gets expected
welfare (and hence expected revenue) at most `1`. -/
theorem expectedWelfare_postedPrice_tightBidderLaws_le_one (k : ℕ) (p : Fin 2 → ℝ) :
    expectedWelfare (postedPrice p).allocation (tightBidderLaws k) ≤ 1 := by
  let stop : List ℝ≥0 → Bool
    | [x] => decide (p 0 ≤ (x : ℝ))
    | [y, _] => decide (p 1 ≤ (y : ℝ))
    | _ => false
  have hle := expectedReward_tightLaws_le k stop
  refine le_trans ?_ hle
  rw [expectedWelfare, expectedReward, ← list_ofFn_tightBidderLaws k, tsum_jointLaw_ofFn_mul]
  refine tsum_le_tsum fun v => mul_le_mul_right ?_ _
  rw [Fin.sum_univ_two]
  have hlist : List.ofFn v = [v 0, v 1] := by simp
  rw [hlist, payoff_cons]
  by_cases hp0 : p 0 ≤ (v 0 : ℝ)
  · have hw0 : AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 0 :=
      ⟨hp0, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
    have hl1 : ¬ AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 1 :=
      fun hw => hw.2 0 Fin.zero_lt_one hp0
    have hs0 : stop [v 0] = true := decide_eq_true hp0
    simp only [postedPrice, acceptMechanism, acceptAllocation_eq_one_iff.mpr hw0,
      acceptAllocation_eq_zero_iff.mpr hl1, mul_one, mul_zero, add_zero, hs0, ↓reduceIte, reward,
      ENNReal.ofReal_coe_nnreal, le_rfl]
  · have hl0 : ¬ AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 0 := fun hw => hp0 hw.1
    have hs0 : stop [v 0] = false := decide_eq_false hp0
    rw [hs0, payoff_cons]
    by_cases hp1 : p 1 ≤ (v 1 : ℝ)
    · have hw1 : AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 1 := by
        refine ⟨hp1, fun j hj => ?_⟩
        have hj0 : j = 0 := by have := j.isLt; omega
        subst hj0
        exact hp0
      have hs1 : stop [v 1, v 0] = true := decide_eq_true hp1
      simp only [Bool.false_eq_true, ↓reduceIte, postedPrice, acceptMechanism,
        acceptAllocation_eq_zero_iff.mpr hl0, acceptAllocation_eq_one_iff.mpr hw1, mul_zero,
        mul_one, zero_add, hs1, reward, ENNReal.ofReal_coe_nnreal, le_rfl]
    · have hl1 : ¬ AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 1 := fun hw => hp1 hw.1
      have hs1 : stop [v 1, v 0] = false := decide_eq_false hp1
      simp [hs1, payoff_nil, postedPrice, acceptMechanism,
        acceptAllocation_eq_zero_iff.mpr hl0, acceptAllocation_eq_zero_iff.mpr hl1]

/-- Approaching the long-shot bidder first at price `k + 1` and then the sure-value bidder at price
`1` extracts the full prophet expectation `(2k + 1) / (k + 1)` as revenue
([ChawlaHartlineMalecSivan2010], Appendix D.2, p. 19). -/
theorem expectedRevenuePMF_swapped_tightBidderLaws (k : ℕ) :
    expectedRevenuePMF (postedPrice ![(k + 1 : ℝ), 1]) ![longShot k, PMF.pure 1] =
      (2 * k + 1) / (k + 1) := by
  let pay2 : List ℝ≥0 → ℝ≥0∞
    | [x, y] => ENNReal.ofReal (∑ i : Fin 2, (postedPrice ![(k + 1 : ℝ), 1]).payment
        (fun j => (![x, y] j : ℝ)) i)
    | _ => 0
  have hrew : expectedRevenuePMF (postedPrice ![(k + 1 : ℝ), 1]) ![longShot k, PMF.pure 1] =
      ∑' xs, jointLaw [longShot k, PMF.pure 1] xs * pay2 xs := by
    have hofFn : List.ofFn (![longShot k, PMF.pure 1] : Fin 2 → PMF ℝ≥0) =
        [longShot k, PMF.pure 1] := by simp
    rw [← hofFn, tsum_jointLaw_ofFn_mul, expectedRevenuePMF]
    refine tsum_congr fun v => ?_
    have hv : List.ofFn v = [v 0, v 1] := by simp
    have hmat : (![v 0, v 1] : Fin 2 → ℝ≥0) = v := by
      funext j
      fin_cases j <;> rfl
    simp only [hv, pay2, hmat]
  rw [hrew, tsum_jointLaw_cons_mul, tsum_longShot_mul]
  have hp1 : (∑' xs, jointLaw [PMF.pure (1 : ℝ≥0)] xs * pay2 (((k : ℝ≥0) + 1) :: xs)) = k + 1 := by
    rw [tsum_jointLaw_cons_mul, tsum_pure_mul, tsum_jointLaw_nil_mul]
    dsimp only [pay2]
    rw [Fin.sum_univ_two]
    have hvec : (fun j : Fin 2 => (![(k : ℝ≥0) + 1, 1] j : ℝ)) = ![(k + 1 : ℝ), 1] := by
      funext j
      fin_cases j <;> simp
    rw [hvec]
    have hw0 : AcceptWins (fun i z => ![(k + 1 : ℝ), 1] i ≤ z) ![(k + 1 : ℝ), 1] 0 :=
      ⟨by simp, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
    have hl1 : ¬ AcceptWins (fun i z => ![(k + 1 : ℝ), 1] i ≤ z) ![(k + 1 : ℝ), 1] 1 :=
      fun hw => hw.2 0 Fin.zero_lt_one (by simp)
    simp only [postedPrice, acceptMechanism, acceptAllocation_eq_one_iff.mpr hw0,
      acceptAllocation_eq_zero_iff.mpr hl1, Matrix.cons_val_zero, Matrix.cons_val_one, mul_one,
      mul_zero, add_zero]
    rw [ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one, ENNReal.ofReal_natCast,
      ENNReal.ofReal_one]
  have hp0 : (∑' xs, jointLaw [PMF.pure (1 : ℝ≥0)] xs * pay2 (0 :: xs)) = 1 := by
    rw [tsum_jointLaw_cons_mul, tsum_pure_mul, tsum_jointLaw_nil_mul]
    dsimp only [pay2]
    rw [Fin.sum_univ_two]
    have hvec : (fun j : Fin 2 => (![(0 : ℝ≥0), 1] j : ℝ)) = ![(0 : ℝ), 1] := by
      funext j
      fin_cases j <;> simp
    rw [hvec]
    have hlt0 : ¬ ![(k + 1 : ℝ), 1] 0 ≤ ![(0 : ℝ), 1] 0 := by
      simp only [Matrix.cons_val_zero, not_le]
      positivity
    have hl0 : ¬ AcceptWins (fun i z => ![(k + 1 : ℝ), 1] i ≤ z) ![(0 : ℝ), 1] 0 :=
      fun hw => hlt0 hw.1
    have hw1 : AcceptWins (fun i z => ![(k + 1 : ℝ), 1] i ≤ z) ![(0 : ℝ), 1] 1 := by
      refine ⟨by simp, fun j hj => ?_⟩
      fin_cases j
      · exact hlt0
      · exact absurd hj (lt_irrefl _)
    simp only [postedPrice, acceptMechanism, acceptAllocation_eq_zero_iff.mpr hl0,
      acceptAllocation_eq_one_iff.mpr hw1, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero,
      mul_one, zero_add, ENNReal.ofReal_one]
  have hcast : ((k + 1 : ℝ≥0) : ℝ≥0) = (k : ℝ≥0) + 1 := rfl
  rw [hcast, hp1, hp0, mul_one]
  congr 1
  ring

/-- **Tightness of `1/2` for fixed-order posted-price revenue and welfare**
([ChawlaHartlineMalecSivan2010], Appendix D.2, "An example with a gap of 2", p. 19): for every
`c > 1/2`, there exists `k` such that on `tightBidderLaws k`, *every* sequential posted-price
mechanism `postedPrice p` in arrival order `(0, 1)` collects less than `c` times the optimal
sequential posted-price revenue `(2k + 1) / (k + 1)` (and less than `c` times Vickrey welfare). -/
theorem exists_postedPrice_revenue_lt {c : ℝ≥0∞} (hc : 1 < 2 * c) :
    ∃ k, ∀ p : Fin 2 → ℝ,
      expectedRevenuePMF (postedPrice p) (tightBidderLaws k) <
        c * expectedRevenuePMF (postedPrice ![(k + 1 : ℝ), 1]) ![longShot k, PMF.pure 1] ∧
      expectedWelfare (postedPrice p).allocation (tightBidderLaws k) <
        c * expectedWelfare Vickrey.allocation (tightBidderLaws k) := by
  obtain ⟨k, hk⟩ := exists_tightLaws_lt hc
  refine ⟨k, fun p => ?_⟩
  have hgap : (1 : ℝ≥0∞) < c * ((2 * k + 1) / (k + 1)) := by
    have hstop := hk (fun _ => true)
    have h1 : expectedReward (fun _ => true) (tightLaws k) = 1 := by
      rw [expectedReward, tightLaws_eq, tsum_jointLaw_cons_mul, tsum_pure_mul]
      simp [payoff_cons, reward]
    rwa [h1, expectedMax_tightLaws] at hstop
  have hwel : expectedWelfare (postedPrice p).allocation (tightBidderLaws k) <
      c * ((2 * k + 1) / (k + 1)) :=
    (expectedWelfare_postedPrice_tightBidderLaws_le_one k p).trans_lt hgap
  have hrev : expectedRevenuePMF (postedPrice p) (tightBidderLaws k) <
      c * ((2 * k + 1) / (k + 1)) :=
    (expectedRevenuePMF_le_expectedWelfare (postedPrice_isIR p) _).trans_lt hwel
  have hvick : expectedWelfare Vickrey.allocation (tightBidderLaws k) = (2 * k + 1) / (k + 1) := by
    rw [expectedWelfare_vickrey_eq_expectedMax, list_ofFn_tightBidderLaws, expectedMax_tightLaws]
  rw [expectedRevenuePMF_swapped_tightBidderLaws, hvick]
  exact ⟨hrev, hwel⟩

end ProphetWelfare

/-! ### Non-i.i.d. regular revenue `1/2`-approximation via posted prices (`Measure.pi μ`) -/

section NonIIDRevenue

variable {ι : Type*} [Fintype ι] {μ : ι → Measure ℝ} {f : ι → ℝ → NNReal} {h : ι → ℝ}

/-- The optimal single-item virtual surplus `max(0, maxᵢ φᵢ(vᵢ))` at valuation profile `v`. -/
noncomputable def posVirtualSurplus (μ : ι → Measure ℝ) (f : ι → ℝ → NNReal) (v : ι → ℝ) : ℝ :=
  Finset.univ.fold max 0 fun i => virtualValue (μ i) (f i) (v i)

theorem posVirtualSurplus_nonneg (μ : ι → Measure ℝ) (f : ι → ℝ → NNReal) (v : ι → ℝ) :
    0 ≤ posVirtualSurplus μ f v :=
  (Finset.le_fold_max _).mpr (Or.inl le_rfl)

theorem virtualValue_le_posVirtualSurplus (μ : ι → Measure ℝ) (f : ι → ℝ → NNReal)
    (v : ι → ℝ) (i : ι) :
    virtualValue (μ i) (f i) (v i) ≤ posVirtualSurplus μ f v :=
  (Finset.le_fold_max _).mpr (Or.inr ⟨i, Finset.mem_univ i, le_rfl⟩)

omit [Fintype ι] in
private theorem integrable_fold_max {ν : Measure (ι → ℝ)} (s : Finset ι) {g : ι → (ι → ℝ) → ℝ}
    (h0 : Integrable (fun _ : ι → ℝ => (0 : ℝ)) ν) (hg : ∀ i ∈ s, Integrable (g i) ν) :
    Integrable (fun v => s.fold max 0 fun i => g i v) ν := by
  classical
  induction s using Finset.induction_on with
  | empty => exact h0
  | insert a s ha ih =>
      have ha_int : Integrable (g a) ν := hg a (Finset.mem_insert_self a s)
      have hs_int : Integrable (fun v => s.fold max 0 fun i => g i v) ν :=
        ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
      have hsup : Integrable (fun v => max (g a v) (s.fold max 0 (fun i => g i v))) ν :=
        ha_int.sup hs_int
      simpa only [Finset.fold_insert ha] using hsup

theorem integrable_posVirtualSurplus [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i)) :
    Integrable (posVirtualSurplus μ f) (Measure.pi μ) :=
  integrable_fold_max Finset.univ (integrable_zero _ _ _) fun i _ =>
    integrable_comp_eval (hμ i).integrable_virtualValue

/-- Every single-item-feasible allocation has virtual welfare at most `posVirtualSurplus`. -/
theorem sum_virtualValue_mul_le_posVirtualSurplus (v : ι → ℝ) {y : ι → ℝ}
    (hy : y ∈ Vickrey.singleItemFeasible) :
    ∑ i, virtualValue (μ i) (f i) (v i) * y i ≤ posVirtualSurplus μ f v := by
  have hy0 : ∀ i, 0 ≤ y i := fun i => by
    rcases hy.1 i with h0 | h1
    · rw [h0]
    · rw [h1]; exact zero_le_one
  calc ∑ i, virtualValue (μ i) (f i) (v i) * y i
      ≤ ∑ i, posVirtualSurplus μ f v * y i :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_right (virtualValue_le_posVirtualSurplus μ f v i) (hy0 i)
    _ = posVirtualSurplus μ f v * ∑ i, y i := by rw [Finset.mul_sum]
    _ ≤ posVirtualSurplus μ f v * 1 :=
        mul_le_mul_of_nonneg_left hy.2 (posVirtualSurplus_nonneg μ f v)
    _ = posVirtualSurplus μ f v := mul_one _

/-- **Chawla–Hartline / Roughgarden posted prices** ([ChawlaHartlineMalecSivan2010], Appendix D.2,
p. 19; [Roughgarden2013CS364A], Lecture 6, §3, pp. 4–5): set target virtual threshold
`t = E[posVirtualSurplus] / 2` and offer bidder `i` the inverse virtual price
`reservePrice (fun z => φᵢ(z) − t)`. -/
noncomputable def virtualPostedPrices (μ : ι → Measure ℝ) (f : ι → ℝ → NNReal) : ι → ℝ :=
  let t := (∫ v, posVirtualSurplus μ f v ∂Measure.pi μ) / 2
  fun i => reservePrice fun z => virtualValue (μ i) (f i) z - t

theorem isReserveThreshold_virtualPostedPrices (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hreg : ∀ i, IsRegular (μ i) (f i) (h i)) (i : ι) :
    let t := (∫ v, posVirtualSurplus μ f v ∂Measure.pi μ) / 2
    IsReserveThreshold (fun z => virtualValue (μ i) (f i) z - t) (virtualPostedPrices μ f i) := by
  intro t
  have ht0 : 0 ≤ t := div_nonneg
    (integral_nonneg fun v => posVirtualSurplus_nonneg μ f v) (by norm_num)
  refine isReserveThreshold_reservePrice ?_ ?_
  · intro a ha b hb hab
    exact sub_le_sub_right (((hreg i).strictMonoOn_Ioi (hμ i)).monotoneOn ha hb hab) t
  · refine ⟨max (h i) (t + 1), lt_of_lt_of_le (by linarith) (le_max_right _ _), ?_⟩
    rw [(hμ i).virtualValue_eq_self (le_max_left _ _)]
    linarith [le_max_right (h i) (t + 1)]

theorem virtualPostedPrices_nonneg (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hreg : ∀ i, IsRegular (μ i) (f i) (h i)) :
    0 ≤ virtualPostedPrices μ f :=
  fun i => (isReserveThreshold_virtualPostedPrices hμ hreg i).1

/-- **Non-i.i.d. regular single-item revenue `1/2`-approximation by sequential posted pricing**
([ChawlaHartlineMalecSivan2010], Theorem 10 (`k = 1`), p. 9, and Appendix D.2, p. 19;
[Roughgarden2013CS364A], Lecture 6, §3, pp. 4–5).

Setting: bidders `i : ι` have independent (not necessarily identical) regular distributions `μ i`
with densities `f i` on `[0, h i]`.

Conclusion: the sequential posted-price mechanism `postedPrice (virtualPostedPrices μ f)` (which is
DSIC, individually rational, normalized, and group strategy-proof) collects expected revenue at
least `1/2` of `∫ posVirtualSurplus`, and hence at least `1/2` of the expected revenue of *every*
DSIC, individually rational, measurable single-item mechanism `M` (in any fixed arrival order). -/
theorem integral_sum_payment_le_two_mul_virtualPostedPrices [LinearOrder ι]
    [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, HasValueDensity (μ i) (f i) (h i))
    (hreg : ∀ i, IsRegular (μ i) (f i) (h i))
    {M : Mechanism ι} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ Vickrey.singleItemFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤
      2 * ∫ v, ∑ i, (postedPrice (virtualPostedPrices μ f)).payment v i ∂Measure.pi μ := by
  classical
  -- Step 1: Bound `Rev(M)` by `E_opt := ∫ v, posVirtualSurplus μ f v ∂Measure.pi μ`.
  have hMB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ 1 := fun v hv i => by
    rcases (hMX v hv).1 i with h0 | h1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
  have hM_le_opt : ∫ v, ∑ i, M.payment v i ∂Measure.pi μ ≤
      ∫ v, posVirtualSurplus μ f v ∂Measure.pi μ := by
    refine (hM.integral_sum_payment_le hIR hμ hMm hMB).trans ?_
    refine integral_mono_ae
      (integrable_finsetSum _ fun i _ => integrable_virtualValue_mul hμ i (hMm i)
        fun v hv => hMB v hv i)
      (integrable_posVirtualSurplus hμ) ?_
    filter_upwards [ae_nonneg hμ] with v hv
    exact sum_virtualValue_mul_le_posVirtualSurplus v (hMX v hv)
  -- Step 2: Express `Rev(postedPrice p)` as expected virtual welfare via Myerson's identity.
  let p := virtualPostedPrices μ f
  let E_opt := ∫ v, posVirtualSurplus μ f v ∂Measure.pi μ
  let t := E_opt / 2
  have hp0 : 0 ≤ p := virtualPostedPrices_nonneg hμ hreg
  have hpB : ∀ v, 0 ≤ v → ∀ i, |(postedPrice p).allocation v i| ≤ 1 := fun v _ i => by
    rcases (postedPrice_mem_singleItemFeasible p v).1 i with h0 | h1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
  have hrev_eq : ∫ v, ∑ i, (postedPrice p).payment v i ∂Measure.pi μ =
      ∫ v, ∑ i, virtualValue (μ i) (f i) (v i) * (postedPrice p).allocation v i ∂Measure.pi μ :=
    (postedPrice_isDSIC p).integral_sum_payment_eq (postedPrice_isNormalized hp0) hμ
      (measurable_postedPrice_allocation p) hpB
  suffices hhalf : E_opt ≤
      2 * ∫ v, ∑ i, virtualValue (μ i) (f i) (v i) * (postedPrice p).allocation v i
        ∂Measure.pi μ by
    rw [hrev_eq]
    exact hM_le_opt.trans hhalf
  -- Step 3: Decompose virtual welfare via Roughgarden Lecture 6, eqs. (2)–(5).
  have ht0 : 0 ≤ t := div_nonneg
    (integral_nonneg fun v => posVirtualSurplus_nonneg μ f v) (by norm_num)
  let priorReject : ι → (ι → ℝ) → ℝ := fun i v => if ∀ j < i, v j < p j then 1 else 0
  let allReject : (ι → ℝ) → ℝ := fun v => 1 - ∑ i, (postedPrice p).allocation v i
  let excess : ι → ℝ → ℝ := fun i z => max (virtualValue (μ i) (f i) z - t) 0
  have hall_le_prior : ∀ (i : ι) (v : ι → ℝ), allReject v ≤ priorReject i v := by
    intro i v
    by_cases hprev : ∀ j < i, v j < p j
    · have hpr : priorReject i v = 1 := by dsimp only [priorReject]; split_ifs; rfl
      rw [hpr]
      dsimp only [allReject]
      have hsum_nn : 0 ≤ ∑ k, (postedPrice p).allocation v k :=
        Finset.sum_nonneg fun k _ => acceptAllocation_nonneg _ v k
      linarith
    · push Not at hprev
      obtain ⟨j, hji, hpj⟩ := hprev
      -- Since `p j ≤ v j`, the smallest `w` with `p w ≤ v w` wins, so `∑ k, alloc v k = 1`!
      let A := Finset.univ.filter fun k : ι => p k ≤ v k
      have hAne : A.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpj⟩⟩
      let w := A.min' hAne
      have hwin : AcceptWins (fun k z => p k ≤ z) v w :=
        ⟨(Finset.mem_filter.mp (Finset.min'_mem A hAne)).2,
          fun m hm hpm =>
            not_le.mpr hm (Finset.min'_le A m (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpm⟩))⟩
      have hsum1 : ∑ k, (postedPrice p).allocation v k = 1 := by
        simp only [postedPrice, acceptMechanism]
        rw [Finset.sum_eq_single w
          (fun k _ hkw => acceptAllocation_eq_zero_iff.mpr fun hkw' => hkw (hkw'.unique hwin))
          (fun hm => absurd (Finset.mem_univ w) hm),
          acceptAllocation_eq_one_iff.mpr hwin]
      have hpf : ¬ (∀ k < i, v k < p k) := fun hall => not_lt.mpr hpj (hall j hji)
      have hpr0 : priorReject i v = 0 := by dsimp only [priorReject]; split_ifs; rfl
      rw [hpr0]
      simp only [allReject, hsum1, sub_self, le_rfl]
  have hall_nonneg : ∀ v : ι → ℝ, 0 ≤ allReject v := by
    intro v
    have hfeas := (postedPrice_mem_singleItemFeasible p v).2
    dsimp only [allReject]
    linarith
  -- Almost-everywhere positivity and non-tie condition (`NullSingletonClass`).
  have hae_ne : ∀ (i : ι) (c : ℝ), ∀ᵐ v ∂Measure.pi μ, v i ≠ c := fun i c => by
    have := (hμ i).nullSingletonClass
    have hz : ∀ᵐ z ∂(μ i), z ≠ c := by
      rw [ae_iff]
      simpa only [Classical.not_not, Set.ofPred_eq_eq_singleton] using measure_singleton c
    exact (Measure.quasiMeasurePreserving_eval μ i).ae hz
  have hae_pos_ne : ∀ᵐ v ∂Measure.pi μ, ∀ i, 0 < v i ∧ v i ≠ p i := by
    have hae0 : ∀ᵐ v ∂Measure.pi μ, ∀ i, v i ≠ 0 := ae_all_iff.mpr fun i => hae_ne i 0
    have haep : ∀ᵐ v ∂Measure.pi μ, ∀ i, v i ≠ p i := ae_all_iff.mpr fun i => hae_ne i (p i)
    filter_upwards [ae_nonneg hμ, hae0, haep] with v hv0 hne0 hnep i
    exact ⟨lt_of_le_of_ne (hv0 i) (Ne.symm (hne0 i)), hnep i⟩
  -- Pointwise a.e. decomposition of `φ_i (v i) * alloc v i`.
  have hae_decomp : ∀ᵐ v ∂Measure.pi μ,
      ∑ i, virtualValue (μ i) (f i) (v i) * (postedPrice p).allocation v i =
        t * (1 - allReject v) + ∑ i, priorReject i v * excess i (v i) := by
    filter_upwards [hae_pos_ne] with v hv
    have h1 : t * (1 - allReject v) = ∑ i, t * (postedPrice p).allocation v i := by
      dsimp only [allReject]
      rw [← Finset.mul_sum]
      ring
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hthr := isReserveThreshold_virtualPostedPrices hμ hreg i
    change IsReserveThreshold (fun z => virtualValue (μ i) (f i) z - t) (p i) at hthr
    by_cases hprev : ∀ j < i, v j < p j
    · have hpr : priorReject i v = 1 := by dsimp only [priorReject]; split_ifs; rfl
      rw [hpr, one_mul]
      by_cases hpi : p i ≤ v i
      · have hpilt : p i < v i := lt_of_le_of_ne hpi (Ne.symm (hv i).2)
        have hφge : 0 ≤ virtualValue (μ i) (f i) (v i) - t := hthr.2.1 (v i) hpilt
        have hwin : AcceptWins (fun k z => p k ≤ z) v i :=
          ⟨hpi, fun j hj => not_le.mpr (hprev j hj)⟩
        have halloc1 : (postedPrice p).allocation v i = 1 :=
          acceptAllocation_eq_one_iff.mpr hwin
        rw [halloc1, mul_one, mul_one, show excess i (v i) = virtualValue (μ i) (f i) (v i) - t from
          max_eq_left hφge]
        ring
      · have hφle : virtualValue (μ i) (f i) (v i) - t ≤ 0 := by
          by_contra hgt
          exact hpi (hthr.2.2 (v i) (hv i).1 (not_le.mp hgt).le)
        have hlose : ¬ AcceptWins (fun k z => p k ≤ z) v i := fun hw => hpi hw.1
        have halloc0 : (postedPrice p).allocation v i = 0 :=
          acceptAllocation_eq_zero_iff.mpr hlose
        rw [halloc0, show excess i (v i) = 0 from max_eq_right hφle]
        ring
    · have hpr : priorReject i v = 0 := by dsimp only [priorReject]; split_ifs; rfl
      have hlose : ¬ AcceptWins (fun k z => p k ≤ z) v i := by
        intro hw
        refine hprev fun j hj => not_le.mp (hw.2 j hj)
      have halloc0 : (postedPrice p).allocation v i = 0 :=
        acceptAllocation_eq_zero_iff.mpr hlose
      rw [hpr, halloc0]
      ring
  -- Measurability & integrability of `priorReject`, `allReject`, and `excess`.
  have hm_prior : ∀ i, Measurable (priorReject i) := by
    intro i
    have hset : MeasurableSet {v : ι → ℝ | ∀ j, j < i → v j < p j} :=
      (Measurable.forall fun j => Measurable.imp measurable_const
        (measurableSet_lt (measurable_pi_apply j) measurable_const).mem).setOf
    exact Measurable.ite hset measurable_const measurable_const
  have hint_prior : ∀ i, Integrable (priorReject i) (Measure.pi μ) := by
    intro i
    refine Integrable.of_bound (hm_prior i).aestronglyMeasurable 1 (ae_of_all _ fun v => ?_)
    dsimp only [priorReject]
    split_ifs <;> norm_num
  have hint_alloc_sum : Integrable (fun v => ∑ i, (postedPrice p).allocation v i)
      (Measure.pi μ) := by
    refine integrable_finsetSum _ fun i _ => ?_
    refine Integrable.of_bound (measurable_postedPrice_allocation p i).aestronglyMeasurable 1
      (ae_of_all _ fun v => ?_)
    rcases (postedPrice_mem_singleItemFeasible p v).1 i with h0 | h1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
  have hint_allReject : Integrable allReject (Measure.pi μ) :=
    (integrable_const 1).sub hint_alloc_sum
  have hint_one_sub : Integrable (fun v => 1 - allReject v) (Measure.pi μ) :=
    (integrable_const 1).sub hint_allReject
  have hm_excess : ∀ i, Measurable (excess i) := fun i =>
    (((hμ i).measurable_virtualValue).sub measurable_const).max measurable_const
  have hint_excess_i : ∀ i, Integrable (excess i) (μ i) := fun i =>
    (((hμ i).integrable_virtualValue).sub (integrable_const t)).sup (integrable_zero _ _ _)
  have hint_excess_pi : ∀ i, Integrable (fun v : ι → ℝ => excess i (v i)) (Measure.pi μ) :=
    fun i => integrable_comp_eval (hint_excess_i i)
  have hint_prod : ∀ i, Integrable (fun v => priorReject i v * excess i (v i)) (Measure.pi μ) := by
    intro i
    refine Integrable.mono' (hint_excess_pi i)
      ((hm_prior i).mul ((hm_excess i).comp (measurable_pi_apply i))).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    have hex0 : 0 ≤ excess i (v i) := le_max_right _ _
    have hpr_abs : |priorReject i v| ≤ 1 := by
      dsimp only [priorReject]; split_ifs <;> norm_num
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hex0]
    exact mul_le_of_le_one_left hex0 hpr_abs
  -- Factor each `∫ priorReject i v * excess i (v i)` by coordinate independence!
  have hfactor : ∀ i,
      ∫ v, priorReject i v * excess i (v i) ∂Measure.pi μ =
        (∫ v, priorReject i v ∂Measure.pi μ) * ∫ z, excess i z ∂μ i := by
    intro i
    have hindep : ∀ (v : ι → ℝ) (z : ℝ),
        (fun w => priorReject i (Function.update v i z) * excess i w) =
          fun w => priorReject i v * excess i w := by
      intro v z
      funext w
      have hp_upd : priorReject i (Function.update v i z) = priorReject i v := by
        dsimp only [priorReject]
        have hiff : (∀ j < i, Function.update v i z j < p j) ↔ ∀ j < i, v j < p j :=
          forall_congr' fun j => imp_congr_right fun hj => by rw [Function.update_of_ne hj.ne]
        simp only [hiff]
      rw [hp_upd]
    rw [integral_apply_eval_eq_integral_integral μ (Φ := fun v z => priorReject i v * excess i z)
      hindep (hint_prod i)]
    simp_rw [integral_const_mul]
    rw [integral_mul_const]
  -- Prophet upper bound on `E_opt`: `posVirtualSurplus v ≤ t + ∑ i, excess i (v i)`.
  have hprophet_pt : ∀ v : ι → ℝ, posVirtualSurplus μ f v ≤ t + ∑ i, excess i (v i) := by
    intro v
    have hex_sum_nn : 0 ≤ ∑ i, excess i (v i) :=
      Finset.sum_nonneg fun i _ => le_max_right _ _
    refine (Finset.fold_max_le (t + ∑ i, excess i (v i))).mpr ⟨by linarith, fun i _ => ?_⟩
    have hle_i : virtualValue (μ i) (f i) (v i) ≤ t + excess i (v i) := by
      have : virtualValue (μ i) (f i) (v i) - t ≤ excess i (v i) := le_max_left _ _
      linarith
    have hle_sum : excess i (v i) ≤ ∑ j, excess j (v j) :=
      Finset.single_le_sum (f := fun j => excess j (v j)) (fun j _ => le_max_right _ _)
        (Finset.mem_univ i)
    linarith
  have hE_opt_le : E_opt ≤ t + ∑ i, ∫ z, excess i z ∂μ i := by
    have hint_rhs : Integrable (fun v => t + ∑ i, excess i (v i)) (Measure.pi μ) :=
      (integrable_const t).add (integrable_finsetSum _ fun i _ => hint_excess_pi i)
    calc E_opt ≤ ∫ v, (t + ∑ i, excess i (v i)) ∂Measure.pi μ :=
          integral_mono (integrable_posVirtualSurplus hμ) hint_rhs hprophet_pt
      _ = t + ∑ i, ∫ v, excess i (v i) ∂Measure.pi μ := by
          rw [integral_add (integrable_const t)
            (integrable_finsetSum _ fun i _ => hint_excess_pi i),
            integral_const, probReal_univ, one_smul,
            integral_finsetSum _ fun i _ => hint_excess_pi i]
      _ = t + ∑ i, ∫ z, excess i z ∂μ i := by
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_apply_eval_eq_integral_integral μ (Φ := fun _ z => excess i z)
            (fun _ _ => rfl) (hint_excess_pi i), integral_const, probReal_univ, one_smul]
  -- Combine lower and upper bounds at `t = E_opt / 2`!
  let R := ∫ v, allReject v ∂Measure.pi μ
  have hR0 : 0 ≤ R := integral_nonneg hall_nonneg
  have h1_sub_R : ∫ v, (1 - allReject v) ∂Measure.pi μ = 1 - R := by
    rw [integral_sub (integrable_const 1) hint_allReject, integral_const, probReal_univ, one_smul]
  have hvw_eq : ∫ v, ∑ i, virtualValue (μ i) (f i) (v i) * (postedPrice p).allocation v i
      ∂Measure.pi μ =
      t * (1 - R) + ∑ i, (∫ v, priorReject i v ∂Measure.pi μ) * ∫ z, excess i z ∂μ i := by
    rw [integral_congr_ae hae_decomp,
      integral_add (hint_one_sub.const_mul t) (integrable_finsetSum _ fun i _ => hint_prod i),
      integral_const_mul, h1_sub_R, integral_finsetSum _ fun i _ => hint_prod i]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hfactor i
  have hsum_ge : R * (E_opt - t) ≤
      ∑ i, (∫ v, priorReject i v ∂Measure.pi μ) * ∫ z, excess i z ∂μ i := by
    calc R * (E_opt - t)
        ≤ R * ∑ i, ∫ z, excess i z ∂μ i :=
          mul_le_mul_of_nonneg_left (by linarith) hR0
      _ = ∑ i, R * ∫ z, excess i z ∂μ i := by rw [Finset.mul_sum]
      _ ≤ ∑ i, (∫ v, priorReject i v ∂Measure.pi μ) * ∫ z, excess i z ∂μ i := by
          refine Finset.sum_le_sum fun i _ => ?_
          refine mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => le_max_right _ _)
          exact integral_mono hint_allReject (hint_prior i) (hall_le_prior i)
  rw [hvw_eq]
  have ht_def : t = E_opt / 2 := rfl
  nlinarith

end NonIIDRevenue

/-! ### The Bulow–Klemperer theorem -/

section BulowKlemperer

/-- **The Bulow–Klemperer theorem** ([BulowKlemperer1996];
[Roughgarden2013CS364A], Lecture 6, Theorem 4.1, p. 6).

Setting: `n` i.i.d. bidders have valuations drawn from a regular distribution `μ` with density `f`
on `[0, h]`.

Conclusion: the prior-independent Vickrey (second-price) auction with `n + 1` i.i.d. bidders and
*zero reserve price* collects expected revenue at least that of *every* DSIC, individually rational,
measurable `n`-bidder single-item mechanism `M` (including Myerson's `n`-bidder optimal auction). -/
theorem bulow_klemperer {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ] {f : ℝ → NNReal}
    {h : ℝ} (hμ : HasValueDensity μ f h) (hreg : IsRegular μ f h)
    {M : Mechanism (Fin n)} (hM : M.IsDSIC) (hIR : M.IsIR)
    (hMX : ∀ v, 0 ≤ v → M.allocation v ∈ Vickrey.singleItemFeasible)
    (hMm : ∀ i, Measurable fun v => M.allocation v i) :
    ∫ v, ∑ i : Fin n, M.payment v i ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ v, ∑ j : Fin (n + 1), (Vickrey.mechanism (ι := Fin (n + 1))).payment v j
        ∂Measure.pi (fun _ : Fin (n + 1) => μ) := by
  -- Step 1: Bound `M` by Myerson's `n`-bidder optimal virtual welfare.
  let optAlloc : (Fin n → ℝ) → Fin n → ℝ := Vickrey.reserveAllocation (virtualValue μ f)
  have hopt_meas : ∀ i : Fin n, Measurable fun v => optAlloc v i :=
    fun i => Vickrey.measurable_reserveAllocation hμ.measurable_virtualValue i
  have hopt_B : ∀ (v : Fin n → ℝ), 0 ≤ v → ∀ i, |optAlloc v i| ≤ 1 := fun v _ i => by
    dsimp only [optAlloc]
    rcases Vickrey.reserveAllocation_binary (virtualValue μ f) v i with h0 | h1
    · rw [h0]; norm_num
    · rw [h1]; norm_num
  have hM_le : ∫ v, ∑ i : Fin n, M.payment v i ∂Measure.pi (fun _ : Fin n => μ) ≤
      ∫ v, ∑ i : Fin n, virtualValue μ f (v i) * optAlloc v i
        ∂Measure.pi (fun _ : Fin n => μ) := by
    refine (Vickrey.integral_sum_payment_le_reserve hμ hreg hM hIR hMX hMm).trans_eq ?_
    exact integral_sum_myersonPayment_eq (fun _ => hμ) hopt_meas hopt_B
  -- Step 2: Embed `optAlloc` into `Fin (n + 1)` by awarding any unsold item to `Fin.last n`.
  let μ₁ := fun _ : Fin (n + 1) => μ
  let initOf : (Fin (n + 1) → ℝ) → Fin n → ℝ := fun v i => v (Fin.castSucc i)
  let bkAlloc : (Fin (n + 1) → ℝ) → Fin (n + 1) → ℝ := fun v =>
    Fin.lastCases (1 - ∑ i : Fin n, optAlloc (initOf v) i)
      (fun i => optAlloc (initOf v) i)
  have hmp_init : MeasurePreserving initOf (Measure.pi μ₁) (Measure.pi fun _ : Fin n => μ) := by
    have h1 := measurePreserving_piFinSuccAbove μ₁ (Fin.last n)
    have h2 : MeasurePreserving Prod.snd
        (μ.prod (Measure.pi fun j : Fin n => μ₁ ((Fin.last n).succAbove j)))
        (Measure.pi fun _ : Fin n => μ) := by
      simpa only [μ₁, Fin.succAbove_last] using
        (MeasureTheory.measurePreserving_snd (μ := μ)
          (ν := Measure.pi fun _ : Fin n => μ))
    have hcomp := h2.comp h1
    have hfn : Prod.snd ∘ MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n) =
        initOf := by
      funext v i
      simp [initOf, MeasurableEquiv.piFinSuccAbove, Fin.init]
    rwa [hfn] at hcomp
  have hm_init : Measurable initOf := hmp_init.measurable
  -- Expected virtual welfare of the first `n` coordinates equals the `n`-bidder optimal revenue.
  have hfirst_n : ∫ v, ∑ i : Fin n, virtualValue μ f (v (Fin.castSucc i)) * optAlloc (initOf v) i
      ∂Measure.pi μ₁ =
      ∫ v₀, ∑ i : Fin n, virtualValue μ f (v₀ i) * optAlloc v₀ i
        ∂Measure.pi (fun _ : Fin n => μ) := by
    let F : (Fin n → ℝ) → ℝ := fun v₀ => ∑ i : Fin n, virtualValue μ f (v₀ i) * optAlloc v₀ i
    change ∫ v, F (initOf v) ∂Measure.pi μ₁ = ∫ v₀, F v₀ ∂Measure.pi (fun _ : Fin n => μ)
    have hmF : Measurable F := Finset.measurable_sum Finset.univ fun i _ =>
      (hμ.measurable_virtualValue.comp (measurable_pi_apply i)).mul (hopt_meas i)
    conv_rhs => rw [← hmp_init.map_eq]
    exact (integral_map hm_init.aemeasurable
      (by rw [hmp_init.map_eq]; exact hmF.aestronglyMeasurable)).symm
  -- Integrability of the first `n` coordinates and the `Fin.last n` remainder under `bkAlloc`.
  let rem : (Fin (n + 1) → ℝ) → ℝ := fun v => 1 - ∑ i : Fin n, optAlloc (initOf v) i
  have hm_rem : Measurable rem := measurable_const.sub
    (Finset.measurable_sum Finset.univ fun i _ => (hopt_meas i).comp hm_init)
  have hrem_abs : ∀ v : Fin (n + 1) → ℝ, |rem v| ≤ 1 := by
    intro v
    have hfeas := Vickrey.reserveAllocation_mem_singleItemFeasible (virtualValue μ f) (initOf v)
    have hnn : 0 ≤ ∑ i : Fin n, optAlloc (initOf v) i :=
      Finset.sum_nonneg fun i _ => Vickrey.reserveAllocation_nonneg _ _ i
    have hle1 : ∑ i : Fin n, optAlloc (initOf v) i ≤ 1 := hfeas.2
    rw [abs_le]
    dsimp only [rem]
    exact ⟨by linarith, by linarith⟩
  have hint1 : Integrable
      (fun (v : Fin (n + 1) → ℝ) =>
        ∑ i : Fin n, virtualValue μ f (v (Fin.castSucc i)) * optAlloc (initOf v) i)
      (Measure.pi μ₁) := by
    refine integrable_finsetSum _ fun i _ => ?_
    have hB' : ∀ (v : Fin (n + 1) → ℝ), 0 ≤ v → |optAlloc (initOf v) i| ≤ 1 :=
      fun v hv => hopt_B (initOf v) (fun k => hv (Fin.castSucc k)) i
    exact integrable_virtualValue_mul (x := fun v _ => optAlloc (initOf v) i)
      (fun _ => hμ) (Fin.castSucc i) ((hopt_meas i).comp hm_init) hB'
  have hint_last : Integrable (fun v => virtualValue μ f (v (Fin.last n)) * rem v)
      (Measure.pi μ₁) := by
    have hφ_int : Integrable (fun (v : Fin (n + 1) → ℝ) => virtualValue μ f (v (Fin.last n)))
        (Measure.pi μ₁) := integrable_comp_eval hμ.integrable_virtualValue
    refine Integrable.mono' hφ_int.norm
      ((hμ.measurable_virtualValue.comp (measurable_pi_apply (Fin.last n))).mul
        hm_rem).aestronglyMeasurable
      (ae_of_all _ fun v => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hrem_abs v)
  have hsplit : ∀ v : Fin (n + 1) → ℝ,
      ∑ j : Fin (n + 1), virtualValue μ f (v j) * bkAlloc v j =
        (∑ i : Fin n, virtualValue μ f (v (Fin.castSucc i)) * optAlloc (initOf v) i) +
          virtualValue μ f (v (Fin.last n)) * rem v := by
    intro v
    rw [Fin.sum_univ_castSucc]
    simp only [bkAlloc, rem, Fin.lastCases_castSucc, Fin.lastCases_last]
  -- Expected virtual surplus of bidder `Fin.last n` under `bkAlloc` is `0`!
  have hlast_zero : ∫ v, virtualValue μ f (v (Fin.last n)) * rem v ∂Measure.pi μ₁ = 0 := by
    have hindep : ∀ (v : Fin (n + 1) → ℝ) (z : ℝ),
        (fun w => virtualValue μ f w * rem (Function.update v (Fin.last n) z)) =
          fun w => virtualValue μ f w * rem v := by
      intro v z
      funext w
      have hinit_upd : initOf (Function.update v (Fin.last n) z) = initOf v := by
        funext i
        dsimp only [initOf]
        exact Function.update_of_ne (Fin.castSucc_ne_last i) _ _
      simp only [rem, hinit_upd]
    rw [integral_apply_eval_eq_integral_integral μ₁
      (Φ := fun v w => virtualValue μ f w * rem v) hindep hint_last]
    dsimp only [μ₁]
    simp_rw [integral_mul_const, hμ.integral_virtualValue_eq_zero, zero_mul]
    exact integral_zero _ _
  -- Step 3: Compare `bkAlloc` pointwise a.e. with `(n + 1)`-bidder `Vickrey.allocation`.
  have hbk_eq : ∫ v, ∑ j : Fin (n + 1), virtualValue μ f (v j) * bkAlloc v j ∂Measure.pi μ₁ =
      ∫ v₀, ∑ i : Fin n, virtualValue μ f (v₀ i) * optAlloc v₀ i
        ∂Measure.pi (fun _ : Fin n => μ) := by
    simp_rw [hsplit]
    rw [integral_add hint1 hint_last, hfirst_n, hlast_zero, add_zero]
  have hae_pos : ∀ᵐ v ∂Measure.pi μ₁, ∀ j : Fin (n + 1), 0 < v j := by
    have hae0 : ∀ᵐ v ∂Measure.pi μ₁, ∀ j : Fin (n + 1), v j ≠ 0 := by
      rw [ae_all_iff]
      intro j
      have := hμ.nullSingletonClass
      have hz : ∀ᵐ z ∂μ₁ j, z ≠ 0 := by
        rw [ae_iff]
        simpa only [Classical.not_not, Set.ofPred_eq_eq_singleton] using measure_singleton (0 : ℝ)
      exact (Measure.quasiMeasurePreserving_eval μ₁ j).ae hz
    filter_upwards [ae_nonneg fun _ : Fin (n + 1) => hμ, hae0] with v hv0 hne j
    exact lt_of_le_of_ne (hv0 j) (Ne.symm (hne j))
  have hvick_B : ∀ (v : Fin (n + 1) → ℝ), 0 ≤ v →
      ∀ j, |(Vickrey.mechanism (ι := Fin (n + 1))).allocation v j| ≤ 1 := fun v _ j => by
    rcases Vickrey.allocation_binary v j with h0 | h1
    · simp [Vickrey.mechanism, h0]
    · simp [Vickrey.mechanism, h1]
  have hvick_rev : ∫ v, ∑ j : Fin (n + 1),
      (Vickrey.mechanism (ι := Fin (n + 1))).payment v j ∂Measure.pi μ₁ =
      ∫ v, ∑ j : Fin (n + 1), virtualValue μ f (v j) * Vickrey.allocation v j ∂Measure.pi μ₁ :=
    Vickrey.mechanism_isDSIC.integral_sum_payment_eq Vickrey.mechanism_isNormalized
      (fun _ => hμ) Vickrey.measurable_allocation hvick_B
  rw [hvick_rev]
  refine hM_le.trans ?_
  rw [← hbk_eq]
  -- Pointwise bound: on `0 < v`, `∑ φ(v j) * bkAlloc v j ≤ φ(v w) = ∑ φ(v j) * Vickrey.allocation`!
  have hint_bk_sum : Integrable
      (fun v => ∑ j : Fin (n + 1), virtualValue μ f (v j) * bkAlloc v j) (Measure.pi μ₁) :=
    (hint1.add hint_last).congr (ae_of_all _ fun v => (hsplit v).symm)
  have hint_vick_sum : Integrable
      (fun v => ∑ j : Fin (n + 1), virtualValue μ f (v j) * Vickrey.allocation v j)
      (Measure.pi μ₁) :=
    integrable_finsetSum _ fun j _ =>
      integrable_virtualValue_mul (fun _ => hμ) j (Vickrey.measurable_allocation j)
        fun v hv => hvick_B v hv j
  refine integral_mono_ae hint_bk_sum hint_vick_sum ?_
  filter_upwards [hae_pos] with v hvpos
  obtain ⟨w, hw⟩ := Vickrey.exists_wins v
  have hφle : ∀ j : Fin (n + 1), virtualValue μ f (v j) ≤ virtualValue μ f (v w) := by
    intro j
    rcases eq_or_ne j w with rfl | hjw
    · exact le_rfl
    · exact (hreg.strictMonoOn_Ioi hμ).monotoneOn (hvpos j) (hvpos w) (hw j hjw).1
  have hbk_nn : ∀ j : Fin (n + 1), 0 ≤ bkAlloc v j := by
    intro j
    refine j.lastCases ?_ (fun i => ?_)
    · simp only [bkAlloc, Fin.lastCases_last]
      have hfeas := Vickrey.reserveAllocation_mem_singleItemFeasible (virtualValue μ f) (initOf v)
      linarith [hfeas.2]
    · simp only [bkAlloc, Fin.lastCases_castSucc]
      exact Vickrey.reserveAllocation_nonneg _ _ i
  have hbk_sum1 : ∑ j : Fin (n + 1), bkAlloc v j = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [bkAlloc, Fin.lastCases_castSucc, Fin.lastCases_last]
    ring
  have hvick_sum : ∑ j : Fin (n + 1), virtualValue μ f (v j) * Vickrey.allocation v j =
      virtualValue μ f (v w) := by
    rw [Finset.sum_eq_single w
      (fun j _ hj => by
        rw [Vickrey.allocation_eq_zero_iff.mpr fun hjw => hj (hjw.unique hw), mul_zero])
      (fun hm => absurd (Finset.mem_univ w) hm),
      Vickrey.allocation_eq_one_iff.mpr hw, mul_one]
  rw [hvick_sum]
  calc ∑ j : Fin (n + 1), virtualValue μ f (v j) * bkAlloc v j
      ≤ ∑ j : Fin (n + 1), virtualValue μ f (v w) * bkAlloc v j :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hφle j) (hbk_nn j)
    _ = virtualValue μ f (v w) * ∑ j : Fin (n + 1), bkAlloc v j := by rw [Finset.mul_sum]
    _ = virtualValue μ f (v w) := by rw [hbk_sum1, mul_one]

end BulowKlemperer

end PostedPrice

end Cslib.GameTheory.SingleParameter
