/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.BulowKlemperer
public import CslibFrontier.Probability.OptimalStopping.ProphetSample
import CslibFrontier.Foundations.MeasureTheory.Integral.PiUpdate
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sequential posted-price mechanisms and prophet auctions

A *sequential posted-price mechanism* (SPM, or *order-oblivious posted-price mechanism* when the
arrival order is adversarial; [ChawlaHartlineMalecSivan2010], §1–§2.2, pp. 1–4;
[Roughgarden2013CS364A], Lecture 6, §2–§3) sells a single item by approaching bidders in the linear
order of `ι` and offering bidder `i` a take-it-or-leave-it price `p i ≥ 0`. The first bidder who
accepts wins the item and pays `p i`; all other bidders receive and pay nothing.

This module develops three main pillars connecting prophet inequalities and simple near-optimal
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

## References

* [S. Chawla, J. D. Hartline, D. L. Malec, B. Sivan, *Multi-parameter mechanism design and
  sequential posted pricing*][ChawlaHartlineMalecSivan2010]
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
  exact le_antisymm (not_lt.mp fun h => hi.2 j h hj.1) (not_lt.mp fun h => hj.2 i h hi.1)

theorem acceptAllocation_binary (accept : ι → ℝ → Prop) (b : ι → ℝ) (i : ι) :
    acceptAllocation accept b i = 0 ∨ acceptAllocation accept b i = 1 := by
  by_cases h : AcceptWins accept b i <;> simp [acceptAllocation, h]

theorem acceptAllocation_eq_one_iff {accept : ι → ℝ → Prop} {b : ι → ℝ} {i : ι} :
    acceptAllocation accept b i = 1 ↔ AcceptWins accept b i := by
  by_cases h : AcceptWins accept b i <;> simp [acceptAllocation, h]

theorem acceptAllocation_eq_zero_iff {accept : ι → ℝ → Prop} {b : ι → ℝ} {i : ι} :
    acceptAllocation accept b i = 0 ↔ ¬ AcceptWins accept b i := by
  by_cases h : AcceptWins accept b i <;> simp [acceptAllocation, h]

theorem acceptAllocation_nonneg (accept : ι → ℝ → Prop) (b : ι → ℝ) (i : ι) :
    0 ≤ acceptAllocation accept b i := by
  rcases acceptAllocation_binary accept b i with h | h <;> simp [h]

private theorem acceptAllocation_congr {α β : Type*} [LinearOrder α] [LinearOrder β]
    {a₁ : α → ℝ → Prop} {a₂ : β → ℝ → Prop} {b₁ : α → ℝ} {b₂ : β → ℝ} {i : α} {j : β}
    (h : AcceptWins a₁ b₁ i ↔ AcceptWins a₂ b₂ j) :
    acceptAllocation a₁ b₁ i = acceptAllocation a₂ b₂ j := by
  by_cases hw : AcceptWins a₁ b₁ i
  · rw [acceptAllocation_eq_one_iff.mpr hw, acceptAllocation_eq_one_iff.mpr (h.mp hw)]
  · rw [acceptAllocation_eq_zero_iff.mpr hw, acceptAllocation_eq_zero_iff.mpr (mt h.mpr hw)]

private theorem AcceptWins.sum_mul_acceptAllocation [Fintype ι] {accept : ι → ℝ → Prop}
    {b : ι → ℝ} {w : ι} (hw : AcceptWins accept b w) (g : ι → ℝ) :
    ∑ j, g j * acceptAllocation accept b j = g w := by
  rw [Finset.sum_eq_single w
    (fun j _ hj => by
      rw [acceptAllocation_eq_zero_iff.mpr fun hjw => hj (hjw.unique hw), mul_zero])
    (fun hm => absurd (Finset.mem_univ w) hm), acceptAllocation_eq_one_iff.mpr hw, mul_one]

private theorem exists_min_le [Finite ι] {P : ι → Prop} {j : ι} (hj : P j) :
    ∃ k ≤ j, P k ∧ ∀ m < k, ¬ P m := by
  classical
  have := Fintype.ofFinite ι
  let A := Finset.univ.filter P
  have hA : A.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  exact ⟨A.min' hA, Finset.min'_le A j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩),
    (Finset.mem_filter.mp (Finset.min'_mem A hA)).2, fun m hm hma =>
      not_le.mpr hm (Finset.min'_le A m (Finset.mem_filter.mpr ⟨Finset.mem_univ m, hma⟩))⟩

theorem acceptAllocation_mem_singleItemFeasible [Fintype ι] (accept : ι → ℝ → Prop) (b : ι → ℝ) :
    acceptAllocation accept b ∈ Vickrey.singleItemFeasible := by
  refine ⟨acceptAllocation_binary accept b, ?_⟩
  by_cases h : ∃ i, AcceptWins accept b i
  · obtain ⟨i, hi⟩ := h
    simpa only [Pi.one_apply, one_mul] using (hi.sum_mul_acceptAllocation 1).le
  · push Not at h
    simp only [fun j => acceptAllocation_eq_zero_iff.mpr (h j), Finset.sum_const_zero, zero_le_one]

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
  have hprev_iff : (∀ j < i, ¬ accept j (Function.update b i v j)) ↔ ∀ j < i, ¬ accept j (b j) :=
    forall_congr' fun j => imp_congr_right fun hj => by rw [Function.update_of_ne hj.ne]
  by_cases hprev : ∀ j < i, ¬ accept j (b j)
  · by_cases hav : accept i v
    · have hwin_v : AcceptWins accept (Function.update b i v) i :=
        ⟨(Function.update_self i v b).symm ▸ hav, hprev_iff.mpr hprev⟩
      rcases acceptAllocation_binary accept b i with hb | hb <;>
        rw [acceptAllocation_eq_one_iff.mpr hwin_v, hb]
      linarith [hle i v hv hav]
    · have hvp : v ≤ p i := not_lt.mp fun hgt => hav (hlt i v hgt)
      have hlose_v : ¬ AcceptWins accept (Function.update b i v) i :=
        fun hw => hav (Function.update_self i v b ▸ hw.1)
      rcases acceptAllocation_binary accept b i with hb | hb <;>
        rw [acceptAllocation_eq_zero_iff.mpr hlose_v, hb]
      linarith
  · rw [acceptAllocation_eq_zero_iff.mpr fun hw => hprev hw.2,
      acceptAllocation_eq_zero_iff.mpr fun hw => hprev (hprev_iff.mp hw.2)]

/-- A sequential posted-price mechanism whose acceptance predicate implies `p i ≤ z` on nonnegative
bids is individually rational. -/
theorem acceptMechanism_isIR {p : ι → ℝ} {accept : ι → ℝ → Prop}
    (hle : ∀ i z, 0 ≤ z → accept i z → p i ≤ z) :
    (acceptMechanism p accept).IsIR := by
  intro i b hb
  simp only [Mechanism.utility, acceptMechanism]
  rcases acceptAllocation_binary accept b i with h0 | h1
  · rw [h0]; linarith
  · rw [h1]; linarith [hle i (b i) (hb i) (acceptAllocation_eq_one_iff.mp h1).1]

/-- With nonnegative prices `0 ≤ p`, a bidder who bids `0` pays `0` (even if `p i = 0` and the
bidder wins, its price is `0`). -/
theorem acceptMechanism_isNormalized {p : ι → ℝ} {accept : ι → ℝ → Prop} (hp : 0 ≤ p)
    (hle : ∀ i z, 0 ≤ z → accept i z → p i ≤ z) :
    (acceptMechanism p accept).IsNormalized := by
  intro i b _
  simp only [acceptMechanism]
  rcases acceptAllocation_binary accept (Function.update b i 0) i with h0 | h1
  · rw [h0, mul_zero]
  · have h0' : accept i 0 := Function.update_self i 0 b ▸ (acceptAllocation_eq_one_iff.mp h1).1
    rw [le_antisymm (hle i 0 le_rfl h0') (hp i), zero_mul]

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
  by_cases hall : ∀ k, accept k (v k) ↔ accept k (b k)
  · obtain ⟨i, hiS⟩ := hS
    have halloc : acceptAllocation accept b i = acceptAllocation accept v i :=
      acceptAllocation_congr (by simp only [AcceptWins, hall])
    exact ⟨i, hiS, le_of_eq (by simp only [Mechanism.utility, acceptMechanism, halloc])⟩
  · obtain ⟨j₀, hj₀⟩ := Classical.not_forall.mp hall
    obtain ⟨k, _, hk_diff, hbefore⟩ :=
      exists_min_le (P := fun k => ¬ (accept k (v k) ↔ accept k (b k))) hj₀
    have hkS : k ∈ S := by_contra fun hnotS => hk_diff (hout k hnotS ▸ Iff.rfl)
    have halloc_eq : acceptAllocation accept b k =
        acceptAllocation accept (Function.update v k (b k)) k :=
      acceptAllocation_congr (by
        simp only [AcceptWins, Function.update_self]
        refine and_congr_right fun _ => forall_congr' fun j => imp_congr_right fun hj => ?_
        rw [Function.update_of_ne hj.ne, Classical.not_not.mp (hbefore j hj)])
    refine ⟨k, hkS, ?_⟩
    simpa only [Mechanism.utility, acceptMechanism, halloc_eq, Function.update_idem,
      Function.update_eq_self] using
      acceptMechanism_isDSIC hlt hle k (Function.update v k (b k)) (v k)
        (update_nonneg hv k (hb k)) (hv k)

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
  -- Consider the first bidder whose winning status changes between `v` and `b`.
  by_cases hall : ∀ k, AcceptWins accept v k ↔ AcceptWins accept b k
  · intro i
    simp only [Mechanism.utility, acceptMechanism, acceptAllocation_congr (hall i).symm]
  · exfalso
    obtain ⟨j₀, hj₀⟩ := Classical.not_forall.mp hall
    obtain ⟨k, _, hk_diff, hbefore⟩ :=
      exists_min_le (P := fun k => ¬ (AcceptWins accept v k ↔ AcceptWins accept b k)) hj₀
    -- Can any `j < k` accept under `v` or `b`? Its earliest accepting `r < k` would win under
    -- both `v` and `b` (since `r ∉ W`), making `k` lose under both, contradicting `hk_diff`.
    have hr_iff : ∀ r < k, AcceptWins accept v r ↔ AcceptWins accept b r :=
      fun r hr => Classical.not_not.mp (hbefore r hr)
    have hno_prev : ∀ (u : ι → ℝ),
        (∀ r < k, AcceptWins accept u r → AcceptWins accept v r ∧ AcceptWins accept b r) →
        ∀ j < k, ¬ accept j (u j) := by
      intro u hu j hj hacc
      obtain ⟨r, hrj, hr_win⟩ := exists_min_le (P := fun r => accept r (u r)) hacc
      have hr_both := hu r (hrj.trans_lt hj) hr_win
      exact hk_diff (iff_of_false (fun hw => hw.2 r (hrj.trans_lt hj) hr_both.1.1)
        (fun hw => hw.2 r (hrj.trans_lt hj) hr_both.2.1))
    have hno_prev_v : ∀ j < k, ¬ accept j (v j) :=
      hno_prev v fun r hr hw => ⟨hw, (hr_iff r hr).mp hw⟩
    have hno_prev_b : ∀ j < k, ¬ accept j (b j) :=
      hno_prev b fun r hr hw => ⟨(hr_iff r hr).mpr hw, hw⟩
    have hk_acc_diff : ¬ (accept k (v k) ↔ accept k (b k)) := fun hiff =>
      hk_diff ⟨fun h => ⟨hiff.mp h.1, hno_prev_b⟩, fun h => ⟨hiff.mpr h.1, hno_prev_v⟩⟩
    have hkS : k ∈ S := by_contra fun hnotS => hk_acc_diff (hout k hnotS ▸ Iff.rfl)
    have hle_u := hcoal k hkS
    simp only [Mechanism.utility, acceptMechanism] at hle_u
    refine hno_tie k hkS ?_
    by_cases hav : accept k (v k)
    · have hab : ¬ accept k (b k) := fun hb' => hk_acc_diff (iff_of_true hav hb')
      rw [acceptAllocation_eq_one_iff.mpr ⟨hav, hno_prev_v⟩,
        acceptAllocation_eq_zero_iff.mpr fun hw => hab hw.1] at hle_u
      linarith [hle k (v k) (hv k) hav]
    · have hab : accept k (b k) := Classical.not_not.mp fun hb' =>
        hk_acc_diff (iff_of_false hav hb')
      rw [acceptAllocation_eq_zero_iff.mpr fun hw => hav hw.1,
        acceptAllocation_eq_one_iff.mpr ⟨hab, hno_prev_b⟩] at hle_u
      linarith [not_lt.mp fun hgt => hav (hlt k (v k) hgt)]

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
    refine le_antisymm ((listMax_le_iff _ _).mpr fun y hy => ?_)
      ((listMax_le_iff _ _).mp le_rfl (v w) (List.mem_ofFn.mpr ⟨w, rfl⟩))
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hy
    rcases eq_or_ne j w with rfl | hj
    · exact le_rfl
    · exact_mod_cast (hw j hj).1
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
              acceptAllocation (fun k' z => accept k'.succ z) (fun j => (v j.succ : ℝ)) k :=
          fun k => acceptAllocation_congr <| by
            simp only [AcceptWins]
            refine and_congr_right fun _ =>
              ⟨fun h j hj => h j.succ (Fin.succ_lt_succ_iff.mpr hj), fun h j hj => ?_⟩
            cases j using Fin.cases with
            | zero => exact h0f
            | succ j' => exact h j' (Fin.succ_lt_succ_iff.mp hj)
        have hpay : ∀ (xs p₁ p₂ : List ℝ≥0),
            payoff (acceptRule a) reward p₁ xs = payoff (acceptRule a) reward p₂ xs := fun xs => by
          induction xs with
          | nil => exact fun _ _ => rfl
          | cons y ys ihy =>
              intro p₁ p₂
              simp only [payoff_cons, acceptRule, reward]
              congr 1
              exact ihy _ _
        simp only [acceptRule, Bool.eq_false_iff.mpr h0, Bool.false_eq_true, ↓reduceIte, hlose0,
          mul_zero, zero_add, hpay _ [v 0] [], ← ih (fun k' z => accept k'.succ z)
            (fun i z => hacc i.succ z) (fun j => v j.succ), hsucc]

/-- At a uniform posted price `t : ℝ≥0`, the expected social welfare of `postedPrice` equals
`expectedReward (thresholdRule t) (List.ofFn μ)`. -/
theorem expectedWelfare_postedPrice_const {n : ℕ} (t : ℝ≥0) (μ : Fin n → PMF ℝ≥0) :
    expectedWelfare (postedPrice (fun _ : Fin n => (t : ℝ))).allocation μ =
      expectedReward (thresholdRule t) (List.ofFn μ) := by
  rw [expectedWelfare, expectedReward, tsum_jointLaw_ofFn_mul]
  exact tsum_congr fun v => congrArg (piFin μ v * ·) <|
    payoff_acceptRule_ofFn (fun x => decide (t ≤ x)) (fun _ z => (t : ℝ) ≤ z)
      (fun _ z => by simp [NNReal.coe_le_coe]) v

/-- At a uniform posted price `t : ℝ≥0`, the expected social welfare of `strictPostedPrice` equals
`expectedReward (strictThresholdRule t) (List.ofFn μ)`. -/
theorem expectedWelfare_strictPostedPrice_const {n : ℕ} (t : ℝ≥0) (μ : Fin n → PMF ℝ≥0) :
    expectedWelfare (strictPostedPrice (fun _ : Fin n => (t : ℝ))).allocation μ =
      expectedReward (strictThresholdRule t) (List.ofFn μ) := by
  rw [expectedWelfare, expectedReward, tsum_jointLaw_ofFn_mul]
  exact tsum_congr fun v => congrArg (piFin μ v * ·) <|
    payoff_acceptRule_ofFn (fun x => decide (t < x)) (fun _ z => (t : ℝ) < z)
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
  simp_rw [expectedWelfare_vickrey_eq_expectedMax, expectedWelfare_postedPrice_const,
    expectedWelfare_strictPostedPrice_const]
  exact exists_expectedMax_le_two_mul_expectedReward (List.ofFn μ)

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
    (i : Fin n) {z : ℝ} (hz : sampleMaxPrice s < z) : singleSampleAccept s π i z :=
  ⟨(NNReal.coe_nonneg _).trans hz.le, fun j => Prod.Lex.toLex_lt_toLex.mpr <| Or.inl <|
    Real.lt_toNNReal_iff_coe_lt.mpr <|
      (NNReal.coe_le_coe.mpr ((Finset.le_fold_max _).mpr
        (Or.inr ⟨j, Finset.mem_univ j, le_rfl⟩))).trans_lt hz⟩

private theorem singleSampleAccept_le {n : ℕ} (s : Fin n → ℝ≥0) (π : Equiv.Perm (Fin (2 * n)))
    (i : Fin n) {z : ℝ} (hz : 0 ≤ z) (ha : singleSampleAccept s π i z) :
    sampleMaxPrice s ≤ z := by
  rw [← Real.coe_toNNReal z hz]
  exact NNReal.coe_le_coe.mpr <| (Finset.fold_max_le z.toNNReal).mpr
    ⟨zero_le, fun j _ => Prod.Lex.monotone_fst _ _ (ha.2 j).le⟩

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
  have hacc (i : Fin n) : singleSampleAccept s π i (v i : ℝ) ↔
      ∀ j : Fin n, sampleTag s π j < onlineTag (v i) π i := by simp [singleSampleAccept]
  set W := Finset.univ.filter fun i : Fin n => ∀ j : Fin n, sampleTag s π j < onlineTag (v i) π i
  by_cases hW : W.Nonempty
  · let w := W.min' hW
    have hwW : w ∈ W := Finset.min'_mem W hW
    have hwin : AcceptWins (singleSampleAccept s π) (fun j => (v j : ℝ)) w :=
      ⟨(hacc w).mpr (Finset.mem_filter.mp hwW).2, fun j hj hja => not_le.mpr hj
        (Finset.min'_le W j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hacc j).mp hja⟩))⟩
    dsimp only [singleSamplePostedPrice, acceptMechanism]
    rw [hwin.sum_mul_acceptAllocation fun i => (v i : ℝ)]
    simp [firstBeatReward, W, hW, w, ENNReal.ofReal_coe_nnreal]
  · have hlose (i : Fin n) :
        (singleSamplePostedPrice s π).allocation (fun j => (v j : ℝ)) i = 0 :=
      acceptAllocation_eq_zero_iff.mpr fun hw =>
        hW ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hacc i).mp hw.1⟩⟩
    simp [firstBeatReward, W, hW, hlose]

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
  simp_rw [expectedWelfare_vickrey_eq_expectedMax, expectedWelfare_singleSamplePostedPrice,
    ← singleSampleExpectedReward_eq]
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
  refine le_trans ?_ (expectedReward_tightLaws_le k stop)
  rw [expectedWelfare, expectedReward, ← list_ofFn_tightBidderLaws k, tsum_jointLaw_ofFn_mul]
  refine tsum_le_tsum fun v => mul_le_mul_right ?_ _
  rw [Fin.sum_univ_two, List.ofFn_succ, List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one,
    payoff_cons]
  by_cases hp0 : p 0 ≤ (v 0 : ℝ)
  · have hw0 : AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 0 :=
      ⟨hp0, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
    have hl1 : ¬ AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 1 :=
      fun hw => hw.2 0 Fin.zero_lt_one hp0
    simp only [stop, postedPrice, acceptMechanism, acceptAllocation_eq_one_iff.mpr hw0,
      acceptAllocation_eq_zero_iff.mpr hl1, mul_one, mul_zero, add_zero, decide_eq_true hp0,
      ↓reduceIte, reward, ENNReal.ofReal_coe_nnreal, le_rfl]
  · have hl0 : ¬ AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 0 := fun hw => hp0 hw.1
    simp only [stop, decide_eq_false hp0, Bool.false_eq_true, ↓reduceIte, payoff_cons]
    by_cases hp1 : p 1 ≤ (v 1 : ℝ)
    · have hw1 : AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 1 :=
        ⟨hp1, fun j hj => (Fin.ext (Nat.lt_one_iff.mp hj) : j = 0) ▸ hp0⟩
      simp only [decide_eq_true hp1, ↓reduceIte, postedPrice, acceptMechanism,
        acceptAllocation_eq_zero_iff.mpr hl0, acceptAllocation_eq_one_iff.mpr hw1, mul_zero,
        mul_one, zero_add, reward, ENNReal.ofReal_coe_nnreal, le_rfl]
    · have hl1 : ¬ AcceptWins (fun i z => p i ≤ z) (fun j => (v j : ℝ)) 1 := fun hw => hp1 hw.1
      simp [decide_eq_false hp1, payoff_nil, postedPrice, acceptMechanism,
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
    have hmat : (![v 0, v 1] : Fin 2 → ℝ≥0) = v := funext fun j => by fin_cases j <;> rfl
    simp only [List.ofFn_succ, List.ofFn_zero, Fin.succ_zero_eq_one, pay2, hmat]
  rw [hrew, tsum_jointLaw_cons_mul, tsum_longShot_mul]
  simp only [tsum_jointLaw_cons_mul, tsum_pure_mul, tsum_jointLaw_nil_mul]
  dsimp only [pay2]
  have hvec (x : ℝ≥0) : (fun j : Fin 2 => (![x, 1] j : ℝ)) = ![(x : ℝ), 1] :=
    funext fun j => by fin_cases j <;> simp
  rw [Fin.sum_univ_two, Fin.sum_univ_two, hvec, hvec]
  simp only [NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one, NNReal.coe_zero]
  have hw0 : AcceptWins (fun i z => ![(k + 1 : ℝ), 1] i ≤ z) ![(k + 1 : ℝ), 1] 0 :=
    ⟨by simp, fun j hj => absurd hj (Fin.not_lt_zero j)⟩
  have hl1 : ¬ AcceptWins (fun i z => ![(k + 1 : ℝ), 1] i ≤ z) ![(k + 1 : ℝ), 1] 1 :=
    fun hw => hw.2 0 Fin.zero_lt_one (by simp)
  have hlt0 : ¬ ![(k + 1 : ℝ), 1] 0 ≤ ![(0 : ℝ), 1] 0 := by
    simp only [Matrix.cons_val_zero, not_le]; positivity
  have hl0 : ¬ AcceptWins (fun i z => ![(k + 1 : ℝ), 1] i ≤ z) ![(0 : ℝ), 1] 0 :=
    fun hw => hlt0 hw.1
  have hw1 : AcceptWins (fun i z => ![(k + 1 : ℝ), 1] i ≤ z) ![(0 : ℝ), 1] 1 :=
    ⟨by simp, fun j hj => (Fin.ext (Nat.lt_one_iff.mp hj) : j = 0) ▸ hlt0⟩
  simp only [postedPrice, acceptMechanism, acceptAllocation_eq_one_iff.mpr hw0,
    acceptAllocation_eq_zero_iff.mpr hl1, acceptAllocation_eq_zero_iff.mpr hl0,
    acceptAllocation_eq_one_iff.mpr hw1, Matrix.cons_val_zero, Matrix.cons_val_one,
    mul_one, mul_zero, add_zero, zero_add, ENNReal.ofReal_one,
    ENNReal.ofReal_add (Nat.cast_nonneg k) zero_le_one, ENNReal.ofReal_natCast]
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
    rw [expectedMax_tightLaws, expectedReward, tightLaws_eq, tsum_jointLaw_cons_mul,
      tsum_pure_mul] at hstop
    simpa [payoff_cons, reward] using hstop
  have hwel : expectedWelfare (postedPrice p).allocation (tightBidderLaws k) <
      c * ((2 * k + 1) / (k + 1)) :=
    (expectedWelfare_postedPrice_tightBidderLaws_le_one k p).trans_lt hgap
  have hrev : expectedRevenuePMF (postedPrice p) (tightBidderLaws k) <
      c * ((2 * k + 1) / (k + 1)) :=
    (expectedRevenuePMF_le_expectedWelfare (postedPrice_isIR p) _).trans_lt hwel
  rw [expectedRevenuePMF_swapped_tightBidderLaws, expectedWelfare_vickrey_eq_expectedMax,
    list_ofFn_tightBidderLaws, expectedMax_tightLaws]
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
      simp only [Finset.fold_insert ha]
      exact (hg a (Finset.mem_insert_self a s)).sup
        (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

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
  have hfeas_abs : ∀ {y : ι → ℝ}, y ∈ Vickrey.singleItemFeasible → ∀ i, |y i| ≤ 1 :=
    fun hy i => by rcases hy.1 i with h | h <;> simp [h]
  -- Step 1: Bound `Rev(M)` by `E_opt := ∫ v, posVirtualSurplus μ f v ∂Measure.pi μ`.
  have hMB : ∀ v, 0 ≤ v → ∀ i, |M.allocation v i| ≤ 1 := fun v hv => hfeas_abs (hMX v hv)
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
  have hpB : ∀ v, 0 ≤ v → ∀ i, |(postedPrice p).allocation v i| ≤ 1 :=
    fun v _ => hfeas_abs (postedPrice_mem_singleItemFeasible p v)
  have hrev_eq : ∫ v, ∑ i, (postedPrice p).payment v i ∂Measure.pi μ =
      ∫ v, ∑ i, virtualValue (μ i) (f i) (v i) * (postedPrice p).allocation v i ∂Measure.pi μ :=
    (postedPrice_isDSIC p).integral_sum_payment_eq
      (postedPrice_isNormalized (virtualPostedPrices_nonneg hμ hreg)) hμ
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
    dsimp only [priorReject, allReject]
    split_ifs with hprev
    · linarith [(Finset.sum_nonneg fun k _ => acceptAllocation_nonneg _ v k :
        0 ≤ ∑ k, (postedPrice p).allocation v k)]
    · push Not at hprev
      obtain ⟨j, _, hpj⟩ := hprev
      -- Since `p j ≤ v j`, the smallest `w` with `p w ≤ v w` wins, so `∑ k, alloc v k = 1`!
      obtain ⟨w, _, hwin⟩ := exists_min_le (P := fun k => p k ≤ v k) hpj
      have h1 := AcceptWins.sum_mul_acceptAllocation (accept := fun k z => p k ≤ z) hwin 1
      simp only [Pi.one_apply, one_mul] at h1
      change 1 - ∑ k, acceptAllocation (fun k z => p k ≤ z) v k ≤ 0
      linarith
  have hall_nonneg : ∀ v : ι → ℝ, 0 ≤ allReject v := fun v => by
    dsimp only [allReject]; linarith [(postedPrice_mem_singleItemFeasible p v).2]
  -- Almost-everywhere positivity and non-tie condition (`NullSingletonClass`).
  have hae_ne : ∀ (i : ι) (c : ℝ), ∀ᵐ v ∂Measure.pi μ, v i ≠ c := fun i c => by
    have := (hμ i).nullSingletonClass
    have hz : ∀ᵐ z ∂(μ i), z ≠ c := by
      rw [ae_iff]
      simpa only [Classical.not_not, Set.ofPred_eq_eq_singleton] using measure_singleton c
    exact (Measure.quasiMeasurePreserving_eval μ i).ae hz
  have hae_pos_ne : ∀ᵐ v ∂Measure.pi μ, ∀ i, 0 < v i ∧ v i ≠ p i := by
    filter_upwards [ae_nonneg hμ, ae_all_iff.mpr fun i => hae_ne i 0,
      ae_all_iff.mpr fun i => hae_ne i (p i)] with v hv0 hne0 hnep i
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
    have hthr : IsReserveThreshold (fun z => virtualValue (μ i) (f i) z - t) (p i) :=
      isReserveThreshold_virtualPostedPrices hμ hreg i
    dsimp only [postedPrice, acceptMechanism, priorReject, excess]
    split_ifs with hprev
    · by_cases hpi : p i ≤ v i
      · rw [acceptAllocation_eq_one_iff.mpr ⟨hpi, fun j hj => not_le.mpr (hprev j hj)⟩,
          max_eq_left (hthr.2.1 (v i) (lt_of_le_of_ne hpi (Ne.symm (hv i).2)))]
        ring
      · rw [acceptAllocation_eq_zero_iff.mpr fun hw => hpi hw.1,
          max_eq_right (le_of_not_gt fun hgt => hpi (hthr.2.2 (v i) (hv i).1 hgt.le))]
        ring
    · rw [acceptAllocation_eq_zero_iff.mpr fun hw => hprev fun j hj => not_le.mp (hw.2 j hj)]
      ring
  -- Measurability & integrability of `priorReject`, `allReject`, and `excess`.
  have hm_prior : ∀ i, Measurable (priorReject i) := fun i =>
    Measurable.ite
      (Measurable.forall fun j => Measurable.imp measurable_const
        (measurableSet_lt (measurable_pi_apply j) measurable_const).mem).setOf
      measurable_const measurable_const
  have hint_prior : ∀ i, Integrable (priorReject i) (Measure.pi μ) := fun i =>
    Integrable.of_bound (hm_prior i).aestronglyMeasurable 1 (ae_of_all _ fun v => by
      dsimp only [priorReject]
      split_ifs <;> norm_num)
  have hint_alloc_sum : Integrable (fun v => ∑ i, (postedPrice p).allocation v i)
      (Measure.pi μ) :=
    integrable_finsetSum _ fun i _ =>
      Integrable.of_bound (measurable_postedPrice_allocation p i).aestronglyMeasurable 1
        (ae_of_all _ fun v => by
          simpa only [Real.norm_eq_abs] using hfeas_abs (postedPrice_mem_singleItemFeasible p v) i)
  have hint_allReject : Integrable allReject (Measure.pi μ) :=
    (integrable_const 1).sub hint_alloc_sum
  have hint_one_sub : Integrable (fun v => 1 - allReject v) (Measure.pi μ) :=
    (integrable_const 1).sub hint_allReject
  have hm_excess : ∀ i, Measurable (excess i) := fun i =>
    (((hμ i).measurable_virtualValue).sub measurable_const).max measurable_const
  have hint_excess_pi : ∀ i, Integrable (fun v : ι → ℝ => excess i (v i)) (Measure.pi μ) :=
    fun i => integrable_comp_eval
      ((((hμ i).integrable_virtualValue).sub (integrable_const t)).sup (integrable_zero _ _ _))
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
    have hindep (v : ι → ℝ) (z : ℝ) :
        (fun w => priorReject i (Function.update v i z) * excess i w) =
          fun w => priorReject i v * excess i w := by
      have hiff : (∀ j < i, Function.update v i z j < p j) ↔ ∀ j < i, v j < p j :=
        forall_congr' fun j => imp_congr_right fun hj => by rw [Function.update_of_ne hj.ne]
      simp only [priorReject, hiff]
    rw [integral_apply_eval_eq_integral_integral μ (Φ := fun v z => priorReject i v * excess i z)
      hindep (hint_prod i)]
    simp only [integral_const_mul, integral_mul_const]
  -- Prophet upper bound on `E_opt`: `posVirtualSurplus v ≤ t + ∑ i, excess i (v i)`.
  have hprophet_pt : ∀ v : ι → ℝ, posVirtualSurplus μ f v ≤ t + ∑ i, excess i (v i) := fun v => by
    refine (Finset.fold_max_le _).mpr
      ⟨add_nonneg ht0 (Finset.sum_nonneg fun _ _ => le_max_right _ _), fun i _ => ?_⟩
    have hle_sum : excess i (v i) ≤ ∑ j, excess j (v j) :=
      Finset.single_le_sum (f := fun j => excess j (v j)) (fun _ _ => le_max_right _ _)
        (Finset.mem_univ i)
    linarith [le_max_left (virtualValue (μ i) (f i) (v i) - t) 0]
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
    exact congrArg (t * (1 - R) + ·) (Finset.sum_congr rfl fun i _ => hfactor i)
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

end PostedPrice

end Cslib.GameTheory.SingleParameter
