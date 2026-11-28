/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.Vickrey
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Multi-unit auctions: `(k + 1)`-st price vs discriminatory `(j + 1)`-st price

In a single-minded multi-unit auction ([Nisan2007], §9.3.5.4, p. 221; [Vickrey1961]), `k`
identical items are sold to bidders `i : ι`, each wanting at most one item (`xᵢ ∈ {0, 1}` with
`∑ᵢ xᵢ ≤ k`, `multiUnitFeasible k`).

Ordering bidders by bid with ties broken in favour of smaller indices (`Beats`, `rank`), the
top-`k` allocation rule (`allocation k`) awards one item to each bidder with 0-indexed
`rank b i < k`. On nonnegative bids:

1. **Welfare maximization and uniform `(k + 1)`-st price truthfulness** ([Nisan2007], §9.3.5.4,
   p. 221): `allocation k` maximizes reported welfare `∑ᵢ bᵢ xᵢ` over `multiUnitFeasible k`
   (`isWelfareMaximizing_allocation`), and charging every winner the uniform `(k + 1)`-st highest
   bid (`bidAtRank k b`, which is `0` when `Fintype.card ι ≤ k`) agrees on nonnegative profiles
   with both `criticalBidMechanism (allocation k)` and `myerson (allocation k)`
   (`criticalBidMechanism_eq_on_nonneg`, `mechanism_payment_eq_myersonPayment`). Consequently
   `MultiUnit.mechanism k` is DSIC, individually rational, and normalized (`mechanism_isDSIC`,
   `mechanism_isIR`, `mechanism_isNormalized`), generalizing `Vickrey.mechanism` (`k = 1`).
2. **Failure of DSIC for discriminatory `(j + 1)`-st price auctions** (original contrast, not in
   [Nisan2007]): contrasting with the uniform `(k + 1)`-st price rule, charging the `j`-th highest
   bidder (`1 ≤ j ≤ k`, 0-indexed `rank = j - 1`) the `(j + 1)`-st highest bid
   (`nextBidMechanism k`) is **not** DSIC whenever `2 ≤ k` and `2 ≤ Fintype.card ι`
   (`not_isDSIC_nextBidMechanism`): when bidder `i₀` has value `3`, bidder `i₁` bids `2`, and any
   remaining bidders bid `0`, truthful bidding `3` gives `i₀` rank `0` at price `2` (utility `1`),
   whereas shading to `1` drops `i₀` to rank `1 < k` (still winning!) at price `0` (utility
   `3 > 1`). Both bounds `2 ≤ k` and `2 ≤ Fintype.card ι` are tight
   (`nextBidMechanism_one_eq_mechanism`, `nextBidMechanism_isDSIC_of_card_le_one`).

**Source locator note.** The unit-demand `(k + 1)`-st price multi-unit auction appears directly in
[Nisan2007], §9.3.5.4 (p. 221). Note that Chapter 1, Exercise 1.2 of the edited volume (Nisan et
al., 2007, p. 26) instead concerns pure Nash equilibria in random two-player matrix games; the
contrasting `nextBidMechanism` counterexample is original and not taken from that exercise.

## Main definitions

* `SingleParameter.MultiUnit.multiUnitFeasible`:
  `{x : ι → ℝ | (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i ≤ k}`.
* `SingleParameter.MultiUnit.Beats`, `SingleParameter.MultiUnit.rank`: tie-broken strict comparison
  and 0-indexed rank from the top.
* `SingleParameter.MultiUnit.Wins`, `SingleParameter.MultiUnit.allocation`: top-`k` winning
  predicate and 0-1 allocation rule.
* `SingleParameter.MultiUnit.bidAtRank`: the `(r + 1)`-st highest bid (clamped at `0`, and `0` when
  `Fintype.card ι ≤ r`).
* `SingleParameter.MultiUnit.mechanism`: uniform `(k + 1)`-st price `k`-unit auction.
* `SingleParameter.MultiUnit.nextBidMechanism`: discriminatory auction charging the `j`-th highest
  bidder (`1 ≤ j ≤ k`) the `(j + 1)`-st highest bid (original).

## Main results

* `SingleParameter.MultiUnit.isWelfareMaximizing_allocation`: `allocation k` maximizes reported
  welfare over `multiUnitFeasible k`.
* `SingleParameter.MultiUnit.criticalBid_allocation_of_wins`,
  `SingleParameter.MultiUnit.criticalBidMechanism_eq_on_nonneg`,
  `SingleParameter.MultiUnit.mechanism_payment_eq_myersonPayment`: `MultiUnit.mechanism k` agrees
  with `criticalBidMechanism` and `myerson` on nonnegative bids.
* `SingleParameter.MultiUnit.mechanism_isDSIC`, `SingleParameter.MultiUnit.mechanism_isIR`,
  `SingleParameter.MultiUnit.mechanism_isNormalized`: the `(k + 1)`-st price auction is DSIC, IR,
  and normalized.
* `SingleParameter.MultiUnit.mechanism_one_eq_vickrey`: for `k = 1`, `MultiUnit.mechanism 1` agrees
  with `Vickrey.mechanism` on nonnegative bids.
* `SingleParameter.MultiUnit.not_isDSIC_nextBidMechanism`: for `2 ≤ k` and `2 ≤ Fintype.card ι`,
  `nextBidMechanism k` is not DSIC (original).
* `SingleParameter.MultiUnit.nextBidMechanism_one_eq_mechanism`,
  `SingleParameter.MultiUnit.nextBidMechanism_isDSIC_of_card_le_one`: tightness of `2 ≤ k` and
  `2 ≤ Fintype.card ι` (original).

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
* [W. Vickrey, *Counterspeculation, auctions, and competitive sealed tenders*][Vickrey1961]
-/

public section

namespace Cslib.GameTheory.SingleParameter.MultiUnit

variable {ι : Type*}

/-- Feasible allocations of `k` identical items to unit-demand bidders: 0-1 vectors summing to at
most `k` ([Nisan2007], §9.3.5.4). -/
def multiUnitFeasible [Fintype ι] (k : ℕ) : Set (ι → ℝ) :=
  {x | (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i ≤ k}

theorem mem_multiUnitFeasible [Fintype ι] {k : ℕ} {x : ι → ℝ} :
    x ∈ multiUnitFeasible k ↔ (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, x i ≤ k :=
  Iff.rfl

section Order

variable [LinearOrder ι]

/-- Bidder `j` strictly beats bidder `i` on bid profile `b`: either `b i < b j`, or `b i = b j` and
`j < i` (ties broken in favour of smaller indices, matching `Vickrey.Wins`). -/
@[expose] def Beats (b : ι → ℝ) (j i : ι) : Prop :=
  b i < b j ∨ (b i = b j ∧ j < i)

theorem beats_irrefl (b : ι → ℝ) (i : ι) : ¬ Beats b i i := by
  rintro (h | ⟨-, h⟩) <;> exact lt_irrefl _ h

theorem beats_trans {b : ι → ℝ} {x y z : ι} (hxy : Beats b x y) (hyz : Beats b y z) :
    Beats b x z := by
  rcases hxy with h1 | ⟨he1, hl1⟩ <;> rcases hyz with h2 | ⟨he2, hl2⟩
  · exact Or.inl (h2.trans h1)
  · exact Or.inl (he2 ▸ h1)
  · exact Or.inl (he1.symm ▸ h2)
  · exact Or.inr ⟨he2.trans he1, hl1.trans hl2⟩

theorem beats_trichotomous {b : ι → ℝ} {i j : ι} (hij : i ≠ j) :
    Beats b i j ∨ Beats b j i := by
  rcases lt_trichotomy (b i) (b j) with hlt | heq | hgt
  · exact Or.inr (Or.inl hlt)
  · rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (Or.inr ⟨heq.symm, h⟩)
    · exact Or.inr (Or.inr ⟨heq, h⟩)
  · exact Or.inl (Or.inl hgt)

theorem le_of_beats {b : ι → ℝ} {j i : ι} (h : Beats b j i) : b i ≤ b j := by
  exact h.elim le_of_lt fun h => h.1.le

theorem le_of_not_beats {b : ι → ℝ} {j i : ι} (h : ¬ Beats b j i) : b j ≤ b i := by
  exact not_lt.1 fun hlt => h (Or.inl hlt)

variable [Fintype ι]

open Classical in
/-- The 0-indexed rank of bidder `i` from the top on bid profile `b`: the number of bidders `j`
with `Beats b j i`. -/
noncomputable def rank (b : ι → ℝ) (i : ι) : ℕ :=
  (Finset.univ.filter fun j => Beats b j i).card

open Classical in
theorem rank_def (b : ι → ℝ) (i : ι) :
    rank b i = (Finset.univ.filter fun j => Beats b j i).card := by
  rfl

open Classical in
theorem rank_lt_card (b : ι → ℝ) (i : ι) : rank b i < Fintype.card ι := by
  rw [rank, ← Finset.card_univ]
  exact Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, Finset.mem_univ i, beats_irrefl b i⟩)

open Classical in
theorem rank_lt_of_beats {b : ι → ℝ} {i j : ι} (h : Beats b i j) : rank b i < rank b j := by
  refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun m hm => ?_).2
    ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩,
      fun hi => beats_irrefl b i (Finset.mem_filter.1 hi).2⟩)
  exact Finset.mem_filter.2 ⟨Finset.mem_univ m, beats_trans (Finset.mem_filter.1 hm).2 h⟩

theorem beats_iff_rank_lt {b : ι → ℝ} {i j : ι} : Beats b i j ↔ rank b i < rank b j := by
  refine ⟨rank_lt_of_beats, fun hlt => ?_⟩
  have hij : i ≠ j := fun h => by subst h; exact lt_irrefl _ hlt
  rcases beats_trichotomous hij with h | h
  · exact h
  · exact absurd (rank_lt_of_beats h) (not_lt.2 hlt.le)

theorem rank_injective (b : ι → ℝ) : Function.Injective (rank b) := fun _ _ heq =>
  by_contra fun hij => (beats_trichotomous hij).elim
    (fun h => (heq ▸ rank_lt_of_beats h).false)
    (fun h => (heq ▸ rank_lt_of_beats h).false)

theorem image_rank_eq_range (b : ι → ℝ) :
    Finset.univ.image (rank b) = Finset.range (Fintype.card ι) := by
  refine Finset.eq_of_subset_of_card_le (fun r hr => ?_) ?_
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hr
    exact Finset.mem_range.2 (rank_lt_card b i)
  · rw [Finset.card_range, Finset.card_image_of_injective _ (rank_injective b), Finset.card_univ]

theorem exists_rank_eq {b : ι → ℝ} {r : ℕ} (hr : r < Fintype.card ι) : ∃ i, rank b i = r := by
  simpa only [Finset.mem_image, Finset.mem_univ, true_and] using
    ((image_rank_eq_range b).symm ▸ Finset.mem_range.2 hr : r ∈ Finset.univ.image (rank b))

/-- Bidder `i` wins one of the `k` identical items iff `rank b i < k`. -/
@[expose] def Wins (k : ℕ) (b : ι → ℝ) (i : ι) : Prop :=
  rank b i < k

theorem wins_one_iff {b : ι → ℝ} {i : ι} : Wins 1 b i ↔ Vickrey.Wins b i := by
  classical
  rw [Wins, Nat.lt_one_iff, rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  refine ⟨fun h j _ => ⟨le_of_not_beats (h (Finset.mem_univ j)), fun hlt =>
    (le_of_not_beats (h (Finset.mem_univ j))).lt_of_ne fun heq =>
      h (Finset.mem_univ j) (Or.inr ⟨heq.symm, hlt⟩)⟩, ?_⟩
  rintro h j - (hlt | ⟨heq, hji⟩)
  · exact not_lt.2 (h j (fun he => lt_irrefl _ (he ▸ hlt))).1 hlt
  · exact ((h j hji.ne).2 hji).ne heq.symm

open Classical in
/-- Top-`k` allocation rule: each of the `k` highest-ranked bidders receives `1` item, and all
other bidders receive `0`. -/
noncomputable def allocation (k : ℕ) (b : ι → ℝ) (i : ι) : ℝ :=
  if Wins k b i then 1 else 0

theorem allocation_one : allocation (ι := ι) 1 = Vickrey.allocation := by
  classical
  ext b i
  simp only [allocation, Vickrey.allocation, wins_one_iff]

theorem allocation_eq_one_iff {k : ℕ} {b : ι → ℝ} {i : ι} :
    allocation k b i = 1 ↔ Wins k b i := by
  simp [allocation]

theorem allocation_eq_zero_iff {k : ℕ} {b : ι → ℝ} {i : ι} :
    allocation k b i = 0 ↔ ¬ Wins k b i := by
  simp [allocation]

theorem allocation_binary (k : ℕ) (b : ι → ℝ) (i : ι) :
    allocation k b i = 0 ∨ allocation k b i = 1 := by
  by_cases h : Wins k b i <;> simp [allocation, h]

theorem isBinary_allocation (k : ℕ) : IsBinary (allocation (ι := ι) k) :=
  fun b _ i => allocation_binary k b i

open Classical in
theorem card_wins (k : ℕ) (b : ι → ℝ) :
    (Finset.univ.filter fun i => Wins k b i).card = min k (Fintype.card ι) := by
  have hinj : Set.InjOn (rank b) ↑(Finset.univ.filter fun i => Wins k b i) :=
    (rank_injective b).injOn
  rw [← Finset.card_image_of_injOn hinj]
  have himg : (Finset.univ.filter fun i => Wins k b i).image (rank b) =
      Finset.range (min k (Fintype.card ι)) := by
    ext r
    rw [Finset.mem_image, Finset.mem_range, lt_min_iff]
    refine ⟨fun ⟨i, hi, hr⟩ => ⟨hr ▸ (Finset.mem_filter.1 hi).2, hr ▸ rank_lt_card b i⟩,
      fun ⟨hrk, hrn⟩ => ?_⟩
    obtain ⟨i, hi⟩ := exists_rank_eq (b := b) hrn
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi.trans_lt hrk⟩, hi⟩
  rw [himg, Finset.card_range]

open Classical in
theorem sum_allocation (k : ℕ) (b : ι → ℝ) :
    ∑ i, allocation k b i = (min k (Fintype.card ι) : ℕ) := by
  simp only [allocation, Finset.sum_boole, card_wins]

theorem allocation_mem_multiUnitFeasible (k : ℕ) (b : ι → ℝ) :
    allocation k b ∈ multiUnitFeasible k := by
  refine mem_multiUnitFeasible.2 ⟨allocation_binary k b, ?_⟩
  rw [sum_allocation]
  exact_mod_cast min_le_left k (Fintype.card ι)

/-- **Top-`k` allocation maximizes welfare** ([Nisan2007], §9.3.5.4): on nonnegative bids,
`allocation k` maximizes `∑ᵢ bᵢ yᵢ` over `multiUnitFeasible k`. -/
theorem isWelfareMaximizing_allocation (k : ℕ) :
    IsWelfareMaximizing (multiUnitFeasible (ι := ι) k) (allocation k) := by
  intro b hb
  refine ⟨allocation_mem_multiUnitFeasible k b, fun y hy => ?_⟩
  rw [mem_multiUnitFeasible] at hy
  have hy01 : ∀ i, 0 ≤ y i ∧ y i ≤ 1 := fun i => by
    rcases hy.1 i with h | h <;> rw [h] <;> exact ⟨by norm_num, by norm_num⟩
  rcases le_or_gt (Fintype.card ι) k with hnk | hkn
  · refine Finset.sum_le_sum fun i _ => ?_
    rw [allocation_eq_one_iff.2 ((rank_lt_card b i).trans_le hnk)]
    exact mul_le_mul_of_nonneg_left (hy01 i).2 (hb i)
  · obtain ⟨ik, hik⟩ := exists_rank_eq (b := b) hkn
    set p := b ik
    have hp0 : 0 ≤ p := hb ik
    have hpt : ∀ i, (b i - p) * y i ≤ (b i - p) * allocation k b i := by
      intro i
      by_cases hw : Wins k b i
      · have hbeat : Beats b i ik := beats_iff_rank_lt.2 (hik ▸ hw)
        have hbp : 0 ≤ b i - p := sub_nonneg.2 (le_of_beats hbeat)
        rw [allocation_eq_one_iff.2 hw]
        exact mul_le_mul_of_nonneg_left (hy01 i).2 hbp
      · have hle : b i ≤ p :=
          le_of_not_beats fun h => hw (by rw [Wins, ← hik]; exact beats_iff_rank_lt.1 h)
        rw [allocation_eq_zero_iff.2 hw, mul_zero]
        exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hle) (hy01 i).1
    have hsum_shift : ∑ i, (b i - p) * y i ≤ ∑ i, (b i - p) * allocation k b i :=
      Finset.sum_le_sum fun i _ => hpt i
    have hexp : ∀ z : ι → ℝ, ∑ i, (b i - p) * z i = (∑ i, b i * z i) - p * ∑ i, z i := fun z => by
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hexp, hexp, sum_allocation, min_eq_left hkn.le] at hsum_shift
    linarith [mul_le_mul_of_nonneg_left hy.2 hp0]

/-- `allocation k` is monotone on nonnegative bids. -/
theorem isMonotone_allocation (k : ℕ) : IsMonotone (allocation (ι := ι) k) :=
  (isWelfareMaximizing_allocation k).isMonotone

/-! ### Uniform `(k + 1)`-st price auction -/

open Classical in
/-- The `(r + 1)`-st highest bid (`0`-indexed rank `r`), clamped below at `0`, or `0` when
`Fintype.card ι ≤ r`. -/
noncomputable def bidAtRank (r : ℕ) (b : ι → ℝ) : ℝ :=
  if h : ∃ i, rank b i = r then max 0 (b (Classical.choose h)) else 0

theorem bidAtRank_eq_of_rank {r : ℕ} {b : ι → ℝ} {i : ι} (hi : rank b i = r) :
    bidAtRank r b = max 0 (b i) := by
  have hex : ∃ j, rank b j = r := ⟨i, hi⟩
  unfold bidAtRank
  rw [dite_eq_left hex, rank_injective b ((Classical.choose_spec hex).trans hi.symm)]

theorem bidAtRank_eq_of_rank_nonneg {r : ℕ} {b : ι → ℝ} (hb : 0 ≤ b) {i : ι}
    (hi : rank b i = r) : bidAtRank r b = b i :=
  (bidAtRank_eq_of_rank hi).trans (max_eq_right (hb i))

theorem bidAtRank_of_card_le {r : ℕ} (b : ι → ℝ) (hr : Fintype.card ι ≤ r) :
    bidAtRank r b = 0 := by
  exact dite_eq_right fun ⟨i, hi⟩ => (hi ▸ rank_lt_card b i).not_ge hr

/-- **Uniform `(k + 1)`-st price multi-unit auction** ([Nisan2007], §9.3.5.4, p. 221): the top `k`
bidders win one item each and every winner pays `bidAtRank k b` (the `(k + 1)`-st highest bid, or
`0` when `Fintype.card ι ≤ k`); losers pay `0`. -/
noncomputable def mechanism (k : ℕ) : Mechanism ι where
  allocation := allocation k
  payment b i := bidAtRank k b * allocation k b i

@[simp] theorem mechanism_allocation (k : ℕ) :
    (mechanism (ι := ι) k).allocation = allocation k := by
  rfl

@[simp] theorem mechanism_payment (k : ℕ) (b : ι → ℝ) (i : ι) :
    (mechanism k).payment b i = bidAtRank k b * allocation k b i := by
  rfl

open Classical in
/-- For every winning bidder `i` on a nonnegative profile `b`, `criticalBid (allocation k) b i`
equals the uniform `(k + 1)`-st highest bid `bidAtRank k b`. -/
theorem criticalBid_allocation_of_wins {k : ℕ} {b : ι → ℝ} (hb : 0 ≤ b) {i : ι}
    (hw : Wins k b i) :
    criticalBid (allocation k) b i = bidAtRank k b := by
  rcases le_or_gt (Fintype.card ι) k with hnk | hkn
  · rw [bidAtRank_of_card_le b hnk]
    have h0 : allocation k (Function.update b i 0) i = 1 :=
      allocation_eq_one_iff.2 ((rank_lt_card _ i).trans_le hnk)
    exact le_antisymm (criticalBid_le le_rfl h0) (criticalBid_nonneg _ b i)
  · obtain ⟨ik, hik⟩ := exists_rank_eq (b := b) hkn
    rw [bidAtRank_eq_of_rank_nonneg hb hik]
    have hbeat_i : Beats b i ik := beats_iff_rank_lt.2 (hik ▸ hw)
    have hi_ne_ik : i ≠ ik := fun h => beats_irrefl b i (h ▸ hbeat_i)
    let S : Finset ι := (Finset.univ.filter fun j => Beats b j ik).erase i
    have hi_mem : i ∈ Finset.univ.filter (fun j => Beats b j ik) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ i, hbeat_i⟩
    have hS_card : S.card = k - 1 := by rw [Finset.card_erase_of_mem hi_mem, ← hik]; rfl
    have hk_pos : 1 ≤ k := Nat.one_le_iff_ne_zero.2 fun h0 => Nat.not_lt_zero _ (h0 ▸ hw)
    refine criticalBid_eq_of_threshold (hb ik) (fun z hz => ?_) (fun z hz hwin => ?_)
    · have hsub : (Finset.univ.filter fun j => Beats (Function.update b i z) j i) ⊆ S := by
        intro j hj
        have hjb : Beats (Function.update b i z) j i := (Finset.mem_filter.1 hj).2
        have hj_ne_i : j ≠ i := fun h => beats_irrefl _ i (h ▸ hjb)
        refine Finset.mem_erase.2 ⟨hj_ne_i, Finset.mem_filter.2 ⟨Finset.mem_univ j, Or.inl ?_⟩⟩
        exact hz.trans_le <| by
          simpa only [Function.update_self, Function.update_of_ne hj_ne_i] using le_of_beats hjb
      exact allocation_eq_one_iff.2
        ((Finset.card_le_card hsub).trans_lt (hS_card ▸ Nat.sub_lt hk_pos zero_lt_one))
    · by_contra! hlt
      have hik_not_S : ik ∉ S := fun hm =>
        beats_irrefl b ik (Finset.mem_filter.1 (Finset.mem_of_mem_erase hm)).2
      have hsup : insert ik S ⊆
          Finset.univ.filter fun j => Beats (Function.update b i z) j i := by
        intro j hj
        refine Finset.mem_filter.2 ⟨Finset.mem_univ j, Or.inl ?_⟩
        rcases Finset.mem_insert.1 hj with rfl | hjS
        · simpa only [Function.update_self, Function.update_of_ne hi_ne_ik.symm] using hlt
        · simpa only [Function.update_self, Function.update_of_ne (Finset.ne_of_mem_erase hjS)]
            using hlt.trans_le (le_of_beats (Finset.mem_filter.1 (Finset.mem_of_mem_erase hjS)).2)
      have hcard := Finset.card_le_card hsup
      rw [Finset.card_insert_of_notMem hik_not_S, hS_card, Nat.sub_add_cancel hk_pos] at hcard
      exact absurd hcard (not_le.2 (allocation_eq_one_iff.1 hwin))

/-- On every nonnegative bid profile, `criticalBidMechanism (allocation k)` and `mechanism k` have
identical allocations and payments. -/
theorem criticalBidMechanism_eq_on_nonneg (k : ℕ) {b : ι → ℝ} (hb : 0 ≤ b) :
    (criticalBidMechanism (allocation (ι := ι) k)).allocation b = (mechanism k).allocation b ∧
      (criticalBidMechanism (allocation (ι := ι) k)).payment b = (mechanism k).payment b := by
  refine ⟨rfl, funext fun i => ?_⟩
  simp only [criticalBidMechanism, mechanism]
  by_cases hw : Wins k b i
  · rw [criticalBid_allocation_of_wins hb hw]
  · rw [allocation_eq_zero_iff.2 hw, mul_zero, mul_zero]

/-- **Uniform `(k + 1)`-st price payment equals Myerson's payment** on nonnegative bids. -/
theorem mechanism_payment_eq_myersonPayment (k : ℕ) {b : ι → ℝ} (hb : 0 ≤ b) (i : ι) :
    (mechanism k).payment b i = myersonPayment (allocation k) b i := by
  rw [← (criticalBidMechanism_eq_on_nonneg k hb).2]
  exact criticalBid_mul_eq_myersonPayment (isMonotone_allocation k) (isBinary_allocation k) hb i

/-- **The `(k + 1)`-st price `k`-unit auction is DSIC** ([Nisan2007], §9.3.5.4, p. 221). -/
theorem mechanism_isDSIC (k : ℕ) : (mechanism (ι := ι) k).IsDSIC :=
  (criticalBidMechanism_isDSIC (isMonotone_allocation k) (isBinary_allocation k)).congr
    fun _ hb => criticalBidMechanism_eq_on_nonneg k hb

/-- **The `(k + 1)`-st price `k`-unit auction is individually rational**. -/
theorem mechanism_isIR (k : ℕ) : (mechanism (ι := ι) k).IsIR :=
  (criticalBidMechanism_isIR (isBinary_allocation k)).congr
    fun _ hb => criticalBidMechanism_eq_on_nonneg k hb

/-- In the `(k + 1)`-st price auction, a zero bid pays zero. -/
theorem mechanism_isNormalized (k : ℕ) : (mechanism (ι := ι) k).IsNormalized := by
  intro i b hb
  rw [mechanism_payment_eq_myersonPayment k (update_nonneg hb i le_rfl)]
  exact myerson_isNormalized _ i b hb

/-- For `k = 1`, `MultiUnit.mechanism 1` agrees with `Vickrey.mechanism` on nonnegative bids. -/
theorem mechanism_one_eq_vickrey {b : ι → ℝ} (hb : 0 ≤ b) :
    (mechanism (ι := ι) 1).allocation b = Vickrey.mechanism.allocation b ∧
      (mechanism (ι := ι) 1).payment b = Vickrey.mechanism.payment b := by
  refine ⟨congrFun allocation_one b, funext fun i => ?_⟩
  rw [mechanism_payment_eq_myersonPayment 1 hb i, allocation_one,
    ← Vickrey.mechanism_payment_eq_myersonPayment hb i]

/-! ### Discriminatory `(j + 1)`-st price auction is not DSIC -/

/-- **Discriminatory `(j + 1)`-st price multi-unit auction** (original; not in [Nisan2007]): the
`j`-th highest bidder (`1 ≤ j ≤ k`, 0-indexed `rank b i = j - 1`) wins one item and pays the
`(j + 1)`-st highest bid `bidAtRank (rank b i + 1) b` (`0` if `Fintype.card ι ≤ j`); losers pay
`0`. -/
noncomputable def nextBidMechanism (k : ℕ) : Mechanism ι where
  allocation := allocation k
  payment b i := bidAtRank (rank b i + 1) b * allocation k b i

@[simp] theorem nextBidMechanism_allocation (k : ℕ) :
    (nextBidMechanism (ι := ι) k).allocation = allocation k := by
  rfl

@[simp] theorem nextBidMechanism_payment (k : ℕ) (b : ι → ℝ) (i : ι) :
    (nextBidMechanism k).payment b i = bidAtRank (rank b i + 1) b * allocation k b i := by
  rfl

/-- For `k = 1`, `nextBidMechanism 1` coincides with `mechanism 1` (since the unique winner has
`rank b i = 0`, paying `bidAtRank 1 b`). -/
theorem nextBidMechanism_one_eq_mechanism :
    nextBidMechanism (ι := ι) 1 = mechanism 1 := by
  refine congrArg (Mechanism.mk (allocation 1)) (funext fun b => funext fun i => ?_)
  by_cases hw : Wins 1 b i
  · rw [Nat.lt_one_iff.1 hw]
  · rw [allocation_eq_zero_iff.2 hw, mul_zero, mul_zero]

open Classical in
/-- When `Fintype.card ι ≤ 1`, `nextBidMechanism k` charges `0` everywhere and is DSIC. -/
theorem nextBidMechanism_isDSIC_of_card_le_one (k : ℕ) (hn : Fintype.card ι ≤ 1) :
    (nextBidMechanism (ι := ι) k).IsDSIC := by
  intro i b v _ _
  have hp0 (c : ι → ℝ) : (nextBidMechanism k).payment c i = 0 := by
    simp only [nextBidMechanism_payment, bidAtRank_of_card_le (r := rank c i + 1) c (by omega),
      zero_mul]
  have ha : ∀ c : ι → ℝ, allocation k c i = if 0 < k then 1 else 0 := fun c => by
    have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.1 hn
    have hr0 : rank c i = 0 := by
      rw [rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun j _ hjb => beats_irrefl c i (hsub.elim j i ▸ hjb)
    simp only [allocation, Wins, hr0]
  simp only [Mechanism.utility, hp0, nextBidMechanism_allocation, ha, sub_zero, le_rfl]

open Classical in
/-- If bidder `i`'s bid strictly exceeds every other bid, `rank b i = 0`. -/
theorem rank_eq_zero_of_gt {b : ι → ℝ} {i : ι} (h : ∀ j, j ≠ i → b j < b i) :
    rank b i = 0 := by
  rw [rank, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun j _ hjb => (le_of_beats hjb).not_gt (h j fun he => beats_irrefl b i (he ▸ hjb))

open Classical in
/-- If `top` strictly outbids `second` and `second` strictly outbids everyone else,
`rank b second = 1`. -/
theorem rank_eq_one_of_between {b : ι → ℝ} {top second : ι} (htop : b second < b top)
    (hother : ∀ j, j ≠ second → j ≠ top → b j < b second) :
    rank b second = 1 := by
  have hfilt : (Finset.univ.filter fun j => Beats b j second) = {top} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    refine ⟨fun hjb => ?_, fun h => h ▸ Or.inl htop⟩
    by_contra hjt
    have hjs : j ≠ second := fun he => beats_irrefl b second (he ▸ hjb)
    exact (le_of_beats hjb).not_gt (hother j hjs hjt)
  rw [rank, hfilt, Finset.card_singleton]

open Classical in
/-- **Charging the `j`-th highest bidder the `(j + 1)`-st highest bid is not DSIC** (original; not
in [Nisan2007]) whenever `2 ≤ k` and `2 ≤ Fintype.card ι`: when `i₀` has true value `3`, `i₁ ≠ i₀`
bids `2`, and any remaining bidders bid `0`, bidding truthfully gives `i₀` rank `0` at price `2`
(utility `1`), whereas shading to `1` gives `i₀` rank `1 < k` (still winning one item) at price `0`
(utility `3 > 1`). -/
theorem not_isDSIC_nextBidMechanism {k : ℕ} (hk : 2 ≤ k) (hn : 2 ≤ Fintype.card ι) :
    ¬ (nextBidMechanism (ι := ι) k).IsDSIC := by
  intro hDSIC
  obtain ⟨i₀, i₁, hne⟩ := Fintype.one_lt_card_iff.1 hn
  let b : ι → ℝ := fun m => if m = i₀ then 1 else if m = i₁ then 2 else 0
  have hb0 : 0 ≤ b := fun m => by dsimp only [b]; split_ifs <;> norm_num
  have hrank_b_i₀ : rank b i₀ = 1 :=
    rank_eq_one_of_between (top := i₁) (by norm_num [b, hne.symm])
      fun j hj0 hj1 => by norm_num [b, hj0, hj1]
  have hrank_b_i₁ : rank b i₁ = 0 := rank_eq_zero_of_gt fun j hj1 => by
    rcases eq_or_ne j i₀ with rfl | hj0 <;> norm_num [b, hne.symm, *]
  have hpay_shaded : bidAtRank 2 b = 0 := by
    by_cases hex : ∃ m, rank b m = 2
    · obtain ⟨m, hm⟩ := hex
      have hm0 : m ≠ i₀ := fun h => by simp [h, hrank_b_i₀] at hm
      have hm1 : m ≠ i₁ := fun h => by simp [h, hrank_b_i₁] at hm
      simpa [b, hm0, hm1] using bidAtRank_eq_of_rank_nonneg hb0 hm
    · exact dite_eq_right hex
  -- At truthful profile `b* = update b i₀ 3`, `i₀` has rank `0` and `i₁` has rank `1`.
  let bStar := Function.update b i₀ 3
  have hbStar0 : 0 ≤ bStar := update_nonneg hb0 i₀ (by norm_num)
  have hrank_bStar_i₀ : rank bStar i₀ = 0 := rank_eq_zero_of_gt fun j hj0 => by
    rcases eq_or_ne j i₁ with rfl | hj1
    · norm_num [bStar, Function.update_self, Function.update_of_ne hj0, b, hj0]
    · norm_num [bStar, Function.update_self, Function.update_of_ne hj0, b, hj0, hj1]
  have hrank_bStar_i₁ : rank bStar i₁ = 1 :=
    rank_eq_one_of_between (top := i₀)
      (by norm_num [bStar, Function.update_self, Function.update_of_ne hne.symm, b, hne.symm])
      fun j hj1 hj0 => by
        norm_num [bStar, Function.update_of_ne hj0, Function.update_of_ne hne.symm, b, hj0, hj1,
          hne.symm]
  have hwin_shaded : allocation k b i₀ = 1 :=
    allocation_eq_one_iff.2 (by rw [Wins, hrank_b_i₀]; omega)
  have hwin_truth : allocation k bStar i₀ = 1 :=
    allocation_eq_one_iff.2 (by rw [Wins, hrank_bStar_i₀]; omega)
  have hpay_truth : bidAtRank 1 bStar = 2 := by
    simpa [bStar, b, hne.symm] using bidAtRank_eq_of_rank_nonneg hbStar0 hrank_bStar_i₁
  have hineq : (nextBidMechanism k).utility i₀ 3 b ≤ (nextBidMechanism k).utility i₀ 3 bStar :=
    hDSIC i₀ b 3 hb0 (by norm_num)
  simp only [Mechanism.utility, nextBidMechanism, hrank_b_i₀, hrank_bStar_i₀,
    hwin_shaded, hwin_truth, hpay_shaded, hpay_truth] at hineq
  norm_num at hineq

end Order

end Cslib.GameTheory.SingleParameter.MultiUnit
