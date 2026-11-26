/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Mechanism.LinearValuation
public import CslibFrontier.GameTheory.Mechanism.Vickrey
public import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Linarith

/-!
# The Vickrey auction is VCG

A single item can go to one bidder or to nobody: the outcomes are `Option ι`, and bidder `i` is
allocated `singleItem ω i`, which is `1` when `ω = some i` and `0` otherwise. On the linear
valuations of scalar bids `b`, the Clarke pivot of bidder `i` is the highest other bid
(`clarkePivot_linearProfile_singleItem`). So for every welfare-maximizing outcome rule, whatever
its tie-breaking, the VCG payment is the second price `highestOtherBid b i` charged to the winner
(`vcg_payment_linearProfile_singleItem`). `winner b` is the Vickrey winner as a single-item
outcome. Every welfare-maximizing rule that chooses it makes VCG, run on linear valuations,
allocate and charge as `SingleParameter.Vickrey.mechanism`
(`vcg_toSingleParameter_eq_of_eq_winner`), and on nonnegative bids such a rule exists
(`exists_vcg_toSingleParameter_eq`). This is the
specialization of VCG to Vickrey ([Roughgarden2013CS364A], Lecture 7, §2; [Nisan2007], §9.3.5.1).

The map `singleItem` identifies `Option ι` with the feasible subtype `singleItemFeasible`
(`singleItemEquiv : Option ι ≃ singleItemFeasible`). Transporting the `Option ι` VCG construction
along this equivalence gives `vcgOutcome` directly on `singleItemFeasible`, recovering
`Vickrey.mechanism` without repeating the Clarke-pivot or second-price analysis
(`clarkePivot_singleItemFeasible`, `vcg_singleItemFeasible_allocation`,
`vcg_singleItemFeasible_payment`).

## Main definitions

* `Cslib.GameTheory.SingleParameter.Vickrey.singleItem`: the allocation of a single-item outcome.
* `Cslib.GameTheory.SingleParameter.Vickrey.winner`: the Vickrey winner as a single-item outcome
  (`winner_eq_some`, `winner_eq_none`).
* `Cslib.GameTheory.SingleParameter.Vickrey.singleItemEquiv`: equivalence
  `Option ι ≃ singleItemFeasible`.
* `Cslib.GameTheory.SingleParameter.Vickrey.singleWinner`,
  `Cslib.GameTheory.SingleParameter.Vickrey.vcgOutcome`: single-winner feasible allocations and
  welfare-maximizing rule on `singleItemFeasible`.

## Main results

* `Cslib.GameTheory.SingleParameter.Vickrey.vcg_payment_linearProfile_singleItem`: VCG charges the
  second price, for any welfare-maximizing rule.
* `Cslib.GameTheory.SingleParameter.Vickrey.vcg_toSingleParameter_eq_of_eq_winner`: VCG with
  Vickrey's tie-breaking allocates and charges as the Vickrey auction.
* `Cslib.GameTheory.SingleParameter.Vickrey.exists_vcg_toSingleParameter_eq`: the Vickrey auction
  is VCG on single-item outcomes.
* `Cslib.GameTheory.SingleParameter.Vickrey.isWelfareMaximizing_vcgOutcome`,
  `Cslib.GameTheory.SingleParameter.Vickrey.vcg_singleItemFeasible_allocation`,
  `Cslib.GameTheory.SingleParameter.Vickrey.vcg_singleItemFeasible_payment`: VCG directly on
  `singleItemFeasible` agrees with `Vickrey.mechanism` ([Nisan2007], §9.3.5.1).

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [W. Vickrey, *Counterspeculation, auctions, and competitive sealed tenders*][Vickrey1961]
-/

public section

namespace Cslib.GameTheory.SingleParameter.Vickrey

open GameTheory.Mechanism (linearProfile vcg groves clarkePivot welfare)

variable {ι : Type*} [LinearOrder ι]

/-- The allocation of the single-item outcome `ω`: bidder `i` gets the item when `ω = some i`. -/
@[expose] def singleItem (ω : Option ι) (i : ι) : ℝ := if ω = some i then 1 else 0

@[simp]
theorem singleItem_none (i : ι) : singleItem none i = 0 := by
  simp [singleItem]

@[simp]
theorem singleItem_some (k i : ι) : singleItem (some k) i = if k = i then 1 else 0 := by
  simp [singleItem]

theorem singleItem_nonneg : 0 ≤ (singleItem : Option ι → ι → ℝ) := fun ω i => by
  by_cases h : ω = some i <;> simp [singleItem, h]

private theorem sum_linearProfile_none (b : ι → ℝ) (s : Finset ι) :
    ∑ j ∈ s, linearProfile singleItem b j none = 0 := by
  simp

private theorem sum_linearProfile_some (b : ι → ℝ) (s : Finset ι) (k : ι) :
    ∑ j ∈ s, linearProfile singleItem b j (some k) = if k ∈ s then b k else 0 := by
  simp

/-- The bids read off a profile of single-item valuations: bidder `j`'s value for winning. -/
private def ownBids (B : ι → Option ι → ℝ) : ι → ℝ := fun j => B j (some j)

private theorem ownBids_linearProfile (b : ι → ℝ) : ownBids (linearProfile singleItem b) = b := by
  funext j
  simp [ownBids]

variable [Fintype ι]

private theorem welfare_none (b : ι → ℝ) : welfare (linearProfile singleItem b) none = 0 :=
  sum_linearProfile_none b _

private theorem welfare_some (b : ι → ℝ) (k : ι) :
    welfare (linearProfile singleItem b) (some k) = b k := by
  rw [welfare, sum_linearProfile_some, ite_eq_left (Finset.mem_univ k)]

/-- On single-item outcomes, the Clarke pivot of bidder `i` for the scalar bids `b` is the highest
other bid: the best the others can do without `i` is to give the item to the highest of them, or
to nobody. -/
theorem clarkePivot_linearProfile_singleItem (b : ι → ℝ) (i : ι) :
    clarkePivot i (linearProfile singleItem b) = highestOtherBid b i := by
  refine le_antisymm (Finset.sup'_le _ _ fun ω _ => ?_)
    (highestOtherBid_le_iff.2 ⟨?_, fun j hj => ?_⟩)
  · change ∑ j ∈ Finset.univ.erase i, linearProfile singleItem b j ω ≤ highestOtherBid b i
    cases ω with
    | none => rw [sum_linearProfile_none]; exact highestOtherBid_nonneg b i
    | some k =>
      rw [sum_linearProfile_some]
      split_ifs with hk
      · exact le_highestOtherBid (Finset.ne_of_mem_erase hk)
      · exact highestOtherBid_nonneg b i
  · exact Finset.le_sup'_of_le _ (Finset.mem_univ none) (sum_linearProfile_none b _).ge
  · refine Finset.le_sup'_of_le _ (Finset.mem_univ (some j)) ?_
    change b j ≤ ∑ k ∈ Finset.univ.erase i, linearProfile singleItem b k (some j)
    rw [sum_linearProfile_some, ite_eq_left (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)]

/-- **VCG charges the second price**: for every welfare-maximizing outcome rule on single-item
outcomes, whatever its tie-breaking, the VCG payment of bidder `i` on the linear valuations of the
bids `b` is the highest other bid if `i` gets the item, and `0` otherwise. -/
theorem vcg_payment_linearProfile_singleItem {f : (ι → Option ι → ℝ) → Option ι}
    (hf : GameTheory.Mechanism.IsWelfareMaximizing f) (b : ι → ℝ) (i : ι) :
    (vcg f).payment (linearProfile singleItem b) i =
      highestOtherBid b i * singleItem (f (linearProfile singleItem b)) i := by
  have hmax := hf (linearProfile singleItem b)
  simp only [vcg, groves, clarkePivot_linearProfile_singleItem]
  generalize f (linearProfile singleItem b) = ω₀ at hmax ⊢
  cases ω₀ with
  | none =>
    rw [welfare_none] at hmax
    rw [sum_linearProfile_none, singleItem_none, mul_zero, sub_zero]
    refine le_antisymm (highestOtherBid_le_iff.2 ⟨le_rfl, fun j _ => ?_⟩)
      (highestOtherBid_nonneg b i)
    simpa only [welfare_some] using hmax (some j)
  | some k =>
    rw [welfare_some] at hmax
    rw [sum_linearProfile_some, singleItem_some]
    by_cases hki : k = i
    · rw [hki, ite_eq_right (Finset.notMem_erase i _), ite_eq_left rfl, sub_zero, mul_one]
    · rw [ite_eq_left (Finset.mem_erase.2 ⟨hki, Finset.mem_univ k⟩), ite_eq_right hki, mul_zero,
        sub_eq_zero]
      refine le_antisymm (highestOtherBid_le_iff.2 ⟨?_, fun j _ => ?_⟩) (le_highestOtherBid hki)
      · simpa only [welfare_none] using hmax none
      · simpa only [welfare_some] using hmax (some j)

open Classical in
/-- The winner of the Vickrey auction as a single-item outcome. -/
noncomputable def winner (b : ι → ℝ) : Option ι := if h : ∃ i, Wins b i then some h.choose else none

/-- The unique Vickrey winner, when there is one, is the single-item outcome. -/
theorem winner_eq_some {b : ι → ℝ} {k : ι} (hk : Wins b k) : winner b = some k := by
  unfold winner
  split_ifs with h
  · exact congrArg some (h.choose_spec.unique hk)
  · exact absurd ⟨k, hk⟩ h

/-- Without a Vickrey winner, which happens only when there are no bidders (`exists_wins`), nobody
gets the item. -/
theorem winner_eq_none {b : ι → ℝ} (h : ¬∃ k, Wins b k) : winner b = none :=
  dite_eq_right h

theorem singleItem_winner (b : ι → ℝ) : singleItem (winner b) = allocation b := by
  funext i
  by_cases h : ∃ k, Wins b k
  · obtain ⟨k, hk⟩ := h
    rw [winner_eq_some hk, singleItem_some]
    by_cases hki : k = i
    · subst hki
      rw [ite_eq_left rfl, allocation_eq_one_iff.2 hk]
    · rw [ite_eq_right hki, allocation_eq_zero_iff.2 fun hi => hki (hk.unique hi)]
  · rw [winner_eq_none h, singleItem_none, allocation_eq_zero_iff.2 fun hi => h ⟨i, hi⟩]

/-- Every single-item outcome allocates a feasible 0-1 vector. -/
theorem singleItem_mem_singleItemFeasible (ω : Option ι) : singleItem ω ∈ singleItemFeasible := by
  refine ⟨fun j => ?_, ?_⟩
  · cases ω with
    | none => exact Or.inl (singleItem_none j)
    | some k =>
      rw [singleItem_some]
      split_ifs
      exacts [Or.inr rfl, Or.inl rfl]
  · cases ω <;> simp

/-- On nonnegative bids the Vickrey winner maximizes welfare among single-item outcomes. -/
theorem welfare_le_winner {b : ι → ℝ} (hb : 0 ≤ b) (ω : Option ι) :
    welfare (linearProfile singleItem b) ω ≤ welfare (linearProfile singleItem b) (winner b) := by
  have h := (isWelfareMaximizing_allocation b hb).2 _ (singleItem_mem_singleItemFeasible ω)
  rwa [← singleItem_winner] at h

open Classical in
/-- A welfare-maximizing rule `f₀`, patched to choose the Vickrey winner on the linear valuations of
nonnegative bids. -/
private noncomputable def vickreyRule (f₀ : (ι → Option ι → ℝ) → Option ι)
    (B : ι → Option ι → ℝ) : Option ι :=
  if 0 ≤ ownBids B ∧ linearProfile singleItem (ownBids B) = B then winner (ownBids B) else f₀ B

private theorem vickreyRule_linearProfile (f₀ : (ι → Option ι → ℝ) → Option ι) {b : ι → ℝ}
    (hb : 0 ≤ b) : vickreyRule f₀ (linearProfile singleItem b) = winner b := by
  simp [vickreyRule, ownBids_linearProfile, hb]

private theorem isWelfareMaximizing_vickreyRule {f₀ : (ι → Option ι → ℝ) → Option ι}
    (hf₀ : GameTheory.Mechanism.IsWelfareMaximizing f₀) :
    GameTheory.Mechanism.IsWelfareMaximizing (vickreyRule f₀) := by
  intro B ω
  by_cases h : 0 ≤ ownBids B ∧ linearProfile singleItem (ownBids B) = B
  · rw [← h.2, vickreyRule_linearProfile f₀ h.1]
    exact welfare_le_winner h.1 ω
  · simp only [vickreyRule, h, ↓reduceIte]
    exact hf₀ B ω

/-- **VCG with Vickrey's tie-breaking charges as Vickrey**: if a welfare-maximizing outcome rule
`f` gives the item to the Vickrey winner on the linear valuations of the bids `b`, then VCG, run
on linear valuations, allocates and charges at `b` exactly as the Vickrey auction. -/
theorem vcg_toSingleParameter_eq_of_eq_winner {f : (ι → Option ι → ℝ) → Option ι}
    (hf : GameTheory.Mechanism.IsWelfareMaximizing f) {b : ι → ℝ}
    (hfb : f (linearProfile singleItem b) = winner b) :
    ((vcg f).toSingleParameter singleItem).allocation b = mechanism.allocation b ∧
      ((vcg f).toSingleParameter singleItem).payment b = mechanism.payment b := by
  refine ⟨by simpa only [GameTheory.Mechanism.toSingleParameter, mechanism, vcg, groves, hfb] using
    singleItem_winner b, funext fun i => ?_⟩
  simpa only [GameTheory.Mechanism.toSingleParameter, mechanism, hfb, singleItem_winner] using
    vcg_payment_linearProfile_singleItem hf b i

/-- **The Vickrey auction is VCG** ([Roughgarden2013CS364A], Lecture 7, §2): some
welfare-maximizing outcome rule `f` on single-item outcomes makes the VCG mechanism, run on linear
valuations, allocate and charge exactly as the Vickrey auction on every nonnegative bid profile. -/
theorem exists_vcg_toSingleParameter_eq :
    ∃ f : (ι → Option ι → ℝ) → Option ι, GameTheory.Mechanism.IsWelfareMaximizing f ∧
      ∀ b : ι → ℝ, 0 ≤ b →
        ((vcg f).toSingleParameter singleItem).allocation b = mechanism.allocation b ∧
          ((vcg f).toSingleParameter singleItem).payment b = mechanism.payment b := by
  obtain ⟨f₀, hf₀⟩ := GameTheory.Mechanism.exists_isWelfareMaximizing (ι := ι) (Ω := Option ι)
  have hf := isWelfareMaximizing_vickreyRule hf₀
  exact ⟨vickreyRule f₀, hf, fun b hb =>
    vcg_toSingleParameter_eq_of_eq_winner hf (vickreyRule_linearProfile f₀ hb)⟩

/-! ### VCG directly on `singleItemFeasible` via `Option ι ≃ singleItemFeasible` -/

omit [Fintype ι] in
private theorem singleItem_injective : Function.Injective (singleItem (ι := ι))
  | none, none, _ => rfl
  | none, some k, h => absurd (congrFun h k) (by simp)
  | some k, none, h => absurd (congrFun h k) (by simp)
  | some k₁, some k₂, h => by
    have hk := congrFun h k₁
    simp only [singleItem_some, ↓reduceIte] at hk
    split_ifs at hk with h21
    · exact congrArg some h21.symm
    · exact absurd hk one_ne_zero

private theorem exists_singleItem_eq_of_mem {y : ι → ℝ} (hy : y ∈ singleItemFeasible) :
    ∃ ω : Option ι, singleItem ω = y := by
  by_cases h : ∃ k, y k = 1
  · obtain ⟨k, hk⟩ := h
    refine ⟨some k, funext fun i => ?_⟩
    rw [singleItem_some]
    rcases eq_or_ne k i with rfl | hki
    · simp [hk]
    · rw [ite_eq_right hki]
      rcases hy.1 i with hi | hi
      · exact hi.symm
      · have hy0 (j : ι) : 0 ≤ y j := by rcases hy.1 j with h0 | h1 <;> linarith
        have hle := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({k, i} : Finset ι))
          fun j _ _ => hy0 j
        rw [Finset.sum_pair hki] at hle
        linarith [hy.2]
  · push Not at h
    exact ⟨none, funext fun i => (singleItem_none i).trans ((hy.1 i).resolve_right (h i)).symm⟩

/-- The canonical bijection between `Option ι` and `singleItemFeasible`: `none` is the zero
allocation and `some i` gives the item to bidder `i`. -/
noncomputable def singleItemEquiv : Option ι ≃ singleItemFeasible (ι := ι) :=
  Equiv.ofBijective (fun ω => ⟨singleItem ω, singleItem_mem_singleItemFeasible ω⟩)
    ⟨fun _ _ h => singleItem_injective (congrArg Subtype.val h),
      fun ⟨_, hy⟩ => let ⟨ω, hω⟩ := exists_singleItem_eq_of_mem hy; ⟨ω, Subtype.ext hω⟩⟩

@[simp]
theorem singleItemEquiv_apply (ω : Option ι) : (singleItemEquiv ω : ι → ℝ) = singleItem ω := by
  rfl

noncomputable instance instFintypeSingleItemFeasible : Fintype (singleItemFeasible (ι := ι)) :=
  Fintype.ofEquiv (Option ι) singleItemEquiv

instance instNonemptySingleItemFeasible : Nonempty (singleItemFeasible (ι := ι)) :=
  ⟨singleItemEquiv none⟩

/-- The feasible single-item allocation in which bidder `i` alone gets the item. -/
def singleWinner (i : ι) : singleItemFeasible (ι := ι) :=
  ⟨singleItem (some i), singleItem_mem_singleItemFeasible (some i)⟩

@[simp]
theorem singleWinner_val (i : ι) : (singleWinner i : ι → ℝ) = singleItem (some i) := by
  rfl

@[simp]
theorem singleWinner_apply_self (i : ι) : (singleWinner i : ι → ℝ) i = 1 := by
  simp only [singleWinner_val, singleItem_some, ↓reduceIte]

theorem singleWinner_apply_of_ne {i j : ι} (hj : j ≠ i) : (singleWinner i : ι → ℝ) j = 0 := by
  simp only [singleWinner_val, singleItem_some, ite_eq_right hj.symm]

/-- A globally welfare-maximizing outcome rule directly on `singleItemFeasible` obtained by
transporting `vickreyRule` along `singleItemEquiv : Option ι ≃ singleItemFeasible`. -/
noncomputable def vcgOutcome (u : ι → singleItemFeasible (ι := ι) → ℝ) :
    singleItemFeasible (ι := ι) :=
  singleItemEquiv (vickreyRule
    (Classical.choose (GameTheory.Mechanism.exists_isWelfareMaximizing (ι := ι) (Ω := Option ι)))
    fun j ω => u j (singleItemEquiv ω))

/-- `vcgOutcome` maximizes reported welfare on every valuation profile. -/
theorem isWelfareMaximizing_vcgOutcome :
    GameTheory.Mechanism.IsWelfareMaximizing (vcgOutcome (ι := ι)) :=
  GameTheory.Mechanism.isWelfareMaximizing_comp_equiv singleItemEquiv
    (isWelfareMaximizing_vickreyRule
      (Classical.choose_spec
        (GameTheory.Mechanism.exists_isWelfareMaximizing (ι := ι) (Ω := Option ι))))

/-- On any nonnegative linear valuation profile on `singleItemFeasible`, `vcgOutcome` chooses
`Vickrey.allocation b`. -/
theorem vcgOutcome_linearProfile {b : ι → ℝ} (hb : 0 ≤ b) :
    vcgOutcome (linearProfile Subtype.val b) =
      ⟨allocation b, allocation_mem_singleItemFeasible b⟩ := by
  apply Subtype.ext
  change singleItem (vickreyRule _ (linearProfile singleItem b)) = allocation b
  rw [vickreyRule_linearProfile _ hb, singleItem_winner]

/-- On any linear valuation profile over `singleItemFeasible`, the Clarke pivot of agent `i`
equals `highestOtherBid b i`. -/
theorem clarkePivot_singleItemFeasible (b : ι → ℝ) (i : ι) :
    clarkePivot i
      (linearProfile (Subtype.val : singleItemFeasible (ι := ι) → ι → ℝ) b) =
        highestOtherBid b i := by
  rw [← GameTheory.Mechanism.clarkePivot_comp_equiv singleItemEquiv]
  exact clarkePivot_linearProfile_singleItem b i

/-- **VCG on `singleItemFeasible` agrees with `Vickrey.mechanism` (allocation)** ([Nisan2007],
§9.3.5.1). -/
theorem vcg_singleItemFeasible_allocation {b : ι → ℝ} (hb : 0 ≤ b) :
    ((vcg (vcgOutcome (ι := ι))).toSingleParameter Subtype.val).allocation b =
      mechanism.allocation b := by
  simp only [GameTheory.Mechanism.toSingleParameter, vcg, groves, vcgOutcome_linearProfile hb,
    mechanism]

/-- **VCG on `singleItemFeasible` agrees with `Vickrey.mechanism` (payment)** ([Nisan2007],
§9.3.5.1). -/
theorem vcg_singleItemFeasible_payment {b : ι → ℝ} (hb : 0 ≤ b) :
    ((vcg (vcgOutcome (ι := ι))).toSingleParameter Subtype.val).payment b =
      mechanism.payment b := by
  let hmax := GameTheory.Mechanism.exists_isWelfareMaximizing (ι := ι) (Ω := Option ι)
  funext i
  change (vcg fun u =>
      singleItemEquiv (vickreyRule hmax.choose fun j ω => u j (singleItemEquiv ω))).payment
      (linearProfile Subtype.val b) i = mechanism.payment b i
  rw [GameTheory.Mechanism.vcg_payment_comp_equiv singleItemEquiv]
  exact congrFun (vcg_toSingleParameter_eq_of_eq_winner
    (isWelfareMaximizing_vickreyRule hmax.choose_spec)
    (vickreyRule_linearProfile hmax.choose hb)).2 i

end Cslib.GameTheory.SingleParameter.Vickrey
