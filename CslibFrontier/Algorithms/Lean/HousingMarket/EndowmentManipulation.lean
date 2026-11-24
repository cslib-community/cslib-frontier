/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.HousingMarket.TopTradingCycles
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card

/-!
# Coalitional pre-trade endowment manipulation in top trading cycles

In a Shapley–Scarf housing market `I : Instance n`, suppose a coalition `S` of agents privately
permutes its initial endowments via `σ : Allocation n` (`∀ i ∉ S, σ i = i`) before Gale's top
trading cycles (TTC) mechanism is run: agent `i` enters the market holding house `σ i` and reports
its true preference order `I.pref i`, so slot `h` in the re-endowed market `I.reendow σ` has
preferences `I.pref (σ.symm h)` and agent `i` ultimately receives house
`I.preTradeTTC σ i = (I.reendow σ).ttc (σ i)`.

Exercise 10.7 of [SchummerVohra2007] (p. 265) asks whether all members of `S` can be **strictly**
better off under `I.preTradeTTC σ` than under `I.ttc`. We prove that the answer is **no** for every
`n` (`not_forall_rank_preTradeTTC_lt`, and in coalition-free form `exists_moved_rank_ttc_le`): under
any nontrivial endowment permutation `σ ≠ 1`, at least one agent `i` with `σ i ≠ i` weakly prefers
its honest TTC house `I.ttc i` to `I.preTradeTTC σ i`.

In contrast, **weak** coalitional pre-trade manipulation (every member of `S` weakly better off and
at least one strictly better off) **is** possible even for `n = 3`
(`exists_weak_preTradeTTC_manipulation`): TTC is group strategy-proof with respect to preference
reports, whereas reallocating physical endowments before TTC changes the ownership pointers seen by
third parties.

## Main definitions

* `Instance.reendow`: the market `Instance n` induced when agent `i` brings house `σ i`.
* `Instance.preTradeTTC`: the resulting physical allocation `σ.trans (I.reendow σ).ttc`.

## Main results

* `Instance.exists_moved_rank_ttc_le`: for every `σ ≠ 1`, some agent `i` with `σ i ≠ i` satisfies
  `I.rank i (I.ttc i) ≤ I.rank i (I.preTradeTTC σ i)`.
* `Instance.not_forall_rank_preTradeTTC_lt` (**NRTV Exercise 10.7**, [SchummerVohra2007], p. 265):
  no nonempty coalition `S` can make all its members strictly better off by permuting its initial
  endowments before TTC.
* `exists_weak_preTradeTTC_manipulation`: a checked `3`-agent housing market and `2`-agent pre-trade
  swap in which one coalition member keeps its top choice while the other strictly improves.

## References

* [ShapleyScarf1974] (primary PDF unverified)
* [SchummerVohra2007], Exercise 10.7, p. 265
-/

public section

namespace Cslib.Algorithms.Lean.HousingMarket

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- The housing market induced when each agent `i` enters TTC holding house `σ i`: the trader
occupying house-slot `h` is physical agent `σ.symm h`, with preferences `I.pref (σ.symm h)`. -/
@[expose] def reendow (σ : Allocation n) : Instance n where
  pref h := I.pref (σ.symm h)

/-- The physical allocation obtained when agents first permute endowments by `σ` and then run TTC:
agent `i` enters with house `σ i` and receives `(I.reendow σ).ttc (σ i)`. -/
@[expose] def preTradeTTC (σ : Allocation n) : Allocation n :=
  σ.trans (I.reendow σ).ttc

@[simp] theorem preTradeTTC_apply (σ : Allocation n) (i : Fin n) :
    I.preTradeTTC σ i = (I.reendow σ).ttc (σ i) := rfl

@[simp] theorem reendow_refl : I.reendow (1 : Allocation n) = I := rfl

@[simp] theorem preTradeTTC_refl : I.preTradeTTC (1 : Allocation n) = I.ttc := by
  ext i
  rfl

@[simp] theorem reendow_rank (σ : Allocation n) (h x : Fin n) :
    (I.reendow σ).rank h x = I.rank (σ.symm h) x := rfl

private theorem eq_empty_of_strict_preTrade_rounds {σ : Allocation n} {S : Finset (Fin n)}
    (hsupp : ∀ i, i ∉ S → σ i = i) :
    ∀ {k : ℕ} {R : Finset (Fin n)}, R.card ≤ k → S ⊆ R →
      (∀ h ∈ R, (I.reendow σ).ttc h ∈ R) →
      (∀ i ∈ S, I.rank i (I.preTradeTTC σ i) < I.rank i (I.ttcRounds k R i)) →
      S = ∅ := by
  have hσ_maps_S : ∀ i ∈ S, σ i ∈ S := by
    intro i hi
    by_contra hnot
    have hfix : σ (σ i) = σ i := hsupp (σ i) hnot
    have heq : σ i = i := σ.injective hfix
    exact hnot (heq.symm ▸ hi)
  intro k
  induction k with
  | zero =>
    intro R hk hSR _ _
    have hR0 : R = ∅ := Finset.card_eq_zero.1 (Nat.eq_zero_of_le_zero hk)
    exact Finset.subset_empty.1 (hR0 ▸ hSR)
  | succ k ih =>
    intro R hk hSR hR hlt
    by_cases hR_emp : R = ∅
    · exact Finset.subset_empty.1 (hR_emp ▸ hSR)
    have hRne : R.Nonempty := Finset.nonempty_iff_ne_empty.2 hR_emp
    set C := I.cycleAgents R
    have hk' : (R \ C).card ≤ k := by
      have hlt_c : (R \ C).card < R.card := I.card_sdiff_cycleAgents_lt hRne
      omega
    -- Step 1: No agent in `C` can belong to `S`.
    have hdisj : ∀ a ∈ C, a ∉ S := by
      intro a haC haS
      have hσa_R : σ a ∈ R := hSR (hσ_maps_S a haS)
      have hpre_R : I.preTradeTTC σ a ∈ R := hR (σ a) hσa_R
      have htop_le : I.rank a (I.topChoice R a) ≤ I.rank a (I.preTradeTTC σ a) :=
        I.rank_topChoice_le hpre_R a
      have hstrict := hlt a haS
      rw [I.ttcRounds_succ_of_mem haC] at hstrict
      exact not_lt_of_ge htop_le hstrict
    -- Step 2: Every agent in `C` is fixed by `σ` (and `σ.symm`), so `(I.reendow σ).ttc` agrees
    -- with `I.topChoice R` on `C` by `(I.reendow σ).inStrictCore_ttc`.
    have hsymm_C : ∀ a ∈ C, σ.symm a = a := by
      intro a haC
      apply σ.injective
      rw [Equiv.apply_symm_apply, hsupp a (hdisj a haC)]
    let μ' : Allocation n := (I.reendow σ).ttc
    have hμ'_strict : (I.reendow σ).InStrictCore μ' := (I.reendow σ).inStrictCore_ttc
    classical
    let g : Fin n → Fin n := fun a => if a ∈ C then I.topChoice R a else a
    have hg : Function.Injective g := by
      intro a b hab
      simp only [g] at hab
      split_ifs at hab with ha hb hb
      · exact I.topChoice_injOn_cycleAgents R ha hb hab
      · exact absurd (hab ▸ I.topChoice_mem_cycleAgents ha) hb
      · exact absurd (hab ▸ I.topChoice_mem_cycleAgents hb) ha
      · exact hab
    let ν : Allocation n := StableMatching.permOfInjective g hg
    have hνC : ∀ a ∈ C, ν a = I.topChoice R a := fun a ha => ite_eq_left ha
    have hμ'C : ∀ a ∈ C, μ' a = I.topChoice R a := by
      have hle : ∀ a ∈ C, I.rank a (I.topChoice R a) ≤ I.rank a (μ' a) :=
        fun a ha => I.rank_topChoice_le (hR a (I.cycleAgents_subset R ha)) a
      intro a ha
      by_contra hne
      refine hμ'_strict C ⟨ν, fun b hb => ?_, fun b hb => ?_, a, ha, ?_⟩
      · rw [hνC b hb]
        exact I.topChoice_mem_cycleAgents hb
      · rw [reendow_rank, reendow_rank, hsymm_C b hb, hνC b hb]
        exact hle b hb
      · rw [reendow_rank, reendow_rank, hsymm_C a ha, hνC a ha]
        exact lt_of_le_of_ne (hle a ha) fun heq => hne (I.rank_injective a heq).symm
    -- Step 3: `μ'` maps `C` onto itself, hence `R \ C` into itself; recurse on `R \ C`.
    have himg_C : C.image μ' = C :=
      Finset.eq_of_subset_of_card_le
        (Finset.image_subset_iff.2 fun b hb => hμ'C b hb ▸ I.topChoice_mem_cycleAgents hb)
        (by rw [Finset.card_image_of_injective C μ'.injective])
    have hR' : ∀ h ∈ R \ C, μ' h ∈ R \ C := by
      intro h hh
      obtain ⟨hhR, hhC⟩ := Finset.mem_sdiff.1 hh
      refine Finset.mem_sdiff.2 ⟨hR h hhR, fun hmem => hhC ?_⟩
      obtain ⟨b, hbC, hbh⟩ := Finset.mem_image.1 (himg_C.symm ▸ hmem)
      exact μ'.injective hbh ▸ hbC
    have hSR' : S ⊆ R \ C := fun i hi => Finset.mem_sdiff.2 ⟨hSR hi, fun hiC => hdisj i hiC hi⟩
    refine ih hk' hSR' hR' fun i hi => ?_
    have hi_not_C : i ∉ C := (Finset.mem_sdiff.1 (hSR' hi)).2
    have hstrict := hlt i hi
    rwa [I.ttcRounds_succ_of_notMem hi_not_C] at hstrict

/-- **NRTV Exercise 10.7** ([SchummerVohra2007], p. 265): no nonempty coalition `S` can make **all**
of its members strictly better off by permuting its initial endowments (`∀ i ∉ S, σ i = i`) before
top trading cycles is run. -/
theorem not_forall_rank_preTradeTTC_lt {S : Finset (Fin n)} (hS : S.Nonempty)
    {σ : Allocation n} (hsupp : ∀ i, i ∉ S → σ i = i) :
    ¬ ∀ i ∈ S, I.rank i (I.preTradeTTC σ i) < I.rank i (I.ttc i) := by
  intro hlt
  have hemp : S = ∅ :=
    I.eq_empty_of_strict_preTrade_rounds hsupp (k := n)
      (by rw [Finset.card_univ, Fintype.card_fin])
      (Finset.subset_univ S)
      (fun _ _ => Finset.mem_univ _)
      (fun i hi => by simpa only [ttc_apply] using hlt i hi)
  exact hS.ne_empty hemp

/-- Coalition-free form of `not_forall_rank_preTradeTTC_lt`: under any nontrivial pre-trade
endowment permutation `σ ≠ 1`, at least one agent `i` who trades its endowment (`σ i ≠ i`) is no
better off than under honest TTC. -/
theorem exists_moved_rank_ttc_le {σ : Allocation n} (hσ : σ ≠ 1) :
    ∃ i : Fin n, σ i ≠ i ∧ I.rank i (I.ttc i) ≤ I.rank i (I.preTradeTTC σ i) := by
  let S : Finset (Fin n) := Finset.univ.filter fun i => σ i ≠ i
  have hSne : S.Nonempty := by
    by_contra hnot
    rw [Finset.not_nonempty_iff_eq_empty] at hnot
    apply hσ
    refine Equiv.ext fun i => ?_
    by_contra hne
    have hiS : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩
    rw [hnot] at hiS
    exact Finset.notMem_empty i hiS
  have hsupp : ∀ i, i ∉ S → σ i = i := by
    intro i hi
    by_contra hne
    exact hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩)
  have hnot_all := I.not_forall_rank_preTradeTTC_lt hSne hsupp
  push Not at hnot_all
  obtain ⟨i, hiS, hle⟩ := hnot_all
  exact ⟨i, (Finset.mem_filter.1 hiS).2, hle⟩

end Instance

/-! ### Weak coalitional pre-trade manipulation is possible (`n = 3`) -/

/-- A `3`-agent housing market witnessing that **weak** coalitional pre-trade manipulation of TTC is
possible:
* Agent `0` ranks `1 > 0 > 2`;
* Agent `1` ranks `0 > 2 > 1`;
* Agent `2` ranks `0 > 1 > 2`.

Under honest TTC (`weakPreTradeInstance.ttc`), agents `0` and `1` trade with each other (`0 ↦ 1`,
`1 ↦ 0`) and agent `2` keeps house `2`. If coalition `S = {0, 2}` swaps endowments (`σ = swap 0 2`)
before TTC, in Round 1 house-slot `0` (now held by agent `2`) points to itself (a `1`-cycle `{0}`),
so agent `2` exits immediately with house `0` (strictly better than `2`), and in Round 2 the
remaining slots `{1, 2}` form a `2`-cycle giving `1 ↦ 2` and `0 ↦ 1` (agent `0` keeps its top
choice `1`). -/
@[expose] def weakPreTradeInstance : Instance 3 where
  pref := ![
    StableMatching.permOfInjective ![1, 0, 2],
    StableMatching.permOfInjective ![0, 2, 1],
    StableMatching.permOfInjective ![0, 1, 2]]

/-- Unlike strict coalitional improvement (`Instance.not_forall_rank_preTradeTTC_lt`), a coalition
can **weakly** improve all its members (with at least one member strictly better off) by permuting
its endowments before TTC. -/
theorem exists_weak_preTradeTTC_manipulation :
    ∃ (I : Instance 3) (S : Finset (Fin 3)) (σ : Allocation 3),
      S.Nonempty ∧
      (∀ i, i ∉ S → σ i = i) ∧
      (∀ i ∈ S, I.rank i (I.preTradeTTC σ i) ≤ I.rank i (I.ttc i)) ∧
      (∃ i ∈ S, I.rank i (I.preTradeTTC σ i) < I.rank i (I.ttc i)) := by
  refine ⟨weakPreTradeInstance, {0, 2}, Equiv.swap 0 2, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide

end Cslib.Algorithms.Lean.HousingMarket
