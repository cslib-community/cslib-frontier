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
  have hσ_maps_S {i : Fin n} (hi : i ∈ S) : σ i ∈ S := by
    by_contra hnot
    exact hnot ((σ.injective (hsupp (σ i) hnot)).symm ▸ hi)
  intro k
  induction k with
  | zero =>
    intro R hk hSR _ _
    exact Finset.subset_empty.1 (Finset.card_eq_zero.1 (Nat.eq_zero_of_le_zero hk) ▸ hSR)
  | succ k ih =>
    intro R hk hSR hR hlt
    rcases R.eq_empty_or_nonempty with rfl | hRne
    · exact Finset.subset_empty.1 hSR
    set C := I.cycleAgents R
    have hk' : (R \ C).card ≤ k :=
      Nat.le_of_lt_succ ((I.card_sdiff_cycleAgents_lt hRne).trans_le hk)
    -- Step 1: No agent in `C` can belong to `S`.
    have hdisj {a : Fin n} (haC : a ∈ C) (haS : a ∈ S) : False :=
      not_lt_of_ge (I.rank_topChoice_le (hR _ (hSR (hσ_maps_S haS))) a)
        (I.ttcRounds_succ_of_mem haC ▸ hlt a haS)
    -- Step 2: Every agent in `C` is fixed by `σ` (and `σ.symm`), so `(I.reendow σ).ttc` agrees
    -- with `I.topChoice R` on `C` by `(I.reendow σ).inStrictCore_ttc`.
    have hsymm_C {a : Fin n} (haC : a ∈ C) : σ.symm a = a :=
      σ.injective (by rw [Equiv.apply_symm_apply, hsupp a (hdisj haC)])
    let μ' : Allocation n := (I.reendow σ).ttc
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
    have hνC {a : Fin n} (ha : a ∈ C) : ν a = I.topChoice R a := ite_eq_left ha
    have hμ'C {a : Fin n} (ha : a ∈ C) : μ' a = I.topChoice R a := by
      have hle {b : Fin n} (hb : b ∈ C) : I.rank b (I.topChoice R b) ≤ I.rank b (μ' b) :=
        I.rank_topChoice_le (hR b (I.cycleAgents_subset R hb)) b
      by_contra hne
      refine (I.reendow σ).inStrictCore_ttc C ⟨ν,
        fun b hb => hνC hb ▸ I.topChoice_mem_cycleAgents hb,
        fun b hb => by simpa [hsymm_C hb, hνC hb] using hle hb, a, ha, ?_⟩
      simpa [hsymm_C ha, hνC ha] using
        lt_of_le_of_ne (hle ha) fun heq => hne (I.rank_injective a heq).symm
    -- Step 3: `μ'` maps `C` onto itself, hence `R \ C` into itself; recurse on `R \ C`.
    have himg_C : C.image μ' = C :=
      Finset.eq_of_subset_of_card_le
        (Finset.image_subset_iff.2 fun _ hb => hμ'C hb ▸ I.topChoice_mem_cycleAgents hb)
        (by rw [Finset.card_image_of_injective C μ'.injective])
    have hR' : ∀ h ∈ R \ C, μ' h ∈ R \ C := fun h hh => by
      obtain ⟨hhR, hhC⟩ := Finset.mem_sdiff.1 hh
      refine Finset.mem_sdiff.2 ⟨hR h hhR, fun hmem => hhC ?_⟩
      obtain ⟨b, hbC, hbh⟩ := Finset.mem_image.1 (himg_C.symm ▸ hmem)
      exact μ'.injective hbh ▸ hbC
    refine ih hk' (fun i hi => Finset.mem_sdiff.2 ⟨hSR hi, fun hiC => hdisj hiC hi⟩) hR'
      fun i hi => ?_
    simpa [I.ttcRounds_succ_of_notMem fun hiC => hdisj hiC hi] using hlt i hi

/-- **NRTV Exercise 10.7** ([SchummerVohra2007], p. 265): no nonempty coalition `S` can make **all**
of its members strictly better off by permuting its initial endowments (`∀ i ∉ S, σ i = i`) before
top trading cycles is run. -/
theorem not_forall_rank_preTradeTTC_lt {S : Finset (Fin n)} (hS : S.Nonempty)
    {σ : Allocation n} (hsupp : ∀ i, i ∉ S → σ i = i) :
    ¬ ∀ i ∈ S, I.rank i (I.preTradeTTC σ i) < I.rank i (I.ttc i) := fun hlt =>
  hS.ne_empty <| I.eq_empty_of_strict_preTrade_rounds hsupp
    (by simp : Finset.univ.card ≤ n) (Finset.subset_univ S) (fun _ _ => Finset.mem_univ _)
    fun i hi => by simpa only [ttc_apply] using hlt i hi

/-- Coalition-free form of `not_forall_rank_preTradeTTC_lt`: under any nontrivial pre-trade
endowment permutation `σ ≠ 1`, at least one agent `i` who trades its endowment (`σ i ≠ i`) is no
better off than under honest TTC. -/
theorem exists_moved_rank_ttc_le {σ : Allocation n} (hσ : σ ≠ 1) :
    ∃ i : Fin n, σ i ≠ i ∧ I.rank i (I.ttc i) ≤ I.rank i (I.preTradeTTC σ i) := by
  let S : Finset (Fin n) := Finset.univ.filter fun i => σ i ≠ i
  have hSne : S.Nonempty := Finset.ne_empty_iff_nonempty.1 fun hemp =>
    hσ (Equiv.ext fun i => Classical.byContradiction fun hne =>
      Finset.notMem_empty i (hemp ▸ Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩))
  have hnot := I.not_forall_rank_preTradeTTC_lt hSne fun i hi =>
    Classical.byContradiction fun hne => hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, hne⟩)
  push Not at hnot
  obtain ⟨i, hiS, hle⟩ := hnot
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
      (∃ i ∈ S, I.rank i (I.preTradeTTC σ i) < I.rank i (I.ttc i)) :=
  ⟨weakPreTradeInstance, {0, 2}, Equiv.swap 0 2, by decide, by decide, by decide, by decide⟩

end Cslib.Algorithms.Lean.HousingMarket
