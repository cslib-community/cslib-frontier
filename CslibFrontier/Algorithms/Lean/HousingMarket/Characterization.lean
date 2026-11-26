/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.HousingMarket.GroupIncentives
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Dynamics.PeriodicPts.Lemmas

/-!
# Ma's axiomatic characterization of top trading cycles and serial dictatorship

In a Shapley–Scarf housing market with strict complete preferences, Gale's top trading cycles
mechanism (`HousingMechanism.topTradingCycles`) satisfies individual rationality, Pareto
efficiency, and strategy-proofness. Jinpeng Ma ([Ma1994]; see also [Svensson1999]) proved the
converse: **top trading cycles is the unique direct mechanism satisfying all three axioms**
(`HousingMechanism.eq_topTradingCycles_iff`).

This module proves Ma's characterization via endowment-masking strong induction on
`∑ i, (I.rank i i).val` combined with Pareto elimination of fixed cycles, and also formalizes the
canonical house-allocation mechanism without endowment guarantees—**serial dictatorship**
(`Instance.serialDictatorship`, `HousingMechanism.serialDictatorship`)—proving that serial
dictatorship is Pareto efficient, non-bossy, and strongly group strategy-proof for all `n` (while
failing individual rationality for `n ≥ 2`, as verified alongside the remaining axiom-independence
witnesses in `CslibFrontierTests.HousingMarketCharacterization`).

## Main definitions

* `Instance.sdSteps`, `Instance.serialDictatorship`, `HousingMechanism.serialDictatorship`:
  priority-order (`0, 1, …, n - 1`) serial dictatorship allocation and mechanism.

## Main results

* `HousingMechanism.eq_topTradingCycles_of_ir_pe_sp`, `HousingMechanism.eq_topTradingCycles_iff`:
  Ma's characterization ([Ma1994]; [Svensson1999]): a housing mechanism is individually rational,
  Pareto efficient, and strategy-proof if and only if it equals `HousingMechanism.topTradingCycles`.
* `HousingMechanism.eq_topTradingCycles_iff_groupStrategyProof`: the same characterization with
  group strategy-proofness in place of strategy-proofness.
* `Instance.isParetoEfficient_serialDictatorship`,
  `HousingMechanism.isParetoEfficient_serialDictatorship`,
  `HousingMechanism.isNonBossy_serialDictatorship`,
  `HousingMechanism.isStrategyProof_serialDictatorship`,
  `HousingMechanism.isGroupStrategyProof_serialDictatorship`: serial dictatorship is Pareto
  efficient, non-bossy, strategy-proof, and strongly group strategy-proof for every `n`.

## References

* [Ma1994]
* [Svensson1999]
* [Papai2000]
* [SchummerVohra2007]
-/

public section

namespace Cslib.Algorithms.Lean.HousingMarket

open Function

/-! ### Part 1: Ma's (1994) axiomatic characterization of top trading cycles -/

namespace Instance

variable {n : ℕ}

private theorem topChoice_iterate_ne_self_of_ne {I : Instance n} {R : Finset (Fin n)}
    {a₀ : Fin n} (ha₀ : a₀ ∈ I.cycleAgents R) (hne : I.topChoice R a₀ ≠ a₀) :
    ∀ t : ℕ, I.topChoice R ((I.topChoice R)^[t] a₀) ≠ (I.topChoice R)^[t] a₀
  | 0 => hne
  | t + 1 => fun heq => by
    rw [iterate_succ_apply'] at heq
    have hprev := I.topChoice_injOn_cycleAgents R (I.iterate_mem_cycleAgents ha₀ (t + 1))
      (I.iterate_mem_cycleAgents ha₀ t) (by rwa [iterate_succ_apply'])
    exact topChoice_iterate_ne_self_of_ne ha₀ hne t (by rwa [iterate_succ_apply'] at hprev)

/-- If `ν` is Pareto efficient in `I` and every remaining agent in `R` either keeps its endowment
or weakly improves upon its TTC house, then `ν` agrees with `I.ttcRounds` on `R`. -/
private theorem eq_ttcRounds_of_pareto_and_or_endowment {I : Instance n} {ν : Allocation n}
    (hPE : I.IsParetoEfficient ν) {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k)
    (hR : ∀ x ∈ R, ν x ∈ R)
    (hor : ∀ j ∈ R, ν j = j ∨ I.rank j (ν j) ≤ I.rank j (I.ttcRounds k R j)) :
    ∀ x ∈ R, ν x = I.ttcRounds k R x := by
  induction k generalizing R with
  | zero => simp_all
  | succ k ih =>
    intro x hx
    have hRne : R.Nonempty := ⟨x, hx⟩
    have hk' : (R \ I.cycleAgents R).card ≤ k :=
      Nat.lt_succ_iff.mp ((I.card_sdiff_cycleAgents_lt hRne).trans_le hk)
    set C := I.cycleAgents R
    set f := I.topChoice R
    have hadich (a : Fin n) (haC : a ∈ C) : ν a = a ∨ ν a = f a := by
      have haR := I.cycleAgents_subset R haC
      rcases hor a haR with hfix | hle
      · exact Or.inl hfix
      · rw [I.ttcRounds_succ_of_mem haC] at hle
        exact Or.inr (I.rank_injective a (le_antisymm hle (I.rank_topChoice_le (hR a haR) a)))
    have hC_eq (a₀ : Fin n) (ha₀ : a₀ ∈ C) : ν a₀ = f a₀ := by
      by_contra hne₀
      have hf_ne₀ : f a₀ ≠ a₀ := fun hfa =>
        (hadich a₀ ha₀).elim (fun h => hne₀ (h.trans hfa.symm)) hne₀
      set O := I.cycleOf R a₀
      have hOC : O ⊆ C := I.cycleOf_subset_cycleAgents ha₀
      have hOclosed : ∀ b ∈ O, f b ∈ O := fun _ hb => I.topChoice_mem_cycleOf hRne ha₀ hb
      set p := minimalPeriod f a₀
      have hp_pos : 0 < p := minimalPeriod_pos_of_mem_periodicPts ((I.mem_cycleAgents hRne).1 ha₀)
      -- Backward induction around the `p`-cycle shows `ν b = b` on all of `O`.
      have hfix_back (m : ℕ) : m ≤ p → ν (f^[p - m] a₀) = f^[p - m] a₀ := by
        induction m with
        | zero =>
          intro _
          rw [Nat.sub_zero, iterate_minimalPeriod]
          exact (hadich a₀ ha₀).resolve_right hne₀
        | succ m ihm =>
          intro hmp
          set b := f^[p - (m + 1)] a₀
          have hfb_eq : f b = f^[p - m] a₀ := by
            rw [show p - m = (p - (m + 1)) + 1 by omega, iterate_succ_apply']
          have hν_fb : ν (f b) = f b := hfb_eq ▸ ihm (by omega)
          exact (hadich b (I.iterate_mem_cycleAgents ha₀ _)).resolve_right fun htop =>
            topChoice_iterate_ne_self_of_ne ha₀ hf_ne₀ (p - (m + 1))
              (ν.injective (htop.trans hν_fb.symm)).symm
      have hO_fix : ∀ b ∈ O, ν b = b ∧ f b ≠ b := by
        rintro b hb
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hb
        refine ⟨?_, topChoice_iterate_ne_self_of_ne ha₀ hf_ne₀ t⟩
        change ν (f^[t] a₀) = f^[t] a₀
        rw [← Function.iterate_mod_minimalPeriod_eq (f := f) (x := a₀) (n := t)]
        exact Nat.sub_sub_self (Nat.mod_lt t hp_pos).le ▸ hfix_back (p - t % p) (Nat.sub_le p _)
      -- Trading along `O` strictly improves all of `O` without hurting anyone outside `O`.
      let ν' : Allocation n := ν.trans (I.cyclePerm hOC hOclosed)
      have hν'_mem (y : Fin n) (hy : y ∈ O) : ν' y = f y := by
        simp only [ν', Equiv.trans_apply, (hO_fix y hy).1]
        exact I.cyclePerm_apply_of_mem hOC hOclosed hy
      have ha₀O : a₀ ∈ O := I.mem_cycleOf_self R a₀
      refine hPE ⟨ν', fun y => ?_, a₀, ?_⟩
      · by_cases hyO : y ∈ O
        · rw [hν'_mem y hyO, (hO_fix y hyO).1]
          exact I.rank_topChoice_le (I.cycleAgents_subset R (hOC hyO)) y
        · have hnotO : ν y ∉ O := fun hm => hyO (ν.injective (hO_fix (ν y) hm).1 ▸ hm)
          rw [Equiv.trans_apply, I.cyclePerm_apply_of_notMem hOC hOclosed hnotO]
      · rw [hν'_mem a₀ ha₀O, (hO_fix a₀ ha₀O).1]
        exact lt_of_le_of_ne (I.rank_topChoice_le (I.cycleAgents_subset R ha₀) a₀)
          fun hr => (hO_fix a₀ ha₀O).2 (I.rank_injective a₀ hr)
    by_cases hxC : x ∈ C
    · rw [hC_eq x hxC, I.ttcRounds_succ_of_mem hxC]
    rw [I.ttcRounds_succ_of_notMem hxC]
    have hmaps : ∀ b ∈ C, ν b ∈ C := fun b hb => hC_eq b hb ▸ I.topChoice_mem_cycleAgents hb
    refine ih hk' (fun a ha => ?_) (fun j hj => ?_) x (Finset.mem_sdiff.2 ⟨hx, hxC⟩)
    · obtain ⟨haR, haC⟩ := Finset.mem_sdiff.1 ha
      exact Finset.mem_sdiff.2 ⟨hR a haR, fun hmem => haC (mem_of_apply_mem ν hmaps hmem)⟩
    · obtain ⟨hjR, hjC⟩ := Finset.mem_sdiff.1 hj
      exact (hor j hjR).imp_right fun hle => by rwa [I.ttcRounds_succ_of_notMem hjC] at hle

private theorem swap_le_iff_of_lt {r k₁ r₀ s : Fin n}
    (hrk : r < k₁) (hkr : k₁ < r₀) :
    Equiv.swap k₁ r₀ s ≤ r ↔ s ≤ r := by
  by_cases hsk : s = k₁
  · subst hsk
    rw [Equiv.swap_apply_left]
    exact iff_of_false (not_le.mpr (hrk.trans hkr)) (not_le.mpr hrk)
  · by_cases hsr : s = r₀
    · subst hsr
      rw [Equiv.swap_apply_right]
      exact iff_of_false (not_le.mpr hrk) (not_le.mpr (hrk.trans hkr))
    · rw [Equiv.swap_apply_of_ne_of_ne hsk hsr]

private theorem swap_eq_self_of_le {r k₁ r₀ s : Fin n}
    (hrk : r < k₁) (hkr : k₁ < r₀) (hs : s ≤ r) :
    Equiv.swap k₁ r₀ s = s :=
  Equiv.swap_apply_of_ne_of_ne (ne_of_lt (lt_of_le_of_lt hs hrk))
    (ne_of_lt (lt_of_le_of_lt hs (hrk.trans hkr)))

end Instance

namespace HousingMechanism

variable {n : ℕ}

/-- **Ma's characterization theorem (uniqueness direction)** ([Ma1994]; [Svensson1999]): every
individually rational, Pareto-efficient, and strategy-proof direct housing mechanism equals
`HousingMechanism.topTradingCycles`. -/
theorem eq_topTradingCycles_of_ir_pe_sp {M : HousingMechanism n}
    (hIR : M.IsIndividuallyRational) (hPE : M.IsParetoEfficient)
    (hSP : M.IsStrategyProof) : M = topTradingCycles := by
  suffices hmain : ∀ (m : ℕ) (I : Instance n),
      (∑ j : Fin n, (I.rank j j).val) = m → M I = I.ttc from funext fun I => hmain _ I rfl
  intro m
  refine Nat.strong_induction_on m fun m ih I hm => Equiv.ext fun x => ?_
  rw [I.ttc_apply]
  refine Instance.eq_ttcRounds_of_pareto_and_or_endowment (hPE I) (k := n) (by simp)
    (fun _ _ => Finset.mem_univ _) (fun i _ => ?_) x (Finset.mem_univ x)
  rw [← I.ttc_apply]
  set r := I.rank i (I.ttc i)
  set r₀ := I.rank i i
  by_cases hgap : r.val + 1 < r₀.val
  · -- Mask `i`'s endowment directly below `I.ttc i` by swapping ranks `r + 1` and `r₀`.
    let k₁ : Fin n := ⟨r.val + 1, by have := r₀.isLt; omega⟩
    have hrk : r < k₁ := Nat.lt_succ_self r.val
    have hkr : k₁ < r₀ := hgap
    let π : Equiv.Perm (Fin n) := (Equiv.swap k₁ r₀).trans (I.pref i)
    set I' := I.updatePref i π
    have hI'_rank (h : Fin n) : I'.rank i h = Equiv.swap k₁ r₀ (I.rank i h) := by
      simp [I', π, Instance.rank]
    have hI'_ii : I'.rank i i = k₁ := by
      rw [hI'_rank, show I.rank i i = r₀ from rfl, Equiv.swap_apply_right]
    have hI'_ttc_rank : I'.rank i (I.ttc i) = r :=
      (hI'_rank _).trans (Instance.swap_eq_self_of_le hrk hkr le_rfl)
    -- `I.ttc` remains in the strict core of `I'`, so `I'.ttc = I.ttc`.
    have hI'_strictCore : I'.InStrictCore I.ttc := by
      rintro S ⟨ν, hS, hle, j₀, hj₀, hlt⟩
      have hle' (j : Fin n) (hj : j ∈ S) : I.rank j (ν j) ≤ I.rank j (I.ttc j) := by
        by_cases hji : j = i
        · subst hji
          have h1 := hle j hj
          rw [hI'_ttc_rank, hI'_rank] at h1
          exact (Instance.swap_le_iff_of_lt hrk hkr).1 h1
        · simpa only [I', I.updatePref_rank_of_ne π hji] using hle j hj
      exact I.inStrictCore_ttc S ⟨ν, hS, hle', j₀, hj₀, lt_of_le_of_ne (hle' j₀ hj₀)
        fun hr => hlt.ne (congrArg (I'.rank j₀) (I.rank_injective j₀ hr))⟩
    -- The endowment-rank sum strictly drops, so the induction hypothesis gives `M I' = I.ttc`.
    have hsum_lt : (∑ j : Fin n, (I'.rank j j).val) < m := by
      rw [← hm]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, hI'_ii ▸ hkr⟩
      rcases eq_or_ne j i with rfl | hji
      · exact hI'_ii ▸ hkr.le
      · rw [I.updatePref_rank_of_ne π hji]
    have hMI' : M I' = I.ttc := (ih _ hsum_lt I' rfl).trans hI'_strictCore.eq_ttc.symm
    -- Strategy-proofness between `I` and `I'` forces `M I i = I.ttc i`.
    have hsp_fwd : I.rank i (M I i) ≤ r := by
      simpa only [I', hMI'] using hSP I i π
    have hsp_bwd : r ≤ I.rank i (M I i) := by
      have hback : I'.updatePref i (I.pref i) = I := by simp [I']
      simpa only [hback, hMI', hI'_ttc_rank, hI'_rank,
        Instance.swap_eq_self_of_le hrk hkr hsp_fwd] using hSP I' i (I.pref i)
    exact Or.inr (le_antisymm hsp_fwd hsp_bwd).le
  · -- No house lies strictly between `I.ttc i` and `i`, so `hIR` suffices directly.
    have hir_i : (I.rank i (M I i)).val ≤ r₀.val := hIR I i
    by_cases heq : (I.rank i (M I i)).val = r₀.val
    · exact Or.inl (I.rank_injective i (Fin.ext heq))
    · exact Or.inr (show (I.rank i (M I i)).val ≤ r.val by omega)

/-- **Ma's characterization of top trading cycles** ([Ma1994]; [Svensson1999]): a direct housing
mechanism satisfies individual rationality, Pareto efficiency, and strategy-proofness if and only
if it is Gale's top trading cycles mechanism. -/
theorem eq_topTradingCycles_iff {M : HousingMechanism n} :
    (M.IsIndividuallyRational ∧ M.IsParetoEfficient ∧ M.IsStrategyProof) ↔
      M = topTradingCycles :=
  ⟨fun ⟨hIR, hPE, hSP⟩ => eq_topTradingCycles_of_ir_pe_sp hIR hPE hSP,
    fun h => h.symm ▸ ⟨isIndividuallyRational_topTradingCycles,
      isParetoEfficient_topTradingCycles, isStrategyProof_topTradingCycles⟩⟩

/-- **Characterization of top trading cycles via group strategy-proofness** ([Bird1984]; [Ma1994];
[Svensson1999]): a direct housing mechanism is individually rational, Pareto efficient, and
strongly group strategy-proof if and only if it equals `HousingMechanism.topTradingCycles`. -/
theorem eq_topTradingCycles_iff_groupStrategyProof {M : HousingMechanism n} :
    (M.IsIndividuallyRational ∧ M.IsParetoEfficient ∧ M.IsGroupStrategyProof) ↔
      M = topTradingCycles :=
  ⟨fun ⟨hIR, hPE, hGSP⟩ => eq_topTradingCycles_of_ir_pe_sp hIR hPE hGSP.isStrategyProof,
    fun h => h.symm ▸ ⟨isIndividuallyRational_topTradingCycles,
      isParetoEfficient_topTradingCycles, isGroupStrategyProof_topTradingCycles⟩⟩

end HousingMechanism

/-! ### Part 2: Priority-order serial dictatorship -/

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- `k` remaining steps of priority-order picking on house set `R`: when `k < n`, agent
`⟨n - 1 - k, _⟩` receives `I.topChoice R ⟨n - 1 - k, _⟩`, and later agents pick recursively from
the remaining houses. -/
@[expose] def sdSteps : ℕ → Finset (Fin n) → Fin n → Fin n
  | 0, _, i => i
  | k + 1, R, i =>
    if hk : k < n then
      let a : Fin n := ⟨n - 1 - k, by omega⟩
      let h := I.topChoice R a
      if i = a then h else sdSteps k (R \ {h}) i
    else
      i

variable {I}

theorem sdSteps_succ_of_eq {k : ℕ} (hk : k < n) (R : Finset (Fin n)) :
    I.sdSteps (k + 1) R ⟨n - 1 - k, by omega⟩ = I.topChoice R ⟨n - 1 - k, by omega⟩ := by
  rw [sdSteps, dite_eq_left hk, ite_eq_left rfl]

theorem sdSteps_succ_of_ne {k : ℕ} (hk : k < n) (R : Finset (Fin n)) {i : Fin n}
    (hia : i ≠ ⟨n - 1 - k, by omega⟩) :
    I.sdSteps (k + 1) R i =
      I.sdSteps k (R \ {I.topChoice R ⟨n - 1 - k, by omega⟩}) i := by
  rw [sdSteps, dite_eq_left hk, ite_eq_right hia]

private theorem card_sdiff_singleton_ge {k : ℕ} {R : Finset (Fin n)} (hcard : k + 1 ≤ R.card)
    {h : Fin n} (hh : h ∈ R) : k ≤ (R \ {h}).card := by
  rw [Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.2 hh), Finset.card_singleton]
  omega

private theorem val_ge_of_ne {k : ℕ} (hk : k < n) {i : Fin n} (hi : n - (k + 1) ≤ i.val)
    (hia : i ≠ ⟨n - 1 - k, by omega⟩) : n - k ≤ i.val := by
  have : i.val ≠ n - 1 - k := fun hv => hia (Fin.ext hv)
  omega

theorem sdSteps_mem {k : ℕ} {R : Finset (Fin n)} (hk_le : k ≤ n) (hcard : k ≤ R.card) {i : Fin n}
    (hi : n - k ≤ i.val) : I.sdSteps k R i ∈ R := by
  induction k generalizing R with
  | zero => exact absurd i.isLt (by omega)
  | succ k ih =>
    have hk : k < n := by omega
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    have hh : I.topChoice R a ∈ R := I.topChoice_mem (Finset.card_pos.1 (by omega)) a
    by_cases hia : i = a
    · rwa [hia, I.sdSteps_succ_of_eq hk R]
    · rw [I.sdSteps_succ_of_ne hk R hia]
      exact Finset.sdiff_subset
        (ih (by omega) (card_sdiff_singleton_ge hcard hh) (val_ge_of_ne hk hi hia))

theorem sdSteps_injOn {k : ℕ} {R : Finset (Fin n)} (hk_le : k ≤ n) (hcard : k ≤ R.card) :
    Set.InjOn (I.sdSteps k R) {i : Fin n | n - k ≤ i.val} := by
  induction k generalizing R with
  | zero => exact fun x (hx : n - 0 ≤ x.val) => absurd x.isLt (by omega)
  | succ k ih =>
    intro x hx y hy hxy
    have hk : k < n := by omega
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    let h := I.topChoice R a
    have hcard' := card_sdiff_singleton_ge hcard (I.topChoice_mem (Finset.card_pos.1 (by omega)) a)
    have hdisj : ∀ {u v : Fin n}, n - (k + 1) ≤ v.val → u = a → v ≠ a →
        I.sdSteps (k + 1) R u ≠ I.sdSteps (k + 1) R v := fun hv hua hva huv => by
      rw [hua, I.sdSteps_succ_of_eq hk R, I.sdSteps_succ_of_ne hk R hva] at huv
      exact (Finset.mem_sdiff.1 (I.sdSteps_mem (by omega) hcard' (val_ge_of_ne hk hv hva))).2
        (huv ▸ Finset.mem_singleton_self h)
    by_cases hxa : x = a <;> by_cases hya : y = a
    · exact hxa.trans hya.symm
    · exact absurd hxy (hdisj hy hxa hya)
    · exact absurd hxy.symm (hdisj hx hya hxa)
    · rw [I.sdSteps_succ_of_ne hk R hxa, I.sdSteps_succ_of_ne hk R hya] at hxy
      exact ih (by omega) hcard' (val_ge_of_ne hk hx hxa) (val_ge_of_ne hk hy hya) hxy

variable (I)

/-- Priority-order (`0, 1, …, n - 1`) serial dictatorship allocation. -/
@[expose] def serialDictatorship : Allocation n :=
  StableMatching.permOfInjective (I.sdSteps n Finset.univ) fun x y hxy =>
    I.sdSteps_injOn le_rfl (by simp) (by simp) (by simp) hxy

@[simp] theorem serialDictatorship_apply (i : Fin n) :
    I.serialDictatorship i = I.sdSteps n Finset.univ i := rfl

private theorem eq_sdSteps_of_rank_le {k : ℕ} {R : Finset (Fin n)} (hk_le : k ≤ n)
    (hcard : k ≤ R.card) {ν : Allocation n}
    (hR : ∀ i : Fin n, n - k ≤ i.val → ν i ∈ R)
    (hle : ∀ i : Fin n, n - k ≤ i.val → I.rank i (ν i) ≤ I.rank i (I.sdSteps k R i)) :
    ∀ i : Fin n, n - k ≤ i.val → ν i = I.sdSteps k R i := by
  induction k generalizing R with
  | zero => exact fun i hi => absurd i.isLt (by omega)
  | succ k ih =>
    intro i hi
    have hk : k < n := by omega
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    have hh : I.topChoice R a ∈ R := I.topChoice_mem (Finset.card_pos.1 (by omega)) a
    have ha_ge : n - (k + 1) ≤ a.val := by dsimp [a]; omega
    have ha_eq : ν a = I.topChoice R a := by
      have h1 := hle a ha_ge
      rw [I.sdSteps_succ_of_eq hk R] at h1
      exact I.rank_injective a (le_antisymm h1 (I.rank_topChoice_le (hR a ha_ge) a))
    by_cases hia : i = a
    · rw [hia, I.sdSteps_succ_of_eq hk R, ha_eq]
    · rw [I.sdSteps_succ_of_ne hk R hia]
      have hne_a (j : Fin n) (hj : n - k ≤ j.val) : j ≠ a :=
        fun h0 => absurd (congrArg Fin.val h0) (by dsimp [a]; omega)
      refine ih (by omega) (card_sdiff_singleton_ge hcard hh) (fun j hj => ?_) (fun j hj => ?_)
        i (val_ge_of_ne hk hi hia)
      · exact Finset.mem_sdiff.2 ⟨hR j (by omega), fun hm =>
          hne_a j hj (ν.injective ((Finset.mem_singleton.1 hm).trans ha_eq.symm))⟩
      · have h1 := hle j (by omega)
        rwa [I.sdSteps_succ_of_ne hk R (hne_a j hj)] at h1

/-- Serial dictatorship always produces a Pareto-efficient allocation. -/
theorem isParetoEfficient_serialDictatorship : I.IsParetoEfficient I.serialDictatorship := by
  rintro ⟨ν, hle, i, hlt⟩
  have heq := I.eq_sdSteps_of_rank_le (k := n) (R := Finset.univ) le_rfl (by simp)
    (fun _ _ => Finset.mem_univ _) (fun j _ => hle j) i (by simp)
  rw [serialDictatorship_apply, ← heq] at hlt
  exact lt_irrefl _ hlt

private theorem rank_sdSteps_le_updatePref {k : ℕ} {R : Finset (Fin n)} (hk_le : k ≤ n)
    (hcard : k ≤ R.card) (i : Fin n) (hi : n - k ≤ i.val) (π : Equiv.Perm (Fin n)) :
    I.rank i (I.sdSteps k R i) ≤ I.rank i ((I.updatePref i π).sdSteps k R i) := by
  induction k generalizing R with
  | zero => exact absurd i.isLt (by omega)
  | succ k ih =>
    have hk : k < n := by omega
    let J := I.updatePref i π
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    by_cases hia : i = a
    · rw [show I.sdSteps (k + 1) R i = I.topChoice R i from hia ▸ I.sdSteps_succ_of_eq hk R]
      exact I.rank_topChoice_le (J.sdSteps_mem hk_le hcard hi) i
    · rw [I.sdSteps_succ_of_ne hk R hia, J.sdSteps_succ_of_ne hk R hia,
        I.updatePref_topChoice_of_ne π (Ne.symm hia) R]
      exact ih (by omega)
        (card_sdiff_singleton_ge hcard (I.topChoice_mem (Finset.card_pos.1 (by omega)) a))
        (val_ge_of_ne hk hi hia)

private theorem sdSteps_succ_congr {J : Instance n} {k : ℕ} (hk : k < n) (R : Finset (Fin n))
    (htop : J.topChoice R ⟨n - 1 - k, by omega⟩ = I.topChoice R ⟨n - 1 - k, by omega⟩)
    {j : Fin n}
    (hrec : j ≠ ⟨n - 1 - k, by omega⟩ →
      J.sdSteps k (R \ {I.topChoice R ⟨n - 1 - k, by omega⟩}) j =
        I.sdSteps k (R \ {I.topChoice R ⟨n - 1 - k, by omega⟩}) j) :
    J.sdSteps (k + 1) R j = I.sdSteps (k + 1) R j := by
  by_cases hja : j = ⟨n - 1 - k, by omega⟩
  · rw [hja, J.sdSteps_succ_of_eq hk R, I.sdSteps_succ_of_eq hk R, htop]
  · rw [J.sdSteps_succ_of_ne hk R hja, I.sdSteps_succ_of_ne hk R hja, htop, hrec hja]

private theorem sdSteps_eq_of_val_lt {k : ℕ} (hk_le : k ≤ n) (R : Finset (Fin n))
    (i : Fin n) (hi : i.val < n - k) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    (I.updatePref i π).sdSteps k R j = I.sdSteps k R j := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have hk : k < n := by omega
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    have hai : a ≠ i := fun h0 => absurd (congrArg Fin.val h0) (by dsimp [a]; omega)
    exact I.sdSteps_succ_congr hk R (I.updatePref_topChoice_of_ne π hai R) fun _ =>
      ih (by omega) _ (by omega)

private theorem sdSteps_updatePref_eq_of_apply_eq {k : ℕ} (hk_le : k ≤ n) (R : Finset (Fin n))
    (i : Fin n) (π : Equiv.Perm (Fin n))
    (heq_i : (I.updatePref i π).sdSteps k R i = I.sdSteps k R i) (j : Fin n) :
    (I.updatePref i π).sdSteps k R j = I.sdSteps k R j := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have hk : k < n := by omega
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    by_cases hia : i = a
    · have htop : (I.updatePref i π).topChoice R a = I.topChoice R a := by
        simpa only [hia, a, sdSteps_succ_of_eq hk R] using heq_i
      have hi_lt : i.val < n - k := by have : i.val = n - 1 - k := congrArg Fin.val hia; omega
      exact I.sdSteps_succ_congr hk R htop fun _ => I.sdSteps_eq_of_val_lt hk.le _ i hi_lt π j
    · have htop := I.updatePref_topChoice_of_ne π (Ne.symm hia) R
      rw [(I.updatePref i π).sdSteps_succ_of_ne hk R hia, I.sdSteps_succ_of_ne hk R hia,
        htop] at heq_i
      exact I.sdSteps_succ_congr hk R htop fun _ => ih (by omega) _ heq_i

end Instance

namespace HousingMechanism

variable {n : ℕ}

/-- Priority-order (`0, 1, …, n - 1`) serial dictatorship direct housing mechanism. -/
@[expose] def serialDictatorship : HousingMechanism n := fun I => I.serialDictatorship

theorem isParetoEfficient_serialDictatorship :
    (serialDictatorship (n := n)).IsParetoEfficient :=
  fun I => I.isParetoEfficient_serialDictatorship

theorem isStrategyProof_serialDictatorship :
    (serialDictatorship (n := n)).IsStrategyProof :=
  fun I i π => I.rank_sdSteps_le_updatePref le_rfl (by simp) i (by simp) π

theorem isNonBossy_serialDictatorship :
    (serialDictatorship (n := n)).IsNonBossy :=
  fun I i π heq => Equiv.ext (I.sdSteps_updatePref_eq_of_apply_eq le_rfl Finset.univ i π heq)

/-- Serial dictatorship is strongly group strategy-proof for every `n` ([Svensson1999];
[Papai2000]). -/
theorem isGroupStrategyProof_serialDictatorship :
    (serialDictatorship (n := n)).IsGroupStrategyProof :=
  isGroupStrategyProof_iff.2 ⟨isStrategyProof_serialDictatorship, isNonBossy_serialDictatorship⟩

end HousingMechanism

end Cslib.Algorithms.Lean.HousingMarket
