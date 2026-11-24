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
    have hprev := I.topChoice_injOn_cycleAgents R
      (I.iterate_mem_cycleAgents ha₀ (t + 1)) (I.iterate_mem_cycleAgents ha₀ t)
      (by rwa [iterate_succ_apply'])
    rw [iterate_succ_apply'] at hprev
    exact topChoice_iterate_ne_self_of_ne ha₀ hne t hprev

/-- If `ν` is Pareto efficient in `I` and every remaining agent in `R` either keeps its endowment
or weakly improves upon its TTC house, then `ν` agrees with `I.ttcRounds` on `R`. -/
private theorem eq_ttcRounds_of_pareto_and_or_endowment {I : Instance n} {ν : Allocation n}
    (hPE : I.IsParetoEfficient ν) {k : ℕ} {R : Finset (Fin n)} (hk : R.card ≤ k)
    (hR : ∀ x ∈ R, ν x ∈ R)
    (hor : ∀ j ∈ R, ν j = j ∨ I.rank j (ν j) ≤ I.rank j (I.ttcRounds k R j)) :
    ∀ x ∈ R, ν x = I.ttcRounds k R x := by
  induction k generalizing R with
  | zero =>
    intro x hx
    simp_all
  | succ k ih =>
    intro x hx
    have hRne : R.Nonempty := ⟨x, hx⟩
    have hk' : (R \ I.cycleAgents R).card ≤ k := by
      have := I.card_sdiff_cycleAgents_lt hRne
      omega
    set C := I.cycleAgents R
    set f := I.topChoice R
    have hadich : ∀ a ∈ C, ν a = a ∨ ν a = f a := by
      intro a haC
      have haR : a ∈ R := I.cycleAgents_subset R haC
      rcases hor a haR with hfix | hle
      · exact Or.inl hfix
      · rw [I.ttcRounds_succ_of_mem haC] at hle
        exact Or.inr (I.rank_injective a (le_antisymm hle (I.rank_topChoice_le (hR a haR) a)))
    have hC_eq : ∀ a₀ ∈ C, ν a₀ = f a₀ := by
      intro a₀ ha₀
      by_contra hne₀
      have hf_ne₀ : f a₀ ≠ a₀ := by
        intro hfa
        rcases hadich a₀ ha₀ with hfix | htop
        · exact hne₀ (hfix.trans hfa.symm)
        · exact hne₀ htop
      set O : Finset (Fin n) := I.cycleOf R a₀
      have hOC : O ⊆ C := I.cycleOf_subset_cycleAgents ha₀
      have hOclosed : ∀ b ∈ O, f b ∈ O := fun _ hb => I.topChoice_mem_cycleOf hRne ha₀ hb
      have hper : a₀ ∈ periodicPts f := (I.mem_cycleAgents hRne).1 ha₀
      set p := minimalPeriod f a₀
      have hp_pos : 0 < p := minimalPeriod_pos_of_mem_periodicPts hper
      -- Backward induction around the `p`-cycle shows `ν b = b` on all of `O`.
      have hfix_back : ∀ m ≤ p, ν (f^[p - m] a₀) = f^[p - m] a₀ := by
        intro m
        induction m with
        | zero =>
          intro _
          have hfp : f^[p] a₀ = a₀ := iterate_minimalPeriod
          rw [Nat.sub_zero, hfp]
          exact (hadich a₀ ha₀).resolve_right hne₀
        | succ m ihm =>
          intro hmp
          set b := f^[p - (m + 1)] a₀
          have hbC : b ∈ C := I.iterate_mem_cycleAgents ha₀ (p - (m + 1))
          have hfb_eq : f b = f^[p - m] a₀ := by
            have hstep : p - m = (p - (m + 1)) + 1 := by omega
            rw [hstep, iterate_succ_apply']
          have hν_fb : ν (f b) = f b := by
            rw [hfb_eq]
            exact ihm (by omega)
          rcases hadich b hbC with hfix | htop
          · exact hfix
          · exfalso
            have hb_eq_fb : b = f b := ν.injective (htop.trans hν_fb.symm)
            exact topChoice_iterate_ne_self_of_ne ha₀ hf_ne₀ (p - (m + 1)) hb_eq_fb.symm
      have hO_fix : ∀ b ∈ O, ν b = b ∧ f b ≠ b := by
        rintro b hb
        obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hb
        refine ⟨?_, topChoice_iterate_ne_self_of_ne ha₀ hf_ne₀ t⟩
        change ν (f^[t] a₀) = f^[t] a₀
        rw [← Function.iterate_mod_minimalPeriod_eq (f := f) (x := a₀) (n := t)]
        have hrem : t % p < p := Nat.mod_lt t hp_pos
        have hsub : t % p = p - (p - t % p) := by omega
        rw [hsub]
        exact hfix_back (p - t % p) (by omega)
      -- Trading along `O` strictly improves all of `O` without hurting anyone outside `O`.
      let ν' : Allocation n := ν.trans (I.cyclePerm hOC hOclosed)
      have ha₀O : a₀ ∈ O := I.mem_cycleOf_self R a₀
      refine hPE ⟨ν', fun y => ?_, a₀, ?_⟩
      · by_cases hyO : y ∈ O
        · obtain ⟨hνy, hfy⟩ := hO_fix y hyO
          have hyR : y ∈ R := I.cycleAgents_subset R (hOC hyO)
          have hν'y : ν' y = f y := by
            simp only [ν', Equiv.trans_apply, hνy]
            exact I.cyclePerm_apply_of_mem hOC hOclosed hyO
          rw [hν'y, hνy]
          exact I.rank_topChoice_le hyR y
        · have hνy_notO : ν y ∉ O := fun hmem =>
            hyO (ν.injective ((hO_fix (ν y) hmem).1) ▸ hmem)
          have hν'y : ν' y = ν y := by
            simp only [ν', Equiv.trans_apply]
            exact I.cyclePerm_apply_of_notMem hOC hOclosed hνy_notO
          rw [hν'y]
      · obtain ⟨hνa, hfa⟩ := hO_fix a₀ ha₀O
        have ha₀R : a₀ ∈ R := I.cycleAgents_subset R ha₀
        have hν'a : ν' a₀ = f a₀ := by
          simp only [ν', Equiv.trans_apply, hνa]
          exact I.cyclePerm_apply_of_mem hOC hOclosed ha₀O
        rw [hν'a, hνa]
        exact lt_of_le_of_ne (I.rank_topChoice_le ha₀R a₀)
          fun hr => hfa (I.rank_injective a₀ hr)
    by_cases hxC : x ∈ C
    · rw [hC_eq x hxC, I.ttcRounds_succ_of_mem hxC]
    rw [I.ttcRounds_succ_of_notMem hxC]
    have hmaps : ∀ b ∈ C, ν b ∈ C := fun b hb => hC_eq b hb ▸ I.topChoice_mem_cycleAgents hb
    refine ih hk' (fun a ha => ?_) (fun j hj => ?_) x (Finset.mem_sdiff.2 ⟨hx, hxC⟩)
    · obtain ⟨haR, haC⟩ := Finset.mem_sdiff.1 ha
      exact Finset.mem_sdiff.2 ⟨hR a haR, fun hmem => haC (mem_of_apply_mem ν hmaps hmem)⟩
    · obtain ⟨hjR, hjC⟩ := Finset.mem_sdiff.1 hj
      rcases hor j hjR with hfix | hle
      · exact Or.inl hfix
      · rw [I.ttcRounds_succ_of_notMem hjC] at hle
        exact Or.inr hle

private theorem swap_le_iff_of_lt {r k₁ r₀ s : Fin n}
    (hrk : r < k₁) (hkr : k₁ < r₀) :
    Equiv.swap k₁ r₀ s ≤ r ↔ s ≤ r := by
  by_cases hsk : s = k₁
  · subst hsk
    rw [Equiv.swap_apply_left]
    exact ⟨fun h => absurd (hrk.trans (hkr.trans_le h)) (lt_irrefl _),
      fun h => absurd (hrk.trans_le h) (lt_irrefl _)⟩
  · by_cases hsr : s = r₀
    · subst hsr
      rw [Equiv.swap_apply_right]
      exact ⟨fun h => absurd (hrk.trans_le h) (lt_irrefl _),
        fun h => absurd ((hrk.trans hkr).trans_le h) (lt_irrefl _)⟩
    · rw [Equiv.swap_apply_of_ne_of_ne hsk hsr]

private theorem swap_eq_self_of_le {r k₁ r₀ s : Fin n}
    (hrk : r < k₁) (hkr : k₁ < r₀) (hs : s ≤ r) :
    Equiv.swap k₁ r₀ s = s := by
  have hsk : s ≠ k₁ := ne_of_lt (lt_of_le_of_lt hs hrk)
  have hsr : s ≠ r₀ := ne_of_lt (lt_of_le_of_lt hs (hrk.trans hkr))
  exact Equiv.swap_apply_of_ne_of_ne hsk hsr

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
      (∑ j : Fin n, (I.rank j j).val) = m → M I = I.ttc by
    funext I
    exact hmain _ I rfl
  intro m
  refine Nat.strong_induction_on m fun m ih => ?_
  intro I hm
  refine Equiv.ext fun x => ?_
  rw [I.ttc_apply]
  refine Instance.eq_ttcRounds_of_pareto_and_or_endowment (hPE I) (k := n) (by simp)
    (fun _ _ => Finset.mem_univ _) (fun i _ => ?_) x (Finset.mem_univ x)
  rw [← I.ttc_apply]
  set r := I.rank i (I.ttc i)
  set r₀ := I.rank i i
  by_cases hgap : r.val + 1 < r₀.val
  · -- Mask `i`'s endowment directly below `I.ttc i` by swapping ranks `r + 1` and `r₀`.
    let k₁ : Fin n := ⟨r.val + 1, by have := r₀.isLt; omega⟩
    have hrk : r < k₁ := by
      change r.val < r.val + 1
      omega
    have hkr : k₁ < r₀ := hgap
    let π : Equiv.Perm (Fin n) := (Equiv.swap k₁ r₀).trans (I.pref i)
    set I' := I.updatePref i π
    have hI'_rank : ∀ h : Fin n, I'.rank i h = Equiv.swap k₁ r₀ (I.rank i h) := fun h => by
      rw [I.updatePref_rank_self]
      simp [π, Instance.rank]
    have hI'_ii : I'.rank i i = k₁ := by
      rw [hI'_rank, show I.rank i i = r₀ from rfl, Equiv.swap_apply_right]
    have hI'_ttc_rank : I'.rank i (I.ttc i) = r := by
      rw [hI'_rank]
      exact Instance.swap_eq_self_of_le hrk hkr le_rfl
    -- `I.ttc` remains in the strict core of `I'`, so `I'.ttc = I.ttc`.
    have hI'_strictCore : I'.InStrictCore I.ttc := by
      rintro S ⟨ν, hS, hle, j₀, hj₀, hlt⟩
      refine I.inStrictCore_ttc S ⟨ν, hS, fun j hj => ?_, j₀, hj₀, ?_⟩
      · by_cases hji : j = i
        · subst hji
          have h1 := hle j hj
          rw [hI'_ttc_rank, hI'_rank] at h1
          exact (Instance.swap_le_iff_of_lt hrk hkr).1 h1
        · simpa only [I', I.updatePref_rank_of_ne π hji] using hle j hj
      · by_cases hji : j₀ = i
        · subst hji
          have h1 := hlt
          rw [hI'_ttc_rank, hI'_rank] at h1
          have hle_orig : I.rank j₀ (ν j₀) ≤ r :=
            (Instance.swap_le_iff_of_lt hrk hkr).1 h1.le
          rwa [Instance.swap_eq_self_of_le hrk hkr hle_orig] at h1
        · simpa only [I', I.updatePref_rank_of_ne π hji] using hlt
    have hI'_ttc : I'.ttc = I.ttc := hI'_strictCore.eq_ttc.symm
    -- The endowment-rank sum strictly drops, so the induction hypothesis gives `M I' = I.ttc`.
    have hsum_lt : (∑ j : Fin n, (I'.rank j j).val) < m := by
      rw [← hm]
      refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
      · by_cases hji : j = i
        · subst hji
          rw [hI'_ii]
          exact hkr.le
        · rw [I.updatePref_rank_of_ne π hji]
      · rw [hI'_ii]
        exact hkr
    have hMI' : M I' = I.ttc := (ih _ hsum_lt I' rfl).trans hI'_ttc
    -- Strategy-proofness between `I` and `I'` forces `M I i = I.ttc i`.
    have hsp_fwd : I.rank i (M I i) ≤ r := by
      have h1 := hSP I i π
      rwa [show I.updatePref i π = I' from rfl, hMI'] at h1
    have hsp_bwd : r ≤ I.rank i (M I i) := by
      have h1 := hSP I' i (I.pref i)
      have hback : I'.updatePref i (I.pref i) = I := by
        simp [I']
      rw [hback, hMI', hI'_ttc_rank, hI'_rank,
        Instance.swap_eq_self_of_le hrk hkr hsp_fwd] at h1
      exact h1
    exact Or.inr (le_antisymm hsp_fwd hsp_bwd).le
  · -- No house lies strictly between `I.ttc i` and `i`, so `hIR` suffices directly.
    have hir_i : (I.rank i (M I i)).val ≤ r₀.val := hIR I i
    by_cases heq : (I.rank i (M I i)).val = r₀.val
    · left
      exact I.rank_injective i (Fin.ext heq)
    · right
      change (I.rank i (M I i)).val ≤ r.val
      omega

/-- **Ma's characterization of top trading cycles** ([Ma1994]; [Svensson1999]): a direct housing
mechanism satisfies individual rationality, Pareto efficiency, and strategy-proofness if and only
if it is Gale's top trading cycles mechanism. -/
theorem eq_topTradingCycles_iff {M : HousingMechanism n} :
    (M.IsIndividuallyRational ∧ M.IsParetoEfficient ∧ M.IsStrategyProof) ↔
      M = topTradingCycles := by
  constructor
  · rintro ⟨hIR, hPE, hSP⟩
    exact eq_topTradingCycles_of_ir_pe_sp hIR hPE hSP
  · rintro rfl
    exact ⟨isIndividuallyRational_topTradingCycles,
      isParetoEfficient_topTradingCycles,
      isStrategyProof_topTradingCycles⟩

/-- **Characterization of top trading cycles via group strategy-proofness** ([Bird1984]; [Ma1994];
[Svensson1999]): a direct housing mechanism is individually rational, Pareto efficient, and
strongly group strategy-proof if and only if it equals `HousingMechanism.topTradingCycles`. -/
theorem eq_topTradingCycles_iff_groupStrategyProof {M : HousingMechanism n} :
    (M.IsIndividuallyRational ∧ M.IsParetoEfficient ∧ M.IsGroupStrategyProof) ↔
      M = topTradingCycles := by
  constructor
  · rintro ⟨hIR, hPE, hGSP⟩
    exact eq_topTradingCycles_of_ir_pe_sp hIR hPE hGSP.isStrategyProof
  · rintro rfl
    exact ⟨isIndividuallyRational_topTradingCycles,
      isParetoEfficient_topTradingCycles,
      isGroupStrategyProof_topTradingCycles⟩

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
  | zero =>
    exfalso
    have := i.isLt
    omega
  | succ k ih =>
    have hk : k < n := by omega
    have hR : R.Nonempty := Finset.card_pos.1 (by omega)
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    have hh : I.topChoice R a ∈ R := I.topChoice_mem hR a
    by_cases hia : i = a
    · rw [hia, I.sdSteps_succ_of_eq hk R]
      exact hh
    · rw [I.sdSteps_succ_of_ne hk R hia]
      exact Finset.sdiff_subset
        (ih (by omega) (card_sdiff_singleton_ge hcard hh) (val_ge_of_ne hk hi hia))

theorem sdSteps_injOn {k : ℕ} {R : Finset (Fin n)} (hk_le : k ≤ n) (hcard : k ≤ R.card) :
    Set.InjOn (I.sdSteps k R) {i : Fin n | n - k ≤ i.val} := by
  induction k generalizing R with
  | zero =>
    intro x hx
    exfalso
    have : n ≤ x.val := hx
    have := x.isLt
    omega
  | succ k ih =>
    intro x hx y hy hxy
    have hk : k < n := by omega
    have hR : R.Nonempty := Finset.card_pos.1 (by omega)
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    let h := I.topChoice R a
    have hh : h ∈ R := I.topChoice_mem hR a
    have hcard' : k ≤ (R \ {h}).card := card_sdiff_singleton_ge hcard hh
    have hdisj : ∀ {u v : Fin n}, n - (k + 1) ≤ v.val → u = a → v ≠ a →
        I.sdSteps (k + 1) R u ≠ I.sdSteps (k + 1) R v := by
      intro u v hv hua hva huv
      rw [hua, I.sdSteps_succ_of_eq hk R, I.sdSteps_succ_of_ne hk R hva] at huv
      have hmem := I.sdSteps_mem (by omega) hcard' (val_ge_of_ne hk hv hva)
      exact (Finset.mem_sdiff.1 hmem).2 (huv ▸ Finset.mem_singleton_self h)
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
  | zero =>
    intro i hi
    exfalso
    have := i.isLt
    omega
  | succ k ih =>
    intro i hi
    have hk : k < n := by omega
    have hRne : R.Nonempty := Finset.card_pos.1 (by omega)
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    let h := I.topChoice R a
    have hh : h ∈ R := I.topChoice_mem hRne a
    have ha_ge : n - (k + 1) ≤ a.val := by
      change n - (k + 1) ≤ n - 1 - k
      omega
    have ha_eq : ν a = h := by
      have h1 := hle a ha_ge
      rw [I.sdSteps_succ_of_eq hk R] at h1
      exact I.rank_injective a (le_antisymm h1 (I.rank_topChoice_le (hR a ha_ge) a))
    by_cases hia : i = a
    · rw [hia, I.sdSteps_succ_of_eq hk R, ha_eq]
    · rw [I.sdSteps_succ_of_ne hk R hia]
      refine ih (by omega) (card_sdiff_singleton_ge hcard hh) (fun j hj => ?_) (fun j hj => ?_)
        i (val_ge_of_ne hk hi hia)
      · have hja : j ≠ a := fun h0 => by
          have : j.val = n - 1 - k := congrArg Fin.val h0
          omega
        refine Finset.mem_sdiff.2 ⟨hR j (by omega), fun hmem => hja ?_⟩
        exact ν.injective ((Finset.mem_singleton.1 hmem).trans ha_eq.symm)
      · have hja : j ≠ a := fun h0 => by
          have : j.val = n - 1 - k := congrArg Fin.val h0
          omega
        have h1 := hle j (by omega)
        rwa [I.sdSteps_succ_of_ne hk R hja] at h1

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
  | zero =>
    exfalso
    have := i.isLt
    omega
  | succ k ih =>
    have hk : k < n := by omega
    have hRne : R.Nonempty := Finset.card_pos.1 (by omega)
    let J := I.updatePref i π
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    by_cases hia : i = a
    · have hJmem : J.sdSteps (k + 1) R i ∈ R := J.sdSteps_mem hk_le hcard hi
      have hIsd : I.sdSteps (k + 1) R i = I.topChoice R i := by
        rw [hia]
        exact I.sdSteps_succ_of_eq hk R
      rw [hIsd]
      exact I.rank_topChoice_le hJmem i
    · have hai : a ≠ i := Ne.symm hia
      have htop_eq : J.topChoice R a = I.topChoice R a := I.updatePref_topChoice_of_ne π hai R
      have hh : I.topChoice R a ∈ R := I.topChoice_mem hRne a
      rw [I.sdSteps_succ_of_ne hk R hia, J.sdSteps_succ_of_ne hk R hia, htop_eq]
      exact ih (by omega) (card_sdiff_singleton_ge hcard hh) (val_ge_of_ne hk hi hia)

private theorem sdSteps_eq_of_val_lt {k : ℕ} (hk_le : k ≤ n) (R : Finset (Fin n))
    (i : Fin n) (hi : i.val < n - k) (π : Equiv.Perm (Fin n)) (j : Fin n) :
    (I.updatePref i π).sdSteps k R j = I.sdSteps k R j := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have hk : k < n := by omega
    let J := I.updatePref i π
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    have hai : a ≠ i := by
      intro h0
      have : n - 1 - k = i.val := congrArg Fin.val h0
      omega
    have htop_eq : J.topChoice R a = I.topChoice R a := I.updatePref_topChoice_of_ne π hai R
    by_cases hja : j = a
    · rw [hja, J.sdSteps_succ_of_eq hk R, I.sdSteps_succ_of_eq hk R, htop_eq]
    · rw [J.sdSteps_succ_of_ne hk R hja, I.sdSteps_succ_of_ne hk R hja, htop_eq]
      exact ih (by omega) _ (by omega)

private theorem sdSteps_updatePref_eq_of_apply_eq {k : ℕ} (hk_le : k ≤ n) (R : Finset (Fin n))
    (i : Fin n) (π : Equiv.Perm (Fin n))
    (heq_i : (I.updatePref i π).sdSteps k R i = I.sdSteps k R i) (j : Fin n) :
    (I.updatePref i π).sdSteps k R j = I.sdSteps k R j := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    have hk : k < n := by omega
    let J := I.updatePref i π
    let a : Fin n := ⟨n - 1 - k, by omega⟩
    by_cases hia : i = a
    · have hJ_ia : J.sdSteps (k + 1) R i = J.topChoice R a :=
        (congrArg (J.sdSteps (k + 1) R) hia).trans (J.sdSteps_succ_of_eq hk R)
      have hI_ia : I.sdSteps (k + 1) R i = I.topChoice R a :=
        (congrArg (I.sdSteps (k + 1) R) hia).trans (I.sdSteps_succ_of_eq hk R)
      have htop_eq : J.topChoice R a = I.topChoice R a :=
        hJ_ia.symm.trans (heq_i.trans hI_ia)
      by_cases hja : j = a
      · rw [hja, J.sdSteps_succ_of_eq hk R, I.sdSteps_succ_of_eq hk R, htop_eq]
      · rw [J.sdSteps_succ_of_ne hk R hja, I.sdSteps_succ_of_ne hk R hja, htop_eq]
        have hi_lt : i.val < n - k := by
          have : i.val = n - 1 - k := congrArg Fin.val hia
          omega
        exact I.sdSteps_eq_of_val_lt (by omega) _ i hi_lt π j
    · have hai : a ≠ i := Ne.symm hia
      have htop_eq : J.topChoice R a = I.topChoice R a := I.updatePref_topChoice_of_ne π hai R
      have heq_i' : J.sdSteps k (R \ {I.topChoice R a}) i =
          I.sdSteps k (R \ {I.topChoice R a}) i := by
        rwa [J.sdSteps_succ_of_ne hk R hia, I.sdSteps_succ_of_ne hk R hia, htop_eq] at heq_i
      by_cases hja : j = a
      · rw [hja, J.sdSteps_succ_of_eq hk R, I.sdSteps_succ_of_eq hk R, htop_eq]
      · rw [J.sdSteps_succ_of_ne hk R hja, I.sdSteps_succ_of_ne hk R hja, htop_eq]
        exact ih (by omega) _ heq_i'

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
