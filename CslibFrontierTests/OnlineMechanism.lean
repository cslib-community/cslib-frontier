/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.GameTheory.Mechanism.Online.Basic
import CslibFrontier.GameTheory.Mechanism.Online.DynamicVCG
public import CslibFrontier.GameTheory.Mechanism.Online.ExpiringItems
import CslibFrontier.GameTheory.Mechanism.Online.PostedPrice
import CslibFrontier.Probability.PMF
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Online mechanism design tests and boundary witnesses

Concrete non-vacuous witnesses and negative boundary cases for `Cslib.GameTheory.OnlineMechanism`
(Parkes example/lemma locators below are not verified against primary PDF):

* **Example 16.1 (`Auction 1` delayed-arrival attack)**: naive per-period Vickrey auction fails
  online truthfulness when Agent 0 delays its arrival from `t = 0` to `t = 1`, raising utility from
  `1` to `2`.
* **Greedy `Auction 2` trace & late-departure attack**: checked allocations and welfare on the
  3-agent instance, plus an explicit counterexample proving `Auction 2` fails
  `IsDSICNoEarlyArrival` when late departures are allowed (`criticalValue` drops from `1` to `0`).
* **Non-monotone policies in departure and arrival dimensions**: policies monotone in value yet
  violating departure or arrival monotonicity are provably non-implementable.
* **Lemma 16.14 `IsNPT` boundary**: dropping `IsNPT` breaks critical-payment uniqueness.
* **Dynamic VCG 2-period ice-cream MDP ([Parkes2007], Example 16.27)**: exact Bellman values
  (`11.5`, `10`, `11`), marginal-externality payment (`3.5` for Agent 1), expected utilities
  (`1.5` and `0.5`), and explicit proof that Agent 0 overbidding drops utility to `1`.
* **Posted-price & geometric threshold witnesses**: critical value formula and `2m`-competitive
  strongly truthful single-item online auction witness.
-/

namespace CslibFrontierTests.OnlineMechanism

open Cslib.GameTheory.OnlineMechanism
open Cslib.GameTheory.OnlineMechanism.DynamicVCG
open scoped ENNReal

private abbrev mkType {T : ℕ} (a d : Fin T) (had : a ≤ d) (v : ℝ) (hv : 0 ≤ v) :
    AgentType (Fin T) :=
  ⟨a, d, v, had, hv⟩

/-! ### 1. Parkes Example 16.1 (`Auction 1`) & Greedy `Auction 2` Trace + Late-Departure Attack -/

section ExpiringWitnesses

open Classical in
/-- Naive per-period Vickrey auction (`Auction 1`, [Parkes2007] Example 16.1, locator not verified
against primary PDF): uses greedy unit-capacity allocation, but charges each period's winner the
highest bid among other active unallocated agents in that period. -/
private noncomputable def auction1 : Mechanism (Fin 3) (Fin 2) where
  policy := greedyPolicy (fun _ => 1)
  payment θ i :=
    match (greedyPolicy (fun _ => 1)).alloc θ i with
    | none => 0
    | some t =>
      let others : Finset (Fin 3) :=
        Finset.univ.filter fun j =>
          j ≠ i ∧ (θ j).InWindow t ∧
            ∀ s : Fin 2, s < t → (greedyPolicy (fun _ => 1)).alloc θ j ≠ some s
      if h : others.Nonempty then others.sup' h fun j => (θ j).value else 0

/-- Helper: in `Fin 2`, if `(greedyPolicy (fun _ => 1)).alloc θ i = some 0`, no other agent wins
at period `0`. -/
private lemma other_ne_some_zero {θ : Fin 3 → AgentType (Fin 2)} {i j : Fin 3} (hne : j ≠ i)
    (hi : (greedyPolicy (fun _ => 1)).alloc θ i = some 0) :
    (greedyPolicy (fun _ => 1)).alloc θ j ≠ some 0 := by
  intro hj
  have hle :
      (Finset.univ.filter fun x => (greedyPolicy (fun _ => 1)).alloc θ x = some 0).card ≤ 1 :=
    (greedyPolicy_isExpiringFeasible (ι := Fin 3) (T := 2) (fun _ => 1) θ).2 0
  have hsub : ({i, j} : Finset (Fin 3)) ⊆
      Finset.univ.filter fun x => (greedyPolicy (fun _ => 1)).alloc θ x = some 0 := by
    intro x hx
    rw [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_pair hne.symm] at hcard
  omega

/-- Helper: if agent `i` has window `[0, 0]` and does not win `0`, it gets `none`. -/
private lemma none_of_window_zero {θ : Fin 3 → AgentType (Fin 2)} {i : Fin 3}
    (hd : (θ i).departure = 0)
    (h0 : (greedyPolicy (fun _ => 1)).alloc θ i ≠ some 0) :
    (greedyPolicy (fun _ => 1)).alloc θ i = none := by
  cases h : (greedyPolicy (fun _ => 1)).alloc θ i with
  | none => rfl
  | some t =>
    have ht0 : t = 0 := le_antisymm
      (hd ▸ ((greedyPolicy (fun _ => 1)).alloc_in_window θ i t h).2) (Fin.zero_le t)
    exact absurd (ht0 ▸ h) h0

/-- Checked trace of `greedyPolicy` on [Parkes2007] Example 16.1 / 16.16 (locator not verified
against primary PDF): on Agent 0 `(0, 1, 5)`, Agent 1 `(0, 0, 4)`, Agent 2 `(1, 1, 3)`, greedy
allocates Agent 0 at `0`, leaves Agent 1 unallocated, and allocates Agent 2 at `1` (welfare `8`,
while offline optimal welfare is `9 ≤ 2 * 8`). Under naive per-period Vickrey (`auction1`),
Agent 0's truthful utility is `1`, whereas delaying arrival to `(1, 1, 5)` raises Agent 0's utility
to `2`, proving `¬ auction1.IsDSIC`. -/
theorem auction1_not_isDSIC_and_greedy_trace :
    let h01 : (0 : Fin 2) ≤ 1 := by decide
    let θ_true : Fin 3 → AgentType (Fin 2) :=
      ![mkType 0 1 h01 5 (by norm_num), mkType 0 0 le_rfl 4 (by norm_num),
        mkType 1 1 le_rfl 3 (by norm_num)]
    let θ_delay : Fin 3 → AgentType (Fin 2) :=
      ![mkType 1 1 le_rfl 5 (by norm_num), mkType 0 0 le_rfl 4 (by norm_num),
        mkType 1 1 le_rfl 3 (by norm_num)]
    (greedyPolicy (fun _ => 1)).alloc θ_true 0 = some 0 ∧
    (greedyPolicy (fun _ => 1)).alloc θ_true 1 = none ∧
    (greedyPolicy (fun _ => 1)).alloc θ_true 2 = some 1 ∧
    welfare θ_true ((greedyPolicy (fun _ => 1)).alloc θ_true) = 8 ∧
    auction1.utility 0 (θ_true 0) θ_true = 1 ∧
    auction1.utility 0 (θ_true 0) θ_delay = 2 ∧
    ¬ auction1.IsDSIC := by
  classical
  intro h01 θ_true θ_delay
  have ht0 : (greedyPolicy (fun _ => 1)).alloc θ_true 0 = some 0 := by
    rw [greedyPolicy_alloc_eq_some_iff_priority]
    refine ⟨fun s hs => absurd hs (Fin.not_lt_zero s), ⟨le_rfl, h01⟩, ?_⟩
    have hempty :
        (Finset.univ.filter fun j : Fin 3 =>
          (∀ s : Fin 2, s < 0 → (greedyPolicy (fun _ => 1)).alloc θ_true j ≠ some s) ∧
          (θ_true j).InWindow 0 ∧
          ((θ_true 0).value < (θ_true j).value ∨
            ((θ_true 0).value = (θ_true j).value ∧ j < 0))) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      fin_cases j <;> simp [θ_true, AgentType.InWindow]
      norm_num
    rw [hempty]; decide
  have ht1 : (greedyPolicy (fun _ => 1)).alloc θ_true 1 = none :=
    none_of_window_zero rfl (other_ne_some_zero (by decide) ht0)
  have ht2_ne0 : (greedyPolicy (fun _ => 1)).alloc θ_true 2 ≠ some 0 :=
    other_ne_some_zero (by decide) ht0
  have ht2 : (greedyPolicy (fun _ => 1)).alloc θ_true 2 = some 1 := by
    rw [greedyPolicy_alloc_eq_some_iff_priority]
    refine ⟨fun s hs => ?_, ⟨le_rfl, le_rfl⟩, ?_⟩
    · have hs0 : s = 0 := Fin.ext (by omega)
      exact hs0 ▸ ht2_ne0
    · have hempty :
          (Finset.univ.filter fun j : Fin 3 =>
            (∀ s : Fin 2, s < 1 → (greedyPolicy (fun _ => 1)).alloc θ_true j ≠ some s) ∧
            (θ_true j).InWindow 1 ∧
            ((θ_true 2).value < (θ_true j).value ∨
              ((θ_true 2).value = (θ_true j).value ∧ j < 2))) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        fin_cases j
        · exact fun h => h.1 0 (by decide) ht0
        · simp [θ_true, AgentType.InWindow]
        · simp [θ_true]
      rw [hempty]; decide
  have hw_true : welfare θ_true ((greedyPolicy (fun _ => 1)).alloc θ_true) = 8 := by
    simp only [welfare, Fin.sum_univ_three, ht0, ht1, ht2, AgentType.realizedValue_none]
    rw [AgentType.realizedValue_some_of_inWindow (show (θ_true 0).InWindow 0 from ⟨le_rfl, h01⟩),
      AgentType.realizedValue_some_of_inWindow (show (θ_true 2).InWindow 1 from ⟨le_rfl, le_rfl⟩)]
    simp only [θ_true, Matrix.cons_val_zero, Matrix.cons_val]
    norm_num
  have hd1 : (greedyPolicy (fun _ => 1)).alloc θ_delay 1 = some 0 := by
    rw [greedyPolicy_alloc_eq_some_iff_priority]
    refine ⟨fun s hs => absurd hs (Fin.not_lt_zero s), ⟨le_rfl, le_rfl⟩, ?_⟩
    have hempty :
        (Finset.univ.filter fun j : Fin 3 =>
          (∀ s : Fin 2, s < 0 → (greedyPolicy (fun _ => 1)).alloc θ_delay j ≠ some s) ∧
          (θ_delay j).InWindow 0 ∧
          ((θ_delay 1).value < (θ_delay j).value ∨
            ((θ_delay 1).value = (θ_delay j).value ∧ j < 1))) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      fin_cases j <;> simp [θ_delay, AgentType.InWindow]
    rw [hempty]; decide
  have hd0_ne0 : (greedyPolicy (fun _ => 1)).alloc θ_delay 0 ≠ some 0 :=
    other_ne_some_zero (by decide) hd1
  have hd0 : (greedyPolicy (fun _ => 1)).alloc θ_delay 0 = some 1 := by
    rw [greedyPolicy_alloc_eq_some_iff_priority]
    refine ⟨fun s hs => ?_, ⟨le_rfl, le_rfl⟩, ?_⟩
    · have hs0 : s = 0 := Fin.ext (by omega)
      exact hs0 ▸ hd0_ne0
    · have hempty :
          (Finset.univ.filter fun j : Fin 3 =>
            (∀ s : Fin 2, s < 1 → (greedyPolicy (fun _ => 1)).alloc θ_delay j ≠ some s) ∧
            (θ_delay j).InWindow 1 ∧
            ((θ_delay 0).value < (θ_delay j).value ∨
              ((θ_delay 0).value = (θ_delay j).value ∧ j < 0))) = ∅ := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        fin_cases j
        · simp [θ_delay]
        · simp [θ_delay, AgentType.InWindow]
        · simp [θ_delay]
          norm_num
      rw [hempty]; decide
  have hu_true : auction1.utility 0 (θ_true 0) θ_true = 1 := by
    simp only [Mechanism.utility, auction1, ht0,
      AgentType.realizedValue_some_of_inWindow (show (θ_true 0).InWindow 0 from ⟨le_rfl, h01⟩)]
    have hoth :
        (Finset.univ.filter fun j : Fin 3 =>
          j ≠ 0 ∧ (θ_true j).InWindow 0 ∧
            ∀ s : Fin 2, s < 0 → (greedyPolicy (fun _ => 1)).alloc θ_true j ≠ some s) = {1} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      fin_cases j <;> simp [θ_true, AgentType.InWindow]
    simp only [hoth, Finset.singleton_nonempty, ↓reduceDIte, Finset.sup'_singleton, θ_true,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  have hu_delay : auction1.utility 0 (θ_true 0) θ_delay = 2 := by
    simp only [Mechanism.utility, auction1, hd0,
      AgentType.realizedValue_some_of_inWindow (show (θ_true 0).InWindow 1 from ⟨h01, le_rfl⟩)]
    have hoth :
        (Finset.univ.filter fun j : Fin 3 =>
          j ≠ 0 ∧ (θ_delay j).InWindow 1 ∧
            ∀ s : Fin 2, s < 1 → (greedyPolicy (fun _ => 1)).alloc θ_delay j ≠ some s) = {2} := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      match j with
      | 0 => simp
      | 1 => simp [θ_delay, AgentType.InWindow]
      | 2 =>
        have h2w : (θ_delay 2).InWindow 1 := ⟨le_rfl, le_rfl⟩
        simp only [h2w, ne_eq, Fin.reduceEq, not_false_eq_true, true_and, iff_true]
        intro s hs
        have hs0 : s = 0 := Fin.ext (by omega)
        rw [hs0]
        exact other_ne_some_zero (j := 2) (by decide) hd1
    simp only [hoth, Finset.singleton_nonempty, ↓reduceDIte, Finset.sup'_singleton, θ_true, θ_delay,
      Matrix.cons_val_zero, Matrix.cons_val]
    norm_num
  have hnot_dsic : ¬ auction1.IsDSIC := by
    intro hdsic
    have hmis : (θ_true 0).IsValidMisreport (θ_delay 0) := ⟨h01, le_rfl⟩
    have hupd : Function.update θ_delay 0 (θ_true 0) = θ_true := by
      ext j; fin_cases j <;> rfl
    have hle := hdsic 0 θ_delay (θ_true 0) hmis
    rw [hupd, hu_true, hu_delay] at hle
    linarith
  exact ⟨ht0, ht1, ht2, hw_true, hu_true, hu_delay, hnot_dsic⟩

/-- Late-departure attack on Greedy `Auction 2`: under no-early-arrival and no-late-departure,
`greedyMechanism (fun _ => 1)` is `IsDSIC`, `IsIR`, `IsNPT`, `IsLoserZero`, and `2`-competitive.
However, when *late-departure* misreports are permitted, Agent 1 with true type `(0, 0, 2)` facing
Agent 0 `(0, 0, 1)` and Agent 2 `(1, 1, 0)` raises its utility from `1` to `2` by misreporting
`(0, 1, 2)` (winning at `t = 0` while dropping its critical value from `1` to `0`), proving
`¬ (greedyMechanism (fun _ => 1)).IsDSICNoEarlyArrival`. -/
public theorem greedyMechanism_late_departure_attack :
    (greedyMechanism (ι := Fin 3) (T := 2) (fun _ => 1)).IsDSIC ∧
    ¬ (greedyMechanism (ι := Fin 3) (T := 2) (fun _ => 1)).IsDSICNoEarlyArrival := by
  classical
  refine ⟨greedyMechanism_isDSIC (fun _ => 1), fun hnea => ?_⟩
  have h01 : (0 : Fin 2) ≤ 1 := by decide
  let θ_true : Fin 3 → AgentType (Fin 2) :=
    ![mkType 0 0 le_rfl 1 (by norm_num), mkType 0 0 le_rfl 2 (by norm_num),
      mkType 1 1 le_rfl 0 le_rfl]
  let θ_late : Fin 3 → AgentType (Fin 2) :=
    ![mkType 0 0 le_rfl 1 (by norm_num), mkType 0 1 h01 2 (by norm_num),
      mkType 1 1 le_rfl 0 le_rfl]
  have hupd : Function.update θ_late 1 (θ_true 1) = θ_true := by
    ext j; fin_cases j <;> rfl
  have h1_wins_at_0 : ∀ (d : Fin 2) (hd : (0 : Fin 2) ≤ d) (r : ℝ) (hr : 0 ≤ r), 1 < r →
      (greedyPolicy (fun _ => 1)).alloc
        (Function.update θ_late 1 (mkType 0 d hd r hr)) 1 = some 0 := by
    intro d hd r hr hr1
    set θ' := Function.update θ_late 1 (mkType 0 d hd r hr)
    have h0' : θ' 0 = mkType 0 0 le_rfl 1 (by norm_num) := rfl
    have h1' : θ' 1 = mkType 0 d hd r hr := Function.update_self 1 _ θ_late
    have h2' : θ' 2 = mkType 1 1 le_rfl 0 le_rfl := rfl
    rw [greedyPolicy_alloc_eq_some_iff_priority]
    refine ⟨fun s hs => absurd hs (Fin.not_lt_zero s), by rw [h1']; exact ⟨le_rfl, hd⟩, ?_⟩
    have hempty :
        (Finset.univ.filter fun j : Fin 3 =>
          (∀ s : Fin 2, s < 0 → (greedyPolicy (fun _ => 1)).alloc θ' j ≠ some s) ∧
          (θ' j).InWindow 0 ∧
          ((θ' 1).value < (θ' j).value ∨ ((θ' 1).value = (θ' j).value ∧ j < 1))) = ∅ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      match j with
      | 0 =>
        rintro ⟨_, _, h | ⟨heq, _⟩⟩
        · rw [h0', h1'] at h; dsimp at h; linarith
        · rw [h0', h1'] at heq; dsimp at heq; linarith
      | 1 =>
        rintro ⟨_, _, h | ⟨_, hlt⟩⟩
        · exact lt_irrefl _ h
        · exact lt_irrefl _ hlt
      | 2 =>
        rintro ⟨_, hw, _⟩
        rw [h2'] at hw; exact absurd hw.1 (by decide)
    rw [hempty]; decide
  have htrue_win : (greedyPolicy (fun _ => 1)).alloc θ_true 1 = some 0 := by
    have hupd' : Function.update θ_late 1 (mkType 0 0 le_rfl 2 (by norm_num)) = θ_true := by
      ext j; match j with | 0 => rfl | 1 => rfl | 2 => rfl
    rw [← hupd']
    exact h1_wins_at_0 0 le_rfl 2 (by norm_num) (by norm_num)
  have hlate_win : (greedyPolicy (fun _ => 1)).alloc θ_late 1 = some 0 := by
    have heq : Function.update θ_late 1 (mkType 0 1 h01 2 (by norm_num)) = θ_late := by
      ext j; match j with | 0 => rfl | 1 => rfl | 2 => rfl
    rw [← heq]
    exact h1_wins_at_0 1 h01 2 (by norm_num) (by norm_num)
  have hcv00 :
      (greedyPolicy (fun _ => 1)).criticalValue θ_late 1 0 0 le_rfl = ENNReal.ofReal 1 := by
    apply Policy.criticalValue_eq_of_threshold (by norm_num)
    · intro r hr hr1
      rw [h1_wins_at_0 0 le_rfl r hr hr1]; rfl
    · intro r hr hwin
      by_contra hlt
      push Not at hlt
      set θ' := Function.update θ_late 1 (mkType 0 0 le_rfl r hr)
      have h0' : θ' 0 = mkType 0 0 le_rfl 1 (by norm_num) := rfl
      have h1' : θ' 1 = mkType 0 0 le_rfl r hr := Function.update_self 1 _ θ_late
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hwin
      have ht0 : t = 0 := le_antisymm
        (by
          have := ((greedyPolicy (fun _ => 1)).alloc_in_window θ' 1 t ht).2
          rw [h1'] at this; exact this)
        (Fin.zero_le t)
      rw [ht0, greedyPolicy_alloc_eq_some_iff_priority] at ht
      have h0mem :
          (0 : Fin 3) ∈ Finset.univ.filter fun j : Fin 3 =>
            (∀ s : Fin 2, s < 0 → (greedyPolicy (fun _ => 1)).alloc θ' j ≠ some s) ∧
            (θ' j).InWindow 0 ∧
            ((θ' 1).value < (θ' j).value ∨ ((θ' 1).value = (θ' j).value ∧ j < 1)) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ 0, fun s hs => absurd hs (Fin.not_lt_zero s),
          by rw [h0']; exact ⟨le_rfl, le_rfl⟩, Or.inl (by rw [h0', h1']; exact hlt)⟩
      have hcard := Finset.one_le_card.mpr ⟨0, h0mem⟩
      have hlt1 : _ < 1 := ht.2.2
      omega
  have hcv01 :
      (greedyPolicy (fun _ => 1)).criticalValue θ_late 1 0 1 h01 = ENNReal.ofReal 0 := by
    apply Policy.criticalValue_eq_of_threshold le_rfl
    · intro r hr hrpos
      set θ' := Function.update θ_late 1 (mkType 0 1 h01 r hr)
      have h0' : θ' 0 = mkType 0 0 le_rfl 1 (by norm_num) := rfl
      have h1' : θ' 1 = mkType 0 1 h01 r hr := Function.update_self 1 _ θ_late
      have h2' : θ' 2 = mkType 1 1 le_rfl 0 le_rfl := rfl
      by_cases h10 : (greedyPolicy (fun _ => 1)).alloc θ' 1 = some 0
      · rw [h10]; rfl
      · have h11 : (greedyPolicy (fun _ => 1)).alloc θ' 1 = some 1 := by
          rw [greedyPolicy_alloc_eq_some_iff_priority]
          refine ⟨fun s hs => ?_, by rw [h1']; exact ⟨h01, le_rfl⟩, ?_⟩
          · have hs0 : s = 0 := Fin.ext (by omega)
            exact hs0 ▸ h10
          · have hempty :
                (Finset.univ.filter fun j : Fin 3 =>
                  (∀ s : Fin 2, s < 1 → (greedyPolicy (fun _ => 1)).alloc θ' j ≠ some s) ∧
                  (θ' j).InWindow 1 ∧
                  ((θ' 1).value < (θ' j).value ∨ ((θ' 1).value = (θ' j).value ∧ j < 1))) = ∅ := by
              ext j
              simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
                iff_false]
              match j with
              | 0 =>
                rintro ⟨_, hw, _⟩
                rw [h0'] at hw; exact absurd hw.2 (by decide)
              | 1 =>
                rintro ⟨_, _, h | ⟨_, hlt⟩⟩
                · exact lt_irrefl _ h
                · exact lt_irrefl _ hlt
              | 2 =>
                rintro ⟨_, _, h | ⟨heq, _⟩⟩
                · rw [h1', h2'] at h; dsimp at h; linarith
                · rw [h1', h2'] at heq; dsimp at heq; linarith
            rw [hempty]; decide
        rw [h11]; rfl
    · intro r hr _; exact hr
  have hds := hnea 1 θ_late (θ_true 1) (by simp [AgentType.NoEarlyArrival, θ_true, θ_late])
  rw [hupd] at hds
  have hu_late : (greedyMechanism (fun _ => 1)).utility 1 (θ_true 1) θ_late = 2 := by
    simp only [Mechanism.utility, greedyMechanism, Policy.criticalMechanism, Policy.criticalPayment,
      hlate_win, AgentType.realizedValue_some_of_inWindow
        (show (θ_true 1).InWindow 0 from ⟨le_rfl, le_rfl⟩),
      Option.isSome_some, ↓reduceIte]
    change (2 : ℝ) - ((greedyPolicy (fun _ => 1)).criticalValue θ_late 1 0 1 h01).toReal = 2
    rw [hcv01, ENNReal.ofReal_zero, ENNReal.toReal_zero, sub_zero]
  have hu_true : (greedyMechanism (fun _ => 1)).utility 1 (θ_true 1) θ_true = 1 := by
    simp only [Mechanism.utility, greedyMechanism, Policy.criticalMechanism, Policy.criticalPayment,
      htrue_win, AgentType.realizedValue_some_of_inWindow
        (show (θ_true 1).InWindow 0 from ⟨le_rfl, le_rfl⟩),
      Option.isSome_some, ↓reduceIte]
    have hcv_eq :
        (greedyPolicy (fun _ => 1)).criticalValue θ_true 1 0 0 le_rfl =
          (greedyPolicy (fun _ => 1)).criticalValue θ_late 1 0 0 le_rfl := by
      rw [← hupd, Policy.criticalValue_update]
    change (2 : ℝ) - ((greedyPolicy (fun _ => 1)).criticalValue θ_true 1 0 0 le_rfl).toReal = 1
    rw [hcv_eq, hcv00, ENNReal.toReal_ofReal (by norm_num)]
    norm_num
  rw [hu_late, hu_true] at hds
  linarith

end ExpiringWitnesses

/-! ### 2. Non-monotone policies in arrival and departure dimensions are non-implementable -/

section NonMonotoneCounterexamples

/-- A single-agent policy on `Fin 2` that allocates at `t = 0` iff the agent's reported departure
is `0`. It is monotone in value and arrival, yet fails monotonicity in the departure dimension. -/
private def impatientOnlyPolicy : Policy Unit (Fin 2) where
  alloc θ _ := if (θ ()).departure = 0 then some 0 else none
  alloc_in_window θ _ t ht := by
    split_ifs at ht with hd
    · have ht0 := Option.some.inj ht
      rw [← ht0]
      exact ⟨(θ ()).arrival_le_departure.trans (le_of_eq hd), le_of_eq hd.symm⟩

/-- `impatientOnlyPolicy` is neither online-monotone nor implementable by any DSIC, IR, NPT,
loser-zero mechanism. -/
theorem impatientOnlyPolicy_not_implementable :
    ¬ impatientOnlyPolicy.IsMonotone ∧ ¬ impatientOnlyPolicy.IsImplementable := by
  have hnot : ¬ impatientOnlyPolicy.IsMonotone := by
    intro hmono
    have h01 : (0 : Fin 2) ≤ 1 := by decide
    let θ₁ : AgentType (Fin 2) := mkType 0 0 le_rfl 1 (by norm_num)
    let θ₂ : AgentType (Fin 2) := mkType 0 1 h01 2 (by norm_num)
    have h := hmono () (fun _ => θ₁) θ₁ θ₂ le_rfl h01 (by dsimp [θ₁, θ₂]; norm_num)
      (by simp [impatientOnlyPolicy, θ₁])
    simp [impatientOnlyPolicy, θ₂] at h
  exact ⟨hnot, fun himp => hnot (Policy.isImplementable_iff_isMonotone.mp himp)⟩

/-- A single-agent policy on `Fin 2` that allocates at `t = 1` iff the agent's reported arrival
is `1`. It is monotone in value and departure, yet fails monotonicity in the arrival dimension
(rewarding delayed arrival). -/
private def lateArrivalOnlyPolicy : Policy Unit (Fin 2) where
  alloc θ _ := if (θ ()).arrival = 1 then some 1 else none
  alloc_in_window θ _ t ht := by
    split_ifs at ht with ha
    · have ht1 := Option.some.inj ht
      rw [← ht1]
      exact ⟨le_of_eq ha, (le_of_eq ha.symm).trans (θ ()).arrival_le_departure⟩

/-- `lateArrivalOnlyPolicy` is neither online-monotone nor implementable. -/
theorem lateArrivalOnlyPolicy_not_implementable :
    ¬ lateArrivalOnlyPolicy.IsMonotone ∧ ¬ lateArrivalOnlyPolicy.IsImplementable := by
  have hnot : ¬ lateArrivalOnlyPolicy.IsMonotone := by
    intro hmono
    have h01 : (0 : Fin 2) ≤ 1 := by decide
    let θ₁ : AgentType (Fin 2) := mkType 1 1 le_rfl 1 (by norm_num)
    let θ₂ : AgentType (Fin 2) := mkType 0 1 h01 2 (by norm_num)
    have h := hmono () (fun _ => θ₁) θ₁ θ₂ h01 le_rfl (by dsimp [θ₁, θ₂]; norm_num)
      (by simp [lateArrivalOnlyPolicy, θ₁])
    simp [lateArrivalOnlyPolicy, θ₂] at h
  exact ⟨hnot, fun himp => hnot (Policy.isImplementable_iff_isMonotone.mp himp)⟩

private def alwaysWinPolicy : Policy Unit (Fin 2) where
  alloc θ _ := some (θ ()).arrival
  alloc_in_window θ _ t ht := by
    have ht' := Option.some.inj ht
    rw [← ht']
    exact ⟨le_rfl, (θ ()).arrival_le_departure⟩

private def subsidizedAlwaysWin : Mechanism Unit (Fin 2) where
  policy := alwaysWinPolicy
  payment _ _ := -1

/-- Boundary witness for Lemma 16.14 (`payment_eq_criticalPayment`): dropping `IsNPT` breaks
uniqueness of critical payments, since `subsidizedAlwaysWin` is `IsDSIC`, `IsIR`, and `IsLoserZero`
while charging `-1 ≠ 0 = criticalPayment`. Also exercises `AgentType.isValidMisreport_refl`. -/
theorem npt_necessary_for_payment_uniqueness :
    subsidizedAlwaysWin.IsDSIC ∧ subsidizedAlwaysWin.IsIR ∧ subsidizedAlwaysWin.IsLoserZero ∧
      ¬ subsidizedAlwaysWin.IsNPT ∧
      ∃ θ, subsidizedAlwaysWin.payment θ () ≠ subsidizedAlwaysWin.policy.criticalPayment θ () := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro _ θ θ_true hmis
    have _ := θ_true.isValidMisreport_refl
    have hin : θ_true.InWindow (θ ()).arrival :=
      AgentType.InWindow.of_isValidMisreport hmis ⟨le_rfl, (θ ()).arrival_le_departure⟩
    simp only [Mechanism.utility, subsidizedAlwaysWin, alwaysWinPolicy, Function.update_self,
      AgentType.realizedValue_some_of_inWindow hin,
      AgentType.realizedValue_some_of_inWindow
        (show θ_true.InWindow θ_true.arrival from ⟨le_rfl, θ_true.arrival_le_departure⟩), le_rfl]
  · intro _ θ
    simp only [Mechanism.utility, subsidizedAlwaysWin, alwaysWinPolicy,
      AgentType.realizedValue_some_of_inWindow
        (show (θ ()).InWindow (θ ()).arrival from ⟨le_rfl, (θ ()).arrival_le_departure⟩)]
    linarith [(θ ()).value_nonneg]
  · intro _ θ hnone
    simp [subsidizedAlwaysWin, alwaysWinPolicy] at hnone
  · intro hnpt
    have := hnpt () (fun _ => mkType 0 0 le_rfl 0 le_rfl)
    simp [subsidizedAlwaysWin] at this
    linarith
  · refine ⟨fun _ => mkType 0 0 le_rfl 5 (by norm_num), ?_⟩
    have hcv :
        alwaysWinPolicy.criticalValue (fun _ => mkType 0 0 le_rfl 5 (by norm_num)) () 0 0 le_rfl =
          ENNReal.ofReal 0 := by
      apply Policy.criticalValue_eq_of_threshold le_rfl
      · intro r hr _
        simp [alwaysWinPolicy]
      · intro r hr _
        exact hr
    have hsome : (alwaysWinPolicy.alloc (fun _ => mkType 0 0 le_rfl 5 (by norm_num)) ()).isSome =
        true := rfl
    change (-1 : ℝ) ≠
      alwaysWinPolicy.criticalPayment (fun _ => mkType 0 0 le_rfl 5 (by norm_num)) ()
    unfold Policy.criticalPayment
    simp only [hsome, ↓reduceIte]
    change (-1 : ℝ) ≠ (alwaysWinPolicy.criticalValue _ () 0 0 le_rfl).toReal
    rw [hcv, ENNReal.ofReal_zero, ENNReal.toReal_zero]
    norm_num

end NonMonotoneCounterexamples

/-! ### 3. Dynamic VCG 2-Period Ice-Cream MDP ([Parkes2007], Example 16.27) -/

section DynamicVCGWitness

/-- State of the 2-period ice-cream MDP ([Parkes2007], Example 16.27, locator not verified against
primary PDF): whether Agent 0 (Parkes's Agent 1) was already served at `t = 0`, and whether
Agent 2 (Parkes's Agent 3) has high value (`10`) vs low value (`2`) at `t = 1`. -/
private structure IceCreamState where
  /-- Whether Agent 0 was already allocated at `t = 0`. -/
  agent0Served : Bool
  /-- Whether Agent 2 has high value (`10`) vs low value (`2`) at `t = 1`. -/
  agent2High : Bool
  deriving DecidableEq, Fintype

private abbrev IceCreamAction := Fin 3

private noncomputable def iceCreamTrans (_s : IceCreamState) (k : IceCreamAction) :
    PMF IceCreamState :=
  (Cslib.Probability.PMF.uniformOfFintype Bool).map fun b => ⟨decide (k = 1), b⟩

private def iceCreamVal : Fin 3 → ℕ → IceCreamState → IceCreamAction → ℝ
  | 0, 0, s, k => if !s.agent0Served ∧ k = 1 then 5 else 0
  | 0, 1, s, k => if !s.agent0Served ∧ k = 1 then 5 else 0
  | 1, 0, _, k => if k = 2 then 4 else 0
  | 2, 1, s, k => if k = 2 then (if s.agent2High then 10 else 2) else 0
  | _, _, _, _ => 0

private noncomputable def iceCreamEnv : DynamicEnv (Fin 3) IceCreamState IceCreamAction where
  discount := 1
  discount_nonneg := by norm_num
  trans := iceCreamTrans
  val := iceCreamVal

private lemma iceCreamTrans_toReal (s : IceCreamState) (k : IceCreamAction)
    (s' : IceCreamState) :
    (iceCreamTrans s k s').toReal =
      if s'.agent0Served = decide (k = 1) then (1 / 2 : ℝ) else 0 := by
  classical
  unfold iceCreamTrans
  rw [PMF.map_apply, tsum_fintype]
  cases s' with
  | mk served high =>
    cases served <;> cases high <;> fin_cases k <;>
      simp [Cslib.Probability.PMF.uniformOfFintype]

private lemma iceCream_val_nonneg (i : Fin 3) (t : ℕ) (s : IceCreamState) (k : IceCreamAction) :
    0 ≤ iceCreamEnv.val i t s k := by
  fin_cases i
  · cases t with
    | zero => simp [iceCreamEnv, iceCreamVal]; split_ifs <;> norm_num
    | succ t =>
      cases t with
      | zero => simp [iceCreamEnv, iceCreamVal]; split_ifs <;> norm_num
      | succ _ => simp [iceCreamEnv, iceCreamVal]
  · cases t with
    | zero => simp [iceCreamEnv, iceCreamVal]; split_ifs <;> norm_num
    | succ _ => simp [iceCreamEnv, iceCreamVal]
  · cases t with
    | zero => simp [iceCreamEnv, iceCreamVal]
    | succ t =>
      cases t with
      | zero => simp [iceCreamEnv, iceCreamVal]; split_ifs <;> norm_num
      | succ _ => simp [iceCreamEnv, iceCreamVal]

/-- Checked Bellman values, Dynamic VCG marginal-externality payments, utilities, and truthfulness
on the 2-period ice-cream MDP ([Parkes2007], Example 16.27, locator not verified against primary
PDF):
* Total optimal expected welfare from `s₀ = ⟨false, false⟩` is `23 / 2` (`11.5`).
* Without Agent 0, optimal welfare is `10`; without Agent 1, optimal welfare is `11`.
* Agent 1's marginal externality payment at `t = 0` under efficient action `k = 2` is `7 / 2`
  (`3.5`), giving utility `1 / 2` (`0.5`).
* Agent 0's truthful expected utility is `3 / 2` (`1.5`), whereas forcing early service at `t = 0`
  (`k = 1`) yields strictly lower expected utility `1 < 3 / 2`. -/
theorem iceCream_dynamicVCG_witness :
    let s₀ : IceCreamState := ⟨false, false⟩
    iceCreamEnv.optimalValue 0 2 s₀ = 23 / 2 ∧
    iceCreamEnv.optimalValueWithout 0 0 2 s₀ = 10 ∧
    iceCreamEnv.optimalValueWithout 1 0 2 s₀ = 11 ∧
    iceCreamEnv.pivotPayment 1 0 1 s₀ 2 = 7 / 2 ∧
    iceCreamEnv.agentUtility 0 (iceCreamEnv.optimalPolicy 0 2 0) 0 2 [] s₀ = 3 / 2 ∧
    iceCreamEnv.agentUtility 1 (iceCreamEnv.optimalPolicy 0 2 0) 0 2 [] s₀ = 1 / 2 ∧
    iceCreamEnv.agentUtility 0 (fun hs => if hs.length = 1 then 1 else 2) 0 2 [] s₀ = 1 := by
  intro s₀
  have hsup3 : ∀ f : Fin 3 → ℝ,
      Finset.univ.sup' Finset.univ_nonempty f = max (max (f 0) (f 1)) (f 2) := by
    intro f
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun x _ => by
        fin_cases x
        · exact le_max_of_le_left (le_max_left _ _)
        · exact le_max_of_le_left (le_max_right _ _)
        · exact le_max_right _ _
    · exact max_le (max_le (Finset.le_sup' f (Finset.mem_univ 0))
        (Finset.le_sup' f (Finset.mem_univ 1))) (Finset.le_sup' f (Finset.mem_univ 2))
  have hothers : ∀ (i : Fin 3) (t : ℕ) (s : IceCreamState) (k : IceCreamAction),
      iceCreamEnv.othersVal i t s k = iceCreamEnv.totalVal t s k - iceCreamEnv.val i t s k := by
    intro i t s k
    have := iceCreamEnv.val_add_othersVal i t s k
    linarith
  have hW1 : ∀ s : IceCreamState,
      iceCreamEnv.optimalValue 1 1 s =
        if s.agent2High then 10 else if s.agent0Served then 2 else 5 := by
    intro s
    cases s with
    | mk served high =>
      cases served <;> cases high <;>
        simp [DynamicEnv.optimalValue, DynamicEnv.bellmanValue, DynamicEnv.totalVal,
          iceCreamEnv, iceCreamVal, Fin.sum_univ_three, hsup3] <;>
        norm_num
  have hW1_no0 : ∀ s : IceCreamState,
      iceCreamEnv.optimalValueWithout 0 1 1 s = if s.agent2High then 10 else 2 := by
    intro s
    unfold DynamicEnv.optimalValueWithout DynamicEnv.bellmanValue
    rw [hsup3]
    simp only [DynamicEnv.bellmanValue, mul_zero, Finset.sum_const_zero, add_zero, hothers,
      DynamicEnv.totalVal, Fin.sum_univ_three]
    cases s with
    | mk served high =>
      cases served <;> cases high <;> simp [iceCreamEnv, iceCreamVal]
  have hW1_no1 : ∀ s : IceCreamState,
      iceCreamEnv.optimalValueWithout 1 1 1 s =
        if s.agent2High then 10 else if s.agent0Served then 2 else 5 := by
    intro s
    unfold DynamicEnv.optimalValueWithout DynamicEnv.bellmanValue
    rw [hsup3]
    simp only [DynamicEnv.bellmanValue, mul_zero, Finset.sum_const_zero, add_zero, hothers,
      DynamicEnv.totalVal, Fin.sum_univ_three]
    cases s with
    | mk served high =>
      cases served <;> cases high <;> simp [iceCreamEnv, iceCreamVal] <;> norm_num
  have hsum_states : ∀ f : IceCreamState → ℝ,
      ∑ s : IceCreamState, f s =
        f ⟨false, false⟩ + f ⟨false, true⟩ + f ⟨true, false⟩ + f ⟨true, true⟩ := by
    intro f
    have huniv :
        (Finset.univ : Finset IceCreamState) =
          {⟨false, false⟩, ⟨false, true⟩, ⟨true, false⟩, ⟨true, true⟩} := by
      ext ⟨a, b⟩; cases a <;> cases b <;> simp
    rw [huniv]
    simp [Finset.sum_insert, add_assoc]
  have hW0 : iceCreamEnv.optimalValue 0 2 s₀ = 23 / 2 := by
    unfold DynamicEnv.optimalValue DynamicEnv.bellmanValue
    rw [hsup3]
    simp only [hsum_states, iceCreamEnv, iceCreamTrans_toReal, DynamicEnv.totalVal, iceCreamVal,
      Fin.sum_univ_three, one_mul, s₀]
    have h1 : iceCreamEnv.bellmanValue iceCreamEnv.totalVal 1 1 ⟨false, false⟩ = 5 :=
      hW1 ⟨false, false⟩
    have h2 : iceCreamEnv.bellmanValue iceCreamEnv.totalVal 1 1 ⟨false, true⟩ = 10 :=
      hW1 ⟨false, true⟩
    have h3 : iceCreamEnv.bellmanValue iceCreamEnv.totalVal 1 1 ⟨true, false⟩ = 2 :=
      hW1 ⟨true, false⟩
    have h4 : iceCreamEnv.bellmanValue iceCreamEnv.totalVal 1 1 ⟨true, true⟩ = 10 :=
      hW1 ⟨true, true⟩
    dsimp only [iceCreamEnv] at h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    norm_num
  have hW0_no0 : iceCreamEnv.optimalValueWithout 0 0 2 s₀ = 10 := by
    unfold DynamicEnv.optimalValueWithout DynamicEnv.bellmanValue
    rw [hsup3]
    simp only [hsum_states, hothers, DynamicEnv.totalVal, Fin.sum_univ_three]
    have h1 : iceCreamEnv.bellmanValue (iceCreamEnv.othersVal 0) 1 1 ⟨false, false⟩ = 2 :=
      hW1_no0 ⟨false, false⟩
    have h2 : iceCreamEnv.bellmanValue (iceCreamEnv.othersVal 0) 1 1 ⟨false, true⟩ = 10 :=
      hW1_no0 ⟨false, true⟩
    have h3 : iceCreamEnv.bellmanValue (iceCreamEnv.othersVal 0) 1 1 ⟨true, false⟩ = 2 :=
      hW1_no0 ⟨true, false⟩
    have h4 : iceCreamEnv.bellmanValue (iceCreamEnv.othersVal 0) 1 1 ⟨true, true⟩ = 10 :=
      hW1_no0 ⟨true, true⟩
    rw [h1, h2, h3, h4]
    simp only [iceCreamEnv, iceCreamTrans_toReal, iceCreamVal, one_mul, s₀]
    norm_num
  have hW0_no1 : iceCreamEnv.optimalValueWithout 1 0 2 s₀ = 11 := by
    unfold DynamicEnv.optimalValueWithout DynamicEnv.bellmanValue
    rw [hsup3]
    simp only [hsum_states, hothers, DynamicEnv.totalVal, Fin.sum_univ_three]
    have h1 : iceCreamEnv.bellmanValue (iceCreamEnv.othersVal 1) 1 1 ⟨false, false⟩ = 5 :=
      hW1_no1 ⟨false, false⟩
    have h2 : iceCreamEnv.bellmanValue (iceCreamEnv.othersVal 1) 1 1 ⟨false, true⟩ = 10 :=
      hW1_no1 ⟨false, true⟩
    have h3 : iceCreamEnv.bellmanValue (iceCreamEnv.othersVal 1) 1 1 ⟨true, false⟩ = 2 :=
      hW1_no1 ⟨true, false⟩
    have h4 : iceCreamEnv.bellmanValue (iceCreamEnv.othersVal 1) 1 1 ⟨true, true⟩ = 10 :=
      hW1_no1 ⟨true, true⟩
    rw [h1, h2, h3, h4]
    simp only [iceCreamEnv, iceCreamTrans_toReal, iceCreamVal, one_mul, s₀]
    norm_num
  have hp1 : iceCreamEnv.pivotPayment 1 0 1 s₀ 2 = 7 / 2 := by
    unfold DynamicEnv.pivotPayment
    rw [hW0_no1, hothers]
    simp only [hsum_states, DynamicEnv.totalVal, iceCreamEnv, iceCreamTrans_toReal, iceCreamVal,
      Fin.sum_univ_three, one_mul, s₀]
    have h1 : iceCreamEnv.optimalValueWithout 1 1 1 ⟨false, false⟩ = 5 := hW1_no1 ⟨false, false⟩
    have h2 : iceCreamEnv.optimalValueWithout 1 1 1 ⟨false, true⟩ = 10 := hW1_no1 ⟨false, true⟩
    have h3 : iceCreamEnv.optimalValueWithout 1 1 1 ⟨true, false⟩ = 2 := hW1_no1 ⟨true, false⟩
    have h4 : iceCreamEnv.optimalValueWithout 1 1 1 ⟨true, true⟩ = 10 := hW1_no1 ⟨true, true⟩
    dsimp only [iceCreamEnv] at h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    norm_num
  have heval :
      iceCreamEnv.evalFrom iceCreamEnv.totalVal (iceCreamEnv.optimalPolicy 0 2 0) 0 2 [] s₀ =
        iceCreamEnv.optimalValue 0 2 s₀ := by
    simpa only [List.length_nil] using iceCreamEnv.evalFrom_optimalPolicy 0 2 [] s₀
  have hu0 : iceCreamEnv.agentUtility 0 (iceCreamEnv.optimalPolicy 0 2 0) 0 2 [] s₀ = 3 / 2 := by
    rw [iceCreamEnv.agentUtility_eq_totalVal_sub, heval, hW0, hW0_no0]
    norm_num
  have hu1 : iceCreamEnv.agentUtility 1 (iceCreamEnv.optimalPolicy 0 2 0) 0 2 [] s₀ = 1 / 2 := by
    rw [iceCreamEnv.agentUtility_eq_totalVal_sub, heval, hW0, hW0_no1]
    norm_num
  have hu0_dev :
      iceCreamEnv.agentUtility 0 (fun hs => if hs.length = 1 then 1 else 2) 0 2 [] s₀ = 1 := by
    rw [iceCreamEnv.agentUtility_eq_totalVal_sub, hW0_no0]
    simp only [DynamicEnv.evalFrom, DynamicEnv.totalVal, iceCreamEnv, iceCreamVal,
      Fin.sum_univ_three, one_mul, s₀, hsum_states, iceCreamTrans_toReal, List.length_cons,
      List.length_nil]
    norm_num
  exact ⟨hW0, hW0_no0, hW0_no1, hp1, hu0, hu1, hu0_dev⟩

/-- Dynamic VCG on `iceCreamEnv` is truthful and individually rational (non-vacuity witness),
and `optimalPolicyWithout` attains `optimalValueWithout` with zero pivot payment. -/
example :
    (∀ (i : Fin 3) (σ : List IceCreamState → IceCreamAction),
      iceCreamEnv.agentUtility i σ 0 2 [] ⟨false, false⟩ ≤
        iceCreamEnv.agentUtility i (iceCreamEnv.optimalPolicy 0 2 0) 0 2 [] ⟨false, false⟩ ∧
      0 ≤ iceCreamEnv.agentUtility i (iceCreamEnv.optimalPolicy 0 2 0) 0 2 [] ⟨false, false⟩) ∧
    iceCreamEnv.evalFrom (iceCreamEnv.othersVal 0)
      (iceCreamEnv.optimalPolicyWithout 0 0 2 0) 0 2 [] ⟨false, false⟩ = 10 ∧
    iceCreamEnv.pivotPayment 0 0 1 ⟨false, false⟩
      (iceCreamEnv.optimalPolicyWithout 0 0 2 0 [⟨false, false⟩]) = 0 := by
  refine ⟨fun i σ => ⟨iceCreamEnv.isTruthful i σ 0 2 [] ⟨false, false⟩,
    iceCreamEnv.isIR i (iceCream_val_nonneg i) 0 2 [] ⟨false, false⟩⟩, ?_, ?_⟩
  · have hno0 : iceCreamEnv.optimalValueWithout 0 0 2 ⟨false, false⟩ = 10 :=
      iceCream_dynamicVCG_witness.2.1
    rw [← hno0]
    simpa only [List.length_nil] using
      iceCreamEnv.evalFrom_optimalPolicyWithout 0 0 2 [] ⟨false, false⟩
  · exact iceCreamEnv.pivotPayment_optimalPolicyWithout 0 (t₀ := 0) (h₀ := 2) (len₀ := 0) (e := 0)
      [] rfl ⟨false, false⟩

end DynamicVCGWitness

/-! ### 4. Posted-Price Schedule & Geometric Threshold Auction Witnesses -/

section PostedPriceWitness

/-- A two-period decreasing agent-independent price schedule `q(0) = 10`, `q(1) = 4`. -/
private def decPriceSchedule : PriceSchedule (Fin 2) 2 where
  price _ t _ := if t = 0 then 10 else 4
  price_nonneg _ t _ := by split_ifs <;> norm_num
  price_update _ _ _ _ := rfl

/-- On `[0, 1]`, the critical value of `decPriceSchedule` is `min(10, 4) = 4`, whereas on `[0, 0]`
it is `10`. -/
theorem decPriceSchedule_criticalValues :
    let h01 : (0 : Fin 2) ≤ 1 := by decide
    let θ : Fin 2 → AgentType (Fin 2) := fun _ => mkType 0 1 h01 6 (by norm_num)
    decPriceSchedule.policy.criticalValue θ 0 0 1 h01 = ENNReal.ofReal 4 ∧
    decPriceSchedule.policy.criticalValue θ 0 0 0 le_rfl = ENNReal.ofReal 10 ∧
    decPriceSchedule.policy.criticalMechanism.IsDSIC := by
  intro h01 θ
  refine ⟨?_, ?_, decPriceSchedule.criticalMechanism_isDSIC⟩
  · rw [decPriceSchedule.criticalValue_eq_iInf]
    apply le_antisymm
    · exact iInf₂_le_of_le (1 : Fin 2) ⟨h01, le_rfl⟩ (by simp [decPriceSchedule])
    · refine le_iInf fun t => le_iInf fun _ => ?_
      fin_cases t
      · exact ENNReal.ofReal_le_ofReal (by simp [decPriceSchedule]; norm_num)
      · simp [decPriceSchedule]
  · rw [decPriceSchedule.criticalValue_eq_iInf]
    apply le_antisymm
    · exact iInf₂_le_of_le (0 : Fin 2) ⟨le_rfl, le_rfl⟩ (by simp [decPriceSchedule])
    · refine le_iInf fun t => le_iInf fun ht => ?_
      have ht0 : t = 0 := le_antisymm ht.2 ht.1
      subst ht0
      simp [decPriceSchedule]

/-- Checked witness for the geometric threshold single-item online auction over `[1, 8)` (`m = 3`,
`L = 1`): every realization is strongly truthful under arbitrary departure misreports and causal,
and on a 2-agent profile with maximum value `5 ∈ [1, 8)` both expected welfare and expected revenue
satisfy the `6`-competitive (`2 * 3`) bound. -/
example :
    let θ : Fin 2 → AgentType (Fin 2) :=
      ![mkType 0 0 le_rfl 3 (by norm_num), mkType 1 1 le_rfl 5 (by norm_num)]
    (∀ k : Fin 3,
      (thresholdSingleItemMechanism (ι := Fin 2) (T := 2)
        (1 * (2 : ℝ) ^ k.val)).IsDSICNoEarlyArrival ∧
      (thresholdSingleItemPolicy (ι := Fin 2) (T := 2) (1 * (2 : ℝ) ^ k.val)).IsCausal) ∧
    (5 : ℝ) ≤ (2 * (3 : ℝ)) *
      ((∑ k : Fin 3,
        welfare θ ((thresholdSingleItemPolicy (1 * (2 : ℝ) ^ k.val)).alloc θ)) / (3 : ℝ)) ∧
    (5 : ℝ) ≤ (2 * (3 : ℝ)) *
      ((∑ k : Fin 3,
        revenue (thresholdSingleItemMechanism (1 * (2 : ℝ) ^ k.val)) θ) / (3 : ℝ)) := by
  intro θ
  refine ⟨fun k => ⟨thresholdSingleItemMechanism_isDSICNoEarlyArrival (by positivity),
    thresholdSingleItemPolicy_isCausal _⟩, ?_, ?_⟩
  · exact geometricThreshold_expected_welfare (ι := Fin 2) (T := 2) (L := 1) (by norm_num)
      (m := 3) (by decide) (θ := θ) (i_max := 1) (by simp [θ]) (by simp [θ]; norm_num)
  · exact geometricThreshold_expected_revenue (ι := Fin 2) (T := 2) (L := 1) (by norm_num)
      (m := 3) (by decide) (θ := θ) (i_max := 1) (by simp [θ]) (by simp [θ]; norm_num)

end PostedPriceWitness

end CslibFrontierTests.OnlineMechanism
