/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

public import CslibFrontier.Algorithms.Lean.HousingMarket.EndowmentManipulation
public import CslibFrontier.Algorithms.Lean.StableMatching.Adachi
public import CslibFrontier.Algorithms.Lean.StableMatching.Incentives
public import CslibFrontier.Algorithms.Lean.StableMatching.ManyToOne
public import CslibFrontier.Algorithms.Lean.StableMatching.Polytope
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Stable matching extensions and TTC pre-trade manipulation: checked instances

Public-surface client tests (`module`, no `import all`, no `native_decide`) exercising the NRTV
Chapter 10 (§10.4 and Exercise 10.7) extensions:

1. **Adachi's pre-matching operator (`Adachi.lean`, NRTV §10.4.1, Theorem 10.14, pp. 259–260):** on
   Roth's `3 × 3` market, `adachiMap` fixes the two embedded stable matchings, moves the unstable
   identity matching, and has distinct greatest and least fixed points `adachiMap.gfp ≠
   adachiMap.lfp`.
2. **Fractional stable matching polytope (`Polytope.lean`, NRTV §10.4.2, Theorem 10.15, p. 261):**
   * On Roth's `3 × 3` market, the non-integral midpoint
     `1/2 • matchingMatrix μa + 1/2 • matchingMatrix μb` belongs to `stablePolytope`, satisfies
     tight positive-support slackness, and is **not** an extreme point, whereas both
     `matchingMatrix μa` and `matchingMatrix μb` are extreme points.
   * On a `2 × 2` market where proposer `0` and receiver `0` rank each other first, the uniform
     doubly-stochastic matrix `(fun _ _ => 1/2)` violates Vande Vate's inequality at `(0, 0)` and
     lies strictly outside `stablePolytope`.
3. **Many-to-one Hospitals–Residents & Roth's Rural Hospitals Theorem (`ManyToOne.lean`, NRTV
   §10.4.3 quota model, p. 261; [Roth1986]):** a `4`-resident, `3`-hospital market
   (`quota = ![2, 1, 2]`) with two distinct stable matchings `M₁ ≠ M₂` in which:
   * Full hospitals `0` (`card = 2 = quota 0`) and `1` (`card = 1 = quota 1`) change their assigned
     resident sets (`M₁.residents 0 ≠ M₂.residents 0`), demonstrating tightness of the
     `card < quota` hypothesis;
   * Under-subscribed rural hospital `2` (`card = 1 < 2 = quota 2`) receives the exact same
     resident set `{3}` in every stable matching (`residents_eq_of_card_lt_quota`).
4. **Stable Roommates nonexistence (NRTV §10.4.3, pp. 261–262):** Gale–Shapley's `4`-agent cyclic
   roommates profile admits no fixed-point-free involution without a blocking pair.
5. **TTC pre-trade endowment manipulation (`EndowmentManipulation.lean`, NRTV Exercise 10.7,
   p. 265):** on `weakPreTradeInstance` (`n = 3`), swapping endowments inside `S = {0, 2}` changes
   TTC from `![1, 0, 2]` to `![1, 2, 0]`, giving weak coalitional improvement while confirming that
   strict coalitional improvement for all members of `S` is impossible.
-/

public section

namespace CslibFrontierTests.StableMatchingExtensions

open Cslib.Algorithms.Lean.StableMatching
open Cslib.Algorithms.Lean.HousingMarket

/-! ### 1. Adachi's Tarski fixed-point characterization (Theorem 10.14) -/

abbrev roth : Cslib.Algorithms.Lean.StableMatching.Instance 3 :=
  MatchingMechanism.rothInstance

abbrev μa : Matching 3 := MatchingMechanism.rothProposerOptimal
abbrev μb : Matching 3 := MatchingMechanism.rothReceiverOptimal

abbrev embedRoth (μ : Matching 3) : roth.PreMatching :=
  Cslib.Algorithms.Lean.StableMatching.Instance.PreMatching.ofMatching roth μ

example : roth.adachiMap (embedRoth μa) = embedRoth μa := by decide

example : roth.adachiMap (embedRoth μb) = embedRoth μb := by decide

example : roth.adachiMap (embedRoth 1) ≠ embedRoth 1 := by decide

example : roth.adachiMap.gfp ≠ roth.adachiMap.lfp := by
  rw [roth.adachiMap_gfp, roth.adachiMap_lfp]
  intro h
  have heq : roth.deferredAcceptance = roth.receiverDeferredAcceptance :=
    Cslib.Algorithms.Lean.StableMatching.Instance.PreMatching.ofMatching_injective h
  have hne : roth.deferredAcceptance ≠ roth.receiverDeferredAcceptance := by decide
  exact hne heq

example : Fintype.card (Function.fixedPoints roth.adachiMap) = 2 := by
  rw [Fintype.card_congr roth.fixedPointsOrderIsoStable.toEquiv]
  decide

/-! ### 2. Fractional stable matching polytope (Theorem 10.15) -/

/-- Non-integral midpoint of the two stable matchings of Roth's `3 × 3` market. -/
noncomputable def rothMidpoint : Fin 3 → Fin 3 → ℝ :=
  (1 / 2 : ℝ) • matchingMatrix μa + (1 / 2 : ℝ) • matchingMatrix μb

example : rothMidpoint ∈ roth.stablePolytope ∧
    rothMidpoint 1 0 = 1 / 2 ∧
    rothMidpoint ∉ roth.stablePolytope.extremePoints ℝ ∧
    matchingMatrix μa ∈ roth.stablePolytope.extremePoints ℝ ∧
    matchingMatrix μb ∈ roth.stablePolytope.extremePoints ℝ := by
  have hstab_a : roth.IsStable μa := by decide
  have hstab_b : roth.IsStable μb := by decide
  have hmem_a : matchingMatrix μa ∈ roth.stablePolytope :=
    (roth.matchingMatrix_mem_stablePolytope_iff μa).2 hstab_a
  have hmem_b : matchingMatrix μb ∈ roth.stablePolytope :=
    (roth.matchingMatrix_mem_stablePolytope_iff μb).2 hstab_b
  have hmid_mem : rothMidpoint ∈ roth.stablePolytope :=
    roth.convex_stablePolytope hmem_a hmem_b (by norm_num) (by norm_num) (by norm_num)
  have hmid_entry : rothMidpoint 1 0 = 1 / 2 := by
    have ha1 : μa 1 = 0 := by decide
    have hb1 : μb 1 = 2 := by decide
    simp [rothMidpoint, matchingMatrix, ha1, hb1]
  refine ⟨hmid_mem, hmid_entry, ?_, ?_, ?_⟩
  · rw [roth.extremePoints_stablePolytope]
    rintro ⟨μ, -, hμ_eq⟩
    have hval := congrFun (congrFun hμ_eq 1) 0
    rw [hmid_entry] at hval
    simp only [matchingMatrix] at hval
    split_ifs at hval <;> norm_num at hval
  · rw [roth.extremePoints_stablePolytope]
    exact ⟨μa, hstab_a, rfl⟩
  · rw [roth.extremePoints_stablePolytope]
    exact ⟨μb, hstab_b, rfl⟩

example : rothMidpoint 1 0 + roth.propBetterMass rothMidpoint 1 0 +
    roth.recvBetterMass rothMidpoint 0 1 = 1 := by
  have hstab_a : roth.IsStable μa := by decide
  have hstab_b : roth.IsStable μb := by decide
  have hmid_mem : rothMidpoint ∈ roth.stablePolytope :=
    roth.convex_stablePolytope
      ((roth.matchingMatrix_mem_stablePolytope_iff μa).2 hstab_a)
      ((roth.matchingMatrix_mem_stablePolytope_iff μb).2 hstab_b)
      (by norm_num) (by norm_num) (by norm_num)
  have hpos : 0 < rothMidpoint 1 0 := by
    have ha1 : μa 1 = 0 := by decide
    have hb1 : μb 1 = 2 := by decide
    simp only [rothMidpoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul, matchingMatrix, ha1, hb1,
      ↓reduceIte, Fin.reduceEq]
    norm_num
  exact roth.eq_one_of_mem_stablePolytope_of_pos hmid_mem hpos

/-- A `2 × 2` market where proposer `0` and receiver `0` rank each other first: the uniform doubly
stochastic matrix `(fun _ _ => 1/2)` is **not** in `stablePolytope` because `(0, 0)` fractionally
blocks it (`1/2 + 0 + 0 < 1`). -/
def alignedTwo : Cslib.Algorithms.Lean.StableMatching.Instance 2 where
  propPref := ![permOfInjective ![0, 1], permOfInjective ![0, 1]]
  recvPref := ![permOfInjective ![0, 1], permOfInjective ![0, 1]]

example : (fun _ _ : Fin 2 => (1 / 2 : ℝ)) ∉ alignedTwo.stablePolytope := by
  rintro ⟨-, -, -, hstab⟩
  have h00 := hstab 0 0
  have hp0 : alignedTwo.propBetterMass (fun _ _ => (1 / 2 : ℝ)) 0 0 = 0 := by
    refine Finset.sum_eq_zero fun r' hr' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
    have hr0 : alignedTwo.propRank 0 0 = 0 := by decide
    rw [hr0] at hr'
    exact False.elim (Nat.not_lt_zero _ hr')
  have hr0 : alignedTwo.recvBetterMass (fun _ _ => (1 / 2 : ℝ)) 0 0 = 0 := by
    refine Finset.sum_eq_zero fun p' hp' => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp'
    have hp00 : alignedTwo.recvRank 0 0 = 0 := by decide
    rw [hp00] at hp'
    exact False.elim (Nat.not_lt_zero _ hp')
  rw [hp0, hr0] at h00
  norm_num at h00

/-! ### 3. Many-to-one Hospitals–Residents & Rural Hospitals Theorem -/

/-- A `4`-resident, `3`-hospital market (`quota = ![2, 1, 2]`) where hospitals `0` and `1` fill
their quotas with different resident sets across stable matchings (`{0, 1}` vs `{0, 2}` at
multi-seat hospital `0`), while rural hospital `2` is under-subscribed (`card = 1 < 2`) and always
receives `{3}` (resident `3` applies first to hospital `1`, is rejected when `1` fills, and lands
at hospital `2`). -/
def ruralMarket : ManyToOneInstance 4 3 where
  resPref := ![[0], [0, 1], [1, 0], [1, 2]]
  hospPref := ![[2, 0, 1], [1, 2, 3], [3, 0, 1, 2]]
  quota := ![2, 1, 2]

/-- Resident-optimal stable matching on `ruralMarket`. -/
def ruralResOptimal : ManyToOneMatching 4 3 where
  hospital := ![some 0, some 0, some 1, some 2]

/-- Hospital-optimal stable matching on `ruralMarket`, differing from `ruralResOptimal` on
residents `1` and `2`. -/
def ruralHospOptimal : ManyToOneMatching 4 3 where
  hospital := ![some 0, some 1, some 0, some 2]

example : ruralMarket.IsStable ruralResOptimal ∧
    ruralMarket.IsStable ruralHospOptimal ∧
    ruralResOptimal ≠ ruralHospOptimal := by decide

-- Full hospitals `0` (`quota = 2`) and `1` (`quota = 1`) change their assigned resident sets across
-- stable matchings, showing that the `card < quota` hypothesis of Rural Hospitals Part 3 is tight:
example : ruralResOptimal.residents 0 = {0, 1} ∧
    ruralHospOptimal.residents 0 = {0, 2} ∧
    ruralResOptimal.residents 0 ≠ ruralHospOptimal.residents 0 ∧
    ruralResOptimal.residents 1 = {2} ∧
    ruralHospOptimal.residents 1 = {1} := by decide

-- Under-subscribed rural hospital `2` (`card = 1 < 2 = quota 2`) receives the exact same resident
-- set `{3}` in EVERY stable matching (including `ruralMarket.deferredAcceptance`):
example (M : ManyToOneMatching 4 3) (hM : ruralMarket.IsStable M) :
    M.residents 2 = {3} := by
  have hres : ruralMarket.IsStable ruralResOptimal := by decide
  have hlt : (ruralResOptimal.residents 2).card < ruralMarket.quota 2 := by decide
  have heq := ruralMarket.residents_eq_of_card_lt_quota hres hM hlt
  have hset : ruralResOptimal.residents 2 = {3} := by decide
  exact heq.symm.trans hset

example : ruralMarket.deferredAcceptance.residents 2 = {3} ∧
    ruralMarket.deferredAcceptance.matchedResidents = {0, 1, 2, 3} := by
  have hda : ruralMarket.IsStable ruralMarket.deferredAcceptance :=
    ruralMarket.isStable_deferredAcceptance
  have hres : ruralMarket.IsStable ruralResOptimal := by decide
  have hlt : (ruralResOptimal.residents 2).card < ruralMarket.quota 2 := by decide
  have hset : ruralResOptimal.residents 2 = {3} := by decide
  have hmatched : ruralResOptimal.matchedResidents = {0, 1, 2, 3} := by decide
  exact ⟨(ruralMarket.residents_eq_of_card_lt_quota hres hda hlt).symm.trans hset,
    (ruralMarket.matchedResidents_eq_of_isStable hda hres).trans hmatched⟩

/-! ### 4. Stable Roommates nonexistence witness (NRTV §10.4.3) -/

/-- Gale and Shapley's `4`-agent roommates preference profile ([GaleShapley1962];
[SchummerVohra2007], Section 10.4.3, pp. 261–262, prose on p. 261 and table on p. 262): agents
`0, 1, 2` rank each other cyclically (`0` prefers `1 > 2`, `1` prefers `2 > 0`, `2` prefers `0 > 1`;
the printed table on p. 262 uses the opposite cyclic orientation and prints a typo `2, 1, 4` in
column `≻_4`) and everyone ranks agent `3` last. No fixed-point-free involution
`μ : Equiv.Perm (Fin 4)` is free of blocking pairs. -/
def roommatesRank : Fin 4 → Fin 4 → Nat
  | 0 => ![3, 0, 1, 2]
  | 1 => ![1, 3, 0, 2]
  | 2 => ![0, 1, 3, 2]
  | 3 => ![0, 1, 2, 3]

example : ¬ ∃ μ : Equiv.Perm (Fin 4),
    (∀ i : Fin 4, μ i ≠ i ∧ μ (μ i) = i) ∧
    ∀ i j : Fin 4, i ≠ j →
      ¬ (roommatesRank i j < roommatesRank i (μ i) ∧
         roommatesRank j i < roommatesRank j (μ j)) := by decide

/-! ### 5. TTC pre-trade endowment manipulation (NRTV Exercise 10.7) -/

example : (∀ i : Fin 3, weakPreTradeInstance.ttc i = (![1, 0, 2] : Fin 3 → Fin 3) i) ∧
    (∀ i : Fin 3,
      weakPreTradeInstance.preTradeTTC (Equiv.swap 0 2) i = (![1, 2, 0] : Fin 3 → Fin 3) i) := by
  decide

example (S : Finset (Fin 3)) (hS : S.Nonempty) (σ : Allocation 3)
    (hsupp : ∀ i, i ∉ S → σ i = i) :
    ¬ ∀ i ∈ S,
      weakPreTradeInstance.rank i (weakPreTradeInstance.preTradeTTC σ i) <
        weakPreTradeInstance.rank i (weakPreTradeInstance.ttc i) :=
  weakPreTradeInstance.not_forall_rank_preTradeTTC_lt hS hsupp

end CslibFrontierTests.StableMatchingExtensions
