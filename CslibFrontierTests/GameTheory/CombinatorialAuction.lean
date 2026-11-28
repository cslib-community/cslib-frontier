/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Walrasian
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Combinatorial auctions: checks for Walrasian equilibrium and LPR/DLPR

Nonvacuous client tests for `Cslib.GameTheory.CombinatorialAuction`:

* an additive 2-bidder, 3-item instance *with* a Walrasian equilibrium, demand ties, an unallocated
  zero-price item, a non-demand bundle, LP strong duality witness, and applications of Theorems
  11.13, 11.15 and Corollary 11.16;
* an equilibrium candidate that satisfies price nonnegativity and the demand condition for every
  bidder, failing *only* because an unallocated item has positive price;
* converting a non-trivial 0–1 `IsLPRFeasible` vector with an unassigned bidder (`∀ S, x i S = 0`)
  to an `Allocation` via `IsLPRFeasible.toAllocation`;
* a strictly fractional (`¬ IsIntegral`) feasible LPR allocation;
* tightness of Example 11.14 (`welfare = 3`, LPR optimum `7 / 2`, no integral LPR optimum);
* exact necessity of `∀ i, 0 ≤ v i ∅` across all three headlines: counterexamples when `v i ∅ < 0`
  for the fractional First Welfare Theorem (Theorem 11.13), the 0–1 form of the Second Welfare
  Theorem (Theorem 11.15), and both directions of Corollary 11.16 (empty-item unit case and a
  `-10`-shifted copy of Example 11.14);
* boundary cases: no items (`M = Empty`), no bidders (`N = Empty`), and one bidder (`N = Unit`).
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.CombinatorialAuction

open Finset Cslib.GameTheory.CombinatorialAuction

/-! ### 1. Positive instance: 2 bidders, 3 items with demand ties and an unallocated item -/

/-- Additive valuations for 2 bidders (`false` = Alice, `true` = Bob) over `Fin 3` items:
Alice has item values `(5, 4, 0)` and Bob has `(4, 5, 0)`. -/
private def addVal (i : Bool) (S : Finset (Fin 3)) : ℝ :=
  ∑ j ∈ S, (if i then (![4, 5, 0] : Fin 3 → ℝ) j else (![5, 4, 0] : Fin 3 → ℝ) j)

private def addPrice : Fin 3 → ℝ := ![4, 4, 0]

private def addAlloc : Allocation Bool (Fin 3) where
  bundle i := if i then {1} else {0}
  disjoint i₁ i₂ hne := by
    cases i₁ <;> cases i₂ <;> first | exact absurd rfl hne | exact by decide

private theorem addVal_empty (i : Bool) : addVal i ∅ = 0 := by
  simp [addVal]

/-- Supporting calculation: at `addPrice = (4, 4, 0)`, marginal utility is nonnegative only on
each bidder's preferred item (`1`), `0` on the other allocated item (`0`), and `0` on item `2`. -/
private theorem isDemand_addAlloc (i : Bool) :
    IsDemand (addVal i) addPrice (addAlloc.bundle i) := by
  intro S
  have hdiff : ∀ T : Finset (Fin 3), addVal i T - ∑ j ∈ T, addPrice j =
      ∑ j ∈ T, ((if i then (![4, 5, 0] : Fin 3 → ℝ) j else (![5, 4, 0] : Fin 3 → ℝ) j) -
        addPrice j) := fun T => by
    simp only [addVal, Finset.sum_sub_distrib]
  rw [hdiff S, hdiff (addAlloc.bundle i)]
  have hle : ∀ T : Finset (Fin 3),
      ∑ j ∈ T, ((if i then (![4, 5, 0] : Fin 3 → ℝ) j else (![5, 4, 0] : Fin 3 → ℝ) j) -
        addPrice j) ≤ 1 := by
    intro T
    cases i
    · have hsub : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
          0 ≤ (if j = (0 : Fin 3) then (1 : ℝ) else 0) := by
        intro j _; split_ifs <;> norm_num
      calc ∑ j ∈ T, ((![5, 4, 0] : Fin 3 → ℝ) j - addPrice j)
          = ∑ j ∈ T, (if j = (0 : Fin 3) then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            fin_cases j <;> norm_num [addPrice]
        _ ≤ ∑ j : Fin 3, (if j = (0 : Fin 3) then (1 : ℝ) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j hj _ => hsub j hj
        _ = 1 := by norm_num [Fin.sum_univ_three]
    · have hsub : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
          0 ≤ (if j = (1 : Fin 3) then (1 : ℝ) else 0) := by
        intro j _; split_ifs <;> norm_num
      calc ∑ j ∈ T, ((![4, 5, 0] : Fin 3 → ℝ) j - addPrice j)
          = ∑ j ∈ T, (if j = (1 : Fin 3) then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            fin_cases j <;> norm_num [addPrice]
        _ ≤ ∑ j : Fin 3, (if j = (1 : Fin 3) then (1 : ℝ) else 0) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j hj _ => hsub j hj
        _ = 1 := by norm_num [Fin.sum_univ_three]
  have hval : (∑ j ∈ addAlloc.bundle i,
      ((if i then (![4, 5, 0] : Fin 3 → ℝ) j else (![5, 4, 0] : Fin 3 → ℝ) j) -
        addPrice j)) = 1 := by
    cases i <;> norm_num [addAlloc, addPrice]
  exact (hle S).trans_eq hval.symm

private theorem isWalrasian_add : IsWalrasianEquilibrium addVal addPrice addAlloc where
  price_nonneg j := by fin_cases j <;> norm_num [addPrice]
  demand := isDemand_addAlloc
  unallocated_price_zero j hj := by
    fin_cases j
    · exact absurd (by simp [addAlloc]) (hj false)
    · exact absurd (by simp [addAlloc]) (hj true)
    · rfl

/-- Social welfare of `addAlloc` is `5 + 5 = 10`. -/
example : welfare addVal addAlloc = 10 := by
  simp only [welfare, Fintype.sum_bool, addAlloc, addVal]
  norm_num

/-- **Demand tie**: at `addPrice = (4, 4, 0)`, Alice (`false`) is indifferent among `{0}`,
`{0, 1}`, and `{0, 2}` (all give net utility `1`). -/
example : IsDemand (addVal false) addPrice {0, 1} ∧
    IsDemand (addVal false) addPrice {0, 2} := by
  have hbase := isDemand_addAlloc false
  have h01 : addVal false {0, 1} - ∑ j ∈ ({0, 1} : Finset (Fin 3)), addPrice j =
      addVal false (addAlloc.bundle false) - ∑ j ∈ addAlloc.bundle false, addPrice j := by
    norm_num [addVal, addPrice, addAlloc]
  have h02 : addVal false {0, 2} - ∑ j ∈ ({0, 2} : Finset (Fin 3)), addPrice j =
      addVal false (addAlloc.bundle false) - ∑ j ∈ addAlloc.bundle false, addPrice j := by
    norm_num [addVal, addPrice, addAlloc]
  exact ⟨fun S => (hbase S).trans_eq h01.symm, fun S => (hbase S).trans_eq h02.symm⟩

/-- **Non-demand bundle**: `{1}` is NOT a demand of Alice at `addPrice` (utility `0 < 1`). -/
example : ¬ IsDemand (addVal false) addPrice {1} := by
  intro h
  have h0 := h {0}
  norm_num [addVal, addPrice] at h0

/-- **Swapped allocation welfare bound** via Theorem 11.13 (`welfare_le`): giving `{1}` to Alice
and `{0}` to Bob gives welfare `8 ≤ 10`. -/
example : ∃ b : Allocation Bool (Fin 3), welfare addVal b = 8 ∧
    welfare addVal b ≤ welfare addVal addAlloc := by
  let b : Allocation Bool (Fin 3) :=
    ⟨fun i => if i then {0} else {1}, fun i₁ i₂ hne => by
      cases i₁ <;> cases i₂ <;> first | exact absurd rfl hne | exact by decide⟩
  exact ⟨b, by simp only [welfare, Fintype.sum_bool, b, addVal]; norm_num,
    isWalrasian_add.welfare_le b⟩

/-- **Nonvacuity of Theorems 11.13, 11.15, and Corollary 11.16**: `addAlloc` is LPR-optimal via
`lprObjective_le`, triggers `exists_isWalrasianEquilibrium_of_lprObjective_le`,
`exists_isWalrasianEquilibrium_of_isIntegral`, and `exists_isWalrasianEquilibrium_iff`. -/
example : (∃ p, IsWalrasianEquilibrium addVal p addAlloc) ∧
    (∃ x, IsLPROptimal addVal x ∧ IsIntegral x) := by
  have hopt : ∀ x, IsLPRFeasible x → lprObjective addVal x ≤ welfare addVal addAlloc :=
    fun x hx => isWalrasian_add.lprObjective_le (fun i => (addVal_empty i).ge) hx
  have h2 := exists_isWalrasianEquilibrium_of_lprObjective_le hopt
  have hint : IsLPROptimal addVal addAlloc.indicator ∧ IsIntegral addAlloc.indicator :=
    ⟨⟨addAlloc.indicator_isLPRFeasible, fun y hy => by
        simpa only [Allocation.lprObjective_indicator] using hopt y hy⟩,
      addAlloc.indicator_isIntegral⟩
  have _h2int := exists_isWalrasianEquilibrium_of_isIntegral (fun i => (addVal_empty i).ge)
    hint.1 hint.2
  have _hcor := (exists_isWalrasianEquilibrium_iff (fun i => (addVal_empty i).ge)).mp
    ⟨addPrice, addAlloc, isWalrasian_add⟩
  exact ⟨h2, addAlloc.indicator, hint⟩

/-- Positive test for LP strong duality `exists_lpr_dlpr_eq`: the common primal/dual optimum on
`addVal` equals `10`. -/
example : ∃ x u p, IsLPRFeasible x ∧ IsDLPRFeasible addVal u p ∧
    lprObjective addVal x = 10 ∧ dlprObjective u p = 10 := by
  obtain ⟨x, u, p, hx, hup, heq⟩ := exists_lpr_dlpr_eq addVal
  have hle : lprObjective addVal x ≤ 10 := by
    have h1 := isWalrasian_add.lprObjective_le (fun i => (addVal_empty i).ge) hx
    have hw : welfare addVal addAlloc = 10 := by
      simp only [welfare, Fintype.sum_bool, addAlloc, addVal]; norm_num
    linarith
  have hge : 10 ≤ dlprObjective u p := by
    have h1 := lprObjective_le_dlprObjective addAlloc.indicator_isLPRFeasible hup
    have hw : lprObjective addVal addAlloc.indicator = 10 := by
      simp only [Allocation.lprObjective_indicator, welfare, Fintype.sum_bool, addAlloc, addVal]
      norm_num
    linarith
  exact ⟨x, u, p, hx, hup, by linarith, by linarith⟩

/-! ### 2. Unallocated item with positive price fails Walrasian equilibrium -/

/-- With one bidder valuing `{false}` at `2` (`0` for `{true}`, `2` for `{false, true}`), prices
`p = (1, 1)` give `0 ≤ p` and make `{false}` a demand (`2 - 1 = 1`), yet fail
`IsWalrasianEquilibrium` *only* because the unallocated item `true` has positive price `1`. -/
example : let v : Unit → Finset Bool → ℝ := fun _ S => if false ∈ S then 2 else 0
    let p : Bool → ℝ := fun _ => 1
    let a : Allocation Unit Bool :=
      ⟨fun _ => {false}, fun i₁ i₂ h => absurd (Subsingleton.elim i₁ i₂) h⟩
    (∀ j, 0 ≤ p j) ∧ (∀ i, IsDemand (v i) p (a.bundle i)) ∧
      ¬ IsWalrasianEquilibrium v p a := by
  intro v p a
  refine ⟨fun _ => zero_le_one, fun () S => ?_, fun h => ?_⟩
  · have hfa : a.bundle () = {false} := rfl
    rw [hfa]
    dsimp only [v, p]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mem_singleton, ↓reduceIte,
      Finset.card_singleton, Nat.cast_one]
    split_ifs with hf
    · have hc : (1 : ℝ) ≤ (S.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr ⟨false, hf⟩
      linarith
    · have : (0 : ℝ) ≤ (S.card : ℝ) := Nat.cast_nonneg _
      linarith
  · have h0 := h.unallocated_price_zero true (fun () => by decide)
    norm_num [p] at h0

/-! ### 3. `0`-`1` feasible LPR vector with an unassigned bidder via `toAllocation` -/

/-- When bidder `true` has `∀ S, x true S = 0` and bidder `false` has `x false {false} = 1`,
`hx.toAllocation` assigns `{false}` to `false` and `∅` to `true`, matching the objective. -/
example : let x : Bool → Finset Bool → ℝ :=
      fun i S => if i = false ∧ S = {false} then 1 else 0
    ∃ hx : IsLPRFeasible x, IsIntegral x ∧
      hx.toAllocation.bundle false = {false} ∧
      hx.toAllocation.bundle true = ∅ := by
  intro x
  have hx : IsLPRFeasible x :=
    { item_le := fun j => by
        rw [Fintype.sum_bool]
        cases j
        · have hT : ∑ S : Finset Bool with false ∈ S, x true S = 0 :=
            Finset.sum_eq_zero fun S _ => by simp [x]
          rw [hT, zero_add]
          have hF : ∑ S : Finset Bool with false ∈ S, x false S = 1 := by
            rw [Finset.sum_eq_single {false}]
            · simp [x]
            · intro S _ hne; simp [x, hne]
            · intro hmem; exact absurd (by decide) hmem
          linarith
        · have : ∀ i S, true ∈ S → x i S = 0 := by
            intro i S hS
            simp only [x]
            split_ifs with h
            · rw [h.2] at hS; exact absurd hS (by decide)
            · rfl
          simp [Finset.sum_eq_zero fun S hS => this _ S (Finset.mem_filter.mp hS).2]
      bidder_le := fun i => by
        cases i
        · rw [Finset.sum_eq_single {false}] <;> simp [x]
        · simp [x]
      nonneg := fun i S => by dsimp only [x]; split_ifs <;> norm_num }
  have hint : IsIntegral x := fun i S => by dsimp only [x]; split_ifs <;> simp
  refine ⟨hx, hint, ?_, ?_⟩
  · exact hx.toAllocation_bundle_eq_of_eq_one (by simp [x])
  · exact hx.toAllocation_bundle_eq_empty (fun S => by simp [x])

/-! ### 4. Example 11.14 tightness, fractional solution, and Corollary 11.16 -/

/-- `noEquilibriumVal` achieves integral welfare `3` (so `welfare_noEquilibriumVal_le` is tight). -/
example : ∃ a : Allocation Bool Bool, welfare noEquilibriumVal a = 3 := by
  let a : Allocation Bool Bool :=
    ⟨fun i => if i then Finset.univ else ∅, fun i₁ i₂ h => by
      cases i₁ <;> cases i₂
      · exact absurd rfl h
      · exact Finset.disjoint_empty_left _
      · exact Finset.disjoint_empty_right _
      · exact absurd rfl h⟩
  exact ⟨a, by simp [welfare, a, noEquilibriumVal]⟩

/-- By Corollary 11.16, `noEquilibriumVal` has NO integral (0–1) optimal solution in LPR, and the
optimal solution `x` witnessing `7 / 2` is genuinely fractional (`¬ IsIntegral x`). -/
example : ¬ ∃ x, IsLPROptimal noEquilibriumVal x ∧ IsIntegral x := by
  intro h
  exact not_exists_isWalrasianEquilibrium_noEquilibriumVal
    ((exists_isWalrasianEquilibrium_iff (fun i => (noEquilibriumVal_empty i).ge)).mpr h)

example : ∃ x, IsLPROptimal noEquilibriumVal x ∧ ¬ IsIntegral x := by
  obtain ⟨x, hx, hval⟩ := exists_isLPROptimal_noEquilibriumVal
  refine ⟨x, hx, fun hint => ?_⟩
  have hno := not_exists_isWalrasianEquilibrium_noEquilibriumVal
  exact hno ((exists_isWalrasianEquilibrium_iff (fun i => (noEquilibriumVal_empty i).ge)).mpr
    ⟨x, hx, hint⟩)

/-! ### 5. Exact necessity of `∀ i, 0 ≤ v i ∅` (three counterexamples) -/

/-- **Counterexample 1 (fractional Theorem 11.13 & forward Corollary 11.16)**: with `v () ∅ = -1`,
`(0, ∅)` is a Walrasian equilibrium of welfare `-1`, while `x = 0` is LPR-feasible with objective
`0 > -1`. Thus neither `lprObjective_le` nor the allocation form of Corollary 11.16 holds without
`∀ i, 0 ≤ v i ∅`. (The integral form `welfare_le` still holds.) -/
example : let v : Unit → Finset Empty → ℝ := fun _ _ => -1
    let a : Allocation Unit Empty := ⟨fun _ => ∅, fun i₁ i₂ h => absurd (Subsingleton.elim i₁ i₂) h⟩
    IsWalrasianEquilibrium v (fun _ => 0) a ∧
      (∀ b : Allocation Unit Empty, welfare v b ≤ welfare v a) ∧
      ∃ x, IsLPRFeasible x ∧ welfare v a < lprObjective v x := by
  intro v a
  have heq : IsWalrasianEquilibrium v (fun _ => 0) a :=
    { price_nonneg := fun e => e.elim
      demand := fun _ S => by simp [v]
      unallocated_price_zero := fun e _ => e.elim }
  refine ⟨heq, fun b => heq.welfare_le b, fun _ _ => 0, isLPRFeasible_zero, ?_⟩
  simp [welfare, lprObjective, v]

/-- **Counterexample 2 (`0`-`1` Second Welfare Theorem)**: with one bidder and one item `()`,
`v () ∅ = -5` and `v () {()} = -1`, `x = 0` is an integral optimal solution of LPR (value `0`),
yet its induced allocation `toAllocation` assigns `∅` and has *no* supporting Walrasian prices
(unallocated `()` forces `p () = 0`, under which `{()}` beats `∅`). -/
example : let v : Unit → Finset Unit → ℝ := fun _ S => if S = ∅ then -5 else -1
    let x : Unit → Finset Unit → ℝ := fun _ _ => 0
    ∃ hopt : IsLPROptimal v x, IsIntegral x ∧
      ¬ ∃ p : Unit → ℝ, IsWalrasianEquilibrium v p hopt.1.toAllocation := by
  intro v x
  have hopt : IsLPROptimal v x := by
    refine ⟨isLPRFeasible_zero, fun y hy => ?_⟩
    have hl : lprObjective v x = 0 := by simp [lprObjective, x]
    rw [hl]
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun S _ => ?_
    refine mul_nonpos_of_nonneg_of_nonpos (hy.nonneg i S) ?_
    dsimp only [v]; split_ifs <;> norm_num
  have hint : IsIntegral x := fun _ _ => .inl rfl
  refine ⟨hopt, hint, fun ⟨p, hp⟩ => ?_⟩
  have hbundle : hopt.1.toAllocation.bundle () = ∅ :=
    hopt.1.toAllocation_bundle_eq_empty (fun _ => rfl)
  have hp0 : p () = 0 := hp.unallocated_price_zero () fun i => by
    cases i; rw [hbundle]; exact Finset.notMem_empty ()
  have hdem := hp.demand () {()}
  rw [hbundle] at hdem
  simp only [Finset.sum_singleton, Finset.sum_empty, sub_zero, hp0, v, ↓reduceIte,
    (Finset.singleton_nonempty _).ne_empty] at hdem
  linarith

/-- **Counterexample 3 (backward Corollary 11.16)**: shifting `noEquilibriumVal` by `-10` yields a
valuation profile where every value is `≤ -7 < 0`, so `x = 0` is an integral optimal solution of
LPR (objective `0`). Shifting by a constant preserves `IsDemand`, so no Walrasian equilibrium
exists. -/
example : let v : Bool → Finset Bool → ℝ := fun i S => noEquilibriumVal i S - 10
    (∃ x, IsLPROptimal v x ∧ IsIntegral x) ∧
      ¬ ∃ (p : Bool → ℝ) (a : Allocation Bool Bool), IsWalrasianEquilibrium v p a := by
  intro v
  constructor
  · refine ⟨fun _ _ => 0, ⟨isLPRFeasible_zero, fun y hy => ?_⟩, fun _ _ => .inl rfl⟩
    have h0 : lprObjective v (fun _ _ => 0) = 0 := by simp [lprObjective]
    rw [h0]
    refine Finset.sum_nonpos fun i _ => Finset.sum_nonpos fun S _ =>
      mul_nonpos_of_nonneg_of_nonpos (hy.nonneg i S) ?_
    dsimp only [v, noEquilibriumVal]
    cases i <;> split_ifs <;> norm_num
  · rintro ⟨p, a, heq⟩
    apply not_exists_isWalrasianEquilibrium_noEquilibriumVal
    refine ⟨p, a, heq.price_nonneg, fun i S => ?_, heq.unallocated_price_zero⟩
    have h := heq.demand i S
    dsimp only [v] at h
    linarith

/-! ### 6. Degenerate boundary cases: empty items, empty bidders, single bidder -/

/-- No items (`M = Empty`): every profile has a Walrasian equilibrium at zero prices. -/
example (v : Bool → Finset Empty → ℝ) :
    ∃ (p : Empty → ℝ) (a : Allocation Bool Empty), IsWalrasianEquilibrium v p a :=
  ⟨Empty.elim, ⟨fun _ => ∅, fun _ _ _ => Finset.disjoint_empty_left _⟩,
    fun e => e.elim, fun i S => by simp [Finset.eq_empty_of_isEmpty S], fun e _ => e.elim⟩

/-- No bidders (`N = Empty`): zero prices clear the market since every item is unallocated. -/
example (v : Empty → Finset Bool → ℝ) :
    ∃ (p : Bool → ℝ) (a : Allocation Empty Bool), IsWalrasianEquilibrium v p a :=
  ⟨fun _ => 0, ⟨Empty.elim, fun e => e.elim⟩,
    fun _ => le_rfl, fun e => e.elim, fun _ _ => rfl⟩

/-- Single bidder (`N = Unit`): any demand bundle at zero prices is a Walrasian equilibrium. -/
example (v : Unit → Finset Bool → ℝ) :
    ∃ (p : Bool → ℝ) (a : Allocation Unit Bool), IsWalrasianEquilibrium v p a := by
  obtain ⟨T, hT⟩ := exists_isDemand (v ()) (fun _ => 0)
  exact ⟨fun _ => 0,
    ⟨fun _ => T, fun i₁ i₂ h => absurd (Subsingleton.elim i₁ i₂) h⟩,
    fun _ => le_rfl, fun () => hT, fun _ _ => rfl⟩

end CslibFrontierTests.GameTheory.CombinatorialAuction
