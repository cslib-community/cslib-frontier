/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.QueryComplexity
import CslibFrontier.GameTheory.Mechanism.CombinatorialAuction.Communication
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Combinatorial auctions: checks for query complexity and communication lower bounds

Nonvacuous client tests for `QueryComplexity` and `Communication` under
`CslibFrontier.GameTheory.Mechanism.CombinatorialAuction`:

* `valueQueryProg` and `marginalValueProg` on concrete `m = 2` (`Fin 2`) and `m = 3` (`Fin 3`)
  normalized monotone `3`-bit integer valuations (`t = 3`), checking exact recovered values and
  query counts `S.card * t ≤ m * t`, plus the `t = 0` zero-query boundary;
* Lemma 11.23 (`C(4, 2) = 6` value-query lower bound) and Exercise 11.3 (`1` demand query vs.
  `≥ 5` value queries) on `m = 4` (`Fin 4`), including concrete welfare checks on
  `oneDemandQueryOptimalAlloc` and the exponential central-binomial growth check;
* DLPR demand-query separation oracle (`dlprBidderCheckProg`, `isDLPRFeasible_iff_of_isValidOracle`,
  `isDLPRFeasible_iff_dlprBidderCheckProg`) on both a feasible `(u, p)` pair and an infeasible pair
  returning an explicit violated constraint `some D`;
* `MonotoneZeroOneVal.dual` normalization and complementarity `v(S) + v*(Sᶜ) = 1`, Lemma 11.26,
  and Theorem 11.25 on `m = 2` (`≥ 2` bits) and `m = 4` (`≥ 6` bits);
* sharpness boundary witnesses: `m = 0` (`Empty`) admits a `0`-bit protocol while `0.choose 0 = 1`,
  and dropping normalization (`u ≡ 0, v ≡ 1`) refutes the literal unnormalized Lemma 11.26.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.GameTheory.CombinatorialAuctionQueryComm

open Finset Cslib Cslib.Query Cslib.Communication Cslib.GameTheory.CombinatorialAuction

/-! ### 1. Lemma 11.22: value-query simulation via demand queries (`m = 2`, `m = 3`, `t = 3`) -/

/-- Supermodular `3`-bit integer valuation on `Fin 2`:
`∅ ↦ 0`, `{0} ↦ 2`, `{1} ↦ 3`, `{0, 1} ↦ 7`. -/
private def val2Nat (S : Finset (Fin 2)) : ℕ :=
  (if (0 : Fin 2) ∈ S then 2 else 0) +
  (if (1 : Fin 2) ∈ S then 3 else 0) +
  (if (0 : Fin 2) ∈ S ∧ (1 : Fin 2) ∈ S then 2 else 0)

private def val2 (S : Finset (Fin 2)) : ℝ := (val2Nat S : ℝ)

private theorem val2_empty : val2 ∅ = 0 := by simp [val2, val2Nat]

private theorem val2_monotone : Monotone val2 := by
  intro S T hST
  have hnat : val2Nat S ≤ val2Nat T := by
    unfold val2Nat
    have h0 : (if (0 : Fin 2) ∈ S then 2 else 0) ≤ if (0 : Fin 2) ∈ T then 2 else 0 := by
      split_ifs with h1 h2 <;> try omega
      exact absurd (hST h1) h2
    have h1 : (if (1 : Fin 2) ∈ S then 3 else 0) ≤ if (1 : Fin 2) ∈ T then 3 else 0 := by
      split_ifs with ha hb <;> try omega
      exact absurd (hST ha) hb
    have h01 : (if (0 : Fin 2) ∈ S ∧ (1 : Fin 2) ∈ S then 2 else 0) ≤
        if (0 : Fin 2) ∈ T ∧ (1 : Fin 2) ∈ T then 2 else 0 := by
      split_ifs with ha hb <;> try omega
      exact absurd ⟨hST ha.1, hST ha.2⟩ hb
    omega
  unfold val2
  exact_mod_cast hnat

private theorem val2_bit : ∃ f : Finset (Fin 2) → ℕ, (∀ S, val2 S = (f S : ℝ)) ∧ ∀ S, f S < 2 ^ 3 :=
  ⟨val2Nat, fun _ => rfl, fun S => by unfold val2Nat; split_ifs <;> omega⟩

/-- On `m = 2`, `t = 3`, `valueQueryProg 3 {0, 1}` recovers `val2 {0, 1} = 7` in exactly
`2 * 3 = 6 ≤ 2 * 3` demand queries, and `marginalValueProg 3 {0} 1` recovers `5` in `3` queries. -/
example : ∃ oracle : {ι : Type} → DemandQuery (Fin 2) ι → ι,
    DemandQuery.IsValidOracle val2 oracle ∧
    (((valueQueryProg 3 ({0, 1} : Finset (Fin 2))).eval oracle : ℕ) : ℝ) = 7 ∧
    (valueQueryProg 3 ({0, 1} : Finset (Fin 2))).countQueries oracle = 6 ∧
    (valueQueryProg 3 ({0, 1} : Finset (Fin 2))).countQueries oracle ≤ Fintype.card (Fin 2) * 3 ∧
    (((marginalValueProg 3 ({0} : Finset (Fin 2)) 1).eval oracle : ℕ) : ℝ) = 5 ∧
    (marginalValueProg 3 ({0} : Finset (Fin 2)) 1).countQueries oracle = 3 := by
  obtain ⟨oracle, horacle⟩ := DemandQuery.exists_isValidOracle val2
  refine ⟨oracle, horacle, ?_, ?_, ?_, ?_, ?_⟩
  · rw [eval_valueQueryProg val2_empty val2_monotone val2_bit horacle]
    norm_num [val2, val2Nat]
  · rw [countQueries_valueQueryProg]; decide
  · exact countQueries_valueQueryProg_le 3 _ oracle
  · rw [eval_marginalValueProg val2_monotone val2_bit horacle (by decide)]
    norm_num [val2, val2Nat]
  · exact countQueries_marginalValueProg 3 _ _ oracle

/-- Normalized monotone `3`-bit integer valuation on `Fin 3`:
`S ↦ 2 * |S| + (1 if 0 ∈ S ∧ 2 ∈ S else 0)` (values in `{0, ..., 7}`). -/
private def val3Nat (S : Finset (Fin 3)) : ℕ :=
  2 * S.card + if (0 : Fin 3) ∈ S ∧ (2 : Fin 3) ∈ S then 1 else 0

private def val3 (S : Finset (Fin 3)) : ℝ := (val3Nat S : ℝ)

private theorem val3_empty : val3 ∅ = 0 := by simp [val3, val3Nat]

private theorem val3_monotone : Monotone val3 := by
  intro S T hST
  have hnat : val3Nat S ≤ val3Nat T := by
    unfold val3Nat
    have hcard : S.card ≤ T.card := Finset.card_le_card hST
    have hbonus : (if (0 : Fin 3) ∈ S ∧ (2 : Fin 3) ∈ S then 1 else 0) ≤
        if (0 : Fin 3) ∈ T ∧ (2 : Fin 3) ∈ T then 1 else 0 := by
      split_ifs with h1 h2 <;> try omega
      exact absurd ⟨hST h1.1, hST h1.2⟩ h2
    omega
  unfold val3
  exact_mod_cast hnat

private theorem val3_bit : ∃ f : Finset (Fin 3) → ℕ, (∀ S, val3 S = (f S : ℝ)) ∧ ∀ S, f S < 2 ^ 3 :=
  ⟨val3Nat, fun _ => rfl, fun S => by
    have hle : S.card ≤ 3 := by simpa using Finset.card_le_univ S
    unfold val3Nat
    split_ifs <;> omega⟩

/-- On `m = 3`, `t = 3`, `valueQueryProg 3 univ` recovers `val3 univ = 7` in `3 * 3 = 9` demand
queries, and on `{0, 2}` recovers `5` in `2 * 3 = 6 ≤ 9` queries. -/
example : ∃ oracle : {ι : Type} → DemandQuery (Fin 3) ι → ι,
    (((valueQueryProg 3 (Finset.univ : Finset (Fin 3))).eval oracle : ℕ) : ℝ) = 7 ∧
    (valueQueryProg 3 (Finset.univ : Finset (Fin 3))).countQueries oracle = 9 ∧
    (((valueQueryProg 3 ({0, 2} : Finset (Fin 3))).eval oracle : ℕ) : ℝ) = 5 ∧
    (valueQueryProg 3 ({0, 2} : Finset (Fin 3))).countQueries oracle = 6 := by
  obtain ⟨oracle, horacle⟩ := DemandQuery.exists_isValidOracle val3
  refine ⟨oracle, ?_, ?_, ?_, ?_⟩
  · rw [eval_valueQueryProg val3_empty val3_monotone val3_bit horacle]
    norm_num [val3, val3Nat]
  · rw [countQueries_valueQueryProg]; decide
  · rw [eval_valueQueryProg val3_empty val3_monotone val3_bit horacle]
    norm_num [val3, val3Nat]
  · rw [countQueries_valueQueryProg]; decide

/-- Boundary case `t = 0`: the zero valuation is recovered with `0` demand queries. -/
example (S : Finset (Fin 2)) :
    ∃ oracle : {ι : Type} → DemandQuery (Fin 2) ι → ι,
      (((valueQueryProg 0 S).eval oracle : ℕ) : ℝ) = (0 : ℝ) ∧
      (valueQueryProg 0 S).countQueries oracle = 0 := by
  obtain ⟨oracle, horacle⟩ := DemandQuery.exists_isValidOracle (fun (_ : Finset (Fin 2)) => (0 : ℝ))
  refine ⟨oracle, ?_, by simp [countQueries_valueQueryProg]⟩
  exact eval_valueQueryProg rfl monotone_const
    ⟨fun _ => 0, fun _ => by simp, fun _ => Nat.zero_lt_one⟩ horacle S

/-! ### 2. Lemma 11.23 & Exercise 11.3 on `m = 4` (`C(4, 2) = 6`) -/

/-- All valuations in `IsSeparatorClassVal (Fin 4)` and `complementThresholdVal (Fin 4)` are
normalized and monotone. -/
example (v : Finset (Fin 4) → ℝ) (hv : IsSeparatorClassVal (Fin 4) v) :
    (v ∅ = 0 ∧ Monotone v) ∧
      (complementThresholdVal (Fin 4) ∅ = 0 ∧ Monotone (complementThresholdVal (Fin 4))) :=
  ⟨hv.empty_and_monotone (by decide), complementThresholdVal_empty_and_monotone (by decide)⟩

/-- Lemma 11.23 on `Fin 4`: any deterministic `ValueQuery` program simulating a demand query at
`separatorPrice (Fin 4)` makes at least `C(4, 2) = 6` queries on `thresholdBaseVal (Fin 4)`. -/
example (prog : FreeM (ValueQuery (Fin 4) ℝ) (Finset (Fin 4)))
    (hsim : ∀ v : Finset (Fin 4) → ℝ, v ∅ = 0 → Monotone v →
      IsDemand v (separatorPrice (Fin 4)) (prog.eval (ValueQuery.oracleOf v))) :
    6 ≤ prog.countQueries (ValueQuery.oracleOf (thresholdBaseVal (Fin 4))) := by
  have h := choose_half_le_countQueries_demandSim (M := Fin 4) (by decide) prog fun v hv =>
    let ⟨h0, hm⟩ := hv.empty_and_monotone (by decide)
    hsim v h0 hm
  exact (by decide : 6 ≤ (Fintype.card (Fin 4)).choose (Fintype.card (Fin 4) / 2)).trans h

/-- Exercise 11.3 on `Fin 4`: `oneDemandQueryOptimalAlloc (Fin 4)` uses `1` demand query and
returns an optimal allocation on both `thresholdBaseVal (Fin 4)` (welfare `2`) and
`hiddenBundleVal (Fin 4) {0, 1}` (welfare `4`), while any `ValueQuery` solver needs `≥ 5`. -/
example :
    (∃ o₀ o₁ : {ι : Type} → DemandQuery (Fin 4) ι → ι,
      (oneDemandQueryOptimalAlloc (Fin 4)).countQueries o₀ = 1 ∧
      (∀ b, welfare ![thresholdBaseVal (Fin 4), complementThresholdVal (Fin 4)] b ≤
        welfare ![thresholdBaseVal (Fin 4), complementThresholdVal (Fin 4)]
          ((oneDemandQueryOptimalAlloc (Fin 4)).eval o₀)) ∧
      (∀ b, welfare ![hiddenBundleVal (Fin 4) {0, 1}, complementThresholdVal (Fin 4)] b ≤
        welfare ![hiddenBundleVal (Fin 4) {0, 1}, complementThresholdVal (Fin 4)]
          ((oneDemandQueryOptimalAlloc (Fin 4)).eval o₁))) ∧
    (∀ prog : FreeM (ValueQuery (Fin 4) ℝ) (Allocation (Fin 2) (Fin 4)),
      (∀ v₁ : Finset (Fin 4) → ℝ, v₁ ∅ = 0 → Monotone v₁ →
        ∀ b, welfare ![v₁, complementThresholdVal (Fin 4)] b ≤
          welfare ![v₁, complementThresholdVal (Fin 4)] (prog.eval (ValueQuery.oracleOf v₁))) →
      5 ≤ prog.countQueries (ValueQuery.oracleOf (thresholdBaseVal (Fin 4)))) := by
  constructor
  · obtain ⟨o₀, ho₀⟩ := DemandQuery.exists_isValidOracle (thresholdBaseVal (Fin 4))
    obtain ⟨o₁, ho₁⟩ := DemandQuery.exists_isValidOracle (hiddenBundleVal (Fin 4) {0, 1})
    refine ⟨o₀, o₁, countQueries_oneDemandQueryOptimalAlloc o₀,
      eval_oneDemandQueryOptimalAlloc_optimal (Or.inl rfl) ho₀,
      eval_oneDemandQueryOptimalAlloc_optimal (Or.inr ⟨{0, 1}, by decide, rfl⟩) ho₁⟩
  · intro prog hopt
    have h := choose_half_sub_one_le_countQueries_optimalAlloc (M := Fin 4) prog
      fun v₁ hv₁ =>
        let ⟨h0, hm⟩ := hv₁.empty_and_monotone (by decide)
        hopt v₁ h0 hm
    exact (by decide : 5 ≤ (Fintype.card (Fin 4)).choose (Fintype.card (Fin 4) / 2) - 1).trans h

/-- Exponential growth check: `4 ^ (m / 2) ≤ (2 * (m / 2) + 1) * m.choose (m / 2)` for all `m`. -/
example (m : ℕ) : 4 ^ (m / 2) ≤ (2 * (m / 2) + 1) * m.choose (m / 2) := by
  have h1 := Nat.four_pow_le_two_mul_add_one_mul_centralBinom (m / 2)
  rw [Nat.centralBinom_eq_two_mul_choose] at h1
  exact h1.trans (Nat.mul_le_mul_left _ (Nat.choose_le_choose (m / 2) (by omega)))

/-! ### 3. Step of §11.5.2: DLPR demand-query separation oracle (feasible and infeasible cases) -/

/-- Two-bidder, two-item `3`-bit integer valuation profile: both bidders have `val2`. -/
private def dlprProfile : Fin 2 → Finset (Fin 2) → ℝ := fun _ => val2

/-- Feasible dual `(u, p)` with `u = (1, 1)` and `p = (3, 3)`: `v S ≤ 1 + 3 * |S|` for every `S`.
`dlprBidderCheckProg` returns `none` for both bidders in at most `2 * (1 + 2 * 3) = 14` queries. -/
example : ∃ oracles : Fin 2 → ({ι : Type} → DemandQuery (Fin 2) ι → ι),
    IsDLPRFeasible dlprProfile (fun _ => 1) (fun _ => 3) ∧
    (∀ i, (dlprBidderCheckProg 3 1 (fun _ : Fin 2 => (3 : ℝ))).eval (oracles i) = none) ∧
    ∑ i : Fin 2, (dlprBidderCheckProg 3 1 (fun _ : Fin 2 => (3 : ℝ))).countQueries (oracles i) ≤
      14 := by
  obtain ⟨o, ho⟩ := DemandQuery.exists_isValidOracle val2
  have hfeas : IsDLPRFeasible dlprProfile (fun _ => 1) (fun _ => 3) :=
    { cover := fun _ S => by
        have h : ∀ T : Finset (Fin 2), val2 T ≤ 1 + ∑ _j ∈ T, (3 : ℝ) := by
          intro T
          rw [Finset.sum_const, nsmul_eq_mul]
          by_cases h0 : (0 : Fin 2) ∈ T <;> by_cases h1 : (1 : Fin 2) ∈ T
          · have hT : T = Finset.univ := by
              ext x; fin_cases x <;> simp [h0, h1]
            subst hT; norm_num [val2, val2Nat]
          · have hT : T = {0} := by
              ext x; fin_cases x <;> simp [h0, h1]
            subst hT; norm_num [val2, val2Nat]
          · have hT : T = {1} := by
              ext x; fin_cases x <;> simp [h0, h1]
            subst hT; norm_num [val2, val2Nat]
          · have hT : T = ∅ := by
              ext x; fin_cases x <;> simp [h0, h1]
            subst hT; norm_num [val2, val2Nat]
        exact h S
      utility_nonneg := fun _ => by norm_num
      price_nonneg := fun _ => by norm_num }
  have hres := isDLPRFeasible_iff_dlprBidderCheckProg (N := Fin 2) (M := Fin 2) (t := 3)
    (v := dlprProfile) (fun _ => val2_empty) (fun _ => val2_monotone) (fun _ => val2_bit)
    (oracles := fun _ => o) (fun _ => ho) (u := fun _ => 1) (p := fun _ => 3)
    (fun _ => by norm_num) (fun _ => by norm_num)
  exact ⟨fun _ => o, hfeas, hres.1.mp hfeas, by simpa using hres.2⟩

/-- Infeasible dual `(u, p)` with `u = (0, 0)` and `p = (3, 3)`: `{0, 1}` violates constraint (11.8)
(`7 > 0 + 6`), so `dlprBidderCheckProg` returns `some D` with `0 + ∑ j ∈ D, 3 < val2 D`. -/
example : ∃ (o : {ι : Type} → DemandQuery (Fin 2) ι → ι) (D : Finset (Fin 2)),
    ¬ IsDLPRFeasible dlprProfile (fun _ => 0) (fun _ => 3) ∧
    (dlprBidderCheckProg 3 0 (fun _ : Fin 2 => (3 : ℝ))).eval o = some D ∧
    (0 : ℝ) + ∑ _j ∈ D, (3 : ℝ) < val2 D := by
  obtain ⟨o, ho⟩ := DemandQuery.exists_isValidOracle val2
  have hnot : ¬ IsDLPRFeasible dlprProfile (fun _ => 0) (fun _ => 3) := by
    intro h
    have hcov := h.cover 0 Finset.univ
    norm_num [dlprProfile, val2, val2Nat] at hcov
  have hne_none : (dlprBidderCheckProg 3 0 (fun _ : Fin 2 => (3 : ℝ))).eval o ≠ none := by
    intro hnone
    have hall := (dlprBidderCheckProg_eq_none_iff val2_empty val2_monotone val2_bit ho 0
      (fun _ : Fin 2 => (3 : ℝ))).mp hnone
    exact hnot ⟨fun _ => hall, fun _ => le_rfl, fun _ => by norm_num⟩
  cases hval : (dlprBidderCheckProg 3 0 (fun _ : Fin 2 => (3 : ℝ))).eval o with
  | none => exact absurd hval hne_none
  | some D =>
    exact ⟨o, D, hnot, hval,
      dlprBidderCheckProg_eq_some_violated val2_empty val2_monotone val2_bit ho hval⟩

/-! ### 4. Lemma 11.26 & Theorem 11.25: communication lower bound (`m = 2`, `m = 4`) -/

/-- Dual valuation check on `Fin 2`: for `v(S) = (0 ∈ S)`, `v.dual` is normalized (`v* ∅ = 0`),
satisfies `v* univ = 1`, and obeys `v(S) + v*(Sᶜ) = 1` for every bundle `S`. -/
example : let v : MonotoneZeroOneVal (Fin 2) :=
      ⟨fun S => decide ((0 : Fin 2) ∈ S), by simp, fun S T hST => by
        by_cases h : (0 : Fin 2) ∈ S
        · simp [h, hST h]
        · simp [h]⟩
    have hv : v.val Finset.univ = true := by simp [v]
    (v.dual hv).val ∅ = false ∧ (v.dual hv).val Finset.univ = true ∧
      ∀ S : Finset (Fin 2), v.toReal S + (v.dual hv).toReal Sᶜ = 1 := by
  intro v hv
  exact ⟨(v.dual hv).empty, v.dual_val_univ hv, v.toReal_add_dual_compl hv⟩

/-- Theorem 11.25 on `m = 2` (`Fin 2`): communication complexity is at least `C(2, 1) = 2` bits. -/
example : (2 : ℕ∞) ≤
    Protocol.ecomplexity
      (fun (v₁ v₂ : MonotoneZeroOneVal (Fin 2)) (a : Allocation (Fin 2) (Fin 2)) =>
        OptimalTwoBidderAlloc v₁.toReal v₂.toReal a)
      Set.univ Set.univ := by
  simpa using choose_half_le_ecomplexity (Fin 2)

/-- Theorem 11.25 on `m = 4` (`Fin 4`): communication complexity is at least `C(4, 2) = 6` bits. -/
example : (6 : ℕ∞) ≤
    Protocol.ecomplexity
      (fun (v₁ v₂ : MonotoneZeroOneVal (Fin 4)) (a : Allocation (Fin 2) (Fin 4)) =>
        OptimalTwoBidderAlloc v₁.toReal v₂.toReal a)
      Set.univ Set.univ := by
  have hc : (Fintype.card (Fin 4)).choose (Fintype.card (Fin 4) / 2) = 6 := by decide
  have h := choose_half_le_ecomplexity (Fin 4)
  rw [hc] at h
  exact h

/-- Lemma 11.26 on `Fin 2`: any optimal-allocation protocol reaches distinct leaves on
`(v₀, v₀*)` and `(v₁, v₁*)` for the two distinct single-item valuations. -/
example (p : Protocol (MonotoneZeroOneVal (Fin 2)) (MonotoneZeroOneVal (Fin 2))
      (Allocation (Fin 2) (Fin 2)))
    (hp : p.Solves (fun v₁ v₂ a => OptimalTwoBidderAlloc v₁.toReal v₂.toReal a)
      Set.univ Set.univ) :
    let v₀ : MonotoneZeroOneVal (Fin 2) :=
      ⟨fun S => decide ((0 : Fin 2) ∈ S), by simp, fun S T hST => by
        by_cases h : (0 : Fin 2) ∈ S
        · simp [h, hST h]
        · simp [h]⟩
    let v₁ : MonotoneZeroOneVal (Fin 2) :=
      ⟨fun S => decide ((1 : Fin 2) ∈ S), by simp, fun S T hST => by
        by_cases h : (1 : Fin 2) ∈ S
        · simp [h, hST h]
        · simp [h]⟩
    p.leaf v₀ (v₀.dual (by simp [v₀])) ≠ p.leaf v₁ (v₁.dual (by simp [v₁])) := by
  intro v₀ v₁
  refine leaf_dual_ne_of_ne (hp.mono (Set.subset_univ _) (Set.subset_univ _))
    (by simp [v₁]) (by simp [v₀]) ?_
  intro hEq
  have h := congrFun (congrArg MonotoneZeroOneVal.val hEq) ({0} : Finset (Fin 2))
  simp [v₀, v₁] at h

/-! ### 5. Sharpness boundary witnesses (`m = 0` and unnormalized constant valuations) -/

/-- **Boundary witness 1 (`m = 0`):** on `Empty`, `(Fintype.card Empty).choose 0 = 1`, yet a
`0`-bit protocol solves `OptimalTwoBidderAlloc` on all pairs, showing `[Nonempty M]` in
Theorem 11.25 is necessary. -/
example : ∃ p : Protocol (MonotoneZeroOneVal Empty) (MonotoneZeroOneVal Empty)
      (Allocation (Fin 2) Empty),
    p.Solves (fun v₁ v₂ a => OptimalTwoBidderAlloc v₁.toReal v₂.toReal a) Set.univ Set.univ ∧
    p.depth = 0 ∧ p.depth < (Fintype.card Empty).choose (Fintype.card Empty / 2) := by
  let a₀ : Allocation (Fin 2) Empty := ⟨fun _ => ∅, fun _ _ _ => Finset.disjoint_empty_left _⟩
  refine ⟨Protocol.output a₀, fun v₁ _ v₂ _ b => ?_, rfl, by decide⟩
  have hb : b = a₀ := by
    ext i x
    exact x.elim
  rw [Protocol.run_output, hb]

/-- **Boundary witness 2 (unnormalized valuations):** without normalization `v ∅ = 0`, the constant
monotone `0/1` valuations `u ≡ 0` and `v ≡ 1` have duals `u* ≡ 1` and `v* ≡ 0`, and the single
allocation `(univ, ∅)` is simultaneously optimal on all four pairs `(v, v*)`, `(u, u*)`, `(v, u*)`,
and `(u, v*)`, refuting the literal unnormalized statement of Lemma 11.26. -/
example : let u : Finset (Fin 2) → ℝ := fun _ => 0
    let v : Finset (Fin 2) → ℝ := fun _ => 1
    let uDual : Finset (Fin 2) → ℝ := fun S => 1 - u Sᶜ
    let vDual : Finset (Fin 2) → ℝ := fun S => 1 - v Sᶜ
    let a : Allocation (Fin 2) (Fin 2) := partitionAlloc Finset.univ
    u ≠ v ∧
    OptimalTwoBidderAlloc v vDual a ∧
    OptimalTwoBidderAlloc u uDual a ∧
    OptimalTwoBidderAlloc v uDual a ∧
    OptimalTwoBidderAlloc u vDual a := by
  intro u v uDual vDual a
  refine ⟨fun h => by have := congrFun h ∅; norm_num [u, v] at this, ?_, ?_, ?_, ?_⟩ <;>
    intro b <;> simp [welfare, Fin.sum_univ_two, u, v, uDual, vDual]

end CslibFrontierTests.GameTheory.CombinatorialAuctionQueryComm
