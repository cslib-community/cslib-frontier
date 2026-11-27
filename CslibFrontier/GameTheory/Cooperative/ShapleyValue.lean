/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Mobius
public import CslibFrontier.GameTheory.Cooperative.MoulinCostSharing
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Topology.Compactness.Compact
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Shapley value and the Nash bargaining solution

This module formalizes the axiomatic characterizations of the **Shapley value** and the **Nash
bargaining solution** ([TardosVazirani2007], Example 1.14; [JainMahdian2007], Section 15.6 and
Exercise 15.2; Shapley 1953; Nash 1950):

1. **Shapley value** (`shapleyValue`): both the subset-size weight formula
   `∑_{S ⊆ A \ {i}} (|S|! (n - 1 - |S|)! / n!) (c(S ∪ {i}) - c(S))` ([JainMahdian2007], Section
   15.6.1, p. 403) and the uniform permutation-average formula `permShapleyValue`
   ([TardosVazirani2007], Example 1.14, p. 22), proved equal (`shapleyValue_eq_permShapleyValue`).
2. **Example 15.24** (`example15_24_nonemptyCore`, `example15_24_shapleyValue`,
   `example15_24_not_inCore`): on `example15_2`, the core is nonempty (Example 15.4,
   pp. 387–388), while `shapleyValue` evaluates to `(23 / 6, 11 / 6, 7 / 3)` and does *not* lie in
   the core (`25 / 6 > 4 = c({b, c})`).
3. **Theorem 15.26 (Shapley's uniqueness theorem)** (`eq_shapleyValue_of_axioms`,
   `existsUnique_shapleyValue`): `shapleyValue` is the unique value operator satisfying
   **Efficiency** (`∑_i φ_i(c) = c(univ)`), **Symmetry** (or **Anonymity**, Definition 15.25),
   **Dummy**, and **Additivity**, proved over the `2^n - 1` unanimity-game basis without assuming
   homogeneity or nonnegativity.

   *Source notes on [JainMahdian2007], Definition 15.25 & Theorem 15.26 (p. 404):*
   - Efficiency (`∑_i φ_i(c) = c(A)`) is assumed implicitly on p. 403–404 ("allocating the cost
     `c(A)` among all agents"); without Efficiency, `φ = 0` also satisfies Anonymity, Dummy, and
     Additivity.
   - In the Dummy axiom on p. 404, `S ⊂ A \ {i}` is a typographical slip for `S ⊆ A \ {i}` (i.e.
     `i ∉ S`); excluding `S = A \ {i}` would treat an agent whose sole nonzero marginal cost is at
     the grand coalition as a dummy, contradicting Efficiency.
4. **Exercise 15.2 and Section 15.6.1**
   (`CostSharingGame.IsSubmodular.shapleyScheme_isCrossMonotone`,
   `CostSharingGame.IsSubmodular.shapleyValue_inCore`): for submodular cost-sharing games, the
   Shapley cost-sharing scheme `shapleyScheme` is cross-monotone (Exercise 15.2, p. 410), hence
   `shapleyValue` lies in the core (Section 15.6.1, p. 403), and `moulinMechanism` on
   `shapleyScheme` is group-strategyproof and `1`-budget-balanced by composing with
   `moulinMechanism_isGroupStrategyproof` and `moulinMechanism_isBudgetBalanced`.
5. **Nash bargaining solution** (`BargainingProblem`, `nashBargainingSolution`,
   `eq_nashBargainingSolution_of_axioms`, `existsUnique_nashBargainingSolution`,
   [JainMahdian2007], Definition 15.27 and **Theorem 15.28**; Nash 1950): on compact convex
   2-player feasible utility sets `X ⊆ ℝ × ℝ` with disagreement point `d ∈ X` and at least one
   strictly individually rational outcome `x > d`, maximizing `(x₁ - d₁)(x₂ - d₂)` over `{x ∈ X |
   x ≥ d}` is the *unique* bargaining solution satisfying Pareto optimality, symmetry, positive
   affine scale invariance, and independence of irrelevant alternatives.

## Main definitions

* `Cslib.GameTheory.shapleyWeight`, `Cslib.GameTheory.shapleyValue`: subset-size weight and Shapley
  value of a TU cost-sharing game ([JainMahdian2007], Section 15.6.1).
* `Cslib.GameTheory.orderPredecessors`, `Cslib.GameTheory.permShapleyValue`: random-ordering
  marginal-cost expectation ([TardosVazirani2007], Example 1.14).
* `Cslib.GameTheory.IsEfficientValue`, `Cslib.GameTheory.IsAnonymousValue`,
  `Cslib.GameTheory.IsSymmetricValue`, `Cslib.GameTheory.SatisfiesDummy`,
  `Cslib.GameTheory.IsAdditiveValue`: Shapley value axioms ([JainMahdian2007], Definition 15.25).
* `Cslib.GameTheory.CostSharingGame.AreSymmetric`,
  `Cslib.GameTheory.CostSharingGame.IsDummyAgent`,
  `Cslib.GameTheory.unanimityGame`: symmetry, dummy agents, and the unanimity-game basis.
* `Cslib.GameTheory.CostSharingGame.shapleyScheme`: coalition-restricted Shapley cost-sharing
  scheme ([JainMahdian2007], Exercise 15.2).
* `Cslib.GameTheory.BargainingProblem`,
  `Cslib.GameTheory.BargainingProblem.individuallyRational`,
  `Cslib.GameTheory.BargainingProblem.nashProduct`,
  `Cslib.GameTheory.nashBargainingSolution`: 2-player Nash bargaining problem and Nash product
  maximizer ([JainMahdian2007], Section 15.6.3).
* `Cslib.GameTheory.IsBargainingSolution`, `Cslib.GameTheory.IsParetoOptimal`,
  `Cslib.GameTheory.IsWeaklyParetoOptimal`, `Cslib.GameTheory.IsSymmetricBargaining`,
  `Cslib.GameTheory.IsScaleInvariant`, `Cslib.GameTheory.SatisfiesIIA`: Nash bargaining axioms
  ([JainMahdian2007], Definition 15.27).

## Main results

* `Cslib.GameTheory.shapleyValue_eq_sum_card`,
  `Cslib.GameTheory.shapleyValue_eq_permShapleyValue`: grouped-cardinality and permutation-average
  characterizations of `shapleyValue`.
* `Cslib.GameTheory.example15_24_nonemptyCore`,
  `Cslib.GameTheory.example15_24_shapleyValue`,
  `Cslib.GameTheory.example15_24_not_inCore`: **Example 15.24** (with **Example 15.4** core
  nonemptiness) of [JainMahdian2007].
* `Cslib.GameTheory.shapleyValue_isEfficient`,
  `Cslib.GameTheory.shapleyValue_isAnonymous`,
  `Cslib.GameTheory.shapleyValue_isSymmetric`,
  `Cslib.GameTheory.shapleyValue_satisfiesDummy`,
  `Cslib.GameTheory.shapleyValue_isAdditive`,
  `Cslib.GameTheory.eq_shapleyValue_of_axioms`,
  `Cslib.GameTheory.existsUnique_shapleyValue`: **Theorem 15.26 (Shapley's uniqueness theorem)** of
  [JainMahdian2007].
* `Cslib.GameTheory.CostSharingGame.IsSubmodular.shapleyScheme_isCrossMonotone`,
  `Cslib.GameTheory.CostSharingGame.IsSubmodular.shapleyValue_inCore`:
  **Exercise 15.2** (p. 410) and **Section 15.6.1** (p. 403) of [JainMahdian2007].
* `Cslib.GameTheory.isGreatest_nashBargainingSolution`,
  `Cslib.GameTheory.nashBargainingSolution_unique_maximizer`,
  `Cslib.GameTheory.eq_nashBargainingSolution_of_axioms`,
  `Cslib.GameTheory.existsUnique_nashBargainingSolution`: **Theorem 15.28 (Nash's bargaining
  theorem)** of [JainMahdian2007].

## References

* [JainMahdian2007]
* [TardosVazirani2007]
-/

public section

namespace Cslib.GameTheory

/-! ## Shapley value: subset-size and permutation-average formulas -/

/-- Combinatorial weight `s! * (n - 1 - s)! / n!` of a coalition `S ⊆ A \ {i}` of size `s` in a
game of `n` agents ([JainMahdian2007], Section 15.6.1, p. 403). -/
noncomputable def shapleyWeight (n s : ℕ) : ℝ :=
  ((s.factorial * (n - 1 - s).factorial : ℕ) : ℝ) / (n.factorial : ℝ)

theorem shapleyWeight_eq (n s : ℕ) :
    shapleyWeight n s =
      ((s.factorial * (n - 1 - s).factorial : ℕ) : ℝ) / (n.factorial : ℝ) := by
  rfl

theorem shapleyWeight_nonneg (n s : ℕ) : 0 ≤ shapleyWeight n s := by
  unfold shapleyWeight
  positivity

/-- The **Shapley value** `shapleyValue G i` of agent `i` in a TU cost-sharing game `G`
([JainMahdian2007], Section 15.6.1, p. 403). -/
noncomputable def shapleyValue {A : Type*} [Fintype A] [DecidableEq A]
    (G : CostSharingGame A) (i : A) : ℝ :=
  ∑ S ∈ (Finset.univ.erase i).powerset,
    shapleyWeight (Fintype.card A) S.card * (G.cost (insert i S) - G.cost S)

theorem shapleyValue_eq {A : Type*} [Fintype A] [DecidableEq A]
    (G : CostSharingGame A) (i : A) :
    shapleyValue G i =
      ∑ S ∈ (Finset.univ.erase i).powerset,
        shapleyWeight (Fintype.card A) S.card * (G.cost (insert i S) - G.cost S) := by
  rfl

/-- Grouped-by-cardinality formula matching the displayed equation of [JainMahdian2007], p. 403. -/
theorem shapleyValue_eq_sum_card {A : Type*} [Fintype A] [DecidableEq A]
    (G : CostSharingGame A) (i : A) :
    shapleyValue G i =
      ∑ s ∈ Finset.range (Fintype.card A),
        shapleyWeight (Fintype.card A) s *
          ∑ S ∈ (Finset.univ.erase i).powersetCard s, (G.cost (insert i S) - G.cost S) := by
  have hcard : (Finset.univ.erase i).card + 1 = Fintype.card A :=
    (Finset.card_erase_add_one (Finset.mem_univ i)).trans Finset.card_univ
  rw [shapleyValue, ← hcard, (Finset.univ.erase i).powerset_card_biUnion,
    Finset.sum_biUnion (fun _ _ _ _ hne => Finset.pairwise_disjoint_powersetCard _ hne)]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun S hS => by rw [(Finset.mem_powersetCard.1 hS).2]

/-- Set of agents appearing strictly before `i` under an agent ordering `σ : Fin (card A) ≃ A`
([TardosVazirani2007], Example 1.14). -/
def orderPredecessors {A : Type*} [Fintype A] (σ : Fin (Fintype.card A) ≃ A) (i : A) :
    Finset A :=
  Finset.univ.filter (fun j => σ.symm j < σ.symm i)

@[simp]
theorem mem_orderPredecessors {A : Type*} [Fintype A] (σ : Fin (Fintype.card A) ≃ A) (i j : A) :
    j ∈ orderPredecessors σ i ↔ σ.symm j < σ.symm i := by
  simp [orderPredecessors]

theorem not_mem_orderPredecessors {A : Type*} [Fintype A] (σ : Fin (Fintype.card A) ≃ A) (i : A) :
    i ∉ orderPredecessors σ i := by
  simp

/-- Permutation-average definition of the Shapley value ([TardosVazirani2007], Example 1.14, p. 22;
[JainMahdian2007], Section 15.6.1, p. 403): average marginal cost of `i` over all `n!` orderings
`σ : Fin (card A) ≃ A`. -/
noncomputable def permShapleyValue {A : Type*} [Fintype A] [DecidableEq A]
    (G : CostSharingGame A) (i : A) : ℝ :=
  ((Fintype.card A).factorial : ℝ)⁻¹ *
    ∑ σ : Fin (Fintype.card A) ≃ A,
      (G.cost (insert i (orderPredecessors σ i)) - G.cost (orderPredecessors σ i))

theorem permShapleyValue_eq {A : Type*} [Fintype A] [DecidableEq A]
    (G : CostSharingGame A) (i : A) :
    permShapleyValue G i =
      ((Fintype.card A).factorial : ℝ)⁻¹ *
        ∑ σ : Fin (Fintype.card A) ≃ A,
          (G.cost (insert i (orderPredecessors σ i)) - G.cost (orderPredecessors σ i)) := by
  rfl

section PermEquivalence

variable {A : Type*} [Fintype A] [DecidableEq A]

private theorem card_fin_lt {n : ℕ} (m : Fin n) :
    (Finset.univ.filter (fun k : Fin n => k < m)).card = (m : ℕ) := by
  rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]

private theorem card_fin_gt {n : ℕ} (m : Fin n) :
    (Finset.univ.filter (fun k : Fin n => m < k)).card = n - 1 - (m : ℕ) := by
  rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]

omit [DecidableEq A] in
private theorem card_orderPredecessors (σ : Fin (Fintype.card A) ≃ A) (i : A) :
    (orderPredecessors σ i).card = (σ.symm i : ℕ) := by
  have heq : orderPredecessors σ i =
      (Finset.univ.filter (fun k : Fin (Fintype.card A) => k < σ.symm i)).map σ.toEmbedding := by
    ext j
    simp only [orderPredecessors, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply]
    exact ⟨fun hj => ⟨σ.symm j, hj, σ.apply_symm_apply j⟩,
      fun ⟨k, hk, hkj⟩ => hkj ▸ (σ.symm_apply_apply k).symm ▸ hk⟩
  rw [heq, Finset.card_map, card_fin_lt]

private theorem card_filter_orderPredecessors_eq (i : A) {S : Finset A}
    (hS : S ⊆ Finset.univ.erase i) :
    (Finset.univ.filter (fun σ : Fin (Fintype.card A) ≃ A => orderPredecessors σ i = S)).card =
      S.card.factorial * (Fintype.card A - 1 - S.card).factorial := by
  set n := Fintype.card A
  set s := S.card
  have hiS : i ∉ S := fun hi => (Finset.mem_erase.1 (hS hi)).1 rfl
  have hn_pos : 1 ≤ n := Fintype.card_pos_iff.2 ⟨i⟩
  have herase_card : (Finset.univ.erase i).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  have hs_le : s ≤ n - 1 := herase_card ▸ Finset.card_le_card hS
  have hs_lt : s < n := by omega
  let iPos : Fin n := ⟨s, hs_lt⟩
  set R : Finset A := (Finset.univ.erase i) \ S
  let LIdx := {k : Fin n // k < iPos}
  let GIdx := {k : Fin n // iPos < k}
  let LVal := {x : A // x ∈ S}
  let GVal := {x : A // x ∈ R}
  -- Bijection between orderings with `orderPredecessors σ i = S` and pairs `(LIdx ≃ LVal) ×
  -- (GIdx ≃ GVal)`.
  let bij : {σ : Fin n ≃ A // orderPredecessors σ i = S} ≃ (LIdx ≃ LVal) × (GIdx ≃ GVal) :=
    { toFun := fun ⟨σ, hσ⟩ =>
        have hpos_eq : σ.symm i = iPos :=
          Fin.ext ((card_orderPredecessors σ i).symm.trans (hσ ▸ rfl))
        have hσ_iPos : σ iPos = i := by
          rw [← hpos_eq, σ.apply_symm_apply]
        -- `σ` maps positions before (after) `iPos` onto `S` (onto `R`).
        ( σ.subtypeEquiv fun k => by
            rw [← hσ, mem_orderPredecessors, σ.symm_apply_apply, hpos_eq],
          σ.subtypeEquiv fun k => by
            simp only [R, ← hσ, Finset.mem_sdiff, Finset.mem_erase, mem_orderPredecessors,
              σ.symm_apply_apply, Finset.mem_univ, and_true, not_lt, ← hσ_iPos,
              σ.injective.ne_iff]
            exact ⟨fun h => ⟨h.ne', h.le⟩, fun h => lt_of_le_of_ne h.2 h.1.symm⟩ )
      invFun := fun ⟨eL, eG⟩ =>
        let fwd : Fin n → A := fun k =>
          if hlt : k < iPos then (eL ⟨k, hlt⟩).1
          else if hgt : iPos < k then (eG ⟨k, hgt⟩).1
          else i
        have hmemR : ∀ x : A, x ∉ S → x ≠ i → x ∈ R := fun x hxS hxi =>
          Finset.mem_sdiff.2 ⟨Finset.mem_erase.2 ⟨hxi, Finset.mem_univ x⟩, hxS⟩
        let bwd : A → Fin n := fun x =>
          if hxS : x ∈ S then (eL.symm ⟨x, hxS⟩).1
          else if hxi : x = i then iPos
          else (eG.symm ⟨x, hmemR x hxS hxi⟩).1
        have hleft : Function.LeftInverse bwd fwd := fun k => by
          dsimp only [fwd, bwd]
          by_cases hlt : k < iPos
          · simp only [hlt, (eL ⟨k, hlt⟩).2, ↓reduceDIte, Subtype.eta, Equiv.symm_apply_apply]
          · by_cases hgt : iPos < k
            · obtain ⟨hmemE, hnotS⟩ := Finset.mem_sdiff.1 (eG ⟨k, hgt⟩).2
              simp only [hlt, hgt, hnotS, (Finset.mem_erase.1 hmemE).1, ↓reduceDIte, Subtype.eta,
                Equiv.symm_apply_apply]
            · have heq : k = iPos := le_antisymm (not_lt.1 hgt) (not_lt.1 hlt)
              subst heq
              simp only [lt_irrefl, hiS, ↓reduceDIte]
        have hright : Function.RightInverse bwd fwd := fun x => by
          dsimp only [fwd, bwd]
          by_cases hxS : x ∈ S
          · simp only [hxS, (eL.symm ⟨x, hxS⟩).2, ↓reduceDIte, Subtype.eta,
              Equiv.apply_symm_apply]
          · by_cases hxi : x = i
            · subst hxi
              simp only [hxS, ↓reduceDIte, lt_irrefl]
            · have hkgt : iPos < (eG.symm ⟨x, hmemR x hxS hxi⟩).1 :=
                (eG.symm ⟨x, hmemR x hxS hxi⟩).2
              simp only [hxS, hxi, not_lt_of_gt hkgt, hkgt, ↓reduceDIte, Subtype.eta,
                Equiv.apply_symm_apply]
        ⟨⟨fwd, bwd, hleft, hright⟩, by
          ext x
          simp only [orderPredecessors, Finset.mem_filter, Finset.mem_univ, true_and]
          change bwd x < bwd i ↔ x ∈ S
          have hbwdi : bwd i = iPos := by simp only [bwd, hiS, ↓reduceDIte]
          rw [hbwdi]
          dsimp only [bwd]
          by_cases hxS : x ∈ S
          · simp only [hxS, ↓reduceDIte, (eL.symm ⟨x, hxS⟩).2]
          · simp only [hxS, ↓reduceDIte, iff_false]
            by_cases hxi : x = i
            · simp only [hxi, ↓reduceDIte, lt_irrefl, not_false_eq_true]
            · simp only [hxi, ↓reduceDIte]
              exact not_lt_of_gt (eG.symm ⟨x, hmemR x hxS hxi⟩).2⟩
      left_inv := fun ⟨σ, hσ⟩ => by
        ext k
        have hpos_eq : σ.symm i = iPos :=
          Fin.ext ((card_orderPredecessors σ i).symm.trans (hσ ▸ rfl))
        change (if hlt : k < iPos then σ k else if hgt : iPos < k then σ k else i) = σ k
        split_ifs with hlt hgt
        iterate 2 rfl
        · have heq : k = iPos := le_antisymm (not_lt.1 hgt) (not_lt.1 hlt)
          rw [heq, ← hpos_eq, σ.apply_symm_apply]
      right_inv := fun ⟨eL, eG⟩ => by
        ext ⟨k, hk⟩
        · change (if hlt : k < iPos then (eL ⟨k, hlt⟩).1
            else if hgt : iPos < k then (eG ⟨k, hgt⟩).1 else i) = (eL ⟨k, hk⟩).1
          split_ifs
          rfl
        · change (if hlt : k < iPos then (eL ⟨k, hlt⟩).1
            else if hgt : iPos < k then (eG ⟨k, hgt⟩).1 else i) = (eG ⟨k, hk⟩).1
          have hnotlt : ¬ k < iPos := not_lt_of_gt hk
          split_ifs
          rfl }
  have hcard_LIdx : Fintype.card LIdx = s := (Fintype.card_subtype _).trans (card_fin_lt iPos)
  have hcard_LVal : Fintype.card LVal = s := Fintype.card_coe S
  have hcard_GIdx : Fintype.card GIdx = n - 1 - s :=
    (Fintype.card_subtype _).trans (card_fin_gt iPos)
  have hcard_GVal : Fintype.card GVal = n - 1 - s := by
    rw [Fintype.card_coe, Finset.card_sdiff, Finset.inter_eq_left.2 hS, herase_card]
  have hequivL : LIdx ≃ LVal := Fintype.equivOfCardEq (hcard_LIdx.trans hcard_LVal.symm)
  have hequivG : GIdx ≃ GVal := Fintype.equivOfCardEq (hcard_GIdx.trans hcard_GVal.symm)
  rw [← Fintype.card_subtype, Fintype.card_congr bij, Fintype.card_prod,
    Fintype.card_equiv hequivL, Fintype.card_equiv hequivG, hcard_LIdx, hcard_GIdx]

/-- Equivalence of the subset-size formula `shapleyValue` ([JainMahdian2007], Section 15.6.1,
p. 403) and the uniform permutation-average formula `permShapleyValue` ([TardosVazirani2007],
Example 1.14, p. 22). -/
theorem shapleyValue_eq_permShapleyValue (G : CostSharingGame A) (i : A) :
    shapleyValue G i = permShapleyValue G i := by
  have hmem : ∀ σ : Fin (Fintype.card A) ≃ A,
      orderPredecessors σ i ∈ (Finset.univ.erase i).powerset := fun σ =>
    Finset.mem_powerset.2 fun j hj =>
      Finset.mem_erase.2 ⟨fun hji => not_mem_orderPredecessors σ i (hji ▸ hj), Finset.mem_univ j⟩
  have hpart :
      (∑ σ : Fin (Fintype.card A) ≃ A,
          (G.cost (insert i (orderPredecessors σ i)) - G.cost (orderPredecessors σ i))) =
        ∑ S ∈ (Finset.univ.erase i).powerset,
          ∑ σ ∈ Finset.univ.filter (fun σ : Fin (Fintype.card A) ≃ A =>
              orderPredecessors σ i = S),
            (G.cost (insert i (orderPredecessors σ i)) - G.cost (orderPredecessors σ i)) := by
    rw [← Finset.sum_biUnion]
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext σ
      simp only [Finset.mem_univ, Finset.mem_biUnion, Finset.mem_filter, true_and, true_iff]
      exact ⟨orderPredecessors σ i, hmem σ, rfl⟩
    · intro S₁ _ S₂ _ hne
      exact Finset.disjoint_filter.2 fun σ _ h₁ h₂ => hne (h₁.symm.trans h₂)
  rw [permShapleyValue, hpart, Finset.mul_sum, shapleyValue]
  refine Finset.sum_congr rfl fun S hS => ?_
  have hconst :
      (∑ σ ∈ Finset.univ.filter (fun σ : Fin (Fintype.card A) ≃ A =>
          orderPredecessors σ i = S),
        (G.cost (insert i (orderPredecessors σ i)) - G.cost (orderPredecessors σ i))) =
      ((Finset.univ.filter (fun σ : Fin (Fintype.card A) ≃ A =>
          orderPredecessors σ i = S)).card : ℝ) *
        (G.cost (insert i S) - G.cost S) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]
  rw [hconst, card_filter_orderPredecessors_eq i (Finset.mem_powerset.1 hS)]
  simp only [shapleyWeight, div_eq_mul_inv, Nat.cast_mul]
  ring

end PermEquivalence

/-! ## Example 15.24: Shapley value outside a nonempty core -/

/-- **Examples 15.4 and 15.24** ([JainMahdian2007], Section 15.2, pp. 387–388, and Section 15.6.1,
p. 403): the 3-agent metric facility location game `example15_2` has a nonempty core, witnessed by
`![4, 2, 2]` (`FacilityLocationInstance.example15_2_inCore_four_two_two`). -/
theorem example15_24_nonemptyCore :
    FacilityLocationInstance.example15_2.toCostSharingGame.NonemptyCore :=
  ⟨![4, 2, 2], FacilityLocationInstance.example15_2_inCore_four_two_two⟩

/-- **Example 15.24** ([JainMahdian2007], p. 403): on the 3-agent facility location game
`example15_2`, the Shapley values are `(23 / 6, 11 / 6, 7 / 3)`. -/
theorem example15_24_shapleyValue :
    shapleyValue FacilityLocationInstance.example15_2.toCostSharingGame 0 = 23 / 6 ∧
    shapleyValue FacilityLocationInstance.example15_2.toCostSharingGame 1 = 11 / 6 ∧
    shapleyValue FacilityLocationInstance.example15_2.toCostSharingGame 2 = 7 / 3 := by
  obtain ⟨h0, h1, h2, h01, h12, h02, huniv⟩ := FacilityLocationInstance.example15_2_cost
  have hc0 : FacilityLocationInstance.example15_2.toCostSharingGame.cost ∅ = 0 :=
    CostSharingGame.cost_empty _
  have huniv3 : ({0, 1, 2} : Finset (Fin 3)) = Finset.univ := by decide
  have h10 : ({1, 0} : Finset (Fin 3)) = {0, 1} := by decide
  have h20 : ({2, 0} : Finset (Fin 3)) = {0, 2} := by decide
  have h21 : ({2, 1} : Finset (Fin 3)) = {1, 2} := by decide
  have h102 : ({1, 0, 2} : Finset (Fin 3)) = Finset.univ := by decide
  have h201 : ({2, 0, 1} : Finset (Fin 3)) = Finset.univ := by decide
  have her0 : (Finset.univ.erase (0 : Fin 3)).powerset = {∅, {1}, {2}, {1, 2}} := by decide
  have her1 : (Finset.univ.erase (1 : Fin 3)).powerset = {∅, {0}, {2}, {0, 2}} := by decide
  have her2 : (Finset.univ.erase (2 : Fin 3)).powerset = {∅, {0}, {1}, {0, 1}} := by decide
  have hcardA : Fintype.card (Fin 3) = 3 := Fintype.card_fin 3
  have hw0 : shapleyWeight 3 0 = 1 / 3 := by norm_num [shapleyWeight, Nat.factorial]
  have hw1 : shapleyWeight 3 1 = 1 / 6 := by norm_num [shapleyWeight, Nat.factorial]
  have hw2 : shapleyWeight 3 2 = 1 / 3 := by norm_num [shapleyWeight, Nat.factorial]
  refine ⟨?_, ?_, ?_⟩
  · rw [shapleyValue, hcardA, her0]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton, Finset.insert_empty, huniv3]
    norm_num [hw0, hw1, hw2, hc0, h0, h1, h2, h01, h12, h02, huniv]
  · rw [shapleyValue, hcardA, her1]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton, Finset.insert_empty, h10, h102]
    norm_num [hw0, hw1, hw2, hc0, h0, h1, h2, h01, h12, h02, huniv]
  · rw [shapleyValue, hcardA, her2]
    repeat rw [Finset.sum_insert (by decide)]
    rw [Finset.sum_singleton, Finset.insert_empty, h20, h21, h201]
    norm_num [hw0, hw1, hw2, hc0, h0, h1, h2, h01, h12, h02, huniv]

/-- **Example 15.24** ([JainMahdian2007], p. 403): the Shapley value `(23 / 6, 11 / 6, 7 / 3)` of
`example15_2` does *not* lie in the core (`φ_b + φ_c = 25 / 6 > 4 = c({b, c})`), even though
`example15_2` has a nonempty core (`example15_2_inCore_four_two_two`). -/
theorem example15_24_not_inCore :
    ¬ FacilityLocationInstance.example15_2.toCostSharingGame.InCore
        (shapleyValue FacilityLocationInstance.example15_2.toCostSharingGame) := by
  rintro ⟨_, hfeas⟩
  obtain ⟨_, hb, hc⟩ := example15_24_shapleyValue
  have h12 := FacilityLocationInstance.example15_2_cost.2.2.2.2.1
  have hbc := hfeas {1, 2}
  rw [Finset.sum_pair (by decide), hb, hc, h12] at hbc
  linarith

/-! ## Axiomatic characterization of the Shapley value (Theorem 15.26) -/

/-- Two agents `i, j` are **symmetric** in `G` if adding either one to any coalition avoiding both
incurs the same cost. -/
@[expose] def CostSharingGame.AreSymmetric {A : Type*} [DecidableEq A]
    (G : CostSharingGame A) (i j : A) : Prop :=
  ∀ S : Finset A, i ∉ S → j ∉ S → G.cost (insert i S) = G.cost (insert j S)

/-- Agent `i` is a **dummy agent** in `G` ([JainMahdian2007], Definition 15.25) if `c(S ∪ {i}) =
c(S)` for every coalition `S ⊆ A \ {i}`. -/
@[expose] def CostSharingGame.IsDummyAgent {A : Type*} [DecidableEq A]
    (G : CostSharingGame A) (i : A) : Prop :=
  ∀ S : Finset A, i ∉ S → G.cost (insert i S) = G.cost S

/-- **Efficiency** (budget balance): `∑_i φ_i(G) = G.cost univ`. -/
@[expose] def IsEfficientValue {A : Type*} [Fintype A]
    (φ : CostSharingGame A → A → ℝ) : Prop :=
  ∀ G : CostSharingGame A, ∑ i : A, φ G i = G.cost Finset.univ

/-- **Anonymity** ([JainMahdian2007], Definition 15.25): permuting agent names permutes their cost
shares (`φ (G.perm π) (π i) = φ G i`). -/
@[expose] def IsAnonymousValue {A : Type*}
    (φ : CostSharingGame A → A → ℝ) : Prop :=
  ∀ (π : Equiv.Perm A) (G : CostSharingGame A) (i : A), φ (G.perm π) (π i) = φ G i

/-- **Symmetry**: symmetric agents receive equal cost shares. -/
@[expose] def IsSymmetricValue {A : Type*} [DecidableEq A]
    (φ : CostSharingGame A → A → ℝ) : Prop :=
  ∀ (G : CostSharingGame A) (i j : A), G.AreSymmetric i j → φ G i = φ G j

/-- **Dummy axiom** ([JainMahdian2007], Definition 15.25): dummy agents pay `0`. -/
@[expose] def SatisfiesDummy {A : Type*} [DecidableEq A]
    (φ : CostSharingGame A → A → ℝ) : Prop :=
  ∀ (G : CostSharingGame A) (i : A), G.IsDummyAgent i → φ G i = 0

/-- **Additivity** ([JainMahdian2007], Definition 15.25): `φ(G₁ + G₂) = φ(G₁) + φ(G₂)`. -/
@[expose] def IsAdditiveValue {A : Type*}
    (φ : CostSharingGame A → A → ℝ) : Prop :=
  ∀ G₁ G₂ : CostSharingGame A, φ (G₁ + G₂) = φ G₁ + φ G₂

private theorem sum_powerset_map {α β M : Type*} [AddCommMonoid M] (f : α ↪ β) (s : Finset α)
    (g : Finset β → M) :
    ∑ t ∈ (s.map f).powerset, g t = ∑ t ∈ s.powerset, g (t.map f) := by
  classical
  have hpow : (s.map f).powerset = s.powerset.map (Finset.mapEmbedding f).toEmbedding := by
    simp only [Finset.map_eq_image, Finset.powerset_image]
    congr 1
    funext t
    exact (Finset.map_eq_image f t).symm
  rw [hpow, Finset.sum_map]
  rfl

/-- Anonymity implies Symmetry via transposition `Equiv.swap i j`. -/
theorem IsAnonymousValue.isSymmetricValue {A : Type*} [DecidableEq A]
    {φ : CostSharingGame A → A → ℝ} (hanon : IsAnonymousValue φ) : IsSymmetricValue φ := by
  intro G i j hsym
  let π := Equiv.swap i j
  have hperm : G.perm π = G := by
    ext S
    rw [CostSharingGame.perm_cost, Equiv.symm_swap]
    -- `swap i j` fixes `S` when `i` and `j` are both in `S` or both outside it.
    have hfix (h : i ∈ S ↔ j ∈ S) : S.map π.toEmbedding = S := by
      ext x
      rw [Finset.mem_map_equiv, Equiv.symm_swap, Equiv.swap_apply_def]
      split_ifs with hxi hxj
      · exact hxi ▸ h.symm
      · exact hxj ▸ h
      · rfl
    by_cases hi : i ∈ S <;> by_cases hj : j ∈ S
    · rw [hfix (iff_of_true hi hj)]
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      have hmap_eq : S.map π.toEmbedding = insert j (S.erase i) := by
        ext x
        rw [Finset.mem_map_equiv, Equiv.symm_swap, Finset.mem_insert, Finset.mem_erase]
        by_cases hxi : x = i
        · subst hxi; simp [hj, hij]
        · by_cases hxj : x = j
          · subst hxj; simp [hi]
          · simp [Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]
      rw [hmap_eq, (hsym (S.erase i) (Finset.notMem_erase i S)
        (fun h => hj (Finset.erase_subset i S h))).symm, Finset.insert_erase hi]
    · have hji : j ≠ i := fun h => hi (h ▸ hj)
      have hmap_eq : S.map π.toEmbedding = insert i (S.erase j) := by
        ext x
        rw [Finset.mem_map_equiv, Equiv.symm_swap, Finset.mem_insert, Finset.mem_erase]
        by_cases hxi : x = i
        · subst hxi; simp [hj]
        · by_cases hxj : x = j
          · subst hxj; simp [hi, hji]
          · simp [Equiv.swap_apply_of_ne_of_ne hxi hxj, hxi, hxj]
      rw [hmap_eq, hsym (S.erase j) (fun h => hi (Finset.erase_subset j S h))
        (Finset.notMem_erase j S), Finset.insert_erase hj]
    · rw [hfix (iff_of_false hi hj)]
  have h := hanon π G i
  rw [hperm, Equiv.swap_apply_left] at h
  exact h.symm

section ShapleyAxiomsAndUniqueness

variable {A : Type*} [Fintype A] [DecidableEq A]

/-- `shapleyValue` satisfies **Efficiency**: the marginal costs along each agent ordering `σ`
telescope to `G.cost univ - G.cost ∅ = G.cost univ`. -/
theorem shapleyValue_isEfficient : IsEfficientValue (shapleyValue (A := A)) := by
  intro G
  simp only [shapleyValue_eq_permShapleyValue, permShapleyValue, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have htelescope : ∀ σ : Fin (Fintype.card A) ≃ A,
      (∑ i : A, (G.cost (insert i (orderPredecessors σ i)) - G.cost (orderPredecessors σ i))) =
        G.cost Finset.univ := by
    intro σ
    let pref : ℕ → Finset A := fun m => Finset.univ.filter (fun j : A => (σ.symm j : ℕ) < m)
    have hpref0 : pref 0 = ∅ := by
      ext j
      simp [pref]
    have hprefN : pref (Fintype.card A) = Finset.univ := by
      ext j
      simp [pref]
    rw [← Equiv.sum_comp σ]
    have hstep : ∀ k : Fin (Fintype.card A),
        G.cost (insert (σ k) (orderPredecessors σ (σ k))) -
          G.cost (orderPredecessors σ (σ k)) =
        G.cost (pref ((k : ℕ) + 1)) - G.cost (pref (k : ℕ)) := by
      intro k
      have hpred : orderPredecessors σ (σ k) = pref (k : ℕ) := by
        ext j
        simp only [orderPredecessors, pref, Finset.mem_filter, Finset.mem_univ, true_and,
          σ.symm_apply_apply]
        exact Iff.rfl
      have hins : insert (σ k) (orderPredecessors σ (σ k)) = pref ((k : ℕ) + 1) := by
        ext j
        simp only [Finset.mem_insert, orderPredecessors, pref, Finset.mem_filter, Finset.mem_univ,
          true_and, σ.symm_apply_apply]
        change (j = σ k ∨ (σ.symm j : ℕ) < (k : ℕ)) ↔ (σ.symm j : ℕ) < (k : ℕ) + 1
        rw [Nat.lt_add_one_iff_lt_or_eq, Fin.val_inj, σ.symm_apply_eq, or_comm]
      rw [hins, hpred]
    rw [Finset.sum_congr rfl fun k _ => hstep k,
      Fin.sum_univ_eq_sum_range (fun m => G.cost (pref (m + 1)) - G.cost (pref m)),
      Finset.sum_range_sub (fun m => G.cost (pref m)), hprefN, hpref0, G.cost_empty, sub_zero]
  rw [Finset.sum_congr rfl fun σ _ => htelescope σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_equiv (Fintype.equivFin A).symm, Fintype.card_fin, nsmul_eq_mul]
  rw [inv_mul_cancel_left₀ (by positivity)]

/-- `shapleyValue` satisfies **Anonymity**. -/
theorem shapleyValue_isAnonymous : IsAnonymousValue (shapleyValue (A := A)) := by
  intro π G i
  rw [shapleyValue, shapleyValue]
  have her : Finset.univ.erase (π i) = (Finset.univ.erase i).map π.toEmbedding := by
    ext x
    simp
  rw [her, sum_powerset_map]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hmap_symm : (S.map π.toEmbedding).map π.symm.toEmbedding = S := by
    ext x; simp [Finset.mem_map_equiv]
  have hins_symm : (insert (π i) (S.map π.toEmbedding)).map π.symm.toEmbedding = insert i S := by
    ext x; simp [Finset.mem_map_equiv]
  simp only [CostSharingGame.perm_cost, Finset.card_map, hmap_symm, hins_symm]

/-- `shapleyValue` satisfies **Symmetry**. -/
theorem shapleyValue_isSymmetric : IsSymmetricValue (shapleyValue (A := A)) :=
  shapleyValue_isAnonymous.isSymmetricValue

/-- `shapleyValue` satisfies the **Dummy** axiom. -/
theorem shapleyValue_satisfiesDummy : SatisfiesDummy (shapleyValue (A := A)) := by
  intro G i hdum
  rw [shapleyValue]
  refine Finset.sum_eq_zero fun S hS => ?_
  have hiS : i ∉ S := fun hi => (Finset.mem_erase.1 (Finset.mem_powerset.1 hS hi)).1 rfl
  rw [hdum S hiS, sub_self, mul_zero]

/-- `shapleyValue` satisfies **Additivity**. -/
theorem shapleyValue_isAdditive : IsAdditiveValue (shapleyValue (A := A)) := by
  intro G₁ G₂
  ext i
  simp only [Pi.add_apply, shapleyValue, CostSharingGame.add_cost, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  ring

/-- Scaled **unanimity game** `unanimityGame T hT w` for a nonempty coalition `T` and real weight
`w`: `cost S = w` if `T ⊆ S` and `0` otherwise. -/
def unanimityGame (T : Finset A) (hT : T.Nonempty) (w : ℝ) : CostSharingGame A where
  cost S := if T ⊆ S then w else 0
  cost_empty := by
    have hnot : ¬ T ⊆ ∅ := fun hsub => hT.ne_empty (Finset.subset_empty.1 hsub)
    simp only [hnot, ↓reduceIte]

omit [Fintype A] in
@[simp]
theorem unanimityGame_cost (T : Finset A) (hT : T.Nonempty) (w : ℝ) (S : Finset A) :
    (unanimityGame T hT w).cost S = if T ⊆ S then w else 0 := by
  rfl

/-- Möbius basis expansion: every TU cost-sharing game `G` is the finite sum of scaled unanimity
games over all nonempty coalitions `T`, weighted by the subset Möbius transform (Harsanyi dividend)
`Cslib.BitString.subsetMobius G.cost T`. -/
theorem eq_sum_unanimityGame (G : CostSharingGame A) :
    G = ∑ x ∈ ((Finset.univ : Finset A).powerset.filter Finset.Nonempty).attach,
      unanimityGame x.1 (Finset.mem_filter.1 x.2).2 (Cslib.BitString.subsetMobius G.cost x.1) := by
  ext S
  have hdiv0 : Cslib.BitString.subsetMobius G.cost ∅ = 0 := by
    simp [Cslib.BitString.subsetMobius]
  have hpow : (Finset.univ : Finset A).powerset.filter (· ⊆ S) = S.powerset := by
    ext T
    simp
  -- Only the coalitions `T ⊆ S` contribute; the empty coalition has dividend `0`.
  rw [CostSharingGame.sum_cost]
  simp only [unanimityGame_cost]
  rw [Finset.sum_attach _ fun T => if T ⊆ S then Cslib.BitString.subsetMobius G.cost T else 0,
    Finset.sum_filter_of_ne fun T _ h =>
      Finset.nonempty_iff_ne_empty.2 fun hT => h (by simp only [hT, Finset.empty_subset,
        ↓reduceIte, hdiv0]),
    ← Finset.sum_filter, hpow, Cslib.BitString.sum_powerset_subsetMobius]

private theorem value_unanimityGame_of_axioms {φ : CostSharingGame A → A → ℝ}
    (heff : IsEfficientValue φ) (hsym : IsSymmetricValue φ) (hdum : SatisfiesDummy φ)
    (T : Finset A) (hT : T.Nonempty) (w : ℝ) (i : A) :
    φ (unanimityGame T hT w) i = if i ∈ T then w / (T.card : ℝ) else 0 := by
  have hdum_out : ∀ j ∉ T, φ (unanimityGame T hT w) j = 0 := by
    intro j hjT
    refine hdum _ j fun S _ => ?_
    have hiff : T ⊆ insert j S ↔ T ⊆ S :=
      ⟨fun h x hx => (Finset.mem_insert.1 (h hx)).resolve_left (fun hxj => hjT (hxj ▸ hx)),
       fun h => h.trans (Finset.subset_insert j S)⟩
    simp only [unanimityGame_cost, hiff]
  have hsym_in : ∀ j ∈ T, ∀ k ∈ T,
      φ (unanimityGame T hT w) j = φ (unanimityGame T hT w) k := by
    intro j hjT k hkT
    refine hsym _ j k fun S hjS hkS => ?_
    simp only [unanimityGame]
    by_cases hjk : j = k
    · subst hjk; rfl
    · have hnj : ¬ T ⊆ insert j S := fun h =>
        hkS ((Finset.mem_insert.1 (h hkT)).resolve_left (Ne.symm hjk))
      have hnk : ¬ T ⊆ insert k S := fun h =>
        hjS ((Finset.mem_insert.1 (h hjT)).resolve_left hjk)
      simp only [hnj, hnk, ↓reduceIte]
  by_cases hiT : i ∈ T
  · simp only [hiT, ↓reduceIte]
    have htot := heff (unanimityGame T hT w)
    have huniv_cost : (unanimityGame T hT w).cost Finset.univ = w := by
      simp only [unanimityGame, Finset.subset_univ T, ↓reduceIte]
    rw [huniv_cost] at htot
    have hsplit : (∑ j : A, φ (unanimityGame T hT w) j) = (T.card : ℝ) *
        φ (unanimityGame T hT w) i := by
      calc
        (∑ j : A, φ (unanimityGame T hT w) j)
          = ∑ j ∈ T, φ (unanimityGame T hT w) j :=
            (Finset.sum_subset (Finset.subset_univ T) fun j _ hjT => hdum_out j hjT).symm
        _ = ∑ _j ∈ T, φ (unanimityGame T hT w) i :=
            Finset.sum_congr rfl fun j hj => hsym_in j hj i hiT
        _ = (T.card : ℝ) * φ (unanimityGame T hT w) i := by rw [Finset.sum_const, nsmul_eq_mul]
    rw [hsplit] at htot
    have hcard_pos : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.2 hT
    exact eq_div_of_mul_eq hcard_pos.ne' (by linarith)
  · simp only [hiT, ↓reduceIte]
    exact hdum_out i hiT

omit [Fintype A] in
private theorem value_sum_of_isAdditive {φ : CostSharingGame A → A → ℝ}
    (hdum : SatisfiesDummy φ) (hadd : IsAdditiveValue φ)
    {ι : Type*} (s : Finset ι) (f : ι → CostSharingGame A) :
    φ (∑ k ∈ s, f k) = ∑ k ∈ s, φ (f k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext i
    simp only [Finset.sum_empty, Pi.zero_apply]
    exact hdum 0 i fun _ _ => rfl
  | insert k s hks ih =>
    rw [Finset.sum_insert hks, hadd, ih, Finset.sum_insert hks]

/-- **Theorem 15.26 (Shapley's uniqueness theorem, Symmetry form)** (Shapley 1953;
[JainMahdian2007], p. 404): any value operator `φ` satisfying Efficiency, Symmetry, Dummy, and
Additivity equals `shapleyValue`. -/
theorem eq_shapleyValue_of_axioms {φ : CostSharingGame A → A → ℝ}
    (heff : IsEfficientValue φ) (hsym : IsSymmetricValue φ)
    (hdum : SatisfiesDummy φ) (hadd : IsAdditiveValue φ) :
    φ = shapleyValue := by
  funext G
  have hbasis := eq_sum_unanimityGame G
  conv_lhs => rw [hbasis]
  conv_rhs => rw [hbasis]
  rw [value_sum_of_isAdditive hdum hadd,
    value_sum_of_isAdditive shapleyValue_satisfiesDummy shapleyValue_isAdditive]
  refine Finset.sum_congr rfl fun x _ => ?_
  ext i
  rw [value_unanimityGame_of_axioms heff hsym hdum,
    value_unanimityGame_of_axioms shapleyValue_isEfficient shapleyValue_isSymmetric
      shapleyValue_satisfiesDummy]

/-- **Theorem 15.26 (Shapley's uniqueness theorem, Anonymity form)** ([JainMahdian2007],
Definition 15.25 & Theorem 15.26, p. 404): `shapleyValue` is the unique value operator satisfying
Efficiency, Anonymity, Dummy, and Additivity.

Note: here `φ` ranges over all real-valued operators `CostSharingGame A → A → ℝ` rather than
Definition 15.25's `ℝ₊^n`-valued restriction on monotone cost functions. -/
theorem existsUnique_shapleyValue :
    ∃! φ : CostSharingGame A → A → ℝ,
      IsEfficientValue φ ∧ IsAnonymousValue φ ∧ SatisfiesDummy φ ∧ IsAdditiveValue φ :=
  ⟨shapleyValue,
    ⟨shapleyValue_isEfficient, shapleyValue_isAnonymous,
      shapleyValue_satisfiesDummy, shapleyValue_isAdditive⟩,
    fun _ ⟨heff, hanon, hdum, hadd⟩ =>
      eq_shapleyValue_of_axioms heff hanon.isSymmetricValue hdum hadd⟩

end ShapleyAxiomsAndUniqueness

/-! ## Exercise 15.2: Cross-monotonicity of the Shapley value on submodular games -/

namespace CostSharingGame

section ShapleyScheme

variable {A : Type*} [DecidableEq A]

/-- Coalition-restricted **Shapley cost-sharing scheme** `shapleyScheme G` ([JainMahdian2007],
Section 15.6.1 and Exercise 15.2): on serviced coalition `T`, each `i ∈ T` pays its Shapley value
in the restricted game `G.restrict T`, and agents outside `T` pay `0`. -/
noncomputable def shapleyScheme (G : CostSharingGame A) : CostSharingScheme A where
  share T i :=
    if i ∈ T then
      ∑ S ∈ (T.erase i).powerset,
        shapleyWeight T.card S.card * (G.cost (insert i S) - G.cost S)
    else 0
  share_eq_zero_of_not_mem {_ _} hi := by simp only [hi, ↓reduceIte]

@[simp]
theorem shapleyScheme_share (G : CostSharingGame A) (T : Finset A) (i : A) :
    G.shapleyScheme.share T i =
      if i ∈ T then
        ∑ S ∈ (T.erase i).powerset,
          shapleyWeight T.card S.card * (G.cost (insert i S) - G.cost S)
      else 0 := by
  rfl

theorem shapleyScheme_univ_eq_shapleyValue [Fintype A] (G : CostSharingGame A) :
    G.shapleyScheme.share Finset.univ = shapleyValue G := by
  ext i
  simp [shapleyScheme, shapleyValue, Finset.card_univ]

theorem shapleyScheme_eq_restrict (G : CostSharingGame A) {T : Finset A} {i : A} (hi : i ∈ T) :
    G.shapleyScheme.share T i = shapleyValue (G.restrict T) ⟨i, hi⟩ := by
  simp only [shapleyScheme, hi, ↓reduceIte, shapleyValue, Fintype.card_coe]
  have her : T.erase i =
      (Finset.univ.erase (⟨i, hi⟩ : {x // x ∈ T})).map (Function.Embedding.subtype _) := by
    ext x
    simp [Finset.mem_map]
  rw [her, sum_powerset_map]
  refine Finset.sum_congr rfl fun S _ => ?_
  simp only [restrict_cost, Finset.card_map, Finset.map_insert, Function.Embedding.coe_subtype]

/-- `shapleyScheme G` is `1`-budget-balanced for every cost-sharing game `G` (by Shapley
efficiency on each subcoalition `T`). -/
theorem shapleyScheme_isBudgetBalanced (G : CostSharingGame A) :
    G.shapleyScheme.IsBudgetBalanced G 1 := by
  rw [CostSharingScheme.isBudgetBalanced_one_iff]
  intro T
  calc
    ∑ i ∈ T, G.shapleyScheme.share T i
      = ∑ x : {x // x ∈ T}, G.shapleyScheme.share T x.1 := (Finset.sum_coe_sort T _).symm
    _ = ∑ x : {x // x ∈ T}, shapleyValue (G.restrict T) x :=
        Finset.sum_congr rfl fun x _ => G.shapleyScheme_eq_restrict x.2
    _ = (G.restrict T).cost Finset.univ := shapleyValue_isEfficient (G.restrict T)
    _ = G.cost T := by
        rw [restrict_cost]
        congr 1
        ext y
        simp

private theorem shapleyWeight_split {t s : ℕ} (hs : s ≤ t) :
    shapleyWeight (t + 2) s + shapleyWeight (t + 2) (s + 1) = shapleyWeight (t + 1) s := by
  have hsub₁ : t + 2 - 1 - s = (t - s) + 1 := by omega
  have hsub₂ : t + 2 - 1 - (s + 1) = t - s := by omega
  have hsub₃ : t + 1 - 1 - s = t - s := by omega
  simp only [shapleyWeight, hsub₁, hsub₂, hsub₃]
  have hf1 : ((t - s) + 1).factorial = ((t - s) + 1) * (t - s).factorial :=
    Nat.factorial_succ (t - s)
  have hf2 : (s + 1).factorial = (s + 1) * s.factorial := Nat.factorial_succ s
  have hf3 : (t + 2).factorial = (t + 2) * (t + 1).factorial := Nat.factorial_succ (t + 1)
  rw [hf1, hf2, hf3]
  push_cast
  have hne1 : ((t + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (t + 1)
  have hne2 : ((t : ℝ) + 2) ≠ 0 := by positivity
  rw [Nat.cast_sub hs]
  field_simp
  ring

/-- **Exercise 15.2** ([JainMahdian2007], p. 410): for any submodular cost-sharing game `G`, the
Shapley cost-sharing scheme `G.shapleyScheme` is **cross-monotone**. -/
theorem IsSubmodular.shapleyScheme_isCrossMonotone {G : CostSharingGame A}
    (hsub : G.IsSubmodular) : G.shapleyScheme.IsCrossMonotone := by
  -- Single-agent step: adding `j ∉ T` never increases the Shapley share of `i ∈ T`.
  have hstep : ∀ (T : Finset A) (j : A), j ∉ T → ∀ i ∈ T,
      G.shapleyScheme.share (insert j T) i ≤ G.shapleyScheme.share T i := by
    intro T j hjT i hiT
    have hji : j ≠ i := fun h => hjT (h ▸ hiT)
    set E := T.erase i
    have hjE : j ∉ E := fun h => hjT (Finset.erase_subset i T h)
    have herase_ins : (insert j T).erase i = insert j E := by
      ext x
      simp only [E, Finset.mem_erase, Finset.mem_insert]
      by_cases hxi : x = i <;> simp [hxi, hji.symm]
    set t := E.card
    have hT_card : T.card = t + 1 := (Finset.card_erase_add_one hiT).symm
    have hinsT_card : (insert j T).card = t + 2 := by
      rw [Finset.card_insert_of_notMem hjT, hT_card]
    simp only [shapleyScheme, hiT, Finset.mem_insert_of_mem hiT, ↓reduceIte, herase_ins,
      hT_card, hinsT_card]
    rw [Finset.sum_powerset_insert hjE, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun S hS => ?_
    have hjS : j ∉ S := fun hj => hjE (Finset.mem_powerset.1 hS hj)
    rw [Finset.card_insert_of_notMem hjS]
    have hs_le : S.card ≤ t := Finset.card_le_card (Finset.mem_powerset.1 hS)
    have hiS : i ∉ S := fun hi => (Finset.mem_erase.1 (Finset.mem_powerset.1 hS hi)).1 rfl
    have hi_insjS : i ∉ insert j S := by simp [hji.symm, hiS]
    have hdim : G.cost (insert i (insert j S)) - G.cost (insert j S) ≤
        G.cost (insert i S) - G.cost S :=
      hsub.marginalGain_le i (Finset.subset_insert j S) hi_insjS
    have hw_nn : 0 ≤ shapleyWeight (t + 2) (S.card + 1) := shapleyWeight_nonneg _ _
    calc
      shapleyWeight (t + 2) S.card * (G.cost (insert i S) - G.cost S) +
          shapleyWeight (t + 2) (S.card + 1) *
            (G.cost (insert i (insert j S)) - G.cost (insert j S))
        ≤ shapleyWeight (t + 2) S.card * (G.cost (insert i S) - G.cost S) +
            shapleyWeight (t + 2) (S.card + 1) * (G.cost (insert i S) - G.cost S) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hdim hw_nn)
      _ = (shapleyWeight (t + 2) S.card + shapleyWeight (t + 2) (S.card + 1)) *
            (G.cost (insert i S) - G.cost S) := (add_mul _ _ _).symm
      _ = shapleyWeight (t + 1) S.card * (G.cost (insert i S) - G.cost S) := by
          rw [shapleyWeight_split hs_le]
  -- Induct on `D = T₂ \ T₁`.
  intro T₁ T₂ hT₁₂ i hiT₁
  have hind : ∀ D : Finset A, Disjoint T₁ D →
      G.shapleyScheme.share (T₁ ∪ D) i ≤ G.shapleyScheme.share T₁ i := by
    intro D
    induction D using Finset.induction_on with
    | empty =>
      intro _
      simp
    | insert j D hjD ih =>
      intro hdisj
      obtain ⟨hjT₁, hdisj'⟩ := Finset.disjoint_insert_right.1 hdisj
      have hj_not : j ∉ T₁ ∪ D := by simp [hjT₁, hjD]
      rw [Finset.union_insert]
      exact (hstep (T₁ ∪ D) j hj_not i (Finset.subset_union_left hiT₁)).trans (ih hdisj')
  have h := hind (T₂ \ T₁) Finset.disjoint_sdiff
  rwa [Finset.union_sdiff_of_subset hT₁₂] at h

/-- **Shapley (1953)** ([JainMahdian2007], Section 15.6.1, p. 403): for any submodular cost-sharing
game `G`, `shapleyValue G` lies in the **core** of `G` (immediate from Exercise 15.2 and
Proposition 15.14). -/
theorem IsSubmodular.shapleyValue_inCore [Fintype A] {G : CostSharingGame A}
    (hsub : G.IsSubmodular) : G.InCore (shapleyValue G) := by
  rw [← G.shapleyScheme_univ_eq_shapleyValue]
  exact G.shapleyScheme.inCore_univ G.shapleyScheme_isBudgetBalanced
    hsub.shapleyScheme_isCrossMonotone

end ShapleyScheme

end CostSharingGame

/-! ## The Nash bargaining solution (Definition 15.27 & Theorem 15.28) -/

/-- A 2-player **Nash bargaining problem** ([JainMahdian2007], Section 15.6.3, pp. 404–405; Nash
1950): a compact, convex feasible utility set `feasible : Set (ℝ × ℝ)` containing a disagreement
outcome `disagreement ∈ feasible` and at least one strictly individually rational outcome `x` with
`disagreement.1 < x.1` and `disagreement.2 < x.2`. -/
structure BargainingProblem where
  /-- Set of feasible utility pairs `(u₁, u₂)`. -/
  feasible : Set (ℝ × ℝ)
  /-- Disagreement outcome `(d₁, d₂)` if negotiations break down. -/
  disagreement : ℝ × ℝ
  /-- The disagreement outcome is feasible. -/
  disagreement_mem : disagreement ∈ feasible
  /-- The feasible set is convex (e.g. closed under lotteries). -/
  convex : Convex ℝ feasible
  /-- The feasible set is compact. -/
  isCompact : IsCompact feasible
  /-- Both players can strictly gain over disagreement. -/
  exists_strictlyIR : ∃ x ∈ feasible, disagreement.1 < x.1 ∧ disagreement.2 < x.2

namespace BargainingProblem

/-- Individually rational feasible subset `{x ∈ feasible | d₁ ≤ x₁ ∧ d₂ ≤ x₂}`. -/
def individuallyRational (B : BargainingProblem) : Set (ℝ × ℝ) :=
  B.feasible ∩ {x : ℝ × ℝ | B.disagreement.1 ≤ x.1 ∧ B.disagreement.2 ≤ x.2}

@[simp]
theorem mem_individuallyRational (B : BargainingProblem) {x : ℝ × ℝ} :
    x ∈ B.individuallyRational ↔
      x ∈ B.feasible ∧ B.disagreement.1 ≤ x.1 ∧ B.disagreement.2 ≤ x.2 := by
  rfl

/-- Nash product `(x₁ - d₁) * (x₂ - d₂)` ([JainMahdian2007], Theorem 15.28). -/
def nashProduct (B : BargainingProblem) (x : ℝ × ℝ) : ℝ :=
  (x.1 - B.disagreement.1) * (x.2 - B.disagreement.2)

@[simp]
theorem nashProduct_apply (B : BargainingProblem) (x : ℝ × ℝ) :
    B.nashProduct x = (x.1 - B.disagreement.1) * (x.2 - B.disagreement.2) := by
  rfl

theorem isCompact_individuallyRational (B : BargainingProblem) :
    IsCompact B.individuallyRational := by
  have hclosed : IsClosed {x : ℝ × ℝ | B.disagreement.1 ≤ x.1 ∧ B.disagreement.2 ≤ x.2} :=
    (isClosed_le continuous_const continuous_fst).inter
      (isClosed_le continuous_const continuous_snd)
  exact B.isCompact.inter_right hclosed

theorem convex_individuallyRational (B : BargainingProblem) :
    Convex ℝ B.individuallyRational := by
  refine B.convex.inter ?_
  intro x hx y hy a b ha hb hab
  obtain rfl : b = 1 - a := by linarith
  simp only [Set.mem_ofPred_eq, Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
    smul_eq_mul] at hx hy ⊢
  -- `d = a • d + (1 - a) • d ≤ a • x + (1 - a) • y` in each coordinate.
  exact ⟨by linarith [mul_le_mul_of_nonneg_left hx.1 ha, mul_le_mul_of_nonneg_left hy.1 hb],
    by linarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]⟩

theorem individuallyRational_nonempty (B : BargainingProblem) :
    B.individuallyRational.Nonempty :=
  ⟨B.disagreement, B.disagreement_mem, le_rfl, le_rfl⟩

/-- Apply an independent positive affine rescaling `(x₁, x₂) ↦ (a₁ x₁ + b₁, a₂ x₂ + b₂)` (`a₁, a₂
> 0`) to a bargaining problem ([JainMahdian2007], Section 15.6.3, pp. 404–405). -/
def mapAffine (B : BargainingProblem) (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (b₁ b₂ : ℝ) : BargainingProblem where
  feasible := (fun x : ℝ × ℝ => (a₁ * x.1 + b₁, a₂ * x.2 + b₂)) '' B.feasible
  disagreement := (a₁ * B.disagreement.1 + b₁, a₂ * B.disagreement.2 + b₂)
  disagreement_mem := ⟨B.disagreement, B.disagreement_mem, rfl⟩
  convex := by
    let L : ℝ × ℝ →ᵃ[ℝ] ℝ × ℝ :=
      { toFun := fun x => (a₁ * x.1 + b₁, a₂ * x.2 + b₂)
        linear :=
          { toFun := fun x => (a₁ * x.1, a₂ * x.2)
            map_add' := fun x y => by ext <;> dsimp <;> ring
            map_smul' := fun r x => by ext <;> dsimp <;> ring }
        map_vadd' := fun p v => by
          ext <;> change _ = _ + _ <;> dsimp <;> ring }
    exact B.convex.affine_image L
  isCompact := B.isCompact.image <|
    ((continuous_const.mul continuous_fst).add continuous_const).prodMk
      ((continuous_const.mul continuous_snd).add continuous_const)
  exists_strictlyIR := by
    obtain ⟨x, hx, hx₁, hx₂⟩ := B.exists_strictlyIR
    exact ⟨(a₁ * x.1 + b₁, a₂ * x.2 + b₂), ⟨x, hx, rfl⟩, by nlinarith, by nlinarith⟩

@[simp]
theorem mapAffine_feasible (B : BargainingProblem) (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (b₁ b₂ : ℝ) :
    (B.mapAffine a₁ a₂ ha₁ ha₂ b₁ b₂).feasible =
      (fun x : ℝ × ℝ => (a₁ * x.1 + b₁, a₂ * x.2 + b₂)) '' B.feasible := by
  rfl

@[simp]
theorem mapAffine_disagreement (B : BargainingProblem) (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (b₁ b₂ : ℝ) :
    (B.mapAffine a₁ a₂ ha₁ ha₂ b₁ b₂).disagreement =
      (a₁ * B.disagreement.1 + b₁, a₂ * B.disagreement.2 + b₂) := by
  rfl

/-- A bargaining problem is **symmetric** ([JainMahdian2007], Definition 15.27) if
`d₁ = d₂` and `(x₁, x₂) ∈ feasible ↔ (x₂, x₁) ∈ feasible`. -/
@[expose] def IsSymmetric (B : BargainingProblem) : Prop :=
  B.disagreement.1 = B.disagreement.2 ∧ ∀ x : ℝ × ℝ, x ∈ B.feasible ↔ x.swap ∈ B.feasible

end BargainingProblem

section NashBargaining

private theorem exists_nashMaximizer (B : BargainingProblem) :
    ∃ xStar ∈ B.individuallyRational,
      ∀ y ∈ B.individuallyRational, B.nashProduct y ≤ B.nashProduct xStar := by
  have hcont : ContinuousOn B.nashProduct B.individuallyRational :=
    ((continuous_fst.sub continuous_const).mul (continuous_snd.sub continuous_const)).continuousOn
  obtain ⟨xStar, hxStar, hmax⟩ :=
    B.isCompact_individuallyRational.exists_isMaxOn B.individuallyRational_nonempty hcont
  exact ⟨xStar, hxStar, fun y hy => isMaxOn_iff.1 hmax y hy⟩

/-- The **Nash bargaining solution** `nashBargainingSolution B` ([JainMahdian2007], Theorem 15.28;
Nash 1950): the unique point in `B.individuallyRational` maximizing `(x₁ - d₁)(x₂ - d₂)`. -/
noncomputable def nashBargainingSolution (B : BargainingProblem) : ℝ × ℝ :=
  (exists_nashMaximizer B).choose

theorem nashBargainingSolution_mem_individuallyRational (B : BargainingProblem) :
    nashBargainingSolution B ∈ B.individuallyRational :=
  (exists_nashMaximizer B).choose_spec.1

theorem nashBargainingSolution_mem (B : BargainingProblem) :
    nashBargainingSolution B ∈ B.feasible :=
  (nashBargainingSolution_mem_individuallyRational B).1

theorem le_nashProduct_nashBargainingSolution (B : BargainingProblem) {y : ℝ × ℝ}
    (hy : y ∈ B.individuallyRational) :
    B.nashProduct y ≤ B.nashProduct (nashBargainingSolution B) :=
  (exists_nashMaximizer B).choose_spec.2 y hy

/-- `nashBargainingSolution B` achieves the maximum of `B.nashProduct` over
`B.individuallyRational`. -/
theorem isGreatest_nashBargainingSolution (B : BargainingProblem) :
    IsGreatest (B.nashProduct '' B.individuallyRational)
      (B.nashProduct (nashBargainingSolution B)) :=
  ⟨⟨nashBargainingSolution B, nashBargainingSolution_mem_individuallyRational B, rfl⟩,
   by rintro _ ⟨y, hy, rfl⟩; exact le_nashProduct_nashBargainingSolution B hy⟩

theorem nashProduct_nashBargainingSolution_pos (B : BargainingProblem) :
    0 < B.nashProduct (nashBargainingSolution B) := by
  obtain ⟨x, hx, hx₁, hx₂⟩ := B.exists_strictlyIR
  have hxIR : x ∈ B.individuallyRational := ⟨hx, hx₁.le, hx₂.le⟩
  have hpos : 0 < B.nashProduct x := mul_pos (sub_pos.2 hx₁) (sub_pos.2 hx₂)
  exact hpos.trans_le (le_nashProduct_nashBargainingSolution B hxIR)

theorem disagreement_lt_nashBargainingSolution (B : BargainingProblem) :
    B.disagreement.1 < (nashBargainingSolution B).1 ∧
      B.disagreement.2 < (nashBargainingSolution B).2 := by
  obtain ⟨_, h₁, h₂⟩ := nashBargainingSolution_mem_individuallyRational B
  have hpos := nashProduct_nashBargainingSolution_pos B
  unfold BargainingProblem.nashProduct at hpos
  refine ⟨lt_of_le_of_ne h₁ fun heq => ?_, lt_of_le_of_ne h₂ fun heq => ?_⟩
  · rw [← heq, sub_self, zero_mul] at hpos; exact lt_irrefl 0 hpos
  · rw [← heq, sub_self, mul_zero] at hpos; exact lt_irrefl 0 hpos

/-- Strict concavity / AM-GM uniqueness: `nashBargainingSolution B` is the *unique* point in
`B.individuallyRational` attaining the maximum Nash product. -/
theorem nashBargainingSolution_unique_maximizer (B : BargainingProblem) {y : ℝ × ℝ}
    (hy : y ∈ B.individuallyRational)
    (hge : B.nashProduct (nashBargainingSolution B) ≤ B.nashProduct y) :
    y = nashBargainingSolution B := by
  set x := nashBargainingSolution B
  have hxIR := nashBargainingSolution_mem_individuallyRational B
  have heq_prod : B.nashProduct y = B.nashProduct x :=
    le_antisymm (le_nashProduct_nashBargainingSolution B hy) hge
  obtain ⟨hx₁, hx₂⟩ := disagreement_lt_nashBargainingSolution B
  set u₁ := x.1 - B.disagreement.1
  set u₂ := x.2 - B.disagreement.2
  set v₁ := y.1 - B.disagreement.1
  set v₂ := y.2 - B.disagreement.2
  have hu₁ : 0 < u₁ := sub_pos.2 hx₁
  have hu₂ : 0 < u₂ := sub_pos.2 hx₂
  have hv₁_nn : 0 ≤ v₁ := sub_nonneg.2 hy.2.1
  have hv₂_nn : 0 ≤ v₂ := sub_nonneg.2 hy.2.2
  have hprod : v₁ * v₂ = u₁ * u₂ := heq_prod
  -- Midpoint `m = (1/2) • x + (1/2) • y ∈ B.individuallyRational`.
  let m : ℝ × ℝ := ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y)
  have hmIR : m ∈ B.individuallyRational :=
    B.convex_individuallyRational hxIR hy (by norm_num) (by norm_num) (by norm_num)
  have hm_le : B.nashProduct m ≤ B.nashProduct x := le_nashProduct_nashBargainingSolution B hmIR
  have hm_prod : 4 * B.nashProduct m = (u₁ + v₁) * (u₂ + v₂) := by
    simp only [BargainingProblem.nashProduct, m, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, smul_eq_mul, u₁, u₂, v₁, v₂]
    ring
  have hdiff_nonpos : (u₁ - v₁) * (v₂ - u₂) ≤ 0 := by
    have : (u₁ + v₁) * (u₂ + v₂) ≤ 4 * (u₁ * u₂) := by
      rw [← hm_prod]
      exact mul_le_mul_of_nonneg_left hm_le (by norm_num)
    nlinarith [hprod]
  have hu₁_eq_v₁ : u₁ = v₁ := by
    rcases lt_trichotomy u₁ v₁ with hlt | heq | hgt
    · have hv₂_lt : v₂ < u₂ := by
        by_contra hge₂
        nlinarith [not_lt.1 hge₂]
      have : 0 < (u₁ - v₁) * (v₂ - u₂) := mul_pos_of_neg_of_neg (sub_neg.2 hlt) (sub_neg.2 hv₂_lt)
      linarith
    · exact heq
    · have hu₂_lt : u₂ < v₂ := by
        by_contra hge₂
        nlinarith [not_lt.1 hge₂]
      have : 0 < (u₁ - v₁) * (v₂ - u₂) := mul_pos (sub_pos.2 hgt) (sub_pos.2 hu₂_lt)
      linarith
  have hu₂_eq_v₂ : u₂ = v₂ :=
    mul_left_cancel₀ hu₁.ne' (by rw [← hu₁_eq_v₁] at hprod; exact hprod.symm)
  ext
  · dsimp only [u₁, v₁] at hu₁_eq_v₁; linarith
  · dsimp only [u₂, v₂] at hu₂_eq_v₂; linarith

/-- A **bargaining solution** selects a feasible outcome `φ B ∈ B.feasible` for every bargaining
problem `B` ([JainMahdian2007], Definition 15.27). -/
@[expose] def IsBargainingSolution (φ : BargainingProblem → ℝ × ℝ) : Prop :=
  ∀ B : BargainingProblem, φ B ∈ B.feasible

/-- **Strong Pareto Optimality**: no feasible outcome weakly improves both players and strictly
improves at least one. -/
@[expose] def IsParetoOptimal (φ : BargainingProblem → ℝ × ℝ) : Prop :=
  ∀ B : BargainingProblem,
    ¬ ∃ p ∈ B.feasible, (φ B).1 ≤ p.1 ∧ (φ B).2 ≤ p.2 ∧ p ≠ φ B

/-- **Weak Pareto Optimality** ([JainMahdian2007], Definition 15.27 verbatim: "there is no point
`p ∈ X` with `p > φ(X)`, coordinate-wise"): no feasible outcome strictly improves both players. -/
@[expose] def IsWeaklyParetoOptimal (φ : BargainingProblem → ℝ × ℝ) : Prop :=
  ∀ B : BargainingProblem,
    ¬ ∃ p ∈ B.feasible, (φ B).1 < p.1 ∧ (φ B).2 < p.2

theorem IsParetoOptimal.isWeaklyParetoOptimal {φ : BargainingProblem → ℝ × ℝ}
    (hpo : IsParetoOptimal φ) : IsWeaklyParetoOptimal φ :=
  fun B ⟨p, hp, h₁, h₂⟩ => hpo B ⟨p, hp, h₁.le, h₂.le, fun heq => h₁.ne' (congr_arg Prod.fst heq)⟩

/-- **Symmetry** ([JainMahdian2007], Definition 15.27): on a symmetric bargaining problem, both
players receive equal utility `(φ B).1 = (φ B).2`. -/
@[expose] def IsSymmetricBargaining (φ : BargainingProblem → ℝ × ℝ) : Prop :=
  ∀ B : BargainingProblem, B.IsSymmetric → (φ B).1 = (φ B).2

/-- **Positive Affine Scale Invariance** ([JainMahdian2007], Section 15.6.3, pp. 404–405, combining
translation to `d = (0, 0)` and Definition 15.27 Scale Independence): independently rescaling each
player's utility by `u_i ↦ a_i u_i + b_i` (`a_i > 0`) transforms the chosen outcome identically. -/
@[expose] def IsScaleInvariant (φ : BargainingProblem → ℝ × ℝ) : Prop :=
  ∀ (B : BargainingProblem) (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (b₁ b₂ : ℝ),
    φ (B.mapAffine a₁ a₂ ha₁ ha₂ b₁ b₂) = (a₁ * (φ B).1 + b₁, a₂ * (φ B).2 + b₂)

/-- **Independence of Irrelevant Alternatives (IIA)** ([JainMahdian2007], Definition 15.27): if
`B₁` and `B₂` share the same disagreement point, `B₁.feasible ⊆ B₂.feasible`, and `φ B₂ ∈
B₁.feasible`, then `φ B₁ = φ B₂`. -/
@[expose] def SatisfiesIIA (φ : BargainingProblem → ℝ × ℝ) : Prop :=
  ∀ B₁ B₂ : BargainingProblem,
    B₁.disagreement = B₂.disagreement →
    B₁.feasible ⊆ B₂.feasible →
    φ B₂ ∈ B₁.feasible →
    φ B₁ = φ B₂

theorem nashBargainingSolution_isBargainingSolution :
    IsBargainingSolution nashBargainingSolution :=
  nashBargainingSolution_mem

theorem nashBargainingSolution_isParetoOptimal :
    IsParetoOptimal nashBargainingSolution := by
  rintro B ⟨p, hp, h₁, h₂, hne⟩
  obtain ⟨hd₁, hd₂⟩ := disagreement_lt_nashBargainingSolution B
  have hpIR : p ∈ B.individuallyRational := ⟨hp, (hd₁.le).trans h₁, (hd₂.le).trans h₂⟩
  have hge : B.nashProduct (nashBargainingSolution B) ≤ B.nashProduct p :=
    mul_le_mul (sub_le_sub_right h₁ _) (sub_le_sub_right h₂ _)
      (sub_nonneg.2 hd₂.le) (sub_nonneg.2 (hd₁.le.trans h₁))
  exact hne (nashBargainingSolution_unique_maximizer B hpIR hge)

theorem nashBargainingSolution_isSymmetric :
    IsSymmetricBargaining nashBargainingSolution := by
  intro B ⟨hd, hswap⟩
  set x := nashBargainingSolution B
  have hxIR := nashBargainingSolution_mem_individuallyRational B
  have hswapIR : x.swap ∈ B.individuallyRational :=
    ⟨(hswap x).1 hxIR.1, hd ▸ hxIR.2.2, hd.symm ▸ hxIR.2.1⟩
  have hprod_eq : B.nashProduct x ≤ B.nashProduct x.swap := by
    simp only [BargainingProblem.nashProduct, Prod.fst_swap, Prod.snd_swap, hd]
    exact (mul_comm _ _).le
  have heq := nashBargainingSolution_unique_maximizer B hswapIR hprod_eq
  exact (congr_arg Prod.fst heq).symm

theorem nashBargainingSolution_isScaleInvariant :
    IsScaleInvariant nashBargainingSolution := by
  intro B a₁ a₂ ha₁ ha₂ b₁ b₂
  set B' := B.mapAffine a₁ a₂ ha₁ ha₂ b₁ b₂
  set x := nashBargainingSolution B
  let Tx : ℝ × ℝ := (a₁ * x.1 + b₁, a₂ * x.2 + b₂)
  have hxIR := nashBargainingSolution_mem_individuallyRational B
  have hTxIR : Tx ∈ B'.individuallyRational :=
    ⟨by
      rw [show B'.feasible = _ from BargainingProblem.mapAffine_feasible B a₁ a₂ ha₁ ha₂ b₁ b₂]
      exact ⟨x, hxIR.1, rfl⟩,
      by simp only [Tx, B', BargainingProblem.mapAffine_disagreement]; nlinarith [hxIR.2.1],
      by simp only [Tx, B', BargainingProblem.mapAffine_disagreement]; nlinarith [hxIR.2.2]⟩
  refine (nashBargainingSolution_unique_maximizer B' hTxIR ?_).symm
  obtain ⟨hy_mem, hy₁, hy₂⟩ := nashBargainingSolution_mem_individuallyRational B'
  rw [show B'.feasible = _ from BargainingProblem.mapAffine_feasible B a₁ a₂ ha₁ ha₂ b₁ b₂]
    at hy_mem
  obtain ⟨y, hy, hy_eq⟩ := hy_mem
  have hyIR : y ∈ B.individuallyRational := by
    rw [← hy_eq] at hy₁ hy₂
    simp only [B', BargainingProblem.mapAffine_disagreement] at hy₁ hy₂
    exact ⟨hy, by nlinarith, by nlinarith⟩
  have hle := le_nashProduct_nashBargainingSolution B hyIR
  rw [← hy_eq]
  have hscale : ∀ z : ℝ × ℝ,
      B'.nashProduct (a₁ * z.1 + b₁, a₂ * z.2 + b₂) = (a₁ * a₂) * B.nashProduct z := by
    intro z
    simp only [BargainingProblem.nashProduct, B', BargainingProblem.mapAffine_disagreement]
    ring
  rw [hscale y, show Tx = (a₁ * x.1 + b₁, a₂ * x.2 + b₂) from rfl, hscale x]
  exact mul_le_mul_of_nonneg_left hle (mul_pos ha₁ ha₂).le

theorem nashBargainingSolution_satisfiesIIA :
    SatisfiesIIA nashBargainingSolution := by
  intro B₁ B₂ hd hsub hmem
  have hx₂IR := nashBargainingSolution_mem_individuallyRational B₂
  have hx₁IR : nashBargainingSolution B₂ ∈ B₁.individuallyRational :=
    ⟨hmem, hd.symm ▸ hx₂IR.2.1, hd.symm ▸ hx₂IR.2.2⟩
  refine (nashBargainingSolution_unique_maximizer B₁ hx₁IR ?_).symm
  have hy₁IR := nashBargainingSolution_mem_individuallyRational B₁
  have hy₂IR : nashBargainingSolution B₁ ∈ B₂.individuallyRational :=
    ⟨hsub hy₁IR.1, hd ▸ hy₁IR.2.1, hd ▸ hy₁IR.2.2⟩
  have hle := le_nashProduct_nashBargainingSolution B₂ hy₂IR
  simpa only [BargainingProblem.nashProduct, hd] using hle

/-- Supporting-hyperplane tangent inequality at normalized `(1, 1)`: if `(1, 1)` maximizes `y₁ y₂`
on `{y ∈ X | y₁, y₂ ≥ 0}` for a convex set `X`, then `y₁ + y₂ ≤ 2` for *every* `y ∈ X`. -/
private theorem sum_le_two_of_unit_nashMax {B : BargainingProblem} (hd : B.disagreement = (0, 0))
    (hx : nashBargainingSolution B = (1, 1)) {y : ℝ × ℝ} (hy : y ∈ B.feasible) :
    y.1 + y.2 ≤ 2 := by
  by_contra hgt
  set δ : ℝ := y.1 + y.2 - 2
  have hδ : 0 < δ := by linarith
  set M : ℝ := |y.1 - 1| + |y.2 - 1| + |(y.1 - 1) * (y.2 - 1)| + 1
  have hM_one : 1 ≤ M := by
    dsimp only [M]
    linarith [abs_nonneg (y.1 - 1), abs_nonneg (y.2 - 1), abs_nonneg ((y.1 - 1) * (y.2 - 1))]
  have hM_pos : 0 < M := by positivity
  let t : ℝ := min (1 / (2 * M)) (δ / (2 * M))
  have ht_pos : 0 < t := lt_min (div_pos (by norm_num) (by positivity)) (div_pos hδ (by positivity))
  have htM_half : t * M ≤ 1 / 2 := by
    have ht1 : t ≤ 1 / (2 * M) := min_le_left _ _
    have := (le_div_iff₀ (by positivity : 0 < 2 * M)).1 ht1
    linarith
  have ht_le_half : t ≤ 1 / 2 := by
    have : t * 1 ≤ t * M := mul_le_mul_of_nonneg_left hM_one ht_pos.le
    linarith
  have htM_δ : t * M ≤ δ / 2 := by
    have ht2 : t ≤ δ / (2 * M) := min_le_right _ _
    have := (le_div_iff₀ (by positivity : 0 < 2 * M)).1 ht2
    linarith
  have h1_mem : ((1 : ℝ), (1 : ℝ)) ∈ B.feasible := hx ▸ nashBargainingSolution_mem B
  let z : ℝ × ℝ := (1 - t) • ((1 : ℝ), (1 : ℝ)) + t • y
  have hz_mem : z ∈ B.feasible :=
    B.convex h1_mem hy (by linarith) ht_pos.le (by ring)
  have hz_coords : z = (1 + t * (y.1 - 1), 1 + t * (y.2 - 1)) := by
    ext <;> simp only [z, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] <;> ring
  have hshift_nn : ∀ r : ℝ, |r| ≤ M → 0 ≤ 1 + t * r := fun r hr => by
    have hmul : t * (-M) ≤ t * r :=
      mul_le_mul_of_nonneg_left (by linarith [neg_abs_le r]) ht_pos.le
    linarith
  have hz₁_nn : 0 ≤ z.1 := by
    rw [hz_coords]
    exact hshift_nn (y.1 - 1) (by
      dsimp only [M]; linarith [abs_nonneg (y.2 - 1), abs_nonneg ((y.1 - 1) * (y.2 - 1))])
  have hz₂_nn : 0 ≤ z.2 := by
    rw [hz_coords]
    exact hshift_nn (y.2 - 1) (by
      dsimp only [M]; linarith [abs_nonneg (y.1 - 1), abs_nonneg ((y.1 - 1) * (y.2 - 1))])
  have hzIR : z ∈ B.individuallyRational := ⟨hz_mem, hd ▸ hz₁_nn, hd ▸ hz₂_nn⟩
  have hle_max : B.nashProduct z ≤ 1 := by
    have h := le_nashProduct_nashBargainingSolution B hzIR
    have h1 : B.nashProduct (nashBargainingSolution B) = 1 := by
      rw [hx, BargainingProblem.nashProduct, hd]
      norm_num
    linarith
  have hquad_low : -(t * (δ / 2)) ≤ t ^ 2 * ((y.1 - 1) * (y.2 - 1)) := by
    have hlow : -M ≤ (y.1 - 1) * (y.2 - 1) := by
      dsimp only [M]
      linarith [abs_nonneg (y.1 - 1), abs_nonneg (y.2 - 1), neg_abs_le ((y.1 - 1) * (y.2 - 1))]
    have hmul1 : t ^ 2 * (-M) ≤ t ^ 2 * ((y.1 - 1) * (y.2 - 1)) :=
      mul_le_mul_of_nonneg_left hlow (sq_nonneg t)
    have hmul2 : t * (t * M) ≤ t * (δ / 2) :=
      mul_le_mul_of_nonneg_left htM_δ ht_pos.le
    have hsq : t ^ 2 * (-M) = -(t * (t * M)) := by ring
    linarith
  have hz_prod : B.nashProduct z = 1 + t * δ + t ^ 2 * ((y.1 - 1) * (y.2 - 1)) := by
    rw [BargainingProblem.nashProduct, hz_coords, hd]
    dsimp only [δ]
    ring
  have hpos_step : 0 < t * (δ / 2) := by positivity
  linarith

/-- **Theorem 15.28 (Nash's bargaining uniqueness theorem)** (Nash 1950; [JainMahdian2007],
Definition 15.27 & Theorem 15.28, pp. 404–405): any bargaining solution satisfying Weak Pareto
Optimality, Symmetry, Positive Affine Scale Invariance, and Independence of Irrelevant Alternatives
equals `nashBargainingSolution`. -/
theorem eq_nashBargainingSolution_of_axioms {φ : BargainingProblem → ℝ × ℝ}
    (hsol : IsBargainingSolution φ)
    (hwpo : IsWeaklyParetoOptimal φ)
    (hsym : IsSymmetricBargaining φ)
    (hscale : IsScaleInvariant φ)
    (hiia : SatisfiesIIA φ) :
    φ = nashBargainingSolution := by
  funext B
  set d := B.disagreement
  set x := nashBargainingSolution B
  obtain ⟨hd₁, hd₂⟩ := disagreement_lt_nashBargainingSolution B
  set u₁ : ℝ := x.1 - d.1
  set u₂ : ℝ := x.2 - d.2
  have hu₁ : 0 < u₁ := sub_pos.2 hd₁
  have hu₂ : 0 < u₂ := sub_pos.2 hd₂
  let a₁ : ℝ := u₁⁻¹
  let a₂ : ℝ := u₂⁻¹
  have ha₁ : 0 < a₁ := inv_pos.2 hu₁
  have ha₂ : 0 < a₂ := inv_pos.2 hu₂
  let b₁ : ℝ := -(a₁ * d.1)
  let b₂ : ℝ := -(a₂ * d.2)
  set B' := B.mapAffine a₁ a₂ ha₁ ha₂ b₁ b₂
  have hd' : B'.disagreement = (0, 0) := by
    ext <;> simp only [B', BargainingProblem.mapAffine_disagreement, b₁, b₂] <;> ring
  have hx' : nashBargainingSolution B' = (1, 1) := by
    rw [nashBargainingSolution_isScaleInvariant]
    ext <;> dsimp only [a₁, a₂, b₁, b₂] <;> rw [← sub_eq_add_neg, ← mul_sub]
    exacts [inv_mul_cancel₀ hu₁.ne', inv_mul_cancel₀ hu₂.ne']
  have hsum_le : ∀ y ∈ B'.feasible, y.1 + y.2 ≤ 2 :=
    fun _ hy => sum_le_two_of_unit_nashMax hd' hx' hy
  -- Enclose `B'.feasible` inside a compact, convex, symmetric triangle `H`.
  have hcont_bound : ContinuousOn (fun y : ℝ × ℝ => max (-y.1) (-y.2)) B'.feasible :=
    (continuous_fst.neg.max continuous_snd.neg).continuousOn
  obtain ⟨y₀, _, hy₀_max⟩ :=
    B'.isCompact.exists_isMaxOn ⟨B'.disagreement, B'.disagreement_mem⟩ hcont_bound
  let R : ℝ := max 1 (max (-y₀.1) (-y₀.2))
  have hR_one : 1 ≤ R := le_max_left _ _
  let H : Set (ℝ × ℝ) := {y : ℝ × ℝ | -R ≤ y.1 ∧ -R ≤ y.2 ∧ y.1 + y.2 ≤ 2}
  have h0_mem_H : ((0 : ℝ), (0 : ℝ)) ∈ H := ⟨by linarith, by linarith, by norm_num⟩
  have h1_mem_H : ((1 : ℝ), (1 : ℝ)) ∈ H := ⟨by linarith, by linarith, by norm_num⟩
  have hsub_H : B'.feasible ⊆ H := by
    intro y hy
    have hmax_le : max (-y.1) (-y.2) ≤ R :=
      (isMaxOn_iff.1 hy₀_max y hy).trans (le_max_right _ _)
    have hy₁ : -y.1 ≤ R := (le_max_left _ _).trans hmax_le
    have hy₂ : -y.2 ≤ R := (le_max_right _ _).trans hmax_le
    exact ⟨by linarith, by linarith, hsum_le y hy⟩
  have hH_convex : Convex ℝ H := by
    intro p hp q hq u v hu hv huv
    simp only [H, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    refine ⟨?_, ?_, ?_⟩
    · have : -R = u * (-R) + v * (-R) := by linear_combination -R * huv.symm
      nlinarith [hp.1, hq.1]
    · have : -R = u * (-R) + v * (-R) := by linear_combination -R * huv.symm
      nlinarith [hp.2.1, hq.2.1]
    · have : 2 = u * 2 + v * 2 := by linear_combination 2 * huv.symm
      nlinarith [hp.2.2, hq.2.2]
  have hH_compact : IsCompact H := by
    have hH_eq : H = (Set.Icc (-R) (2 + R) ×ˢ Set.Icc (-R) (2 + R)) ∩
        {y : ℝ × ℝ | y.1 + y.2 ≤ 2} := by
      ext y
      simp only [H, Set.mem_inter_iff, Set.mem_prod, Set.mem_Icc, Set.mem_ofPred_eq]
      exact ⟨fun ⟨h₁, h₂, hs⟩ => ⟨⟨⟨h₁, by linarith⟩, ⟨h₂, by linarith⟩⟩, hs⟩,
        fun ⟨⟨⟨h₁, _⟩, ⟨h₂, _⟩⟩, hs⟩ => ⟨h₁, h₂, hs⟩⟩
    rw [hH_eq]
    exact (isCompact_Icc.prod isCompact_Icc).inter_right
      (isClosed_le (continuous_fst.add continuous_snd) continuous_const)
  let B'' : BargainingProblem :=
    { feasible := H
      disagreement := (0, 0)
      disagreement_mem := h0_mem_H
      convex := hH_convex
      isCompact := hH_compact
      exists_strictlyIR := ⟨(1, 1), h1_mem_H, by norm_num, by norm_num⟩ }
  have hB''_sym : B''.IsSymmetric := by
    refine ⟨rfl, fun y => ?_⟩
    simp only [B'', H, Set.mem_ofPred_eq, Prod.fst_swap, Prod.snd_swap]
    exact ⟨fun ⟨h₁, h₂, hs⟩ => ⟨h₂, h₁, by linarith⟩,
      fun ⟨h₂, h₁, hs⟩ => ⟨h₁, h₂, by linarith⟩⟩
  have hφB'' : φ B'' = (1, 1) := by
    have hmem := hsol B''
    simp only [B'', H, Set.mem_ofPred_eq] at hmem
    have hsym_eq : (φ B'').1 = (φ B'').2 := hsym B'' hB''_sym
    have hle1 : (φ B'').1 ≤ 1 := by linarith [hmem.2.2]
    -- Weak Pareto optimality rules out `(φ B'').1 = (φ B'').2 < 1`, as `(1, 1) ∈ H`.
    have hge1 : 1 ≤ (φ B'').1 :=
      not_lt.1 fun hlt => hwpo B'' ⟨(1, 1), h1_mem_H, hlt, hsym_eq ▸ hlt⟩
    have h1 : (φ B'').1 = 1 := le_antisymm hle1 hge1
    exact Prod.ext h1 (hsym_eq.symm.trans h1)
  have h1_mem_B' : ((1 : ℝ), (1 : ℝ)) ∈ B'.feasible := hx' ▸ nashBargainingSolution_mem B'
  have hφB' : φ B' = (1, 1) :=
    (hiia B' B'' hd' hsub_H (hφB''.symm ▸ h1_mem_B')).trans hφB''
  have hφB_scale : (a₁ * (φ B).1 + b₁, a₂ * (φ B).2 + b₂) = (1, 1) :=
    (hscale B a₁ a₂ ha₁ ha₂ b₁ b₂).symm.trans hφB'
  have hc₁ : u₁⁻¹ * ((φ B).1 - d.1) = 1 := by
    rw [mul_sub, sub_eq_add_neg]; exact congr_arg Prod.fst hφB_scale
  have hc₂ : u₂⁻¹ * ((φ B).2 - d.2) = 1 := by
    rw [mul_sub, sub_eq_add_neg]; exact congr_arg Prod.snd hφB_scale
  have h₁ := (inv_mul_eq_one₀ hu₁.ne').1 hc₁
  have h₂ := (inv_mul_eq_one₀ hu₂.ne').1 hc₂
  dsimp only [u₁, u₂] at h₁ h₂
  ext <;> linarith

/-- **Theorem 15.28 (Nash's bargaining theorem, existence and uniqueness)** ([JainMahdian2007],
Definition 15.27 & Theorem 15.28, pp. 404–405): `nashBargainingSolution` is the unique bargaining
solution satisfying Weak Pareto Optimality, Symmetry, Positive Affine Scale Invariance, and
Independence of Irrelevant Alternatives (and likewise under Strong Pareto Optimality). -/
theorem existsUnique_nashBargainingSolution :
    ∃! φ : BargainingProblem → ℝ × ℝ,
      IsBargainingSolution φ ∧ IsWeaklyParetoOptimal φ ∧ IsSymmetricBargaining φ ∧
        IsScaleInvariant φ ∧ SatisfiesIIA φ :=
  ⟨nashBargainingSolution,
    ⟨nashBargainingSolution_isBargainingSolution,
      nashBargainingSolution_isParetoOptimal.isWeaklyParetoOptimal,
      nashBargainingSolution_isSymmetric,
      nashBargainingSolution_isScaleInvariant,
      nashBargainingSolution_satisfiesIIA⟩,
    fun _ ⟨hsol, hwpo, hsym, hscale, hiia⟩ =>
      eq_nashBargainingSolution_of_axioms hsol hwpo hsym hscale hiia⟩

theorem existsUnique_nashBargainingSolution_paretoOptimal :
    ∃! φ : BargainingProblem → ℝ × ℝ,
      IsBargainingSolution φ ∧ IsParetoOptimal φ ∧ IsSymmetricBargaining φ ∧
        IsScaleInvariant φ ∧ SatisfiesIIA φ :=
  ⟨nashBargainingSolution,
    ⟨nashBargainingSolution_isBargainingSolution,
      nashBargainingSolution_isParetoOptimal,
      nashBargainingSolution_isSymmetric,
      nashBargainingSolution_isScaleInvariant,
      nashBargainingSolution_satisfiesIIA⟩,
    fun _ ⟨hsol, hpo, hsym, hscale, hiia⟩ =>
      eq_nashBargainingSolution_of_axioms hsol hpo.isWeaklyParetoOptimal hsym hscale hiia⟩

end NashBargaining

end Cslib.GameTheory
