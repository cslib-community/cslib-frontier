/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Cooperative.Basic
public import Mathlib.Order.Bounds.Defs
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Bondareva–Shapley theorem, approximate cores, and linear exchange economies

This module proves the linear-programming duality theory of the core for transferable-utility
cost-sharing and cooperative value games ([JainMahdian2007], Section 15.2 and Exercise 15.1):

1. **Strong LP duality** (`CostSharingGame.exists_isGreatest_isLeast_coreLP`) between the
   cost-recovery maximization LP `(15.1)` (`max ∑_j α_j` subject to `∀ S, ∑_{j ∈ S} α_j ≤ c(S)`)
   and the fractional set-cover / balanced-weights minimization LP `(15.2)`
   (`min ∑_S λ_S c(S)` subject to `IsBalancedWeights λ`), proved via
   `Matrix.exists_isGreatest_isLeast_dotProduct` from
   `CslibFrontier/Foundations/LinearAlgebra/Matrix/LinearProgramming.lean`.
2. **Theorem 15.6 (Bondareva–Shapley theorem)** (`CostSharingGame.nonemptyCore_iff_balanced` and
   its surplus dual `CooperativeGame.nonemptyCore_iff_balanced`): a TU cost-sharing game has a
   nonempty core if and only if `c(univ) ≤ ∑_S λ_S c(S)` for every balanced weight collection `λ`
   (Bondareva 1963; Shapley 1967).
3. **Theorem 15.8 (`γ`-Bondareva–Shapley theorem)**
   (`CostSharingGame.nonemptyApproxCore_iff_balanced`): a TU cost-sharing game has a nonempty
   `γ`-core if and only if `γ * c(univ) ≤ ∑_S λ_S c(S)` for every balanced weight collection `λ`.
   Strong LP duality establishes this equivalence for every real `γ` without needing `γ ≤ 1`.
4. **Corollary 15.9** (`CostSharingGame.IsSubadditive.isLeast_integralBalanced`,
   `CostSharingGame.IsSubadditive.isGreatest_nonemptyApproxCore_integralityGapLP`): defining
   `integralLpOpt` as the optimal integral value of LP `(15.2)` over `IsIntegralBalancedWeights`
   and `integralityGapLP := lpOpt / integralLpOpt` as the LP `(15.2)` integrality gap, for
   subadditive games `integralLpOpt = c(univ)` and, when `0 < c(univ)`, the largest `γ` with a
   nonempty `γ`-core equals `integralityGapLP`.
5. **Exercise 15.1** (`LinearExchangeEconomy`): the TU cooperative game of a linear Arrow–Debreu
   exchange economy — where `v(S)` is the maximum total linear utility achievable by redistributing
   coalition `S`'s endowments — always has a nonempty core.

## Main definitions

* `Cslib.GameTheory.CostSharingGame.lpOpt`: common optimal value of LPs `(15.1)` and `(15.2)`.
* `Cslib.GameTheory.IsIntegralBalancedWeights`: `ℕ`-valued balanced weights (exact coalition
  partitions, integral solutions of LP `(15.2)`).
* `Cslib.GameTheory.CostSharingGame.integralLpOpt`: optimal integral value of LP `(15.2)` over
  `IsIntegralBalancedWeights`.
* `Cslib.GameTheory.CostSharingGame.integralityGapLP`: fractional-to-integral optimum ratio
  `G.lpOpt / G.integralLpOpt` of LP `(15.2)` ([JainMahdian2007], Corollary 15.9).
* `Cslib.GameTheory.LinearExchangeEconomy`,
  `Cslib.GameTheory.LinearExchangeEconomy.IsFeasibleRedistribution`,
  `Cslib.GameTheory.LinearExchangeEconomy.IsExactRedistribution`,
  `Cslib.GameTheory.LinearExchangeEconomy.coalitionValue`,
  `Cslib.GameTheory.LinearExchangeEconomy.toCooperativeGame`,
  `Cslib.GameTheory.LinearExchangeEconomy.marketPriceAllocation`: linear Arrow–Debreu exchange
  economy TU game ([JainMahdian2007], Exercise 15.1).

## Main results

* `Cslib.GameTheory.CostSharingGame.exists_isGreatest_isLeast_coreLP`,
  `Cslib.GameTheory.CostSharingGame.isGreatest_coreFeasible_lpOpt`,
  `Cslib.GameTheory.CostSharingGame.isLeast_balanced_lpOpt`: strong duality and attainment for LPs
  `(15.1)` and `(15.2)`.
* `Cslib.GameTheory.CostSharingGame.nonemptyCore_iff_balanced`,
  `Cslib.GameTheory.CooperativeGame.nonemptyCore_iff_balanced`: **Bondareva–Shapley theorem**
  ([JainMahdian2007], Theorem 15.6).
* `Cslib.GameTheory.CostSharingGame.nonemptyApproxCore_iff_balanced`: **`γ`-Bondareva–Shapley
  theorem** ([JainMahdian2007], Theorem 15.8).
* `Cslib.GameTheory.CostSharingGame.IsSubadditive.isLeast_integralBalanced`,
  `Cslib.GameTheory.CostSharingGame.IsSubadditive.integralLpOpt_eq_cost_univ`,
  `Cslib.GameTheory.CostSharingGame.IsSubadditive.isGreatest_nonemptyApproxCore_integralityGapLP`:
  **Corollary 15.9** of [JainMahdian2007].
* `Cslib.GameTheory.LinearExchangeEconomy.isGreatest_feasibleRedistribution`,
  `Cslib.GameTheory.LinearExchangeEconomy.isGreatest_exactRedistribution`,
  `Cslib.GameTheory.LinearExchangeEconomy.marketPriceAllocation_inCore`,
  `Cslib.GameTheory.LinearExchangeEconomy.toCooperativeGame_nonemptyCore`: **Exercise 15.1** of
  [JainMahdian2007].

## References

* [JainMahdian2007]
-/

public section

namespace Cslib.GameTheory

/-! ## Strong LP duality and the Bondareva–Shapley theorems -/

namespace CostSharingGame

section Duality

open Matrix

variable {A : Type*} [Fintype A]

private def incidenceMatrix [DecidableEq A] : Matrix (Finset A) A ℝ :=
  fun S j => if j ∈ S then 1 else 0

private theorem mulVec_incidenceMatrix_le_iff [DecidableEq A] (G : CostSharingGame A)
    (α : A → ℝ) :
    incidenceMatrix *ᵥ α ≤ G.cost ↔ G.IsCoreFeasible α := by
  refine forall_congr' fun S => ?_
  simp only [Matrix.mulVec, dotProduct, incidenceMatrix, ite_mul, one_mul, zero_mul,
    ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

private theorem vecMul_incidenceMatrix_eq_iff [DecidableEq A] (w : Finset A → ℝ) :
    (0 ≤ w ∧ w ᵥ* incidenceMatrix = fun _ => 1) ↔ IsBalancedWeights w := by
  simp only [IsBalancedWeights, Pi.le_def, Pi.zero_apply, funext_iff, Matrix.vecMul, dotProduct,
    incidenceMatrix, mul_ite, mul_one, mul_zero, ← Finset.sum_filter]

/-- **Strong LP duality for LPs `(15.1)` and `(15.2)`** ([JainMahdian2007], proof of Theorem 15.6,
p. 388): the primal maximum `max {∑_j α_j | IsCoreFeasible α}` and the dual balanced-weights
minimum `min {∑_S w_S c(S) | IsBalancedWeights w}` are both attained and equal. -/
theorem exists_isGreatest_isLeast_coreLP [DecidableEq A] (G : CostSharingGame A) :
    ∃ v : ℝ,
      IsGreatest ((fun α : A → ℝ => ∑ j : A, α j) '' {α | G.IsCoreFeasible α}) v ∧
      IsLeast ((fun w : Finset A → ℝ => ∑ S : Finset A, w S * G.cost S) ''
        {w | IsBalancedWeights w}) v := by
  have hP : ∃ α : A → ℝ, incidenceMatrix *ᵥ α ≤ G.cost := by
    let B : ℝ := ∑ T : Finset A, |G.cost T|
    have hB : 0 ≤ B := Finset.sum_nonneg fun T _ => abs_nonneg (G.cost T)
    refine ⟨fun _ => -B, (G.mulVec_incidenceMatrix_le_iff _).2 fun S => ?_⟩
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp
    rw [Finset.sum_const, nsmul_eq_mul]
    linarith [le_mul_of_one_le_left hB (Nat.one_le_cast.mpr (Finset.one_le_card.2 hS)),
      neg_abs_le (G.cost S),
      Finset.single_le_sum (fun T _ => abs_nonneg (G.cost T)) (Finset.mem_univ S)]
  have hD : ∃ w : Finset A → ℝ, 0 ≤ w ∧ w ᵥ* incidenceMatrix = fun _ => 1 :=
    ⟨_, (vecMul_incidenceMatrix_eq_iff _).2 isBalancedWeights_univ⟩
  obtain ⟨v, hG, hL⟩ :=
    Matrix.exists_isGreatest_isLeast_dotProduct incidenceMatrix G.cost (fun _ => 1) hP hD
  exact ⟨v, by simpa only [dotProduct, one_mul, G.mulVec_incidenceMatrix_le_iff] using hG,
    by simpa only [dotProduct, vecMul_incidenceMatrix_eq_iff] using hL⟩

/-- The common optimal value of the cost-recovery LP `(15.1)` and the fractional balanced-weights
LP `(15.2)` ([JainMahdian2007], Section 15.2). -/
noncomputable def lpOpt (G : CostSharingGame A) : ℝ := by
  classical
  exact G.exists_isGreatest_isLeast_coreLP.choose

theorem isGreatest_coreFeasible_lpOpt (G : CostSharingGame A) :
    IsGreatest ((fun α : A → ℝ => ∑ j : A, α j) '' {α | G.IsCoreFeasible α}) G.lpOpt := by
  classical
  exact G.exists_isGreatest_isLeast_coreLP.choose_spec.1

theorem isLeast_balanced_lpOpt [DecidableEq A] (G : CostSharingGame A) :
    IsLeast ((fun w : Finset A → ℝ => ∑ S : Finset A, w S * G.cost S) ''
      {w | IsBalancedWeights w}) G.lpOpt := by
  obtain ⟨v, hG, hL⟩ := G.exists_isGreatest_isLeast_coreLP
  exact hG.unique G.isGreatest_coreFeasible_lpOpt ▸ hL

theorem lpOpt_le_cost_univ (G : CostSharingGame A) :
    G.lpOpt ≤ G.cost Finset.univ :=
  let ⟨⟨_, hα, hsum⟩, _⟩ := G.isGreatest_coreFeasible_lpOpt
  hsum ▸ hα Finset.univ

/-- **Theorem 15.8 (`γ`-Bondareva–Shapley theorem)** ([JainMahdian2007], p. 389): a TU
cost-sharing game `G` has a nonempty `γ`-core if and only if every balanced weight collection `w`
satisfies `γ * G.cost univ ≤ ∑ S, w S * G.cost S`.

Strong LP duality establishes this equivalence for every `γ : ℝ` (including `γ ≤ 1` as stated in
Theorem 15.8). -/
theorem nonemptyApproxCore_iff_balanced [DecidableEq A] (G : CostSharingGame A) (γ : ℝ) :
    G.NonemptyApproxCore γ ↔
      ∀ w : Finset A → ℝ, IsBalancedWeights w →
        γ * G.cost Finset.univ ≤ ∑ S : Finset A, w S * G.cost S := by
  refine ⟨fun ⟨α, hα⟩ _ hw => hα.mul_le_sum_balanced hw, fun h => ?_⟩
  obtain ⟨⟨α, hα, hsum⟩, -⟩ := G.isGreatest_coreFeasible_lpOpt
  obtain ⟨⟨w, hw, hwsum⟩, -⟩ := G.isLeast_balanced_lpOpt
  refine ⟨α, ⟨⟨?_, hα Finset.univ⟩, hα⟩⟩
  calc
    γ * G.cost Finset.univ ≤ ∑ S : Finset A, w S * G.cost S := h w hw
    _ = G.lpOpt := hwsum
    _ = ∑ j : A, α j := hsum.symm

theorem nonemptyApproxCore_iff_le_lpOpt (G : CostSharingGame A) (γ : ℝ) :
    G.NonemptyApproxCore γ ↔ γ * G.cost Finset.univ ≤ G.lpOpt := by
  classical
  rw [G.nonemptyApproxCore_iff_balanced]
  obtain ⟨⟨w, hw, hwsum⟩, hmin⟩ := G.isLeast_balanced_lpOpt
  exact ⟨fun h => hwsum ▸ h w hw, fun h w' hw' => h.trans (hmin ⟨w', hw', rfl⟩)⟩

/-- **Theorem 15.6 (Bondareva–Shapley theorem)** (Bondareva 1963; Shapley 1967;
[JainMahdian2007], p. 388): a TU cost-sharing game `G` has a nonempty core if and only if every
balanced weight collection `w` satisfies `G.cost univ ≤ ∑ S, w S * G.cost S`. -/
theorem nonemptyCore_iff_balanced [DecidableEq A] (G : CostSharingGame A) :
    G.NonemptyCore ↔
      ∀ w : Finset A → ℝ, IsBalancedWeights w →
        G.cost Finset.univ ≤ ∑ S : Finset A, w S * G.cost S := by
  simpa only [nonemptyApproxCore_one_iff, one_mul] using G.nonemptyApproxCore_iff_balanced 1

theorem nonemptyCore_iff_lpOpt_eq (G : CostSharingGame A) :
    G.NonemptyCore ↔ G.lpOpt = G.cost Finset.univ := by
  rw [← G.nonemptyApproxCore_one_iff, G.nonemptyApproxCore_iff_le_lpOpt, one_mul]
  exact ⟨fun h => le_antisymm G.lpOpt_le_cost_univ h, fun h => h.ge⟩

end Duality

end CostSharingGame

/-- **Bondareva–Shapley theorem for cooperative value games**: a TU surplus-sharing game `G` has a
nonempty core if and only if `∑ S, w S * G.val S ≤ G.val univ` for every balanced weight collection
`w`. -/
theorem CooperativeGame.nonemptyCore_iff_balanced {A : Type*} [Fintype A] [DecidableEq A]
    (G : CooperativeGame A) :
    G.NonemptyCore ↔
      ∀ w : Finset A → ℝ, IsBalancedWeights w →
        ∑ S : Finset A, w S * G.val S ≤ G.val Finset.univ := by
  rw [← G.nonemptyCore_toCostSharingGame_iff, G.toCostSharingGame.nonemptyCore_iff_balanced]
  refine forall₂_congr fun w _ => ?_
  simp only [CooperativeGame.toCostSharingGame_cost, mul_neg, Finset.sum_neg_distrib,
    neg_le_neg_iff]

/-! ## Corollary 15.9: Subadditivity and the integrality gap of LP `(15.2)` -/

/-- An **integral balanced weight collection** `w : Finset A → ℕ` is an integral feasible solution
of LP `(15.2)` (`∀ j, ∑_{S : j ∈ S} w S = 1`), i.e. an exact partition of `A` into coalitions
(plus an arbitrary weight on `∅`, which has cost `0`). -/
@[expose] def IsIntegralBalancedWeights {A : Type*} [Fintype A] [DecidableEq A]
    (w : Finset A → ℕ) : Prop :=
  ∀ j : A, (∑ S with j ∈ S, w S) = 1

theorem isIntegralBalancedWeights_univ {A : Type*} [Fintype A] [DecidableEq A] :
    IsIntegralBalancedWeights (fun S : Finset A => if S = Finset.univ then 1 else 0) :=
  fun _ => by simp

namespace CostSharingGame

section IntegralityGap

variable {A : Type*} [Fintype A]

omit [Fintype A] in
private theorem cost_biUnion_le_sum_of_pairwiseDisjoint [DecidableEq A] {G : CostSharingGame A}
    (hsub : G.IsSubadditive) {P : Finset (Finset A)}
    (hdisj : (P : Set (Finset A)).PairwiseDisjoint id) :
    G.cost (P.biUnion id) ≤ ∑ S ∈ P, G.cost S := by
  induction P using Finset.induction_on with
  | empty => simp
  | insert S P hSP ih =>
    rw [Finset.coe_insert] at hdisj
    rw [Finset.biUnion_insert, Finset.sum_insert hSP]
    exact (hsub ((Finset.disjoint_biUnion_right S P id).2 fun T hT =>
      hdisj (Set.mem_insert S ↑P) (Set.mem_insert_of_mem S hT) fun hST => hSP (hST ▸ hT))).trans
      (add_le_add le_rfl (ih (hdisj.subset (Set.subset_insert S ↑P))))

private theorem integralBalanced_support_spec [DecidableEq A] (G : CostSharingGame A)
    {w : Finset A → ℕ} (hw : IsIntegralBalancedWeights w) :
    let P : Finset (Finset A) := Finset.univ.filter (fun S => S.Nonempty ∧ w S ≠ 0)
    (P : Set (Finset A)).PairwiseDisjoint id ∧
      P.biUnion id = Finset.univ ∧
      ∑ S : Finset A, (w S : ℝ) * G.cost S = ∑ S ∈ P, G.cost S := by
  intro P
  have hw_one (S) (hS : S ∈ P) : w S = 1 := by
    obtain ⟨⟨j, hj⟩, hne⟩ := (Finset.mem_filter.1 hS).2
    have hle : w S ≤ ∑ T with j ∈ T, w T := Finset.single_le_sum (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ S, hj⟩)
    rw [hw j] at hle; omega
  have hP_disj : (P : Set (Finset A)).PairwiseDisjoint id := fun S₁ h₁ S₂ h₂ hne =>
    Finset.disjoint_left.2 fun j hj₁ hj₂ => by
      have hsub : ({S₁, S₂} : Finset (Finset A)) ⊆ Finset.univ.filter (j ∈ ·) := by
        simpa [Finset.insert_subset_iff] using ⟨hj₁, hj₂⟩
      have hle := Finset.sum_le_sum_of_subset hsub (f := w)
      rw [Finset.sum_pair hne, hw_one S₁ h₁, hw_one S₂ h₂, hw j] at hle; omega
  have hP_union : P.biUnion id = Finset.univ := by
    ext j
    simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
    obtain ⟨T, hT, hwT⟩ := Finset.sum_pos_iff.1 (by rw [hw j]; omega)
    exact ⟨T, Finset.mem_filter.2 ⟨Finset.mem_univ T, ⟨j, (Finset.mem_filter.1 hT).2⟩, hwT.ne'⟩,
      (Finset.mem_filter.1 hT).2⟩
  refine ⟨hP_disj, hP_union, ?_⟩
  calc
    ∑ S : Finset A, (w S : ℝ) * G.cost S
      = ∑ S ∈ P, (w S : ℝ) * G.cost S := by
        refine (Finset.sum_subset (Finset.subset_univ P) fun S _ hSP => ?_).symm
        simp only [P, Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_not] at hSP
        rcases S.eq_empty_or_nonempty with rfl | hS
        · simp
        · rw [hSP hS, Nat.cast_zero, zero_mul]
    _ = ∑ S ∈ P, G.cost S := Finset.sum_congr rfl fun S hS => by simp [hw_one S hS]

private theorem exists_isLeast_integralBalanced [DecidableEq A] (G : CostSharingGame A) :
    ∃ v : ℝ,
      IsLeast ((fun w : Finset A → ℕ => ∑ S : Finset A, (w S : ℝ) * G.cost S) ''
        {w | IsIntegralBalancedWeights w}) v := by
  classical
  let valid : Finset (Finset (Finset A)) :=
    Finset.univ.filter fun P =>
      (P : Set (Finset A)).PairwiseDisjoint id ∧ P.biUnion id = Finset.univ
  have hmem_valid {w : Finset A → ℕ} (hw : IsIntegralBalancedWeights w) :
      ∃ P ∈ valid, ∑ S : Finset A, (w S : ℝ) * G.cost S = ∑ S ∈ P, G.cost S :=
    let ⟨hdisj, hunion, hsum⟩ := G.integralBalanced_support_spec hw
    ⟨_, Finset.mem_filter.2 ⟨Finset.mem_univ _, hdisj, hunion⟩, hsum⟩
  have hof_valid : ∀ {P : Finset (Finset A)}, P ∈ valid →
      ∃ w : Finset A → ℕ, IsIntegralBalancedWeights w ∧
        ∑ S : Finset A, (w S : ℝ) * G.cost S = ∑ S ∈ P, G.cost S := by
    intro P hP
    obtain ⟨hdisj, hunion⟩ := (Finset.mem_filter.1 hP).2
    refine ⟨fun S => if S ∈ P then 1 else 0, fun j => ?_, ?_⟩
    · obtain ⟨S₀, hS₀P, hjS₀⟩ := Finset.mem_biUnion.1 (hunion.symm ▸ Finset.mem_univ j)
      rw [Finset.sum_eq_single_of_mem S₀ (Finset.mem_filter.2 ⟨Finset.mem_univ S₀, hjS₀⟩)]
      · simp [hS₀P]
      · exact fun S hS hne => ite_eq_right fun hSP =>
          Finset.disjoint_left.1 (hdisj hSP hS₀P hne) (Finset.mem_filter.1 hS).2 hjS₀
    · simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ite_mul, one_mul, zero_mul,
        ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  have hne : valid.Nonempty := (hmem_valid isIntegralBalancedWeights_univ).imp fun _ h => h.1
  obtain ⟨P₀, hP₀, hmin⟩ := valid.exists_min_image (fun P => ∑ S ∈ P, G.cost S) hne
  obtain ⟨w₀, hw₀, hsum₀⟩ := hof_valid hP₀
  exact ⟨∑ S ∈ P₀, G.cost S, ⟨w₀, hw₀, hsum₀⟩, fun _ ⟨_, hw, h⟩ =>
    let ⟨P, hP, hsum⟩ := hmem_valid hw
    h ▸ (hmin P hP).trans_eq hsum.symm⟩

/-- The optimal integral value of LP `(15.2)` over `IsIntegralBalancedWeights`
([JainMahdian2007], Section 15.2.2, p. 389). -/
noncomputable def integralLpOpt (G : CostSharingGame A) : ℝ :=
  letI := Classical.decEq A
  G.exists_isLeast_integralBalanced.choose

theorem isLeast_integralBalanced_integralLpOpt [DecidableEq A] (G : CostSharingGame A) :
    IsLeast ((fun w : Finset A → ℕ => ∑ S : Finset A, (w S : ℝ) * G.cost S) ''
      {w | IsIntegralBalancedWeights w}) G.integralLpOpt := by
  obtain rfl : ‹DecidableEq A› = Classical.decEq A := Subsingleton.elim _ _
  exact (@exists_isLeast_integralBalanced A _ (Classical.decEq A) G).choose_spec

theorem lpOpt_le_integralLpOpt (G : CostSharingGame A) :
    G.lpOpt ≤ G.integralLpOpt := by
  classical
  obtain ⟨⟨w, hw, hsum⟩, -⟩ := G.isLeast_integralBalanced_integralLpOpt
  have hbal : IsBalancedWeights (fun S => (w S : ℝ)) :=
    ⟨fun _ => Nat.cast_nonneg _, fun j => by dsimp only; rw [← Nat.cast_sum, hw j, Nat.cast_one]⟩
  exact hsum ▸ G.isLeast_balanced_lpOpt.2 ⟨fun S => (w S : ℝ), hbal, rfl⟩

/-- For a subadditive cost-sharing game, the **optimal integral value of LP `(15.2)` is precisely
`G.cost univ`** ([JainMahdian2007], p. 389, preceding Corollary 15.9). -/
theorem IsSubadditive.isLeast_integralBalanced [DecidableEq A] {G : CostSharingGame A}
    (hsub : G.IsSubadditive) :
    IsLeast ((fun w : Finset A → ℕ => ∑ S : Finset A, (w S : ℝ) * G.cost S) ''
      {w | IsIntegralBalancedWeights w}) (G.cost Finset.univ) := by
  refine ⟨⟨fun S => if S = Finset.univ then 1 else 0, isIntegralBalancedWeights_univ,
    by simp [ite_mul]⟩, ?_⟩
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨hP_disj, hP_union, hsum⟩ := G.integralBalanced_support_spec hw
  calc
    G.cost Finset.univ = G.cost _ := by rw [hP_union]
    _ ≤ _ := cost_biUnion_le_sum_of_pairwiseDisjoint hsub hP_disj
    _ = ∑ S : Finset A, (w S : ℝ) * G.cost S := hsum.symm

theorem IsSubadditive.integralLpOpt_eq_cost_univ [DecidableEq A] {G : CostSharingGame A}
    (hsub : G.IsSubadditive) :
    G.integralLpOpt = G.cost Finset.univ :=
  G.isLeast_integralBalanced_integralLpOpt.unique hsub.isLeast_integralBalanced

/-- The **integrality gap** `G.lpOpt / G.integralLpOpt` of LP `(15.2)` ([JainMahdian2007],
Corollary 15.9 and p. 390, expressed as the fractional-to-integral optimum ratio `≤ 1`, e.g.
`7.5 / 8` in Example 15.4). -/
noncomputable def integralityGapLP (G : CostSharingGame A) : ℝ :=
  G.lpOpt / G.integralLpOpt

theorem integralityGapLP_eq (G : CostSharingGame A) :
    G.integralityGapLP = G.lpOpt / G.integralLpOpt := by
  rfl

theorem integralityGapLP_le_one (G : CostSharingGame A) (hpos : 0 < G.integralLpOpt) :
    G.integralityGapLP ≤ 1 :=
  (div_le_one hpos).2 G.lpOpt_le_integralLpOpt

/-- **Corollary 15.9** ([JainMahdian2007], p. 389): for a subadditive cost-sharing game with
`0 < G.cost univ`, the largest value `γ` for which the `γ`-core of `G` is nonempty equals the
integrality gap `G.integralityGapLP = G.lpOpt / G.integralLpOpt` of LP `(15.2)`. -/
theorem IsSubadditive.isGreatest_nonemptyApproxCore_integralityGapLP [DecidableEq A]
    {G : CostSharingGame A} (hsub : G.IsSubadditive) (hpos : 0 < G.cost Finset.univ) :
    IsGreatest {γ : ℝ | G.NonemptyApproxCore γ} G.integralityGapLP := by
  refine ⟨by rw [Set.mem_ofPred_eq, G.nonemptyApproxCore_iff_le_lpOpt, integralityGapLP,
      hsub.integralLpOpt_eq_cost_univ, div_mul_cancel₀ _ hpos.ne'], fun γ hγ => ?_⟩
  rw [Set.mem_ofPred_eq, G.nonemptyApproxCore_iff_le_lpOpt] at hγ
  rwa [integralityGapLP, hsub.integralLpOpt_eq_cost_univ, le_div_iff₀ hpos]

end IntegralityGap

end CostSharingGame

/-! ## Exercise 15.1: Linear Arrow–Debreu exchange economy TU game -/

/-- A **linear Arrow–Debreu exchange economy** ([JainMahdian2007], Exercise 15.1) with agents `A`
and divisible goods `G`: each agent `i` has an initial bundle `endowment i : G → ℝ` and linear
marginal utilities `utility i : G → ℝ`. -/
structure LinearExchangeEconomy (A G : Type*) where
  /-- Initial endowment `endowment i g` of good `g` held by agent `i`. -/
  endowment : A → G → ℝ
  /-- Marginal utility `utility i g` derived by agent `i` per unit of good `g`. -/
  utility : A → G → ℝ
  /-- Initial endowments are nonnegative. -/
  endowment_nonneg : ∀ (i : A) (g : G), 0 ≤ endowment i g
  /-- Marginal utilities are nonnegative. -/
  utility_nonneg : ∀ (i : A) (g : G), 0 ≤ utility i g

namespace LinearExchangeEconomy

variable {A G : Type*}

/-- A consumption profile `x : A → G → ℝ` is a **feasible redistribution** for coalition `S` (with
free disposal) if each member receives a nonnegative bundle and `∑ i ∈ S, x i g` does not exceed
`S`'s total endowment `∑ i ∈ S, endowment i g` of every good `g`. -/
@[expose] def IsFeasibleRedistribution (E : LinearExchangeEconomy A G) (S : Finset A)
    (x : A → G → ℝ) : Prop :=
  (∀ i ∈ S, ∀ g : G, 0 ≤ x i g) ∧ ∀ g : G, ∑ i ∈ S, x i g ≤ ∑ i ∈ S, E.endowment i g

/-- An **exact redistribution** for coalition `S` allocates all of `S`'s endowment among members of
`S` without disposal (`∑ i ∈ S, x i g = ∑ i ∈ S, endowment i g`). -/
@[expose] def IsExactRedistribution (E : LinearExchangeEconomy A G) (S : Finset A)
    (x : A → G → ℝ) : Prop :=
  (∀ i ∈ S, ∀ g : G, 0 ≤ x i g) ∧ ∀ g : G, ∑ i ∈ S, x i g = ∑ i ∈ S, E.endowment i g

theorem IsExactRedistribution.isFeasibleRedistribution {E : LinearExchangeEconomy A G}
    {S : Finset A} {x : A → G → ℝ} (hx : E.IsExactRedistribution S x) :
    E.IsFeasibleRedistribution S x :=
  ⟨hx.1, fun g => (hx.2 g).le⟩

/-- Maximum total utility achievable by coalition `S`: for each good `g`, allocate `S`'s entire
supply `∑ i ∈ S, endowment i g` to a member of `S` with the highest marginal utility for `g`. -/
noncomputable def coalitionValue [Fintype G] (E : LinearExchangeEconomy A G)
    (S : Finset A) : ℝ :=
  if hS : S.Nonempty then
    ∑ g : G, (S.sup' hS (fun i => E.utility i g)) * ∑ i ∈ S, E.endowment i g
  else 0

@[simp]
theorem coalitionValue_empty [Fintype G] (E : LinearExchangeEconomy A G) :
    E.coalitionValue ∅ = 0 := by
  simp [coalitionValue]

theorem coalitionValue_of_nonempty [Fintype G] (E : LinearExchangeEconomy A G)
    {S : Finset A} (hS : S.Nonempty) :
    E.coalitionValue S =
      ∑ g : G, (S.sup' hS (fun i => E.utility i g)) * ∑ i ∈ S, E.endowment i g := by
  simp only [coalitionValue, hS, ↓reduceDIte]

private theorem sum_le_coalitionValue_of_feasible [Fintype G]
    (E : LinearExchangeEconomy A G) {S : Finset A} {x : A → G → ℝ}
    (hx : E.IsFeasibleRedistribution S x) :
    ∑ i ∈ S, ∑ g : G, E.utility i g * x i g ≤ E.coalitionValue S := by
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [coalitionValue]
  · rw [Finset.sum_comm, E.coalitionValue_of_nonempty hS]
    refine Finset.sum_le_sum fun g _ => ?_
    obtain ⟨i₀, hi₀⟩ := id hS
    calc ∑ i ∈ S, E.utility i g * x i g ≤ ∑ i ∈ S, S.sup' hS (E.utility · g) * x i g :=
        Finset.sum_le_sum fun i hi =>
          mul_le_mul_of_nonneg_right (Finset.le_sup' (E.utility · g) hi) (hx.1 i hi g)
      _ ≤ _ := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (hx.2 g)
          ((E.utility_nonneg i₀ g).trans (Finset.le_sup' (fun k => E.utility k g) hi₀))

/-- Optimal redistribution of `S`'s endowments attained by `coalitionValue` (`IsGreatest` over
`IsExactRedistribution`). -/
theorem isGreatest_exactRedistribution [Fintype G]
    (E : LinearExchangeEconomy A G) (S : Finset A) :
    IsGreatest ((fun x : A → G → ℝ => ∑ i ∈ S, ∑ g : G, E.utility i g * x i g) ''
      {x | E.IsExactRedistribution S x}) (E.coalitionValue S) := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp [IsGreatest, IsExactRedistribution, upperBounds]
  · choose winner hwinner_mem hwinner_eq using
      fun g : G => Finset.exists_mem_eq_sup' hS (E.utility · g)
    let xStar : A → G → ℝ := fun i g =>
      if i = winner g then ∑ j ∈ S, E.endowment j g else 0
    have hxStar : E.IsExactRedistribution S xStar := ⟨fun _ _ g => by
      dsimp only [xStar]
      split_ifs
      exacts [Finset.sum_nonneg fun j _ => E.endowment_nonneg j g, le_rfl],
      fun g => by simp [xStar, hwinner_mem g]⟩
    refine ⟨⟨xStar, hxStar, ?_⟩, fun _ ⟨_, hx, h⟩ =>
      h ▸ E.sum_le_coalitionValue_of_feasible hx.isFeasibleRedistribution⟩
    dsimp only
    rw [Finset.sum_comm, E.coalitionValue_of_nonempty hS]
    exact Finset.sum_congr rfl fun g _ => by simp [xStar, mul_ite, hwinner_mem g, hwinner_eq g]

theorem isGreatest_feasibleRedistribution [Fintype G]
    (E : LinearExchangeEconomy A G) (S : Finset A) :
    IsGreatest ((fun x : A → G → ℝ => ∑ i ∈ S, ∑ g : G, E.utility i g * x i g) ''
      {x | E.IsFeasibleRedistribution S x}) (E.coalitionValue S) := by
  obtain ⟨⟨xStar, hxStar, hval⟩, _⟩ := E.isGreatest_exactRedistribution S
  exact ⟨⟨xStar, hxStar.isFeasibleRedistribution, hval⟩,
    fun _ ⟨_, hx, h⟩ => h ▸ E.sum_le_coalitionValue_of_feasible hx⟩

/-- The TU **cooperative value game** associated to a linear Arrow–Debreu exchange economy `E`
([JainMahdian2007], Exercise 15.1). -/
noncomputable def toCooperativeGame [Fintype G] (E : LinearExchangeEconomy A G) :
    CooperativeGame A where
  val := E.coalitionValue
  val_empty := E.coalitionValue_empty

@[simp]
theorem toCooperativeGame_val [Fintype G] (E : LinearExchangeEconomy A G) (S : Finset A) :
    E.toCooperativeGame.val S = E.coalitionValue S := by
  rfl

/-- Competitive / grand-coalition price payoff allocation: price each good `g` at its maximum
marginal utility `max_{k ∈ univ} utility k g` and credit each agent `i` the value of `i`'s initial
endowment at these prices. -/
noncomputable def marketPriceAllocation [Fintype A] [Fintype G]
    (E : LinearExchangeEconomy A G) (i : A) : ℝ :=
  if hA : (Finset.univ : Finset A).Nonempty then
    ∑ g : G, (Finset.univ.sup' hA (fun k => E.utility k g)) * E.endowment i g
  else 0

theorem marketPriceAllocation_of_nonempty [Fintype A] [Fintype G]
    (E : LinearExchangeEconomy A G) (hA : (Finset.univ : Finset A).Nonempty) (i : A) :
    E.marketPriceAllocation i =
      ∑ g : G, (Finset.univ.sup' hA (fun k => E.utility k g)) * E.endowment i g := by
  simp only [marketPriceAllocation, hA, ↓reduceDIte]

/-- **Exercise 15.1** ([JainMahdian2007], p. 410): `marketPriceAllocation` lies in the core of
`E.toCooperativeGame`. -/
theorem marketPriceAllocation_inCore [Fintype A] [Fintype G] (E : LinearExchangeEconomy A G) :
    E.toCooperativeGame.InCore E.marketPriceAllocation := by
  refine ⟨?_, fun S => ?_⟩
  · by_cases hA : (Finset.univ : Finset A).Nonempty
    · simp only [marketPriceAllocation, toCooperativeGame, coalitionValue, hA, ↓reduceDIte]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun g _ => (Finset.mul_sum _ _ _).symm
    · simp [marketPriceAllocation, toCooperativeGame, coalitionValue, hA]
  · by_cases hS : S.Nonempty
    · have hA : (Finset.univ : Finset A).Nonempty := hS.mono (Finset.subset_univ S)
      simp only [marketPriceAllocation, toCooperativeGame, coalitionValue, hS, hA, ↓reduceDIte]
      rw [Finset.sum_comm]
      exact Finset.sum_le_sum fun g _ => by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_right
          (Finset.sup'_le hS _ fun i _ => Finset.le_sup' (E.utility · g) (Finset.mem_univ i))
          (Finset.sum_nonneg fun i _ => E.endowment_nonneg i g)
    · simp [Finset.not_nonempty_iff_eq_empty.1 hS]

/-- **Exercise 15.1** ([JainMahdian2007], p. 410): every linear Arrow–Debreu exchange economy TU
game has a **nonempty core** (answering Exercise 15.1 in the affirmative), and hence satisfies the
Bondareva–Shapley balancedness inequality for all balanced weight collections. -/
theorem toCooperativeGame_nonemptyCore [Fintype A] [Fintype G] (E : LinearExchangeEconomy A G) :
    E.toCooperativeGame.NonemptyCore :=
  ⟨E.marketPriceAllocation, E.marketPriceAllocation_inCore⟩

end LinearExchangeEconomy

end Cslib.GameTheory
