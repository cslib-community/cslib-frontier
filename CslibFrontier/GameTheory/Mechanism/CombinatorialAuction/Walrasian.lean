/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.BooleanAlgebra
public import Mathlib.Data.Fintype.Powerset
import CslibFrontier.Foundations.LinearAlgebra.Matrix.LinearProgramming
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Combinatorial auctions: Walrasian equilibrium and the LP relaxation

In a combinatorial auction, a finite set `M` of indivisible items is allocated among a finite set
`N` of bidders, each with a valuation `v i : Finset M → ℝ` on bundles `S : Finset M`
([BlumrosenNisan2007], §11.1.1, pp. 267–268). This module formalizes §11.3 of
[BlumrosenNisan2007] (pp. 275–279): the linear programming relaxation (LPR) and its dual (DLPR),
demand bundles, Walrasian equilibria, the First and Second Welfare Theorems (Theorems 11.13 and
11.15), Example 11.14, and the equivalence with integral LPR optima (Corollary 11.16).

## Normalization and monotonicity assumptions

Definition 11.1 of [BlumrosenNisan2007] (p. 268) requires valuations to be normalized (`v i ∅ = 0`)
and monotone (`S ⊆ T → v i S ≤ v i T`, "free disposal"). Monotonicity is not used in any theorem
of §11.3, so we work directly with arbitrary real-valued profiles `v : N → Finset M → ℝ` and state
the exact empty-bundle condition where needed:

* The integral part of the First Welfare Theorem (`IsWalrasianEquilibrium.welfare_le`) and the
  allocation form of the Second Welfare Theorem (`exists_isWalrasianEquilibrium_of_lprObjective_le`)
  hold for arbitrary real valuations `v : N → Finset M → ℝ`.
* The fractional part of the First Welfare Theorem (`IsWalrasianEquilibrium.lprObjective_le`), the
  0–1 vector form of the Second Welfare Theorem (`exists_isWalrasianEquilibrium_of_isIntegral`),
  and Corollary 11.16 (`exists_isWalrasianEquilibrium_iff`) assume `∀ i, 0 ≤ v i ∅` (strictly
  weaker than normalization `v i ∅ = 0`). The inequality is tight: in inequality (11.10) of
  [BlumrosenNisan2007] (p. 278), scaling `∑ S, x i S ≤ 1` by the utility
  `u i = v i (a.bundle i) - ∑ j ∈ a.bundle i, p j` requires `0 ≤ u i`, which follows from demand
  optimality against `S = ∅` when `0 ≤ v i ∅`. Counterexamples showing each of these statements
  fails when `v i ∅ < 0` live in `CslibFrontierTests.GameTheory.CombinatorialAuction`.

No computational or query-complexity claims are made here (solving LPR via demand oracles is §11.5
of [BlumrosenNisan2007]).

## Main definitions

* `Allocation`: a pairwise-disjoint assignment of bundles `bundle : N → Finset M`
  ([BlumrosenNisan2007], Definition 11.2, p. 268).
* `welfare`: the social welfare `∑ i, v i (a.bundle i)` of an allocation `a`
  (Definition 11.2, p. 268).
* `Allocation.indicator`: the 0–1 vector `x i S = 1` iff `S = a.bundle i`.
* `lprObjective`, `IsLPRFeasible`, `IsIntegral`, `IsLPROptimal`: the linear programming relaxation
  LPR (displays (11.3)–(11.6), p. 276) and its integer program restriction `x i S ∈ {0, 1}`.
* `IsLPRFeasible.toAllocation`: assigns each bidder the unique bundle with weight `1` (or `∅`
  if none), turning a feasible 0–1 vector `x` into an `Allocation`.
* `dlprObjective`, `IsDLPRFeasible`: the dual linear program DLPR (displays (11.7)–(11.9), p. 276).
* `IsDemand`: bundle `T` maximizes `v S - ∑ j ∈ S, p j` at item prices `p`
  (Definition 11.11, p. 277).
* `IsWalrasianEquilibrium`: nonnegative prices `p` and an allocation `a` in which every bidder
  receives a demand bundle and unallocated items have price `0` (Definition 11.12, p. 277).
* `noEquilibriumVal`: the two-bidder, two-item valuation profile of Example 11.14 (p. 278).

## Main results

* `lprObjective_le_dlprObjective`, `exists_lpr_dlpr_eq`: weak and strong LP duality between LPR
  and DLPR, deduced from `Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg`.
* `IsWalrasianEquilibrium.welfare_le`, `IsWalrasianEquilibrium.lprObjective_le`: **First Welfare
  Theorem** ([BlumrosenNisan2007], Theorem 11.13, pp. 277–278).
* `not_exists_isWalrasianEquilibrium_noEquilibriumVal`: **Example 11.14** (p. 278) has no
  Walrasian equilibrium, with best allocation welfare `3` and exact LPR optimum `7 / 2`
  (`welfare_noEquilibriumVal_le`, `exists_isLPROptimal_noEquilibriumVal`).
* `exists_isWalrasianEquilibrium_of_lprObjective_le`,
  `exists_isWalrasianEquilibrium_of_isIntegral`: **Second Welfare Theorem**
  ([BlumrosenNisan2007], Theorem 11.15, pp. 278–279).
* `exists_isWalrasianEquilibrium_iff`: **Corollary 11.16** ([BlumrosenNisan2007], p. 279):
  a Walrasian equilibrium exists iff LPR admits an integral optimal solution (with
  `exists_isIntegral_isLPROptimal_iff` equating 0–1 vectors and allocations under `0 ≤ v i ∅`).

## References

* [L. Blumrosen and N. Nisan, *Combinatorial Auctions*][BlumrosenNisan2007], Chapter 11,
  §§11.1 and 11.3, pp. 267–268 and 275–279.
-/

public section

namespace Cslib.GameTheory.CombinatorialAuction

open Finset

/-! ### Allocations and social welfare -/

/-- An *allocation* of a set of indivisible items `M` among bidders `N`: each bidder `i` receives
a bundle `bundle i : Finset M`, and distinct bidders receive disjoint bundles
([BlumrosenNisan2007], Definition 11.2, p. 268). Unallocated items belong to no `bundle i`. -/
@[ext]
structure Allocation (N M : Type*) where
  /-- The bundle of items assigned to each bidder. -/
  bundle : N → Finset M
  /-- Distinct bidders receive disjoint bundles (`Sᵢ ∩ Sⱼ = ∅` for `i ≠ j`). -/
  disjoint : Pairwise (Function.onFun Disjoint bundle)

/-- The *social welfare* `∑ i, v i (a.bundle i)` obtained by allocation `a` under valuation
profile `v` ([BlumrosenNisan2007], Definition 11.2, p. 268). -/
@[expose] def welfare {N M : Type*} [Fintype N] (v : N → Finset M → ℝ)
    (a : Allocation N M) : ℝ :=
  ∑ i, v i (a.bundle i)

/-- The 0–1 indicator fractional allocation of `a : Allocation N M`: entry `(i, S)` is `1` when
`S = a.bundle i` and `0` otherwise ([BlumrosenNisan2007], §11.3.1, p. 276). -/
@[expose] def Allocation.indicator {N M : Type*} [DecidableEq M] (a : Allocation N M)
    (i : N) (S : Finset M) : ℝ :=
  if S = a.bundle i then 1 else 0

/-! ### Linear programming relaxation (LPR) and its dual (DLPR) -/

/-- The objective function `∑ i, ∑ S, x i S * v i S` of the linear programming relaxation LPR
([BlumrosenNisan2007], §11.3.1, display (11.3), p. 276). -/
@[expose] def lprObjective {N M : Type*} [Fintype N] [Fintype M]
    (v : N → Finset M → ℝ) (x : N → Finset M → ℝ) : ℝ :=
  ∑ i, ∑ S : Finset M, x i S * v i S

/-- Feasibility of a fractional allocation `x : N → Finset M → ℝ` in the linear programming
relaxation LPR ([BlumrosenNisan2007], §11.3.1, displays (11.4)–(11.6), p. 276). -/
structure IsLPRFeasible {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    (x : N → Finset M → ℝ) : Prop where
  /-- Constraint (11.4): each item `j` is fractionally allocated at most once. -/
  item_le (j : M) : ∑ i : N, ∑ S : Finset M with j ∈ S, x i S ≤ 1
  /-- Constraint (11.5): each bidder `i` receives total bundle weight at most `1`. -/
  bidder_le (i : N) : ∑ S : Finset M, x i S ≤ 1
  /-- Constraint (11.6): every bundle weight is nonnegative. -/
  nonneg (i : N) (S : Finset M) : 0 ≤ x i S

/-- A fractional allocation `x` is *integral* (0–1) if every variable `x i S` lies in `{0, 1}`
([BlumrosenNisan2007], §11.3.1, p. 276). Under `IsLPRFeasible`, constraint (11.5) together with
`nonneg` implies that `0 ≤ x i S ≤ 1`, so `x i S ∈ ℤ` is equivalent to `x i S ∈ {0, 1}`. -/
@[expose] def IsIntegral {N M : Type*} (x : N → Finset M → ℝ) : Prop :=
  ∀ i S, x i S = 0 ∨ x i S = 1

/-- Optimality of `x` in the linear programming relaxation LPR for valuation profile `v`:
`x` is LPR-feasible and attains at least as large an objective as every LPR-feasible `y`
([BlumrosenNisan2007], §11.3.1, p. 276). -/
@[expose] def IsLPROptimal {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    (v : N → Finset M → ℝ) (x : N → Finset M → ℝ) : Prop :=
  IsLPRFeasible x ∧ ∀ y, IsLPRFeasible y → lprObjective v y ≤ lprObjective v x

/-- The zero fractional allocation is LPR-feasible. -/
theorem isLPRFeasible_zero {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M] :
    IsLPRFeasible (fun (_ : N) (_ : Finset M) => (0 : ℝ)) where
  item_le j := by simp
  bidder_le i := by simp
  nonneg _ _ := le_rfl

/-- The indicator of an allocation is a 0–1 vector. -/
theorem Allocation.indicator_isIntegral {N M : Type*} [DecidableEq M] (a : Allocation N M) :
    IsIntegral a.indicator := fun i S => by
  unfold Allocation.indicator
  split_ifs <;> simp

/-- The indicator of an allocation is LPR-feasible. -/
theorem Allocation.indicator_isLPRFeasible {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    (a : Allocation N M) : IsLPRFeasible a.indicator where
  item_le j := by
    classical
    have hsum : ∀ i : N, (∑ S : Finset M with j ∈ S, a.indicator i S) =
        if j ∈ a.bundle i then (1 : ℝ) else 0 := by
      intro i
      unfold Allocation.indicator
      rw [Finset.sum_ite_eq']
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    simp_rw [hsum]
    by_cases h : ∃ i : N, j ∈ a.bundle i
    · obtain ⟨i₀, hi₀⟩ := h
      rw [Fintype.sum_eq_single i₀ fun i hne =>
        ite_eq_right fun hi => Finset.disjoint_left.mp (a.disjoint hne) hi hi₀]
      simp [hi₀]
    · push Not at h
      simp [h]
  bidder_le i := by
    simp [Allocation.indicator]
  nonneg i S := by
    unfold Allocation.indicator
    split_ifs <;> norm_num

/-- The LPR objective evaluated at the indicator of an allocation equals its social welfare. -/
@[simp]
theorem Allocation.lprObjective_indicator {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    (v : N → Finset M → ℝ) (a : Allocation N M) :
    lprObjective v a.indicator = welfare v a := by
  simp [lprObjective, welfare, Allocation.indicator]

section IntegralToAllocation

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]

private theorem IsLPRFeasible.unique_bundle_eq_one {x : N → Finset M → ℝ}
    (hx : IsLPRFeasible x) {i : N} {S₁ S₂ : Finset M}
    (h₁ : x i S₁ = 1) (h₂ : x i S₂ = 1) : S₁ = S₂ := by
  by_contra hne
  have hle : x i S₁ + x i S₂ ≤ ∑ S : Finset M, x i S := by
    simpa [Finset.sum_pair hne] using
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({S₁, S₂} : Finset (Finset M)))
        (fun S _ _ => hx.nonneg i S)
  linarith [hx.bidder_le i]

private theorem IsLPRFeasible.disjoint_of_eq_one {x : N → Finset M → ℝ}
    (hx : IsLPRFeasible x) {i₁ i₂ : N} (hne : i₁ ≠ i₂) {S₁ S₂ : Finset M}
    (h₁ : x i₁ S₁ = 1) (h₂ : x i₂ S₂ = 1) : Disjoint S₁ S₂ := by
  rw [Finset.disjoint_left]
  intro j hj₁ hj₂
  have hterm : ∀ i S, j ∈ S → x i S ≤ ∑ T : Finset M with j ∈ T, x i T := fun i S hS =>
    Finset.single_le_sum (fun T _ => hx.nonneg i T)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ S, hS⟩)
  have hnonneg : ∀ i : N, 0 ≤ ∑ T : Finset M with j ∈ T, x i T := fun i =>
    Finset.sum_nonneg fun T _ => hx.nonneg i T
  have hle : (∑ T : Finset M with j ∈ T, x i₁ T) + (∑ T : Finset M with j ∈ T, x i₂ T) ≤
      ∑ i : N, ∑ T : Finset M with j ∈ T, x i T := by
    classical
    simpa [Finset.sum_pair hne] using
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({i₁, i₂} : Finset N))
        (fun i _ _ => hnonneg i)
  linarith [hterm i₁ S₁ hj₁, hterm i₂ S₂ hj₂, hx.item_le j]

open Classical in
/-- The `Allocation` induced by an LPR-feasible vector `x`: bidder `i` receives the unique bundle
`S` with `x i S = 1`, or `∅` if no bundle has weight `1` ([BlumrosenNisan2007], §11.3.1, p. 276).
For a 0–1 vector `x`, constraint (11.5) guarantees at most one bundle with weight `1` per bidder,
and constraint (11.4) guarantees those bundles are pairwise disjoint. -/
noncomputable def IsLPRFeasible.toAllocation {x : N → Finset M → ℝ}
    (hx : IsLPRFeasible x) : Allocation N M where
  bundle i := if h : ∃ S : Finset M, x i S = 1 then h.choose else ∅
  disjoint i₁ i₂ hne := by
    dsimp only [Function.onFun]
    split_ifs with h₁ h₂
    · exact hx.disjoint_of_eq_one hne h₁.choose_spec h₂.choose_spec
    · exact Finset.disjoint_empty_right _
    · exact Finset.disjoint_empty_left _
    · exact Finset.disjoint_empty_left _

/-- If an LPR-feasible vector `x` gives `x i S = 1`, then `toAllocation` assigns `S` to `i`. -/
theorem IsLPRFeasible.toAllocation_bundle_eq_of_eq_one {x : N → Finset M → ℝ}
    (hx : IsLPRFeasible x) {i : N} {S : Finset M} (h : x i S = 1) :
    hx.toAllocation.bundle i = S := by
  classical
  change (if h' : ∃ T : Finset M, x i T = 1 then h'.choose else ∅) = S
  split_ifs with h'
  · exact hx.unique_bundle_eq_one h'.choose_spec h
  · exact absurd ⟨S, h⟩ h'

/-- If an LPR-feasible vector `x` gives weight `0` to every bundle for bidder `i`, then
`toAllocation` assigns `∅` to `i`. -/
theorem IsLPRFeasible.toAllocation_bundle_eq_empty {x : N → Finset M → ℝ}
    (hx : IsLPRFeasible x) {i : N} (h : ∀ S : Finset M, x i S = 0) :
    hx.toAllocation.bundle i = ∅ := by
  classical
  change (if h' : ∃ T : Finset M, x i T = 1 then h'.choose else ∅) = ∅
  split_ifs with h'
  · exact absurd h'.choose_spec (by linarith [h h'.choose])
  · rfl

/-- Under `∀ i, 0 ≤ v i ∅`, rounding a feasible 0–1 vector `x` to an `Allocation` (setting
unassigned bidders to `∅`) does not decrease its social welfare. -/
theorem IsLPRFeasible.lprObjective_le_welfare_toAllocation {v : N → Finset M → ℝ}
    (hv : ∀ i, 0 ≤ v i ∅) {x : N → Finset M → ℝ} (hx : IsLPRFeasible x)
    (hint : IsIntegral x) :
    lprObjective v x ≤ welfare v hx.toAllocation := by
  unfold lprObjective welfare
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hex : ∃ S : Finset M, x i S = 1
  · obtain ⟨S₀, hS₀⟩ := hex
    rw [hx.toAllocation_bundle_eq_of_eq_one hS₀, Fintype.sum_eq_single S₀ fun S hne => by
      rw [(hint i S).resolve_right fun h1 => hne (hx.unique_bundle_eq_one h1 hS₀), zero_mul],
      hS₀, one_mul]
  · push Not at hex
    have hzero : ∀ S : Finset M, x i S = 0 := fun S =>
      (hint i S).resolve_right (hex S)
    rw [hx.toAllocation_bundle_eq_empty hzero]
    simp [hzero, hv i]

end IntegralToAllocation

/-- The objective function `∑ i, u i + ∑ j, p j` of the dual linear program DLPR
([BlumrosenNisan2007], §11.3.1, display (11.7), p. 276). -/
@[expose] def dlprObjective {N M : Type*} [Fintype N] [Fintype M]
    (u : N → ℝ) (p : M → ℝ) : ℝ :=
  ∑ i, u i + ∑ j, p j

/-- Feasibility of bidder utilities `u : N → ℝ` and item prices `p : M → ℝ` in the dual linear
programming relaxation DLPR ([BlumrosenNisan2007], §11.3.1, displays (11.8)–(11.9), p. 276). -/
structure IsDLPRFeasible {N M : Type*} (v : N → Finset M → ℝ) (u : N → ℝ) (p : M → ℝ) :
    Prop where
  /-- Constraint (11.8): `uᵢ + ∑_{j ∈ S} pⱼ ≥ vᵢ(S)` for every bidder `i` and bundle `S`. -/
  cover (i : N) (S : Finset M) : v i S ≤ u i + ∑ j ∈ S, p j
  /-- Constraint (11.9): utilities are nonnegative. -/
  utility_nonneg (i : N) : 0 ≤ u i
  /-- Constraint (11.9): item prices are nonnegative. -/
  price_nonneg (j : M) : 0 ≤ p j

/-! ### Weak and strong LP duality for LPR / DLPR -/

section Duality

open Matrix

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]

private def lprMatrix [DecidableEq N] : Matrix (M ⊕ N) (N × Finset M) ℝ :=
  Matrix.of fun row col =>
    match row with
    | .inl j => if j ∈ col.2 then 1 else 0
    | .inr k => if k = col.1 then 1 else 0

private theorem lprMatrix_mulVec_inl [DecidableEq N] (x : N → Finset M → ℝ) (j : M) :
    (lprMatrix *ᵥ Function.uncurry x) (.inl j) =
      ∑ i : N, ∑ S : Finset M with j ∈ S, x i S := by
  simp only [Matrix.mulVec, dotProduct, lprMatrix, Matrix.of_apply, Fintype.sum_prod_type,
    Function.uncurry_apply_pair, ite_mul, one_mul, zero_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_filter]

private theorem lprMatrix_mulVec_inr [DecidableEq N] (x : N → Finset M → ℝ) (k : N) :
    (lprMatrix *ᵥ Function.uncurry x) (.inr k) = ∑ S : Finset M, x k S := by
  simp only [Matrix.mulVec, dotProduct, lprMatrix, Matrix.of_apply, Fintype.sum_prod_type,
    Function.uncurry_apply_pair, ite_mul, one_mul, zero_mul]
  rw [Fintype.sum_eq_single k fun i hne => Finset.sum_eq_zero fun S _ => by simp [hne.symm]]
  simp

private theorem vecMul_lprMatrix [DecidableEq N] (p : M → ℝ) (u : N → ℝ) (i : N)
    (S : Finset M) :
    (Sum.elim p u ᵥ* lprMatrix) (i, S) = u i + ∑ j ∈ S, p j := by
  simp only [Matrix.vecMul, dotProduct, lprMatrix, Matrix.of_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter, add_comm]
  simp

omit [DecidableEq M] in
private theorem dotProduct_lprCost (v : N → Finset M → ℝ) (x : N → Finset M → ℝ) :
    Function.uncurry v ⬝ᵥ Function.uncurry x = lprObjective v x := by
  simp only [dotProduct, Fintype.sum_prod_type, Function.uncurry_apply_pair, lprObjective]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun S _ => mul_comm _ _

omit [DecidableEq M] in
private theorem dotProduct_dlprRhs (p : M → ℝ) (u : N → ℝ) :
    Sum.elim p u ⬝ᵥ (1 : M ⊕ N → ℝ) = dlprObjective u p := by
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.one_apply, mul_one,
    dlprObjective, add_comm]

private theorem isLPRFeasible_iff_matrix [DecidableEq N] (x : N → Finset M → ℝ) :
    IsLPRFeasible x ↔
      0 ≤ Function.uncurry x ∧ lprMatrix *ᵥ Function.uncurry x ≤ (1 : M ⊕ N → ℝ) := by
  constructor
  · intro hx
    refine ⟨fun ⟨i, S⟩ => hx.nonneg i S, ?_⟩
    rintro (j | k)
    exacts [(lprMatrix_mulVec_inl x j).trans_le (hx.item_le j),
      (lprMatrix_mulVec_inr x k).trans_le (hx.bidder_le k)]
  · rintro ⟨hnonneg, hmul⟩
    exact
      { item_le := fun j => by
          simpa [lprMatrix_mulVec_inl] using hmul (.inl j)
        bidder_le := fun k => by
          simpa [lprMatrix_mulVec_inr] using hmul (.inr k)
        nonneg := fun i S => hnonneg (i, S) }

private theorem isDLPRFeasible_iff_matrix [DecidableEq N]
    (v : N → Finset M → ℝ) (u : N → ℝ) (p : M → ℝ) :
    IsDLPRFeasible v u p ↔
      0 ≤ Sum.elim p u ∧ Function.uncurry v ≤ Sum.elim p u ᵥ* lprMatrix := by
  constructor
  · intro h
    refine ⟨by rintro (j | i); exacts [h.price_nonneg j, h.utility_nonneg i], fun ⟨i, S⟩ => ?_⟩
    rw [vecMul_lprMatrix]
    exact h.cover i S
  · rintro ⟨hnonneg, hle⟩
    exact
      { cover := fun i S => by
          simpa [vecMul_lprMatrix] using hle (i, S)
        utility_nonneg := fun i => hnonneg (.inr i)
        price_nonneg := fun j => hnonneg (.inl j) }

/-- **Weak LP duality** between LPR and DLPR ([BlumrosenNisan2007], §11.3.1, pp. 276–277): the
objective of any LPR-feasible fractional allocation is at most the objective of any DLPR-feasible
utility-price pair. -/
theorem lprObjective_le_dlprObjective {v : N → Finset M → ℝ} {x : N → Finset M → ℝ}
    {u : N → ℝ} {p : M → ℝ} (hx : IsLPRFeasible x) (hup : IsDLPRFeasible v u p) :
    lprObjective v x ≤ dlprObjective u p := by
  classical
  have ⟨hx0, hxA⟩ := (isLPRFeasible_iff_matrix x).mp hx
  have ⟨hy0, hyA⟩ := (isDLPRFeasible_iff_matrix v u p).mp hup
  simpa only [dotProduct_lprCost, dotProduct_dlprRhs] using
    Matrix.dotProduct_le_dotProduct_of_nonneg_of_mulVec_le hx0 hxA hy0 hyA

/-- **Strong LP duality** between LPR and DLPR ([BlumrosenNisan2007], §11.3.1, pp. 276–277):
both programs are always feasible, so there exist feasible primal `x` and dual `(u, p)` attaining
equal objective values. Derived directly from
`Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg` with no unproved assumptions on `v`. -/
theorem exists_lpr_dlpr_eq (v : N → Finset M → ℝ) :
    ∃ (x : N → Finset M → ℝ) (u : N → ℝ) (p : M → ℝ),
      IsLPRFeasible x ∧ IsDLPRFeasible v u p ∧ lprObjective v x = dlprObjective u p := by
  classical
  have hP : ∃ x' : N × Finset M → ℝ, 0 ≤ x' ∧ lprMatrix *ᵥ x' ≤ (1 : M ⊕ N → ℝ) :=
    ⟨Function.uncurry (fun _ _ => 0), (isLPRFeasible_iff_matrix _).mp isLPRFeasible_zero⟩
  let u₀ : N → ℝ := fun i => ∑ S : Finset M, max (v i S) 0
  have hD0 : IsDLPRFeasible v u₀ (fun _ => 0) :=
    { cover := fun i S => by
        simp only [Finset.sum_const_zero, add_zero, u₀]
        exact (le_max_left (v i S) 0).trans
          (Finset.single_le_sum (fun T _ => le_max_right (v i T) 0) (Finset.mem_univ S))
      utility_nonneg := fun i => Finset.sum_nonneg fun S _ => le_max_right _ _
      price_nonneg := fun _ => le_rfl }
  have hD : ∃ y' : M ⊕ N → ℝ, 0 ≤ y' ∧ Function.uncurry v ≤ y' ᵥ* lprMatrix :=
    ⟨Sum.elim (fun _ => 0) u₀, (isDLPRFeasible_iff_matrix v u₀ (fun _ => 0)).mp hD0⟩
  obtain ⟨val, ⟨⟨x', hx', hxv⟩, -⟩, ⟨⟨y', hy', hyv⟩, -⟩⟩ :=
    Matrix.exists_isGreatest_isLeast_dotProduct_of_nonneg
      lprMatrix 1 (Function.uncurry v) hP hD
  refine ⟨Function.curry x', y' ∘ Sum.inr, y' ∘ Sum.inl, ?_, ?_, ?_⟩
  · exact (isLPRFeasible_iff_matrix (Function.curry x')).mpr
      (by simpa [Function.uncurry_curry] using hx')
  · refine (isDLPRFeasible_iff_matrix v (y' ∘ Sum.inr) (y' ∘ Sum.inl)).mpr ?_
    simpa [Sum.elim_comp_inl_inr] using hy'
  · rw [← dotProduct_lprCost, ← dotProduct_dlprRhs, Function.uncurry_curry,
      Sum.elim_comp_inl_inr]
    exact hxv.trans hyv.symm

end Duality

/-! ### Demand and Walrasian equilibrium -/

/-- A bundle `T` is a *demand* for valuation `v` at item prices `p : M → ℝ` if it maximizes
quasilinear utility `v S - ∑ j ∈ S, p j` over all bundles `S : Finset M`
([BlumrosenNisan2007], Definition 11.11, p. 277). -/
@[expose] def IsDemand {M : Type*} (v : Finset M → ℝ) (p : M → ℝ) (T : Finset M) : Prop :=
  ∀ S : Finset M, v S - ∑ j ∈ S, p j ≤ v T - ∑ j ∈ T, p j

/-- Every valuation on a finite item set has at least one demand bundle at any item prices `p`. -/
theorem exists_isDemand {M : Type*} [Finite M] (v : Finset M → ℝ) (p : M → ℝ) :
    ∃ T : Finset M, IsDemand v p T := by
  have := Fintype.ofFinite M
  obtain ⟨T, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset M))
    (fun S => v S - ∑ j ∈ S, p j) ⟨∅, Finset.mem_univ ∅⟩
  exact ⟨T, fun S => hmax S (Finset.mem_univ S)⟩

/-- A *Walrasian equilibrium* consists of nonnegative item prices `p : M → ℝ` and an allocation
`a : Allocation N M` such that every bidder receives a demand bundle at prices `p`, and every
unallocated item has price `0` ([BlumrosenNisan2007], Definition 11.12, p. 277). -/
structure IsWalrasianEquilibrium {N M : Type*} (v : N → Finset M → ℝ) (p : M → ℝ)
    (a : Allocation N M) : Prop where
  /-- Item prices are nonnegative (`pⱼ* ≥ 0`). -/
  price_nonneg (j : M) : 0 ≤ p j
  /-- Each bidder `i` receives a demand bundle at prices `p`. -/
  demand (i : N) : IsDemand (v i) p (a.bundle i)
  /-- Every unallocated item (`j ∉ ⋃ i, a.bundle i`) has price `0`. -/
  unallocated_price_zero (j : M) : (∀ i : N, j ∉ a.bundle i) → p j = 0

private theorem sum_bundle_prices_le {N M : Type*} [Fintype N] [Fintype M]
    {p : M → ℝ} (hp : ∀ j, 0 ≤ p j) (a : Allocation N M) :
    ∑ i : N, ∑ j ∈ a.bundle i, p j ≤ ∑ j : M, p j := by
  classical
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset N) a.bundle :=
    fun i₁ _ i₂ _ hne => a.disjoint hne
  rw [← Finset.sum_biUnion hdisj]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hp j)

private theorem sum_bundle_prices_eq {N M : Type*} [Fintype N] [Fintype M]
    {p : M → ℝ} {a : Allocation N M}
    (hzero : ∀ j : M, (∀ i : N, j ∉ a.bundle i) → p j = 0) :
    ∑ i : N, ∑ j ∈ a.bundle i, p j = ∑ j : M, p j := by
  classical
  have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset N) a.bundle :=
    fun i₁ _ i₂ _ hne => a.disjoint hne
  rw [← Finset.sum_biUnion hdisj]
  refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
  exact hzero j fun i hi => hj (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hi⟩)

/-! ### The First Welfare Theorem (Theorem 11.13) -/

/-- **The First Welfare Theorem (integral form)** ([BlumrosenNisan2007], Theorem 11.13, p. 277):
every Walrasian equilibrium allocation maximizes social welfare among all integral allocations.
This part holds for arbitrary real valuations `v : N → Finset M → ℝ` without normalization or
monotonicity. -/
theorem IsWalrasianEquilibrium.welfare_le {N M : Type*} [Fintype N] [Finite M]
    {v : N → Finset M → ℝ} {p : M → ℝ} {a : Allocation N M}
    (heq : IsWalrasianEquilibrium v p a) (b : Allocation N M) :
    welfare v b ≤ welfare v a := by
  classical
  have := Fintype.ofFinite M
  have hdem : ∑ i : N, (v i (b.bundle i) - ∑ j ∈ b.bundle i, p j) ≤
      ∑ i : N, (v i (a.bundle i) - ∑ j ∈ a.bundle i, p j) :=
    Finset.sum_le_sum fun i _ => heq.demand i (b.bundle i)
  simp only [Finset.sum_sub_distrib] at hdem
  have hb := sum_bundle_prices_le heq.price_nonneg b
  have ha := sum_bundle_prices_eq heq.unallocated_price_zero
  unfold welfare
  linarith

/-- **The First Welfare Theorem (fractional form)** ([BlumrosenNisan2007], Theorem 11.13,
pp. 277–278): if `∀ i, 0 ≤ v i ∅` (in particular, for valuations normalized as in Definition 11.1),
then a Walrasian equilibrium allocation maximizes social welfare over all feasible fractional
solutions of LPR: `lprObjective v x ≤ welfare v a`.

The condition `∀ i, 0 ≤ v i ∅` cannot be dropped (when `v i ∅ < 0`, the zero fractional allocation
has objective `0` strictly above the welfare of allocating `∅` to every bidder). -/
theorem IsWalrasianEquilibrium.lprObjective_le {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq M] {v : N → Finset M → ℝ} {p : M → ℝ} {a : Allocation N M}
    (heq : IsWalrasianEquilibrium v p a) (hv : ∀ i, 0 ≤ v i ∅)
    {x : N → Finset M → ℝ} (hx : IsLPRFeasible x) :
    lprObjective v x ≤ welfare v a := by
  let u : N → ℝ := fun i => v i (a.bundle i) - ∑ j ∈ a.bundle i, p j
  have hdual : IsDLPRFeasible v u p :=
    { cover := fun i S => by dsimp only [u]; linarith [heq.demand i S]
      utility_nonneg := fun i => (hv i).trans (by simpa [u] using heq.demand i ∅)
      price_nonneg := heq.price_nonneg }
  have hobj : dlprObjective u p = welfare v a := by
    unfold dlprObjective welfare
    simp only [u, Finset.sum_sub_distrib]
    rw [sum_bundle_prices_eq heq.unallocated_price_zero]
    linarith
  exact (lprObjective_le_dlprObjective hx hdual).trans_eq hobj

/-! ### The Second Welfare Theorem (Theorem 11.15) and Corollary 11.16 -/

/-- **The Second Welfare Theorem (allocation form)** ([BlumrosenNisan2007], Theorem 11.15,
pp. 278–279): if an allocation `a` achieves at least the LPR objective of every feasible fractional
allocation, then there exist item prices `p` making `(p, a)` a Walrasian equilibrium. This form
holds for arbitrary real valuations `v : N → Finset M → ℝ` without normalization or monotonicity. -/
theorem exists_isWalrasianEquilibrium_of_lprObjective_le {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq M] {v : N → Finset M → ℝ} {a : Allocation N M}
    (hopt : ∀ x, IsLPRFeasible x → lprObjective v x ≤ welfare v a) :
    ∃ p : M → ℝ, IsWalrasianEquilibrium v p a := by
  obtain ⟨x₀, u, p, hx₀, hup, heq⟩ := exists_lpr_dlpr_eq v
  have hle : dlprObjective u p ≤ welfare v a := heq ▸ hopt x₀ hx₀
  unfold welfare dlprObjective at hle
  -- Complementary slackness via the chain `∑ vᵢ(S*ᵢ) ≤ ∑ (uᵢ + p(S*ᵢ)) ≤ ∑ uᵢ + ∑ pⱼ = ∑ vᵢ(S*ᵢ)`.
  have hcov := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hup.cover i (a.bundle i)
  have hpriceSum := sum_bundle_prices_le hup.price_nonneg a
  rw [Finset.sum_add_distrib] at hcov
  have hbind := (Finset.sum_eq_sum_iff_of_le fun i (_ : i ∈ Finset.univ) =>
    hup.cover i (a.bundle i)).1 (by rw [Finset.sum_add_distrib]; linarith)
  refine ⟨p, hup.price_nonneg, fun i S => ?_, fun j hj => ?_⟩
  · linarith [hup.cover i S, hbind i (Finset.mem_univ i)]
  · have hdisj : Set.PairwiseDisjoint (Finset.univ : Finset N) a.bundle :=
      fun i₁ _ i₂ _ hne => a.disjoint hne
    by_contra hne
    have := Finset.sum_lt_sum_of_subset (Finset.subset_univ (Finset.univ.biUnion a.bundle))
      (Finset.mem_univ j) (by simpa using hj) ((hup.price_nonneg j).lt_of_ne' hne)
      fun k _ _ => hup.price_nonneg k
    rw [Finset.sum_biUnion hdisj] at this
    linarith

/-- **The Second Welfare Theorem (0–1 LPR form)** ([BlumrosenNisan2007], Theorem 11.15,
pp. 278–279): if `x` is an integral (0–1) optimal solution of LPR and `∀ i, 0 ≤ v i ∅`, then the
induced allocation `hx.1.toAllocation` admits a supporting Walrasian equilibrium price vector
(and achieves the same objective value `lprObjective v x`). -/
theorem exists_isWalrasianEquilibrium_of_isIntegral {N M : Type*} [Fintype N] [Fintype M]
    [DecidableEq M] {v : N → Finset M → ℝ} (hv : ∀ i, 0 ≤ v i ∅) {x : N → Finset M → ℝ}
    (hx : IsLPROptimal v x) (hint : IsIntegral x) :
    ∃ p : M → ℝ, IsWalrasianEquilibrium v p hx.1.toAllocation ∧
      welfare v hx.1.toAllocation = lprObjective v x := by
  have hge : lprObjective v x ≤ welfare v hx.1.toAllocation :=
    hx.1.lprObjective_le_welfare_toAllocation hv hint
  have hle : welfare v hx.1.toAllocation ≤ lprObjective v x := by
    simpa only [Allocation.lprObjective_indicator] using
      hx.2 _ hx.1.toAllocation.indicator_isLPRFeasible
  have heq : welfare v hx.1.toAllocation = lprObjective v x := le_antisymm hle hge
  obtain ⟨p, hp⟩ := exists_isWalrasianEquilibrium_of_lprObjective_le fun y hy =>
    (hx.2 y hy).trans_eq heq.symm
  exact ⟨p, hp, heq⟩

/-- Under `∀ i, 0 ≤ v i ∅`, LPR admits a 0–1 optimal solution iff there is an `Allocation` whose
social welfare dominates every feasible fractional allocation. -/
theorem exists_isIntegral_isLPROptimal_iff {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    {v : N → Finset M → ℝ} (hv : ∀ i, 0 ≤ v i ∅) :
    (∃ x, IsLPROptimal v x ∧ IsIntegral x) ↔
      ∃ a : Allocation N M, ∀ x, IsLPRFeasible x → lprObjective v x ≤ welfare v a := by
  constructor
  · rintro ⟨x, hx, hint⟩
    refine ⟨hx.1.toAllocation, fun y hy => ?_⟩
    exact (hx.2 y hy).trans (hx.1.lprObjective_le_welfare_toAllocation hv hint)
  · rintro ⟨a, ha⟩
    refine ⟨a.indicator, ⟨a.indicator_isLPRFeasible, fun y hy => ?_⟩, a.indicator_isIntegral⟩
    simpa only [Allocation.lprObjective_indicator] using ha y hy

/-- **Corollary 11.16** ([BlumrosenNisan2007], §11.3.2, p. 279): assuming `∀ i, 0 ≤ v i ∅` (in
particular, for normalized valuations), a Walrasian equilibrium exists if and only if the linear
programming relaxation LPR admits an integral (0–1) optimal solution. -/
theorem exists_isWalrasianEquilibrium_iff {N M : Type*} [Fintype N] [Fintype M] [DecidableEq M]
    {v : N → Finset M → ℝ} (hv : ∀ i, 0 ≤ v i ∅) :
    (∃ (p : M → ℝ) (a : Allocation N M), IsWalrasianEquilibrium v p a) ↔
      ∃ x, IsLPROptimal v x ∧ IsIntegral x := by
  rw [exists_isIntegral_isLPROptimal_iff hv]
  exact ⟨fun ⟨_, a, heq⟩ => ⟨a, fun _ hx => heq.lprObjective_le hv hx⟩,
    fun ⟨a, ha⟩ => let ⟨p, hp⟩ := exists_isWalrasianEquilibrium_of_lprObjective_le ha; ⟨p, a, hp⟩⟩

/-! ### Example 11.14: no Walrasian equilibrium -/

/-- The two-bidder, two-item valuation profile of [BlumrosenNisan2007], Example 11.14 (p. 278).
Bidders are `false` (Alice) and `true` (Bob), and items are `{false, true}`. Alice values every
nonempty bundle at `2` (`0` for `∅`); Bob values the full bundle `{false, true}` at `3` (`0` for
every proper subset). -/
@[expose] def noEquilibriumVal (i : Bool) (S : Finset Bool) : ℝ :=
  if i then (if S = Finset.univ then 3 else 0) else (if S.Nonempty then 2 else 0)

/-- The valuations of Example 11.14 are normalized (`vᵢ(∅) = 0`). -/
theorem noEquilibriumVal_empty (i : Bool) : noEquilibriumVal i ∅ = 0 := by
  cases i
  · simp [noEquilibriumVal]
  · simp only [noEquilibriumVal, ↓reduceIte]
    exact ite_eq_right (by decide)

/-- The valuations of Example 11.14 are monotone ("free disposal"). -/
theorem noEquilibriumVal_monotone (i : Bool) : Monotone (noEquilibriumVal i) := by
  intro S T hST
  cases i
  · simp only [noEquilibriumVal, Bool.false_eq_true, ↓reduceIte]
    split_ifs with hS hT <;> norm_num
    exact absurd (hS.mono hST) hT
  · simp only [noEquilibriumVal, ↓reduceIte]
    split_ifs with hS hT <;> norm_num
    exact absurd (Finset.eq_univ_of_forall fun x => hST (hS ▸ Finset.mem_univ x)) hT

/-- Every allocation in Example 11.14 has social welfare at most `3`
([BlumrosenNisan2007], Example 11.14, p. 278; attained by allocating `{false, true}` to Bob). -/
theorem welfare_noEquilibriumVal_le (a : Allocation Bool Bool) :
    welfare noEquilibriumVal a ≤ 3 := by
  unfold welfare
  rw [Fintype.sum_bool]
  by_cases h : a.bundle true = Finset.univ
  · have hA : a.bundle false = ∅ := by
      simpa only [Function.onFun, h, Finset.disjoint_iff_inter_eq_empty, Finset.inter_univ] using
        a.disjoint (by decide : false ≠ true)
    simp [noEquilibriumVal, h, hA]
  · simp only [noEquilibriumVal, h, ↓reduceIte, Bool.false_eq_true]
    split_ifs <;> norm_num

private theorem sum_finset_bool (f : Finset Bool → ℝ) :
    ∑ S : Finset Bool, f S = f ∅ + f {false} + f {true} + f Finset.univ := by
  rw [show (Finset.univ : Finset (Finset Bool)) = {∅, {false}, {true}, Finset.univ} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  ring

private noncomputable def noEquilibriumFractional (i : Bool) (S : Finset Bool) : ℝ :=
  if i then (if S.card = 2 then 1 / 2 else 0) else (if S.card = 1 then 1 / 2 else 0)

private theorem noEquilibriumFractional_isLPRFeasible :
    IsLPRFeasible noEquilibriumFractional :=
  { item_le := fun j => by
      rw [Fintype.sum_bool, Finset.sum_filter, Finset.sum_filter,
        sum_finset_bool, sum_finset_bool]
      cases j <;>
        simp only [Finset.notMem_empty, Finset.mem_singleton, Finset.mem_univ, ↓reduceIte,
          noEquilibriumFractional, Bool.false_eq_true, Bool.true_eq_false, Finset.card_singleton,
          Finset.card_univ, Fintype.card_bool] <;>
        norm_num
    bidder_le := fun i => by
      rw [sum_finset_bool]
      cases i <;>
        simp only [noEquilibriumFractional, Bool.false_eq_true, ↓reduceIte,
          Finset.card_empty, Finset.card_singleton, Finset.card_univ, Fintype.card_bool] <;>
        norm_num
    nonneg := fun i S => by
      dsimp only [noEquilibriumFractional]
      split_ifs <;> norm_num }

/-- The exact optimum of LPR on Example 11.14 is `7 / 2` (strictly greater than the best integral
welfare `3`), witnessed by assigning weight `1 / 2` to `(Alice, {a})`, `(Alice, {b})`, and
`(Bob, {a, b})`, with dual optimum `u = (1 / 2, 0)` and `p = (3 / 2, 3 / 2)`. -/
theorem exists_isLPROptimal_noEquilibriumVal :
    ∃ x, IsLPROptimal noEquilibriumVal x ∧ lprObjective noEquilibriumVal x = 7 / 2 := by
  have hval : lprObjective noEquilibriumVal noEquilibriumFractional = 7 / 2 := by
    unfold lprObjective
    rw [Fintype.sum_bool, sum_finset_bool, sum_finset_bool]
    norm_num [noEquilibriumFractional, noEquilibriumVal]
  have hup : IsDLPRFeasible noEquilibriumVal
      (fun i => if i then (0 : ℝ) else 1 / 2) (fun _ => (3 / 2 : ℝ)) :=
    { cover := fun i S => by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hnonneg : (0 : ℝ) ≤ (S.card : ℝ) * (3 / 2) := by positivity
        cases i <;> simp only [noEquilibriumVal, Bool.false_eq_true, ↓reduceIte] <;>
          split_ifs with hS
        · have hc : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hS
          linarith
        · linarith
        · simp [hS]
          norm_num
        · linarith
      utility_nonneg := fun i => by cases i <;> norm_num
      price_nonneg := fun _ => by norm_num }
  have hdual : dlprObjective (fun i : Bool => if i then (0 : ℝ) else 1 / 2)
      (fun _ : Bool => (3 / 2 : ℝ)) = 7 / 2 := by
    unfold dlprObjective
    rw [Fintype.sum_bool, Fintype.sum_bool]
    norm_num
  refine ⟨noEquilibriumFractional, ⟨noEquilibriumFractional_isLPRFeasible, fun y hy => ?_⟩, hval⟩
  exact (lprObjective_le_dlprObjective hy hup).trans_eq (hdual.trans hval.symm)

/-- **Example 11.14** ([BlumrosenNisan2007], §11.3.2, p. 278): the two-bidder, two-item
combinatorial auction `noEquilibriumVal` admits no Walrasian equilibrium. -/
theorem not_exists_isWalrasianEquilibrium_noEquilibriumVal :
    ¬ ∃ (p : Bool → ℝ) (a : Allocation Bool Bool),
      IsWalrasianEquilibrium noEquilibriumVal p a := by
  rintro ⟨p, a, heq⟩
  obtain ⟨x, hx, hval⟩ := exists_isLPROptimal_noEquilibriumVal
  have h1 := heq.lprObjective_le (fun i => (noEquilibriumVal_empty i).ge) hx.1
  have h2 := welfare_noEquilibriumVal_le a
  linarith

end Cslib.GameTheory.CombinatorialAuction
