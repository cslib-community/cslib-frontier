/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import CslibFrontier.Probability.Minimax.Value
public import Mathlib.Analysis.Convex.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Two-player zero-sum bimatrix games and linear-programming duality

A two-player bimatrix game `G : BimatrixGame M N` is **zero-sum** (`BimatrixGame.IsZeroSum`) if
`G.B = -G.A`, so the column player's payoff is the negation of the row player's payoff at every
outcome (`BimatrixGame.zeroSum A = ⟨A, -A⟩`; [TardosVazirani2007], Section 1.4.2, pp. 16–18).

Following [TardosVazirani2007], Section 1.4.2, p. 17, the row player's maximum guaranteed win is
given by the maximin linear program `max v` subject to `x ≥ 0`, `∑ i, x i = 1`, and
`∀ j, v ≤ (x ᵥ* A) j` (`IsMaximinFeasible`, `IsMaximinOptimal`), while the column player's minimum
guaranteed loss is given by the dual minimax linear program `min v` subject to `y ≥ 0`,
`∑ j, y j = 1`, and `∀ i, (A *ᵥ y) i ≤ v` (`IsMinimaxFeasible`, `IsMinimaxOptimal`).

This module establishes:

* **Weak and strong LP duality and minimax value bridge**: every maximin-feasible value `v₁` is at
  most `x ⬝ᵥ (A *ᵥ y)` and every minimax-feasible value `v₂` is at least `x ⬝ᵥ (A *ᵥ y)`, giving
  weak duality `v₁ ≤ v₂` (`IsMaximinFeasible.le_of_isMinimaxFeasible`). Connecting the dual pair to
  `Cslib.Probability.IsMinimaxValue` on `Aᵀ` (`isMinimaxValue_transpose_iff`) yields existence of
  primal-dual optimal solutions of equal value (`exists_isMaximinOptimal_and_isMinimaxOptimal`,
  `eq_of_isMaximinOptimal_of_isMinimaxOptimal`).
* **LP characterization of zero-sum Nash equilibria** ([TardosVazirani2007], Theorem 1.11,
  pp. 17–18): optimal solutions `(x, v₁)` and `(y, v₂)` to the two linear programs satisfy
  `v₁ = v₂ = (zeroSum A).payoff₁ x y` and form a Nash equilibrium of `zeroSum A`
  (`isNash_zeroSum_of_lpOptimal`, `payoff₁_zeroSum_eq_of_lpOptimal`), and conversely every Nash
  equilibrium of a zero-sum game is an optimal primal-dual pair at the equilibrium payoff
  (`isNash_zeroSum_iff_lpOptimal`, `IsZeroSum.isNash_iff`). The polynomial-time LP solvability
  remark in Section 1.4.2 is not formalized here (tracked in #7789).
* **Structural properties of zero-sum Nash equilibria**: equilibrium exchangeability
  (`IsZeroSum.isNash_exchange`), uniqueness of the equilibrium payoff
  (`IsZeroSum.payoff₁_eq_of_isNash`), and convexity of the set of Nash equilibria
  (`IsZeroSum.convex_isNash`).

## Main definitions

* `Cslib.GameTheory.BimatrixGame.zeroSum`: the zero-sum bimatrix game `⟨A, -A⟩`.
* `Cslib.GameTheory.BimatrixGame.IsZeroSum`: predicate `G.B = -G.A`.
* `Cslib.GameTheory.BimatrixGame.IsMaximinFeasible`,
  `Cslib.GameTheory.BimatrixGame.IsMaximinOptimal`: feasibility and optimality for the row player's
  maximin linear program ([TardosVazirani2007], Section 1.4.2, p. 17).
* `Cslib.GameTheory.BimatrixGame.IsMinimaxFeasible`,
  `Cslib.GameTheory.BimatrixGame.IsMinimaxOptimal`: feasibility and optimality for the column
  player's minimax linear program ([TardosVazirani2007], Section 1.4.2, p. 17).

## Main results

* `Cslib.GameTheory.BimatrixGame.IsMaximinFeasible.le_of_isMinimaxFeasible`: weak LP duality.
* `Cslib.GameTheory.BimatrixGame.isMinimaxValue_transpose_iff`,
  `Cslib.GameTheory.BimatrixGame.exists_isMaximinOptimal_and_isMinimaxOptimal`,
  `Cslib.GameTheory.BimatrixGame.eq_of_isMaximinOptimal_of_isMinimaxOptimal`: strong duality and
  minimax value equivalence.
* `Cslib.GameTheory.BimatrixGame.isNash_zeroSum_of_lpOptimal`,
  `Cslib.GameTheory.BimatrixGame.isNash_zeroSum_iff_lpOptimal`,
  `Cslib.GameTheory.BimatrixGame.IsZeroSum.isNash_iff`: Nash equilibria of zero-sum games coincide
  with optimal primal-dual LP pairs ([TardosVazirani2007], Theorem 1.11, pp. 17–18).
* `Cslib.GameTheory.BimatrixGame.IsZeroSum.isNash_exchange`,
  `Cslib.GameTheory.BimatrixGame.IsZeroSum.payoff₁_eq_of_isNash`,
  `Cslib.GameTheory.BimatrixGame.IsZeroSum.convex_isNash`: exchangeability, unique value, and
  convexity of zero-sum Nash equilibria.

## References

* [É. Tardos and V. V. Vazirani, *Basic Solution Concepts and Computational
  Issues*][TardosVazirani2007]
* [J. von Neumann, *Zur Theorie der Gesellschaftsspiele*][vonNeumann1928]
-/

public section

namespace Cslib.GameTheory.BimatrixGame

open Convexity Finset Matrix

section ZeroSumBasic

variable {M N : Type*}

/-- The two-player zero-sum bimatrix game `⟨A, -A⟩` determined by the row player's payoff matrix
`A` ([TardosVazirani2007], Section 1.4.2, p. 16). -/
def zeroSum (A : Matrix M N ℝ) : BimatrixGame M N :=
  ⟨A, -A⟩

@[simp]
theorem zeroSum_A (A : Matrix M N ℝ) : (zeroSum A).A = A := by rfl

@[simp]
theorem zeroSum_B (A : Matrix M N ℝ) : (zeroSum A).B = -A := by rfl

/-- A bimatrix game `G` is **zero-sum** ([TardosVazirani2007], Section 1.4.2, p. 16) if
`G.B = -G.A`. -/
@[expose] def IsZeroSum (G : BimatrixGame M N) : Prop :=
  G.B = -G.A

theorem isZeroSum_zeroSum (A : Matrix M N ℝ) : (zeroSum A).IsZeroSum := by rfl

theorem IsZeroSum.eq_zeroSum {G : BimatrixGame M N} (hG : G.IsZeroSum) : G = zeroSum G.A := by
  cases G
  dsimp only [IsZeroSum] at hG
  subst hG
  rfl

@[simp]
theorem swap_zeroSum (A : Matrix M N ℝ) : (zeroSum A).swap = zeroSum (-Aᵀ) := by
  simp only [zeroSum, swap_mk, transpose_neg, neg_neg]

theorem IsZeroSum.swap {G : BimatrixGame M N} (hG : G.IsZeroSum) : G.swap.IsZeroSum := by
  rw [hG.eq_zeroSum, swap_zeroSum]
  exact isZeroSum_zeroSum _

end ZeroSumBasic

section MaximinDefs

variable {M N : Type*} [Fintype M]

/-- `(x, v)` is **feasible** for the row player's maximin linear program
([TardosVazirani2007], Section 1.4.2, p. 17): `x` is a mixed strategy guaranteeing expected payoff
at least `v` against every pure column `j`. -/
@[expose] def IsMaximinFeasible (A : Matrix M N ℝ) (x : M → ℝ) (v : ℝ) : Prop :=
  IsMixedStrategy x ∧ ∀ j : N, v ≤ (x ᵥ* A) j

/-- `(x, v)` is **optimal** for the row player's maximin linear program
([TardosVazirani2007], Section 1.4.2, p. 17): it is feasible and `v` is at least the value of every
maximin-feasible pair. -/
@[expose] def IsMaximinOptimal (A : Matrix M N ℝ) (x : M → ℝ) (v : ℝ) : Prop :=
  IsMaximinFeasible A x v ∧ ∀ (x' : M → ℝ) (v' : ℝ), IsMaximinFeasible A x' v' → v' ≤ v

theorem IsMaximinFeasible.isMixedStrategy {A : Matrix M N ℝ} {x : M → ℝ} {v : ℝ}
    (hx : IsMaximinFeasible A x v) : IsMixedStrategy x := hx.1

theorem IsMaximinFeasible.le_vecMul {A : Matrix M N ℝ} {x : M → ℝ} {v : ℝ}
    (hx : IsMaximinFeasible A x v) (j : N) : v ≤ (x ᵥ* A) j := hx.2 j

theorem IsMaximinOptimal.isMaximinFeasible {A : Matrix M N ℝ} {x : M → ℝ} {v : ℝ}
    (hx : IsMaximinOptimal A x v) : IsMaximinFeasible A x v := hx.1

private theorem convex_isMaximinFeasible (A : Matrix M N ℝ) (v : ℝ) :
    Convex ℝ {x : M → ℝ | IsMaximinFeasible A x v} := by
  rintro x₁ ⟨hx₁, hle₁⟩ x₂ ⟨hx₂, hle₂⟩ a b ha hb hab
  refine ⟨isMixedStrategy_iff.2 ⟨fun i => ?_, ?_⟩, fun j => ?_⟩
  · exact add_nonneg (mul_nonneg ha (hx₁.nonneg i)) (mul_nonneg hb (hx₂.nonneg i))
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      hx₁.sum_eq_one, hx₂.sum_eq_one, mul_one, hab]
  · have hv : a * v + b * v = v := by rw [← add_mul, hab, one_mul]
    simp only [add_vecMul, smul_vecMul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [mul_le_mul_of_nonneg_left (hle₁ j) ha, mul_le_mul_of_nonneg_left (hle₂ j) hb]

end MaximinDefs

section MinimaxDefs

variable {M N : Type*} [Fintype N]

/-- `(y, v)` is **feasible** for the column player's minimax linear program
([TardosVazirani2007], Section 1.4.2, p. 17): `y` is a mixed strategy holding every pure row `i` to
expected payoff at most `v`. -/
@[expose] def IsMinimaxFeasible (A : Matrix M N ℝ) (y : N → ℝ) (v : ℝ) : Prop :=
  IsMixedStrategy y ∧ ∀ i : M, (A *ᵥ y) i ≤ v

/-- `(y, v)` is **optimal** for the column player's minimax linear program
([TardosVazirani2007], Section 1.4.2, p. 17): it is feasible and `v` is at most the value of every
minimax-feasible pair. -/
@[expose] def IsMinimaxOptimal (A : Matrix M N ℝ) (y : N → ℝ) (v : ℝ) : Prop :=
  IsMinimaxFeasible A y v ∧ ∀ (y' : N → ℝ) (v' : ℝ), IsMinimaxFeasible A y' v' → v ≤ v'

theorem IsMinimaxFeasible.isMixedStrategy {A : Matrix M N ℝ} {y : N → ℝ} {v : ℝ}
    (hy : IsMinimaxFeasible A y v) : IsMixedStrategy y := hy.1

theorem IsMinimaxFeasible.mulVec_le {A : Matrix M N ℝ} {y : N → ℝ} {v : ℝ}
    (hy : IsMinimaxFeasible A y v) (i : M) : (A *ᵥ y) i ≤ v := hy.2 i

theorem IsMinimaxOptimal.isMinimaxFeasible {A : Matrix M N ℝ} {y : N → ℝ} {v : ℝ}
    (hy : IsMinimaxOptimal A y v) : IsMinimaxFeasible A y v := hy.1

private theorem convex_isMinimaxFeasible (A : Matrix M N ℝ) (v : ℝ) :
    Convex ℝ {y : N → ℝ | IsMinimaxFeasible A y v} := by
  have heq : {y : N → ℝ | IsMinimaxFeasible A y v} =
      {y : N → ℝ | IsMaximinFeasible (-Aᵀ) y (-v)} := by
    ext y
    simp only [Set.mem_ofPred_eq, IsMinimaxFeasible, IsMaximinFeasible, vecMul_neg,
      vecMul_transpose, Pi.neg_apply, neg_le_neg_iff]
  rw [heq]
  exact convex_isMaximinFeasible (-Aᵀ) (-v)

end MinimaxDefs

section ZeroSumLP

variable {M N : Type*} [Fintype M] [Fintype N]

/-- In a zero-sum game, player 2's expected payoff is the negation of player 1's expected payoff. -/
theorem IsZeroSum.payoff₂_eq_neg_payoff₁ {G : BimatrixGame M N} (hG : G.IsZeroSum)
    (x : M → ℝ) (y : N → ℝ) : G.payoff₂ x y = -G.payoff₁ x y := by
  rw [payoff₂_eq_dotProduct, payoff₁_eq_dotProduct, hG, vecMul_neg, dotProduct_neg,
    dotProduct_comm, dotProduct_mulVec]

@[simp]
theorem payoff₂_zeroSum (A : Matrix M N ℝ) (x : M → ℝ) (y : N → ℝ) :
    (zeroSum A).payoff₂ x y = -(zeroSum A).payoff₁ x y :=
  (isZeroSum_zeroSum A).payoff₂_eq_neg_payoff₁ x y

/-- Against any mixed column strategy `y`, a maximin-feasible row strategy `(x, v)` earns expected
payoff at least `v`. -/
theorem IsMaximinFeasible.le_payoff₁ {A : Matrix M N ℝ} {x : M → ℝ} {v : ℝ}
    (hx : IsMaximinFeasible A x v) {y : N → ℝ} (hy : IsMixedStrategy y) :
    v ≤ (zeroSum A).payoff₁ x y := by
  rw [payoff₁_eq_dotProduct, zeroSum_A, dotProduct_mulVec, dotProduct_comm]
  calc v = ∑ j : N, y j * v := by rw [← sum_mul, hy.sum_eq_one, one_mul]
    _ ≤ ∑ j : N, y j * (x ᵥ* A) j :=
        sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hx.le_vecMul j) (hy.nonneg j)
    _ = y ⬝ᵥ (x ᵥ* A) := rfl

/-- Against any mixed row strategy `x`, a minimax-feasible column strategy `(y, v)` holds player 1's
expected payoff to at most `v`. -/
theorem IsMinimaxFeasible.payoff₁_le {A : Matrix M N ℝ} {y : N → ℝ} {v : ℝ}
    (hy : IsMinimaxFeasible A y v) {x : M → ℝ} (hx : IsMixedStrategy x) :
    (zeroSum A).payoff₁ x y ≤ v := by
  rw [payoff₁_eq_dotProduct, zeroSum_A]
  exact hx.dotProduct_le_of_forall_le hy.mulVec_le

/-- **Weak LP duality for zero-sum matrix games** ([TardosVazirani2007], Section 1.4.2, p. 17):
every maximin-feasible value `v₁` is at most every minimax-feasible value `v₂`. -/
theorem IsMaximinFeasible.le_of_isMinimaxFeasible {A : Matrix M N ℝ} {x : M → ℝ} {y : N → ℝ}
    {v₁ v₂ : ℝ} (hx : IsMaximinFeasible A x v₁) (hy : IsMinimaxFeasible A y v₂) :
    v₁ ≤ v₂ :=
  (hx.le_payoff₁ hy.isMixedStrategy).trans (hy.payoff₁_le hx.isMixedStrategy)

/-- Maximin-feasible and minimax-feasible solutions attaining the same value `v` are both
optimal. -/
theorem isMaximinOptimal_and_isMinimaxOptimal_of_feasible {A : Matrix M N ℝ} {x : M → ℝ}
    {y : N → ℝ} {v : ℝ} (hx : IsMaximinFeasible A x v) (hy : IsMinimaxFeasible A y v) :
    IsMaximinOptimal A x v ∧ IsMinimaxOptimal A y v :=
  ⟨⟨hx, fun _ _ hx' => hx'.le_of_isMinimaxFeasible hy⟩,
    ⟨hy, fun _ _ hy' => hx.le_of_isMinimaxFeasible hy'⟩⟩

/-- **Bridge to `Cslib.Probability.IsMinimaxValue`**: `v` is the minimax value of the transposed
loss table `Aᵀ` (where the first player chooses `j : N` paying `A i j` and the second chooses
`i : M` collecting `A i j`) iff `v` is simultaneously attained by maximin-optimal and
minimax-optimal strategies. -/
theorem isMinimaxValue_transpose_iff (A : Matrix M N ℝ) (v : ℝ) :
    Probability.IsMinimaxValue Aᵀ v ↔
      (∃ x : M → ℝ, IsMaximinOptimal A x v) ∧ ∃ y : N → ℝ, IsMinimaxOptimal A y v := by
  constructor
  · rintro ⟨⟨q, hq⟩, ⟨p, hp⟩⟩
    have hx : IsMaximinFeasible A p.weights v := by
      refine ⟨isMixedStrategy_weights p, fun j => (hp j).trans_eq ?_⟩
      rfl
    have hy : IsMinimaxFeasible A q.weights v := by
      refine ⟨isMixedStrategy_weights q, fun i => (le_of_eq ?_).trans (hq i)⟩
      exact sum_congr rfl fun j _ => mul_comm _ _
    obtain ⟨hx_opt, hy_opt⟩ := isMaximinOptimal_and_isMinimaxOptimal_of_feasible hx hy
    exact ⟨⟨p.weights, hx_opt⟩, ⟨q.weights, hy_opt⟩⟩
  · rintro ⟨⟨x, hx, -⟩, ⟨y, hy, -⟩⟩
    exact Probability.IsMinimaxValue.of_weights hy.isMixedStrategy.nonneg
      hy.isMixedStrategy.sum_eq_one
      (fun i => (le_of_eq (sum_congr rfl fun j _ => mul_comm _ _)).trans (hy.mulVec_le i))
      hx.isMixedStrategy.nonneg hx.isMixedStrategy.sum_eq_one hx.le_vecMul

/-- **Strong LP duality / minimax existence for zero-sum matrix games** ([TardosVazirani2007],
Section 1.4.2, pp. 17–18; [vonNeumann1928]): every finite nonempty zero-sum matrix game admits
optimal primal and dual strategies `(x, y)` sharing a common optimal value `v`. -/
theorem exists_isMaximinOptimal_and_isMinimaxOptimal [Nonempty M] [Nonempty N]
    (A : Matrix M N ℝ) :
    ∃ (x : M → ℝ) (y : N → ℝ) (v : ℝ), IsMaximinOptimal A x v ∧ IsMinimaxOptimal A y v := by
  obtain ⟨v, hv⟩ := Probability.exists_isMinimaxValue Aᵀ
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := (isMinimaxValue_transpose_iff A v).1 hv
  exact ⟨x, y, v, hx, hy⟩

/-- **Strong LP duality for optimal values** ([TardosVazirani2007], Section 1.4.2, pp. 17–18):
if `(x, v₁)` is maximin-optimal and `(y, v₂)` is minimax-optimal, then `v₁ = v₂`. -/
theorem eq_of_isMaximinOptimal_of_isMinimaxOptimal {A : Matrix M N ℝ} {x : M → ℝ} {y : N → ℝ}
    {v₁ v₂ : ℝ} (hx : IsMaximinOptimal A x v₁) (hy : IsMinimaxOptimal A y v₂) :
    v₁ = v₂ := by
  obtain ⟨i₀, -⟩ := hx.isMaximinFeasible.isMixedStrategy.exists_pos
  obtain ⟨j₀, -⟩ := hy.isMinimaxFeasible.isMixedStrategy.exists_pos
  have : Nonempty M := ⟨i₀⟩
  have : Nonempty N := ⟨j₀⟩
  obtain ⟨xStar, yStar, vStar, hxStar, hyStar⟩ := exists_isMaximinOptimal_and_isMinimaxOptimal A
  have h₁ : v₁ = vStar :=
    le_antisymm (hxStar.2 x v₁ hx.isMaximinFeasible) (hx.2 xStar vStar hxStar.isMaximinFeasible)
  have h₂ : v₂ = vStar :=
    le_antisymm (hy.2 yStar vStar hyStar.isMinimaxFeasible)
      (hyStar.2 y v₂ hy.isMinimaxFeasible)
  exact h₁.trans h₂.symm

/-- At any pair of maximin-optimal `(x, v₁)` and minimax-optimal `(y, v₂)` solutions, player 1's
expected payoff `(zeroSum A).payoff₁ x y` equals the maximin optimum `v₁`. -/
theorem payoff₁_zeroSum_eq_of_lpOptimal {A : Matrix M N ℝ} {x : M → ℝ} {y : N → ℝ}
    {v₁ v₂ : ℝ} (hx : IsMaximinOptimal A x v₁) (hy : IsMinimaxOptimal A y v₂) :
    (zeroSum A).payoff₁ x y = v₁ := by
  have hv : v₁ = v₂ := eq_of_isMaximinOptimal_of_isMinimaxOptimal hx hy
  subst hv
  exact le_antisymm (hy.isMinimaxFeasible.payoff₁_le hx.isMaximinFeasible.isMixedStrategy)
    (hx.isMaximinFeasible.le_payoff₁ hy.isMinimaxFeasible.isMixedStrategy)

/-- **Optimal LP solutions form a Nash equilibrium** ([TardosVazirani2007], Theorem 1.11,
pp. 17–18): if `(x, v₁)` is optimal for the row player's maximin LP and `(y, v₂)` is optimal for
the column player's minimax LP, then `(x, y)` is a Nash equilibrium of `zeroSum A`. -/
theorem isNash_zeroSum_of_lpOptimal {A : Matrix M N ℝ} {x : M → ℝ} {y : N → ℝ}
    {v₁ v₂ : ℝ} (hx : IsMaximinOptimal A x v₁) (hy : IsMinimaxOptimal A y v₂) :
    (zeroSum A).IsNash x y := by
  have hv : v₁ = v₂ := eq_of_isMaximinOptimal_of_isMinimaxOptimal hx hy
  subst hv
  have hpay : (zeroSum A).payoff₁ x y = v₁ := payoff₁_zeroSum_eq_of_lpOptimal hx hy
  refine isNash_iff.2 ⟨isBestResponse₁_iff_le_payoff₁.2
    ⟨hx.isMaximinFeasible.isMixedStrategy, fun i => ?_⟩,
    isBestResponse₂_iff_le_payoff₂.2 ⟨hy.isMinimaxFeasible.isMixedStrategy, fun j => ?_⟩⟩
  · rw [zeroSum_A, hpay]
    exact hy.isMinimaxFeasible.mulVec_le i
  · rw [zeroSum_B, payoff₂_zeroSum, hpay, vecMul_neg, Pi.neg_apply, neg_le_neg_iff]
    exact hx.isMaximinFeasible.le_vecMul j

/-- Every Nash equilibrium `(x, y)` of `zeroSum A` is a primal-dual optimal pair at the equilibrium
payoff `(zeroSum A).payoff₁ x y` ([TardosVazirani2007], Section 1.4.2, pp. 17–18). -/
theorem isNash_zeroSum_iff_lpOptimal_payoff₁ {A : Matrix M N ℝ} {x : M → ℝ} {y : N → ℝ} :
    (zeroSum A).IsNash x y ↔
      IsMaximinOptimal A x ((zeroSum A).payoff₁ x y) ∧
        IsMinimaxOptimal A y ((zeroSum A).payoff₁ x y) := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
    have hx_feas : IsMaximinFeasible A x ((zeroSum A).payoff₁ x y) := by
      refine ⟨h₁.isMixedStrategy, fun j => ?_⟩
      have hj := h₂.le_payoff₂ j
      rwa [zeroSum_B, payoff₂_zeroSum, vecMul_neg, Pi.neg_apply, neg_le_neg_iff] at hj
    have hy_feas : IsMinimaxFeasible A y ((zeroSum A).payoff₁ x y) :=
      ⟨h₂.isMixedStrategy, fun i => by simpa only [zeroSum_A] using h₁.le_payoff₁ i⟩
    exact isMaximinOptimal_and_isMinimaxOptimal_of_feasible hx_feas hy_feas
  · rintro ⟨hx, hy⟩
    exact isNash_zeroSum_of_lpOptimal hx hy

/-- **Primal-dual LP characterization of zero-sum Nash equilibria** ([TardosVazirani2007],
Section 1.4.2 and Theorem 1.11, pp. 17–18): `(x, y)` is a Nash equilibrium of `zeroSum A` iff
there is a value `v` at which `x` is maximin-optimal and `y` is minimax-optimal. -/
theorem isNash_zeroSum_iff_lpOptimal {A : Matrix M N ℝ} {x : M → ℝ} {y : N → ℝ} :
    (zeroSum A).IsNash x y ↔ ∃ v : ℝ, IsMaximinOptimal A x v ∧ IsMinimaxOptimal A y v :=
  ⟨fun h => ⟨(zeroSum A).payoff₁ x y, isNash_zeroSum_iff_lpOptimal_payoff₁.1 h⟩,
    fun ⟨_, hx, hy⟩ => isNash_zeroSum_of_lpOptimal hx hy⟩

/-- **LP characterization of Nash equilibria for any zero-sum bimatrix game** (`G.B = -G.A`). -/
theorem IsZeroSum.isNash_iff_payoff₁ {G : BimatrixGame M N} (hG : G.IsZeroSum)
    {x : M → ℝ} {y : N → ℝ} :
    G.IsNash x y ↔
      IsMaximinOptimal G.A x (G.payoff₁ x y) ∧ IsMinimaxOptimal G.A y (G.payoff₁ x y) := by
  conv_lhs => rw [hG.eq_zeroSum]
  conv_rhs => rw [hG.eq_zeroSum]
  exact isNash_zeroSum_iff_lpOptimal_payoff₁

/-- **Existential LP characterization of Nash equilibria** for any zero-sum bimatrix game. -/
theorem IsZeroSum.isNash_iff {G : BimatrixGame M N} (hG : G.IsZeroSum) {x : M → ℝ} {y : N → ℝ} :
    G.IsNash x y ↔ ∃ v : ℝ, IsMaximinOptimal G.A x v ∧ IsMinimaxOptimal G.A y v := by
  conv_lhs => rw [hG.eq_zeroSum]
  exact isNash_zeroSum_iff_lpOptimal

/-! ### Structural properties of zero-sum Nash equilibria -/

/-- **Equilibrium exchangeability**: in a zero-sum bimatrix game, if `(x₁, y₁)` and `(x₂, y₂)` are
Nash equilibria, then `(x₁, y₂)` is also a Nash equilibrium. -/
theorem IsZeroSum.isNash_exchange {G : BimatrixGame M N} (hG : G.IsZeroSum)
    {x₁ x₂ : M → ℝ} {y₁ y₂ : N → ℝ} (h₁ : G.IsNash x₁ y₁) (h₂ : G.IsNash x₂ y₂) :
    G.IsNash x₁ y₂ := by
  obtain ⟨v₁, hx₁, -⟩ := hG.isNash_iff.1 h₁
  obtain ⟨v₂, -, hy₂⟩ := hG.isNash_iff.1 h₂
  rw [hG.eq_zeroSum]
  exact isNash_zeroSum_of_lpOptimal hx₁ hy₂

/-- **Unique equilibrium value**: all Nash equilibria of a zero-sum bimatrix game yield the same
expected payoff to player 1. -/
theorem IsZeroSum.payoff₁_eq_of_isNash {G : BimatrixGame M N} (hG : G.IsZeroSum)
    {x₁ x₂ : M → ℝ} {y₁ y₂ : N → ℝ} (h₁ : G.IsNash x₁ y₁) (h₂ : G.IsNash x₂ y₂) :
    G.payoff₁ x₁ y₁ = G.payoff₁ x₂ y₂ :=
  eq_of_isMaximinOptimal_of_isMinimaxOptimal
    (hG.isNash_iff_payoff₁.1 h₁).1 (hG.isNash_iff_payoff₁.1 h₂).2

/-- **Convexity of Nash equilibria**: in a zero-sum bimatrix game, the set of Nash equilibria is
convex in `(M → ℝ) × (N → ℝ)`. -/
theorem IsZeroSum.convex_isNash {G : BimatrixGame M N} (hG : G.IsZeroSum) :
    Convex ℝ {p : (M → ℝ) × (N → ℝ) | G.IsNash p.1 p.2} := by
  rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂ a b ha hb hab
  rw [Set.mem_ofPred_eq] at h₁ h₂ ⊢
  set v : ℝ := G.payoff₁ x₁ y₁
  have hv₂ : G.payoff₁ x₂ y₂ = v := (hG.payoff₁_eq_of_isNash h₁ h₂).symm
  obtain ⟨hx₁, hy₁⟩ := hG.isNash_iff_payoff₁.1 h₁
  obtain ⟨hx₂, hy₂⟩ := hG.isNash_iff_payoff₁.1 h₂
  rw [hv₂] at hx₂ hy₂
  have hx : IsMaximinFeasible G.A (a • x₁ + b • x₂) v :=
    convex_isMaximinFeasible G.A v hx₁.isMaximinFeasible hx₂.isMaximinFeasible ha hb hab
  have hy : IsMinimaxFeasible G.A (a • y₁ + b • y₂) v :=
    convex_isMinimaxFeasible G.A v hy₁.isMinimaxFeasible hy₂.isMinimaxFeasible ha hb hab
  exact hG.isNash_iff.2 ⟨v, isMaximinOptimal_and_isMinimaxOptimal_of_feasible hx hy⟩

end ZeroSumLP

end Cslib.GameTheory.BimatrixGame
