/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import CslibFrontier.GameTheory.Bimatrix.CostGame
public import CslibFrontier.GameTheory.Bimatrix.Symmetric
public import CslibFrontier.GameTheory.Strategic.Correlated
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The correlated-equilibrium polytope and extreme-point Nash equilibria

In a finite two-player bimatrix game `G : BimatrixGame M N`, a joint probability matrix
`P : Matrix M N ℝ` is a **correlated equilibrium** (`BimatrixGame.IsCorrelated`;
[TardosVazirani2007], Section 1.3.6, p. 15; [Papadimitriou2007], Section 2.7, equation (CE), p. 46)
if its entries are nonnegative, sum to `1`, and no recommended row `i` or column `j` has a
profitable unilateral deviation `i'` or `j'`. The set of such matrices is the
**correlated-equilibrium polytope** (`BimatrixGame.correlatedPolytope`).

This module establishes:

* **Convexity, cost-game bridge, and product-distribution characterization**
  ([Papadimitriou2007], Section 2.7, pp. 46–47): `G.correlatedPolytope` is convex
  (`convex_correlatedPolytope`), corresponds under `jointMatrix` and `jointWeight` to
  `CostGame.IsCorrelatedEquilibrium` on `G.toCostGame` (`isCorrelated_jointMatrix_iff`,
  `isCorrelated_iff_toCostGame`), and contains a product matrix `Matrix.vecMulVec x y` of mixed
  strategies iff `(x, y)` is a Nash equilibrium (`isCorrelated_vecMulVec_iff_isNash`).
* **Support equality and support-equation uniqueness in nondegenerate games**
  ([vonStengel2007], Exercises 3.1 and 3.2, p. 77): in any Nash equilibrium `(x, y)` of a
  nondegenerate game, every pure best response is played with positive probability
  (`IsNondegenerate.support_left_eq_of_isNash`, `IsNondegenerate.support_right_eq_of_isNash`), and
  no distinct mixed strategy supported inside `Function.support y` can keep all pure best responses
  to `y` optimal when `{i | G.IsPureBestResponse₁ y i}.ncard = (Function.support y).ncard`
  (`IsNondegenerate.eq_of_support_subset_of_isPureBestResponse₁`,
  `IsNondegenerate.eq_of_support_subset_of_isPureBestResponse₂`).
* **Extreme points and linear-objective uniqueness of nondegenerate Nash equilibria**
  ([Papadimitriou2007], Section 2.7.1, Theorem 2.5 and accompanying remark, p. 47): in any
  nondegenerate bimatrix game, every Nash equilibrium `(x, y)` is the unique maximizer of an
  explicit linear objective over `G.correlatedPolytope`
  (`IsNondegenerate.exists_unique_maximizer_correlatedPolytope`) and hence an extreme point of
  `G.correlatedPolytope` (`IsNondegenerate.vecMulVec_mem_extremePoints_correlatedPolytope`). The
  efficient LP solvability remarks of Section 2.7 are not formalized here (tracked in #7789).
* **Chicken / traffic-light separation between `correlatedPolytope` and `conv(NE)`**
  ([Papadimitriou2007], Section 2.7 and Figure 2.4, pp. 45–48; cf. [TardosVazirani2007],
  Example 1.10, pp. 14–15): the symmetric `2 × 2` Chicken / drivers game
  `chickenGame = ofSymmetric !![4, 1; 5, 0]` is nondegenerate, has exactly three Nash equilibria
  (two pure with social welfare `6` and one symmetric mixed with social welfare `5`), admits the
  50–50 traffic signal `C₁ = !![0, 1/2; 1/2, 0]` outside rank-one product distributions, and admits
  the social-welfare-optimal correlated equilibrium `C₂ = !![1/3, 1/3; 1/3, 0]` achieving welfare
  `20 / 3`, strictly exceeding `6` and therefore lying strictly outside the convex hull of all Nash
  equilibrium product distributions (`chickenOptimalCorrelated_mem_sdiff_convexHull_isNash`).

## Main definitions

* `Cslib.GameTheory.BimatrixGame.IsCorrelated`: bimatrix correlated equilibrium predicate.
* `Cslib.GameTheory.BimatrixGame.correlatedPolytope`: `{P | G.IsCorrelated P}`.
* `Cslib.GameTheory.BimatrixGame.jointMatrix`, `Cslib.GameTheory.BimatrixGame.jointWeight`:
  conversions between bimatrix joint matrices and `G.toCostGame` profile distributions.
* `Cslib.GameTheory.BimatrixGame.socialWelfare`: expected sum of utilities under `P`.
* `Cslib.GameTheory.BimatrixGame.chickenGame`,
  `Cslib.GameTheory.BimatrixGame.chickenTrafficLight`,
  `Cslib.GameTheory.BimatrixGame.chickenOptimalCorrelated`: the `2 × 2` Chicken / drivers game and
  correlated equilibria `C₁`, `C₂` of [Papadimitriou2007], Section 2.7, pp. 45–48.

## Main results

* `Cslib.GameTheory.BimatrixGame.convex_correlatedPolytope`,
  `Cslib.GameTheory.BimatrixGame.isCorrelated_jointMatrix_iff`,
  `Cslib.GameTheory.BimatrixGame.isCorrelated_iff_toCostGame`,
  `Cslib.GameTheory.BimatrixGame.isCorrelated_vecMulVec_iff_isNash`: convexity, cost-game
  equivalence, and product-distribution characterization of `correlatedPolytope`.
* `Cslib.GameTheory.BimatrixGame.IsNondegenerate.support_left_eq_of_isNash`,
  `Cslib.GameTheory.BimatrixGame.IsNondegenerate.support_right_eq_of_isNash`: [vonStengel2007],
  Exercise 3.2, p. 77.
* `Cslib.GameTheory.BimatrixGame.IsNondegenerate.eq_of_support_subset_of_isPureBestResponse₁`,
  `Cslib.GameTheory.BimatrixGame.IsNondegenerate.eq_of_support_subset_of_isPureBestResponse₂`:
  [vonStengel2007], Exercise 3.1, p. 77.
* `Cslib.GameTheory.BimatrixGame.IsNondegenerate.exists_unique_maximizer_correlatedPolytope`,
  `Cslib.GameTheory.BimatrixGame.IsNondegenerate.vecMulVec_mem_extremePoints_correlatedPolytope`:
  [Papadimitriou2007], Theorem 2.5, p. 47.
* `Cslib.GameTheory.BimatrixGame.chickenGame_isNondegenerate`,
  `Cslib.GameTheory.BimatrixGame.chickenGame_isNash_iff`,
  `Cslib.GameTheory.BimatrixGame.chickenOptimalCorrelated_mem_sdiff_convexHull_isNash`,
  `Cslib.GameTheory.BimatrixGame.chickenOptimalCorrelated_socialWelfare_gt_convexHull_isNash`:
  complete equilibrium classification and strict `CE \ conv(NE)` welfare separation for Chicken.

## References

* [C. H. Papadimitriou, *The Complexity of Finding Nash Equilibria*][Papadimitriou2007]
* [É. Tardos and V. V. Vazirani, *Basic Solution Concepts and Computational
  Issues*][TardosVazirani2007]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007]
-/

public section

namespace Cslib.GameTheory.BimatrixGame

open Convexity Finset Function Matrix

/-! ### The bimatrix correlated-equilibrium polytope -/

section Polytope

universe u v

variable {M : Type u} {N : Type v} [Fintype M] [Fintype N]

/-- A joint distribution matrix `P : Matrix M N ℝ` is a **correlated equilibrium** of `G`
([TardosVazirani2007], Section 1.3.6, p. 15; [Papadimitriou2007], Section 2.7, equation (CE),
p. 46): its entries are nonnegative and sum to `1`, and conditioned on any recommended row `i` (or
column `j`), switching to `i'` (or `j'`) does not increase that player's expected payoff. -/
@[expose] def IsCorrelated (G : BimatrixGame M N) (P : Matrix M N ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∑ i, ∑ j, P i j = 1) ∧
    (∀ i i' : M, ∑ j : N, P i j * G.A i' j ≤ ∑ j : N, P i j * G.A i j) ∧
    ∀ j j' : N, ∑ i : M, P i j * G.B i j' ≤ ∑ i : M, P i j * G.B i j

/-- The **correlated-equilibrium polytope** `{P | G.IsCorrelated P}` in `Matrix M N ℝ`
([Papadimitriou2007], Section 2.7, pp. 46–48). -/
def correlatedPolytope (G : BimatrixGame M N) : Set (Matrix M N ℝ) :=
  {P | G.IsCorrelated P}

@[simp]
theorem mem_correlatedPolytope_iff {G : BimatrixGame M N} {P : Matrix M N ℝ} :
    P ∈ G.correlatedPolytope ↔ G.IsCorrelated P := by
  rw [correlatedPolytope, Set.mem_ofPred_eq]

theorem IsCorrelated.nonneg {G : BimatrixGame M N} {P : Matrix M N ℝ}
    (hP : G.IsCorrelated P) (i : M) (j : N) : 0 ≤ P i j :=
  hP.1 i j

theorem IsCorrelated.sum_eq_one {G : BimatrixGame M N} {P : Matrix M N ℝ}
    (hP : G.IsCorrelated P) : ∑ i, ∑ j, P i j = 1 :=
  hP.2.1

theorem IsCorrelated.row_le {G : BimatrixGame M N} {P : Matrix M N ℝ}
    (hP : G.IsCorrelated P) (i i' : M) :
    ∑ j : N, P i j * G.A i' j ≤ ∑ j : N, P i j * G.A i j :=
  hP.2.2.1 i i'

theorem IsCorrelated.col_le {G : BimatrixGame M N} {P : Matrix M N ℝ}
    (hP : G.IsCorrelated P) (j j' : N) :
    ∑ i : M, P i j * G.B i j' ≤ ∑ i : M, P i j * G.B i j :=
  hP.2.2.2 j j'

/-- Swapping the players transposes correlated equilibria. -/
@[simp]
theorem isCorrelated_swap {G : BimatrixGame M N} {P : Matrix M N ℝ} :
    G.swap.IsCorrelated Pᵀ ↔ G.IsCorrelated P := by
  simp only [IsCorrelated, transpose_apply, swap_A, swap_B]
  exact ⟨fun ⟨hnn, hsum, hrow, hcol⟩ =>
      ⟨fun i j => hnn j i, (Finset.sum_comm (f := fun i j => P i j)).trans hsum, hcol, hrow⟩,
    fun ⟨hnn, hsum, hrow, hcol⟩ =>
      ⟨fun j i => hnn i j, (Finset.sum_comm (f := fun j i => P i j)).trans hsum, hcol, hrow⟩⟩

/-- **The correlated-equilibrium polytope is convex** ([Papadimitriou2007], Section 2.7, p. 47). -/
theorem convex_correlatedPolytope (G : BimatrixGame M N) : Convex ℝ G.correlatedPolytope := by
  rintro P₁ hP₁ P₂ hP₂ a b ha hb hab
  rcases mem_correlatedPolytope_iff.1 hP₁ with ⟨hnn₁, hsum₁, hrow₁, hcol₁⟩
  rcases mem_correlatedPolytope_iff.1 hP₂ with ⟨hnn₂, hsum₂, hrow₂, hcol₂⟩
  refine mem_correlatedPolytope_iff.2
    ⟨fun i j => add_nonneg (mul_nonneg ha (hnn₁ i j)) (mul_nonneg hb (hnn₂ i j)), ?_,
      fun i i' => ?_, fun j j' => ?_⟩
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
      hsum₁, hsum₂, mul_one, hab]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, mul_assoc,
      sum_add_distrib, ← mul_sum]
    linarith [mul_le_mul_of_nonneg_left (hrow₁ i i') ha, mul_le_mul_of_nonneg_left (hrow₂ i i') hb]
  · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, mul_assoc,
      sum_add_distrib, ← mul_sum]
    linarith [mul_le_mul_of_nonneg_left (hcol₁ j j') ha, mul_le_mul_of_nonneg_left (hcol₂ j j') hb]

/-! ### Bridge to `CostGame.IsCorrelatedEquilibrium` -/

private def pureProfile (i : M) (j : N) : ∀ b, PureStrategy M N b
  | false => ULift.up i
  | true => ULift.up j

private def pureProfileEquiv : (∀ b, PureStrategy M N b) ≃ M × N where
  toFun s := (ULift.down (s false), ULift.down (s true))
  invFun p := pureProfile p.1 p.2
  left_inv s := by
    funext b
    cases b <;> rfl
  right_inv _ := rfl

omit [Fintype M] [Fintype N] in
/-- The joint probability matrix on `M × N` induced by a distribution on `G.toCostGame` profiles. -/
def jointMatrix (σ : StdSimplex ℝ (∀ b, PureStrategy M N b)) : Matrix M N ℝ :=
  Matrix.of fun i j => σ.weights (pureProfile i j)

omit [Fintype M] [Fintype N] in
@[simp]
theorem jointMatrix_apply (σ : StdSimplex ℝ (∀ b, PureStrategy M N b)) (i : M) (j : N) :
    jointMatrix σ i j =
      σ.weights (fun b => match b with | false => ULift.up i | true => ULift.up j) := by
  rfl

omit [Fintype M] [Fintype N] in
/-- The profile weight function on `∀ b, PureStrategy M N b` induced by a matrix `P`. -/
def jointWeight (P : Matrix M N ℝ) (s : ∀ b, PureStrategy M N b) : ℝ :=
  P (ULift.down (s false)) (ULift.down (s true))

omit [Fintype M] [Fintype N] in
@[simp]
theorem jointWeight_apply (P : Matrix M N ℝ) (s : ∀ b, PureStrategy M N b) :
    jointWeight P s = P (ULift.down (s false)) (ULift.down (s true)) := by
  rfl

private theorem sum_jointWeight_eq (P : Matrix M N ℝ)
    (f : (∀ b, PureStrategy M N b) → ℝ) :
    ∑ s, jointWeight P s * f s =
      ∑ i : M, ∑ j : N, P i j * f (pureProfile i j) := by
  rw [← pureProfileEquiv.symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- **Equivalence between `BimatrixGame.IsCorrelated` and `CostGame.IsCorrelatedEquilibrium` on
`G.toCostGame`**: a distribution `σ` on pure profiles of `G.toCostGame` is a correlated equilibrium
iff its induced matrix `jointMatrix σ` lies in `G.correlatedPolytope`. -/
theorem isCorrelated_jointMatrix_iff (G : BimatrixGame M N)
    (σ : StdSimplex ℝ (∀ b, PureStrategy M N b)) :
    G.IsCorrelated (jointMatrix σ) ↔ G.toCostGame.IsCorrelatedEquilibrium σ := by
  classical
  have hnn : ∀ i j, 0 ≤ jointMatrix σ i j := fun i j => σ.weights_nonneg _
  have hsum : ∑ i : M, ∑ j : N, jointMatrix σ i j = 1 := by
    have htot := σ.total_of_fintype
    rw [← pureProfileEquiv.symm.sum_comp, Fintype.sum_prod_type] at htot
    exact htot
  have hrow_sum (i i' : M) :
      σ.weights.sum (fun s w =>
        w * if s false = ULift.up i then G.toCostGame.cost false (update s false (ULift.up i'))
          else 0) = -∑ j : N, jointMatrix σ i j * G.A i' j := by
    rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), ← pureProfileEquiv.symm.sum_comp,
      Fintype.sum_prod_type]
    have hinner : ∀ x : M,
        (∑ y : N, σ.weights (pureProfile x y) *
          if pureProfile x y false = ULift.up i then
            G.toCostGame.cost false (update (pureProfile x y) false (ULift.up i')) else 0) =
        if x = i then -(∑ y : N, jointMatrix σ i y * G.A i' y) else 0 := fun x => by
      by_cases hxi : x = i
      · subst hxi
        simp only [pureProfile, toCostGame, update_self, update_of_ne (by decide : true ≠ false),
          ↓reduceIte, mul_neg, sum_neg_distrib]
        rfl
      · simp only [hxi, ↓reduceIte]
        exact sum_eq_zero fun y _ => by
          have hne : pureProfile x y false ≠ ULift.up i := fun h => hxi (congrArg ULift.down h)
          simp only [hne, ↓reduceIte, mul_zero]
    exact (sum_congr rfl fun x _ => hinner x).trans
      (by simp only [sum_ite_eq', mem_univ, ↓reduceIte])
  have hcol_sum (j j' : N) :
      σ.weights.sum (fun s w =>
        w * if s true = ULift.up j then G.toCostGame.cost true (update s true (ULift.up j'))
          else 0) = -∑ i : M, jointMatrix σ i j * G.B i j' := by
    rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _), ← pureProfileEquiv.symm.sum_comp,
      Fintype.sum_prod_type, sum_comm]
    have hinner : ∀ y : N,
        (∑ x : M, σ.weights (pureProfile x y) *
          if pureProfile x y true = ULift.up j then
            G.toCostGame.cost true (update (pureProfile x y) true (ULift.up j')) else 0) =
        if y = j then -(∑ x : M, jointMatrix σ x j * G.B x j') else 0 := fun y => by
      by_cases hyj : y = j
      · subst hyj
        simp only [pureProfile, toCostGame, update_self, update_of_ne (by decide : false ≠ true),
          ↓reduceIte, mul_neg, sum_neg_distrib]
        rfl
      · simp only [hyj, ↓reduceIte]
        exact sum_eq_zero fun x _ => by
          have hne : pureProfile x y true ≠ ULift.up j := fun h => hyj (congrArg ULift.down h)
          simp only [hne, ↓reduceIte, mul_zero]
    exact (sum_congr rfl fun y _ => hinner y).trans
      (by simp only [sum_ite_eq', mem_univ, ↓reduceIte])
  have hself_eq (b : Bool) (a : PureStrategy M N b) :
      σ.weights.sum (fun s w => w * if s b = a then G.toCostGame.cost b s else 0) =
      σ.weights.sum (fun s w => w * if s b = a then G.toCostGame.cost b (update s b a) else 0) :=
    Finsupp.sum_congr fun s _ => by
      split_ifs with hs
      · rw [← hs, update_eq_self]
      · rfl
  rw [CostGame.isCorrelatedEquilibrium_iff]
  constructor
  · rintro ⟨-, -, hrow, hcol⟩ (_ | _) ⟨a⟩ ⟨a'⟩
    · rw [hself_eq false ⟨a⟩, hrow_sum a a, hrow_sum a a', neg_le_neg_iff]
      exact hrow a a'
    · rw [hself_eq true ⟨a⟩, hcol_sum a a, hcol_sum a a', neg_le_neg_iff]
      exact hcol a a'
  · intro hce
    refine ⟨hnn, hsum, fun i i' => ?_, fun j j' => ?_⟩
    · simpa only [hself_eq false ⟨i⟩, hrow_sum i i, hrow_sum i i', neg_le_neg_iff] using
        hce false ⟨i⟩ ⟨i'⟩
    · simpa only [hself_eq true ⟨j⟩, hcol_sum j j, hcol_sum j j', neg_le_neg_iff] using
        hce true ⟨j⟩ ⟨j'⟩

/-- **Polytope-level bridge to `G.toCostGame`**: `P` lies in `G.correlatedPolytope` iff
`jointWeight P` belongs to the switching-function correlated-equilibrium polytope of `G.toCostGame`
in `(∀ b, PureStrategy M N b) → ℝ` (`CostGame.convex_correlatedEquilibriumPolytope`). -/
theorem isCorrelated_iff_toCostGame (G : BimatrixGame M N) (P : Matrix M N ℝ) :
    G.IsCorrelated P ↔ IsMixedStrategy (jointWeight P) ∧
      ∀ b (δ : PureStrategy M N b → PureStrategy M N b),
        ∑ s, jointWeight P s * G.toCostGame.cost b s ≤
          ∑ s, jointWeight P s * G.toCostGame.cost b (update s b (δ (s b))) := by
  have hmix : IsMixedStrategy (jointWeight P) ↔
      (∀ i j, 0 ≤ P i j) ∧ ∑ i : M, ∑ j : N, P i j = 1 := by
    rw [isMixedStrategy_iff, ← pureProfileEquiv.symm.sum_comp, Fintype.sum_prod_type]
    exact and_congr ⟨fun h i j => h (pureProfile i j), fun h s => h _ _⟩ Iff.rfl
  constructor
  · rintro ⟨hnn, hsum, hrow, hcol⟩
    refine ⟨hmix.2 ⟨hnn, hsum⟩, fun b δ => ?_⟩
    cases b
    · rw [sum_jointWeight_eq, sum_jointWeight_eq]
      refine sum_le_sum fun i _ => ?_
      cases hδ : δ ⟨i⟩ with | up i' =>
      simpa only [pureProfile, toCostGame, hδ, update_self,
        update_of_ne (by decide : true ≠ false), mul_neg, sum_neg_distrib, neg_le_neg_iff]
        using hrow i i'
    · rw [(sum_jointWeight_eq P _).trans Finset.sum_comm,
        (sum_jointWeight_eq P _).trans Finset.sum_comm]
      refine sum_le_sum fun j _ => ?_
      cases hδ : δ ⟨j⟩ with | up j' =>
      simpa only [pureProfile, toCostGame, hδ, update_self,
        update_of_ne (by decide : false ≠ true), mul_neg, sum_neg_distrib, neg_le_neg_iff]
        using hcol j j'
  · rintro ⟨hw, hsw⟩
    let σ : StdSimplex ℝ (∀ b, PureStrategy M N b) :=
      { weights := Finsupp.equivFunOnFinite.symm (jointWeight P)
        nonneg := hw.nonneg
        total := (Finsupp.sum_fintype _ _ (fun _ => rfl)).trans hw.sum_eq_one }
    have hσ : G.toCostGame.IsCorrelatedEquilibrium σ := fun b δ => by
      rw [Finsupp.sum_fintype _ _ (fun _ => zero_mul _),
        Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
      exact hsw b δ
    exact (G.isCorrelated_jointMatrix_iff σ).2 hσ

omit [Fintype M] in
private theorem sum_vecMulVec_mul_A (x : M → ℝ) (y : N → ℝ) (A : Matrix M N ℝ) (i k : M) :
    ∑ j : N, Matrix.vecMulVec x y i j * A k j = x i * (A *ᵥ y) k := by
  simp only [vecMulVec_apply, mul_assoc, ← mul_sum, mulVec, dotProduct]
  exact congrArg (x i * ·) (sum_congr rfl fun _ _ => mul_comm _ _)

omit [Fintype N] in
private theorem sum_vecMulVec_mul_B (x : M → ℝ) (y : N → ℝ) (B : Matrix M N ℝ) (j k : N) :
    ∑ i : M, Matrix.vecMulVec x y i j * B i k = y j * (x ᵥ* B) k := by
  calc ∑ i : M, Matrix.vecMulVec x y i j * B i k = ∑ i : M, y j * (x i * B i k) :=
        sum_congr rfl fun _ _ => by rw [vecMulVec_apply]; ring
    _ = y j * (x ᵥ* B) k := by rw [← mul_sum]; rfl

/-! ### Product distributions and Nash equilibria -/

/-- The product matrix `Matrix.vecMulVec x y` of any Nash equilibrium `(x, y)` is a correlated
equilibrium ([Papadimitriou2007], Section 2.7, p. 46). -/
theorem IsNash.isCorrelated_vecMulVec {G : BimatrixGame M N} {x : M → ℝ} {y : N → ℝ}
    (h : G.IsNash x y) : G.IsCorrelated (Matrix.vecMulVec x y) := by
  obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
  have hx := h₁.isMixedStrategy
  have hy := h₂.isMixedStrategy
  refine ⟨fun i j => mul_nonneg (hx.nonneg i) (hy.nonneg j), ?_, fun i i' => ?_, fun j j' => ?_⟩
  · simp only [vecMulVec_apply, ← mul_sum, hy.sum_eq_one, mul_one, hx.sum_eq_one]
  · rw [sum_vecMulVec_mul_A, sum_vecMulVec_mul_A]
    rcases (hx.nonneg i).eq_or_lt with h0 | hi
    · rw [← h0, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left
        (isPureBestResponse₁_iff.1 ((isBestResponse₁_iff.1 h₁).2 i hi) i') hi.le
  · rw [sum_vecMulVec_mul_B, sum_vecMulVec_mul_B]
    rcases (hy.nonneg j).eq_or_lt with h0 | hj
    · rw [← h0, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left
        (isPureBestResponse₂_iff.1 ((isBestResponse₂_iff.1 h₂).2 j hj) j') hj.le

/-- **Product correlated equilibria are Nash equilibria** ([Papadimitriou2007], Section 2.7,
p. 46): for mixed strategies `x` and `y`, their outer product `Matrix.vecMulVec x y` is a
correlated equilibrium iff `(x, y)` is a Nash equilibrium. -/
theorem isCorrelated_vecMulVec_iff_isNash {G : BimatrixGame M N} {x : M → ℝ} {y : N → ℝ}
    (hx : IsMixedStrategy x) (hy : IsMixedStrategy y) :
    G.IsCorrelated (Matrix.vecMulVec x y) ↔ G.IsNash x y := by
  refine ⟨fun hP => ?_, fun h => h.isCorrelated_vecMulVec⟩
  rcases hP with ⟨-, -, hrow, hcol⟩
  refine isNash_iff.2 ⟨isBestResponse₁_iff.2 ⟨hx, fun i hi => isPureBestResponse₁_iff.2
    fun i' => ?_⟩, isBestResponse₂_iff.2 ⟨hy, fun j hj => isPureBestResponse₂_iff.2
    fun j' => ?_⟩⟩
  · exact le_of_mul_le_mul_left (by simpa only [sum_vecMulVec_mul_A] using hrow i i') hi
  · exact le_of_mul_le_mul_left (by simpa only [sum_vecMulVec_mul_B] using hcol j j') hj

/-- Every convex combination of Nash equilibrium product matrices belongs to `G.correlatedPolytope`
([Papadimitriou2007], Section 2.7, pp. 46–47). -/
theorem convexHull_vecMulVec_isNash_subset_correlatedPolytope (G : BimatrixGame M N) :
    convexHull ℝ {P : Matrix M N ℝ | ∃ x y, G.IsNash x y ∧ Matrix.vecMulVec x y = P} ⊆
      G.correlatedPolytope := by
  refine convexHull_min ?_ G.convex_correlatedPolytope
  rintro P ⟨x, y, h, rfl⟩
  exact mem_correlatedPolytope_iff.2 h.isCorrelated_vecMulVec

end Polytope

/-! ### Nondegenerate support equality and support-equation uniqueness -/

section NondegenerateSupport

variable {M N : Type*} [Fintype M] [Fintype N]

/-- **All pure best responses are played in a nondegenerate Nash equilibrium** ([vonStengel2007],
Exercise 3.2, p. 77), row player: if `G` is nondegenerate and `(x, y)` is a Nash equilibrium, then
`Function.support x` equals `{i | G.IsPureBestResponse₁ y i}`. -/
theorem IsNondegenerate.support_left_eq_of_isNash {G : BimatrixGame M N}
    (hG : G.IsNondegenerate) {x : M → ℝ} {y : N → ℝ} (h : G.IsNash x y) :
    Function.support x = {i | G.IsPureBestResponse₁ y i} := by
  obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
  have hsub : Function.support x ⊆ {i | G.IsPureBestResponse₁ y i} := fun i hi =>
    (isBestResponse₁_iff.1 h₁).2 i ((h₁.isMixedStrategy.nonneg i).lt_of_ne' hi)
  have hcard : {i | G.IsPureBestResponse₁ y i}.ncard ≤ (Function.support x).ncard :=
    ((isNondegenerate_iff.1 hG).2 y h₂.isMixedStrategy).trans_eq (h.ncard_support_eq hG).symm
  exact Set.eq_of_subset_of_ncard_le hsub hcard (Set.toFinite _)

/-- **All pure best responses are played in a nondegenerate Nash equilibrium** ([vonStengel2007],
Exercise 3.2, p. 77), column player. -/
theorem IsNondegenerate.support_right_eq_of_isNash {G : BimatrixGame M N}
    (hG : G.IsNondegenerate) {x : M → ℝ} {y : N → ℝ} (h : G.IsNash x y) :
    Function.support y = {j | G.IsPureBestResponse₂ x j} := by
  simpa only [isPureBestResponse₁_swap] using
    (isNondegenerate_swap.2 hG).support_left_eq_of_isNash (isNash_swap.2 h)

/-- **Uniqueness of support-equation solutions in nondegenerate games** ([vonStengel2007],
Exercise 3.1, p. 77, proving the uniqueness claim after Algorithm 3.4 on p. 57): in a
nondegenerate game `G`, if a mixed strategy `y` has `{i | G.IsPureBestResponse₁ y i}.ncard =
(Function.support y).ncard`, then any mixed strategy `y'` with `Function.support y' ⊆
Function.support y` for which every pure best response to `y` remains a pure best response to `y'`
must equal `y`. -/
theorem IsNondegenerate.eq_of_support_subset_of_isPureBestResponse₁ {G : BimatrixGame M N}
    (hG : G.IsNondegenerate) {y y' : N → ℝ}
    (hy : IsMixedStrategy y) (hy' : IsMixedStrategy y')
    (hsupp : Function.support y' ⊆ Function.support y)
    (hcard : {i | G.IsPureBestResponse₁ y i}.ncard = (Function.support y).ncard)
    (hbr : ∀ i, G.IsPureBestResponse₁ y i → G.IsPureBestResponse₁ y' i) :
    y' = y := by
  classical
  by_contra hne
  set d : N → ℝ := y' - y
  have hd_sum : ∑ j : N, d j = 0 := by
    simp only [d, Pi.sub_apply, sum_sub_distrib, hy'.sum_eq_one, hy.sum_eq_one, sub_self]
  have hd_zero_outside : ∀ j : N, y j = 0 → d j = 0 := fun j hyj => by
    have hy'j : y' j = 0 := by_contra fun h0 => hsupp h0 hyj
    simp only [d, Pi.sub_apply, hy'j, hyj, sub_self]
  have hex_neg : ∃ j : N, d j < 0 := by
    by_contra! hnn
    have hd0 := (sum_eq_zero_iff_of_nonneg fun j _ => hnn j).1 hd_sum
    exact hne <| funext fun j => sub_eq_zero.1 (hd0 j (mem_univ j))
  -- Obtain a pure best response `i₀` to `y` from `hy.exists_pos` and `hcard`.
  obtain ⟨j_pos, hj_pos⟩ := hy.exists_pos
  have hsupp_pos : 0 < (Function.support y).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨j_pos, hj_pos.ne'⟩
  obtain ⟨i₀, hi₀⟩ := Set.nonempty_of_ncard_ne_zero (hcard.trans_gt hsupp_pos).ne'
  rw [Set.mem_ofPred_eq] at hi₀
  have hi₀_le : ∀ k : M, (G.A *ᵥ y) k ≤ (G.A *ᵥ y) i₀ := isPureBestResponse₁_iff.1 hi₀
  have hi₀'_le : ∀ k : M, (G.A *ᵥ y') k ≤ (G.A *ᵥ y') i₀ :=
    isPureBestResponse₁_iff.1 (hbr i₀ hi₀)
  -- Every row in `I := {i | G.IsPureBestResponse₁ y i}` ties `i₀` along `y + t • d`.
  have hray_eq : ∀ (t : ℝ) (i : M), G.IsPureBestResponse₁ y i →
      (G.A *ᵥ (y + t • d)) i = (G.A *ᵥ (y + t • d)) i₀ := fun t i hi => by
    have hy_eq : (G.A *ᵥ y) i = (G.A *ᵥ y) i₀ :=
      le_antisymm (hi₀_le i) ((isPureBestResponse₁_iff.1 hi) i₀)
    have hy'_eq : (G.A *ᵥ y') i = (G.A *ᵥ y') i₀ :=
      le_antisymm (hi₀'_le i) ((isPureBestResponse₁_iff.1 (hbr i hi)) i₀)
    simp only [d, mulVec_add, mulVec_smul, mulVec_sub, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      smul_eq_mul, hy_eq, hy'_eq]
  -- Minimum positive step `t₁` hitting `y j + t₁ * d j = 0` for some `j` with `d j < 0`.
  set S_neg : Finset N := univ.filter fun j => d j < 0
  obtain ⟨j_neg, hj_neg⟩ := hex_neg
  obtain ⟨j₁, hj₁S, hj₁_min⟩ :=
    exists_min_image S_neg (fun j => y j / (-d j)) ⟨j_neg, mem_filter.2 ⟨mem_univ _, hj_neg⟩⟩
  have hj₁_neg : d j₁ < 0 := (mem_filter.1 hj₁S).2
  have hy_j₁_pos : 0 < y j₁ :=
    (hy.nonneg j₁).lt_of_ne' fun h0 => hj₁_neg.ne (hd_zero_outside j₁ h0)
  set t₁ : ℝ := y j₁ / (-d j₁)
  have ht₁_pos : 0 < t₁ := div_pos hy_j₁_pos (neg_pos.2 hj₁_neg)
  have hmix_of_le : ∀ t : ℝ, 0 ≤ t → t ≤ t₁ → IsMixedStrategy (y + t • d) := fun t ht₀ ht₁ =>
    isMixedStrategy_iff.2 ⟨fun j => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rcases lt_or_ge (d j) 0 with hdj | hdj
      · have hmul := (le_div_iff₀ (neg_pos.2 hdj)).1
          (ht₁.trans (hj₁_min j (mem_filter.2 ⟨mem_univ _, hdj⟩)))
        linarith
      · exact add_nonneg (hy.nonneg j) (mul_nonneg ht₀ hdj),
      by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, sum_add_distrib, ← mul_sum,
          hy.sum_eq_one, hd_sum, mul_zero, add_zero]⟩
  have hsupp_ray : ∀ t : ℝ, Function.support (y + t • d) ⊆ Function.support y := fun t j hj => by
    by_contra hyj
    rw [Function.mem_support, not_not] at hyj
    exact hj (by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hyj,
      hd_zero_outside j hyj, mul_zero, add_zero])
  -- Case split on whether `i₀` (hence every row in `I`) is still a pure best response at `t₁`.
  by_cases hbr_t₁ : ∀ i' : M, (G.A *ᵥ (y + t₁ • d)) i' ≤ (G.A *ᵥ (y + t₁ • d)) i₀
  · -- Case 1: `I` remains optimal at `y + t₁ • d`, while `j₁ ∈ support y` drops out of support.
    have hy_t₁ := hmix_of_le t₁ ht₁_pos.le le_rfl
    have hj₁_zero : (y + t₁ • d) j₁ = 0 := by
      simp only [t₁, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hj₁_neg.ne]
      ring
    have hlt_supp : (Function.support (y + t₁ • d)).ncard < (Function.support y).ncard :=
      Set.ncard_lt_ncard (lt_of_le_of_ne (hsupp_ray t₁) fun heq => by
        have hj₁_in : j₁ ∈ Function.support y := hy_j₁_pos.ne'
        rw [← heq] at hj₁_in
        exact hj₁_in hj₁_zero) (Set.toFinite _)
    have hle_br : {i | G.IsPureBestResponse₁ y i}.ncard ≤
        {i | G.IsPureBestResponse₁ (y + t₁ • d) i}.ncard :=
      Set.ncard_le_ncard (fun i hi => isPureBestResponse₁_iff.2 fun i' =>
        (hbr_t₁ i').trans_eq (hray_eq t₁ i hi).symm) (Set.toFinite _)
    have hnd := (isNondegenerate_iff.1 hG).2 (y + t₁ • d) hy_t₁
    omega
  · -- Case 2: Some row outside `I` overtakes `i₀` before `t₁`; stop at the first tie `t₂ < t₁`.
    push Not at hbr_t₁
    obtain ⟨i₁, hi₁_gt⟩ := hbr_t₁
    have hi₁_not : ¬G.IsPureBestResponse₁ y i₁ := fun h => hi₁_gt.ne (hray_eq t₁ i₁ h).symm
    have hgap_pos : ∀ i' : M, ¬G.IsPureBestResponse₁ y i' → 0 < (G.A *ᵥ y) i₀ - (G.A *ᵥ y) i' :=
      fun i' hi' => sub_pos.2 <| (hi₀_le i').lt_of_ne fun heq =>
        hi' (isPureBestResponse₁_iff.2 fun k => (hi₀_le k).trans_eq heq.symm)
    have hi₁_slope : 0 < (G.A *ᵥ d) i₁ - (G.A *ᵥ d) i₀ := by
      have hgap₁ := hgap_pos i₁ hi₁_not
      simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi₁_gt
      by_contra! hle
      linarith [mul_nonpos_of_nonneg_of_nonpos ht₁_pos.le hle]
    set S_viol : Finset M :=
      univ.filter fun i' => ¬G.IsPureBestResponse₁ y i' ∧ 0 < (G.A *ᵥ d) i' - (G.A *ᵥ d) i₀
    obtain ⟨i₂, hi₂S, hi₂_min⟩ := exists_min_image S_viol
      (fun i' => ((G.A *ᵥ y) i₀ - (G.A *ᵥ y) i') / ((G.A *ᵥ d) i' - (G.A *ᵥ d) i₀))
      ⟨i₁, mem_filter.2 ⟨mem_univ _, hi₁_not, hi₁_slope⟩⟩
    obtain ⟨hi₂_not, hi₂_slope⟩ := (mem_filter.1 hi₂S).2
    set t₂ : ℝ := ((G.A *ᵥ y) i₀ - (G.A *ᵥ y) i₂) / ((G.A *ᵥ d) i₂ - (G.A *ᵥ d) i₀)
    have ht₂_pos : 0 < t₂ := div_pos (hgap_pos i₂ hi₂_not) hi₂_slope
    have ht₂_lt_t₁ : t₂ < t₁ := by
      refine (hi₂_min i₁ (mem_filter.2 ⟨mem_univ _, hi₁_not, hi₁_slope⟩)).trans_lt ?_
      rw [div_lt_iff₀ hi₁_slope]
      simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi₁_gt
      linarith
    have hbr_t₂ : ∀ i' : M, (G.A *ᵥ (y + t₂ • d)) i' ≤ (G.A *ᵥ (y + t₂ • d)) i₀ := fun i' => by
      by_cases hi' : G.IsPureBestResponse₁ y i'
      · exact (hray_eq t₂ i' hi').le
      · simp only [mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rcases lt_or_ge 0 ((G.A *ᵥ d) i' - (G.A *ᵥ d) i₀) with hslope | hslope
        · linarith [(le_div_iff₀ hslope).1 (hi₂_min i' (mem_filter.2 ⟨mem_univ _, hi', hslope⟩))]
        · linarith [mul_nonpos_of_nonneg_of_nonpos ht₂_pos.le hslope, (hgap_pos i' hi').le]
    have hi₂_tie : (G.A *ᵥ (y + t₂ • d)) i₂ = (G.A *ᵥ (y + t₂ • d)) i₀ := by
      simp only [t₂, mulVec_add, mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hi₂_slope.ne']; ring
    have hins_sub : insert i₂ {i | G.IsPureBestResponse₁ y i} ⊆
        {i | G.IsPureBestResponse₁ (y + t₂ • d) i} := fun i hi =>
      isPureBestResponse₁_iff.2 fun i' =>
        (hbr_t₂ i').trans_eq (hi.elim (· ▸ hi₂_tie.symm) fun h => (hray_eq t₂ i h).symm)
    have hcard_ins : (insert i₂ {i | G.IsPureBestResponse₁ y i}).ncard =
        (Function.support y).ncard + 1 := by
      rw [Set.ncard_insert_of_notMem hi₂_not (Set.toFinite _), hcard]
    have hle_br := Set.ncard_le_ncard hins_sub (Set.toFinite _)
    have hle_supp := Set.ncard_le_ncard (hsupp_ray t₂) (Set.toFinite _)
    have hnd := (isNondegenerate_iff.1 hG).2 (y + t₂ • d) (hmix_of_le t₂ ht₂_pos.le ht₂_lt_t₁.le)
    omega

/-- **Uniqueness of support-equation solutions in nondegenerate games**, row-strategy form
([vonStengel2007], Exercise 3.1, p. 77). -/
theorem IsNondegenerate.eq_of_support_subset_of_isPureBestResponse₂ {G : BimatrixGame M N}
    (hG : G.IsNondegenerate) {x x' : M → ℝ}
    (hx : IsMixedStrategy x) (hx' : IsMixedStrategy x')
    (hsupp : Function.support x' ⊆ Function.support x)
    (hcard : {j | G.IsPureBestResponse₂ x j}.ncard = (Function.support x).ncard)
    (hbr : ∀ j, G.IsPureBestResponse₂ x j → G.IsPureBestResponse₂ x' j) :
    x' = x := by
  refine (isNondegenerate_swap.2 hG).eq_of_support_subset_of_isPureBestResponse₁ hx hx' hsupp ?_ ?_
  · simpa only [isPureBestResponse₁_swap] using hcard
  · intro j hj
    exact isPureBestResponse₁_swap.2 (hbr j (isPureBestResponse₁_swap.1 hj))

end NondegenerateSupport

/-! ### Theorem 2.5: Nondegenerate Nash equilibria are extreme points of `correlatedPolytope` -/

section ExtremePoints

variable {M N : Type*} [Fintype M] [Fintype N]

private theorem sum_sum_eq_zero_apply {α β : Type*} [Fintype α] [Fintype β] {f : α → β → ℝ}
    (hf : ∀ a b, 0 ≤ f a b) (hsum : ∑ a, ∑ b, f a b = 0) (a : α) (b : β) : f a b = 0 :=
  (sum_eq_zero_iff_of_nonneg fun b' _ => hf a b').1
    ((sum_eq_zero_iff_of_nonneg fun a' _ => sum_nonneg fun b' _ => hf a' b').1 hsum a (mem_univ a))
    b (mem_univ b)

/-- Conditional row factorization via Exercise 3.1: if `P ∈ G.correlatedPolytope` vanishes outside
`support x × support y` and has zero row-deviation slack among rows in `support x`, then every row
of `P` is proportional to `y`. -/
private theorem row_eq_sum_mul_of_tight {G : BimatrixGame M N} (hG : G.IsNondegenerate)
    {x : M → ℝ} {y : N → ℝ} (h : G.IsNash x y) {P : Matrix M N ℝ} (hP : G.IsCorrelated P)
    (hzero : ∀ i j, (x i = 0 ∨ y j = 0) → P i j = 0)
    (htight : ∀ i i', 0 < x i → 0 < x i' →
      ∑ j : N, P i j * (G.A i j - G.A i' j) = 0) :
    ∀ (i : M) (j : N), P i j = (∑ j' : N, P i j') * y j := by
  obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
  have hx := h₁.isMixedStrategy
  have hy := h₂.isMixedStrategy
  intro i
  set s : ℝ := ∑ j' : N, P i j'
  rcases (sum_nonneg fun j' _ => hP.nonneg i j' : 0 ≤ s).eq_or_lt with hs0 | hs_pos
  · intro j
    rw [(sum_eq_zero_iff_of_nonneg fun j' _ => hP.nonneg i j').1 hs0.symm j (mem_univ j),
      show s = 0 from hs0.symm, zero_mul]
  · have hxi_pos : 0 < x i := (hx.nonneg i).lt_of_ne' fun hxi0 =>
      hs_pos.ne' (sum_eq_zero fun j' _ => hzero i j' (.inl hxi0))
    have hPi_ne : (fun j' => P i j') ≠ 0 := fun h0 => by
      simp only [h0, Pi.zero_apply, sum_const_zero, lt_self_iff_false] at hs_pos
    set yi : N → ℝ := s⁻¹ • fun j' => P i j'
    have hyi : IsMixedStrategy yi := isMixedStrategy_inv_sum_smul (fun j' => hP.nonneg i j') hPi_ne
    have hsupp_yi : Function.support yi ⊆ Function.support y := fun j hj => by
      by_contra hyj0
      rw [Function.mem_support, not_not] at hyj0
      exact hj (by simp only [yi, Pi.smul_apply, smul_eq_mul, hzero i j (.inr hyj0), mul_zero])
    have hcard_y : {i' | G.IsPureBestResponse₁ y i'}.ncard = (Function.support y).ncard :=
      hG.support_left_eq_of_isNash h ▸ h.ncard_support_eq hG
    have hbr_yi : ∀ i', G.IsPureBestResponse₁ y i' → G.IsPureBestResponse₁ yi i' := fun i' hi' => by
      have hi'_supp : i' ∈ Function.support x := by
        rw [hG.support_left_eq_of_isNash h]
        exact hi'
      have hxi'_pos : 0 < x i' := (hx.nonneg i').lt_of_ne' hi'_supp
      have heq : ∑ j : N, P i j * G.A i j = ∑ j : N, P i j * G.A i' j := by
        simpa only [mul_sub, sum_sub_distrib, sub_eq_zero] using htight i i' hxi_pos hxi'_pos
      have hmulVec : ∀ k : M, (G.A *ᵥ yi) k = s⁻¹ * ∑ j : N, P i j * G.A k j := fun k =>
        calc (G.A *ᵥ yi) k = ∑ j : N, G.A k j * (s⁻¹ * P i j) := rfl
          _ = ∑ j : N, s⁻¹ * (P i j * G.A k j) := sum_congr rfl fun _ _ => by ring
          _ = s⁻¹ * ∑ j : N, P i j * G.A k j := by rw [← mul_sum]
      exact isPureBestResponse₁_iff.2 fun i'' => by
        rw [hmulVec i'', hmulVec i']
        exact mul_le_mul_of_nonneg_left ((hP.row_le i i'').trans_eq heq) (inv_nonneg.2 hs_pos.le)
    have hyi_eq := hG.eq_of_support_subset_of_isPureBestResponse₁ hy hyi hsupp_yi hcard_y hbr_yi
    intro j
    have hj : s⁻¹ * P i j = y j := congrFun hyi_eq j
    calc P i j = s * (s⁻¹ * P i j) := by rw [← mul_assoc, mul_inv_cancel₀ hs_pos.ne', one_mul]
      _ = s * y j := by rw [hj]

/-- **Every Nash equilibrium of a nondegenerate bimatrix game is the unique correlated-equilibrium
maximizer of some linear objective** ([Papadimitriou2007], Section 2.7.1, p. 47): for any
nondegenerate game `G` and Nash equilibrium `(x, y)`, there exists a weight matrix
`W : Matrix M N ℝ` whose linear objective `P ↦ ∑ i, ∑ j, W i j * P i j` on `G.correlatedPolytope`
attains its maximum uniquely at `Matrix.vecMulVec x y`. -/
theorem IsNondegenerate.exists_unique_maximizer_correlatedPolytope {G : BimatrixGame M N}
    (hG : G.IsNondegenerate) {x : M → ℝ} {y : N → ℝ} (h : G.IsNash x y) :
    ∃ W : Matrix M N ℝ, ∀ P ∈ G.correlatedPolytope,
      (∑ i : M, ∑ j : N, W i j * P i j ≤
        ∑ i : M, ∑ j : N, W i j * Matrix.vecMulVec x y i j) ∧
      (∑ i : M, ∑ j : N, W i j * P i j =
        ∑ i : M, ∑ j : N, W i j * Matrix.vecMulVec x y i j ↔ P = Matrix.vecMulVec x y) := by
  classical
  obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
  have hy := h₂.isMixedStrategy
  let c₁ : M → N → ℝ := fun i j => if x i = 0 ∨ y j = 0 then 1 else 0
  let c₂ : M → N → ℝ := fun i j =>
    if 0 < x i then ∑ i' : M, (if 0 < x i' then G.A i j - G.A i' j else 0) else 0
  let c₃ : M → N → ℝ := fun i j =>
    if 0 < y j then ∑ j' : N, (if 0 < y j' then G.B i j - G.B i j' else 0) else 0
  let W : Matrix M N ℝ := Matrix.of fun i j => -(c₁ i j + c₂ i j + c₃ i j)
  -- Decompose `-∑ i, ∑ j, W i j * P i j` into the three nonnegative slack penalties.
  have hpen (P : Matrix M N ℝ) :
      -(∑ i : M, ∑ j : N, W i j * P i j) =
        (∑ i : M, ∑ j : N, c₁ i j * P i j) +
        (∑ i : M, ∑ i' : M,
          if 0 < x i ∧ 0 < x i' then ∑ j : N, P i j * (G.A i j - G.A i' j) else 0) +
        (∑ j : N, ∑ j' : N,
          if 0 < y j ∧ 0 < y j' then ∑ i : M, P i j * (G.B i j - G.B i j') else 0) := by
    have hW_expand : -(∑ i : M, ∑ j : N, W i j * P i j) =
        (∑ i : M, ∑ j : N, c₁ i j * P i j) +
        (∑ i : M, ∑ j : N, c₂ i j * P i j) +
        (∑ i : M, ∑ j : N, c₃ i j * P i j) := by
      simp only [W, of_apply, neg_mul, sum_neg_distrib, neg_neg, add_mul, sum_add_distrib]
    have hc₂_sum : (∑ i : M, ∑ j : N, c₂ i j * P i j) =
        ∑ i : M, ∑ i' : M,
          if 0 < x i ∧ 0 < x i' then ∑ j : N, P i j * (G.A i j - G.A i' j) else 0 :=
      sum_congr rfl fun i _ => by
        by_cases hxi : 0 < x i
        · simp only [c₂, hxi, ↓reduceIte, true_and, sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun i' _ => ?_
          by_cases hxi' : 0 < x i'
          · simp only [hxi', ↓reduceIte]
            exact sum_congr rfl fun _ _ => mul_comm _ _
          · simp only [hxi', ↓reduceIte, zero_mul, sum_const_zero]
        · simp only [c₂, hxi, ↓reduceIte, false_and, zero_mul, sum_const_zero]
    have hc₃_sum : (∑ i : M, ∑ j : N, c₃ i j * P i j) =
        ∑ j : N, ∑ j' : N,
          if 0 < y j ∧ 0 < y j' then ∑ i : M, P i j * (G.B i j - G.B i j') else 0 := by
      rw [sum_comm]
      exact sum_congr rfl fun j _ => by
        by_cases hyj : 0 < y j
        · simp only [c₃, hyj, ↓reduceIte, true_and, sum_mul]
          rw [sum_comm]
          refine sum_congr rfl fun j' _ => ?_
          by_cases hyj' : 0 < y j'
          · simp only [hyj', ↓reduceIte]
            exact sum_congr rfl fun _ _ => mul_comm _ _
          · simp only [hyj', ↓reduceIte, zero_mul, sum_const_zero]
        · simp only [c₃, hyj, ↓reduceIte, false_and, zero_mul, sum_const_zero]
    rw [hW_expand, hc₂_sum, hc₃_sum]
  -- At `vecMulVec x y`, all three slack penalties vanish.
  have hopt_zero : ∑ i : M, ∑ j : N, W i j * Matrix.vecMulVec x y i j = 0 := by
    suffices -(∑ i : M, ∑ j : N, W i j * Matrix.vecMulVec x y i j) = 0 by linarith
    have h₁_zero : ∑ i : M, ∑ j : N, c₁ i j * Matrix.vecMulVec x y i j = 0 :=
      sum_eq_zero fun i _ => sum_eq_zero fun j _ => by
        dsimp only [c₁]
        rw [vecMulVec_apply]
        by_cases hxy : x i = 0 ∨ y j = 0
        · rcases hxy with h0 | h0 <;> simp [h0]
        · simp [hxy]
    have h₂_zero : (∑ i : M, ∑ i' : M,
        if 0 < x i ∧ 0 < x i' then
          ∑ j : N, Matrix.vecMulVec x y i j * (G.A i j - G.A i' j) else 0) = 0 :=
      sum_eq_zero fun i _ => sum_eq_zero fun i' _ => by
        split_ifs with hpos
        · have heq : (G.A *ᵥ y) i = (G.A *ᵥ y) i' :=
            calc (G.A *ᵥ y) i = _ := (h₁.payoff₁_eq_of_pos hpos.1).symm
              _ = (G.A *ᵥ y) i' := h₁.payoff₁_eq_of_pos hpos.2
          calc ∑ j : N, Matrix.vecMulVec x y i j * (G.A i j - G.A i' j)
              = x i * (G.A *ᵥ y) i - x i * (G.A *ᵥ y) i' := by
                simp only [mul_sub, sum_sub_distrib, sum_vecMulVec_mul_A]
            _ = 0 := by rw [heq, sub_self]
        · rfl
    have h₃_zero : (∑ j : N, ∑ j' : N,
        if 0 < y j ∧ 0 < y j' then
          ∑ i : M, Matrix.vecMulVec x y i j * (G.B i j - G.B i j') else 0) = 0 :=
      sum_eq_zero fun j _ => sum_eq_zero fun j' _ => by
        split_ifs with hpos
        · have heq : (x ᵥ* G.B) j = (x ᵥ* G.B) j' :=
            calc (x ᵥ* G.B) j = _ := (h₂.payoff₂_eq_of_pos hpos.1).symm
              _ = (x ᵥ* G.B) j' := h₂.payoff₂_eq_of_pos hpos.2
          calc ∑ i : M, Matrix.vecMulVec x y i j * (G.B i j - G.B i j')
              = y j * (x ᵥ* G.B) j - y j * (x ᵥ* G.B) j' := by
                simp only [mul_sub, sum_sub_distrib, sum_vecMulVec_mul_B]
            _ = 0 := by rw [heq, sub_self]
        · rfl
    rw [hpen, h₁_zero, h₂_zero, h₃_zero, add_zero, add_zero]
  refine ⟨W, fun P hP_mem => ?_⟩
  have hP := mem_correlatedPolytope_iff.1 hP_mem
  have hc₁_nn : ∀ i j, 0 ≤ c₁ i j * P i j := fun i j => by
    dsimp only [c₁]
    split_ifs
    · exact mul_nonneg zero_le_one (hP.nonneg i j)
    · rw [zero_mul]
  have hrow_nn : ∀ i i' : M,
      0 ≤ if 0 < x i ∧ 0 < x i' then ∑ j : N, P i j * (G.A i j - G.A i' j) else 0 := fun i i' => by
    split_ifs
    · simp only [mul_sub, sum_sub_distrib]
      exact sub_nonneg.2 (hP.row_le i i')
    · exact le_rfl
  have hcol_nn : ∀ j j' : N,
      0 ≤ if 0 < y j ∧ 0 < y j' then ∑ i : M, P i j * (G.B i j - G.B i j') else 0 := fun j j' => by
    split_ifs
    · simp only [mul_sub, sum_sub_distrib]
      exact sub_nonneg.2 (hP.col_le j j')
    · exact le_rfl
  have hb₁_nn : 0 ≤ ∑ i : M, ∑ j : N, c₁ i j * P i j :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => hc₁_nn i j
  have hb₂_nn : 0 ≤ ∑ i : M, ∑ i' : M,
      if 0 < x i ∧ 0 < x i' then ∑ j : N, P i j * (G.A i j - G.A i' j) else 0 :=
    sum_nonneg fun i _ => sum_nonneg fun i' _ => hrow_nn i i'
  have hb₃_nn : 0 ≤ ∑ j : N, ∑ j' : N,
      if 0 < y j ∧ 0 < y j' then ∑ i : M, P i j * (G.B i j - G.B i j') else 0 :=
    sum_nonneg fun j _ => sum_nonneg fun j' _ => hcol_nn j j'
  rw [hopt_zero]
  refine ⟨by linarith [hpen P],
    ⟨fun heq0 => ?_, fun hPeq => by rw [hPeq, hopt_zero]⟩⟩
  have hpen0 := hpen P
  rw [heq0, neg_zero] at hpen0
  have hzero : ∀ i j, (x i = 0 ∨ y j = 0) → P i j = 0 := fun i j hij => by
    simpa only [c₁, hij, ↓reduceIte, one_mul] using
      sum_sum_eq_zero_apply hc₁_nn (by linarith) i j
  have htight₁ : ∀ i i', 0 < x i → 0 < x i' → ∑ j : N, P i j * (G.A i j - G.A i' j) = 0 :=
    fun i i' hxi hxi' => by
      simpa only [hxi, hxi', and_self, ↓reduceIte] using
        sum_sum_eq_zero_apply hrow_nn (by linarith) i i'
  have htight₂ : ∀ j j', 0 < y j → 0 < y j' →
      ∑ i : M, Pᵀ j i * (G.swap.A j i - G.swap.A j' i) = 0 := fun j j' hyj hyj' => by
    simpa only [hyj, hyj', and_self, ↓reduceIte, transpose_apply, swap_A] using
      sum_sum_eq_zero_apply hcol_nn (by linarith) j j'
  have hrow_fac := row_eq_sum_mul_of_tight hG h hP hzero htight₁
  have hcol_fac := row_eq_sum_mul_of_tight (isNondegenerate_swap.2 hG) (isNash_swap.2 h)
    (isCorrelated_swap.2 hP) (fun j i hji => hzero i j hji.symm) htight₂
  -- `P i j = (∑ j', P i j') * y j = (∑ i', P i' j) * x i`; summing over `i` identifies marginals.
  have hmarg : ∀ i : M, ∑ j' : N, P i j' = x i := fun i => by
    calc ∑ j' : N, P i j' = (∑ j' : N, P i j') * ∑ j : N, y j := by rw [hy.sum_eq_one, mul_one]
      _ = ∑ j : N, P i j := by rw [mul_sum]; exact sum_congr rfl fun j _ => (hrow_fac i j).symm
      _ = ∑ j : N, (∑ i' : M, P i' j) * x i := sum_congr rfl fun j _ => hcol_fac j i
      _ = x i := by
          rw [← sum_mul, Finset.sum_comm (f := fun j i' => P i' j), hP.sum_eq_one, one_mul]
  ext i j
  rw [hrow_fac i j, hmarg i, vecMulVec_apply]

/-- **Nondegenerate Nash equilibria are extreme points of the correlated-equilibrium polytope**
([Papadimitriou2007], Section 2.7.1, Theorem 2.5, p. 47): in any nondegenerate two-player game `G`,
if `(x, y)` is a Nash equilibrium, then
`Matrix.vecMulVec x y ∈ G.correlatedPolytope.extremePoints ℝ`. -/
theorem IsNondegenerate.vecMulVec_mem_extremePoints_correlatedPolytope {G : BimatrixGame M N}
    (hG : G.IsNondegenerate) {x : M → ℝ} {y : N → ℝ} (h : G.IsNash x y) :
    Matrix.vecMulVec x y ∈ G.correlatedPolytope.extremePoints ℝ := by
  obtain ⟨W, hW⟩ := hG.exists_unique_maximizer_correlatedPolytope h
  refine mem_extremePoints_iff_left.2 ⟨mem_correlatedPolytope_iff.2 h.isCorrelated_vecMulVec,
    fun P₁ hP₁ P₂ hP₂ ⟨a, b, ha, hb, hab, hcomb⟩ => ?_⟩
  set f : Matrix M N ℝ → ℝ := fun P => ∑ i : M, ∑ j : N, W i j * P i j
  have hf_comb : a * f P₁ + b * f P₂ = f (Matrix.vecMulVec x y) :=
    calc a * f P₁ + b * f P₂
        = (∑ i : M, ∑ j : N, W i j * (a * P₁ i j)) +
            ∑ i : M, ∑ j : N, W i j * (b * P₂ i j) := by
          simp only [f, mul_sum]
          congr 1 <;> exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring
      _ = f (Matrix.vecMulVec x y) := by
          rw [← hcomb]
          simp only [f, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_add, sum_add_distrib]
  have hsum_ab : a * f (Matrix.vecMulVec x y) + b * f (Matrix.vecMulVec x y) =
      f (Matrix.vecMulVec x y) := by rw [← add_mul, hab, one_mul]
  refine (hW P₁ hP₁).2.1 (by_contra fun hne₁ => ?_)
  linarith [mul_lt_mul_of_pos_left ((hW P₁ hP₁).1.lt_of_ne hne₁) ha,
    mul_le_mul_of_nonneg_left (hW P₂ hP₂).1 hb.le]

end ExtremePoints

/-! ### Chicken / traffic-light separation between `correlatedPolytope` and `conv(NE)` -/

section ChickenSeparation

/-- The expected sum of both players' payoffs under a joint matrix `P`
([Papadimitriou2007], Section 2.7, p. 47). -/
def socialWelfare {M N : Type*} [Fintype M] [Fintype N] (G : BimatrixGame M N)
    (P : Matrix M N ℝ) : ℝ :=
  ∑ i : M, ∑ j : N, P i j * (G.A i j + G.B i j)

theorem socialWelfare_def {M N : Type*} [Fintype M] [Fintype N] (G : BimatrixGame M N)
    (P : Matrix M N ℝ) :
    G.socialWelfare P = ∑ i : M, ∑ j : N, P i j * (G.A i j + G.B i j) := by
  rw [socialWelfare]

/-- The symmetric `2 × 2` **Chicken / drivers game** of [Papadimitriou2007], Section 2.7, p. 45
(`0` = Stop, `1` = Go, with payoff matrix `!![4, 1; 5, 0]`). In contrast to the `(-100, 1, 0)`
variant of [TardosVazirani2007], Example 1.10, p. 15 (where mutual stopping pays `(0, 0)` so pure
equilibria already attain the maximum outcome sum `1`), mutual stopping `(0, 0)` here pays `(4, 4)`
with sum `8`, strictly higher than `(Stop, Go)` and `(Go, Stop)` (sum `6`). -/
def chickenGame : BimatrixGame (Fin 2) (Fin 2) :=
  ofSymmetric !![4, 1; 5, 0]

@[simp]
theorem chickenGame_A : chickenGame.A = !![(4 : ℝ), 1; 5, 0] := by
  simp only [chickenGame, ofSymmetric_A]

@[simp]
theorem chickenGame_B : chickenGame.B = (!![(4 : ℝ), 1; 5, 0])ᵀ := by
  simp only [chickenGame, ofSymmetric_B]

theorem chickenGame_isSymmetric : chickenGame.IsSymmetric :=
  isSymmetric_ofSymmetric _

private theorem chickenGame_mulVec_zero {y : Fin 2 → ℝ} (hy : y 0 + y 1 = 1) :
    (chickenGame.A *ᵥ y) 0 = 3 * y 0 + 1 := by
  have heval : (chickenGame.A *ᵥ y) 0 = 4 * y 0 + 1 * y 1 := by
    simp [chickenGame_A, mulVec, dotProduct, Fin.sum_univ_two]
  linarith

private theorem chickenGame_mulVec_one (y : Fin 2 → ℝ) :
    (chickenGame.A *ᵥ y) 1 = 5 * y 0 := by
  simp [chickenGame_A, mulVec, dotProduct, Fin.sum_univ_two]

private theorem chickenGame_ncard_pureBestResponse₁_le {y : Fin 2 → ℝ} (hy : IsMixedStrategy y) :
    {i | chickenGame.IsPureBestResponse₁ y i}.ncard ≤ (Function.support y).ncard := by
  have hsum : y 0 + y 1 = 1 := by simpa only [Fin.sum_univ_two] using hy.sum_eq_one
  have hr₀ := chickenGame_mulVec_zero hsum
  have hr₁ := chickenGame_mulVec_one y
  by_cases hhalf : y 0 = 1 / 2
  · have hsupp_univ : Function.support y = Set.univ := by
      ext i
      fin_cases i <;>
        simp only [Fin.zero_eta, Fin.mk_one, Function.mem_support, Set.mem_univ, iff_true] <;>
        linarith
    rw [hsupp_univ]
    exact Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  · obtain ⟨j₀, hj₀⟩ := hy.exists_pos
    have hsupp_ge : 1 ≤ (Function.support y).ncard :=
      Set.ncard_singleton j₀ ▸
        Set.ncard_le_ncard (Set.singleton_subset_iff.2 hj₀.ne') (Set.toFinite _)
    rcases lt_or_gt_of_ne hhalf with hlt | hgt
    · refine ((Set.ncard_le_ncard (t := {0}) (fun i hi => ?_) (Set.toFinite _)).trans_eq
        (Set.ncard_singleton 0)).trans hsupp_ge
      rw [Set.mem_ofPred_eq, isPureBestResponse₁_iff] at hi
      fin_cases i
      · exact Set.mem_singleton 0
      · exfalso
        have h01 : (chickenGame.A *ᵥ y) 0 ≤ (chickenGame.A *ᵥ y) 1 := hi 0
        linarith
    · refine ((Set.ncard_le_ncard (t := {1}) (fun i hi => ?_) (Set.toFinite _)).trans_eq
        (Set.ncard_singleton 1)).trans hsupp_ge
      rw [Set.mem_ofPred_eq, isPureBestResponse₁_iff] at hi
      fin_cases i
      · exfalso
        have h10 : (chickenGame.A *ᵥ y) 1 ≤ (chickenGame.A *ᵥ y) 0 := hi 1
        linarith
      · exact Set.mem_singleton 1

/-- The `2 × 2` Chicken game is nondegenerate. -/
theorem chickenGame_isNondegenerate : chickenGame.IsNondegenerate := by
  refine isNondegenerate_iff.2
    ⟨fun x hx => ?_, fun _ hy => chickenGame_ncard_pureBestResponse₁_le hy⟩
  have hswap : {j | chickenGame.IsPureBestResponse₂ x j} =
      {j | chickenGame.IsPureBestResponse₁ x j} := by
    ext j
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, ← isPureBestResponse₁_swap,
      chickenGame_isSymmetric.swap_eq]
  rw [hswap]
  exact chickenGame_ncard_pureBestResponse₁_le hx

private theorem fin2_eq_pair (v : Fin 2 → ℝ) : v = ![v 0, v 1] :=
  funext fun i => by fin_cases i <;> rfl

/-- **Complete classification of the Nash equilibria of Chicken** ([Papadimitriou2007], Section 2.7,
p. 46): `chickenGame` has exactly three Nash equilibria — the two asymmetric pure equilibria
`(![0, 1], ![1, 0])` and `(![1, 0], ![0, 1])` and the symmetric mixed equilibrium
`(![1 / 2, 1 / 2], ![1 / 2, 1 / 2])`. -/
theorem chickenGame_isNash_iff {x y : Fin 2 → ℝ} :
    chickenGame.IsNash x y ↔
      (x = ![0, 1] ∧ y = ![1, 0]) ∨
      (x = ![1, 0] ∧ y = ![0, 1]) ∨
      (x = ![1 / 2, 1 / 2] ∧ y = ![1 / 2, 1 / 2]) := by
  constructor
  · intro h
    obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
    have h₂' := (chickenGame_isSymmetric.isBestResponse₂_iff_isBestResponse₁).1 h₂
    have hx_sum : x 0 + x 1 = 1 := by
      simpa only [Fin.sum_univ_two] using h₁.isMixedStrategy.sum_eq_one
    have hy_sum : y 0 + y 1 = 1 := by
      simpa only [Fin.sum_univ_two] using h₂.isMixedStrategy.sum_eq_one
    have hy_r₀ := chickenGame_mulVec_zero hy_sum
    have hy_r₁ := chickenGame_mulVec_one y
    have hx_r₀ := chickenGame_mulVec_zero hx_sum
    have hx_r₁ := chickenGame_mulVec_one x
    have hzero_of_lt : ∀ {u v : Fin 2 → ℝ}, chickenGame.IsBestResponse₁ u v →
        ∀ (i i' : Fin 2), (chickenGame.A *ᵥ v) i < (chickenGame.A *ᵥ v) i' → u i = 0 :=
      fun huv i i' hlt => by_contra fun hne => not_le_of_gt hlt <| isPureBestResponse₁_iff.1
        ((isBestResponse₁_iff.1 huv).2 i ((huv.isMixedStrategy.nonneg i).lt_of_ne' hne)) i'
    rcases lt_trichotomy (y 0) (1 / 2) with hylt | hyeq | hygt
    · have hx1 : x 1 = 0 := hzero_of_lt h₁ 1 0 (by linarith)
      have hy0 : y 0 = 0 := hzero_of_lt h₂' 0 1 (by linarith)
      exact Or.inr <| Or.inl ⟨by rw [fin2_eq_pair x, hx1, show x 0 = 1 by linarith],
        by rw [fin2_eq_pair y, hy0, show y 1 = 1 by linarith]⟩
    · have hbr0 := isPureBestResponse₁_iff.1 ((isBestResponse₁_iff.1 h₂').2 0 (by linarith)) 1
      have hbr1 := isPureBestResponse₁_iff.1 ((isBestResponse₁_iff.1 h₂').2 1 (by linarith)) 0
      exact Or.inr <| Or.inr
        ⟨by rw [fin2_eq_pair x, show x 0 = 1 / 2 by linarith, show x 1 = 1 / 2 by linarith],
        by rw [fin2_eq_pair y, hyeq, show y 1 = 1 / 2 by linarith]⟩
    · have hx0 : x 0 = 0 := hzero_of_lt h₁ 0 1 (by linarith)
      have hy1 : y 1 = 0 := hzero_of_lt h₂' 1 0 (by linarith)
      exact Or.inl ⟨by rw [fin2_eq_pair x, hx0, show x 1 = 1 by linarith],
        by rw [fin2_eq_pair y, show y 0 = 1 by linarith, hy1]⟩
  · have hcheck : ∀ a b c d : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → 0 ≤ c → 0 ≤ d → c + d = 1 →
        (∀ i : Fin 2, 0 < (![a, b] : Fin 2 → ℝ) i →
          ∀ i' : Fin 2, (chickenGame.A *ᵥ ![c, d]) i' ≤ (chickenGame.A *ᵥ ![c, d]) i) →
        (∀ j : Fin 2, 0 < (![c, d] : Fin 2 → ℝ) j →
          ∀ j' : Fin 2, (chickenGame.A *ᵥ ![a, b]) j' ≤ (chickenGame.A *ᵥ ![a, b]) j) →
        chickenGame.IsNash ![a, b] ![c, d] := fun a b c d ha hb hab hc hd hcd h1 h2 =>
      isNash_iff.2
        ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_iff.2 ⟨fun i => by fin_cases i <;> assumption,
            by simp [Fin.sum_univ_two, hab]⟩, fun i hi => isPureBestResponse₁_iff.2 (h1 i hi)⟩,
        (chickenGame_isSymmetric.isBestResponse₂_iff_isBestResponse₁).2
          (isBestResponse₁_iff.2 ⟨isMixedStrategy_iff.2 ⟨fun j => by fin_cases j <;> assumption,
            by simp [Fin.sum_univ_two, hcd]⟩, fun j hj => isPureBestResponse₁_iff.2 (h2 j hj)⟩)⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · refine hcheck 0 1 1 0 le_rfl zero_le_one (by norm_num) zero_le_one le_rfl (by norm_num)
        (fun i hi i' => ?_) (fun j hj j' => ?_)
      · revert hi
        fin_cases i <;> fin_cases i' <;>
          norm_num [chickenGame, mulVec, dotProduct, Fin.sum_univ_two]
      · revert hj
        fin_cases j <;> fin_cases j' <;>
          norm_num [chickenGame, mulVec, dotProduct, Fin.sum_univ_two]
    · refine hcheck 1 0 0 1 zero_le_one le_rfl (by norm_num) le_rfl zero_le_one (by norm_num)
        (fun i hi i' => ?_) (fun j hj j' => ?_)
      · revert hi
        fin_cases i <;> fin_cases i' <;>
          norm_num [chickenGame, mulVec, dotProduct, Fin.sum_univ_two]
      · revert hj
        fin_cases j <;> fin_cases j' <;>
          norm_num [chickenGame, mulVec, dotProduct, Fin.sum_univ_two]
    · refine hcheck (1 / 2) (1 / 2) (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (fun i _ i' => ?_) (fun i _ i' => ?_) <;>
        (fin_cases i <;> fin_cases i' <;>
          norm_num [chickenGame, mulVec, dotProduct, Fin.sum_univ_two])

/-- The 50–50 traffic-signal correlated equilibrium `C₁ = !![0, 1 / 2; 1 / 2, 0]` of
[Papadimitriou2007], Section 2.7, pp. 46–47 (cf. [TardosVazirani2007], Example 1.10, p. 15). -/
noncomputable def chickenTrafficLight : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1 / 2; 1 / 2, 0]

theorem chickenTrafficLight_mem_correlatedPolytope :
    chickenTrafficLight ∈ chickenGame.correlatedPolytope := by
  refine mem_correlatedPolytope_iff.2 ⟨fun i j => ?_, ?_, fun i i' => ?_, fun j j' => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [chickenTrafficLight]
  · norm_num [chickenTrafficLight, Fin.sum_univ_two]
  · fin_cases i <;> fin_cases i' <;> norm_num [chickenTrafficLight, chickenGame, Fin.sum_univ_two]
  · fin_cases j <;> fin_cases j' <;> norm_num [chickenTrafficLight, chickenGame, Fin.sum_univ_two]

/-- `C₁ = !![0, 1 / 2; 1 / 2, 0]` has rank `2`, so it is not of the form `Matrix.vecMulVec x y`
for any `x, y : Fin 2 → ℝ` ([Papadimitriou2007], Section 2.7, p. 46). -/
theorem chickenTrafficLight_ne_vecMulVec (x y : Fin 2 → ℝ) :
    Matrix.vecMulVec x y ≠ chickenTrafficLight := by
  intro h
  have h00 : x 0 * y 0 = 0 := by
    simpa [vecMulVec_apply, chickenTrafficLight] using congrFun (congrFun h 0) 0
  have h01 : x 0 * y 1 = 1 / 2 := by
    simpa [vecMulVec_apply, chickenTrafficLight] using congrFun (congrFun h 0) 1
  have h10 : x 1 * y 0 = 1 / 2 := by
    simpa [vecMulVec_apply, chickenTrafficLight] using congrFun (congrFun h 1) 0
  rcases mul_eq_zero.1 h00 with hx0 | hy0
  · rw [hx0, zero_mul] at h01; norm_num at h01
  · rw [hy0, mul_zero] at h10; norm_num at h10

/-- The social-welfare-optimal correlated equilibrium `C₂ = !![1 / 3, 1 / 3; 1 / 3, 0]` of
[Papadimitriou2007], Section 2.7, p. 47 ("a traffic light that is red for both one third of the
time"). -/
noncomputable def chickenOptimalCorrelated : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 / 3, 1 / 3; 1 / 3, 0]

theorem chickenOptimalCorrelated_mem_correlatedPolytope :
    chickenOptimalCorrelated ∈ chickenGame.correlatedPolytope := by
  refine mem_correlatedPolytope_iff.2 ⟨fun i j => ?_, ?_, fun i i' => ?_, fun j j' => ?_⟩
  · fin_cases i <;> fin_cases j <;> norm_num [chickenOptimalCorrelated]
  · norm_num [chickenOptimalCorrelated, Fin.sum_univ_two]
  · fin_cases i <;> fin_cases i' <;>
      norm_num [chickenOptimalCorrelated, chickenGame, Fin.sum_univ_two]
  · fin_cases j <;> fin_cases j' <;>
      norm_num [chickenOptimalCorrelated, chickenGame, Fin.sum_univ_two]

theorem chickenGame_socialWelfare_optimalCorrelated :
    chickenGame.socialWelfare chickenOptimalCorrelated = 20 / 3 := by
  norm_num [socialWelfare, chickenOptimalCorrelated, chickenGame, Fin.sum_univ_two]

/-- Over all correlated equilibria of `chickenGame`, `20 / 3` is the maximum social welfare
([Papadimitriou2007], Section 2.7, p. 47). -/
theorem chickenGame_socialWelfare_le_of_correlated {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : P ∈ chickenGame.correlatedPolytope) :
    chickenGame.socialWelfare P ≤ 20 / 3 := by
  have hcorr := mem_correlatedPolytope_iff.1 hP
  have hnn11 : 0 ≤ P 1 1 := hcorr.nonneg 1 1
  have hsum : (P 0 0 + P 0 1) + (P 1 0 + P 1 1) = 1 := by
    simpa [Fin.sum_univ_two] using hcorr.sum_eq_one
  have hrow01 : P 0 0 * 5 + P 0 1 * 0 ≤ P 0 0 * 4 + P 0 1 * 1 := by
    simpa [Fin.sum_univ_two, chickenGame_A] using hcorr.row_le 0 1
  have hcol01 : P 0 0 * 5 + P 1 0 * 0 ≤ P 0 0 * 4 + P 1 0 * 1 := by
    simpa [Fin.sum_univ_two, chickenGame_B] using hcorr.col_le 0 1
  have hsw : chickenGame.socialWelfare P =
      (P 0 0 * (4 + 4) + P 0 1 * (1 + 5)) + (P 1 0 * (5 + 1) + P 1 1 * (0 + 0)) := by
    simp [socialWelfare, Fin.sum_univ_two, chickenGame_A, chickenGame_B]
  linarith

/-- Every point in the convex hull of Nash equilibrium product distributions of `chickenGame` has
expected social welfare at most `6`. -/
theorem chickenGame_socialWelfare_le_six_of_mem_convexHull_isNash {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : P ∈ convexHull ℝ {Q | ∃ x y, chickenGame.IsNash x y ∧ Matrix.vecMulVec x y = Q}) :
    chickenGame.socialWelfare P ≤ 6 := by
  have hconv : Convex ℝ {Q : Matrix (Fin 2) (Fin 2) ℝ | chickenGame.socialWelfare Q ≤ 6} := by
    rintro Q₁ h₁ Q₂ h₂ a b ha hb hab
    rw [Set.mem_ofPred_eq] at h₁ h₂ ⊢
    have hlin : chickenGame.socialWelfare (a • Q₁ + b • Q₂) =
        a * chickenGame.socialWelfare Q₁ + b * chickenGame.socialWelfare Q₂ := by
      simp only [socialWelfare, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul,
        mul_assoc, sum_add_distrib, ← mul_sum]
    linarith [mul_le_mul_of_nonneg_left h₁ ha, mul_le_mul_of_nonneg_left h₂ hb,
      show a * 6 + b * 6 = (6 : ℝ) by rw [← add_mul, hab, one_mul]]
  refine convexHull_min (fun Q hQ => ?_) hconv hP
  rcases hQ with ⟨x, y, hNash, rfl⟩
  rw [Set.mem_ofPred_eq]
  rcases chickenGame_isNash_iff.1 hNash with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    norm_num [socialWelfare, vecMulVec_apply, chickenGame, Fin.sum_univ_two]

/-- **Strict separation `CE \ conv(NE)`**: `chickenOptimalCorrelated` lies in
`chickenGame.correlatedPolytope` and strictly outside the convex hull of Nash equilibrium product
distributions ([Papadimitriou2007], Section 2.7.1, Figure 2.4, pp. 47–48). -/
theorem chickenOptimalCorrelated_mem_sdiff_convexHull_isNash :
    chickenOptimalCorrelated ∈ chickenGame.correlatedPolytope \
      convexHull ℝ {Q | ∃ x y, chickenGame.IsNash x y ∧ Matrix.vecMulVec x y = Q} := by
  refine ⟨chickenOptimalCorrelated_mem_correlatedPolytope, fun hmem => ?_⟩
  have hle := chickenGame_socialWelfare_le_six_of_mem_convexHull_isNash hmem
  rw [chickenGame_socialWelfare_optimalCorrelated] at hle
  norm_num at hle

/-- The social welfare of `chickenOptimalCorrelated` (`20 / 3`) strictly exceeds that of every
convex combination of Nash equilibrium product distributions (`≤ 6`). -/
theorem chickenOptimalCorrelated_socialWelfare_gt_convexHull_isNash {P : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : P ∈ convexHull ℝ {Q | ∃ x y, chickenGame.IsNash x y ∧ Matrix.vecMulVec x y = Q}) :
    chickenGame.socialWelfare P < chickenGame.socialWelfare chickenOptimalCorrelated := by
  have hle := chickenGame_socialWelfare_le_six_of_mem_convexHull_isNash hP
  rw [chickenGame_socialWelfare_optimalCorrelated]
  linarith

end ChickenSeparation

end Cslib.GameTheory.BimatrixGame
