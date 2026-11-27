/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import CslibFrontier.GameTheory.Strategic.Symmetric
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Symmetric bimatrix games and equilibrium correspondence for symmetrization

A two-player bimatrix game `G : BimatrixGame M M` with shared strategy set `M` is **symmetric**
(`BimatrixGame.IsSymmetric`) if `G.B = G.Aᵀ` ([Papadimitriou2007], Example 2.2, p. 30): swapping
the roles of the two players leaves all payoffs unchanged. A mixed strategy `x : M → ℝ` is a
**symmetric Nash equilibrium** (`BimatrixGame.IsSymmetricNash`) if `(x, x)` is a Nash equilibrium,
equivalently if `x` is a best response of player 1 to `x`.

This module establishes:

* **Symmetry bridge and symmetric Nash equilibrium existence for bimatrix games**
  ([Papadimitriou2007], Example 2.2, pp. 30–31, and Section 2.3.1, p. 34; player-interchangeable
  specialization of [Nash1951], Theorem 2): `toSymmCostGame` embeds `BimatrixGame M M` into
  `CostGame Bool (fun _ => M)` preserving symmetry and symmetric Nash equilibria, so
  `CostGame.IsSymmetric.exists_isSymmetricMixedNash` immediately yields
  `BimatrixGame.IsSymmetric.exists_isSymmetricNash`.
* **Algebraic equilibrium-correspondence step of [Papadimitriou2007], Theorem 2.4** (Section 2.3.1,
  p. 34; the polynomial-time search reduction on `BimatrixCode` remains open in #7789): for any
  positive bimatrix game `G = (A, B)` on `M × N`, the two-block symmetric game
  `symmReduction G = ofSymmetric [[0, A], [Bᵀ, 0]]` on `M ⊕ N` has the property that every
  symmetric Nash equilibrium `z` assigns strictly positive mass to both `M` and `N` and its
  normalized block projections `(symmProj₁ z, symmProj₂ z)` form a Nash equilibrium of `G`;
  conversely, every Nash equilibrium `(x, y)` of `G` lifts to a symmetric Nash equilibrium of
  `symmReduction G` (`exists_addConst_symmReduction` shifts arbitrary-sign finite games first).

## Main definitions

* `Cslib.GameTheory.BimatrixGame.IsSymmetric`: `G.B = G.Aᵀ`.
* `Cslib.GameTheory.BimatrixGame.ofSymmetric`: the symmetric bimatrix game `⟨A, Aᵀ⟩`.
* `Cslib.GameTheory.BimatrixGame.IsSymmetricNash`: `G.IsNash x x`.
* `Cslib.GameTheory.BimatrixGame.toSymmCostGame`: symmetric-type embedding into
  `CostGame Bool (fun _ => M)`.
* `Cslib.GameTheory.BimatrixGame.symmReduction`, `symmProj₁`, `symmProj₂`: the two-block symmetric
  game on `M ⊕ N` and its normalized block projections used in the proof of [Papadimitriou2007],
  Theorem 2.4.

## Main results

* `Cslib.GameTheory.BimatrixGame.IsSymmetric.exists_isSymmetricNash`: every finite nonempty
  symmetric bimatrix game has a symmetric Nash equilibrium.
* `Cslib.GameTheory.BimatrixGame.symmReduction_pos_and_isNash`,
  `Cslib.GameTheory.BimatrixGame.isSymmetricNash_symmReduction_of_isNash`,
  `Cslib.GameTheory.BimatrixGame.exists_addConst_symmReduction`: the algebraic equilibrium
  correspondence over `ℝ` behind [Papadimitriou2007], Theorem 2.4 (including the constant-shift
  form for arbitrary-sign finite bimatrix games; the polynomial-time reduction remains open in
  #7789).

## References

* [C. H. Papadimitriou, *The Complexity of Finding Nash Equilibria*][Papadimitriou2007]
* [J. Nash, *Non-Cooperative Games*][Nash1951]
* [N. Nisan, T. Roughgarden, É. Tardos, and V. V. Vazirani (eds.),
  *Algorithmic Game Theory*][NisanRoughgardenTardosVazirani2007]
-/

public section

namespace Cslib.GameTheory.BimatrixGame

open Finset Function Matrix

/-! ### Symmetric two-player bimatrix games -/

section SymmetricBimatrix

variable {M : Type*}

/-- A bimatrix game `G : BimatrixGame M M` on a common strategy set `M` is **symmetric**
([Papadimitriou2007], Example 2.2, p. 30) if `G.B = G.Aᵀ`. -/
@[expose] def IsSymmetric (G : BimatrixGame M M) : Prop :=
  G.B = G.Aᵀ

/-- The symmetric bimatrix game `⟨A, Aᵀ⟩` determined by player 1's payoff matrix `A`. -/
def ofSymmetric (A : Matrix M M ℝ) : BimatrixGame M M :=
  ⟨A, Aᵀ⟩

@[simp]
theorem ofSymmetric_A (A : Matrix M M ℝ) : (ofSymmetric A).A = A := by rfl

@[simp]
theorem ofSymmetric_B (A : Matrix M M ℝ) : (ofSymmetric A).B = Aᵀ := by rfl

theorem isSymmetric_ofSymmetric (A : Matrix M M ℝ) : (ofSymmetric A).IsSymmetric := by rfl

theorem IsSymmetric.swap_eq {G : BimatrixGame M M} (hG : G.IsSymmetric) : G.swap = G := by
  rcases G with ⟨A, B⟩
  obtain rfl : B = Aᵀ := hG
  simp [swap_mk]

/-- Embedding of `G : BimatrixGame M M` as a two-player `CostGame Bool (fun _ => M)` on the shared
strategy type `M`, where `false` is the row player and `true` is the column player. -/
def toSymmCostGame (G : BimatrixGame M M) : CostGame Bool (fun _ => M) where
  cost
    | false => fun s => -G.A (s false) (s true)
    | true => fun s => -G.B (s false) (s true)

@[simp]
theorem toSymmCostGame_cost_false (G : BimatrixGame M M) (s : Bool → M) :
    G.toSymmCostGame.cost false s = -G.A (s false) (s true) := by rfl

@[simp]
theorem toSymmCostGame_cost_true (G : BimatrixGame M M) (s : Bool → M) :
    G.toSymmCostGame.cost true s = -G.B (s false) (s true) := by rfl

/-- `G.toSymmCostGame` is symmetric in the `CostGame` sense iff `G` is symmetric (`G.B = G.Aᵀ`). -/
theorem isSymmetric_toSymmCostGame_iff {G : BimatrixGame M M} :
    G.toSymmCostGame.IsSymmetric ↔ G.IsSymmetric := by
  constructor
  · intro h
    ext i j
    simpa [toSymmCostGame] using (h (Equiv.swap false true) (fun b => cond b j i) false).symm
  · intro (hG : G.B = G.Aᵀ) π s b
    cases b <;> cases hf : π false <;> cases ht : π true <;>
      first
      | exact absurd (π.injective (hf.trans ht.symm)) (by decide)
      | simp only [toSymmCostGame_cost_false, toSymmCostGame_cost_true, Function.comp_apply, hf,
          ht, hG, transpose_apply]

section FintypeSymmetric

variable [Fintype M] {G : BimatrixGame M M}

/-- `x : M → ℝ` is a **symmetric Nash equilibrium** of `G` ([Papadimitriou2007], Example 2.2,
p. 30) if `(x, x)` is a Nash equilibrium of `G`. -/
@[expose] def IsSymmetricNash (G : BimatrixGame M M) (x : M → ℝ) : Prop :=
  G.IsNash x x

theorem IsSymmetric.payoff₂_eq (hG : G.IsSymmetric) (x y : M → ℝ) :
    G.payoff₂ x y = G.payoff₁ y x := by
  rw [← payoff₁_swap, hG.swap_eq]

theorem IsSymmetric.isBestResponse₂_iff_isBestResponse₁ (hG : G.IsSymmetric) {x y : M → ℝ} :
    G.IsBestResponse₂ y x ↔ G.IsBestResponse₁ y x := by
  rw [← isBestResponse₁_swap, hG.swap_eq]

theorem IsSymmetric.isNash_comm (hG : G.IsSymmetric) {x y : M → ℝ} :
    G.IsNash x y ↔ G.IsNash y x := by
  rw [← isNash_swap, hG.swap_eq]

theorem IsSymmetric.isSymmetricNash_iff_isBestResponse₁ (hG : G.IsSymmetric) {x : M → ℝ} :
    G.IsSymmetricNash x ↔ G.IsBestResponse₁ x x := by
  rw [IsSymmetricNash, isNash_iff, hG.isBestResponse₂_iff_isBestResponse₁, and_self]

/-- Pure-row characterization of `IsSymmetricNash` in a symmetric bimatrix game. -/
theorem IsSymmetric.isSymmetricNash_iff (hG : G.IsSymmetric) {x : M → ℝ} :
    G.IsSymmetricNash x ↔ IsMixedStrategy x ∧ ∀ i : M, (G.A *ᵥ x) i ≤ G.payoff₁ x x := by
  rw [hG.isSymmetricNash_iff_isBestResponse₁, isBestResponse₁_iff_le_payoff₁]

/-- Support characterization of `IsSymmetricNash` in a symmetric bimatrix game: every strategy in
the support of `x` is a pure best response to `x`. -/
theorem IsSymmetric.isSymmetricNash_iff_pureBestResponse (hG : G.IsSymmetric) {x : M → ℝ} :
    G.IsSymmetricNash x ↔ IsMixedStrategy x ∧ ∀ i : M, 0 < x i → G.IsPureBestResponse₁ x i := by
  rw [hG.isSymmetricNash_iff_isBestResponse₁, isBestResponse₁_iff]

private def boolPairEquiv (α : Type*) : (Bool → α) ≃ α × α where
  toFun s := (s false, s true)
  invFun p b := cond b p.2 p.1
  left_inv s := by
    funext b
    cases b <;> rfl
  right_inv p := by
    ext <;> rfl

private theorem deviationCost_toSymmCostGame_false {x : M → ℝ} (hx : ∑ i : M, x i = 1) (i : M) :
    G.toSymmCostGame.deviationCost (fun _ => x) false i = -(G.A *ᵥ x) i := by
  have hterm (a b : M) : productWeight (fun _ : Bool => x) ((boolPairEquiv M).symm (a, b)) *
      G.toSymmCostGame.cost false (update ((boolPairEquiv M).symm (a, b)) false i) =
      x a * -(G.A i b * x b) := by
    simp only [productWeight_def, Fintype.prod_bool, boolPairEquiv, Equiv.coe_fn_symm_mk,
      toSymmCostGame, update_self, ne_eq, Bool.true_eq_false, not_false_eq_true, update_of_ne,
      Bool.cond_true, Bool.cond_false]
    ring
  rw [CostGame.deviationCost_def, ← (boolPairEquiv M).symm.sum_comp, Fintype.sum_prod_type]
  simp only [hterm, mul_neg, sum_neg_distrib, ← mul_sum, ← sum_mul, hx, one_mul, mulVec, dotProduct]

private theorem expectedCost_toSymmCostGame_false {x : M → ℝ} (hx : ∑ i : M, x i = 1) :
    G.toSymmCostGame.expectedCost (fun _ => x) false = -G.payoff₁ x x := by
  rw [← G.toSymmCostGame.sum_mul_deviationCost_eq_expectedCost (fun _ => x) hx,
    payoff₁_eq_dotProduct]
  simp only [deviationCost_toSymmCostGame_false hx, mul_neg, Finset.sum_neg_distrib, dotProduct]

/-- In a symmetric bimatrix game, `x` is a symmetric Nash equilibrium iff `x` is a symmetric mixed
Nash equilibrium of `G.toSymmCostGame`. -/
theorem IsSymmetric.isSymmetricNash_iff_isSymmetricMixedNash (hG : G.IsSymmetric) {x : M → ℝ} :
    G.IsSymmetricNash x ↔ G.toSymmCostGame.IsSymmetricMixedNash x := by
  rw [hG.isSymmetricNash_iff,
    (isSymmetric_toSymmCostGame_iff.2 hG).isSymmetricMixedNash_iff_at false]
  refine and_congr_right fun hx => forall_congr' fun i => ?_
  rw [expectedCost_toSymmCostGame_false hx.sum_eq_one,
    deviationCost_toSymmCostGame_false hx.sum_eq_one i, neg_le_neg_iff]

/-- **Symmetric Nash equilibrium existence for bimatrix games** ([Papadimitriou2007], Example 2.2,
pp. 30–31, and Section 2.3.1, p. 34; two-player specialization of [Nash1951], Theorem 2): every
finite nonempty symmetric bimatrix game has a symmetric Nash equilibrium. -/
theorem IsSymmetric.exists_isSymmetricNash [Nonempty M] (hG : G.IsSymmetric) :
    ∃ x : M → ℝ, G.IsSymmetricNash x := by
  obtain ⟨x, hx⟩ := (isSymmetric_toSymmCostGame_iff.2 hG).exists_isSymmetricMixedNash
  exact ⟨x, hG.isSymmetricNash_iff_isSymmetricMixedNash.2 hx⟩

end FintypeSymmetric

end SymmetricBimatrix

/-! ### Algebraic equilibrium-correspondence step of [Papadimitriou2007], Theorem 2.4 -/

section TwoBlockReduction

variable {M N : Type*}

/-- Player 1's payoff matrix `[[0, A], [Bᵀ, 0]]` on `M ⊕ N` for the two-block symmetrization in
the proof of [Papadimitriou2007], Theorem 2.4, p. 34. -/
private def symmReductionMatrix (G : BimatrixGame M N) : Matrix (M ⊕ N) (M ⊕ N) ℝ :=
  Matrix.fromBlocks 0 G.A G.Bᵀ 0

/-- The symmetric two-player game `ofSymmetric [[0, A], [Bᵀ, 0]]` on `M ⊕ N` associated to a
bimatrix game `G` in the proof of [Papadimitriou2007], Theorem 2.4, p. 34. -/
def symmReduction (G : BimatrixGame M N) : BimatrixGame (M ⊕ N) (M ⊕ N) :=
  ofSymmetric G.symmReductionMatrix

theorem isSymmetric_symmReduction (G : BimatrixGame M N) : G.symmReduction.IsSymmetric := by rfl

@[simp]
theorem symmReduction_B (G : BimatrixGame M N) : G.symmReduction.B = G.symmReduction.Aᵀ := by rfl

@[simp]
theorem symmReduction_A_inl_inl (G : BimatrixGame M N) (i i' : M) :
    G.symmReduction.A (.inl i) (.inl i') = 0 := by rfl

@[simp]
theorem symmReduction_A_inl_inr (G : BimatrixGame M N) (i : M) (j : N) :
    G.symmReduction.A (.inl i) (.inr j) = G.A i j := by rfl

@[simp]
theorem symmReduction_A_inr_inl (G : BimatrixGame M N) (j : N) (i : M) :
    G.symmReduction.A (.inr j) (.inl i) = G.B i j := by rfl

@[simp]
theorem symmReduction_A_inr_inr (G : BimatrixGame M N) (j j' : N) :
    G.symmReduction.A (.inr j) (.inr j') = 0 := by rfl

section FintypeTwoBlock

variable [Fintype M] [Fintype N]

/-- Normalized `M`-block projection of `z : M ⊕ N → ℝ`. -/
noncomputable def symmProj₁ (z : M ⊕ N → ℝ) : M → ℝ :=
  (∑ i : M, z (.inl i))⁻¹ • fun i => z (.inl i)

/-- Normalized `N`-block projection of `z : M ⊕ N → ℝ`. -/
noncomputable def symmProj₂ (z : M ⊕ N → ℝ) : N → ℝ :=
  (∑ j : N, z (.inr j))⁻¹ • fun j => z (.inr j)

omit [Fintype N] in
@[simp]
theorem symmProj₁_apply (z : M ⊕ N → ℝ) (i : M) :
    symmProj₁ z i = (∑ i' : M, z (.inl i'))⁻¹ * z (.inl i) := by rfl

omit [Fintype M] in
@[simp]
theorem symmProj₂_apply (z : M ⊕ N → ℝ) (j : N) :
    symmProj₂ z j = (∑ j' : N, z (.inr j'))⁻¹ * z (.inr j) := by rfl

private theorem mulVec_symmReductionMatrix_inl (G : BimatrixGame M N) (z : M ⊕ N → ℝ) (i : M) :
    (G.symmReductionMatrix *ᵥ z) (.inl i) = (G.A *ᵥ fun j => z (.inr j)) i := by
  change ∑ k : M ⊕ N, G.symmReductionMatrix (.inl i) k * z k = ∑ j : N, G.A i j * z (.inr j)
  rw [Fintype.sum_sum_type]
  simp only [symmReductionMatrix, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.zero_apply,
    zero_mul, sum_const_zero, zero_add]

private theorem mulVec_symmReductionMatrix_inr (G : BimatrixGame M N) (z : M ⊕ N → ℝ) (j : N) :
    (G.symmReductionMatrix *ᵥ z) (.inr j) = ((fun i => z (.inl i)) ᵥ* G.B) j := by
  change ∑ k : M ⊕ N, G.symmReductionMatrix (.inr j) k * z k = ∑ i : M, z (.inl i) * G.B i j
  rw [Fintype.sum_sum_type]
  simp only [symmReductionMatrix, fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_apply,
    Matrix.zero_apply, zero_mul, sum_const_zero, add_zero]
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- Normalizing positive nonnegative vectors `(x, y)` that satisfy the unscaled best-response
support conditions yields a Nash equilibrium `(sx⁻¹ • x, sy⁻¹ • y)`. -/
private theorem isNash_inv_sum_smul {M N : Type*} [Fintype M] [Fintype N] {G : BimatrixGame M N}
    {x : M → ℝ} {y : N → ℝ}
    (hx_nn : ∀ i, 0 ≤ x i) (hsx_pos : 0 < ∑ i : M, x i)
    (hy_nn : ∀ j, 0 ≤ y j) (hsy_pos : 0 < ∑ j : N, y j)
    (hopt₁ : ∀ i : M, 0 < x i → ∀ i' : M, (G.A *ᵥ y) i' ≤ (G.A *ᵥ y) i)
    (hopt₂ : ∀ j : N, 0 < y j → ∀ j' : N, (x ᵥ* G.B) j' ≤ (x ᵥ* G.B) j) :
    G.IsNash ((∑ i : M, x i)⁻¹ • x) ((∑ j : N, y j)⁻¹ • y) := by
  have hx_ne : x ≠ 0 := fun h0 => hsx_pos.ne' (by simp [h0])
  have hy_ne : y ≠ 0 := fun h0 => hsy_pos.ne' (by simp [h0])
  refine isNash_iff.2
    ⟨isBestResponse₁_iff.2 ⟨isMixedStrategy_inv_sum_smul hx_nn hx_ne, fun i hi =>
      isPureBestResponse₁_iff.2 fun i' => ?_⟩,
     isBestResponse₂_iff.2 ⟨isMixedStrategy_inv_sum_smul hy_nn hy_ne, fun j hj =>
      isPureBestResponse₂_iff.2 fun j' => ?_⟩⟩
  · have hxi : 0 < x i := pos_of_mul_pos_right hi (inv_nonneg.2 hsx_pos.le)
    rw [mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hopt₁ i hxi i') (inv_nonneg.2 hsy_pos.le)
  · have hyj : 0 < y j := pos_of_mul_pos_right hj (inv_nonneg.2 hsy_pos.le)
    rw [smul_vecMul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (hopt₂ j hyj j') (inv_nonneg.2 hsx_pos.le)

/-- A step of [Papadimitriou2007], Theorem 2.4 (Section 2.3.1, p. 34; the polynomial-time search
reduction on `BimatrixCode` remains open in #7789): the algebraic equilibrium-recovery direction
over `ℝ`. If `G` has strictly positive payoffs, then at every symmetric Nash equilibrium `z` of
`G.symmReduction`, both blocks `M` and `N` carry strictly positive probability mass, and their
normalized projections `(symmProj₁ z, symmProj₂ z)` form a Nash equilibrium of `G`. -/
theorem symmReduction_pos_and_isNash [Nonempty M] [Nonempty N] {G : BimatrixGame M N}
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) {z : M ⊕ N → ℝ}
    (hz : G.symmReduction.IsSymmetricNash z) :
    0 < ∑ i : M, z (.inl i) ∧ 0 < ∑ j : N, z (.inr j) ∧
      G.IsNash (symmProj₁ z) (symmProj₂ z) := by
  have hbr : G.symmReduction.IsBestResponse₁ z z :=
    (isSymmetric_symmReduction G).isSymmetricNash_iff_isBestResponse₁.1 hz
  have hz_mix : IsMixedStrategy z := hbr.isMixedStrategy
  have hAz : G.symmReduction.A = G.symmReductionMatrix := rfl
  have hsum : ∑ i : M, z (.inl i) + ∑ j : N, z (.inr j) = 1 :=
    Fintype.sum_sum_type z ▸ hz_mix.sum_eq_one
  have hsx_pos : 0 < ∑ i : M, z (.inl i) := by
    refine (sum_nonneg fun i _ => hz_mix.nonneg (.inl i)).lt_of_ne fun hsx0 => ?_
    have hx : (fun i => z (.inl i)) = 0 := funext fun i =>
      (sum_eq_zero_iff_of_nonneg fun i _ => hz_mix.nonneg (.inl i)).1 hsx0.symm i (mem_univ i)
    have hy_mix : IsMixedStrategy fun j => z (.inr j) :=
      isMixedStrategy_iff.2 ⟨fun j => hz_mix.nonneg (.inr j), by linarith⟩
    obtain ⟨j₁, hj₁⟩ := hy_mix.exists_pos
    have hval :=
      (hbr.le_payoff₁ (.inl (Classical.arbitrary M))).trans_eq (hbr.payoff₁_eq_of_pos hj₁)
    rw [hAz, mulVec_symmReductionMatrix_inl, mulVec_symmReductionMatrix_inr, hx, zero_vecMul]
      at hval
    exact not_le_of_gt (by simpa [mulVec, dotProduct_comm] using hy_mix.dotProduct_pos (hA _)) hval
  have hsy_pos : 0 < ∑ j : N, z (.inr j) := by
    refine (sum_nonneg fun j _ => hz_mix.nonneg (.inr j)).lt_of_ne fun hsy0 => ?_
    have hy : (fun j => z (.inr j)) = 0 := funext fun j =>
      (sum_eq_zero_iff_of_nonneg fun j _ => hz_mix.nonneg (.inr j)).1 hsy0.symm j (mem_univ j)
    have hx_mix : IsMixedStrategy fun i => z (.inl i) :=
      isMixedStrategy_iff.2 ⟨fun i => hz_mix.nonneg (.inl i), by linarith⟩
    obtain ⟨i₁, hi₁⟩ := hx_mix.exists_pos
    have hval :=
      (hbr.le_payoff₁ (.inr (Classical.arbitrary N))).trans_eq (hbr.payoff₁_eq_of_pos hi₁)
    rw [hAz, mulVec_symmReductionMatrix_inr, mulVec_symmReductionMatrix_inl, hy, mulVec_zero]
      at hval
    exact absurd hval (not_le.2 (hx_mix.dotProduct_pos fun i => hB i _))
  refine ⟨hsx_pos, hsy_pos, isNash_inv_sum_smul (fun i => hz_mix.nonneg (.inl i)) hsx_pos
    (fun j => hz_mix.nonneg (.inr j)) hsy_pos (fun i hxi i' => ?_) (fun j hyj j' => ?_)⟩
  · have hopt := (hbr.le_payoff₁ (.inl i')).trans_eq (hbr.payoff₁_eq_of_pos hxi)
    rwa [hAz, mulVec_symmReductionMatrix_inl, mulVec_symmReductionMatrix_inl] at hopt
  · have hopt := (hbr.le_payoff₁ (.inr j')).trans_eq (hbr.payoff₁_eq_of_pos hyj)
    rwa [hAz, mulVec_symmReductionMatrix_inr, mulVec_symmReductionMatrix_inr] at hopt

/-- A step of [Papadimitriou2007], Theorem 2.4 (Section 2.3.1, p. 34; the polynomial-time search
reduction on `BimatrixCode` remains open in #7789): the algebraic equilibrium-lifting direction
over `ℝ`. Every Nash equilibrium `(x, y)` of a positive bimatrix game `G` lifts to a symmetric
Nash equilibrium `Sum.elim ((u / (u + v)) • x) ((v / (u + v)) • y)` of `G.symmReduction`, where
`u = G.payoff₁ x y` and `v = G.payoff₂ x y`. -/
theorem isSymmetricNash_symmReduction_of_isNash {G : BimatrixGame M N}
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) {x : M → ℝ} {y : N → ℝ}
    (hNash : G.IsNash x y) :
    G.symmReduction.IsSymmetricNash
      (Sum.elim ((G.payoff₁ x y / (G.payoff₁ x y + G.payoff₂ x y)) • x)
        ((G.payoff₂ x y / (G.payoff₁ x y + G.payoff₂ x y)) • y)) := by
  obtain ⟨hbr₁, hbr₂⟩ := isNash_iff.1 hNash
  have hx := hbr₁.isMixedStrategy
  have hy := hbr₂.isMixedStrategy
  set u : ℝ := G.payoff₁ x y
  set v : ℝ := G.payoff₂ x y
  have huv : 0 < u + v := add_pos (G.payoff₁_pos hA hx hy) (G.payoff₂_pos hB hx hy)
  set α : ℝ := u / (u + v)
  set β : ℝ := v / (u + v)
  have hα : 0 < α := div_pos (G.payoff₁_pos hA hx hy) huv
  have hβ : 0 < β := div_pos (G.payoff₂_pos hB hx hy) huv
  have hαβ : α + β = 1 := by rw [← add_div, div_self huv.ne']
  set z : M ⊕ N → ℝ := Sum.elim (α • x) (β • y)
  have hz_mix : IsMixedStrategy z := isMixedStrategy_iff.2
    ⟨Sum.rec (fun i => mul_nonneg hα.le (hx.nonneg i)) (fun j => mul_nonneg hβ.le (hy.nonneg j)),
      by simp only [Fintype.sum_sum_type, z, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply,
        smul_eq_mul, ← mul_sum, hx.sum_eq_one, hy.sum_eq_one, mul_one, hαβ]⟩
  have hval_inl (i : M) : (G.symmReduction.A *ᵥ z) (.inl i) = β * (G.A *ᵥ y) i :=
    (mulVec_symmReductionMatrix_inl G z i).trans (congrFun (mulVec_smul G.A β y) i)
  have hval_inr (j : N) : (G.symmReduction.A *ᵥ z) (.inr j) = α * (x ᵥ* G.B) j :=
    (mulVec_symmReductionMatrix_inr G z j).trans (congrFun (smul_vecMul α x G.B) j)
  have hcommon : β * u = α * v := by dsimp only [α, β]; ring
  refine ((isSymmetric_symmReduction G).isSymmetricNash_iff_pureBestResponse).2
    ⟨hz_mix, fun k hk => isPureBestResponse₁_iff.2 fun k' => ?_⟩
  have hk_eq : (G.symmReduction.A *ᵥ z) k = β * u := by
    cases k with
    | inl i => rw [hval_inl, ← hbr₁.payoff₁_eq_of_pos (pos_of_mul_pos_right hk hα.le)]
    | inr j => rw [hval_inr, hcommon, ← hbr₂.payoff₂_eq_of_pos (pos_of_mul_pos_right hk hβ.le)]
  rw [hk_eq]
  cases k' with
  | inl i' => rw [hval_inl]; exact mul_le_mul_of_nonneg_left (hbr₁.le_payoff₁ i') hβ.le
  | inr j' => rw [hval_inr, hcommon]; exact mul_le_mul_of_nonneg_left (hbr₂.le_payoff₂ j') hα.le

/-- A step of [Papadimitriou2007], Theorem 2.4 (Section 2.3.1, p. 34; the polynomial-time search
reduction on `BimatrixCode` remains open in #7789): the algebraic constant-shift equilibrium
correspondence over `ℝ` for arbitrary-sign finite nonempty bimatrix games. For any finite nonempty
bimatrix game `G`, there exists a uniform shift `c : ℝ` such that `G' := G.addConst c` has strictly
positive payoffs, every symmetric Nash equilibrium `z` of `G'.symmReduction` puts strictly positive
mass on both blocks and projects to a Nash equilibrium `(symmProj₁ z, symmProj₂ z)` of `G`, and
every Nash equilibrium of `G` lifts to a symmetric Nash equilibrium of `G'.symmReduction`. -/
theorem exists_addConst_symmReduction [Nonempty M] [Nonempty N] (G : BimatrixGame M N) :
    ∃ c : ℝ,
      (∀ z : M ⊕ N → ℝ, (G.addConst c).symmReduction.IsSymmetricNash z →
        0 < ∑ i : M, z (.inl i) ∧ 0 < ∑ j : N, z (.inr j) ∧
          G.IsNash (symmProj₁ z) (symmProj₂ z)) ∧
      (∀ (x : M → ℝ) (y : N → ℝ), G.IsNash x y →
        (G.addConst c).symmReduction.IsSymmetricNash
          (Sum.elim
            (((G.addConst c).payoff₁ x y /
                ((G.addConst c).payoff₁ x y + (G.addConst c).payoff₂ x y)) • x)
            (((G.addConst c).payoff₂ x y /
                ((G.addConst c).payoff₁ x y + (G.addConst c).payoff₂ x y)) • y))) := by
  obtain ⟨c, hA, hB⟩ := G.exists_addConst_pos
  exact ⟨c, fun z hz =>
      (symmReduction_pos_and_isNash hA hB hz).imp_right (And.imp_right isNash_addConst.1),
    fun x y hxy => isSymmetricNash_symmReduction_of_isNash hA hB (isNash_addConst.2 hxy)⟩

end FintypeTwoBlock

end TwoBlockReduction

end Cslib.GameTheory.BimatrixGame
