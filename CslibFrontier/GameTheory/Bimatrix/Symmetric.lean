/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import CslibFrontier.GameTheory.Strategic.Symmetric
public import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Symmetric bimatrix games and reductions to symmetric Nash equilibrium

A two-player bimatrix game `G : BimatrixGame M M` with shared strategy set `M` is **symmetric**
(`BimatrixGame.IsSymmetric`) if `G.B = G.Aᵀ` ([Papadimitriou2007], Example 2.2, p. 30): swapping
the roles of the two players leaves all payoffs unchanged. A mixed strategy `x : M → ℝ` is a
**symmetric Nash equilibrium** (`BimatrixGame.IsSymmetricNash`) if `(x, x)` is a Nash equilibrium,
equivalently if `x` is a best response of player 1 to `x`.

This module establishes:

* **Symmetry bridge and Nash's symmetric existence theorem for bimatrix games**
  ([Nash1951]; [Papadimitriou2007], Example 2.2, pp. 30–31, and Section 2.3.1, p. 34):
  `toSymmCostGame` embeds `BimatrixGame M M` into `CostGame Bool (fun _ => M)` preserving symmetry
  and symmetric Nash equilibria, so `CostGame.IsSymmetric.exists_isSymmetricMixedNash` immediately
  yields `BimatrixGame.IsSymmetric.exists_isSymmetricNash`.
* **Papadimitriou's two-block reduction from general `NASH` to `SYMMETRIC NASH`**
  ([Papadimitriou2007], Theorem 2.4, p. 34): for any positive bimatrix game `G = (A, B)` on
  `M × N`, the symmetric game `symmReduction G = ofSymmetric [[0, A], [Bᵀ, 0]]` on `M ⊕ N` has the
  property that every symmetric Nash equilibrium `z` assigns strictly positive mass to both `M` and
  `N` and its normalized block projections `(symmProj₁ z, symmProj₂ z)` form a Nash equilibrium of
  `G`; conversely, every Nash equilibrium `(x, y)` of `G` lifts to a symmetric Nash equilibrium of
  `symmReduction G`.
* **Gale–Kuhn–Tucker three-block symmetric reduction** ([GaleKuhnTucker1950]; [Papadimitriou2007],
  Section 2.3.1): for the three-block game `gktGame G = ofSymmetric [[0, A, -1], [Bᵀ, 0, 1],
  [1, -1, 0]]` on `M ⊕ N ⊕ Unit`, whenever `A > 0` and `B > 0`, every symmetric Nash equilibrium
  assigns strictly positive mass to `M` and `N` whose normalized projections `(gktProj₁ z,
  gktProj₂ z)` form a Nash equilibrium of `G`; moreover, whenever `1 ≤ B` (achievable on any finite
  game via `BimatrixGame.addConst`), the auxiliary `Unit` strategy receives probability `0`
  (`gktGame_unit_eq_zero`, `gktGame_recovery`).

## Main definitions

* `Cslib.GameTheory.BimatrixGame.IsSymmetric`: `G.B = G.Aᵀ`.
* `Cslib.GameTheory.BimatrixGame.ofSymmetric`: the symmetric bimatrix game `⟨A, Aᵀ⟩`.
* `Cslib.GameTheory.BimatrixGame.IsSymmetricNash`: `G.IsNash x x`.
* `Cslib.GameTheory.BimatrixGame.toSymmCostGame`: symmetric-type embedding into
  `CostGame Bool (fun _ => M)`.
* `Cslib.GameTheory.BimatrixGame.symmReduction`, `symmProj₁`, `symmProj₂`: Theorem 2.4's two-block
  symmetric game on `M ⊕ N` and its normalized block projections.
* `Cslib.GameTheory.BimatrixGame.gktMatrix`, `gktGame`, `gktProj₁`, `gktProj₂`: the
  Gale–Kuhn–Tucker three-block symmetric game on `M ⊕ N ⊕ Unit` and its normalized projections.

## Main results

* `Cslib.GameTheory.BimatrixGame.IsSymmetric.exists_isSymmetricNash`: every finite nonempty
  symmetric bimatrix game has a symmetric Nash equilibrium.
* `Cslib.GameTheory.BimatrixGame.symmReduction_pos_and_isNash`,
  `Cslib.GameTheory.BimatrixGame.isSymmetricNash_symmReduction_of_isNash`,
  `Cslib.GameTheory.BimatrixGame.exists_addConst_symmReduction`: Theorem 2.4's two-way
  correspondence between Nash equilibria of `G` and symmetric Nash equilibria of `symmReduction G`
  (including the constant-shift reduction for arbitrary-sign finite bimatrix games).
* `Cslib.GameTheory.BimatrixGame.gktGame_isNash_proj`,
  `Cslib.GameTheory.BimatrixGame.gktGame_unit_eq_zero`,
  `Cslib.GameTheory.BimatrixGame.gktGame_recovery`: equilibrium recovery and zero `Unit` weight in
  `gktGame G`.

## References

* [D. Gale, H. W. Kuhn, and A. W. Tucker, *On Symmetric Games*][GaleKuhnTucker1950]
* [J. Nash, *Non-Cooperative Games*][Nash1951]
* [N. Nisan, T. Roughgarden, É. Tardos, and V. V. Vazirani (eds.),
  *Algorithmic Game Theory*][NisanRoughgardenTardosVazirani2007]
* [C. H. Papadimitriou, *The Complexity of Finding Nash Equilibria*][Papadimitriou2007]
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
@[expose] def ofSymmetric (A : Matrix M M ℝ) : BimatrixGame M M :=
  ⟨A, Aᵀ⟩

@[simp]
theorem ofSymmetric_A (A : Matrix M M ℝ) : (ofSymmetric A).A = A := rfl

@[simp]
theorem ofSymmetric_B (A : Matrix M M ℝ) : (ofSymmetric A).B = Aᵀ := rfl

theorem isSymmetric_ofSymmetric (A : Matrix M M ℝ) : (ofSymmetric A).IsSymmetric := rfl

theorem IsSymmetric.swap_eq {G : BimatrixGame M M} (hG : G.IsSymmetric) : G.swap = G := by
  cases G
  dsimp only [IsSymmetric] at hG
  subst hG
  simp only [swap_mk, transpose_transpose]

/-- Embedding of `G : BimatrixGame M M` as a two-player `CostGame Bool (fun _ => M)` on the shared
strategy type `M`, where `false` is the row player and `true` is the column player. -/
@[expose] def toSymmCostGame (G : BimatrixGame M M) : CostGame Bool (fun _ => M) where
  cost
    | false => fun s => -G.A (s false) (s true)
    | true => fun s => -G.B (s false) (s true)

/-- `G.toSymmCostGame` is symmetric in the `CostGame` sense iff `G` is symmetric (`G.B = G.Aᵀ`). -/
theorem isSymmetric_toSymmCostGame_iff {G : BimatrixGame M M} :
    G.toSymmCostGame.IsSymmetric ↔ G.IsSymmetric := by
  constructor
  · intro h
    ext i j
    have hij := h (Equiv.swap false true) (fun b => cond b j i) false
    dsimp only [toSymmCostGame, Function.comp_apply] at hij
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, Bool.cond_true, Bool.cond_false,
      neg_inj, transpose_apply] at hij ⊢
    exact hij.symm
  · intro hG π s b
    by_cases hπ : π false = false
    · have hπt : π true = true := by
        rcases Bool.dichotomy (π true) with ht | ht
        · exact absurd (π.injective (ht.trans hπ.symm)) (by decide)
        · exact ht
      have hs : s ∘ π = s := by
        funext c
        cases c <;> simp only [Function.comp_apply, hπ, hπt]
      rw [hs]
      cases b <;> simp only [hπ, hπt]
    · have hπf : π false = true := Bool.eq_true_of_not_eq_false hπ
      have hπt : π true = false := by
        rcases Bool.dichotomy (π true) with ht | ht
        · exact ht
        · exact absurd (π.injective (ht.trans hπf.symm)) (by decide)
      cases b
      · rw [hπf]
        dsimp only [toSymmCostGame, Function.comp_apply]
        rw [hπf, hπt, hG, transpose_apply]
      · rw [hπt]
        dsimp only [toSymmCostGame, Function.comp_apply]
        rw [hπf, hπt, hG, transpose_apply]

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

theorem isBestResponse₁_iff_le_payoff₁ {N : Type*} [Fintype N] {H : BimatrixGame M N}
    {x : M → ℝ} {y : N → ℝ} :
    H.IsBestResponse₁ x y ↔ IsMixedStrategy x ∧ ∀ i : M, (H.A *ᵥ y) i ≤ H.payoff₁ x y := by
  constructor
  · exact fun h => ⟨h.isMixedStrategy, h.le_payoff₁⟩
  · rintro ⟨hx, hle⟩
    refine isBestResponse₁_iff.2 ⟨hx, ?_⟩
    simp only [isPureBestResponse₁_iff]
    simp_rw [payoff₁_eq_dotProduct] at hle
    exact hx.forall_dotProduct_le_iff.1 fun x' hx' => hx'.dotProduct_le_of_forall_le hle

theorem isBestResponse₂_iff_le_payoff₂ {N : Type*} [Fintype N] {H : BimatrixGame M N}
    {x : M → ℝ} {y : N → ℝ} :
    H.IsBestResponse₂ y x ↔ IsMixedStrategy y ∧ ∀ j : N, (x ᵥ* H.B) j ≤ H.payoff₂ x y := by
  rw [← isBestResponse₁_swap, isBestResponse₁_iff_le_payoff₁]
  simp only [payoff₁_swap, swap_A, mulVec_transpose]

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
  rw [CostGame.deviationCost_def, ← (boolPairEquiv M).symm.sum_comp]
  have hterm : ∀ p : M × M,
      productWeight (fun _ : Bool => x) ((boolPairEquiv M).symm p) *
          G.toSymmCostGame.cost false (update ((boolPairEquiv M).symm p) false i) =
        x p.1 * (-(G.A i p.2 * x p.2)) := by
    intro p
    rw [productWeight_def, Fintype.prod_bool]
    dsimp only [boolPairEquiv, Equiv.coe_fn_symm_mk, toSymmCostGame]
    have hf : update (fun b => cond b p.2 p.1) false i false = i := by rw [update_self]
    have ht : update (fun b => cond b p.2 p.1) false i true = p.2 := by
      rw [update_of_ne (by decide : true ≠ false)]
      rfl
    rw [hf, ht]
    simp only [Bool.cond_true, Bool.cond_false]
    ring
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  simp_rw [← mul_sum]
  rw [← sum_mul, hx, one_mul, Finset.sum_neg_distrib]
  rfl

private theorem expectedCost_toSymmCostGame_false {x : M → ℝ} (hx : ∑ i : M, x i = 1) :
    G.toSymmCostGame.expectedCost (fun _ => x) false = -G.payoff₁ x x := by
  rw [← G.toSymmCostGame.sum_mul_deviationCost_eq_expectedCost (fun _ => x) hx]
  simp_rw [deviationCost_toSymmCostGame_false hx, mul_neg, Finset.sum_neg_distrib]
  rw [payoff₁_eq_dotProduct]
  rfl

/-- In a symmetric bimatrix game, `x` is a symmetric Nash equilibrium iff `x` is a symmetric mixed
Nash equilibrium of `G.toSymmCostGame`. -/
theorem IsSymmetric.isSymmetricNash_iff_isSymmetricMixedNash (hG : G.IsSymmetric) {x : M → ℝ} :
    G.IsSymmetricNash x ↔ G.toSymmCostGame.IsSymmetricMixedNash x := by
  rw [hG.isSymmetricNash_iff,
    (isSymmetric_toSymmCostGame_iff.2 hG).isSymmetricMixedNash_iff_at false]
  refine and_congr_right fun hx => forall_congr' fun i => ?_
  rw [expectedCost_toSymmCostGame_false hx.sum_eq_one,
    deviationCost_toSymmCostGame_false hx.sum_eq_one i, neg_le_neg_iff]

/-- **Nash's symmetric equilibrium theorem for bimatrix games** ([Nash1951];
[Papadimitriou2007], Example 2.2, pp. 30–31, and Section 2.3.1, p. 34): every finite nonempty
symmetric bimatrix game has a symmetric Nash equilibrium. -/
theorem IsSymmetric.exists_isSymmetricNash [Nonempty M] (hG : G.IsSymmetric) :
    ∃ x : M → ℝ, G.IsSymmetricNash x := by
  obtain ⟨x, hx⟩ := (isSymmetric_toSymmCostGame_iff.2 hG).exists_isSymmetricMixedNash
  exact ⟨x, hG.isSymmetricNash_iff_isSymmetricMixedNash.2 hx⟩

end FintypeSymmetric

end SymmetricBimatrix

/-! ### Theorem 2.4: Two-block symmetric reduction on `M ⊕ N` -/

section TwoBlockReduction

variable {M N : Type*}

/-- Player 1's payoff matrix `[[0, A], [Bᵀ, 0]]` on `M ⊕ N` for Papadimitriou's reduction to
symmetric games ([Papadimitriou2007], Theorem 2.4, p. 34). -/
@[expose] def symmReductionMatrix (G : BimatrixGame M N) : Matrix (M ⊕ N) (M ⊕ N) ℝ :=
  Matrix.fromBlocks 0 G.A G.Bᵀ 0

/-- The symmetric two-player game `ofSymmetric [[0, A], [Bᵀ, 0]]` on `M ⊕ N` associated to a
bimatrix game `G` ([Papadimitriou2007], Theorem 2.4, p. 34). -/
@[expose] def symmReduction (G : BimatrixGame M N) : BimatrixGame (M ⊕ N) (M ⊕ N) :=
  ofSymmetric G.symmReductionMatrix

theorem isSymmetric_symmReduction (G : BimatrixGame M N) : G.symmReduction.IsSymmetric := rfl

section FintypeTwoBlock

variable [Fintype M] [Fintype N]

/-- Normalized `M`-block projection of `z : M ⊕ N → ℝ`. -/
@[expose] noncomputable def symmProj₁ (z : M ⊕ N → ℝ) : M → ℝ :=
  (∑ i : M, z (.inl i))⁻¹ • fun i => z (.inl i)

/-- Normalized `N`-block projection of `z : M ⊕ N → ℝ`. -/
@[expose] noncomputable def symmProj₂ (z : M ⊕ N → ℝ) : N → ℝ :=
  (∑ j : N, z (.inr j))⁻¹ • fun j => z (.inr j)

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
  have hx_ne : x ≠ 0 := by
    intro h0
    simp only [h0, Pi.zero_apply, sum_const_zero, lt_self_iff_false] at hsx_pos
  have hy_ne : y ≠ 0 := by
    intro h0
    simp only [h0, Pi.zero_apply, sum_const_zero, lt_self_iff_false] at hsy_pos
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

/-- **Forward direction of Theorem 2.4** ([Papadimitriou2007], Section 2.3.1, p. 34): if `G` has
strictly positive payoffs, then at every symmetric Nash equilibrium `z` of `G.symmReduction`, both
blocks `M` and `N` carry strictly positive probability mass, and their normalized projections
`(symmProj₁ z, symmProj₂ z)` form a Nash equilibrium of `G`. -/
theorem symmReduction_pos_and_isNash [Nonempty M] [Nonempty N] {G : BimatrixGame M N}
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) {z : M ⊕ N → ℝ}
    (hz : G.symmReduction.IsSymmetricNash z) :
    0 < ∑ i : M, z (.inl i) ∧ 0 < ∑ j : N, z (.inr j) ∧
      G.IsNash (symmProj₁ z) (symmProj₂ z) := by
  have hbr : G.symmReduction.IsBestResponse₁ z z :=
    (isSymmetric_symmReduction G).isSymmetricNash_iff_isBestResponse₁.1 hz
  have hz_mix : IsMixedStrategy z := hbr.isMixedStrategy
  set x : M → ℝ := fun i => z (.inl i)
  set y : N → ℝ := fun j => z (.inr j)
  set sx : ℝ := ∑ i : M, x i
  set sy : ℝ := ∑ j : N, y j
  have hsx_nn : 0 ≤ sx := sum_nonneg fun i _ => hz_mix.nonneg (.inl i)
  have hsy_nn : 0 ≤ sy := sum_nonneg fun j _ => hz_mix.nonneg (.inr j)
  have hsx_add_sy : sx + sy = 1 := by
    have h1 := hz_mix.sum_eq_one
    rwa [Fintype.sum_sum_type] at h1
  have hsx_pos : 0 < sx := by
    rcases hsx_nn.eq_or_lt with hsx0 | hsx_pos
    · have hx0 : ∀ i : M, x i = 0 := fun i =>
        le_antisymm (single_le_sum (fun i' _ => hz_mix.nonneg (.inl i')) (mem_univ i)
          |>.trans hsx0.symm.le) (hz_mix.nonneg (.inl i))
      have hsy1 : sy = 1 := by linarith
      have hy_mix : IsMixedStrategy y :=
        isMixedStrategy_iff.2 ⟨fun j => hz_mix.nonneg (.inr j), hsy1⟩
      obtain ⟨j₁, hj₁⟩ := hy_mix.exists_pos
      have hval0 : G.symmReduction.payoff₁ z z = 0 := by
        rw [hbr.payoff₁_eq_of_pos hj₁, show G.symmReduction.A = G.symmReductionMatrix from rfl,
          mulVec_symmReductionMatrix_inr]
        exact sum_eq_zero fun i _ => by
          change x i * G.B i j₁ = 0
          rw [hx0 i, zero_mul]
      let i₀ : M := Classical.arbitrary M
      have hpos_row : 0 < (G.symmReduction.A *ᵥ z) (.inl i₀) := by
        rw [show G.symmReduction.A = G.symmReductionMatrix from rfl, mulVec_symmReductionMatrix_inl]
        change 0 < G.A i₀ ⬝ᵥ y
        rw [dotProduct_comm]
        exact hy_mix.dotProduct_pos (hA i₀)
      linarith [hbr.le_payoff₁ (.inl i₀)]
    · exact hsx_pos
  have hsy_pos : 0 < sy := by
    rcases hsy_nn.eq_or_lt with hsy0 | hsy_pos
    · have hy0 : ∀ j : N, y j = 0 := fun j =>
        le_antisymm (single_le_sum (fun j' _ => hz_mix.nonneg (.inr j')) (mem_univ j)
          |>.trans hsy0.symm.le) (hz_mix.nonneg (.inr j))
      have hsx1 : sx = 1 := by linarith
      have hx_mix : IsMixedStrategy x :=
        isMixedStrategy_iff.2 ⟨fun i => hz_mix.nonneg (.inl i), hsx1⟩
      obtain ⟨i₁, hi₁⟩ := hx_mix.exists_pos
      have hval0 : G.symmReduction.payoff₁ z z = 0 := by
        rw [hbr.payoff₁_eq_of_pos hi₁, show G.symmReduction.A = G.symmReductionMatrix from rfl,
          mulVec_symmReductionMatrix_inl]
        exact sum_eq_zero fun j _ => by
          change G.A i₁ j * y j = 0
          rw [hy0 j, mul_zero]
      let j₀ : N := Classical.arbitrary N
      have hpos_col : 0 < (G.symmReduction.A *ᵥ z) (.inr j₀) := by
        rw [show G.symmReduction.A = G.symmReductionMatrix from rfl, mulVec_symmReductionMatrix_inr]
        exact hx_mix.dotProduct_pos fun i => hB i j₀
      linarith [hbr.le_payoff₁ (.inr j₀)]
    · exact hsy_pos
  refine ⟨hsx_pos, hsy_pos, isNash_inv_sum_smul (fun i => hz_mix.nonneg (.inl i)) hsx_pos
    (fun j => hz_mix.nonneg (.inr j)) hsy_pos (fun i hxi i' => ?_) (fun j hyj j' => ?_)⟩
  · have hopt := (hbr.le_payoff₁ (.inl i')).trans_eq (hbr.payoff₁_eq_of_pos hxi)
    rwa [show G.symmReduction.A = G.symmReductionMatrix from rfl, mulVec_symmReductionMatrix_inl,
      mulVec_symmReductionMatrix_inl] at hopt
  · have hopt := (hbr.le_payoff₁ (.inr j')).trans_eq (hbr.payoff₁_eq_of_pos hyj)
    rwa [show G.symmReduction.A = G.symmReductionMatrix from rfl, mulVec_symmReductionMatrix_inr,
      mulVec_symmReductionMatrix_inr] at hopt

/-- **Reverse direction of Theorem 2.4**: every Nash equilibrium `(x, y)` of a positive bimatrix
game `G` lifts to a symmetric Nash equilibrium `Sum.elim ((u / (u + v)) • x) ((v / (u + v)) • y)`
of `G.symmReduction`, where `u = G.payoff₁ x y` and `v = G.payoff₂ x y`. -/
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
  have hu : 0 < u := G.payoff₁_pos hA hx hy
  have hv : 0 < v := G.payoff₂_pos hB hx hy
  have huv : 0 < u + v := add_pos hu hv
  set α : ℝ := u / (u + v)
  set β : ℝ := v / (u + v)
  have hα : 0 < α := div_pos hu huv
  have hβ : 0 < β := div_pos hv huv
  have hαβ : α + β = 1 := by
    dsimp only [α, β]
    rw [← add_div, div_self huv.ne']
  set z : M ⊕ N → ℝ := Sum.elim (α • x) (β • y)
  have hz_mix : IsMixedStrategy z := by
    refine isMixedStrategy_iff.2 ⟨fun k => ?_, ?_⟩
    · cases k with
      | inl i => exact mul_nonneg hα.le (hx.nonneg i)
      | inr j => exact mul_nonneg hβ.le (hy.nonneg j)
    · rw [Fintype.sum_sum_type]
      simp only [z, Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, ← mul_sum,
        hx.sum_eq_one, hy.sum_eq_one, mul_one, hαβ]
  have hval_inl : ∀ i : M, (G.symmReduction.A *ᵥ z) (.inl i) = β * (G.A *ᵥ y) i := fun i => by
    rw [show G.symmReduction.A = G.symmReductionMatrix from rfl, mulVec_symmReductionMatrix_inl]
    dsimp only [z]
    simp only [Sum.elim_inr]
    rw [mulVec_smul, Pi.smul_apply, smul_eq_mul]
  have hval_inr : ∀ j : N, (G.symmReduction.A *ᵥ z) (.inr j) = α * (x ᵥ* G.B) j := fun j => by
    rw [show G.symmReduction.A = G.symmReductionMatrix from rfl, mulVec_symmReductionMatrix_inr]
    dsimp only [z]
    simp only [Sum.elim_inl]
    rw [smul_vecMul, Pi.smul_apply, smul_eq_mul]
  have hcommon : β * u = α * v := by
    dsimp only [α, β]
    ring
  refine ((isSymmetric_symmReduction G).isSymmetricNash_iff_pureBestResponse).2
    ⟨hz_mix, fun k hk => isPureBestResponse₁_iff.2 fun k' => ?_⟩
  have hk_eq : (G.symmReduction.A *ᵥ z) k = β * u := by
    cases k with
    | inl i =>
      have hxi : 0 < x i := pos_of_mul_pos_right hk hα.le
      rw [hval_inl, ← hbr₁.payoff₁_eq_of_pos hxi]
    | inr j =>
      have hyj : 0 < y j := pos_of_mul_pos_right hk hβ.le
      rw [hval_inr, hcommon, ← hbr₂.payoff₂_eq_of_pos hyj]
  rw [hk_eq]
  cases k' with
  | inl i' =>
    rw [hval_inl]
    exact mul_le_mul_of_nonneg_left (hbr₁.le_payoff₁ i') hβ.le
  | inr j' =>
    rw [hval_inr, hcommon]
    exact mul_le_mul_of_nonneg_left (hbr₂.le_payoff₂ j') hα.le

/-- **General (arbitrary-sign) constant-shift corollary of Theorem 2.4** ([Papadimitriou2007],
Theorem 2.4, Section 2.3.1, p. 34): for *any* finite nonempty bimatrix game `G` (without sign
restrictions), there exists a uniform shift `c : ℝ` such that `G' := G.addConst c` has strictly
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
  refine ⟨c, fun z hz => ?_, fun x y hxy => ?_⟩
  · obtain ⟨hsx, hsy, hNash⟩ := symmReduction_pos_and_isNash hA hB hz
    exact ⟨hsx, hsy, isNash_addConst.1 hNash⟩
  · exact isSymmetricNash_symmReduction_of_isNash hA hB (isNash_addConst.2 hxy)

end FintypeTwoBlock

end TwoBlockReduction

/-! ### Gale–Kuhn–Tucker three-block symmetric game on `M ⊕ N ⊕ Unit` -/

section GaleKuhnTucker

variable {M N : Type*}

/-- The three-block matrix `[[0, A, -1], [Bᵀ, 0, 1], [1, -1, 0]]` on `M ⊕ N ⊕ Unit`, extending
the Gale–Kuhn–Tucker zero-sum symmetrization ([GaleKuhnTucker1950]) to general bimatrix games
`G = (A, B)`. -/
@[expose] def gktMatrix (G : BimatrixGame M N) :
    Matrix (M ⊕ N ⊕ Unit) (M ⊕ N ⊕ Unit) ℝ
  | .inl _, .inl _ => 0
  | .inl i, .inr (.inl j) => G.A i j
  | .inl _, .inr (.inr _) => -1
  | .inr (.inl j), .inl i => G.B i j
  | .inr (.inl _), .inr (.inl _) => 0
  | .inr (.inl _), .inr (.inr _) => 1
  | .inr (.inr _), .inl _ => 1
  | .inr (.inr _), .inr (.inl _) => -1
  | .inr (.inr _), .inr (.inr _) => 0

/-- The symmetric two-player bimatrix game `ofSymmetric G.gktMatrix` on `M ⊕ N ⊕ Unit`. -/
@[expose] def gktGame (G : BimatrixGame M N) :
    BimatrixGame (M ⊕ N ⊕ Unit) (M ⊕ N ⊕ Unit) :=
  ofSymmetric G.gktMatrix

theorem isSymmetric_gktGame (G : BimatrixGame M N) : G.gktGame.IsSymmetric := rfl

section FintypeGKT

variable [Fintype M] [Fintype N]

/-- Normalized `M`-block projection of `z : M ⊕ N ⊕ Unit → ℝ`. -/
@[expose] noncomputable def gktProj₁ (z : M ⊕ N ⊕ Unit → ℝ) : M → ℝ :=
  (∑ i : M, z (.inl i))⁻¹ • fun i => z (.inl i)

/-- Normalized `N`-block projection of `z : M ⊕ N ⊕ Unit → ℝ`. -/
@[expose] noncomputable def gktProj₂ (z : M ⊕ N ⊕ Unit → ℝ) : N → ℝ :=
  (∑ j : N, z (.inr (.inl j)))⁻¹ • fun j => z (.inr (.inl j))

private theorem mulVec_gktMatrix_inl (G : BimatrixGame M N) (z : M ⊕ N ⊕ Unit → ℝ) (i : M) :
    (G.gktMatrix *ᵥ z) (.inl i) = (G.A *ᵥ fun j => z (.inr (.inl j))) i - z (.inr (.inr ())) := by
  change ∑ k : M ⊕ N ⊕ Unit, G.gktMatrix (.inl i) k * z k =
    (∑ j : N, G.A i j * z (.inr (.inl j))) - z (.inr (.inr ()))
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
  simp only [gktMatrix, zero_mul, sum_const_zero, zero_add]
  ring

private theorem mulVec_gktMatrix_inr_inl (G : BimatrixGame M N) (z : M ⊕ N ⊕ Unit → ℝ) (j : N) :
    (G.gktMatrix *ᵥ z) (.inr (.inl j)) =
      ((fun i => z (.inl i)) ᵥ* G.B) j + z (.inr (.inr ())) := by
  change ∑ k : M ⊕ N ⊕ Unit, G.gktMatrix (.inr (.inl j)) k * z k =
    (∑ i : M, z (.inl i) * G.B i j) + z (.inr (.inr ()))
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
  simp only [gktMatrix, zero_mul, sum_const_zero, one_mul, zero_add]
  congr 1
  exact sum_congr rfl fun i _ => mul_comm _ _

private theorem mulVec_gktMatrix_unit (G : BimatrixGame M N) (z : M ⊕ N ⊕ Unit → ℝ) :
    (G.gktMatrix *ᵥ z) (.inr (.inr ())) =
      (∑ i : M, z (.inl i)) - ∑ j : N, z (.inr (.inl j)) := by
  change ∑ k : M ⊕ N ⊕ Unit, G.gktMatrix (.inr (.inr ())) k * z k = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)]
  simp only [gktMatrix, one_mul, neg_mul, zero_mul, add_zero, Finset.sum_neg_distrib]
  ring

/-- When `A > 0`, every symmetric Nash equilibrium `z` of `G.gktGame` assigns strictly positive
probability mass to `M`. -/
theorem gktGame_sum_inl_pos [Nonempty M] [Nonempty N] {G : BimatrixGame M N}
    (hA : ∀ i j, 0 < G.A i j) {z : M ⊕ N ⊕ Unit → ℝ}
    (hz : G.gktGame.IsSymmetricNash z) :
    0 < ∑ i : M, z (.inl i) := by
  have hbr : G.gktGame.IsBestResponse₁ z z :=
    (isSymmetric_gktGame G).isSymmetricNash_iff_isBestResponse₁.1 hz
  have hz_mix := hbr.isMixedStrategy
  set x : M → ℝ := fun i => z (.inl i)
  set y : N → ℝ := fun j => z (.inr (.inl j))
  set w : ℝ := z (.inr (.inr ()))
  set sx : ℝ := ∑ i : M, x i
  set sy : ℝ := ∑ j : N, y j
  have hsx_nn : 0 ≤ sx := sum_nonneg fun i _ => hz_mix.nonneg (.inl i)
  have hsy_nn : 0 ≤ sy := sum_nonneg fun j _ => hz_mix.nonneg (.inr (.inl j))
  have hw_nn : 0 ≤ w := hz_mix.nonneg (.inr (.inr ()))
  have htot : sx + sy + w = 1 := by
    have h1 := hz_mix.sum_eq_one
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit)] at h1
    change sx + (sy + w) = 1 at h1
    linarith
  rcases hsx_nn.eq_or_lt with hsx0 | hsx_pos
  · exfalso
    have hx0 : ∀ i : M, x i = 0 := fun i =>
      le_antisymm (single_le_sum (fun i' _ => hz_mix.nonneg (.inl i')) (mem_univ i)
        |>.trans hsx0.symm.le) (hz_mix.nonneg (.inl i))
    have hxB0 : ∀ j : N, (x ᵥ* G.B) j = 0 := fun j =>
      sum_eq_zero fun i _ => by simp only [hx0 i, zero_mul]
    rcases hsy_nn.eq_or_lt with hsy0 | hsy_pos
    · have hw1 : w = 1 := by linarith
      have hval0 : G.gktGame.payoff₁ z z = 0 := by
        rw [hbr.payoff₁_eq_of_pos (show 0 < z (.inr (.inr ())) by linarith),
          show G.gktGame.A = G.gktMatrix from rfl, mulVec_gktMatrix_unit]
        change sx - sy = 0
        linarith
      let j₀ : N := Classical.arbitrary N
      have hj₀_pay : (G.gktGame.A *ᵥ z) (.inr (.inl j₀)) = 1 := by
        rw [show G.gktGame.A = G.gktMatrix from rfl, mulVec_gktMatrix_inr_inl, hxB0 j₀]
        linarith
      linarith [hbr.le_payoff₁ (.inr (.inl j₀))]
    · have hex_j : ∃ j₁ : N, 0 < y j₁ := by
        by_contra h
        push Not at h
        have h0 : sy = 0 := sum_eq_zero fun j _ =>
          le_antisymm (h j) (hz_mix.nonneg (.inr (.inl j)))
        linarith
      obtain ⟨j₁, hj₁⟩ := hex_j
      have hval_w : G.gktGame.payoff₁ z z = w := by
        rw [hbr.payoff₁_eq_of_pos hj₁, show G.gktGame.A = G.gktMatrix from rfl,
          mulVec_gktMatrix_inr_inl, hxB0 j₁, zero_add]
      rcases hw_nn.eq_or_lt with hw0 | hw_pos
      · have hsy1 : sy = 1 := by linarith
        have hy_mix : IsMixedStrategy y :=
          isMixedStrategy_iff.2 ⟨fun j => hz_mix.nonneg (.inr (.inl j)), hsy1⟩
        let i₀ : M := Classical.arbitrary M
        have hpos_A : 0 < (G.A *ᵥ y) i₀ := by
          change 0 < G.A i₀ ⬝ᵥ y
          rw [dotProduct_comm]
          exact hy_mix.dotProduct_pos (hA i₀)
        have hi₀_pay : (G.gktGame.A *ᵥ z) (.inl i₀) = (G.A *ᵥ y) i₀ := by
          rw [show G.gktGame.A = G.gktMatrix from rfl, mulVec_gktMatrix_inl]
          change (G.A *ᵥ y) i₀ - w = (G.A *ᵥ y) i₀
          linarith
        linarith [hbr.le_payoff₁ (.inl i₀)]
      · have hval_neg : G.gktGame.payoff₁ z z = -sy := by
          rw [hbr.payoff₁_eq_of_pos hw_pos, show G.gktGame.A = G.gktMatrix from rfl,
            mulVec_gktMatrix_unit]
          change sx - sy = -sy
          linarith
        linarith
  · exact hsx_pos

/-- When `A > 0` and `B > 0`, every symmetric Nash equilibrium `z` of `G.gktGame` assigns strictly
positive probability mass to `N`. -/
theorem gktGame_sum_inr_inl_pos [Nonempty M] [Nonempty N] {G : BimatrixGame M N}
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) {z : M ⊕ N ⊕ Unit → ℝ}
    (hz : G.gktGame.IsSymmetricNash z) :
    0 < ∑ j : N, z (.inr (.inl j)) := by
  have hbr : G.gktGame.IsBestResponse₁ z z :=
    (isSymmetric_gktGame G).isSymmetricNash_iff_isBestResponse₁.1 hz
  have hz_mix := hbr.isMixedStrategy
  have hsx_pos := gktGame_sum_inl_pos hA hz
  set x : M → ℝ := fun i => z (.inl i)
  set y : N → ℝ := fun j => z (.inr (.inl j))
  set w : ℝ := z (.inr (.inr ()))
  set sy : ℝ := ∑ j : N, y j
  have hsy_nn : 0 ≤ sy := sum_nonneg fun j _ => hz_mix.nonneg (.inr (.inl j))
  have hw_nn : 0 ≤ w := hz_mix.nonneg (.inr (.inr ()))
  rcases hsy_nn.eq_or_lt with hsy0 | hsy_pos
  · exfalso
    have hy0 : ∀ j : N, y j = 0 := fun j =>
      le_antisymm (single_le_sum (fun j' _ => hz_mix.nonneg (.inr (.inl j'))) (mem_univ j)
        |>.trans hsy0.symm.le) (hz_mix.nonneg (.inr (.inl j)))
    have hex_i : ∃ i₁ : M, 0 < x i₁ := by
      by_contra h
      push Not at h
      have h0 : ∑ i : M, x i = 0 := sum_eq_zero fun i _ =>
        le_antisymm (h i) (hz_mix.nonneg (.inl i))
      linarith
    obtain ⟨i₁, hi₁⟩ := hex_i
    have hAy0 : (G.A *ᵥ y) i₁ = 0 :=
      sum_eq_zero fun j _ => by simp only [hy0 j, mul_zero]
    have hval_neg_w : G.gktGame.payoff₁ z z = -w := by
      rw [hbr.payoff₁_eq_of_pos hi₁, show G.gktGame.A = G.gktMatrix from rfl,
        mulVec_gktMatrix_inl, hAy0, zero_sub]
    let j₀ : N := Classical.arbitrary N
    have hxB_pos : 0 < (x ᵥ* G.B) j₀ :=
      (sum_pos_iff_of_nonneg fun i _ =>
        mul_nonneg (hz_mix.nonneg (.inl i)) (hB i j₀).le).2
        ⟨i₁, mem_univ i₁, mul_pos hi₁ (hB i₁ j₀)⟩
    have hj₀_pay : (G.gktGame.A *ᵥ z) (.inr (.inl j₀)) = (x ᵥ* G.B) j₀ + w := by
      rw [show G.gktGame.A = G.gktMatrix from rfl, mulVec_gktMatrix_inr_inl]
    linarith [hbr.le_payoff₁ (.inr (.inl j₀))]
  · exact hsy_pos

/-- **Gale–Kuhn–Tucker equilibrium recovery**: for any bimatrix game `G` with `A > 0` and `B > 0`
and any symmetric Nash equilibrium `z` of `G.gktGame`, the normalized block projections
`(gktProj₁ z, gktProj₂ z)` form a Nash equilibrium of `G`. -/
theorem gktGame_isNash_proj [Nonempty M] [Nonempty N] {G : BimatrixGame M N}
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) {z : M ⊕ N ⊕ Unit → ℝ}
    (hz : G.gktGame.IsSymmetricNash z) :
    G.IsNash (gktProj₁ z) (gktProj₂ z) := by
  have hbr : G.gktGame.IsBestResponse₁ z z :=
    (isSymmetric_gktGame G).isSymmetricNash_iff_isBestResponse₁.1 hz
  have hz_mix := hbr.isMixedStrategy
  have hsx_pos := gktGame_sum_inl_pos hA hz
  have hsy_pos := gktGame_sum_inr_inl_pos hA hB hz
  refine isNash_inv_sum_smul (fun i => hz_mix.nonneg (.inl i)) hsx_pos
    (fun j => hz_mix.nonneg (.inr (.inl j))) hsy_pos (fun i hxi i' => ?_) (fun j hyj j' => ?_)
  · have hopt := (hbr.le_payoff₁ (.inl i')).trans_eq (hbr.payoff₁_eq_of_pos hxi)
    rw [show G.gktGame.A = G.gktMatrix from rfl, mulVec_gktMatrix_inl, mulVec_gktMatrix_inl] at hopt
    linarith
  · have hopt := (hbr.le_payoff₁ (.inr (.inl j'))).trans_eq (hbr.payoff₁_eq_of_pos hyj)
    rw [show G.gktGame.A = G.gktMatrix from rfl, mulVec_gktMatrix_inr_inl,
      mulVec_gktMatrix_inr_inl] at hopt
    linarith

/-- When `A > 0` and `1 ≤ B` (obtainable on any finite game via `BimatrixGame.addConst`), every
symmetric Nash equilibrium `z` of `G.gktGame` assigns probability `0` to the auxiliary `Unit`
strategy. -/
theorem gktGame_unit_eq_zero [Nonempty M] [Nonempty N] {G : BimatrixGame M N}
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 1 ≤ G.B i j) {z : M ⊕ N ⊕ Unit → ℝ}
    (hz : G.gktGame.IsSymmetricNash z) :
    z (.inr (.inr ())) = 0 := by
  have hbr : G.gktGame.IsBestResponse₁ z z :=
    (isSymmetric_gktGame G).isSymmetricNash_iff_isBestResponse₁.1 hz
  have hz_mix := hbr.isMixedStrategy
  have hB_pos : ∀ i j, 0 < G.B i j := fun i j => zero_lt_one.trans_le (hB i j)
  have hsy_pos := gktGame_sum_inr_inl_pos hA hB_pos hz
  rcases (hz_mix.nonneg (.inr (.inr ()))).eq_or_lt with hw0 | hw_pos
  · exact hw0.symm
  · exfalso
    let j₀ : N := Classical.arbitrary N
    have hxB_ge : ∑ i : M, z (.inl i) ≤ ((fun i => z (.inl i)) ᵥ* G.B) j₀ := by
      calc ∑ i : M, z (.inl i)
          = ∑ i : M, z (.inl i) * 1 := by simp only [mul_one]
        _ ≤ ∑ i : M, z (.inl i) * G.B i j₀ :=
            sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hB i j₀) (hz_mix.nonneg (.inl i))
    have hunit_eq : G.gktGame.payoff₁ z z =
        (∑ i : M, z (.inl i)) - ∑ j : N, z (.inr (.inl j)) := by
      rw [hbr.payoff₁_eq_of_pos hw_pos, show G.gktGame.A = G.gktMatrix from rfl,
        mulVec_gktMatrix_unit]
    have hj₀_le := hbr.le_payoff₁ (.inr (.inl j₀))
    rw [show G.gktGame.A = G.gktMatrix from rfl, mulVec_gktMatrix_inr_inl, hunit_eq] at hj₀_le
    linarith

/-- **Full Gale–Kuhn–Tucker symmetric reduction theorem**: when `0 < A` and `1 ≤ B`, every
symmetric Nash equilibrium `z` of `G.gktGame` assigns weight `0` to `Unit`, strictly positive
weights to `M` and `N`, and its normalized projections `(gktProj₁ z, gktProj₂ z)` form a Nash
equilibrium of `G`. -/
theorem gktGame_recovery [Nonempty M] [Nonempty N] {G : BimatrixGame M N}
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 1 ≤ G.B i j) {z : M ⊕ N ⊕ Unit → ℝ}
    (hz : G.gktGame.IsSymmetricNash z) :
    z (.inr (.inr ())) = 0 ∧ 0 < ∑ i : M, z (.inl i) ∧
      0 < ∑ j : N, z (.inr (.inl j)) ∧ G.IsNash (gktProj₁ z) (gktProj₂ z) := by
  have hB_pos : ∀ i j, 0 < G.B i j := fun i j => zero_lt_one.trans_le (hB i j)
  exact ⟨gktGame_unit_eq_zero hA hB hz, gktGame_sum_inl_pos hA hz,
    gktGame_sum_inr_inl_pos hA hB_pos hz, gktGame_isNash_proj hA hB_pos hz⟩

end FintypeGKT

end GaleKuhnTucker

end Cslib.GameTheory.BimatrixGame
