/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.GameTheory.Bimatrix.Basic
public import CslibFrontier.GameTheory.Bimatrix.LemkeHowson
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Best response polytopes and the odd number of Nash equilibria

For a bimatrix game `G` with payoff matrices `A B : Matrix M N ℝ`, the *best response polytopes*
of [vonStengel2007], equation (3.6), are
`P = {x ∈ ℝ^M | x ≥ 0, Bᵀ x ≤ 1}` and `Q = {y ∈ ℝ^N | A y ≤ 1, y ≥ 0}`.
Both are written as systems of inequalities with rows indexed by the labels `M ⊕ N`
(`BimatrixGame.matP`, `BimatrixGame.rhsP`, `BimatrixGame.matQ`, `BimatrixGame.rhsQ`): the label
`i : M` of `x ∈ P` means `x i = 0` and the label `j : N` means `(xᵀ B) j = 1`, while the label
`i : M` of `y ∈ Q` means `(A y) i = 1` and `j : N` means `y j = 0`.

When all payoffs are positive, a nonzero completely labelled pair `(x, y) ∈ P × Q` rescales to a
Nash equilibrium `(x / ∑ x, y / ∑ y)` (`BimatrixGame.isNash_of_completelyLabeled`), and every Nash
equilibrium arises this way (`BimatrixGame.IsNash.completelyLabeled`). For a nondegenerate game
the systems are nondegenerate (`BimatrixGame.IsNondegenerate.isNondegenerateSystem_matP`), so
the completely labelled vertex pairs are exactly the artificial equilibrium `(0, 0)` and the
images of the Nash equilibria (`BimatrixGame.setOf_completelyLabeled_eq`). Combined with the
parity of completely labelled vertex pairs in the Lemke–Howson graph
(`Cslib.GameTheory.LemkeHowson.even_ncard_completelyLabeled`) this gives
[vonStengel2007], Corollary 3.7: **a nondegenerate bimatrix game has an odd number of Nash
equilibria** (`BimatrixGame.IsNondegenerate.odd_ncard_isNash`); in particular it has one
(`BimatrixGame.IsNondegenerate.exists_isNash`).

The argument is the undirected parity argument behind the Lemke–Howson algorithm
[LemkeHowson1964]; it does not formalize the algorithm's running time, the orientation of its
paths, or the membership of two-player Nash in PPAD.

## Main definitions

* `BimatrixGame.matP`, `BimatrixGame.rhsP`: the best response polytope `P` of player 1.
* `BimatrixGame.matQ`, `BimatrixGame.rhsQ`: the best response polytope `Q` of player 2.
* `BimatrixGame.toPolytopes`: the map from Nash equilibria to completely labelled pairs.

## Main results

* `BimatrixGame.IsNondegenerate.isNondegenerateSystem_matP`,
  `BimatrixGame.IsNondegenerate.isNondegenerateSystem_matQ`: the polytopes of a nondegenerate
  game are nondegenerate.
* `BimatrixGame.isNash_of_completelyLabeled`, `BimatrixGame.IsNash.completelyLabeled`:
  completely labelled pairs and Nash equilibria.
* `BimatrixGame.setOf_completelyLabeled_eq`: the completely labelled vertex pairs of a
  nondegenerate game with positive payoffs.
* `BimatrixGame.IsNondegenerate.odd_ncard_isNash`: a nondegenerate bimatrix game has an odd
  number of Nash equilibria ([vonStengel2007], Corollary 3.7).
* `BimatrixGame.IsNondegenerate.exists_isNash`: a nondegenerate bimatrix game has a Nash
  equilibrium. Nash's theorem for all bimatrix games is `BimatrixGame.exists_isNash` in
  `CslibFrontier.GameTheory.Bimatrix.Existence`.

## References

* [C. E. Lemke and J. T. Howson, Jr., *Equilibrium points of bimatrix games*][LemkeHowson1964]
* [B. von Stengel, *Equilibrium computation for two-player games in strategic and extensive
  form*][vonStengel2007], Sections 3.2–3.4
-/

public section

open Finset Matrix

namespace Cslib.GameTheory.BimatrixGame

variable {M N : Type*} [Fintype M] [Fintype N] (G : BimatrixGame M N)

/-! ### The best response polytopes -/

/-- The constraint matrix of the best response polytope `P = {x | x ≥ 0, Bᵀ x ≤ 1}` of player 1,
with rows labelled by `M ⊕ N` ([vonStengel2007], equation (3.6)). -/
def matP [DecidableEq M] : Matrix (M ⊕ N) M ℝ := fromRows (-1) G.Bᵀ

omit [Fintype M] [Fintype N] in
variable (M N) in
/-- The right-hand side of the best response polytope `P`: `0` on `M`, `1` on `N`. -/
def rhsP : M ⊕ N → ℝ := Sum.elim 0 1

/-- The constraint matrix of the best response polytope `Q = {y | A y ≤ 1, y ≥ 0}` of player 2,
with rows labelled by `M ⊕ N` ([vonStengel2007], equation (3.6)). -/
def matQ [DecidableEq N] : Matrix (M ⊕ N) N ℝ := fromRows G.A (-1)

omit [Fintype M] [Fintype N] in
variable (M N) in
/-- The right-hand side of the best response polytope `Q`: `1` on `M`, `0` on `N`. -/
def rhsQ : M ⊕ N → ℝ := Sum.elim 1 0

omit [Fintype M] [Fintype N] in
/-- Player 2's polytope matrix `matQ` is player 1's polytope matrix for `G.swap` with `M ⊕ N`
reindexed by `Equiv.sumComm M N`. -/
theorem matQ_eq_submatrix_swap_matP [DecidableEq N] :
    G.matQ = G.swap.matP.submatrix (Equiv.sumComm M N) id := by
  ext (i | j) k <;> simp [matQ, matP]

omit [Fintype M] [Fintype N] in
/-- Player 2's right-hand side `rhsQ` is `rhsP N M` composed with `Equiv.sumComm M N`. -/
theorem rhsQ_eq_rhsP_comp_sumComm : rhsQ M N = rhsP N M ∘ Equiv.sumComm M N :=
  funext fun | .inl _ | .inr _ => rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem rhsP_inl (i : M) : rhsP M N (.inl i) = 0 := by rw [rhsP]; rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem rhsP_inr (j : N) : rhsP M N (.inr j) = 1 := by rw [rhsP]; rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem rhsQ_inl (i : M) : rhsQ M N (.inl i) = 1 := by rw [rhsQ]; rfl

omit [Fintype M] [Fintype N] in
@[simp] theorem rhsQ_inr (j : N) : rhsQ M N (.inr j) = 0 := by rw [rhsQ]; rfl

variable [DecidableEq M] [DecidableEq N] {G} {x : M → ℝ} {y : N → ℝ}

omit [Fintype N] [DecidableEq N] in
theorem matP_mulVec (x : M → ℝ) : G.matP *ᵥ x = Sum.elim (-x) (x ᵥ* G.B) := by
  rw [matP, fromRows_mulVec, neg_mulVec, one_mulVec, mulVec_transpose]

omit [Fintype M] [DecidableEq M] in
theorem matQ_mulVec (y : N → ℝ) : G.matQ *ᵥ y = Sum.elim (G.A *ᵥ y) (-y) := by
  rw [matQ, fromRows_mulVec, neg_mulVec, one_mulVec]

omit [Fintype N] [DecidableEq N] in
@[simp]
theorem matP_mulVec_inl (x : M → ℝ) (i : M) : (G.matP *ᵥ x) (.inl i) = -x i :=
  congrFun (matP_mulVec x) (.inl i)

omit [Fintype N] [DecidableEq N] in
@[simp]
theorem matP_mulVec_inr (x : M → ℝ) (j : N) : (G.matP *ᵥ x) (.inr j) = (x ᵥ* G.B) j :=
  congrFun (matP_mulVec x) (.inr j)

omit [Fintype M] [DecidableEq M] in
@[simp]
theorem matQ_mulVec_inl (y : N → ℝ) (i : M) : (G.matQ *ᵥ y) (.inl i) = (G.A *ᵥ y) i :=
  congrFun (matQ_mulVec y) (.inl i)

omit [Fintype M] [DecidableEq M] in
@[simp]
theorem matQ_mulVec_inr (y : N → ℝ) (j : N) : (G.matQ *ᵥ y) (.inr j) = -y j :=
  congrFun (matQ_mulVec y) (.inr j)

omit [DecidableEq N] in
theorem inl_mem_tightRows_matP {i : M} : .inl i ∈ tightRows G.matP (rhsP M N) x ↔ x i = 0 := by
  simp

omit [DecidableEq N] in
theorem inr_mem_tightRows_matP {j : N} :
    .inr j ∈ tightRows G.matP (rhsP M N) x ↔ (x ᵥ* G.B) j = 1 := by
  simp

omit [DecidableEq M] in
theorem inl_mem_tightRows_matQ {i : M} :
    .inl i ∈ tightRows G.matQ (rhsQ M N) y ↔ (G.A *ᵥ y) i = 1 := by
  simp

omit [DecidableEq M] in
theorem inr_mem_tightRows_matQ {j : N} : .inr j ∈ tightRows G.matQ (rhsQ M N) y ↔ y j = 0 := by
  simp

omit [Fintype N] [DecidableEq N] in
/-- `x ∈ P` iff `x ≥ 0` and `Bᵀ x ≤ 1`. -/
theorem matP_mulVec_le_iff :
    G.matP *ᵥ x ≤ rhsP M N ↔ (∀ i, 0 ≤ x i) ∧ ∀ j, (x ᵥ* G.B) j ≤ 1 := by
  simp [Pi.le_def, matP_mulVec]

omit [Fintype M] [DecidableEq M] in
/-- `y ∈ Q` iff `A y ≤ 1` and `y ≥ 0`. -/
theorem matQ_mulVec_le_iff :
    G.matQ *ᵥ y ≤ rhsQ M N ↔ (∀ i, (G.A *ᵥ y) i ≤ 1) ∧ ∀ j, 0 ≤ y j := by
  simp [Pi.le_def, matQ_mulVec]

omit [Fintype N] [DecidableEq N] in
private theorem swap_matQ_mulVec_le_iff :
    G.swap.matQ *ᵥ x ≤ rhsQ N M ↔ G.matP *ᵥ x ≤ rhsP M N := by
  simp only [matQ_mulVec_le_iff, matP_mulVec_le_iff, swap_A, mulVec_transpose, and_comm]

omit [Fintype M] [DecidableEq M] in
private theorem swap_matP_mulVec_le_iff :
    G.swap.matP *ᵥ y ≤ rhsP N M ↔ G.matQ *ᵥ y ≤ rhsQ M N := by
  rw [← swap_matQ_mulVec_le_iff, swap_swap]

/-! ### Nondegeneracy and boundedness -/

omit [Fintype M] [DecidableEq M] [DecidableEq N] in
/-- A row where `A y` attains the bound `1` of `Q` is a pure best response of player 1 to every
nonnegative rescaling of `y`. -/
private theorem isPureBestResponse₁_smul_of_eq_one {c : ℝ} (hc : 0 ≤ c)
    (hy : ∀ i, (G.A *ᵥ y) i ≤ 1) {i : M} (hi : (G.A *ᵥ y) i = 1) :
    G.IsPureBestResponse₁ (c • y) i :=
  isPureBestResponse₁_iff.2 fun i' => by
    simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul, hi, mul_one]
    exact (mul_le_mul_of_nonneg_left (hy i') hc).trans_eq (mul_one _)

omit [DecidableEq N] in
/-- The best response polytope `P` of a nondegenerate game is a nondegenerate system: a point of
`P` has at most `card M` labels. -/
theorem IsNondegenerate.isNondegenerateSystem_matP (hG : G.IsNondegenerate) :
    IsNondegenerateSystem G.matP (rhsP M N) := by
  classical
  rw [isNondegenerateSystem_iff]
  intro x hx
  obtain ⟨hx₀, hxB⟩ := matP_mulVec_le_iff.1 hx
  have hL : (tightRows G.matP (rhsP M N) x).toLeft = univ.filter (x · = 0) :=
    Finset.ext fun _ => by simp
  rw [← card_toLeft_add_card_toRight, hL]
  rcases eq_or_ne x 0 with rfl | hx0
  · have hR : (tightRows G.matP (rhsP M N) 0).toRight = ∅ := Finset.ext fun _ => by simp
    rw [hR, card_empty, add_zero]
    exact card_le_univ _
  obtain ⟨i₀, hi₀⟩ := Function.ne_iff.1 hx0
  have hpos : 0 < ∑ i, x i :=
    (sum_pos_iff_of_nonneg fun j _ => hx₀ j).2 ⟨i₀, mem_univ _, (hx₀ i₀).lt_of_ne' hi₀⟩
  have hsupp : (Function.support ((∑ i, x i)⁻¹ • x)).ncard =
      #(univ.filter fun i => ¬x i = 0) := by
    rw [Function.support_const_smul_of_ne_zero _ _ (inv_ne_zero hpos.ne'),
      ← Set.ncard_coe_finset]
    exact congrArg Set.ncard (Set.ext fun _ => by simp)
  have hT : ((tightRows G.matP (rhsP M N) x).toRight : Set N) ⊆
      {j | G.IsPureBestResponse₂ ((∑ i, x i)⁻¹ • x) j} := fun j hj => by
    rw [Finset.mem_coe, mem_toRight, inr_mem_tightRows_matP] at hj
    exact isPureBestResponse₁_swap.1 (isPureBestResponse₁_smul_of_eq_one (G := G.swap)
      (inv_nonneg.2 hpos.le) (fun j' => by simpa only [swap_A, mulVec_transpose] using hxB j')
      (by simpa only [swap_A, mulVec_transpose] using hj))
  have h1 := (Set.ncard_le_ncard hT (Set.toFinite _)).trans
    ((isNondegenerate_iff.1 hG).1 _ (isMixedStrategy_inv_sum_smul hx₀ hx0))
  have hsum := card_filter_add_card_filter_not (s := univ) (x · = 0)
  rw [Set.ncard_coe_finset, hsupp] at h1
  rw [card_univ] at hsum
  omega

omit [DecidableEq M] in
/-- The best response polytope `Q` of a nondegenerate game is a nondegenerate system: a point of
`Q` has at most `card N` labels. -/
theorem IsNondegenerate.isNondegenerateSystem_matQ (hG : G.IsNondegenerate) :
    IsNondegenerateSystem G.matQ (rhsQ M N) := by
  rw [matQ_eq_submatrix_swap_matP, rhsQ_eq_rhsP_comp_sumComm, isNondegenerateSystem_submatrix_equiv]
  exact (isNondegenerate_swap.2 hG).isNondegenerateSystem_matP

omit [Fintype N] [DecidableEq N] in
/-- With positive payoffs to player 2, the best response polytope `P` is bounded: its recession
cone is `{0}`. -/
theorem eq_zero_of_matP_mulVec_nonpos [Nonempty N] (hB : ∀ i j, 0 < G.B i j) {v : M → ℝ}
    (hv : G.matP *ᵥ v ≤ 0) : v = 0 := by
  have hnn (i : M) : 0 ≤ v i := by simpa [matP_mulVec] using hv (.inl i)
  obtain ⟨j⟩ := ‹Nonempty N›
  have hsum : ∑ i, v i * G.B i j = 0 :=
    le_antisymm (by simpa [vecMul, dotProduct] using hv (.inr j))
      (sum_nonneg fun i _ => mul_nonneg (hnn i) (hB i j).le)
  exact funext fun i => (mul_eq_zero.1 ((sum_eq_zero_iff_of_nonneg fun i _ =>
    mul_nonneg (hnn i) (hB i j).le).1 hsum i (mem_univ _))).resolve_right (hB i j).ne'

omit [Fintype M] [DecidableEq M] in
/-- With positive payoffs to player 1, the best response polytope `Q` is bounded: its recession
cone is `{0}`. -/
theorem eq_zero_of_matQ_mulVec_nonpos [Nonempty M] (hA : ∀ i j, 0 < G.A i j) {v : N → ℝ}
    (hv : G.matQ *ᵥ v ≤ 0) : v = 0 :=
  G.swap.eq_zero_of_matP_mulVec_nonpos
    (fun j i => by simpa only [swap_B, transpose_apply] using hA i j) fun r => by
      simpa only [matQ_eq_submatrix_swap_matP, mulVec, dotProduct, submatrix_apply, id_eq,
        Equiv.sumComm_apply, Sum.swap_swap, Pi.zero_apply] using hv (Equiv.sumComm N M r)

omit [DecidableEq N] in
/-- The origin is a vertex of `P`. -/
theorem isVertex_matP_zero : IsVertex G.matP (rhsP M N) 0 :=
  isVertex_iff.2 ⟨matP_mulVec_le_iff.2 ⟨fun _ => le_rfl, fun _ => by simp⟩, fun v hv =>
    funext fun i => by simpa [matP_mulVec] using hv (.inl i) (inl_mem_tightRows_matP.2 rfl)⟩

omit [DecidableEq M] in
/-- The origin is a vertex of `Q`. -/
theorem isVertex_matQ_zero : IsVertex G.matQ (rhsQ M N) 0 := by
  rw [matQ_eq_submatrix_swap_matP, rhsQ_eq_rhsP_comp_sumComm, isVertex_submatrix_equiv]
  exact isVertex_matP_zero

/-! ### Completely labelled pairs and Nash equilibria -/

/-- A pair `(x, y)` is completely labelled for `P` and `Q` iff every row `i` is unplayed in `x`
or a best response with payoff `1` against `y`, and every column `j` is unplayed in `y` or a best
response with payoff `1` against `x`. -/
theorem completelyLabeled_iff_forall :
    LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y ↔
      (∀ i, x i = 0 ∨ (G.A *ᵥ y) i = 1) ∧ ∀ j, (x ᵥ* G.B) j = 1 ∨ y j = 0 := by
  simp [LemkeHowson.completelyLabeled_iff]

/-- Swapping the players swaps completely labelled pairs of `(P, Q)`. -/
private theorem completelyLabeled_swap :
    LemkeHowson.CompletelyLabeled G.swap.matP (rhsP N M) G.swap.matQ (rhsQ N M) y x ↔
      LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y := by
  simp only [completelyLabeled_iff_forall, swap_A, swap_B, mulVec_transpose, vecMul_transpose,
    or_comm, and_comm]

/-- In a feasible completely labelled pair, `x = 0` iff `y = 0`. -/
theorem eq_zero_iff_eq_zero_of_completelyLabeled (hx : G.matP *ᵥ x ≤ rhsP M N)
    (hy : G.matQ *ᵥ y ≤ rhsQ M N)
    (hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y) :
    x = 0 ↔ y = 0 := by
  obtain ⟨hcl₁, hcl₂⟩ := completelyLabeled_iff_forall.1 hcl
  constructor
  · rintro rfl
    exact funext fun j => by simpa using hcl₂ j
  · rintro rfl
    exact funext fun i => by simpa using hcl₁ i

private theorem isBestResponse₁_of_completelyLabeled (hx : G.matP *ᵥ x ≤ rhsP M N)
    (hy : G.matQ *ᵥ y ≤ rhsQ M N)
    (hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y)
    (hx0 : x ≠ 0) : G.IsBestResponse₁ ((∑ i, x i)⁻¹ • x) ((∑ j, y j)⁻¹ • y) := by
  obtain ⟨hx₀, -⟩ := matP_mulVec_le_iff.1 hx
  obtain ⟨hy₁, hy₀⟩ := matQ_mulVec_le_iff.1 hy
  obtain ⟨hcl₁, -⟩ := completelyLabeled_iff_forall.1 hcl
  refine isBestResponse₁_iff.2 ⟨isMixedStrategy_inv_sum_smul hx₀ hx0, fun i hi => ?_⟩
  exact isPureBestResponse₁_smul_of_eq_one (inv_nonneg.2 (sum_nonneg fun j _ => hy₀ j)) hy₁
    ((hcl₁ i).resolve_left fun h => by simp [h] at hi)

/-- A nonzero feasible completely labelled pair `(x, y)` of `P × Q` rescales to the Nash
equilibrium `(x / ∑ x, y / ∑ y)` ([vonStengel2007], Section 3.3). -/
theorem isNash_of_completelyLabeled (hx : G.matP *ᵥ x ≤ rhsP M N) (hy : G.matQ *ᵥ y ≤ rhsQ M N)
    (hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y)
    (hx0 : x ≠ 0) : G.IsNash ((∑ i, x i)⁻¹ • x) ((∑ j, y j)⁻¹ • y) := by
  have hy0 : y ≠ 0 := mt (eq_zero_iff_eq_zero_of_completelyLabeled hx hy hcl).2 hx0
  exact isNash_iff.2 ⟨isBestResponse₁_of_completelyLabeled hx hy hcl hx0,
    isBestResponse₁_swap.1
      (isBestResponse₁_of_completelyLabeled (swap_matP_mulVec_le_iff.2 hy)
        (swap_matQ_mulVec_le_iff.2 hx) (completelyLabeled_swap.2 hcl) hy0)⟩

omit [DecidableEq N] in
private theorem matP_mulVec_inv_payoff₂_le (hB : ∀ i j, 0 < G.B i j) (h : G.IsNash x y) :
    G.matP *ᵥ ((G.payoff₂ x y)⁻¹ • x) ≤ rhsP M N ∧
      ∀ j, ((((G.payoff₂ x y)⁻¹ • x) ᵥ* G.B) j = 1 ∨ y j = 0) := by
  obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
  have hp := G.payoff₂_pos hB h₁.isMixedStrategy h₂.isMixedStrategy
  refine ⟨matP_mulVec_le_iff.2 ⟨fun i => smul_nonneg (inv_nonneg.2 hp.le)
    (h₁.isMixedStrategy.nonneg i), fun j => ?_⟩, fun j => ?_⟩
  · rw [smul_vecMul, Pi.smul_apply, smul_eq_mul, inv_mul_le_iff₀ hp, mul_one]
    exact h₂.le_payoff₂ j
  · refine (h₂.isMixedStrategy.nonneg j).lt_or_eq.imp (fun hj => ?_) Eq.symm
    rw [smul_vecMul, Pi.smul_apply, smul_eq_mul, ← h₂.payoff₂_eq_of_pos hj, inv_mul_cancel₀ hp.ne']

/-- A Nash equilibrium `(x, y)` of a game with positive payoffs, rescaled by the inverse
equilibrium payoffs, is a feasible completely labelled pair of `P × Q`
([vonStengel2007], Section 3.3). -/
theorem IsNash.completelyLabeled (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j)
    (h : G.IsNash x y) :
    G.matP *ᵥ ((G.payoff₂ x y)⁻¹ • x) ≤ rhsP M N ∧
      G.matQ *ᵥ ((G.payoff₁ x y)⁻¹ • y) ≤ rhsQ M N ∧
      LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N)
        ((G.payoff₂ x y)⁻¹ • x) ((G.payoff₁ x y)⁻¹ • y) := by
  obtain ⟨hP, hcl₂⟩ := matP_mulVec_inv_payoff₂_le hB h
  obtain ⟨hQ', hcl₁'⟩ := matP_mulVec_inv_payoff₂_le (G := G.swap)
    (fun j i => by simpa only [swap_B, transpose_apply] using hA i j) (isNash_swap.2 h)
  refine ⟨hP, payoff₂_swap G y x ▸ swap_matP_mulVec_le_iff.1 hQ',
    completelyLabeled_iff_forall.2 ⟨fun i => (hcl₁' i).symm.imp
      (fun hi => by rw [Pi.smul_apply, hi, smul_zero])
      (by simpa only [payoff₂_swap, swap_B, vecMul_transpose] using ·),
    fun j => (hcl₂ j).imp_right fun hj => by rw [Pi.smul_apply, hj, smul_zero]⟩⟩

/-! ### The completely labelled vertex pairs -/

omit [DecidableEq M] [DecidableEq N] in
variable (G) in
/-- The completely labelled pair of a Nash equilibrium `(x, y)`: both strategies rescaled by the
inverse of the other player's equilibrium payoff. -/
noncomputable def toPolytopes (p : (M → ℝ) × (N → ℝ)) : (M → ℝ) × (N → ℝ) :=
  ((G.payoff₂ p.1 p.2)⁻¹ • p.1, (G.payoff₁ p.1 p.2)⁻¹ • p.2)

omit [DecidableEq M] [DecidableEq N] in
theorem toPolytopes_apply (p : (M → ℝ) × (N → ℝ)) :
    G.toPolytopes p = ((G.payoff₂ p.1 p.2)⁻¹ • p.1, (G.payoff₁ p.1 p.2)⁻¹ • p.2) := by
  rw [toPolytopes]

omit [DecidableEq M] [DecidableEq N] in
/-- With positive payoffs, distinct Nash equilibria give distinct completely labelled pairs. -/
theorem injOn_toPolytopes (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) :
    Set.InjOn G.toPolytopes {p | G.IsNash p.1 p.2} := by
  rintro ⟨x, y⟩ h ⟨x', y'⟩ h' he
  rw [Set.mem_ofPred_eq, isNash_iff] at h h'
  have hx := h.1.isMixedStrategy
  have hy := h.2.isMixedStrategy
  rw [toPolytopes_apply, toPolytopes_apply, Prod.mk.injEq] at he
  exact Prod.ext
    (hx.eq_of_smul_eq_smul h'.1.isMixedStrategy (inv_ne_zero (G.payoff₂_pos hB hx hy).ne') he.1)
    (hy.eq_of_smul_eq_smul h'.2.isMixedStrategy (inv_ne_zero (G.payoff₁_pos hA hx hy).ne') he.2)

omit [DecidableEq M] [DecidableEq N] in
/-- With positive payoffs to player 2, no Nash equilibrium gives the artificial pair `(0, 0)`. -/
theorem zero_notMem_image_toPolytopes (hB : ∀ i j, 0 < G.B i j) :
    0 ∉ G.toPolytopes '' {p | G.IsNash p.1 p.2} := by
  rintro ⟨⟨x, y⟩, h, he⟩
  obtain ⟨h₁, h₂⟩ := isNash_iff.1 h
  exact h₁.isMixedStrategy.ne_zero ((smul_eq_zero.1 (Prod.mk_eq_zero.1 he).1).resolve_left
    (inv_ne_zero (G.payoff₂_pos hB h₁.isMixedStrategy h₂.isMixedStrategy).ne'))

private theorem payoff₁_inv_sum_smul (hx : G.matP *ᵥ x ≤ rhsP M N)
    (hy : G.matQ *ᵥ y ≤ rhsQ M N)
    (hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y)
    (hx0 : x ≠ 0) :
    G.payoff₁ ((∑ i, x i)⁻¹ • x) ((∑ j, y j)⁻¹ • y) = (∑ j, y j)⁻¹ := by
  obtain ⟨hcl₁, -⟩ := completelyLabeled_iff_forall.1 hcl
  rw [payoff₁_eq_dotProduct]
  refine (isBestResponse₁_of_completelyLabeled hx hy hcl hx0).isMixedStrategy
    |>.dotProduct_eq_of_forall_pos fun i hi => ?_
  rw [mulVec_smul, Pi.smul_apply, smul_eq_mul,
    (hcl₁ i).resolve_left fun h => by simp [h] at hi, mul_one]

/-- The equilibrium payoffs of the Nash equilibrium obtained from a nonzero completely labelled
pair `(x, y)` are `1 / ∑ y` and `1 / ∑ x`. -/
private theorem payoff_inv_sum_smul (hx : G.matP *ᵥ x ≤ rhsP M N)
    (hy : G.matQ *ᵥ y ≤ rhsQ M N)
    (hcl : LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) x y)
    (hx0 : x ≠ 0) :
    G.payoff₁ ((∑ i, x i)⁻¹ • x) ((∑ j, y j)⁻¹ • y) = (∑ j, y j)⁻¹ ∧
      G.payoff₂ ((∑ i, x i)⁻¹ • x) ((∑ j, y j)⁻¹ • y) = (∑ i, x i)⁻¹ := by
  have hy0 : y ≠ 0 := fun h => hx0 ((eq_zero_iff_eq_zero_of_completelyLabeled hx hy hcl).2 h)
  exact ⟨payoff₁_inv_sum_smul hx hy hcl hx0, by
    rw [← payoff₁_swap]
    exact payoff₁_inv_sum_smul (swap_matP_mulVec_le_iff.2 hy) (swap_matQ_mulVec_le_iff.2 hx)
      (completelyLabeled_swap.2 hcl) hy0⟩

/-- **Completely labelled vertex pairs** ([vonStengel2007], Section 3.4). For a nondegenerate game
with positive payoffs, the completely labelled vertex pairs of `P × Q` are the artificial
equilibrium `(0, 0)` and the rescaled Nash equilibria. -/
theorem setOf_completelyLabeled_eq (hG : G.IsNondegenerate)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) :
    {p : (M → ℝ) × (N → ℝ) | IsVertex G.matP (rhsP M N) p.1 ∧ IsVertex G.matQ (rhsQ M N) p.2 ∧
      LemkeHowson.CompletelyLabeled G.matP (rhsP M N) G.matQ (rhsQ M N) p.1 p.2} =
      insert 0 (G.toPolytopes '' {p | G.IsNash p.1 p.2}) := by
  have hnd₁ := hG.isNondegenerateSystem_matP
  have hnd₂ := hG.isNondegenerateSystem_matQ
  ext ⟨x, y⟩
  rw [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_image]
  constructor
  · rintro ⟨hxv, hyv, hcl⟩
    have hx := hxv.mulVec_le
    have hy := hyv.mulVec_le
    rcases eq_or_ne x 0 with rfl | hx0
    · exact Or.inl (Prod.mk_eq_zero.2 ⟨rfl,
        (eq_zero_iff_eq_zero_of_completelyLabeled hx hy hcl).1 rfl⟩)
    · obtain ⟨hx₀, -⟩ := matP_mulVec_le_iff.1 hx
      obtain ⟨-, hy₀⟩ := matQ_mulVec_le_iff.1 hy
      have hy0 : y ≠ 0 := mt (eq_zero_iff_eq_zero_of_completelyLabeled hx hy hcl).2 hx0
      have hsx : ∑ i, x i ≠ 0 := fun h =>
        hx0 (funext fun i => (sum_eq_zero_iff_of_nonneg fun k _ => hx₀ k).1 h i (mem_univ _))
      have hsy : ∑ j, y j ≠ 0 := fun h =>
        hy0 (funext fun j => (sum_eq_zero_iff_of_nonneg fun k _ => hy₀ k).1 h j (mem_univ _))
      obtain ⟨hu, hv⟩ := payoff_inv_sum_smul hx hy hcl hx0
      refine Or.inr ⟨((∑ i, x i)⁻¹ • x, (∑ j, y j)⁻¹ • y),
        isNash_of_completelyLabeled hx hy hcl hx0, ?_⟩
      rw [toPolytopes_apply, hu, hv, inv_inv, inv_inv, smul_inv_smul₀ hsx, smul_inv_smul₀ hsy]
  · rintro (h | ⟨⟨x', y'⟩, h, he⟩)
    · obtain ⟨rfl, rfl⟩ := Prod.mk_eq_zero.1 h
      exact ⟨isVertex_matP_zero, isVertex_matQ_zero,
        completelyLabeled_iff_forall.2 ⟨fun _ => .inl rfl, fun _ => .inr rfl⟩⟩
    · rw [Set.mem_ofPred_eq] at h
      obtain ⟨i₀, -⟩ := (isNash_iff.1 h).1.isMixedStrategy.exists_pos
      obtain ⟨j₀, -⟩ := (isNash_iff.1 h).2.isMixedStrategy.exists_pos
      have : Nonempty M := ⟨i₀⟩
      have : Nonempty N := ⟨j₀⟩
      obtain ⟨hx, hy, hcl⟩ := h.completelyLabeled hA hB
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (G.toPolytopes_apply (x', y') ▸ he)
      exact ⟨LemkeHowson.isVertex_left_of_completelyLabeled hnd₁
          (fun _ => eq_zero_of_matP_mulVec_nonpos hB) hnd₂ Fintype.card_sum hx hy hcl,
        LemkeHowson.isVertex_right_of_completelyLabeled hnd₁ hnd₂
          (fun _ => eq_zero_of_matQ_mulVec_nonpos hA) Fintype.card_sum hx hy hcl, hcl⟩

omit [DecidableEq M] [DecidableEq N] in
/-- A nondegenerate bimatrix game with positive payoffs has an odd number of Nash equilibria. -/
theorem IsNondegenerate.odd_ncard_isNash_of_pos [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate)
    (hA : ∀ i j, 0 < G.A i j) (hB : ∀ i j, 0 < G.B i j) :
    Odd {p : (M → ℝ) × (N → ℝ) | G.IsNash p.1 p.2}.ncard := by
  classical
  have heven := LemkeHowson.even_ncard_completelyLabeled hG.isNondegenerateSystem_matP
    (fun _ => eq_zero_of_matP_mulVec_nonpos hB) hG.isNondegenerateSystem_matQ
    (fun _ => eq_zero_of_matQ_mulVec_nonpos hA) (Fintype.card_sum (α := M) (β := N))
  have hfin : (G.toPolytopes '' {p | G.IsNash p.1 p.2}).Finite :=
    ((setOf_isVertex_finite (A := G.matP) (b := rhsP M N)).prod
      (setOf_isVertex_finite (A := G.matQ) (b := rhsQ M N))).subset fun p hp => by
      have hp' := (setOf_completelyLabeled_eq hG hA hB).symm ▸ Set.mem_insert_of_mem 0 hp
      exact ⟨hp'.1, hp'.2.1⟩
  rwa [setOf_completelyLabeled_eq hG hA hB, Set.ncard_insert_of_notMem
    (zero_notMem_image_toPolytopes hB) hfin, (injOn_toPolytopes hA hB).ncard_image,
    Nat.even_add_one, Nat.not_even_iff_odd] at heven

omit [DecidableEq M] [DecidableEq N] in
/-- **A nondegenerate bimatrix game has an odd number of Nash equilibria** ([vonStengel2007],
Corollary 3.7). The proof is the parity argument behind the Lemke–Howson algorithm
[LemkeHowson1964]: after making all payoffs positive, the Nash equilibria correspond to the
completely labelled vertex pairs of the best response polytopes other than `(0, 0)`, and there is
an even number of those (`Cslib.GameTheory.LemkeHowson.even_ncard_completelyLabeled`). -/
theorem IsNondegenerate.odd_ncard_isNash [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate) :
    Odd {p : (M → ℝ) × (N → ℝ) | G.IsNash p.1 p.2}.ncard := by
  obtain ⟨c, hA, hB⟩ := G.exists_addConst_pos
  simpa only [isNash_addConst] using (isNondegenerate_addConst.2 hG).odd_ncard_isNash_of_pos hA hB

omit [DecidableEq M] [DecidableEq N] in
/-- A nondegenerate bimatrix game has a Nash equilibrium. This is the special case of Nash's
theorem for nondegenerate bimatrix games, obtained here from
`BimatrixGame.IsNondegenerate.odd_ncard_isNash`. -/
theorem IsNondegenerate.exists_isNash [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate) :
    ∃ x y, G.IsNash x y :=
  let ⟨⟨x, y⟩, h⟩ := Set.nonempty_of_ncard_ne_zero hG.odd_ncard_isNash.pos.ne'
  ⟨x, y, h⟩

omit [DecidableEq M] [DecidableEq N] in
/-- A nondegenerate bimatrix game has finitely many Nash equilibria. -/
theorem IsNondegenerate.finite_setOf_isNash [Nonempty M] [Nonempty N] (hG : G.IsNondegenerate) :
    {p : (M → ℝ) × (N → ℝ) | G.IsNash p.1 p.2}.Finite :=
  Set.finite_of_ncard_ne_zero hG.odd_ncard_isNash.pos.ne'

end Cslib.GameTheory.BimatrixGame
