/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module
-- upstream: candidate (Mathlib, `Mathlib/LinearAlgebra/Matrix/PosDef.lean`)

public import CslibFrontier.Init
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Positive (semi)definiteness criteria

A symmetric `2 × 2` real matrix `!![a, b; b, c]` with `a, c ≥ 0` and `b² ≤ ac` is positive
semidefinite (`Matrix.posSemidef_fin_two`), and so is a symmetric real matrix that is diagonally
dominant, `∑_{j ≠ i} |R i j| ≤ R i i` (`Matrix.posSemidef_of_diagDominant`). An `LDLᴴ` product
`L * diagonal d * Lᴴ` with `L` unit lower triangular is positive definite exactly when every `d i`
is positive, and positive semidefinite exactly when every `d i` is nonnegative. Since `L` is
invertible, this is a case of Sylvester's law of inertia for the congruence by `L`. Conversely,
over a field with trivial star, such as `ℚ`, every positive semidefinite (definite) matrix has
such a factorization with `d ≥ 0` (`d > 0`), found by symmetric elimination without pivoting;
Mathlib's `LDL.lower_conj_diag` covers only positive definite matrices over `RCLike` fields.

## Main results

* `Matrix.posSemidef_fin_two`: the diagonal-and-determinant criterion for a symmetric `2 × 2` real
  matrix to be positive semidefinite.
* `Matrix.posSemidef_of_diagDominant`: a symmetric, diagonally dominant real matrix is positive
  semidefinite.
* `Matrix.posDef_mul_diagonal_mul_conjTranspose_iff`,
  `Matrix.posSemidef_mul_diagonal_mul_conjTranspose_iff`: the `LDLᴴ` criteria.
* `Matrix.exists_LDL_of_posSemidef`, `Matrix.exists_LDL_of_posDef`: their converses over a field
  with trivial star, such as `ℚ`: a positive semidefinite (definite) matrix factors as
  `L * diagonal d * Lᵀ` with `L` unit lower triangular and `d ≥ 0` (`d > 0`), by symmetric
  elimination without pivoting.
-/

public section

namespace Matrix

/-- A symmetric `2 × 2` real matrix with nonnegative diagonal and nonnegative determinant is
positive semidefinite. -/
theorem posSemidef_fin_two {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (h : b ^ 2 ≤ a * c) :
    (!![a, b; b, c]).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    fin_cases i <;> fin_cases j <;> rfl
  · simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, star_trivial]
    rcases ha.eq_or_lt with rfl | hapos
    · obtain rfl : b = 0 := sq_eq_zero_iff.mp (le_antisymm (by simpa using h) (sq_nonneg b))
      nlinarith [mul_nonneg hc (sq_nonneg (x 1))]
    · refine (mul_nonneg_iff_of_pos_left hapos).1 ?_
      nlinarith [sq_nonneg (a * x 0 + b * x 1), mul_nonneg (sub_nonneg.2 h) (sq_nonneg (x 1))]

/-- **Diagonal dominance.** A symmetric real matrix with `∑_{j ≠ i} |R i j| ≤ R i i` for every
`i` is positive semidefinite. -/
theorem posSemidef_of_diagDominant {n : Type*} [Fintype n] [DecidableEq n] {R : Matrix n n ℝ}
    (hR : Rᵀ = R) (h : ∀ i, ∑ j, (if i = j then 0 else |R i j|) ≤ R i i) : R.PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨by rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hR], fun x => ?_⟩
  simp only [star_trivial, dotProduct, mulVec, Finset.mul_sum]
  set c : n → n → ℝ := fun i j => if i = j then 0 else |R i j| with hc
  have hsymm : ∀ i j, R j i = R i j := fun i j => by
    rw [← transpose_apply R i j, hR]
  have hcs : ∀ i j, c j i = c i j := fun i j => by
    simp only [hc, hsymm, eq_comm]
  -- each off-diagonal pair is bounded below
  have hT : ∀ i j, 0 ≤ 2 * (x i * (R i j * x j)) + c i j * x i ^ 2 + c i j * x j ^ 2 -
      (if i = j then 2 * (x i * (R i j * x j)) else 0) := by
    intro i j
    simp only [hc]
    split_ifs with hij
    · simp
    · rcases abs_cases (R i j) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1]
      · nlinarith [mul_nonneg h2 (sq_nonneg (x i + x j))]
      · nlinarith [mul_nonneg (neg_nonneg.2 h2.le) (sq_nonneg (x i - x j))]
  have hsum := Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hT i j
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true] at hsum
  have hswap : ∑ i, ∑ j, c i j * x j ^ 2 = ∑ i, ∑ j, c i j * x i ^ 2 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hcs]
  have hdiag : ∑ i, ∑ j, c i j * x i ^ 2 ≤ ∑ i, x i * (R i i * x i) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_mul]
    nlinarith [mul_le_mul_of_nonneg_right (h i) (sq_nonneg (x i))]
  have h2 : ∑ i, ∑ j, 2 * (x i * (R i j * x j)) = 2 * ∑ i, ∑ j, x i * (R i j * x j) := by
    simp only [Finset.mul_sum]
  have h3 : ∑ i, 2 * (x i * (R i i * x i)) = 2 * ∑ i, x i * (R i i * x i) := by
    simp only [Finset.mul_sum]
  rw [hswap] at hsum
  linarith [hsum, hdiag, h2, h3]

section LDL

variable {n R : Type*} [Fintype n] [DecidableEq n] [LinearOrder n] [CommRing R]
  {L : Matrix n n R} {d : n → R}

/-- A unit lower-triangular matrix is a unit: its determinant is the product of its
diagonal. -/
private theorem isUnit_of_isLowerTriangular (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1) :
    IsUnit L :=
  (isUnit_iff_isUnit_det L).2 <| by simp [det_of_isLowerTriangular L hL, h1]

/-- An `LDLᴴ` product with `L` unit lower triangular is positive definite exactly when every
diagonal entry `d i` is positive. -/
theorem posDef_mul_diagonal_mul_conjTranspose_iff [PartialOrder R] [StarRing R]
    [StarOrderedRing R] [NoZeroDivisors R] [Nontrivial R] (hL : L.IsLowerTriangular)
    (h1 : ∀ i, L i i = 1) :
    (L * diagonal d * Lᴴ).PosDef ↔ ∀ i, 0 < d i := by
  rw [← star_eq_conjTranspose,
    IsUnit.posDef_star_right_conjugate_iff (isUnit_of_isLowerTriangular hL h1), posDef_diagonal_iff]

/-- An `LDLᴴ` product with `L` unit lower triangular is positive semidefinite exactly when every
diagonal entry `d i` is nonnegative. -/
theorem posSemidef_mul_diagonal_mul_conjTranspose_iff [PartialOrder R] [StarRing R]
    [StarOrderedRing R] (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1) :
    (L * diagonal d * Lᴴ).PosSemidef ↔ ∀ i, 0 ≤ d i := by
  rw [← star_eq_conjTranspose,
    IsUnit.posSemidef_star_right_conjugate_iff (isUnit_of_isLowerTriangular hL h1),
    posSemidef_diagonal_iff]

end LDL

section LDLExistence

variable {K : Type*} [Field K] [PartialOrder K] [StarRing K] [StarOrderedRing K] [TrivialStar K]

/-- Entry `(i, j)` of `L * diagonal d * Lᵀ` is `∑ₖ L i k * d k * L j k`. -/
theorem mul_diagonal_mul_transpose_apply {m R : Type*} [Fintype m] [DecidableEq m]
    [NonUnitalNonAssocSemiring R] (L : Matrix m m R) (d : m → R) (i j : m) :
    (L * diagonal d * Lᵀ) i j = ∑ k, L i k * d k * L j k := by
  rw [Matrix.mul_apply]
  simp only [mul_diagonal, transpose_apply]

/-- **Existence of `LDLᵀ` for positive semidefinite matrices.** Over a field with trivial star
and a star order, such as `ℚ` or `ℝ`, every positive semidefinite `M` factors as
`M = L * diagonal d * Lᵀ` with `L` unit lower triangular and every `d i ≥ 0`, including a
singular `M`.

The proof is symmetric Gaussian elimination without pivoting. With pivot `a = M 0 0 ≥ 0` and
first column `b`, set `l = a⁻¹ • b`. A zero pivot forces `b = 0`
(`Matrix.PosSemidef.dotProduct_mulVec_zero_iff` at the first basis vector), so `b = a • l` in
both cases and `L` has the column `l` below its first entry. The Schur complement
`M i.succ j.succ - a * l i * l j` is positive semidefinite, since its quadratic form at `y` is
that of `M` at `Fin.cons (-(l ⬝ᵥ y)) y`, and it factors by induction. -/
theorem exists_LDL_of_posSemidef : ∀ {n : ℕ} {M : Matrix (Fin n) (Fin n) K}, M.PosSemidef →
    ∃ (L : Matrix (Fin n) (Fin n) K) (d : Fin n → K), L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧
      (∀ i, 0 ≤ d i) ∧ M = L * diagonal d * Lᵀ
  | 0, _, _ => ⟨1, 0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      by ext i; exact i.elim0⟩
  | n + 1, M, hM => by
    have hsymm : ∀ i j, M j i = M i j := fun i j => by
      simpa using congrFun (congrFun hM.isHermitian.eq i) j
    set a := M 0 0
    set l : Fin n → K := fun j => a⁻¹ * M j.succ 0
    -- the first column is `a • l`: a zero pivot forces it to vanish
    have hb : ∀ j, M j.succ 0 = a * l j := by
      intro j
      by_cases ha : a = 0
      · have h0 : M *ᵥ Pi.single 0 1 = 0 :=
          (hM.dotProduct_mulVec_zero_iff).1 (by simpa [a] using ha)
        simpa [ha, l] using congrFun h0 j.succ
      · simp [l, ha]
    -- the Schur complement is positive semidefinite
    set S : Matrix (Fin n) (Fin n) K := of fun i j => M i.succ j.succ - a * l i * l j
    have hS : S.PosSemidef := by
      refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun y => ?_
      · ext i j
        simp only [S, conjTranspose_apply, of_apply, star_trivial, hsymm]
        ring
      · have := hM.dotProduct_mulVec_nonneg (Fin.cons (-(l ⬝ᵥ y)) y)
        convert this using 1
        set t := l ⬝ᵥ y
        simp only [star_trivial, dotProduct, mulVec, Fin.sum_univ_succ, Fin.cons_zero,
          Fin.cons_succ, S, of_apply]
        have e1 : ∑ x, M 0 x.succ * y x = a * t := by
          simp only [← hsymm 0, hb, t, dotProduct, Finset.mul_sum, mul_assoc]
        have e2 : ∀ x, ∑ j, (M x.succ j.succ - a * l x * l j) * y j =
            ∑ j, M x.succ j.succ * y j - a * l x * t := by
          intro x
          simp only [sub_mul, Finset.sum_sub_distrib, t, dotProduct, Finset.mul_sum, mul_assoc]
        have e3 : ∑ x, y x * (a * l x * t) = a * t * t := by
          simp only [t, dotProduct, Finset.sum_mul, Finset.mul_sum]
          exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
        have e4 : ∑ x, y x * (M x.succ 0 * -t) = -(a * t * t) := by
          rw [← e3, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun _ _ => by rw [hb]; ring
        simp only [e1, e2, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [e3, e4]
        ring
    obtain ⟨L', d', hL', h1', hd', hS'⟩ := exists_LDL_of_posSemidef hS
    have hSij (i j : Fin n) : M i.succ j.succ = ∑ k, L' i k * d' k * L' j k + a * l i * l j :=
      sub_eq_iff_eq_add.mp (by
        simpa only [S, of_apply, mul_diagonal_mul_transpose_apply] using
          congrFun (congrFun hS' i) j)
    set L : Matrix (Fin (n + 1)) (Fin (n + 1)) K := of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases (l i') (fun j' => L' i' j') j) i
    refine ⟨L, Fin.cons a d', fun i j hij => ?_, Fin.cases rfl h1',
      Fin.cases hM.diag_nonneg hd', ?_⟩
    · cases i using Fin.cases <;> cases j using Fin.cases
      · exact absurd hij (lt_irrefl _)
      · rfl
      · exact absurd hij (Fin.succ_pos _).not_gt
      · exact hL' (Fin.succ_lt_succ_iff.1 hij)
    · ext i j
      rw [mul_diagonal_mul_transpose_apply]
      simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      cases i using Fin.cases <;> cases j using Fin.cases <;>
        simp only [L, of_apply, Fin.cases_zero, Fin.cases_succ, hSij, hb, ← hsymm 0 (Fin.succ _),
          mul_zero, zero_mul, mul_one, one_mul, add_zero, Finset.sum_const_zero] <;> ring

/-- **Existence of `LDLᵀ` for positive definite matrices.** Every positive definite `M` factors as
`M = L * diagonal d * Lᵀ` with `L` unit lower triangular and every `d i > 0`. -/
theorem exists_LDL_of_posDef {n : ℕ} {M : Matrix (Fin n) (Fin n) K} (hM : M.PosDef) :
    ∃ (L : Matrix (Fin n) (Fin n) K) (d : Fin n → K), L.IsLowerTriangular ∧ (∀ i, L i i = 1) ∧
      (∀ i, 0 < d i) ∧ M = L * diagonal d * Lᵀ := by
  obtain ⟨L, d, hL, h1, -, rfl⟩ := exists_LDL_of_posSemidef hM.posSemidef
  refine ⟨L, d, hL, h1, ?_, rfl⟩
  rwa [← conjTranspose_eq_transpose_of_trivial, posDef_mul_diagonal_mul_conjTranspose_iff hL h1]
    at hM

end LDLExistence

end Matrix
