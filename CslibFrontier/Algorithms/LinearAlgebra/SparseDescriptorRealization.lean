/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.SparseDescriptorCertificate

/-!
# Realizations and equilibria from structured decouplings

`Cslib.LinearAlgebra.SparseDecouplingCert` certifies an index-one decoupling in Schur form,
`T E U = [[E₁₁, 0], [0, 0]]`, `T F U = [[F₁₁, F₁₂], [F₂₁, F₂₂]]`, `F₂₂ K = F₂₁`, without ever
forming `P` and `Q` (`DescriptorSystem.IndexOneDecoupling.ofSchur`). This file adds the input
and output maps of the reduced system and a sparse equilibrium check, so that a structured
certificate gives the same proper realization `ẋ = A x + B u`, `y - y₀ = C x + D u` as a dense
`Cslib.LinearAlgebra.DecouplingCert` (`DecouplingCert.realization_toDecoupling`).

For the decoupling of `ofSchur`, the blocks of `P` and `Q` are (`P₁_ofSchur`, `P₂_ofSchur`,
`Q₁_ofSchur`, `Q₂_ofSchur`)

  `P₁ = E₁₁⁻¹ (T₁ - F₁₂ F₂₂⁻¹ T₂)`,  `P₂ = F₂₂⁻¹ T₂`,  `Q₁ = U₁ - U₂ K`,  `Q₂ = U₂`,

with `T₁`, `T₂` the first `k` and the last `r` rows of `T` and `U₁`, `U₂` the first `k` and the
last `r` columns of `U`. The input matrix `B = P₁ G` and the algebraic response `P₂ G` again
involve inverses. A `Cslib.LinearAlgebra.SparseRealizationCert` supplies them as sparse
solutions instead, `W = P₂ G` and `B = P₁ G`, and its checker `SparseRealizationCert.check`
verifies, with sparse rational products,

  `F₂₂ W = T₂ G`  and  `E₁₁ B = T₁ G - F₁₂ W`.

Given these, everything else is a product of checked sparse rows, computed rather than
supplied: for output rows `H`, the reconstruction `z = z₀ + Q₁ x - (U₂ W) u` with
`Q₁ = U₁ - U₂ K` (`SparseDecouplingCert.stateRows`, `SparseRealizationCert.inputRows`), the
output matrix `C = H Q₁` and the direct feedthrough `D = -H U₂ W`
(`SparseRealizationCert.realization_toDecoupling`).

`isEquilibriumSparse` checks `F z₀ + b = 0` for sparse rows of `F` with one sparse product
(`isEquilibrium_of_isEquilibriumSparse`), instead of the dense row products of
`isEquilibriumRows`.

## Main definitions

* `Cslib.LinearAlgebra.SparseRealizationCert`, `SparseRealizationCert.check`.
* `Cslib.LinearAlgebra.SparseDecouplingCert.stateRows`,
  `Cslib.LinearAlgebra.SparseRealizationCert.inputRows`, `outputRows`, `feedthroughRows`.
* `Cslib.LinearAlgebra.isEquilibriumSparse`.

## Main results

* `DescriptorSystem.IndexOneDecoupling.P₁_ofSchur`, `P₂_ofSchur`, `Q₁_ofSchur`, `Q₂_ofSchur`.
* `Cslib.LinearAlgebra.SparseRealizationCert.realization_toDecoupling`,
  `Cslib.LinearAlgebra.SparseRealizationCert.Q₂_P₂_G_toDecoupling`,
  `Cslib.LinearAlgebra.SparseDecouplingCert.Q₁_toDecoupling`.
* `Cslib.LinearAlgebra.isEquilibrium_of_isEquilibriumSparse`.
-/

public section

open Matrix Mathlib.Tactic.Matrix

namespace DescriptorSystem

namespace IndexOneDecoupling

variable {ι m κ ρ : Type*} [Fintype ι] [Fintype m] [Fintype κ] [Fintype ρ] [DecidableEq ι]
  [DecidableEq κ] [DecidableEq ρ] {S : DescriptorSystem ι m}
  (e : ι ≃ κ ⊕ ρ) (T : Matrix (κ ⊕ ρ) ι ℝ) (Tᵢ : Matrix ι (κ ⊕ ρ) ℝ) (U : Matrix ι (κ ⊕ ρ) ℝ)
  (Uᵢ : Matrix (κ ⊕ ρ) ι ℝ) (E₁₁ F₁₁ : Matrix κ κ ℝ) (F₁₂ : Matrix κ ρ ℝ) (F₂₁ K : Matrix ρ κ ℝ)
  (F₂₂ : Matrix ρ ρ ℝ) (hT : Tᵢ * T = 1) (hU : U * Uᵢ = 1)
  (hE : T * S.E * U = fromBlocks E₁₁ 0 0 0) (hF : T * S.F * U = fromBlocks F₁₁ F₁₂ F₂₁ F₂₂)
  (hE₁₁ : IsUnit E₁₁.det) (hF₂₂ : IsUnit F₂₂.det) (hK : F₂₂ * K = F₂₁)

omit [Fintype m] in
/-- The differential rows of `P` in the Schur-form decoupling. -/
theorem P₁_ofSchur :
    (ofSchur e T Tᵢ U Uᵢ E₁₁ F₁₁ F₁₂ F₂₁ K F₂₂ hT hU hE hF hE₁₁ hF₂₂ hK).P₁ =
      E₁₁⁻¹ * (T.toRows₁ - F₁₂ * F₂₂⁻¹ * T.toRows₂) := by
  have h : (fromBlocks E₁₁⁻¹ (-(E₁₁⁻¹ * F₁₂ * F₂₂⁻¹)) 0 F₂₂⁻¹ * T).toRows₁ =
      fromCols E₁₁⁻¹ (-(E₁₁⁻¹ * F₁₂ * F₂₂⁻¹)) * fromRows T.toRows₁ T.toRows₂ := by
    rw [fromRows_toRows]
    ext i j
    simp [toRows₁_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  refine h.trans ?_
  rw [fromCols_mul_fromRows, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.neg_mul, ← sub_eq_add_neg]

omit [Fintype m] in
/-- The algebraic rows of `P` in the Schur-form decoupling. -/
theorem P₂_ofSchur :
    (ofSchur e T Tᵢ U Uᵢ E₁₁ F₁₁ F₁₂ F₂₁ K F₂₂ hT hU hE hF hE₁₁ hF₂₂ hK).P₂ =
      F₂₂⁻¹ * T.toRows₂ := by
  ext i j
  simp [ofSchur, ofPartitioned, toRows₂_apply, Matrix.mul_apply, Fintype.sum_sum_type]

omit [Fintype m] in
/-- The differential columns of `Q` in the Schur-form decoupling. -/
theorem Q₁_ofSchur :
    (ofSchur e T Tᵢ U Uᵢ E₁₁ F₁₁ F₁₂ F₂₁ K F₂₂ hT hU hE hF hE₁₁ hF₂₂ hK).Q₁ =
      U.toCols₁ - U.toCols₂ * K := by
  ext i j
  simp [ofSchur, ofPartitioned, toCols₁_apply, toCols₂_apply, Matrix.mul_apply,
    Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg]

omit [Fintype m] in
/-- The algebraic columns of `Q` in the Schur-form decoupling. -/
theorem Q₂_ofSchur :
    (ofSchur e T Tᵢ U Uᵢ E₁₁ F₁₁ F₁₂ F₂₁ K F₂₂ hT hU hE hF hE₁₁ hF₂₂ hK).Q₂ = U.toCols₂ := by
  ext i j
  simp [ofSchur, ofPartitioned, toCols₂_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.one_apply]

omit [Fintype m] in
/-- **Input maps of the Schur-form decoupling from solutions.** If `F₂₂ W = T₂ G` and
`E₁₁ B = T₁ G - F₁₂ W`, then `P₂ G = W` and the input matrix `P₁ G` of the reduced system is
`B`. -/
theorem P₂_G_B_ofSchur {W : Matrix ρ m ℝ} {B : Matrix κ m ℝ}
    (hW : F₂₂ * W = T.toRows₂ * S.G) (hB : E₁₁ * B = T.toRows₁ * S.G - F₁₂ * W) :
    (ofSchur e T Tᵢ U Uᵢ E₁₁ F₁₁ F₁₂ F₂₁ K F₂₂ hT hU hE hF hE₁₁ hF₂₂ hK).P₂ * S.G = W ∧
      (ofSchur e T Tᵢ U Uᵢ E₁₁ F₁₁ F₁₂ F₂₁ K F₂₂ hT hU hE hF hE₁₁ hF₂₂ hK).B = B := by
  have hW' : F₂₂⁻¹ * (T.toRows₂ * S.G) = W := by
    rw [← hW, ← Matrix.mul_assoc, nonsing_inv_mul _ hF₂₂, Matrix.one_mul]
  refine ⟨by rw [P₂_ofSchur, Matrix.mul_assoc, hW'], ?_⟩
  rw [IndexOneDecoupling.B, P₁_ofSchur, Matrix.mul_assoc, Matrix.sub_mul,
    show F₁₂ * F₂₂⁻¹ * T.toRows₂ * S.G = F₁₂ * (F₂₂⁻¹ * (T.toRows₂ * S.G)) by
      simp only [Matrix.mul_assoc],
    hW', ← hB, ← Matrix.mul_assoc, nonsing_inv_mul _ hE₁₁, Matrix.one_mul]

end IndexOneDecoupling

end DescriptorSystem

namespace Cslib.LinearAlgebra

/-! ### Rows of the block transforms -/

section Rows

/-- The first `k` rows of a split matrix, read from sparse rows. -/
theorem realOfSparse_take {k r N n : ℕ} (h : k + r = N) (X : List (List (ℕ × ℚ))) :
    ((realOfSparse N n X).submatrix (blockEquiv h).symm id).toRows₁ =
      realOfSparse k n (X.take k) := by
  ext i j
  simp [toRows₁_apply, ofSparse_apply, blockEquiv]

/-- The last `r` rows of a split matrix, read from sparse rows. -/
theorem realOfSparse_drop {k r N n : ℕ} (h : k + r = N) (X : List (List (ℕ × ℚ))) :
    ((realOfSparse N n X).submatrix (blockEquiv h).symm id).toRows₂ =
      realOfSparse r n (X.drop k) := by
  ext i j
  simp [toRows₂_apply, ofSparse_apply, blockEquiv]

/-- The first `k` columns of a split matrix, read from sparse rows. -/
theorem realOfSparse_loCols {k r N n : ℕ} (h : k + r = N) (X : List (List (ℕ × ℚ))) :
    ((realOfSparse n N X).submatrix id (blockEquiv h).symm).toCols₁ =
      realOfSparse n k (X.map (loCols k)) := by
  ext i j
  simp only [toCols₁_apply, submatrix_apply, map_apply, ofSparse_apply, id,
    getD_map_nil (loCols k) rfl, sparseGet_loCols k _ j.is_lt]
  simp [blockEquiv]

/-- The last `r` columns of a split matrix, read from sparse rows. -/
theorem realOfSparse_hiCols {k r N n : ℕ} (h : k + r = N) (X : List (List (ℕ × ℚ))) :
    ((realOfSparse n N X).submatrix id (blockEquiv h).symm).toCols₂ =
      realOfSparse n r (X.map (hiCols k)) := by
  ext i j
  simp only [toCols₂_apply, submatrix_apply, map_apply, ofSparse_apply, id,
    getD_map_nil (hiCols k) rfl, sparseGet_hiCols]
  simp [blockEquiv]

theorem length_subSparse :
    ∀ X Y : List (List (ℕ × ℚ)), (subSparse X Y).length = max X.length Y.length
  | r :: rs, s :: ss => by simp [subSparse, length_subSparse rs ss]
  | rs, [] => by cases rs <;> simp [subSparse]
  | [], s :: ss => by simp [subSparse]

/-- Sparse rows that `eqSparse` identifies have the same real matrix. -/
theorem realOfSparse_eq_of_eqSparse {m n : ℕ} {X Y : List (List (ℕ × ℚ))}
    (h : eqSparse X Y = true) : realOfSparse m n X = realOfSparse m n Y :=
  congrArg (Matrix.map · _) (ofSparse_eq_of_eqSparse h)

/-- The rows of `-X`. -/
@[expose] def negSparse (X : List (List (ℕ × ℚ))) : List (List (ℕ × ℚ)) :=
  X.map (sparseMap fun x => -x)

theorem realOfSparse_negSparse {m n : ℕ} (X : List (List (ℕ × ℚ))) :
    realOfSparse m n (negSparse X) = -realOfSparse m n X := by
  ext i j
  simp only [negSparse, realOfSparse, map_apply, ofSparse_apply, Matrix.neg_apply,
    getD_map_nil _ (rfl : sparseMap (fun x : ℚ => -x) [] = []),
    sparseGet_sparseMap neg_zero (fun a b => neg_add a b), Rat.cast_neg]

end Rows

/-! ### Realizations -/

namespace SparseDecouplingCert

/-- `N × k`: the sparse rows of `Q₁ = U₁ - U₂ K`, the unknowns from the differential
coordinates. -/
@[expose] def stateRows (d : SparseDecouplingCert) : List (List (ℕ × ℚ)) :=
  subSparse (d.U.map (loCols d.k)) (sparseMul (d.U.map (hiCols d.k)) d.K)

variable {d : SparseDecouplingCert} {N m : ℕ} {E F : List (List (ℕ × ℚ))}
  {S : DescriptorSystem (Fin N) (Fin m)}

private theorem K_length (h : d.check N E F = true) : d.K.length = d.r := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h.2.2.2.2.2.2.1

/-- The unknowns of an accepted decoupling from its differential coordinates are
`Q₁ = U₁ - U₂ K`. -/
theorem Q₁_toDecoupling (hE : S.E = realOfSparse N N E) (hF : S.F = realOfSparse N N F)
    (h : d.check N E F = true) :
    (toDecoupling hE hF h).Q₁ = realOfSparse N d.k d.stateRows := by
  unfold toDecoupling
  rw [DescriptorSystem.IndexOneDecoupling.Q₁_ofSchur, stateRows, realOfSparse_sub,
    realOfSparse_mul _ _ (K_length h).le, realOfSparse_loCols, realOfSparse_hiCols]

end SparseDecouplingCert

/-- The input data of a proper realization through a structured decoupling: sparse solutions
`W = P₂ G` (`r × m`) and `B = P₁ G` (`k × m`); see the module documentation. -/
structure SparseRealizationCert where
  /-- `r × m`: the solution of `F₂₂ W = T₂ G`. -/
  W : List (List (ℕ × ℚ))
  /-- `k × m`: the solution of `E₁₁ B = T₁ G - F₁₂ W`, the input matrix of the reduced system. -/
  B : List (List (ℕ × ℚ))

namespace SparseRealizationCert

variable (e : SparseRealizationCert) (d : SparseDecouplingCert)

/-- Whether `e` gives the input maps of the decoupling `d` for the input matrix `G`, given by
sparse rows with at most `N` rows. -/
@[expose] def check (N : ℕ) (E F G : List (List (ℕ × ℚ))) : Bool :=
  Nat.ble G.length N && e.W.length == d.r && e.B.length == d.k &&
  eqSparse (sparseMul (blk₂₂ d.k (d.bar F)) e.W) (sparseMul (d.T.drop d.k) G) &&
  eqSparse (sparseMul (blk₁₁ d.k (d.bar E)) e.B)
    (subSparse (sparseMul (d.T.take d.k) G) (sparseMul (blk₁₂ d.k (d.bar F)) e.W))

/-- `N × m`: the sparse rows of `Q₂ P₂ G = U₂ W`, the response of the unknowns to the input. -/
@[expose] def inputRows : List (List (ℕ × ℚ)) := sparseMul (d.U.map (hiCols d.k)) e.W

/-- `p × k`: the output matrix `C = H Q₁` for output rows `H`. -/
@[expose] def outputRows (H : List (List (ℕ × ℚ))) : List (List (ℕ × ℚ)) :=
  sparseMul H d.stateRows

/-- `p × m`: the direct feedthrough `D = -H Q₂ P₂ G` for output rows `H`. -/
@[expose] def feedthroughRows (H : List (List (ℕ × ℚ))) : List (List (ℕ × ℚ)) :=
  negSparse (sparseMul H (e.inputRows d))

variable {e d} {N m : ℕ} {E F G : List (List (ℕ × ℚ))} {S : DescriptorSystem (Fin N) (Fin m)}

private theorem facts (hG : S.G = realOfSparse N m G) (hd : d.check N E F = true)
    (h : e.check d N E F G = true) :
    realOfSparse d.r d.r (blk₂₂ d.k (d.bar F)) * realOfSparse d.r m e.W =
        ((realOfSparse N N d.T).submatrix (blockEquiv (d.spec hd).hN).symm id).toRows₂ * S.G ∧
      realOfSparse d.k d.k (blk₁₁ d.k (d.bar E)) * realOfSparse d.k m e.B =
        ((realOfSparse N N d.T).submatrix (blockEquiv (d.spec hd).hN).symm id).toRows₁ * S.G -
          realOfSparse d.k d.r (blk₁₂ d.k (d.bar F)) * realOfSparse d.r m e.W ∧
      e.W.length = d.r ∧ G.length ≤ N := by
  simp only [check, Bool.and_eq_true, beq_iff_eq, Nat.ble_eq] at h
  obtain ⟨⟨⟨⟨hGl, hWl⟩, hBl⟩, hW⟩, hB⟩ := h
  refine ⟨?_, ?_, hWl, hGl⟩
  · rw [← SparseDecouplingCert.realOfSparse_mul _ _ hWl.le, realOfSparse_eq_of_eqSparse hW,
      SparseDecouplingCert.realOfSparse_mul _ _ hGl, realOfSparse_drop, hG]
  · rw [← SparseDecouplingCert.realOfSparse_mul _ _ hBl.le,
      realOfSparse_eq_of_eqSparse hB, SparseDecouplingCert.realOfSparse_sub,
      SparseDecouplingCert.realOfSparse_mul _ _ hGl,
      SparseDecouplingCert.realOfSparse_mul _ _ hWl.le, realOfSparse_take, hG]

/-- **The input maps of an accepted structured decoupling.** `Q₂ P₂ G` is the matrix of
`inputRows` and the input matrix `P₁ G` of the reduced system is the matrix of `e.B`. -/
theorem Q₂_P₂_G_toDecoupling (hE : S.E = realOfSparse N N E) (hF : S.F = realOfSparse N N F)
    (hG : S.G = realOfSparse N m G) (hd : d.check N E F = true)
    (h : e.check d N E F G = true) :
    (SparseDecouplingCert.toDecoupling hE hF hd).Q₂ *
        (SparseDecouplingCert.toDecoupling hE hF hd).P₂ * S.G = realOfSparse N m (e.inputRows d) ∧
      (SparseDecouplingCert.toDecoupling hE hF hd).B = realOfSparse d.k m e.B := by
  obtain ⟨hW, hB, hWl, -⟩ := facts hG hd h
  obtain ⟨h₁, h₂⟩ := DescriptorSystem.IndexOneDecoupling.P₂_G_B_ofSchur (S := S) _ _ _ _ _ _ _ _ _
    _ _ (d.spec hd).hT (d.spec hd).hU (hE ▸ (d.spec hd).hE) (hF ▸ (d.spec hd).hF)
    (d.spec hd).hE₁₁ (d.spec hd).hF₂₂ (d.spec hd).hK hW hB
  refine ⟨?_, h₂⟩
  rw [Matrix.mul_assoc]
  unfold SparseDecouplingCert.toDecoupling
  rw [h₁, DescriptorSystem.IndexOneDecoupling.Q₂_ofSchur, realOfSparse_hiCols, inputRows,
    SparseDecouplingCert.realOfSparse_mul _ _ hWl.le]

/-- **The checked proper realization of a structured decoupling.** For an accepted structured
decoupling `d` with accepted input data `e` and output rows `H`, the realization
`ẋ = A x + B u`, `y = C x + D u` of `DescriptorSystem.IndexOneDecoupling.realization` has the
matrices of `d.A`, `e.B`, `outputRows` (`C = H Q₁`) and `feedthroughRows` (`D = -H Q₂ P₂ G`). -/
theorem realization_toDecoupling (hE : S.E = realOfSparse N N E)
    (hF : S.F = realOfSparse N N F) (hG : S.G = realOfSparse N m G)
    (hd : d.check N E F = true) (h : e.check d N E F G = true) (p : ℕ)
    (H : List (List (ℕ × ℚ))) :
    (SparseDecouplingCert.toDecoupling hE hF hd).realization (realOfSparse p N H) =
      { A := realOfRows d.k d.k d.A, B := realOfSparse d.k m e.B
        C := realOfSparse p d.k (outputRows d H)
        D := realOfSparse p m (e.feedthroughRows d H) } := by
  have hl : d.stateRows.length ≤ N := by
    simp only [SparseDecouplingCert.check, Bool.and_eq_true, beq_iff_eq] at hd
    simp only [SparseDecouplingCert.stateRows, length_subSparse, List.length_map,
      length_sparseMul]
    omega
  have hi : (e.inputRows d).length ≤ N := by
    simp only [SparseDecouplingCert.check, Bool.and_eq_true, beq_iff_eq] at hd
    simp only [inputRows, length_sparseMul, List.length_map]
    omega
  obtain ⟨h₁, h₂⟩ := Q₂_P₂_G_toDecoupling hE hF hG hd h
  simp only [Matrix.mul_assoc] at h₁
  simp only [DescriptorSystem.IndexOneDecoupling.realization,
    SparseDecouplingCert.A_toDecoupling, h₂, SparseDecouplingCert.Q₁_toDecoupling, outputRows,
    feedthroughRows, realOfSparse_negSparse, Matrix.mul_assoc, h₁,
    SparseDecouplingCert.realOfSparse_mul _ _ hl,
    SparseDecouplingCert.realOfSparse_mul (l := p) H (e.inputRows d) hi]

end SparseRealizationCert

/-! ### Equilibria -/

/-- The sparse rows of the column vector `v`. -/
@[expose] def colSparse (v : List ℚ) : List (List (ℕ × ℚ)) := v.map fun x => [(0, x)]

/-- Whether `z₀` is an equilibrium, `F z₀ + b = 0`, of the system with `N` unknowns and sparse
rows `F`: one sparse product. -/
@[expose] def isEquilibriumSparse (N : ℕ) (F : List (List (ℕ × ℚ))) (b z₀ : List ℚ) : Bool :=
  Nat.ble z₀.length N && eqSparse (sparseMul F (colSparse z₀)) (colSparse (b.map fun x => -x))

private theorem realOfSparse_colSparse (N : ℕ) (v : List ℚ) (i : Fin N) :
    realOfSparse N 1 (colSparse v) i 0 = realOfList N v i := by
  simp only [realOfSparse, map_apply, ofSparse_apply, colSparse, realOfList, ofList_apply]
  rcases Nat.lt_or_ge (i : ℕ) v.length with hi | hi
  · simp [List.getD_eq_getElem?_getD, hi, sparseGet_cons]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

/-- **Soundness of the sparse equilibrium check.** -/
theorem isEquilibrium_of_isEquilibriumSparse {N m : ℕ} {S : DescriptorSystem (Fin N) (Fin m)}
    {F : List (List (ℕ × ℚ))} {b z₀ : List ℚ} (hF : S.F = realOfSparse N N F)
    (hb : S.b = realOfList N b) (h : isEquilibriumSparse N F b z₀ = true) :
    S.IsEquilibrium (realOfList N z₀) := by
  simp only [isEquilibriumSparse, Bool.and_eq_true, Nat.ble_eq] at h
  have hm := realOfSparse_eq_of_eqSparse (m := N) (n := 1) h.2
  rw [SparseDecouplingCert.realOfSparse_mul _ _ (by simpa [colSparse] using h.1)] at hm
  change S.F *ᵥ realOfList N z₀ + S.b = 0
  funext i
  have hi := congrFun (congrFun hm i) 0
  rw [Matrix.mul_apply, realOfSparse_colSparse] at hi
  have hb' := realOfSparse_colSparse N (b.map fun x => -x) i
  rw [hF, hb, Pi.add_apply, Pi.zero_apply, mulVec, dotProduct]
  simp only [realOfSparse_colSparse] at hi
  rw [hi]
  simp only [realOfList, ofList_apply, List.getD_eq_getElem?_getD, List.getElem?_map]
  rcases b[(i : ℕ)]? <;> simp

end Cslib.LinearAlgebra
