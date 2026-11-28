/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Unitary extension and polar decomposition of matrices

An isometry `V : n × ι`, `Vᴴ V = 1`, whose columns are placed at injective positions extends to a
unitary (`Matrix.exists_unitary_extension`): extend the orthonormal columns to an orthonormal
basis. Consequently a square matrix `y : m × n` with `|m| = |n|` has a **polar decomposition**
`y = R |y|` with `R` unitary and `|y| ≥ 0`, `|y|² = yᴴ y` (`Matrix.exists_polar`): in an eigenbasis
of `yᴴ y` the columns of `y` are orthogonal, the normalized nonzero ones form an isometry, and
`R` extends it.

## Main results

* `Matrix.exists_unitary_extension`: an isometry extends to a unitary.
* `Matrix.exists_polar`: polar decomposition of a square matrix; `yᴴ y ≤ 1` gives `|y| ≤ 1`.
* `Matrix.IsHermitian.exists_isometry_of_mul_self`: a Hermitian projection is `E Eᴴ` for an
  isometry `E`.
-/

public section

open Finset
open scoped ComplexOrder MatrixOrder

namespace Matrix

/-- **Unitary extension of an isometry**: if the columns of `V : n × ι` are orthonormal and
`j : ι → n` is injective, some unitary `U` has the columns of `V` at the positions `j i`. -/
theorem exists_unitary_extension {n ι : Type*} [Fintype n] [DecidableEq n] [DecidableEq ι]
    (V : Matrix n ι ℂ) (hV : Vᴴ * V = 1) {j : ι → n}
    (hj : Function.Injective j) : ∃ U ∈ unitaryGroup n ℂ, ∀ k i, U k (j i) = V k i := by
  classical
  set v : n → EuclideanSpace ℂ n := fun m =>
    if h : ∃ i, j i = m then WithLp.toLp 2 fun k => V k h.choose else 0
  have hvj : ∀ i, v (j i) = WithLp.toLp 2 fun k => V k i := fun i => by
    have h : ∃ i', j i' = j i := ⟨i, rfl⟩
    have hc : h.choose = i := hj h.choose_spec
    simp only [v, h, ↓reduceDIte, hc]
  have hv' : Orthonormal ℂ fun i => v (j i) := by
    rw [orthonormal_iff_ite]
    intro i i'
    have h : ∑ k, star (V k i) * V k i' = if i = i' then 1 else 0 := by
      have := congrFun (congrFun hV i) i'
      simpa [Matrix.mul_apply, Matrix.one_apply] using this
    rw [hvj, hvj, ← h]
    simp only [PiLp.inner_apply, RCLike.inner_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hv : Orthonormal ℂ ((Set.range j).domRestrict v) := by
    convert hv'.comp _ (Equiv.ofInjective j hj).symm.injective
    ext1 ⟨m, hm⟩
    simp [Equiv.apply_ofInjective_symm]
  obtain ⟨b, hb⟩ := hv.exists_orthonormalBasis_extension_of_card_eq
    (by rw [finrank_euclideanSpace])
  refine ⟨(EuclideanSpace.basisFun n ℂ).toBasis.toMatrix b,
    OrthonormalBasis.toMatrix_orthonormalBasis_mem_unitary _ _, fun k i => ?_⟩
  rw [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, hb (j i) (Set.mem_range_self i), hvj]

/-- Unitary diagonalization of a Hermitian matrix, with `Uᴴ` on the right. -/
private theorem exists_unitary_eq_diagonal {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : ∃ U : Matrix n n ℂ, Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧
      A = U * diagonal (fun k => (hA.eigenvalues k : ℂ)) * Uᴴ := by
  refine ⟨hA.eigenvectorUnitary, ?_, ?_, ?_⟩
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_star_mul_self _
  · rw [← star_eq_conjTranspose]; exact Unitary.coe_mul_star_self _
  · conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose, Function.comp_def]


/-- **Polar decomposition** of a square matrix `y : m × n`, `|m| = |n|`: a unitary `R` and
`h = |y| ≥ 0` with `h² = yᴴ y` and `y = R h`; if `yᴴ y ≤ 1` then `h ≤ 1`. -/
theorem exists_polar {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (y : Matrix m n ℂ) (hmn : Fintype.card m = Fintype.card n) :
    ∃ (R : Matrix m n ℂ) (h : Matrix n n ℂ), Rᴴ * R = 1 ∧ R * Rᴴ = 1 ∧ h.PosSemidef ∧
      h * h = yᴴ * y ∧ y = R * h ∧ (yᴴ * y ≤ 1 → h ≤ 1) := by
  classical
  set B := yᴴ * y
  have hB : B.PosSemidef := posSemidef_conjTranspose_mul_self y
  set μ := hB.1.eigenvalues
  have hμ0 : ∀ k, 0 ≤ μ k := hB.eigenvalues_nonneg
  obtain ⟨U, hU1, hU2, hBU⟩ := exists_unitary_eq_diagonal hB.1
  set s : n → ℝ := fun k => √(μ k)
  have hss : ∀ k, s k * s k = μ k := fun k => Real.mul_self_sqrt (hμ0 k)
  set Y := y * U
  -- Columns of `Y` are orthogonal with squared norms `μ`.
  have hYY : Yᴴ * Y = diagonal (fun k => (μ k : ℂ)) := by
    have hYB : Yᴴ * Y = Uᴴ * B * U := by simp only [Y, B, conjTranspose_mul, Matrix.mul_assoc]
    rw [hYB, hBU]
    simp only [← Matrix.mul_assoc, hU1, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
  have hcol : ∀ k l, ∑ i, star (Y i k) * Y i l = if k = l then (μ k : ℂ) else 0 := fun k l => by
    simpa [Matrix.mul_apply, diagonal_apply] using congrFun (congrFun hYY k) l
  have hY0 : ∀ k, μ k = 0 → ∀ i, Y i k = 0 := fun k hk i => by
    have h0 : ∑ i, star (Y i k) * Y i k = 0 := by
      rw [hcol, ite_eq_left rfl, hk, Complex.ofReal_zero]
    have hn (i : m) : star (Y i k) * Y i k = ((‖Y i k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [hn, ← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h0
    simpa using (sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg ‖Y i k‖).mp h0 i (mem_univ i)
  -- The normalized nonzero columns form an isometry.
  let P := {k : n // μ k ≠ 0}
  let W : Matrix m P ℂ := Matrix.of fun i k => Y i k.val / (s k.val : ℂ)
  have hs0 : ∀ k : P, (s k.val : ℂ) ≠ 0 := fun k => by
    rw [Complex.ofReal_ne_zero]
    exact (Real.sqrt_pos.mpr (lt_of_le_of_ne (hμ0 k.val) (Ne.symm k.property))).ne'
  have hW : Wᴴ * W = 1 := by
    ext k l
    simp only [Matrix.mul_apply, conjTranspose_apply, W, Matrix.of_apply, Matrix.one_apply]
    have : ∀ i, star (Y i k.val / (s k.val : ℂ)) * (Y i l.val / (s l.val : ℂ)) =
        (star (Y i k.val) * Y i l.val) / ((s k.val : ℂ) * (s l.val : ℂ)) := fun i => by
      rw [star_div₀, Complex.star_def, Complex.conj_ofReal]; ring
    simp only [this, ← sum_div, hcol]
    by_cases hkl : k = l
    · subst hkl
      rw [ite_eq_left rfl, ite_eq_left rfl, ← Complex.ofReal_mul, hss, div_self]
      exact_mod_cast k.property
    · rw [ite_eq_right (fun h => absurd (Subtype.ext h) hkl), ite_eq_right (absurd · hkl), zero_div]
  -- Extend to a unitary and reindex.
  let σ : n ≃ m := Fintype.equivOfCardEq hmn.symm
  obtain ⟨U', hU', hU'W⟩ := exists_unitary_extension W hW
    (j := fun k : P => σ k.val) (fun a b hab => Subtype.ext (σ.injective hab))
  have hU'1 : U'ᴴ * U' = 1 := by
    rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff'.mp hU')
  have hU'2 : U' * U'ᴴ = 1 := by
    rw [← star_eq_conjTranspose]; exact (mem_unitaryGroup_iff.mp hU')
  set R' : Matrix m n ℂ := U'.submatrix id σ
  have hR'1 : R'ᴴ * R' = 1 := by
    ext k l
    have := congrFun (congrFun hU'1 (σ k)) (σ l)
    simpa [Matrix.mul_apply, R', Matrix.one_apply, σ.injective.eq_iff] using this
  have hR'2 : R' * R'ᴴ = 1 := by
    ext i i'
    have := congrFun (congrFun hU'2 i) i'
    simp only [Matrix.mul_apply, conjTranspose_apply, R', submatrix_apply, id] at this ⊢
    rw [← this]
    exact σ.sum_comp (fun j => U' i j * star (U' i' j))
  have hR'Y : R' * diagonal (fun k => (s k : ℂ)) = Y := by
    ext i k
    rw [mul_diagonal]
    by_cases hk : μ k = 0
    · rw [hY0 k hk i]
      simp [s, hk]
    · have h1 := hU'W i ⟨k, hk⟩
      simp only [R', submatrix_apply, id, W, Matrix.of_apply] at h1 ⊢
      rw [h1, div_mul_cancel₀ _ (hs0 ⟨k, hk⟩)]
  set h := U * diagonal (fun k => (s k : ℂ)) * Uᴴ
  refine ⟨R' * Uᴴ, h, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc R'ᴴ,
      hR'1, Matrix.one_mul, hU2]
  · rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ,
      hU1, Matrix.one_mul, hR'2]
  · exact (posSemidef_diagonal_iff.mpr fun k =>
      Complex.zero_le_real.mpr (Real.sqrt_nonneg _)).mul_mul_conjTranspose_same U
  · have : h * h = U * diagonal (fun k => (μ k : ℂ)) * Uᴴ := by
      simp only [h, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Uᴴ U, hU1, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _),
        diagonal_mul_diagonal]
      congr 3
      ext k
      rw [← Complex.ofReal_mul, hss]
    rw [this, hBU]
  · simp only [h, ← Matrix.mul_assoc]
    rw [Matrix.mul_assoc R', hU1, Matrix.mul_one, hR'Y, Matrix.mul_assoc, hU2, Matrix.mul_one]
  · intro hB1
    have hd : (1 - diagonal (fun k => (μ k : ℂ))).PosSemidef := by
      have := (Matrix.le_iff.mp hB1).conjTranspose_mul_mul_same U
      rwa [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU1, hBU, ← Matrix.mul_assoc,
        ← Matrix.mul_assoc, hU1, Matrix.one_mul, Matrix.mul_assoc, hU1, Matrix.mul_one] at this
    have hμ1 (k : n) : μ k ≤ 1 := by
      have h' := hd.diag_nonneg (i := k)
      rw [Matrix.sub_apply, one_apply_eq, diagonal_apply_eq, ← Complex.ofReal_one,
        ← Complex.ofReal_sub, Complex.zero_le_real] at h'
      linarith
    rw [Matrix.le_iff]
    have e : 1 - h = U * diagonal (fun k => ((1 - s k : ℝ) : ℂ)) * Uᴴ := by
      have ed : diagonal (fun k => ((1 - s k : ℝ) : ℂ)) = 1 - diagonal (fun k => (s k : ℂ)) := by
        ext i j; by_cases hij : i = j <;> simp [hij]
      rw [ed, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU2]
    rw [e]
    refine (posSemidef_diagonal_iff.mpr fun k =>
      Complex.zero_le_real.mpr ?_).mul_mul_conjTranspose_same U
    linarith [Real.sqrt_le_one.mpr (hμ1 k)]

/-- A Hermitian projection factors through an isometry: `P = E Eᴴ` with `Eᴴ E = 1`, where the
columns of `E` are the eigenvectors of `P` for the eigenvalue `1`. -/
theorem IsHermitian.exists_isometry_of_mul_self {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (hAA : A * A = A) :
    ∃ L : Finset n, ∃ E : Matrix n L ℂ, Eᴴ * E = 1 ∧ E * Eᴴ = A := by
  obtain ⟨U, hU1, hU2, hUd⟩ := exists_unitary_eq_diagonal hA
  set lam := hA.eigenvalues
  have hD : Uᴴ * A * U = diagonal fun k => (lam k : ℂ) := by
    rw [hUd]
    simp only [← Matrix.mul_assoc, hU1, Matrix.one_mul]
    rw [Matrix.mul_assoc, hU1, Matrix.mul_one]
  have hlam : ∀ k, lam k * lam k = lam k := fun k => by
    have h := congrArg (fun M => Uᴴ * M * U) hAA
    have e : Uᴴ * (A * A) * U =
        (Uᴴ * A * U) * (Uᴴ * A * U) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc U Uᴴ, hU2, Matrix.one_mul]
    rw [e, hD, diagonal_mul_diagonal] at h
    have := congrFun (congrFun h k) k
    simp only [diagonal_apply_eq] at this
    exact_mod_cast this
  have hl01 : ∀ k, lam k ≠ 1 → lam k = 0 := fun k hk => by
    have := hlam k
    have : lam k * (lam k - 1) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd (by linarith) hk
  refine ⟨univ.filter fun k => lam k = 1, Matrix.of fun i k => U i k.val, ?_, ?_⟩
  · ext k k'
    have := congrFun (congrFun hU1 k.val) k'.val
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, Matrix.one_apply] at this ⊢
    rw [this]
    exact if_congr Subtype.ext_iff.symm rfl rfl
  · ext i j
    rw [hUd]
    simp only [Matrix.mul_apply, conjTranspose_apply, Matrix.of_apply, diagonal_apply,
      mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    rw [Finset.sum_coe_sort (univ.filter fun k => lam k = 1)
      (fun k => U i k * star (U j k)), Finset.sum_filter]
    refine sum_congr rfl fun k _ => ?_
    split_ifs with hk
    · rw [hk]; push_cast; ring
    · rw [hl01 k hk]; push_cast; ring

end Matrix
