/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Algebra.DFT
public import CslibFrontier.Foundations.Combinatorics.Expander.Cayley
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.GroupCirculant.Eigenvalues
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.KroneckerRank
public import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
public import Mathlib.LinearAlgebra.Matrix.Circulant
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Foundations.Data.BitString.Neg
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Rank

/-!
# Group-circulant spectra, character matrices, and Boolean-cube diagonalization

For a finite additive abelian group `G` and weight function `w : G → R`, Mathlib's
`Matrix.circulant w : Matrix G G R` has `(x, y)`-entry `w (x - y)`. Every additive character
`ψ : AddChar G R` is an eigenvector of `Matrix.circulant w` with eigenvalue
`Matrix.circulantEigenvalue w ψ = ∑ g : G, w g * ψ (-g)` (`Matrix.circulant_mulVec_addChar`),
and multiplication of group-circulant matrices corresponds to pointwise multiplication of these
character eigenvalues (`Matrix.circulantEigenvalue_mulVec`).

Assembling the characters as columns of `Matrix.addCharMatrix G L` and conjugate rows of
`Matrix.dualAddCharMatrix G L` diagonalizes `Matrix.circulant w` over any field `L` with
`(Fintype.card G : L) ≠ 0` and `Fintype.card (AddChar G L) = Fintype.card G` (a character-splitting
field for `G`), yielding `(Matrix.circulant w).rank = Nat.card {ψ // circulantEigenvalue w ψ ≠ 0}`
(`Matrix.rank_circulant_of_card_addChar_eq`, and finset-cardinality form
`Matrix.rank_circulant_eq_card_filter`). Combining Pontryagin duality (`AddChar.card_eq`) with
`Matrix.rank_map_of_field` (`CslibFrontier/Foundations/LinearAlgebra/Matrix/Rank.lean`) gives
`Matrix.rank_circulant_of_field_hom`, `Matrix.rank_circulant_complex`,
`Matrix.rank_circulant_rat`, and `Matrix.rank_circulant_real`.

On the Boolean cube `ι → Bool`, the character (Walsh–Hadamard) matrix `Matrix.cubeCharMatrix R ι`
factors on `Fin n → Bool` as the `n`-th Kronecker power
`Matrix.kroneckerPow (Matrix.sylvesterTwo R) n` (`Matrix.cubeCharMatrix_eq_kroneckerPow`),
satisfies `cubeCharMatrix R ι * cubeCharMatrix R ι = (2 ^ Fintype.card ι : R) • 1`
(`Matrix.cubeCharMatrix_mul_self`), and diagonalizes every Boolean-cube circulant directly over any
field `K` with `(2 : K) ≠ 0` (`Matrix.rank_circulant_cube`). Specialization lemmas connect
Boolean-cube circulants to the walk operator and generator bias of `Cslib.RotationMap.cubeCayley`
(`Matrix.cubeCayley_walk_eq_circulant_mulVec`, `Matrix.circulantEigenvalue_cubeCayleyWeight`) and
cyclic circulants on `Fin n` to `Cslib.dft` (`Matrix.circulant_mulVec_pow_eq_dft_smul`).

## Main definitions

* `Matrix.circulantEigenvalue`, defined in
  `CslibFrontier/Foundations/LinearAlgebra/Matrix/GroupCirculant/Eigenvalues.lean`: eigenvalue
  `∑ g, w g * ψ (-g)` of `Matrix.circulant w` on `ψ`.
* `Matrix.addCharMatrix`, `Matrix.dualAddCharMatrix`: character and dual-character matrices on `G`.
* `Matrix.sylvesterTwo`, `Matrix.cubeCharMatrix`: `2 × 2` Sylvester kernel and Walsh–Hadamard
  Boolean-cube character matrix.
* `Matrix.cubeCayleyWeight`: transition weight vector realizing `(cubeCayley s).walk` as a
  Boolean-cube circulant.

## Main results

* `Matrix.circulant_mulVec_addChar` and `Matrix.circulantEigenvalue_mulVec`, proved in
  `CslibFrontier/Foundations/LinearAlgebra/Matrix/GroupCirculant/Eigenvalues.lean`: character
  eigenpairs and convolution multiplicativity.
* `Matrix.circulant_mul_addCharMatrix`, `Matrix.dualAddCharMatrix_mul_addCharMatrix`,
  `Matrix.diagonalize_circulant_of_card_addChar_eq`: character-matrix orthogonality and similarity
  diagonalization.
* `Matrix.rank_circulant_of_card_addChar_eq`, `Matrix.rank_circulant_eq_card_filter`,
  `Matrix.rank_circulant_of_rank_map_eq`, `Matrix.rank_circulant_complex`: rank equals the count
  of nonzero character eigenvalues.
* `Matrix.cubeCharMatrix_eq_kroneckerPow`, `Matrix.cubeCharMatrix_mul_self`,
  `Matrix.rank_cubeCharMatrix`, `Matrix.rank_circulant_cube`: Walsh–Hadamard Kronecker power,
  orthogonality, and Boolean-cube circulant rank in characteristic `≠ 2`.
* `Matrix.cubeCayley_walk_eq_circulant_mulVec`, `Matrix.circulantEigenvalue_cubeCayleyWeight`,
  `Matrix.circulant_mulVec_pow_eq_dft_smul`: bridges to `Cslib.RotationMap.cubeCayley` and
  `Cslib.dft`.
-/

public section

namespace Matrix

open Finset
open scoped BigOperators

/-! ### Character matrices, diagonalization, and rank over splitting fields and `ℂ` -/

section Diagonalization

/-- Matrix whose columns are the additive characters `ψ : AddChar G R` evaluated on `G`. -/
@[expose] def addCharMatrix (G R : Type*) [AddCommGroup G] [CommMonoid R] :
    Matrix G (AddChar G R) R :=
  of fun g ψ => ψ g

/-- Dual character matrix with `(ψ, g)`-entry `ψ (-g)`. -/
@[expose] def dualAddCharMatrix (G R : Type*) [AddCommGroup G] [CommMonoid R] :
    Matrix (AddChar G R) G R :=
  of fun ψ g => ψ (-g)

@[simp]
theorem addCharMatrix_apply {G R : Type*} [AddCommGroup G] [CommMonoid R]
    (g : G) (ψ : AddChar G R) :
    addCharMatrix G R g ψ = ψ g :=
  rfl

@[simp]
theorem dualAddCharMatrix_apply {G R : Type*} [AddCommGroup G] [CommMonoid R]
    (ψ : AddChar G R) (g : G) :
    dualAddCharMatrix G R ψ g = ψ (-g) :=
  rfl

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- Right-multiplying `circulant w` by `addCharMatrix` scales each column `ψ` by
`circulantEigenvalue w ψ`. -/
theorem circulant_mul_addCharMatrix {R : Type*} [CommSemiring R] [Fintype (AddChar G R)]
    [DecidableEq (AddChar G R)] (w : G → R) :
    circulant w * addCharMatrix G R =
      addCharMatrix G R * diagonal (circulantEigenvalue w) := by
  ext x ψ
  rw [mul_diagonal]
  simpa [Matrix.mul_apply, mulVec, dotProduct, mul_comm] using
    congrFun (circulant_mulVec_addChar w ψ) x

/-- Character orthogonality in matrix form: `dualAddCharMatrix * addCharMatrix = |G| • 1` over any
integral domain. -/
theorem dualAddCharMatrix_mul_addCharMatrix {R : Type*} [CommRing R] [IsDomain R]
    [DecidableEq (AddChar G R)] :
    dualAddCharMatrix G R * addCharMatrix G R =
      (Fintype.card G : R) • (1 : Matrix (AddChar G R) (AddChar G R) R) := by
  ext ψ χ
  rw [Matrix.mul_apply]
  simp only [dualAddCharMatrix_apply, addCharMatrix_apply,
    show ∀ g : G, ψ (-g) * χ g = (χ - ψ) g from fun g => by rw [AddChar.sub_apply, mul_comm],
    AddChar.sum_eq_ite]
  simp [Matrix.one_apply, sub_eq_zero, eq_comm]

/-- **Similarity diagonalization of a group circulant** over any field `L` with
`(Fintype.card G : L) ≠ 0` and `Fintype.card (AddChar G L) = Fintype.card G`. -/
theorem diagonalize_circulant_of_card_addChar_eq {L : Type*} [Field L] [Fintype (AddChar G L)]
    [DecidableEq G] (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) (w : G → L) :
    let e : G ≃ AddChar G L := (Fintype.equivOfCardEq hcard).symm
    let P : Matrix G G L := (addCharMatrix G L).submatrix id e
    let Q : Matrix G G L := (Fintype.card G : L)⁻¹ • (dualAddCharMatrix G L).submatrix e id
    Q * P = 1 ∧ IsUnit P ∧ IsUnit Q ∧
      Q * circulant w * P = diagonal (fun g => circulantEigenvalue w (e g)) := by
  classical
  dsimp only
  let e : G ≃ AddChar G L := (Fintype.equivOfCardEq hcard).symm
  let P : Matrix G G L := (addCharMatrix G L).submatrix id e
  let Q : Matrix G G L := (Fintype.card G : L)⁻¹ • (dualAddCharMatrix G L).submatrix e id
  have hQP : Q * P = 1 := by
    dsimp only [Q, P]
    rw [smul_mul, show (dualAddCharMatrix G L).submatrix e id * (addCharMatrix G L).submatrix id e =
        (dualAddCharMatrix G L * addCharMatrix G L).submatrix e e by ext; simp [Matrix.mul_apply],
      dualAddCharMatrix_mul_addCharMatrix]
    ext
    simp [Matrix.one_apply, e.injective.eq_iff, inv_mul_cancel₀ hchar]
  have hdetQP : Q.det * P.det = 1 := by rw [← det_mul, hQP, det_one]
  refine ⟨hQP, (isUnit_iff_isUnit_det P).mpr (IsUnit.mk0 _ (right_ne_zero_of_mul_eq_one hdetQP)),
    (isUnit_iff_isUnit_det Q).mpr (IsUnit.mk0 _ (left_ne_zero_of_mul_eq_one hdetQP)), ?_⟩
  have hCP : circulant w * P = P * diagonal (fun g => circulantEigenvalue w (e g)) := by
    ext x g
    have hxg := congrFun (congrFun (circulant_mul_addCharMatrix w) x) (e g)
    rw [mul_diagonal] at hxg ⊢
    simpa [P, Matrix.mul_apply] using hxg
  rw [Matrix.mul_assoc, hCP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]

/-- **Rank of a group-circulant matrix over a character-splitting field**: when `AddChar G L` has
cardinality `|G|` and `(|G| : L) ≠ 0`, `(circulant w).rank` equals the number of characters with
nonzero eigenvalue. -/
theorem rank_circulant_of_card_addChar_eq {L : Type*} [Field L] [Fintype (AddChar G L)]
    (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) (w : G → L) :
    (circulant w).rank = Nat.card {ψ : AddChar G L // circulantEigenvalue w ψ ≠ 0} := by
  classical
  let e : G ≃ AddChar G L := (Fintype.equivOfCardEq hcard).symm
  obtain ⟨_, hPunit, hQunit, hdiag⟩ := diagonalize_circulant_of_card_addChar_eq hchar hcard w
  rw [← rank_mul_eq_right_of_isUnit_det _ (circulant w) ((isUnit_iff_isUnit_det _).mp hQunit),
    ← rank_mul_eq_left_of_isUnit_det _ _ ((isUnit_iff_isUnit_det _).mp hPunit), hdiag,
    rank_diagonal, Nat.card_eq_fintype_card]
  exact Fintype.card_congr (Equiv.subtypeEquiv e fun _ => Iff.rfl)

/-- Finset-cardinality form of `rank_circulant_of_card_addChar_eq` when `L` has decidable
equality. -/
theorem rank_circulant_eq_card_filter {L : Type*} [Field L] [DecidableEq L] [Fintype (AddChar G L)]
    (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) (w : G → L) :
    (circulant w).rank = #{ψ : AddChar G L | circulantEigenvalue w ψ ≠ 0} := by
  rw [rank_circulant_of_card_addChar_eq hchar hcard w, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

/-- **Rank of a group-circulant matrix via a rank-preserving scalar extension** `f : K →+* L` into
a character-splitting field `L`. -/
theorem rank_circulant_of_rank_map_eq {K L : Type*} [Field K] [Field L] [Fintype (AddChar G L)]
    (f : K →+* L) {w : G → K} (hrank : ((circulant w).map f).rank = (circulant w).rank)
    (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) :
    (circulant w).rank = Nat.card {ψ : AddChar G L // circulantEigenvalue (f ∘ w) ψ ≠ 0} := by
  rw [← hrank, map_circulant]
  exact rank_circulant_of_card_addChar_eq hchar hcard (f ∘ w)

/-- **Rank of a group-circulant matrix via scalar extension** along `f : K →+* L` into a
character-splitting field `L`, reusing `Matrix.rank_map_of_field`. -/
theorem rank_circulant_of_field_hom {K L : Type*} [Field K] [Field L] [Fintype (AddChar G L)]
    (f : K →+* L) (hchar : (Fintype.card G : L) ≠ 0)
    (hcard : Fintype.card (AddChar G L) = Fintype.card G) (w : G → K) :
    (circulant w).rank = Nat.card {ψ : AddChar G L // circulantEigenvalue (f ∘ w) ψ ≠ 0} :=
  rank_circulant_of_rank_map_eq f (rank_map_of_field f (circulant w)) hchar hcard

/-- **Rank of a complex group-circulant matrix**: `(circulant w).rank` equals the number of complex
characters with nonzero eigenvalue. -/
theorem rank_circulant_complex (w : G → ℂ) :
    (circulant w).rank = Nat.card {ψ : AddChar G ℂ // circulantEigenvalue w ψ ≠ 0} :=
  rank_circulant_of_card_addChar_eq (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    AddChar.card_eq w

/-- **Rank of a rational group-circulant matrix**: `(circulant w).rank` equals the number of
complex characters where `∑ g, (w g : ℂ) * ψ (-g) ≠ 0`. -/
theorem rank_circulant_rat (w : G → ℚ) :
    (circulant w).rank =
      Nat.card {ψ : AddChar G ℂ // circulantEigenvalue (fun g => (w g : ℂ)) ψ ≠ 0} :=
  rank_circulant_of_field_hom (Rat.castHom ℂ)
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) AddChar.card_eq w

/-- **Rank of a real group-circulant matrix**: `(circulant w).rank` equals the number of complex
characters where `∑ g, (w g : ℂ) * ψ (-g) ≠ 0`. -/
theorem rank_circulant_real (w : G → ℝ) :
    (circulant w).rank =
      Nat.card {ψ : AddChar G ℂ // circulantEigenvalue (fun g => (w g : ℂ)) ψ ≠ 0} :=
  rank_circulant_of_field_hom Complex.ofRealHom
    (Nat.cast_ne_zero.mpr Fintype.card_ne_zero) AddChar.card_eq w

end Diagonalization

/-! ### Boolean-cube character (Walsh–Hadamard) matrices and Kronecker powers -/

section BooleanCube

/-- The `2 × 2` Sylvester–Hadamard kernel `[[1, 1], [1, -1]]` indexed by `Bool`. -/
@[expose] def sylvesterTwo (R : Type*) [Ring R] : Matrix Bool Bool R :=
  of fun a b => if a && b then -1 else 1

@[simp]
theorem sylvesterTwo_apply {R : Type*} [Ring R] (a b : Bool) :
    sylvesterTwo R a b = if a && b then -1 else 1 :=
  rfl

/-- `sylvesterTwo R * sylvesterTwo R = 2 • 1` over any commutative ring. -/
theorem sylvesterTwo_mul_self (R : Type*) [CommRing R] :
    sylvesterTwo R * sylvesterTwo R = (2 : R) • (1 : Matrix Bool Bool R) := by
  ext a b
  rw [Matrix.mul_apply, Fintype.sum_bool]
  cases a <;> cases b <;> simp [sylvesterTwo] <;> ring

/-- The Walsh–Hadamard character matrix on the Boolean cube `ι → Bool`, with `(x, y)`-entry
`χ_{supp y}(x) = ∏_{i : y i} (-1)^{x i}`. -/
@[expose] def cubeCharMatrix (R ι : Type*) [CommRing R] [Fintype ι] :
    Matrix (ι → Bool) (ι → Bool) R :=
  of fun x y => Cslib.BitString.chi R (univ.filter fun i => y i = true) x

theorem cubeCharMatrix_apply {R ι : Type*} [CommRing R] [Fintype ι] (x y : ι → Bool) :
    cubeCharMatrix R ι x y = ∏ i : ι, sylvesterTwo R (x i) (y i) := by
  simp only [cubeCharMatrix, of_apply, Cslib.BitString.chi, prod_filter, sylvesterTwo_apply]
  refine prod_congr rfl fun i _ => ?_
  cases x i <;> cases y i <;> simp

/-- **Walsh–Hadamard Kronecker-power factorization**: on `Fin n → Bool`, `cubeCharMatrix R (Fin n)`
is identically the `n`-th Kronecker power of `sylvesterTwo R`. -/
theorem cubeCharMatrix_eq_kroneckerPow (R : Type*) [CommRing R] (n : ℕ) :
    cubeCharMatrix R (Fin n) = kroneckerPow (sylvesterTwo R) n := by
  ext x y
  rw [cubeCharMatrix_apply, kroneckerPow_apply]

/-- `cubeCharMatrix R ι` is symmetric. -/
theorem transpose_cubeCharMatrix (R ι : Type*) [CommRing R] [Fintype ι] :
    (cubeCharMatrix R ι)ᵀ = cubeCharMatrix R ι := by
  ext x y
  simp only [transpose_apply, cubeCharMatrix_apply, sylvesterTwo_apply, Bool.and_comm]

/-- **Orthogonality of the Boolean-cube character matrix** over any commutative ring:
`cubeCharMatrix R ι * cubeCharMatrix R ι = (2 ^ |ι| : R) • 1`. -/
theorem cubeCharMatrix_mul_self (R ι : Type*) [CommRing R] [Fintype ι] [DecidableEq ι] :
    cubeCharMatrix R ι * cubeCharMatrix R ι =
      ((2 : R) ^ Fintype.card ι) • (1 : Matrix (ι → Bool) (ι → Bool) R) := by
  ext x z
  rw [show (((2 : R) ^ Fintype.card ι) • (1 : Matrix (ι → Bool) (ι → Bool) R)) x z =
      if x = z then (2 : R) ^ Fintype.card ι else 0 by simp [Matrix.one_apply]]
  simp only [Matrix.mul_apply, cubeCharMatrix_apply, ← prod_mul_distrib]
  rw [← Fintype.prod_sum fun (i : ι) (b : Bool) => sylvesterTwo R (x i) b * sylvesterTwo R b (z i)]
  by_cases hxz : x = z
  · subst hxz
    have hpair (i : ι) : (∑ b : Bool, sylvesterTwo R (x i) b * sylvesterTwo R b (x i)) = 2 := by
      rw [Fintype.sum_bool]
      cases x i <;> simp [sylvesterTwo] <;> ring
    simp_rw [hpair]; simp
  · obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hxz
    rw [ite_eq_right hxz]
    refine prod_eq_zero (mem_univ i₀) ?_
    rw [Fintype.sum_bool]
    revert hi₀; cases x i₀ <;> cases z i₀ <;> simp [sylvesterTwo]

/-- Over any field of characteristic different from `2`, `cubeCharMatrix K ι` is invertible and has
full rank `2 ^ |ι|`. -/
theorem isUnit_cubeCharMatrix {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (h2 : (2 : K) ≠ 0) :
    IsUnit (cubeCharMatrix K ι) := by
  have hmul : (((2 : K) ^ Fintype.card ι)⁻¹ • cubeCharMatrix K ι) * cubeCharMatrix K ι = 1 := by
    rw [smul_mul, cubeCharMatrix_mul_self, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ h2), one_smul]
  exact (isUnit_iff_isUnit_det _).mpr
    (IsUnit.mk0 _ (right_ne_zero_of_mul_eq_one (by rw [← det_mul, hmul, det_one])))

theorem rank_cubeCharMatrix {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (h2 : (2 : K) ≠ 0) :
    (cubeCharMatrix K ι).rank = 2 ^ Fintype.card ι := by
  simpa using rank_of_isUnit (cubeCharMatrix K ι) (isUnit_cubeCharMatrix h2)

/-- Right-multiplying a Boolean-cube circulant `circulant w` by `cubeCharMatrix R ι` scales column
`y` by the Walsh–Hadamard eigenvalue `∑ x, w x * cubeCharMatrix R ι x y`. -/
theorem circulant_mul_cubeCharMatrix {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (w : (ι → Bool) → R) :
    circulant w * cubeCharMatrix R ι =
      cubeCharMatrix R ι * diagonal (fun y => ∑ x, w x * cubeCharMatrix R ι x y) := by
  ext x y
  let S : Finset ι := univ.filter fun i => y i = true
  rw [mul_diagonal, Matrix.mul_apply]
  change (circulant w *ᵥ ⇑(Cslib.BitString.chiChar R S)) x =
    cubeCharMatrix R ι x y * ∑ g, w g * cubeCharMatrix R ι g y
  rw [congrFun (circulant_mulVec_addChar w (Cslib.BitString.chiChar R S)) x, Pi.smul_apply,
    smul_eq_mul, circulantEigenvalue_of_symm fun g => by rw [Cslib.BitString.neg_eq_self],
    mul_comm]
  rfl

/-- **Rank of a Boolean-cube circulant** over any field `K` with `(2 : K) ≠ 0` (`ℚ`, `ℝ`, or odd
characteristic): `(circulant w).rank` equals the number of subsets `S : Finset ι` whose Walsh
transform `∑ x, w x * χ_S(x)` is nonzero. -/
theorem rank_circulant_cube {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [DecidableEq K]
    (h2 : (2 : K) ≠ 0) (w : (ι → Bool) → K) :
    (circulant w).rank =
      #{S : Finset ι | ∑ x : ι → Bool, w x * Cslib.BitString.chi K S x ≠ 0} := by
  let H := cubeCharMatrix K ι
  let Hinv := ((2 : K) ^ Fintype.card ι)⁻¹ • H
  have hHH : Hinv * H = 1 := by
    rw [smul_mul, cubeCharMatrix_mul_self, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ h2), one_smul]
  have hHinv_det : IsUnit Hinv.det :=
    IsUnit.mk0 _ (left_ne_zero_of_mul_eq_one (by rw [← det_mul, hHH, det_one]))
  rw [← rank_mul_eq_right_of_isUnit_det Hinv (circulant w) hHinv_det,
    ← rank_mul_eq_left_of_isUnit_det H _ ((isUnit_iff_isUnit_det H).mp (isUnit_cubeCharMatrix h2)),
    Matrix.mul_assoc, circulant_mul_cubeCharMatrix, ← Matrix.mul_assoc, hHH, Matrix.one_mul,
    rank_diagonal, Fintype.card_subtype]
  refine Finset.card_bij (fun y _ => univ.filter fun i => y i = true)
    (fun _ hy => mem_filter.mpr
      ⟨mem_univ _, by simpa [H, cubeCharMatrix] using (mem_filter.mp hy).2⟩)
    (fun _ _ _ _ h => funext fun i => Bool.eq_iff_iff.mpr <| by
      simpa only [mem_filter, mem_univ, true_and] using Finset.ext_iff.mp h i)
    fun S hS => ⟨fun i => decide (i ∈ S), mem_filter.mpr ⟨mem_univ _, ?_⟩, by ext; simp⟩
  simpa [H, cubeCharMatrix, show (univ.filter fun i => decide (i ∈ S) = true) = S by ext; simp]
    using (mem_filter.mp hS).2

end BooleanCube

/-! ### Bridges to Boolean-cube Cayley graphs (`Cslib.RotationMap.cubeCayley`) and cyclic DFT -/

section Bridges

/-- Normalized generator-multiplicity weight of `Cslib.RotationMap.cubeCayley s`. -/
@[expose] noncomputable def cubeCayleyWeight {ι : Type*} [Fintype ι] {d : ℕ}
    (s : Fin d → ι → Bool) (g : ι → Bool) : ℝ :=
  (#{j : Fin d | s j = g} : ℝ) / d

/-- The walk operator of `Cslib.RotationMap.cubeCayley s` acts as matrix-vector multiplication by
`Matrix.circulant (cubeCayleyWeight s)`. -/
theorem cubeCayley_walk_eq_circulant_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    (s : Fin d → ι → Bool) (f : (ι → Bool) → ℝ) :
    (Cslib.RotationMap.cubeCayley s).walk f = circulant (cubeCayleyWeight s) *ᵥ f := by
  funext u
  rw [Cslib.RotationMap.walk_apply]
  simp only [Cslib.RotationMap.cubeCayley_neighbor, Fintype.expect_eq_sum_div_card,
    Fintype.card_fin, mulVec, dotProduct, circulant_apply, cubeCayleyWeight]
  rw [sum_congr rfl fun y _ => show (#{j : Fin d | s j = u - y} : ℝ) / d * f y =
      ∑ j : Fin d, if s j = u - y then f y / d else 0 by
    rw [card_filter, Nat.cast_sum]
    simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero, sum_div, sum_mul, ite_div, zero_div,
      ite_mul, zero_mul]
    exact sum_congr rfl fun _ _ => by split_ifs <;> ring, sum_comm, sum_div]
  refine sum_congr rfl fun j _ => ?_
  have heq (y : ι → Bool) : (s j = u - y) ↔ (y = u + s j) := by
    rw [Cslib.BitString.sub_eq_add]
    exact ⟨fun h => by rw [h, ← add_assoc, Cslib.BitString.add_self, zero_add],
      fun h => by rw [h, ← add_assoc, Cslib.BitString.add_self, zero_add]⟩
  simp [heq]

/-- The character eigenvalue of `cubeCayleyWeight s` at `chiChar ℝ S` agrees with the generator
bias `Cslib.BitString.bias ((Cslib.Probability.PMF.uniformOfFintype (Fin d)).map s) S`. -/
theorem circulantEigenvalue_cubeCayleyWeight {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}
    [NeZero d] (s : Fin d → ι → Bool) (S : Finset ι) :
    circulantEigenvalue (cubeCayleyWeight s) (Cslib.BitString.chiChar ℝ S) =
      Cslib.BitString.bias ((Cslib.Probability.PMF.uniformOfFintype (Fin d)).map s) S := by
  have hw := congrFun (cubeCayley_walk_eq_circulant_mulVec s (Cslib.BitString.chi ℝ S)) 0
  rw [show Cslib.BitString.chi ℝ S = ⇑(Cslib.BitString.chiChar ℝ S) from rfl,
    circulant_mulVec_addChar] at hw
  have hw' : (Cslib.RotationMap.cubeCayley s).walk (Cslib.BitString.chi ℝ S) 0 =
      circulantEigenvalue (cubeCayleyWeight s) (Cslib.BitString.chiChar ℝ S) := by
    simpa [Pi.smul_apply, smul_eq_mul] using hw
  rw [← hw', Cslib.BitString.bias_uniformOfFintype_map, Cslib.RotationMap.walk_apply]
  exact expect_congr rfl fun _ _ => by simp [Cslib.RotationMap.cubeCayley_neighbor]

/-- On `Fin (n + 1)`, the `k`-th Fourier mode `j ↦ ω ^ (j * k)` (for `ω ^ (n + 1) = 1`) is an
eigenvector of `Matrix.circulant w` with eigenvalue `Cslib.dft ω (fun i => w (-i)) k`. -/
theorem circulant_mulVec_pow_eq_dft_smul {R : Type*} [CommRing R] {n : ℕ} {ω : R}
    (hω : ω ^ (n + 1) = 1) (w : Fin (n + 1) → R) (k : Fin (n + 1)) :
    circulant w *ᵥ (fun j : Fin (n + 1) => ω ^ ((j : ℕ) * k)) =
      Cslib.dft ω (fun i : Fin (n + 1) => w (-i)) k •
        (fun j : Fin (n + 1) => ω ^ ((j : ℕ) * k)) := by
  funext x
  simp only [mulVec, dotProduct, circulant_apply, Cslib.dft, Pi.smul_apply, smul_eq_mul, sum_mul]
  refine Fintype.sum_equiv (Equiv.subRight x) _ _ fun j => ?_
  have hpow : ω ^ (((j - x : Fin (n + 1)) : ℕ) * k) * ω ^ ((x : ℕ) * k) = ω ^ ((j : ℕ) * k) := by
    conv_rhs => rw [← sub_add_cancel j x, Fin.val_add, pow_eq_pow_mod _ hω, Nat.mod_mul_mod,
      ← pow_eq_pow_mod _ hω, add_mul, pow_add]
  rw [Equiv.subRight_apply, neg_sub, mul_assoc, hpow]

end Bridges

end Matrix
