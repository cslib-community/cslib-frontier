/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Determinant
public import CslibFrontier.Computability.Circuit.Arithmetic.SubstMatrix
import CslibFrontier.Foundations.LinearAlgebra.Matrix.BranchingProgramDeterminant

/-!
# Specialization matrices, branching programs and projections of the determinant

A polynomial over a commutative ring `K` is a projection of the `m × m` generic determinant
`(genericMatrix K m).det` if and only if it is the determinant of an `m × m` *specialization matrix*
(`IsSubstMatrix`), whose entries are variables `X i` or constants `C c` (`IsSubstEntry`). Through
block-diagonal specialization matrices, projections of generic determinants are closed under
multiplication (with dimensions adding) and monotone in the matrix dimension.

To close under addition as well, `IsSubstABP k P` represents `P` as the source-to-sink path sum of a
strictly upper-triangular specialization branching program on `Fin (k + 2)` in topological order.
By `Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul`, such a program yields a projection of
`(genericMatrix K (k + 1)).det`, with `-1` along the subdiagonal of `N - 1` absorbing the cycle
signs over every commutative ring `K` without field or characteristic hypotheses. Series and
parallel-bridge compositions add at most `k₁ + k₂ + 1` steps, giving both linear-size formula
simulation (`CslibFrontier/Computability/Circuit/Arithmetic/Determinant/Formula.lean`) and
Valiant's projection universality (`exists_isProjection_det`) for arbitrary multivariate
polynomials.

## Main definitions

* `Cslib.Circuits.Arithmetic.IsSubstABP`: `P` is computed by a strictly upper-triangular
  specialization branching program on `Fin (k + 2)`.

## Main results

* `Cslib.Circuits.Arithmetic.isProjection_det_iff_exists_isSubstMatrix`: `P` is a projection of
  `(genericMatrix K m).det` if and only if `P` is the determinant of an `m × m` specialization
  matrix.
* `Cslib.Circuits.Arithmetic.IsSubstMatrix.isProjection_det`: the determinant of a square
  specialization matrix on a finite type `α` is a projection of the `|α| × |α|` generic
  determinant.
* `Cslib.Circuits.Arithmetic.IsProjection.det_mul`: projections of generic determinants multiply by
  adding dimensions.
* `Cslib.Circuits.Arithmetic.isProjection_det_mono`: projections of generic determinants pad to any
  larger dimension.
* `Cslib.Circuits.Arithmetic.IsSubstABP.isProjection_det`,
  `Cslib.Circuits.Arithmetic.IsSubstABP.of_isSubstEntry`,
  `Cslib.Circuits.Arithmetic.IsSubstABP.add`, `Cslib.Circuits.Arithmetic.IsSubstABP.mul`:
  closure of specialization branching programs and conversion to `(k + 1) × (k + 1)` determinant
  projections.
* `Cslib.Circuits.Arithmetic.exists_isProjection_det`: **Valiant's projection universality**: every
  polynomial in `MvPolynomial σ K` is a projection of `(genericMatrix K m).det` for some `m`.

## References

* [L. G. Valiant, *Completeness classes in algebra*][Valiant1979Algebra], §1–§2, Theorem 1
  (pp. 249–251)
* [P. Bürgisser, *Completeness and Reduction in Algebraic Complexity Theory*][Burgisser2000],
  Chapter 2
* [R. Saptharishi, *A survey of lower bounds in arithmetic circuit
  complexity*][Saptharishi2026Survey], chapter "Algebraic complexity classes", Theorem `thm:vp` and
  Section `sec:formula-to-dets`
-/

public section

namespace Cslib.Circuits.Arithmetic

open MvPolynomial
open scoped Matrix

universe u

variable {K : Type u} [CommRing K] {m : ℕ} {σ : Type*}

/-- Applying a projection `ρ` to `(genericMatrix K m).det` gives the determinant of the specialized
matrix. -/
private theorem projection_det_genericMatrix (ρ : Fin (m * m) → σ ⊕ K) :
    projection ρ (genericMatrix K m).det =
      (Matrix.of fun i j : Fin m =>
        Sum.elim X (fun a => C a) (ρ (finProdFinEquiv (i, j)))).det := by
  rw [AlgHom.map_det]
  exact congrArg Matrix.det (Matrix.ext fun i j => by
    simp only [AlgHom.mapMatrix_apply, genericMatrix, Matrix.map_apply, Matrix.of_apply,
      projection_X])

namespace IsSubstMatrix

/-- The determinant of a square specialization matrix indexed by `α` is a projection of the
`|α| × |α|` generic determinant. -/
theorem isProjection_det {α : Type*} [Fintype α] [DecidableEq α]
    {M : Matrix α α (MvPolynomial σ K)} (hM : IsSubstMatrix M) :
    IsProjection M.det (genericMatrix K (Fintype.card α)).det := by
  choose ρ hρ using hM
  let e := (Fintype.equivFin α).symm
  refine ⟨fun idx =>
    let pq := finProdFinEquiv.symm idx
    ρ (e pq.1) (e pq.2), ?_⟩
  rw [projection_det_genericMatrix, ← Matrix.det_submatrix_equiv_self e M]
  exact congrArg Matrix.det (Matrix.ext fun i j => by
    simpa only [Matrix.of_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply] using
      hρ (e i) (e j))

end IsSubstMatrix

/-- A polynomial `P` is a projection of `(genericMatrix K m).det` if and only if it is the
determinant of an `m × m` specialization matrix. -/
theorem isProjection_det_iff_exists_isSubstMatrix {P : MvPolynomial σ K} {m : ℕ} :
    IsProjection P (genericMatrix K m).det ↔
      ∃ M : Matrix (Fin m) (Fin m) (MvPolynomial σ K), IsSubstMatrix M ∧ M.det = P := by
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨Matrix.of fun i j => Sum.elim X (fun a => C a) (ρ (finProdFinEquiv (i, j))),
      fun i j => ⟨ρ (finProdFinEquiv (i, j)), rfl⟩,
      (projection_det_genericMatrix ρ).symm⟩
  · rintro ⟨M, hM, rfl⟩
    have h := hM.isProjection_det
    rwa [Fintype.card_fin] at h

/-- **Multiplicative closure of determinant projections**: if `P` is a projection of the `m × m`
generic determinant and `Q` is a projection of the `k × k` generic determinant, then `P * Q` is a
projection of the `(m + k) × (m + k)` generic determinant. -/
theorem IsProjection.det_mul {P Q : MvPolynomial σ K} {m k : ℕ}
    (hP : IsProjection P (genericMatrix K m).det)
    (hQ : IsProjection Q (genericMatrix K k).det) :
    IsProjection (P * Q) (genericMatrix K (m + k)).det := by
  obtain ⟨M₁, hM₁, rfl⟩ := isProjection_det_iff_exists_isSubstMatrix.mp hP
  obtain ⟨M₂, hM₂, rfl⟩ := isProjection_det_iff_exists_isSubstMatrix.mp hQ
  have h := (hM₁.fromBlocks .zero .zero hM₂).isProjection_det
  rwa [Matrix.det_fromBlocks_zero₂₁, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin] at h

/-- **Monotonicity of determinant projections in the matrix dimension**: if `m ≤ k` and `P` is a
projection of `(genericMatrix K m).det`, then `P` is a projection of `(genericMatrix K k).det`. -/
theorem isProjection_det_mono {P : MvPolynomial σ K} {m k : ℕ} (hmk : m ≤ k)
    (hP : IsProjection P (genericMatrix K m).det) :
    IsProjection P (genericMatrix K k).det := by
  have h := hP.det_mul
    (isProjection_det_iff_exists_isSubstMatrix.mpr ⟨1, .one, Matrix.det_one⟩ :
      IsProjection 1 (genericMatrix K (k - m)).det)
  rwa [mul_one, Nat.add_sub_of_le hmk] at h

/-! ### Acyclic specialization branching programs -/

/-- A polynomial `P` is computed by a *specialization branching program* of size `k + 1` when some
strictly upper-triangular specialization matrix `N` on `Fin (k + 2)` has path-sum vector `q`
(`q = Pi.single 0 1 + q ᵥ* N`) ending at `q (Fin.last (k + 1)) = P`. -/
def IsSubstABP (k : ℕ) (P : MvPolynomial σ K) : Prop :=
  ∃ (N : Matrix (Fin (k + 2)) (Fin (k + 2)) (MvPolynomial σ K))
    (q : Fin (k + 2) → MvPolynomial σ K),
    IsSubstMatrix N ∧ (∀ i j, j ≤ i → N i j = 0) ∧
      q = Pi.single 0 1 + q ᵥ* N ∧ q (Fin.last (k + 1)) = P

namespace IsSubstABP

private theorem pathSum_zero {R : Type*} [CommRing R] {k : ℕ}
    {N : Matrix (Fin (k + 2)) (Fin (k + 2)) R} {q : Fin (k + 2) → R}
    (hN : ∀ i j, j ≤ i → N i j = 0) (hq : q = Pi.single 0 1 + q ᵥ* N) :
    q 0 = 1 := by
  have h0 : (q ᵥ* N) 0 = 0 := by
    rw [Matrix.vecMul, dotProduct]
    exact Finset.sum_eq_zero fun i _ => by rw [hN i 0 (Fin.zero_le i), mul_zero]
  simpa only [Pi.add_apply, Pi.single_eq_same, h0, add_zero] using congrFun hq 0

private theorem pathSum_succ {R : Type*} [CommRing R] {k : ℕ}
    {N : Matrix (Fin (k + 2)) (Fin (k + 2)) R} {q : Fin (k + 2) → R}
    (hq : q = Pi.single 0 1 + q ᵥ* N) (b : Fin (k + 1)) :
    q b.succ = (q ᵥ* N) b.succ := by
  simpa only [Pi.add_apply, Pi.single_eq_of_ne (Fin.succ_ne_zero b), zero_add] using
    congrFun hq b.succ

/-- Order-preserving index equivalence between `Fin (k₁ + 2) ⊕ Fin (k₂ + 1)` and
`Fin ((k₁ + k₂ + 1) + 2)`. -/
private def abpEquiv (k₁ k₂ : ℕ) : Fin (k₁ + 2) ⊕ Fin (k₂ + 1) ≃ Fin ((k₁ + k₂ + 1) + 2) :=
  finSumFinEquiv.trans (finCongr (by omega))

private theorem abpEquiv_inl_zero (k₁ k₂ : ℕ) : abpEquiv k₁ k₂ (.inl 0) = 0 := by
  ext
  simp [abpEquiv]

private theorem abpEquiv_inr_last (k₁ k₂ : ℕ) :
    abpEquiv k₁ k₂ (.inr (Fin.last k₂)) = Fin.last (k₁ + k₂ + 2) := by
  ext
  simp only [abpEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast, finSumFinEquiv_apply_right,
    Fin.val_natAdd, Fin.val_last]
  omega

/-- Combining two strictly upper-triangular matrices with an arbitrary upper-right coupling block
`B` preserves strict upper triangularity and specialization entries. -/
private def abpCombine {R : Type*} [Zero R] {k₁ k₂ : ℕ}
    (N₁ : Matrix (Fin (k₁ + 2)) (Fin (k₁ + 2)) R)
    (B : Matrix (Fin (k₁ + 2)) (Fin (k₂ + 1)) R)
    (N₂ : Matrix (Fin (k₂ + 2)) (Fin (k₂ + 2)) R) :
    Matrix (Fin ((k₁ + k₂ + 1) + 2)) (Fin ((k₁ + k₂ + 1) + 2)) R :=
  (Matrix.fromBlocks N₁ B 0 (N₂.submatrix Fin.succ Fin.succ)).submatrix
    (abpEquiv k₁ k₂).symm (abpEquiv k₁ k₂).symm

private theorem isSubstMatrix_abpCombine {k₁ k₂ : ℕ}
    {N₁ : Matrix (Fin (k₁ + 2)) (Fin (k₁ + 2)) (MvPolynomial σ K)}
    {B : Matrix (Fin (k₁ + 2)) (Fin (k₂ + 1)) (MvPolynomial σ K)}
    {N₂ : Matrix (Fin (k₂ + 2)) (Fin (k₂ + 2)) (MvPolynomial σ K)}
    (hN₁ : IsSubstMatrix N₁) (hB : IsSubstMatrix B) (hN₂ : IsSubstMatrix N₂) :
    IsSubstMatrix (abpCombine N₁ B N₂) :=
  (hN₁.fromBlocks hB .zero (hN₂.submatrix _ _)).submatrix _ _

private theorem abpCombine_eq_zero_of_le {R : Type*} [Zero R] {k₁ k₂ : ℕ}
    {N₁ : Matrix (Fin (k₁ + 2)) (Fin (k₁ + 2)) R}
    (B : Matrix (Fin (k₁ + 2)) (Fin (k₂ + 1)) R)
    {N₂ : Matrix (Fin (k₂ + 2)) (Fin (k₂ + 2)) R}
    (hN₁ : ∀ i j, j ≤ i → N₁ i j = 0) (hN₂ : ∀ i j, j ≤ i → N₂ i j = 0) :
    ∀ i j, j ≤ i → abpCombine N₁ B N₂ i j = 0 := by
  intro i j hji
  obtain ⟨x, rfl⟩ := (abpEquiv k₁ k₂).surjective i
  obtain ⟨y, rfl⟩ := (abpEquiv k₁ k₂).surjective j
  simp only [abpCombine, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases x with a | b <;> rcases y with a' | b'
  · refine hN₁ a a' ?_
    simp only [abpEquiv, Equiv.trans_apply, finCongr_apply, Fin.le_iff_val_le_val, Fin.val_cast,
      finSumFinEquiv_apply_left, Fin.val_castAdd] at hji ⊢
    exact hji
  · exfalso
    simp only [abpEquiv, Equiv.trans_apply, finCongr_apply, Fin.le_iff_val_le_val, Fin.val_cast,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.val_castAdd,
      Fin.val_natAdd] at hji
    omega
  · rfl
  · refine hN₂ b.succ b'.succ ?_
    simp only [abpEquiv, Equiv.trans_apply, finCongr_apply, Fin.le_iff_val_le_val, Fin.val_cast,
      finSumFinEquiv_apply_right, Fin.val_natAdd, Fin.val_succ] at hji ⊢
    omega

private theorem pathSum_abpCombine {R : Type*} [CommRing R] {k₁ k₂ : ℕ}
    {N₁ : Matrix (Fin (k₁ + 2)) (Fin (k₁ + 2)) R}
    {B : Matrix (Fin (k₁ + 2)) (Fin (k₂ + 1)) R}
    {N₂ : Matrix (Fin (k₂ + 2)) (Fin (k₂ + 2)) R}
    {q₁ : Fin (k₁ + 2) → R} (r : Fin (k₂ + 1) → R)
    (hq₁ : q₁ = Pi.single 0 1 + q₁ ᵥ* N₁)
    (hr : ∀ b, r b = (q₁ ᵥ* B) b + (r ᵥ* N₂.submatrix Fin.succ Fin.succ) b) :
    let q := Sum.elim q₁ r ∘ (abpEquiv k₁ k₂).symm
    q = Pi.single 0 1 + q ᵥ* abpCombine N₁ B N₂ := by
  intro q
  ext j
  obtain ⟨y, rfl⟩ := (abpEquiv k₁ k₂).surjective j
  have hvm : (q ᵥ* abpCombine N₁ B N₂) (abpEquiv k₁ k₂ y) =
      (Sum.elim q₁ r ᵥ* Matrix.fromBlocks N₁ B 0 (N₂.submatrix Fin.succ Fin.succ)) y := by
    simp only [q, abpCombine, Matrix.vecMul, dotProduct, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Function.comp_apply]
    rw [← (abpEquiv k₁ k₂).sum_comp]
    simp only [Equiv.symm_apply_apply]
  simp only [Pi.add_apply, hvm, Matrix.vecMul_fromBlocks, Matrix.vecMul_zero, add_zero]
  rcases y with a | b
  · simp only [q, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_comp_inl,
      ← abpEquiv_inl_zero k₁ k₂]
    rcases eq_or_ne a 0 with rfl | ha
    · simpa only [Pi.add_apply, Pi.single_eq_same] using congrFun hq₁ 0
    · simpa only [Pi.add_apply,
        Pi.single_eq_of_ne (fun h => ha (Sum.inl.inj ((abpEquiv k₁ k₂).injective h))),
        Pi.single_eq_of_ne ha] using congrFun hq₁ a
  · simp only [q, Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
    rw [Pi.single_eq_of_ne (by
      rw [← abpEquiv_inl_zero k₁ k₂]; exact fun h => nomatch (abpEquiv k₁ k₂).injective h),
      zero_add]
    exact hr b

/-- A specialization branching program of size `k + 1` gives a projection of the
`(k + 1) × (k + 1)` generic determinant. -/
theorem isProjection_det {k : ℕ} {P : MvPolynomial σ K} (h : IsSubstABP k P) :
    IsProjection P (genericMatrix K (k + 1)).det := by
  obtain ⟨N, q, hM, hN, hq, rfl⟩ := h
  refine isProjection_det_iff_exists_isSubstMatrix.mpr
    ⟨(N - 1).submatrix Fin.castSucc Fin.succ, fun a b => ?_,
      (Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul N hN hq).symm⟩
  simp only [Matrix.submatrix_apply, Matrix.sub_apply]
  by_cases hab : a.castSucc = b.succ
  · rw [hN a.castSucc b.succ hab.symm.le, hab, Matrix.one_apply_eq, zero_sub]
    exact .neg_one
  · rw [Matrix.one_apply_ne hab, sub_zero]
    exact hM a.castSucc b.succ

/-- Every single substitution entry (a variable `X i` or constant `C c`) is computed by a `1`-step
specialization branching program (`k = 0`). -/
theorem of_isSubstEntry {P : MvPolynomial σ K} (hP : IsSubstEntry P) :
    IsSubstABP 0 P := by
  refine ⟨Matrix.of fun i j => if i = 0 ∧ j = 1 then P else 0,
    Fin.cases 1 (fun _ => P), fun i j => ?_, fun i j hji => ?_, ?_, rfl⟩
  · simp only [Matrix.of_apply]
    split_ifs <;> [exact hP; exact .zero]
  · simp only [Matrix.of_apply, ite_eq_right_iff, and_imp]
    rintro rfl rfl
    exact absurd hji (by decide)
  · funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [Matrix.vecMul, dotProduct]
    · rw [Subsingleton.elim i 0, Fin.cases_succ]
      simp [Matrix.vecMul, dotProduct]

/-- **Multiplicative closure** of specialization branching programs by series composition. -/
theorem mul {k₁ k₂ : ℕ} {P Q : MvPolynomial σ K}
    (hP : IsSubstABP k₁ P) (hQ : IsSubstABP k₂ Q) :
    IsSubstABP (k₁ + k₂ + 1) (P * Q) := by
  obtain ⟨N₁, q₁, hM₁, hN₁, hq₁, rfl⟩ := hP
  obtain ⟨N₂, q₂, hM₂, hN₂, hq₂, rfl⟩ := hQ
  let B : Matrix (Fin (k₁ + 2)) (Fin (k₂ + 1)) (MvPolynomial σ K) :=
    Matrix.of fun a b => if a = Fin.last (k₁ + 1) then N₂ 0 b.succ else 0
  let r : Fin (k₂ + 1) → MvPolynomial σ K := fun b => q₁ (Fin.last (k₁ + 1)) * q₂ b.succ
  have hB : IsSubstMatrix B := fun a b => by
    simp only [B, Matrix.of_apply]
    split_ifs <;> [exact hM₂ 0 b.succ; exact .zero]
  refine ⟨abpCombine N₁ B N₂, Sum.elim q₁ r ∘ (abpEquiv k₁ k₂).symm,
    isSubstMatrix_abpCombine hM₁ hB hM₂, abpCombine_eq_zero_of_le B hN₁ hN₂,
    pathSum_abpCombine r hq₁ fun b => ?_, ?_⟩
  · have hB_eval : (q₁ ᵥ* B) b = q₁ (Fin.last (k₁ + 1)) * (q₂ 0 * N₂ 0 b.succ) := by
      rw [pathSum_zero hN₂ hq₂, one_mul, Matrix.vecMul, dotProduct,
        Finset.sum_eq_single (Fin.last (k₁ + 1)) (fun a _ ha => by simp [B, ha])
          (fun h => absurd (Finset.mem_univ _) h)]
      simp [B]
    have hD_eval : (r ᵥ* N₂.submatrix Fin.succ Fin.succ) b =
        q₁ (Fin.last (k₁ + 1)) * ∑ b' : Fin (k₂ + 1), q₂ b'.succ * N₂ b'.succ b.succ := by
      simp only [r, Matrix.vecMul, dotProduct, Matrix.submatrix_apply, Finset.mul_sum, mul_assoc]
    rw [hB_eval, hD_eval, ← mul_add, ← Fin.sum_univ_succ (fun i => q₂ i * N₂ i b.succ),
      ← dotProduct, ← Matrix.vecMul, ← pathSum_succ hq₂ b]
  · simp only [Function.comp_apply, ← abpEquiv_inr_last k₁ k₂, Equiv.symm_apply_apply,
      Sum.elim_inr, r, Fin.succ_last]

/-- **Additive closure** of specialization branching programs by parallel composition with a unit
bridge edge between sinks. -/
theorem add {k₁ k₂ : ℕ} {P Q : MvPolynomial σ K}
    (hP : IsSubstABP k₁ P) (hQ : IsSubstABP k₂ Q) :
    IsSubstABP (k₁ + k₂ + 1) (P + Q) := by
  obtain ⟨N₁, q₁, hM₁, hN₁, hq₁, rfl⟩ := hP
  obtain ⟨N₂, q₂, hM₂, hN₂, hq₂, rfl⟩ := hQ
  let B : Matrix (Fin (k₁ + 2)) (Fin (k₂ + 1)) (MvPolynomial σ K) :=
    Matrix.of fun a b =>
      if a = 0 then N₂ 0 b.succ
      else if a = Fin.last (k₁ + 1) ∧ b = Fin.last k₂ then 1 else 0
  let r : Fin (k₂ + 1) → MvPolynomial σ K :=
    fun b => q₂ b.succ + if b = Fin.last k₂ then q₁ (Fin.last (k₁ + 1)) else 0
  have hB : IsSubstMatrix B := fun a b => by
    simp only [B, Matrix.of_apply]
    split_ifs <;> [exact hM₂ 0 b.succ; exact .one; exact .zero]
  refine ⟨abpCombine N₁ B N₂, Sum.elim q₁ r ∘ (abpEquiv k₁ k₂).symm,
    isSubstMatrix_abpCombine hM₁ hB hM₂, abpCombine_eq_zero_of_le B hN₁ hN₂,
    pathSum_abpCombine r hq₁ fun b => ?_, ?_⟩
  · have h0_ne : (0 : Fin (k₁ + 2)) ≠ Fin.last (k₁ + 1) := by simp [Fin.ext_iff]
    have hB_eval : (q₁ ᵥ* B) b = q₂ 0 * N₂ 0 b.succ +
        if b = Fin.last k₂ then q₁ (Fin.last (k₁ + 1)) else 0 := by
      rw [Matrix.vecMul, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0),
        ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h0_ne.symm, Finset.mem_univ _⟩)]
      have hrest : ∑ a ∈ (Finset.univ.erase 0).erase (Fin.last (k₁ + 1)), q₁ a * B a b = 0 :=
        Finset.sum_eq_zero fun a ha => by
          rcases Finset.mem_erase.mp ha with ⟨hal, ha0⟩
          simp [B, (Finset.mem_erase.mp ha0).1, hal]
      rw [hrest, add_zero, pathSum_zero hN₁ hq₁, pathSum_zero hN₂ hq₂]
      simp only [B, Matrix.of_apply, ↓reduceIte, h0_ne.symm, true_and, mul_ite, mul_one, mul_zero]
    have hD_eval : (r ᵥ* N₂.submatrix Fin.succ Fin.succ) b =
        ∑ b' : Fin (k₂ + 1), q₂ b'.succ * N₂ b'.succ b.succ := by
      rw [Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rcases eq_or_ne b' (Fin.last k₂) with rfl | hb'
      · rw [Matrix.submatrix_apply, hN₂ _ _ (Fin.succ_le_succ_iff.mpr (Fin.le_last b)),
          mul_zero, mul_zero]
      · simp [r, Matrix.submatrix_apply, hb']
    rw [hB_eval, hD_eval, add_right_comm,
      ← Fin.sum_univ_succ (fun i => q₂ i * N₂ i b.succ), ← dotProduct, ← Matrix.vecMul,
      ← pathSum_succ hq₂ b]
  · simp only [Function.comp_apply, ← abpEquiv_inr_last k₁ k₂, Equiv.symm_apply_apply,
      Sum.elim_inr, r, ↓reduceIte, Fin.succ_last]
    exact add_comm _ _

end IsSubstABP

/-- Every polynomial in `MvPolynomial σ K` is computed by a specialization branching program of
some finite size. -/
theorem exists_isSubstABP (f : MvPolynomial σ K) : ∃ k, IsSubstABP k f := by
  induction f using MvPolynomial.induction_on with
  | C a => exact ⟨0, .of_isSubstEntry (.C a)⟩
  | add p q hp hq =>
    obtain ⟨k₁, h₁⟩ := hp
    obtain ⟨k₂, h₂⟩ := hq
    exact ⟨k₁ + k₂ + 1, h₁.add h₂⟩
  | mul_X p i hp =>
    obtain ⟨k₁, h₁⟩ := hp
    exact ⟨k₁ + 0 + 1, h₁.mul (.of_isSubstEntry (.X i))⟩

/-- **Valiant's projection universality**: over every commutative ring `K` and arbitrary variable
index type `σ`, every polynomial `f : MvPolynomial σ K` is a projection of `(genericMatrix K m).det`
for some `m : ℕ` [Valiant][Valiant1979Algebra]. -/
theorem exists_isProjection_det (f : MvPolynomial σ K) :
    ∃ m, IsProjection f (genericMatrix K m).det := by
  obtain ⟨k, hk⟩ := exists_isSubstABP f
  exact ⟨k + 1, hk.isProjection_det⟩

end Cslib.Circuits.Arithmetic
