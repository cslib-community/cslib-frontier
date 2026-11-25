/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Algebra.Measurement
public import CslibFrontier.Foundations.Quantum.POVM.Restriction
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Polar
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import CslibFrontier.Foundations.Quantum.POVM.OutcomeVector
public import Mathlib.LinearAlgebra.UnitaryGroup
import CslibFrontier.Foundations.Analysis.InnerProductSpace.PiL2

/-!
# Naimark dilation

Every positive-operator-valued measurement is the compression of a projective one
[Naimark][Naimark1940]: for a POVM `{E_a}` on `ℂ^ι` and an outcome `a₀`, there is a projective
measurement `{P_a}` on `ℂ^ι ⊗ ℂ^A` (`Cslib.Quantum.POVM.dilate`) with
`Jᴴ P_a J = E_a` for the embedding `J ψ = ψ ⊗ |a₀⟩` (`Cslib.Quantum.POVM.compress_dilate`).
So measuring `ψ` with `E` and measuring `ψ ⊗ |a₀⟩` with `P` give the same outcome distribution.

The construction: `V ψ = ∑_a √E_a ψ ⊗ |a⟩` is an isometry, because `∑_a E_a = 1`; a unitary `U`
on `ℂ^ι ⊗ ℂ^A` with `U J = V` exists, by extending the orthonormal columns of `V` to an orthonormal
basis (`Matrix.exists_unitary_extension`); and `P_a = Uᴴ (1 ⊗ |a⟩⟨a|) U`.

## Main definitions

* `Cslib.Quantum.ancillaEmbed`: the embedding `ψ ↦ ψ ⊗ |a₀⟩`.
* `Cslib.Quantum.POVM.dilate`: the Naimark dilation of a POVM.

## Main results

* `Cslib.Quantum.POVM.isProjective_dilate`: the dilation is projective.
* `Cslib.Quantum.POVM.compress_dilate`: the dilation compresses to the POVM.
* `Cslib.Quantum.POVM.restrictBasis_dilate`: restriction to the prepared ancilla recovers the POVM.

## References

* [M. A. Naimark, *Spectral functions of a symmetric operator*][Naimark1940]
-/

@[expose] public section

namespace Cslib.Quantum

open Matrix
open scoped Kronecker

variable {ι A : Type*} [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A]

/-- The embedding `ψ ↦ ψ ⊗ |a₀⟩` into `ℂ^ι ⊗ ℂ^A`. -/
def ancillaEmbed (a₀ : A) : Matrix (ι × A) ι ℂ :=
  fun p i => if p = (i, a₀) then 1 else 0

theorem conjTranspose_ancillaEmbed_mul (a₀ : A) :
    (ancillaEmbed (ι := ι) a₀)ᴴ * ancillaEmbed (ι := ι) a₀ = 1 := by
  ext i i'
  rw [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type]
  by_cases h : i = i'
  · subst h
    simp [ancillaEmbed, ite_and]
  · simp [ancillaEmbed, ite_and, h, Ne.symm h]

omit [Fintype ι] [DecidableEq ι] [Fintype A] [DecidableEq A] in
/-- The basis coordinates with the ancilla fixed to `a₀`. -/
def ancillaBasis (a₀ : A) : ι ↪ ι × A :=
  ⟨fun i => (i, a₀), fun _ _ h => congrArg Prod.fst h⟩

/-- Compression to the prepared ancilla selects a principal submatrix. -/
theorem compress_ancillaEmbed (a₀ : A) (M : Matrix (ι × A) (ι × A) ℂ) :
    (ancillaEmbed a₀)ᴴ * M * ancillaEmbed a₀ =
      M.submatrix (ancillaBasis a₀) (ancillaBasis a₀) := by
  rw [Matrix.mul_assoc]
  ext i j
  change ((ancillaEmbed (ι := ι) a₀)ᴴ * (M * ancillaEmbed (ι := ι) a₀)) i j = M (i, a₀) (j, a₀)
  simp [Matrix.mul_apply, ancillaEmbed, ite_mul, mul_ite]

/-- The projection `1 ⊗ |a⟩⟨a|` onto the ancilla value `a`. -/
def ancillaProj (a : A) : Matrix (ι × A) (ι × A) ℂ :=
  1 ⊗ₖ Matrix.single a a 1

omit [Fintype ι] [Fintype A] in
theorem isHermitian_ancillaProj (a : A) : (ancillaProj (ι := ι) a).IsHermitian := by
  rw [ancillaProj, IsHermitian, conjTranspose_kronecker, conjTranspose_one]
  congr 1
  ext c d
  simp [Matrix.single, conjTranspose_apply, and_comm]

theorem ancillaProj_mul_self (a : A) :
    ancillaProj (ι := ι) a * ancillaProj a = ancillaProj a := by
  rw [ancillaProj, ← mul_kronecker_mul, Matrix.mul_one, single_mul_single_same, mul_one]

omit [Fintype ι] in
theorem sum_ancillaProj : ∑ a, ancillaProj (ι := ι) (A := A) a = 1 := by
  ext ⟨i, c⟩ ⟨i', c'⟩
  simp only [ancillaProj, Matrix.sum_apply, kroneckerMap_apply, Matrix.single_apply]
  by_cases h : c = c'
  · subst h
    simp [Matrix.one_apply]
  · rw [Matrix.one_apply_ne fun hp => h (Prod.mk.inj hp).2]
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : x = c <;> simp [hx, h]

private theorem ancillaProj_conjTranspose_mul_self (a : A) :
    (ancillaProj (ι := ι) a)ᴴ * ancillaProj a = ancillaProj a := by
  rw [(isHermitian_ancillaProj a).eq, ancillaProj_mul_self]

namespace POVM

open scoped MatrixOrder ComplexOrder

variable (M : POVM A ι)

/-- The **Naimark isometry** `V ψ = ∑_a √E_a ψ ⊗ |a⟩`. -/
noncomputable def naimarkIsometry : Matrix (ι × A) ι ℂ :=
  fun p j => M.sqrtEffect p.2 p.1 j

omit [DecidableEq A] in
private theorem sum_conj_sqrtEffect (a : A) (j j' : ι) :
    ∑ i, star (M.sqrtEffect a i j) * M.sqrtEffect a i j' = M.effect a j j' := by
  rw [← M.sqrtEffect_mul_self a, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← conjTranspose_apply, M.conjTranspose_sqrtEffect]

omit [DecidableEq A] in
theorem conjTranspose_naimarkIsometry_mul : (M.naimarkIsometry)ᴴ * M.naimarkIsometry = 1 := by
  rw [← M.sum_effect]
  ext j j'
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_comm, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← M.sum_conj_sqrtEffect a]
  simp [naimarkIsometry, conjTranspose_apply]

theorem naimarkIsometry_compress (a : A) :
    (M.naimarkIsometry)ᴴ * ancillaProj a * M.naimarkIsometry = M.effect a := by
  have hW : ancillaProj a * M.naimarkIsometry =
      Matrix.of fun p j => if p.2 = a then M.sqrtEffect a p.1 j else 0 := by
    ext ⟨i, c⟩ j
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.of_apply]
    by_cases hc : c = a
    · subst hc
      simp [ancillaProj, kroneckerMap_apply, Matrix.single_apply, Matrix.one_apply,
        naimarkIsometry]
    · simp [ancillaProj, kroneckerMap_apply, hc, Ne.symm hc]
  rw [Matrix.mul_assoc, hW]
  ext j j'
  rw [Matrix.mul_apply, Fintype.sum_prod_type, ← M.sum_conj_sqrtEffect a]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [naimarkIsometry, conjTranspose_apply, Matrix.of_apply]

variable (a₀ : A)

theorem exists_naimarkUnitary : ∃ U ∈ unitaryGroup (ι × A) ℂ,
    ∀ p i, U p (i, a₀) = M.naimarkIsometry p i :=
  exists_unitary_extension M.naimarkIsometry M.conjTranspose_naimarkIsometry_mul
    (j := fun i => (i, a₀)) fun _ _ h => (Prod.mk.inj h).1

/-- A unitary on `ℂ^ι ⊗ ℂ^A` mapping `ψ ⊗ |a₀⟩` to `V ψ`. -/
noncomputable def naimarkUnitary : Matrix (ι × A) (ι × A) ℂ :=
  (M.exists_naimarkUnitary a₀).choose

theorem naimarkUnitary_mem : M.naimarkUnitary a₀ ∈ unitaryGroup (ι × A) ℂ :=
  (M.exists_naimarkUnitary a₀).choose_spec.1

theorem naimarkUnitary_mul_ancillaEmbed :
    M.naimarkUnitary a₀ * ancillaEmbed a₀ = M.naimarkIsometry := by
  ext p i
  rw [Matrix.mul_apply, Finset.sum_eq_single (i, a₀) (fun q _ hq => by simp [ancillaEmbed, hq])
    (by simp), ← (M.exists_naimarkUnitary a₀).choose_spec.2 p i]
  simp [ancillaEmbed, naimarkUnitary]

private theorem conjTranspose_naimarkUnitary_mul :
    (M.naimarkUnitary a₀)ᴴ * M.naimarkUnitary a₀ = 1 :=
  mem_unitaryGroup_iff'.mp (M.naimarkUnitary_mem a₀)

private theorem naimarkUnitary_mul_conjTranspose :
    M.naimarkUnitary a₀ * (M.naimarkUnitary a₀)ᴴ = 1 :=
  mem_unitaryGroup_iff.mp (M.naimarkUnitary_mem a₀)

/-- The **Naimark dilation** of a POVM: the projective measurement `Uᴴ (1 ⊗ |a⟩⟨a|) U` on
`ℂ^ι ⊗ ℂ^A`. -/
noncomputable def dilate : POVM A (ι × A) where
  effect a := (M.naimarkUnitary a₀)ᴴ * ancillaProj a * M.naimarkUnitary a₀
  posSemidef a := by
    have h : (M.naimarkUnitary a₀)ᴴ * ancillaProj a * M.naimarkUnitary a₀ =
        (ancillaProj a * M.naimarkUnitary a₀)ᴴ * (ancillaProj a * M.naimarkUnitary a₀) := by
      rw [conjTranspose_mul, Matrix.mul_assoc (M.naimarkUnitary a₀)ᴴ (ancillaProj a)ᴴ,
        ← Matrix.mul_assoc (ancillaProj a)ᴴ, ancillaProj_conjTranspose_mul_self, Matrix.mul_assoc]
    rw [h]
    exact posSemidef_conjTranspose_mul_self _
  sum_effect := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_ancillaProj, Matrix.mul_one,
      M.conjTranspose_naimarkUnitary_mul]

theorem dilate_effect (a : A) : (M.dilate a₀).effect a =
    (M.naimarkUnitary a₀)ᴴ * ancillaProj a * M.naimarkUnitary a₀ :=
  rfl

/-- The Naimark dilation is projective. -/
theorem dilate_effect_mul_self (a : A) :
    (M.dilate a₀).effect a * (M.dilate a₀).effect a = (M.dilate a₀).effect a := by
  simp only [dilate_effect]
  rw [show (M.naimarkUnitary a₀)ᴴ * ancillaProj a * M.naimarkUnitary a₀ *
      ((M.naimarkUnitary a₀)ᴴ * ancillaProj a * M.naimarkUnitary a₀) =
      (M.naimarkUnitary a₀)ᴴ * ancillaProj a * (M.naimarkUnitary a₀ * (M.naimarkUnitary a₀)ᴴ) *
        ancillaProj a * M.naimarkUnitary a₀ by simp only [Matrix.mul_assoc],
    M.naimarkUnitary_mul_conjTranspose, Matrix.mul_one, Matrix.mul_assoc (M.naimarkUnitary a₀)ᴴ,
    ancillaProj_mul_self]

theorem isProjective_dilate : (M.dilate a₀).toMeasurement.IsProjective :=
  M.dilate_effect_mul_self a₀

/-- **Naimark**: the dilation compresses to the POVM, `Jᴴ P_a J = E_a` for `J ψ = ψ ⊗ |a₀⟩`. -/
theorem compress_dilate (a : A) :
    (ancillaEmbed a₀)ᴴ * (M.dilate a₀).effect a * ancillaEmbed a₀ = M.effect a := by
  rw [dilate_effect, ← M.naimarkIsometry_compress a, ← M.naimarkUnitary_mul_ancillaEmbed a₀,
    conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- Restricting the dilation of a POVM recovers the original POVM. -/
@[simp] theorem restrictBasis_dilate :
    (M.dilate a₀).restrictBasis (ancillaBasis a₀) = M := by
  have h : ((M.dilate a₀).restrictBasis (ancillaBasis a₀)).effect = M.effect := by
    funext a
    rw [restrictBasis_effect, ← compress_ancillaEmbed, compress_dilate]
  generalize (M.dilate a₀).restrictBasis (ancillaBasis a₀) = N at h ⊢
  cases N
  cases M
  cases h
  rfl

end POVM

end Cslib.Quantum
