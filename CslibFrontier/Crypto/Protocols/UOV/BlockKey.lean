/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.LinearAlgebra.Matrix.UpperTriangularQuadratic
public import CslibFrontier.Foundations.LinearAlgebra.MultivariateQuadratic
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Round-3 UOV block public keys and signing linearization

In Version 3.0 of the UOV specification ([UOV2026], §3.1, pp. 11–13, and §3.2.3 / Figure 2,
pp. 14–17), the secret oil subspace is the column space of the `(v + m) × m` block matrix
`[O; Iₘ]` for `O ∈ R^{v × m}`, and each of the `m` homogeneous public polynomials is represented
by an upper-triangular `(v + m) × (v + m)` block matrix

```text
Pᵢ = [[Pᵢ⁽¹⁾, Pᵢ⁽²⁾],
      [0,     Pᵢ⁽³⁾]]
```

with upper-triangular `Pᵢ⁽¹⁾` and `Pᵢ⁽³⁾ = Upper(-Oᵀ Pᵢ⁽¹⁾ O - Oᵀ Pᵢ⁽²⁾)`. Because
`Upper(M) - M` induces an alternating bilinear form in every characteristic
(`Matrix.isAlt_toLinearMap₂'_upperQuadratic_sub`), the restricted matrix
`[Oᵀ Iₘ] Pᵢ [O; Iₘ] = Oᵀ Pᵢ⁽¹⁾ O + Oᵀ Pᵢ⁽²⁾ + Pᵢ⁽³⁾` induces an alternating bilinear form and
therefore vanishes identically on the embedded oil subspace, including in characteristic two.

To invert the resulting public map `P : R^{v + m} → R^m` at target `t` given a vinegar vector
`u ∈ R^v`, UOV forms the candidate preimage `s = [u; 0] + [O; Iₘ] x`, the vinegar evaluation
`yᵢ = uᵀ Pᵢ⁽¹⁾ u`, the precomputed secret-key matrices `Sᵢ = (Pᵢ⁽¹⁾ + Pᵢ⁽¹⁾ᵀ) O + Pᵢ⁽²⁾`, and the
`m × m` linear system matrix `L` whose `i`-th row is `uᵀ Sᵢ`. Reusing
`MultivariateQuadraticMap.map_add_of_mem` and `MultivariateQuadraticMap.polar_ofMatrices_apply`
yields the exact characteristic-independent linearization law

```text
P(s)ᵢ = uᵀ Pᵢ⁽¹⁾ u + (uᵀ Sᵢ) x,
```

so `P(s) = t` if and only if `L x = t - y`.

The algebraic construction is parameterized over any commutative ring `R` and dimensions `(v, m)`,
instantiating directly at the Round-3 binary extension fields `UOV.F16` and `UOV.F256` from
`CslibFrontier.Crypto.Protocols.UOV.Field`. Seed expansion (`SHAKE256` / `AES128-CTR`), byte
serialization, the 256-attempt counter loop, retry failure bounds, and ROM/QROM security
reductions remain open under #4987.

## Main definitions

* `Cslib.Crypto.UOV.BlockKeyMaterial`: the expanded secret oil matrix `O` together with upper-left
  upper-triangular vinegar blocks `P⁽¹⁾` and mixed blocks `P⁽²⁾`.
* `Cslib.Crypto.UOV.vinegarEmbed`, `Cslib.Crypto.UOV.oilEmbed`,
  `Cslib.Crypto.UOV.blockOilSubspace`, `Cslib.Crypto.UOV.signatureVector`: `[u; 0]`, the linear
  oil embedding `[O; Iₘ]`, its column-space submodule, and `s = [u; 0] + [O; Iₘ] x`.
* `Cslib.Crypto.UOV.oilBlock`, `Cslib.Crypto.UOV.blockMatrix`,
  `Cslib.Crypto.UOV.BlockKeyMaterial.publicMatrix`, `Cslib.Crypto.UOV.BlockKeyMaterial.publicMap`:
  `Pᵢ⁽³⁾ = Upper(-Oᵀ Pᵢ⁽¹⁾ O - Oᵀ Pᵢ⁽²⁾)`, the reindexed `(v + m) × (v + m)` block matrix `Pᵢ`,
  and the induced `MultivariateQuadraticMap`.
* `Cslib.Crypto.UOV.linearizationMatrix`, `Cslib.Crypto.UOV.vinegarEval`,
  `Cslib.Crypto.UOV.signingMatrix`, `Cslib.Crypto.UOV.BlockKeyMaterial.signingSystemMatrix`:
  `Sᵢ = (Pᵢ⁽¹⁾ + Pᵢ⁽¹⁾ᵀ) O + Pᵢ⁽²⁾`, `yᵢ = uᵀ Pᵢ⁽¹⁾ u`, and the row matrix `L`.

## Main results

* `Cslib.Crypto.UOV.oilEmbed_injective`: the oil-space parameterization `x ↦ [O x; x]` is
  injective over every commutative ring.
* `Cslib.Crypto.UOV.isUpperTriangular_blockMatrix`,
  `Cslib.Crypto.UOV.BlockKeyMaterial.isUpperTriangular_publicMatrix`: `Pᵢ` is upper triangular.
* `Cslib.Crypto.UOV.isAlt_oilRestriction`: `[Oᵀ Iₘ] Pᵢ [O; Iₘ]` induces an alternating bilinear
  form in every characteristic.
* `Cslib.Crypto.UOV.eq_oilBlock_iff`: `oilBlock O P1 P2` is the unique upper-triangular `m × m`
  block making `(blockMatrix P1 P2 P3).toQuadraticForm'` vanish on `blockOilSubspace O`.
* `Cslib.Crypto.UOV.BlockKeyMaterial.publicMap_vanishesOn`: the constructed public map vanishes on
  `blockOilSubspace O`.
* `Cslib.Crypto.UOV.BlockKeyMaterial.publicMap_signatureVector_apply`,
  `Cslib.Crypto.UOV.BlockKeyMaterial.publicMap_signatureVector`: exact coordinate and vector
  signing linearization identities `P([u; 0] + [O; Iₘ] x) = y + L x`.
* `Cslib.Crypto.UOV.BlockKeyMaterial.publicMap_signatureVector_eq_iff`:
  `P(s) = t ↔ L x = t - y`.

## References

* [W. Beullens et al., *UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting
  Documentation*, v3.0, §3.1, pp. 11–13; §3.2.1–3.2.3 / Figure 2, pp. 13–17; §3.3, p. 19][UOV2026]
-/

public section

namespace Cslib.Crypto.UOV

open Matrix

section BlockConstruction

variable {R : Type*} [CommRing R] {v m : ℕ}

/-- The expanded algebraic key matrices from which Round-3 UOV constructs its public key and
signing matrices ([UOV2026], Figure 2, line 3, p. 16): the secret oil matrix `O ∈ R^{v × m}`
together with upper-triangular vinegar-vinegar blocks `P1 i ∈ R^{v × v}` and vinegar-oil blocks
`P2 i ∈ R^{v × m}`. -/
structure BlockKeyMaterial (R : Type*) [Zero R] (v m : ℕ) where
  /-- Secret oil-space generator `O ∈ R^{v × m}` defining the oil embedding `x ↦ [O x; x]`. -/
  oilMatrix : Matrix (Fin v) (Fin m) R
  /-- Upper-left vinegar quadratic blocks `Pᵢ⁽¹⁾ ∈ R^{v × v}`. -/
  vinegarBlock : Fin m → Matrix (Fin v) (Fin v) R
  /-- Upper-right mixed vinegar-oil blocks `Pᵢ⁽²⁾ ∈ R^{v × m}`. -/
  mixedBlock : Fin m → Matrix (Fin v) (Fin m) R
  /-- Each expanded `Pᵢ⁽¹⁾` block is upper triangular ([UOV2026], Figure 2, line 3, p. 16). -/
  isUpperTriangular_vinegarBlock : ∀ i, (vinegarBlock i).IsUpperTriangular

/-- Embed a vinegar vector `u ∈ R^v` as `[u; 0] ∈ R^{v + m}`. -/
@[expose] def vinegarEmbed (u : Fin v → R) : Fin (v + m) → R :=
  Fin.append u 0

/-- Linear map `x ↦ [O x; x]` parametrizing the Round-3 UOV oil subspace ([UOV2026], §3.1,
p. 12). -/
@[expose] def oilEmbed (O : Matrix (Fin v) (Fin m) R) :
    (Fin m → R) →ₗ[R] (Fin (v + m) → R) where
  toFun x := Fin.append (O *ᵥ x) x
  map_add' x y := by
    ext k
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
    · simp [Fin.append_left, mulVec_add]
    · simp [Fin.append_right]
  map_smul' c x := by
    ext k
    obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k
    · simp [Fin.append_left, mulVec_smul]
    · simp [Fin.append_right]

/-- Explicit coordinate formula for `oilEmbed O x`. -/
theorem oilEmbed_apply (O : Matrix (Fin v) (Fin m) R) (x : Fin m → R) :
    oilEmbed O x = Fin.append (O *ᵥ x) x :=
  rfl

/-- The oil-space parameterization `x ↦ [O x; x]` is injective because its last `m` coordinates
recover `x` directly ([UOV2026], §3.1, p. 12). -/
theorem oilEmbed_injective (O : Matrix (Fin v) (Fin m) R) :
    Function.Injective (oilEmbed O) := by
  intro x y h
  ext j
  simpa [oilEmbed_apply, Fin.append_right] using congrFun h (finSumFinEquiv (Sum.inr j))

/-- The hidden oil subspace spanned by the columns of `[O; Iₘ]`. -/
def blockOilSubspace (O : Matrix (Fin v) (Fin m) R) :
    Submodule R (Fin (v + m) → R) :=
  LinearMap.range (oilEmbed O)

@[simp]
theorem mem_blockOilSubspace {O : Matrix (Fin v) (Fin m) R} {z : Fin (v + m) → R} :
    z ∈ blockOilSubspace O ↔ ∃ x, oilEmbed O x = z := by
  simp [blockOilSubspace]

/-- Every vector `oilEmbed O x` lies in `blockOilSubspace O`. -/
theorem oilEmbed_mem_blockOilSubspace (O : Matrix (Fin v) (Fin m) R) (x : Fin m → R) :
    oilEmbed O x ∈ blockOilSubspace O :=
  ⟨x, rfl⟩

/-- Candidate UOV signature vector `s = [u; 0] + [O; Iₘ] x = [u + O x; x]`
([UOV2026], §3.1, p. 12). -/
@[expose] def signatureVector (O : Matrix (Fin v) (Fin m) R)
    (u : Fin v → R) (x : Fin m → R) : Fin (v + m) → R :=
  vinegarEmbed u + oilEmbed O x

/-- `signatureVector O u x` equals `Fin.append (u + O *ᵥ x) x`. -/
theorem signatureVector_eq_append (O : Matrix (Fin v) (Fin m) R)
    (u : Fin v → R) (x : Fin m → R) :
    signatureVector O u x = Fin.append (u + O *ᵥ x) x := by
  ext k
  obtain ⟨i | j, rfl⟩ := finSumFinEquiv.surjective k <;>
    simp [signatureVector, vinegarEmbed, oilEmbed_apply]

/-- The lower-right oil block `Pᵢ⁽³⁾ = Upper(-Oᵀ Pᵢ⁽¹⁾ O - Oᵀ Pᵢ⁽²⁾)` ([UOV2026], §3.1, p. 12,
and Figure 2, line 5, p. 16). -/
@[expose] def oilBlock (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R) :
    Matrix (Fin m) (Fin m) R :=
  (-O.transpose * P1 * O - O.transpose * P2).upperQuadratic

/-- In characteristic two, signs drop from `oilBlock`:
`Pᵢ⁽³⁾ = Upper(Oᵀ Pᵢ⁽¹⁾ O + Oᵀ Pᵢ⁽²⁾)`. -/
theorem oilBlock_eq_of_charTwo [CharP R 2] (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R) :
    oilBlock O P1 P2 = (O.transpose * P1 * O + O.transpose * P2).upperQuadratic := by
  rw [oilBlock]; congr 1
  ext i j; simp [Matrix.neg_mul, CharTwo.sub_eq_add, CharTwo.neg_eq]

/-- Assemble the `(v + m) × (v + m)` public polynomial matrix `[[P1, P2], [0, P3]]` indexed on
`Fin (v + m)` via `finSumFinEquiv` ([UOV2026], §3.1, p. 12). -/
@[expose] def blockMatrix (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R)
    (P3 : Matrix (Fin m) (Fin m) R) : Matrix (Fin (v + m)) (Fin (v + m)) R :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks P1 P2 0 P3)

/-- When `P1` and `P3` are upper triangular, the assembled `(v + m) × (v + m)` block matrix is
upper triangular under the standard order on `Fin (v + m)`. -/
theorem isUpperTriangular_blockMatrix {P1 : Matrix (Fin v) (Fin v) R}
    (P2 : Matrix (Fin v) (Fin m) R) {P3 : Matrix (Fin m) (Fin m) R}
    (hP1 : P1.IsUpperTriangular) (hP3 : P3.IsUpperTriangular) :
    (blockMatrix P1 P2 P3).IsUpperTriangular := by
  intro a b hab
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective a <;>
    obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective b
  · simp only [id_eq, finSumFinEquiv_apply_left, Fin.lt_def, Fin.val_castAdd] at hab
    simpa [blockMatrix] using hP1 hab
  · simp only [id_eq, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.lt_def,
      Fin.val_castAdd, Fin.val_natAdd] at hab
    omega
  · simp [blockMatrix]
  · simp only [id_eq, finSumFinEquiv_apply_right, Fin.lt_def, Fin.val_natAdd] at hab
    simpa [blockMatrix] using hP3 (show j < i by omega)

/-- The restricted oil-space matrix `Oᵀ P1 O + Oᵀ P2 + oilBlock O P1 P2` (`[Oᵀ Iₘ] Pᵢ [O; Iₘ]`)
induces an alternating bilinear form in every characteristic ([UOV2026], §3.1, p. 12). -/
theorem isAlt_oilRestriction (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R) :
    (Matrix.toLinearMap₂' R (S₁ := R) (S₂ := R)
      (O.transpose * P1 * O + O.transpose * P2 + oilBlock O P1 P2)).IsAlt := by
  let M : Matrix (Fin m) (Fin m) R := -O.transpose * P1 * O - O.transpose * P2
  rw [show O.transpose * P1 * O + O.transpose * P2 + oilBlock O P1 P2 = M.upperQuadratic - M by
    ext i j
    simp only [oilBlock, M, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_mul, Matrix.neg_apply]
    ring]
  exact Matrix.isAlt_toLinearMap₂'_upperQuadratic_sub M

private theorem append_dotProduct_blockMatrix_mulVec (P1 : Matrix (Fin v) (Fin v) R)
    (P2 : Matrix (Fin v) (Fin m) R) (P3 : Matrix (Fin m) (Fin m) R)
    (a c : Fin v → R) (b d : Fin m → R) :
    Fin.append a b ⬝ᵥ (blockMatrix P1 P2 P3 *ᵥ Fin.append c d) =
      a ⬝ᵥ (P1 *ᵥ c) + a ⬝ᵥ (P2 *ᵥ d) + b ⬝ᵥ (P3 *ᵥ d) := by
  rw [blockMatrix, Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv, dotProduct_comp_equiv_symm,
    Equiv.symm_symm]
  change (Fin.append a b ∘ Sum.elim (Fin.castAdd _) (Fin.natAdd _)) ⬝ᵥ
      (Matrix.fromBlocks P1 P2 0 P3 *ᵥ
        (Fin.append c d ∘ Sum.elim (Fin.castAdd _) (Fin.natAdd _))) = _
  rw [Fin.append_comp_sumElim, Fin.append_comp_sumElim, Matrix.fromBlocks_mulVec,
    sumElim_dotProduct_sumElim]
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, zero_mulVec, zero_add, dotProduct_add]

private theorem toQuadraticForm'_blockMatrix_oilEmbed (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R)
    (P3 : Matrix (Fin m) (Fin m) R) (x : Fin m → R) :
    (blockMatrix P1 P2 P3).toQuadraticForm' (oilEmbed O x) =
      P3.toQuadraticForm' x - (-O.transpose * P1 * O - O.transpose * P2).toQuadraticForm' x := by
  rw [Matrix.toQuadraticForm'_apply, Matrix.toQuadraticForm'_apply, Matrix.toQuadraticForm'_apply,
    oilEmbed_apply, append_dotProduct_blockMatrix_mulVec,
    show (O *ᵥ x) ⬝ᵥ (P1 *ᵥ (O *ᵥ x)) = x ⬝ᵥ ((O.transpose * P1 * O) *ᵥ x) by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_transpose_mulVec, dotProduct_comm],
    show (O *ᵥ x) ⬝ᵥ (P2 *ᵥ x) = x ⬝ᵥ ((O.transpose * P2) *ᵥ x) by
      rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]]
  simp only [Matrix.sub_mulVec, Matrix.neg_mul, Matrix.neg_mulVec, dotProduct_sub, dotProduct_neg]
  ring

/-- **Uniqueness of the oil block `Pᵢ⁽³⁾`** ([UOV2026], §3.1, p. 12): an `m × m` matrix `P3` is
upper triangular and makes `(blockMatrix P1 P2 P3).toQuadraticForm'` vanish on
`blockOilSubspace O` if and only if `P3 = oilBlock O P1 P2`. -/
theorem eq_oilBlock_iff (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R)
    {P3 : Matrix (Fin m) (Fin m) R} :
    (P3.IsUpperTriangular ∧
      MultivariateQuadraticMap.VanishesOn
        (blockMatrix P1 P2 P3).toQuadraticForm' (blockOilSubspace O)) ↔
      P3 = oilBlock O P1 P2 := by
  have hvan : MultivariateQuadraticMap.VanishesOn
      (blockMatrix P1 P2 P3).toQuadraticForm' (blockOilSubspace O) ↔
        P3.toQuadraticForm' = (-O.transpose * P1 * O - O.transpose * P2).toQuadraticForm' :=
    ⟨fun h => by
      ext x
      have hx := h (oilEmbed O x) (oilEmbed_mem_blockOilSubspace O x)
      rwa [toQuadraticForm'_blockMatrix_oilEmbed, sub_eq_zero] at hx,
     fun h _ hz => by
      obtain ⟨x, rfl⟩ := mem_blockOilSubspace.mp hz
      rw [toQuadraticForm'_blockMatrix_oilEmbed, h, sub_self]⟩
  rw [hvan, oilBlock, Matrix.eq_upperQuadratic_iff_toQuadraticForm'_eq]

/-- `i`-th public polynomial matrix `Pᵢ` constructed from `key`. -/
@[expose] def BlockKeyMaterial.publicMatrix (key : BlockKeyMaterial R v m) (i : Fin m) :
    Matrix (Fin (v + m)) (Fin (v + m)) R :=
  blockMatrix (key.vinegarBlock i) (key.mixedBlock i)
    (oilBlock key.oilMatrix (key.vinegarBlock i) (key.mixedBlock i))

/-- Every `key.publicMatrix i` is upper triangular ([UOV2026], §3.1, p. 12, and Figure 2, lines
3–6, p. 16). -/
theorem BlockKeyMaterial.isUpperTriangular_publicMatrix (key : BlockKeyMaterial R v m) (i : Fin m) :
    (key.publicMatrix i).IsUpperTriangular :=
  isUpperTriangular_blockMatrix _ (key.isUpperTriangular_vinegarBlock i)
    (Matrix.isUpperTriangular_upperQuadratic _)

/-- The Round-3 UOV public quadratic map `P : R^{v + m} → R^m` assembled from
`key.publicMatrix`. -/
@[expose] def BlockKeyMaterial.publicMap (key : BlockKeyMaterial R v m) :
    MultivariateQuadraticMap R (Fin (v + m)) (Fin m) :=
  MultivariateQuadraticMap.ofMatrices key.publicMatrix

/-- The constructed public quadratic map vanishes on the entire embedded oil subspace `[O; Iₘ]`. -/
theorem BlockKeyMaterial.publicMap_vanishesOn (key : BlockKeyMaterial R v m) :
    MultivariateQuadraticMap.VanishesOn key.publicMap (blockOilSubspace key.oilMatrix) := by
  intro z hz
  ext i
  exact ((eq_oilBlock_iff key.oilMatrix (key.vinegarBlock i) (key.mixedBlock i)).mpr rfl).2 z hz

/-! ## Signing linearization -/

/-- Precomputed secret-key matrix `Sᵢ = (Pᵢ⁽¹⁾ + Pᵢ⁽¹⁾ᵀ) O + Pᵢ⁽²⁾ ∈ R^{v × m}`
([UOV2026], §3.1, p. 13, and `UOV.ExpandSK`, Figure 2, line 4, p. 16). -/
@[expose] def linearizationMatrix (O : Matrix (Fin v) (Fin m) R)
    (P1 : Matrix (Fin v) (Fin v) R) (P2 : Matrix (Fin v) (Fin m) R) :
    Matrix (Fin v) (Fin m) R :=
  (P1 + P1.transpose) * O + P2

/-- Vinegar evaluation vector `y ∈ R^m` with `yᵢ = uᵀ Pᵢ⁽¹⁾ u` ([UOV2026], §3.1, p. 13). -/
@[expose] def vinegarEval (P1 : Fin m → Matrix (Fin v) (Fin v) R)
    (u : Fin v → R) : Fin m → R :=
  fun i => u ⬝ᵥ (P1 i *ᵥ u)

/-- `key.publicMap` evaluated at `vinegarEmbed u = [u; 0]` equals
`vinegarEval key.vinegarBlock u`. -/
@[simp]
theorem BlockKeyMaterial.publicMap_vinegarEmbed (key : BlockKeyMaterial R v m) (u : Fin v → R) :
    key.publicMap (vinegarEmbed u) = vinegarEval key.vinegarBlock u := by
  ext i
  rw [BlockKeyMaterial.publicMap, MultivariateQuadraticMap.ofMatrices_apply,
    BlockKeyMaterial.publicMatrix, vinegarEmbed, append_dotProduct_blockMatrix_mulVec]
  simp [vinegarEval]

/-- The `m × m` signing linear-system matrix `L` whose `i`-th row is `uᵀ Sᵢ`
([UOV2026], §3.1, p. 13). -/
@[expose] def signingMatrix (S : Fin m → Matrix (Fin v) (Fin m) R)
    (u : Fin v → R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => (u ᵥ* S i) j

@[simp]
theorem signingMatrix_mulVec_apply (S : Fin m → Matrix (Fin v) (Fin m) R)
    (u : Fin v → R) (x : Fin m → R) (i : Fin m) :
    (signingMatrix S u *ᵥ x) i = (u ᵥ* S i) ⬝ᵥ x :=
  rfl

/-- `key`'s signing matrix `L` at vinegar vector `u`. -/
@[expose] def BlockKeyMaterial.signingSystemMatrix (key : BlockKeyMaterial R v m)
    (u : Fin v → R) : Matrix (Fin m) (Fin m) R :=
  signingMatrix
    (fun i => linearizationMatrix key.oilMatrix (key.vinegarBlock i) (key.mixedBlock i)) u

/-- Polar evaluation between `[u; 0]` and `[O x; x]` equals `(uᵀ Sᵢ) x`, retaining the transpose
contribution `Pᵢ⁽¹⁾ᵀ O` in every characteristic. -/
theorem BlockKeyMaterial.polar_vinegarEmbed_oilEmbed_apply (key : BlockKeyMaterial R v m)
    (u : Fin v → R) (x : Fin m → R) (i : Fin m) :
    QuadraticMap.polar key.publicMap (vinegarEmbed u) (oilEmbed key.oilMatrix x) i =
      (u ᵥ* linearizationMatrix key.oilMatrix (key.vinegarBlock i) (key.mixedBlock i)) ⬝ᵥ x := by
  rw [BlockKeyMaterial.publicMap, MultivariateQuadraticMap.polar_ofMatrices_apply,
    BlockKeyMaterial.publicMatrix, vinegarEmbed, oilEmbed_apply,
    append_dotProduct_blockMatrix_mulVec, append_dotProduct_blockMatrix_mulVec]
  simp only [mulVec_zero, dotProduct_zero, zero_dotProduct, add_zero]
  rw [show (key.oilMatrix *ᵥ x) ⬝ᵥ (key.vinegarBlock i *ᵥ u) =
    u ⬝ᵥ ((key.vinegarBlock i).transpose *ᵥ (key.oilMatrix *ᵥ x)) by
      rw [Matrix.dotProduct_transpose_mulVec, dotProduct_comm], ← dotProduct_mulVec]
  simp only [linearizationMatrix, Matrix.add_mul, add_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_add]
  ring

/-- **UOV coordinate signing linearization** ([UOV2026], §3.1, pp. 12–13):
`pᵢ([u; 0] + [O; Iₘ] x) = uᵀ Pᵢ⁽¹⁾ u + (uᵀ Sᵢ) x` in every characteristic. -/
theorem BlockKeyMaterial.publicMap_signatureVector_apply (key : BlockKeyMaterial R v m)
    (u : Fin v → R) (x : Fin m → R) (i : Fin m) :
    key.publicMap (signatureVector key.oilMatrix u x) i =
      u ⬝ᵥ (key.vinegarBlock i *ᵥ u) +
        (u ᵥ* linearizationMatrix key.oilMatrix
          (key.vinegarBlock i) (key.mixedBlock i)) ⬝ᵥ x := by
  simpa only [signatureVector, Pi.add_apply, BlockKeyMaterial.publicMap_vinegarEmbed, vinegarEval,
    QuadraticMap.polarBilin_apply_apply, BlockKeyMaterial.polar_vinegarEmbed_oilEmbed_apply] using
    congrFun (MultivariateQuadraticMap.map_add_of_mem key.publicMap_vanishesOn
      (vinegarEmbed u) (oilEmbed_mem_blockOilSubspace key.oilMatrix x)) i

/-- **UOV vector signing linearization** ([UOV2026], §3.1, p. 13):
`P([u; 0] + [O; Iₘ] x) = y + L x`. -/
theorem BlockKeyMaterial.publicMap_signatureVector (key : BlockKeyMaterial R v m)
    (u : Fin v → R) (x : Fin m → R) :
    key.publicMap (signatureVector key.oilMatrix u x) =
      vinegarEval key.vinegarBlock u + key.signingSystemMatrix u *ᵥ x := by
  ext i; exact key.publicMap_signatureVector_apply u x i

/-- **UOV signing linear-system equivalence** ([UOV2026], §3.1, p. 13, and `UOV.Sign` /
`UOV.Verify`, Figure 2, pp. 16–17): `P([u; 0] + [O; Iₘ] x) = t` if and only if `L x = t - y`. -/
theorem BlockKeyMaterial.publicMap_signatureVector_eq_iff (key : BlockKeyMaterial R v m)
    (u : Fin v → R) (x t : Fin m → R) :
    key.publicMap (signatureVector key.oilMatrix u x) = t ↔
      key.signingSystemMatrix u *ᵥ x = t - vinegarEval key.vinegarBlock u := by
  rw [key.publicMap_signatureVector, add_comm, eq_sub_iff_add_eq]

end BlockConstruction

end Cslib.Crypto.UOV
