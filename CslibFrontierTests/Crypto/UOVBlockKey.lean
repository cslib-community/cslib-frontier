/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.UOV.BlockKey
public import CslibFrontier.Crypto.Protocols.UOV.Field
public import Mathlib.Algebra.Field.ZMod

/-!
# Characteristic-two and Round-3 field clients of UOV block keys and signing linearization

These ordinary-import clients exercise `Cslib.Crypto.UOV.BlockKeyMaterial` directly over `ZMod 2`
and the Round-3 concrete fields `UOV.F16` and `UOV.F256`:

1. A concrete characteristic-two `(v = 2, m = 2)` instance over `ZMod 2` with nonzero `O`,
   non-symmetric upper-triangular `P₀⁽¹⁾`, nonzero mixed block `P₁⁽²⁾`, and solved nontrivial
   target `t = ![1, 1]`. Regression guards verify that dropping the `Pᵢ⁽¹⁾ᵀ O` transpose term,
   dropping the mixed block `Pᵢ⁽²⁾`, or omitting the `O x` oil-embedding term from `s` each breaks
   the linear system or produces a vector rejected by `key.publicMap`.
2. Direct instantiations over `UOV.F16` (`q = 16`) and `UOV.F256` (`q = 256`), alongside proofs
   that `ZMod 16` and `ZMod 256` are not domains, verifying characteristic two, field cardinalities
   `16` and `256`, upper-triangularity of `key.publicMatrix`, oil-subspace vanishing, and signing
   correctness via `BlockKeyMaterial.publicMap_signatureVector_eq_iff` without unfolding matrix
   bodies.
-/

public section

namespace CslibFrontierTests.Crypto.UOVBlockKey

open Cslib Cslib.Crypto Cslib.Crypto.UOV Matrix

/-- Concrete `(v = 2, m = 2)` characteristic-two expanded key material with non-symmetric
upper-triangular `P₀⁽¹⁾`, nonzero `O`, and nonzero mixed block `P₁⁽²⁾`. -/
def charTwoKey : BlockKeyMaterial (ZMod 2) 2 2 where
  oilMatrix := !![1, 0; 0, 1]
  vinegarBlock
    | 0 => !![1, 1; 0, 0]
    | 1 => 0
  mixedBlock
    | 0 => 0
    | 1 => !![1, 0; 0, 1]
  isUpperTriangular_vinegarBlock i a b hab := by
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp at hab ⊢

private def sampleVinegar : Fin 2 → ZMod 2 := ![0, 1]
private def sampleTarget : Fin 2 → ZMod 2 := ![1, 1]
private def sampleOilSolution : Fin 2 → ZMod 2 := ![1, 1]

/-- Both public matrices of `charTwoKey` are upper triangular directly from `BlockKeyMaterial`. -/
theorem charTwoKey_upper (i : Fin 2) :
    (charTwoKey.publicMatrix i).IsUpperTriangular :=
  charTwoKey.isUpperTriangular_publicMatrix i

-- Solved linear system `L x = t - y` over `ZMod 2`.
private theorem charTwoKey_solves_linear_system :
    charTwoKey.signingSystemMatrix sampleVinegar *ᵥ sampleOilSolution =
      sampleTarget - vinegarEval charTwoKey.vinegarBlock sampleVinegar := by
  decide

-- Signing correctness follows directly from `publicMap_signatureVector_eq_iff` without unfolding
-- matrix helpers.
example :
    charTwoKey.publicMap
      (signatureVector charTwoKey.oilMatrix sampleVinegar sampleOilSolution) =
        sampleTarget :=
  (charTwoKey.publicMap_signatureVector_eq_iff
    sampleVinegar sampleOilSolution sampleTarget).mpr charTwoKey_solves_linear_system

-- Regression 1: dropping the `Pᵢ⁽¹⁾ᵀ O` transpose contribution breaks the signing linear system.
example :
    let wrongS : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i =>
      charTwoKey.vinegarBlock i * charTwoKey.oilMatrix + charTwoKey.mixedBlock i
    signingMatrix wrongS sampleVinegar *ᵥ sampleOilSolution ≠
      sampleTarget - vinegarEval charTwoKey.vinegarBlock sampleVinegar := by
  decide

-- Regression 2: dropping the mixed block `Pᵢ⁽²⁾` breaks the signing linear system.
example :
    let wrongS : Fin 2 → Matrix (Fin 2) (Fin 2) (ZMod 2) := fun i =>
      (charTwoKey.vinegarBlock i + (charTwoKey.vinegarBlock i).transpose) *
        charTwoKey.oilMatrix
    signingMatrix wrongS sampleVinegar *ᵥ sampleOilSolution ≠
      sampleTarget - vinegarEval charTwoKey.vinegarBlock sampleVinegar := by
  decide

-- Regression 3: omitting the `O x` oil-embedding contribution from `s` (`[u; x]` instead of
-- `[u + O x; x]`) fails public-key verification at `sampleTarget`.
example :
    charTwoKey.publicMap (Fin.append sampleVinegar sampleOilSolution) ≠ sampleTarget := by
  decide

/-! ## Round-3 `UOV.F16` (`GF(16)`) and `UOV.F256` (`GF(256)`) clients -/

-- `UOV.F16` and `UOV.F256` have orders `16` and `256` and are characteristic-two fields, whereas
-- `ZMod 16` and `ZMod 256` have nontrivial zero divisors (`4 * 4 = 0`, `16 * 16 = 0`).
example :
    Fintype.card F16 = 16 ∧
      Fintype.card F256 = 256 ∧
      ¬ IsDomain (ZMod 16) ∧ ¬ IsDomain (ZMod 256) := by
  refine ⟨BinaryField.card (w := 4) (by decide), BinaryField.card (w := 8) (by decide), ?_, ?_⟩
  · intro h
    have hz : (4 : ZMod 16) * 4 = 0 := by decide
    rcases mul_eq_zero.mp hz with h4 | h4 <;> revert h4 <;> decide
  · intro h
    have hz : (16 : ZMod 256) * 16 = 0 := by decide
    rcases mul_eq_zero.mp hz with h16 | h16 <;> revert h16 <;> decide

/-- Over `UOV.F256` (`q = 256`) and any dimensions `(v, m)`, every `BlockKeyMaterial` yields
upper-triangular public matrices, embeds its `m` oil coordinates injectively and linearly, vanishes
on its embedded oil space, and certifies any solution of its `m × m` signing linear system without
unfolding matrix definitions. -/
theorem f256_signing_correct {v m : ℕ}
    (key : BlockKeyMaterial F256 v m)
    (u : Fin v → F256) (x t : Fin m → F256)
    (hx : key.signingSystemMatrix u *ᵥ x = t - vinegarEval key.vinegarBlock u) :
    (∀ i, (key.publicMatrix i).IsUpperTriangular) ∧
      Function.Injective (oilEmbed key.oilMatrix) ∧
      key.publicMap (oilEmbed key.oilMatrix x) = 0 ∧
      key.publicMap (signatureVector key.oilMatrix u x) = t :=
  ⟨key.isUpperTriangular_publicMatrix,
    oilEmbed_injective key.oilMatrix,
    key.publicMap_vanishesOn _ (oilEmbed_mem_blockOilSubspace key.oilMatrix x),
    (key.publicMap_signatureVector_eq_iff u x t).mpr hx⟩

/-- Uniqueness check on `charTwoKey`: any upper-triangular `2 × 2` lower-right block making the
assembled `4 × 4` block matrix vanish on `blockOilSubspace charTwoKey.oilMatrix` must equal
`oilBlock`. -/
example (i : Fin 2) (P3 : Matrix (Fin 2) (Fin 2) (ZMod 2))
    (hP3 : P3.IsUpperTriangular)
    (hvan : MultivariateQuadraticMap.VanishesOn
      (blockMatrix (charTwoKey.vinegarBlock i) (charTwoKey.mixedBlock i) P3).toQuadraticForm'
      (blockOilSubspace charTwoKey.oilMatrix)) :
    P3 = oilBlock charTwoKey.oilMatrix (charTwoKey.vinegarBlock i) (charTwoKey.mixedBlock i) :=
  (eq_oilBlock_iff _ _ _).mp ⟨hP3, hvan⟩

/-- Concrete non-symmetric characteristic-two check over `UOV.F16` (`GF(16)`): `1 + 1 = 0`, while
solving `L x = t - y` over `F16` yields a valid preimage of `t`. -/
noncomputable example :
    let α : F16 := AdjoinRoot.root (leastIrreducible 4)
    let key : BlockKeyMaterial F16 2 1 :=
      { oilMatrix := !![1; α]
        vinegarBlock := fun _ => !![1, α; 0, 1]
        mixedBlock := fun _ => !![α; 1]
        isUpperTriangular_vinegarBlock := fun _ a b hab => by
          fin_cases a <;> fin_cases b <;> simp at hab ⊢ }
    let u : Fin 2 → F16 := ![0, 1]
    let x : Fin 1 → F16 := ![1]
    let t : Fin 1 → F16 := vinegarEval key.vinegarBlock u + key.signingSystemMatrix u *ᵥ x
    (1 : F16) + 1 = 0 ∧ key.publicMap (signatureVector key.oilMatrix u x) = t :=
  ⟨CharTwo.add_self_eq_zero 1,
    (BlockKeyMaterial.publicMap_signatureVector_eq_iff _ _ _ _).mpr (by simp)⟩

end CslibFrontierTests.Crypto.UOVBlockKey
