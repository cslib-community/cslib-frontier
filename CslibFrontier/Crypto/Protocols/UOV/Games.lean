/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.Signature.OneMore
public import CslibFrontier.Foundations.LinearAlgebra.MultivariateQuadratic
public import Mathlib.Data.FunLike.Fintype

/-!
# Ideal UOV keys and raw preimage certification

The ideal UOV problem samples `o` homogeneous oil-and-vinegar quadratic polynomials in `v + o`
variables and an independent uniform invertible linear change of input variables. Here the first
`v` coordinates are vinegar coordinates and the last `o` are oil coordinates. A full coefficient
table is sampled uniformly, and only entries `i ≤ j` with `i < v` contribute to the central map.
Thus each allowed quadratic monomial has an independent uniform coefficient, while no oil-oil
monomial occurs. Unused entries are retained as secret randomness irrelevant to the public map.
The public map is
`P = Q ∘ T`, with `T` the hiding equivalence. This is the ideal key distribution of
[UOV2026, Appendix A, Definition 2, p. 49], not its seed-expanded implementation key generation.

`idealRawScheme` packages these keys and equality verification in the shared `Signature.Scheme`
interface. Its total finite preimage derivation program returns an optional preimage: `none`
records failure and always rejects, while `some s` is checked by `P s = target`. Failure
probability is retained without conditioning. This matters even for ideal keys, whose support
includes zero maps. The program is an explicit parameter: the construction asserts neither that
it succeeds nor that it has UOV's source signing distribution or unbounded retry behavior.
Implementing and verifying that algorithm remains issue #4987, with the algebraic precursor
in #5219.

For the ordinary UOV experiment, pass this scheme and the independent sampler
`fun _ => ProbComp.uniform (Fin o → F)` to `Signature.targetExperiment`. For the multiple-target
and one-more variants, pass `fun _ => ProbComp.uniform (Fin N → Fin o → F)` to
`Signature.multiTargetExperiment` or `Signature.oneMoreExperiment`. The latter samples all
targets independently and retains the exact supplied preimage-oracle distribution. The ordinary
experiment never invokes that oracle; ordinary preimage answers embed using `some`. Target
sampling is not the image of a sampled preimage.
These are exact finite classical programs; finite enumeration here carries no efficiency
certificate, asymptotic hardness assertion, or quantum random-oracle claim.

## Main definitions

* `IdealKeyMaterial`: the coefficient table and hiding equivalence.
* `centralMap`, `oilSubspace`: the OV polynomial map and its coordinate oil subspace.
* `IdealKeyMaterial.publicMap`: the hidden quadratic map.
* `idealKeyGen`, `idealRawScheme`: ideal key sampling and parameterized raw certification.

## Main results

* `centralMap_vanishesOn`: the central map vanishes on the entire oil subspace.
* `IdealKeyMaterial.publicMap_vanishesOn`: the public map vanishes on its hidden preimage.

## References

* [W. Beullens et al., *UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting
  Documentation*, v3.0, Appendix A, Definition 2, p. 49][UOV2026]
* [Baum et al., *PoMFRIT*, USENIX prepublication, Definition 3.1][PoMFRIT2026]
-/

public section

namespace Cslib.Crypto.UOV

open Matrix
open scoped BigOperators

variable {F : Type} [Field F] {v o : ℕ}

/-- Ideal OV coefficient randomness together with an independently sampled input hiding map.
Only upper-triangular entries having a vinegar row contribute to the polynomial map. -/
structure IdealKeyMaterial (F : Type) [Field F] (v o : ℕ) where
  /-- Uniform independent coefficients; inactive entries are ignored by `centralMap`. -/
  coefficients : Fin o → Matrix (Fin (v + o)) (Fin (v + o)) F
  /-- The invertible map from public input coordinates to central input coordinates. -/
  inputEquiv : (Fin (v + o) → F) ≃ₗ[F] (Fin (v + o) → F)

/-- The homogeneous OV map with one independent coefficient for every allowed monomial.
Upper-triangular indexing counts each monomial once, including in characteristic two. -/
@[expose] def centralMap (v o : ℕ)
    (A : Fin o → Matrix (Fin (v + o)) (Fin (v + o)) F) :
    MultivariateQuadraticMap F (Fin (v + o)) (Fin o) :=
  MultivariateQuadraticMap.ofMatrices fun k i j =>
    if i ≤ j ∧ i.val < v then A k i j else 0

/-- Vectors whose vinegar coordinates vanish; the remaining coordinates are the oil variables. -/
@[expose] def oilSubspace (F : Type) [Field F] (v o : ℕ) :
    Submodule F (Fin (v + o) → F) where
  carrier := {x | ∀ i, i.val < v → x i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy i hi
    simp [hx i hi, hy i hi]
  smul_mem' := by
    intro a x hx i hi
    simp [hx i hi]

/-- Every monomial contains a vinegar variable, so the entire central oil subspace maps to zero. -/
theorem centralMap_vanishesOn
    (A : Fin o → Matrix (Fin (v + o)) (Fin (v + o)) F) :
    MultivariateQuadraticMap.VanishesOn (centralMap v o A) (oilSubspace F v o) := by
  intro x hx
  change ∀ i, i.val < v → x i = 0 at hx
  ext k
  calc
    centralMap v o A x k =
        x ⬝ᵥ ((fun i j => if i ≤ j ∧ i.val < v then A k i j else 0) *ᵥ x) :=
      MultivariateQuadraticMap.ofMatrices_apply _ _ _
    _ = 0 := by
      change (∑ i, x i * ∑ j,
        (if i ≤ j ∧ i.val < v then A k i j else 0) * x j) = 0
      apply Finset.sum_eq_zero
      intro i _
      by_cases hv : i.val < v
      · rw [hx i hv, zero_mul]
      · simp [hv]

/-- The public UOV map, with hiding orientation `P = Q ∘ T`. -/
@[expose] def IdealKeyMaterial.publicMap (key : IdealKeyMaterial F v o) :
    MultivariateQuadraticMap F (Fin (v + o)) (Fin o) :=
  (centralMap v o key.coefficients).comp key.inputEquiv.toLinearMap

/-- Input hiding transports the central oil subspace by the inverse image of the hiding map. -/
theorem IdealKeyMaterial.publicMap_vanishesOn (key : IdealKeyMaterial F v o) :
    MultivariateQuadraticMap.VanishesOn key.publicMap
      ((oilSubspace F v o).comap key.inputEquiv.toLinearMap) :=
  (centralMap_vanishesOn key.coefficients).comp_comap key.inputEquiv.toLinearMap

/-- Exact ideal key generation: independent uniform coefficient entries and uniform invertible
input hiding. Enumerating all linear equivalences is a finite model, not an efficiency claim. -/
@[expose] noncomputable def idealKeyGen (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (v o : ℕ) :
    ProbComp (MultivariateQuadraticMap F (Fin (v + o)) (Fin o) × IdealKeyMaterial F v o) := by
  letI : Fintype ((Fin (v + o) → F) ≃ₗ[F] (Fin (v + o) → F)) := FunLike.fintype _
  letI : Nonempty ((Fin (v + o) → F) ≃ₗ[F] (Fin (v + o) → F)) :=
    ⟨LinearEquiv.refl F _⟩
  exact do
    let coefficients ← ProbComp.uniform (Fin o → Matrix (Fin (v + o)) (Fin (v + o)) F)
    let inputEquiv ← ProbComp.uniform ((Fin (v + o) → F) ≃ₗ[F] (Fin (v + o) → F))
    let key : IdealKeyMaterial F v o := ⟨coefficients, inputEquiv⟩
    return (key.publicMap, key)

/-- Ideal UOV keys and the caller's exact finite preimage derivation program, with explicit
failure. `none` rejects; `some s` verifies by equality. Failure probability is not conditioned
away. This definition does not claim signer correctness or instantiate the source signer. -/
@[expose] noncomputable def idealRawScheme [Fintype F] [DecidableEq F]
    (derivePreimage : IdealKeyMaterial F v o → (Fin o → F) →
      ProbComp (Option (Fin (v + o) → F))) :
    Signature.Scheme (MultivariateQuadraticMap F (Fin (v + o)) (Fin o))
      (IdealKeyMaterial F v o) (Fin o → F) (Option (Fin (v + o) → F)) where
  keyGen := idealKeyGen F v o
  sign := derivePreimage
  verify := fun P target preimage =>
    match preimage with
    | none => false
    | some s => decide (P s = target)

end Cslib.Crypto.UOV
