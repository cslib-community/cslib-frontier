/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.UOV.Games
public import Mathlib.Algebra.Field.ZMod

/-!
# Ideal UOV generator and game examples

The two-coordinate example distinguishes retained vinegar-square and mixed coefficients from
the removed oil-square coefficient. The zero-vinegar edge is identically zero. Generic callers
instantiate the shared experiments with independent uniform targets, retaining an arbitrary
preimage derivation program instead of supplying a fictitious signer.
-/

public section

noncomputable section

namespace CslibFrontierTests.Crypto.UOVGames

open Cslib Cslib.Crypto Cslib.Crypto.UOV Matrix

/-- The concrete OV polynomial examples use the field with five elements. -/
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- With all raw coefficients equal to one, only the vinegar-square and mixed terms remain. -/
theorem centralMap_two_variables (x : Fin 2 → ZMod 5) :
    centralMap 1 1 (fun _ _ _ => (1 : ZMod 5)) x 0 = x 0 * x 0 + x 0 * x 1 := by
  calc
    centralMap 1 1 (fun _ _ _ => (1 : ZMod 5)) x 0 =
        x ⬝ᵥ ((fun i j : Fin 2 => if i ≤ j ∧ i.val < 1 then (1 : ZMod 5) else 0) *ᵥ x) :=
      MultivariateQuadraticMap.ofMatrices_apply _ _ _
    _ = x 0 * x 0 + x 0 * x 1 := by
      simp [dotProduct, mulVec, Fin.sum_univ_two, mul_add]

-- The same map is zero on oil vectors and nonzero on this vinegar vector.
example : centralMap 1 1 (fun _ _ _ => (1 : ZMod 5)) ![0, 1] = 0 := by
  apply centralMap_vanishesOn
  intro i hi
  have hval : i.val = 0 := Nat.lt_one_iff.mp hi
  have hi0 : i = 0 := Fin.ext hval
  simp [hi0]

example : centralMap 1 1 (fun _ _ _ => (1 : ZMod 5)) ![1, 0] 0 = 1 := by
  simpa using centralMap_two_variables ![1, 0]

example {F : Type} [Field F] (o : ℕ)
    (A : Fin o → Matrix (Fin (0 + o)) (Fin (0 + o)) F) (x : Fin (0 + o) → F) :
    centralMap 0 o A x = 0 := by
  apply centralMap_vanishesOn
  intro i hi
  omega

-- Public oil vectors are obtained by the inverse hiding map, not the forward hiding map.
example {F : Type} [Field F] {v o : ℕ} (key : IdealKeyMaterial F v o)
    (x : Fin (v + o) → F) (hx : x ∈ oilSubspace F v o) :
    key.publicMap (key.inputEquiv.symm x) = 0 := by
  apply key.publicMap_vanishesOn
  change key.inputEquiv (key.inputEquiv.symm x) ∈ oilSubspace F v o
  simpa only [LinearEquiv.apply_symm_apply] using hx

section Games

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {v o N : ℕ}
variable
  (derivePreimage : IdealKeyMaterial F v o → (Fin o → F) →
    ProbComp (Option (Fin (v + o) → F)))

-- Failed derivations remain rejecting outcomes even on the always-solvable zero target.
example (P : MultivariateQuadraticMap F (Fin (v + o)) (Fin o)) :
    (idealRawScheme derivePreimage).verify P 0 none = false := rfl

-- Ordinary inversion does not depend on how the signing oracle would sample preimages.
example
    (otherDerivation : IdealKeyMaterial F v o → (Fin o → F) →
      ProbComp (Option (Fin (v + o) → F)))
    (A : MultivariateQuadraticMap F (Fin (v + o)) (Fin o) → (Fin o → F) →
      ProbComp (Fin (v + o) → F)) :
    Signature.targetExperiment (idealRawScheme derivePreimage)
        (fun _ => ProbComp.uniform (Fin o → F)) (fun pk y => some <$> A pk y) =
      Signature.targetExperiment (idealRawScheme otherDerivation)
        (fun _ => ProbComp.uniform (Fin o → F)) (fun pk y => some <$> A pk y) := rfl

-- The UOV specialization inherits the zero-query relation without reimplementing either game.
example
    (A : MultivariateQuadraticMap F (Fin (v + o)) (Fin o) → (Fin N → Fin o → F) →
      ProbComp (Signature.PreimageClaim N (Option (Fin (v + o) → F)))) :
    Signature.oneMoreExperiment (idealRawScheme derivePreimage)
        (fun _ => ProbComp.uniform (Fin N → Fin o → F)) 0 (Signature.liftMultiTarget A) =
      Signature.multiTargetExperiment (idealRawScheme derivePreimage)
        (fun _ => ProbComp.uniform (Fin N → Fin o → F)) A :=
  Signature.oneMore_liftMultiTarget _ _ _

end Games

end CslibFrontierTests.Crypto.UOVGames
