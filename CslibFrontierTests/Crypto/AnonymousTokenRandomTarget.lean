/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.AnonymousToken.RandomTarget
public import CslibFrontier.Crypto.Protocols.UOV.Games

/-!
# Extracted redemption callers

The UOV caller uses the ideal key distribution, optional preimages, and an independently uniform
challenge vector. Concrete transcripts distinguish semantic-message uniqueness from target-value
uniqueness and check that three returned tokens are truncated to two one-more claims at budget one.
-/

public section

namespace CslibFrontierTests.Crypto.AnonymousTokenRandomTarget

open Cslib Cslib.Crypto Cslib.Crypto.AnonymousToken

/-- The generic extracted-redemption reduction applies directly to the failure-aware ideal UOV
certifier and independent uniform target slots. No source signing algorithm is assumed. -/
theorem idealUOV_redemption_le_oneMore {F Message : Type} [Field F] [Fintype F]
    [DecidableEq F] [DecidableEq Message] {v o N : ℕ}
    (derivePreimage : UOV.IdealKeyMaterial F v o → (Fin o → F) →
      ProbComp (Option (Fin (v + o) → F)))
    (slot : Message ↪ Fin N) (budget : ℕ)
    (A : MultivariateQuadraticMap F (Fin (v + o)) (Fin o) → (Fin N → Fin o → F) →
      ProbOracleComp (fun _ : Fin o → F => Option (Fin (v + o) → F))
        (List (Token Message Unit (Option (Fin (v + o) → F))))) :
    Experiment.succProbability
        (extractedRedemptionExperiment (UOV.idealRawScheme derivePreimage)
          (fun _ => ProbComp.uniform (Fin N → Fin o → F)) slot budget A) ≤
      Experiment.succProbability
        (Signature.oneMoreExperiment (UOV.idealRawScheme derivePreimage)
          (fun _ => ProbComp.uniform (Fin N → Fin o → F)) budget
          (reduceRedemptions slot budget A)) :=
  extractedRedemption_succProbability_le _ _ _ _ _

private def identityCertifier : Signature.Scheme Unit Unit Bool Bool where
  keyGen := pure ((), ())
  sign := fun _ target => pure target
  verify := fun _ target signature => decide (signature = target)

-- Distinct messages may certify colliding target values. A one-call transcript permits two
-- claims, and three valid redemptions therefore pass the extracted test.
example : extractedRedemptionAccept identityCertifier () (fun _ : Fin 3 => true)
    (Function.Embedding.refl (Fin 3)) 1
    [⟨⟨0, ()⟩, true⟩, ⟨⟨1, ()⟩, true⟩, ⟨⟨2, ()⟩, true⟩] [(false, false)] = true := by
  simp [extractedRedemptionAccept, Token.valid, identityCertifier]

-- Repeating a semantic message fails even when every listed witness verifies.
example : extractedRedemptionAccept identityCertifier () (fun _ : Fin 3 => true)
    (Function.Embedding.refl (Fin 3)) 1
    [⟨⟨0, ()⟩, true⟩, ⟨⟨0, ()⟩, true⟩, ⟨⟨2, ()⟩, true⟩] [] = false := by
  simp [extractedRedemptionAccept, Token.valid, identityCertifier]

-- The reduction returns exactly the prefix required by the fixed-budget one-more game.
example : reduceRedemptions (Function.Embedding.refl (Fin 3)) 1
    (fun (_ : Unit) (_ : Fin 3 → Bool) => pure
      [⟨⟨0, ()⟩, true⟩, ⟨⟨1, ()⟩, true⟩, ⟨⟨2, ()⟩, true⟩]) () (fun _ => true) =
    pure ([⟨0, true⟩, ⟨1, true⟩] : List (Signature.PreimageClaim 3 Bool)) := by
  simp [reduceRedemptions]

example {PK Message Target Sig : Type} {N : ℕ} (slot : Message ↪ Fin N) (budget : ℕ)
    (A : PK → (Fin N → Target) →
      ProbOracleComp (fun _ : Target => Sig) (List (Token Message Unit Sig)))
    (pk : PK) (targets : Fin N → Target) {queries : ℕ}
    (h : (A pk targets).IsQueryBounded queries) :
    (reduceRedemptions slot budget A pk targets).IsQueryBounded queries :=
  reduceRedemptions_queryBound slot budget A pk targets h

end CslibFrontierTests.Crypto.AnonymousTokenRandomTarget
