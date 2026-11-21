/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedRank

/-! Checked clients for carrying a binary seed rank through Hoza's digit scan. -/

set_option linter.privateModule false

namespace CslibFrontierTests.HozaSeedRank

open Cslib Cslib.Reachability.Hoza Cslib.Reachability.Hoza.SeedRank Cslib.Code.JustesenFamily
open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

private def contextBit (ctx : Bool) (_ : ℕ) : Bool := ctx

-- The rank 1 has two implicit zero digits at width 3. The accumulator must still step over them.
example : accumulateRank contextBit ⟨true, 1, 3⟩ = 36 := by decide +kernel

example : ComputableInSpace (accumulateRank contextBit) (encRequest encBool) encNat
    (fun q => (encRequest encBool q).length + q.width) :=
  accumulateRank_inSpace encBool contextBit (fst encBool encNat)

-- The complete native adapter accepts both the retained seed and the layer at runtime.
example : ComputableInSpace (weightRank contextBit) (encWeightRequest encBool) encNat
    (fun q => (encWeightRequest encBool q).length + q.seed.width) :=
  weightRank_inSpace encBool contextBit (fst encBool encNat)

example : weightRank contextBit ⟨⟨true, 1, 3⟩, 0⟩ = 0 := rfl

-- The positive-layer adapter passes the computed accumulator to the existing scaling routine.
example : weightRank contextBit ⟨⟨true, 1, 3⟩, 12⟩ = scaleAccumulatedWeight 12 36 := by
  have ha : accumulateRank contextBit ⟨true, 1, 3⟩ = 36 := by decide +kernel
  change scaleAccumulatedWeight 12 (accumulateRank contextBit ⟨true, 1, 3⟩) = _
  rw [ha]

-- The checker can use the original theorem's weight directly for the retained seed rank.
example {κ : Type} {w n : ℕ} (code : κ → ℕ → Bool) (ctx : κ)
    (rank : Fin (2 ^ codeLength w n)) (z : Fin (n + 1) × Fin w)
    (hcode : ∀ j : Fin (codeLength w n), code ctx j.val = indexedCodewordMod z.2 j) :
    weightRank code ⟨⟨ctx, rank.val, codeLength w n⟩, z.1.val⟩ =
      generatedWeight ((BitString.equivFin _).symm rank) z :=
  weightRank_eq_generatedWeight code ctx rank z hcode

end CslibFrontierTests.HozaSeedRank
