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

-- Scaling from the retained rank gives the existing weight with its layer-zero rule.
example {κ : Type} {w n : ℕ} (code : κ → ℕ → Bool) (ctx : κ)
    (rank : Fin (2 ^ codeLength w n)) (z : Fin (n + 1) × Fin w)
    (hcode : ∀ j : Fin (codeLength w n), code ctx j.val = indexedCodewordMod z.2 j) :
    (if z.1.val = 0 then 0 else scaleAccumulatedWeight z.1.val
      (accumulateRank code ⟨ctx, rank.val, codeLength w n⟩)) =
    generatedWeightScan ((BitString.equivFin _).symm rank) z := by
  rw [← SeedDigits.scaledMaskedPrefix_eq_generatedWeightScan _ z (code ctx) hcode]
  simp only [List.length_ofFn, SeedDigits.maskedPrefix_ofFn, accumulateRank_eq_seed]

end CslibFrontierTests.HozaSeedRank
