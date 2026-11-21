/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Scale
import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.SeedDigits
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunPropFinite

/-! Checked ordinary-import seed read, masking, and final scaling. -/

set_option linter.privateModule false

namespace CslibFrontierTests.HozaSeedDigits

open Cslib.Reachability.Hoza Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInSpace

private def code (enabled : Bool) (j : ℕ) : Bool :=
  enabled && !(decide (j = 1))

private theorem code_inSpace :
    ComputableInSpace (fun p : Bool × ℕ => code p.1 p.2) (encPair encBool encNat) encBool
      (fun p => (encPair encBool encNat p).length) :=
  budget_boolAnd (fst encBool encNat)
    (budget_boolNot (budget_natEq (snd encBool encNat) (budget_const 1 (.refl _))))

/-- The middle seed bit is masked out by the code callback. -/
example : ((SeedDigits.machine code true).run [true, true, true] 4).accumulator = 37 := by
  rw [show 4 = [true, true, true].length + 1 from rfl, SeedDigits.run_at_end]
  rfl

/-- A raw word in seed index order produces the accumulator of the finite seed function. -/
example {n : ℕ} (seed : Fin n → Bool) :
    ((SeedDigits.machine code true).run (List.ofFn seed) (n + 1)).accumulator =
      accumulateWeightDigits (fun j => code true j.val && seed j) := by
  simpa only [List.length_ofFn, SeedDigits.maskedPrefix_ofFn] using
    congrArg SeedDigits.State.accumulator (SeedDigits.run_at_end code true (List.ofFn seed))

/-- An ordinary-import caller composes the native read-only digit scan and final scaling. -/
example :
    ComputableInSpace
      (fun seed => scaleAccumulatedWeight 12 (SeedDigits.maskedPrefix (code true) seed seed.length))
      encBits encNat List.length := by
  have hscan := SeedDigits.maskedSeed_inSpace encBool code true code_inSpace
  have hpack := budget_prod (budget_const (encB := encNat) 12 (.refl _)) hscan
  exact (budget_comp_linear scaleAccumulatedWeight_inSpace hpack).of_enc_eq fun _ => rfl

open Cslib.Code.JustesenFamily in
/-- The actual raw-word run, followed by guarded scaling, gives the isolation weight. -/
example {w n : ℕ} (seed : Fin (codeLength w n) → Bool) (z : Fin (n + 1) × Fin w)
    (code : ℕ → Bool)
    (hcode : ∀ j : Fin (codeLength w n), code j.val = indexedCodewordMod z.2 j) :
    (if z.1.val = 0 then 0 else
      scaleAccumulatedWeight z.1.val
        (((SeedDigits.machine (fun (_ : Unit) => code) ()).run (List.ofFn seed)
          ((List.ofFn seed).length + 1)).accumulator)) =
      generatedWeight seed z := by
  rw [SeedDigits.run_at_end, ← generatedWeightScan_eq]
  exact SeedDigits.scaledMaskedPrefix_eq_generatedWeightScan seed z code hcode

end CslibFrontierTests.HozaSeedDigits
