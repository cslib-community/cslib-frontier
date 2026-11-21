/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Algorithms.Reachability.MinIsolation.Generator.Scale
import Mathlib.Data.Nat.PadicValNat

/-! Checked native scaling of Hoza's completed accumulator. -/

set_option linter.privateModule false

namespace CslibFrontierTests.HozaWeightScale

open Cslib.Reachability.Hoza Turing.MultiTapeTM

/-- A caller can retain the layer and accumulator as binary fields for the native scaling. -/
example :
    ComputableInSpace (fun p : ℕ × ℕ => scaleAccumulatedWeight p.1 p.2)
      (encPair encNat encNat) encNat (fun p => (encPair encNat encNat p).length) :=
  scaleAccumulatedWeight_inSpace

/-- An even layer with an odd part uses two factors of six. -/
example : scaleAccumulatedWeight 12 5 = 180 := by
  have h : multiplicity (2 : ℕ) 12 = 2 :=
    multiplicity_eq_of_dvd_of_not_dvd (by decide) (by decide)
  simpa only [scaleAccumulatedWeight, Nat.padicValNat_def, h] using
    (show (6 : ℕ) ^ 2 * 5 = 180 by decide)

end CslibFrontierTests.HozaWeightScale
