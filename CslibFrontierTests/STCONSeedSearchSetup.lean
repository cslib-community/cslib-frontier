/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SeedSearchSetup

/-! Ordinary-import checks for the original-input initializer and its scan endpoints. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSeedSearchSetup

open Cslib.Complexity.STCON Cslib.Reachability.Hoza
open Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)

example :
    ComputableInLogSpace (configurationSeedSearchSetup ntm c) encBits encSeedSearchSetup ∧
    ∃ C, ∀ w : List Bool,
      (encSeedSearchSetup (configurationSeedSearchSetup ntm c w)).length ≤
        C * (Nat.log2 w.length + 1) :=
  ⟨configurationSeedSearchSetup_inLogSpace ntm c, length_configurationSeedSearchSetup_le_log ntm c⟩

-- Both scalar endpoints can be used directly as bounded scan positions.
example (w : List Bool) :
    let s := configurationSeedSearchSetup ntm c w
    let n := s.parameters.search.subdivision.vertexCount
    s.sourceID < n ∧ s.targetID < n :=
  configurationSeedSearchSetup_endpoints_lt_vertexCount ntm c w

end CslibFrontierTests.STCONSeedSearchSetup
