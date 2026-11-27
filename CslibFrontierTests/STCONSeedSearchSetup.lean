/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SeedSearchSetup

/-! Ordinary-import checks for the original-input initializer and its scan sources. -/

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

-- The indexed loop can compute the next source from the setup it already retains.
example :
    ComputableInSpace (fun p : SeedSearchSetup × ℕ => p.1.originalSourceID p.2)
      (encPair encSeedSearchSetup encNat) encNat
      (fun p => (encPair encSeedSearchSetup encNat p).length) :=
  originalSourceID_inSpace

example (w : List Bool) :
    let I := configurationInstance ntm c w
    let s := configurationSeedSearchSetup ntm c w
    let index := subdivisionIndex I s.parameters.search.subdivision.chainBound
    s.parameters.search.subdivision.originalCount = ((I.n - 1) + 1) * I.n ∧
    ∀ position : Fin (((I.n - 1) + 1) * I.n),
      s.originalSourceID position.val = (originalRootID index position).val :=
  ⟨configurationSeedSearchSetup_originalCount ntm c w,
    configurationSeedSearchSetup_originalSourceID_eq ntm c w⟩

example (w : List Bool) :
    let s := configurationSeedSearchSetup ntm c w
    ∀ {position : ℕ}, position < s.parameters.search.subdivision.originalCount →
      s.originalSourceID position < s.parameters.search.subdivision.vertexCount :=
  configurationSeedSearchSetup_originalSourceID_lt_vertexCount ntm c w

end CslibFrontierTests.STCONSeedSearchSetup
