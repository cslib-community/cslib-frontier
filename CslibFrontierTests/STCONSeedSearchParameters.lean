/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.SeedSearchParameters

/-! Ordinary-import checks for native seed-search initialization from the original input. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONSeedSearchParameters

open Cslib.Complexity.STCON Cslib.Reachability.Hoza Cslib.Code.JustesenFamily
open Cslib.LayeredDigraph.Subdivision Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)

example :
    ComputableInLogSpace (configurationSeedSearchParameters ntm c)
      encBits encSeedSearchParameters ∧
    ∃ C, ∀ w : List Bool,
      (encSeedSearchParameters (configurationSeedSearchParameters ntm c w)).length ≤
        C * (Nat.log2 w.length + 1) :=
  ⟨configurationSeedSearchParameters_inLogSpace ntm c,
    length_configurationSeedSearchParameters_le_log ntm c⟩

-- The scan dimensions are those of the actual layer-first configuration graph.
example (w : List Bool) :
    let I := configurationInstance ntm c w
    let p := configurationSeedSearchParameters ntm c w
    p.search.seedWidth = codeLength I.n (I.n - 1) ∧
      p.search.subdivision.vertexCount =
        Nat.card (Vertex (Fin ((I.n - 1) + 1) × Fin I.n) p.search.subdivision.chainBound) :=
  ⟨rfl, subdivisionSize_vertexCount _ _⟩

end CslibFrontierTests.STCONSeedSearchParameters
