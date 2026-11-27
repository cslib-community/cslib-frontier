/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredParameters
import CslibFrontier.Computability.Complexity.Problems.STCON.LayeredCallback

/-! Checked native initialization and agreement with the layered graph interface. -/

set_option linter.privateModule false

namespace CslibFrontierTests.STCONLayeredParameters

open Cslib.Complexity.STCON Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] (ntm : MultiTapeNTM k Bool State) (c : ℕ)

/-- Native preparation and storage bounds use the original input length. -/
example :
    ComputableInLogSpace (fun w : List Bool => layeredParameters ntm c w.length)
      encBits encLayeredParameters ∧
    ∃ C, ∀ w : List Bool,
      (encLayeredParameters (layeredParameters ntm c w.length)).length ≤
        C * (Nat.log2 w.length + 1) :=
  ⟨layeredParameters_inLogSpace ntm c, length_layeredParameters_le_log ntm c⟩

/-- The binary record supplies the actual endpoint coordinates and common query parameters. -/
example (w : List Bool) :
    let p := layeredParameters ntm c w.length
    let I := configurationInstance ntm c w
    layeredQueryRequest ntm c w (layeredStart I) (layeredTarget I) =
      ⟨p.radix, p.inputLength, 0, p.source, p.width - 1, p.width - 1, none⟩ := by
  rfl

end CslibFrontierTests.STCONLayeredParameters
