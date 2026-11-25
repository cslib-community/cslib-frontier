/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Correct

/-!
# Tests for the Hennie–Stearns simulation

The levels of three moves of a blank track sum to `2 ^ 0 + 2 ^ 1 + 2 ^ 0`.
-/

namespace CslibFrontierTests.HennieStearns

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.HennieStearns

/-- Two moves to the right reach levels `0` and `1`, and a move back to the left level `0`. -/
example : (blankTrack (Symbol := Bool)).cost 0 [.R, .R, .L] = 4 := by decide

end CslibFrontierTests.HennieStearns
