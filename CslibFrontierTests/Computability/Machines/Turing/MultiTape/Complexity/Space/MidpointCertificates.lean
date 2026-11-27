/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space.MidpointCertificates

set_option linter.privateModule false

open Cslib.Reachability

example : midpointCheck Nat.succ 2 1 5 := (midpointCheck_iff _ _ _ _).mpr (by decide)
example : ¬ midpointCheck Nat.succ 2 1 4 := by rw [midpointCheck_iff]; decide
example : midpointBits 8 3 = 27 := by decide
example : (midpointSchedule 3).length = 6 := by decide
