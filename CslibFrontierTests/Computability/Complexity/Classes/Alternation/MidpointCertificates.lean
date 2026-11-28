/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Complexity.Classes.Alternation.MidpointCertificates

set_option linter.privateModule false

open Cslib.Complexity Cslib.Reachability

example : midpointCheck Nat.succ 2 1 5 := (midpointCheck_iff _ _ _ _).mpr (by decide)
example : ¬ midpointCheck Nat.succ 2 1 4 := by rw [midpointCheck_iff]; decide

example : (midpointBlocks 8 3).length = 6 ∧ (midpointBlocks 8 3).sum = 27 := by
  rw [midpointBlocks_length, midpointBlocks_sum]
  decide

example : Alternation true (midpointBlocks 2 2)
    (fun z => midpointVerify (List.map Bool.not) 2 2 [true, false] [true, false] z = true) := by
  apply (alternation_midpointVerify_iff (List.map Bool.not) 2 2 [true, false] [true, false]
    (fun _ h => by simpa only [List.length_map] using h) rfl).mpr
  rw [midpointCheck_iff]
  decide

-- On this transcript the first half succeeds and the second half fails.
example :
    midpointVerify (List.map Bool.not) 2 1 [true, false] [false, true] [false, true, false] = true ∧
    midpointVerify (List.map Bool.not) 2 1 [true, false] [false, true] [false, true, true] =
      false := by
  decide

example : reach (fun a b => decide (a.map Bool.not = b)) 1 1 [true] [true] = true := by
  apply reach_of_midpointCheck (List.map Bool.not) 1 1 [true] [true]
  · intro a h
    simpa only [List.length_map] using h
  · rfl
  · rw [midpointCheck_iff]
    decide

-- A zero-step walk can succeed where the one-step deterministic check fails.
example : reach (fun a b => decide (a.map Bool.not = b)) 1 0 [true] [true] = true ∧
    ¬ midpointCheck (List.map Bool.not) 0 [true] [true] := by
  simp [reach, midpointCheck]
