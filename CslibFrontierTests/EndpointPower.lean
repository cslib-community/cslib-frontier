/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Boolean.Iteration.EndpointPower

/-!
# Boundary cases for endpoint checkpoints
-/

namespace CslibFrontierTests.EndpointPower

open Cslib.FunctionalGraph

-- The unique least rank is at the right endpoint of the window starting at 1.
example : IsEndpointCheckpoint Nat.succ (fun i => 3 - i) 2 1 := by
  unfold IsEndpointCheckpoint Function.Injective
  decide

-- With ranks 2, 1, 1 the right endpoint qualifies even though the first minimum is interior.
example : IsEndpointCheckpoint Nat.succ (fun i => if i = 0 then 2 else 1) 2 0 := by
  unfold IsEndpointCheckpoint Function.Injective
  decide

-- Tied ranks qualify a simple window, but a repeated state still disqualifies it.
example : IsEndpointCheckpoint Nat.succ (fun _ => (0 : ℕ)) 2 0 := by
  unfold IsEndpointCheckpoint Function.Injective
  decide

example : ¬ IsEndpointCheckpoint (id : Bool → Bool) (fun _ => (0 : ℕ)) 1 false := by
  unfold IsEndpointCheckpoint Function.Injective
  decide

-- A simple window whose unique minimum is strictly interior is skipped.
example : ¬ IsEndpointCheckpoint Nat.succ (fun i => if i = 1 then 0 else 1) 2 0 := by
  unfold IsEndpointCheckpoint Function.Injective
  decide

end CslibFrontierTests.EndpointPower
