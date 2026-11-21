/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootEndpointResolveShort

open Turing.MultiTapeTM

-- A direct address takes precedence over an invalid scan, including the row numbered zero.
example : RootEndpointResolveShort.run (some ⟨.inl 0, 7⟩, none) = some (0, 7) := by simp

-- Work branches distinguish rejected requests, exhausted searches and found index zero.
example (w : RootEndpointAddress.Work) (column : ℕ) :
    RootEndpointResolveShort.run (some ⟨.inr w, column⟩, none) = none ∧
    RootEndpointResolveShort.run (some ⟨.inr w, column⟩, some none) = some (w.sink, column) ∧
    RootEndpointResolveShort.run (some ⟨.inr w, column⟩, some (some 0)) = some (0, column) := by
  simp [RootEndpointFinish.run]

-- The answer encoding preserves zero-valued bits below the top bit in a successful index.
example :
    ScheduleEndpointAnswer.encAnswer (some (some 4)) = [true, true, false, false, true] ∧
    encOption (encOption encNat) (some (some 4)) = [true, true, false, false, true] := by decide
