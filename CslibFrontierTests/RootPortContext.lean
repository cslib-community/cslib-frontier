/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPortContext

open Turing.MultiTapeTM RootPortContext

-- A large leaf index preserves the port, raw table and the common prefix bound.
example (a : RootPortQuery.Input) :
    let b := inputOf (word a, 2 ^ 64)
    b.1 = a.1 ∧ b.2.raw = a.2.raw ∧ b.2.context.edge = a.2.context.edge ∧
      b.2.context.candidate = 2 ^ 64 := by
  simp [withCandidate, RootPredecessorContext.withCandidate]
