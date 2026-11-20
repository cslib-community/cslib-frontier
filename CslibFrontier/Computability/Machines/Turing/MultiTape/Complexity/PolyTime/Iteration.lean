/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops

/-!
# Polynomial-time iteration with invariants

The plain `ComputableInPolyTime.iterate`, `.iterateWith` and specification rules retain
the unary iteration count and all intermediate-state bounds. Captured parameters share one
uniform joint step certificate; bounded-growth rules retain the same growth contract.
-/
