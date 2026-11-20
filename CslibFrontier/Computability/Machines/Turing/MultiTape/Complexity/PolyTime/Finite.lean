/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeFinitePrimitives

/-!
# Polynomial-time finite dispatch

The plain `ComputableInPolyTime.finite_cases` rule certifies dispatch on a computed finite tag,
including the captured input. Neither the tag nor the result needs a default inhabitant.
-/
