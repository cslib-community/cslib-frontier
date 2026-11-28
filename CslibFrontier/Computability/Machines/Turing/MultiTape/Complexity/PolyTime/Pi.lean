/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimePiPrimitives

/-!
# Polynomial-time finite tables

The plain `ComputableInPolyTime.ofFn`, `.pi` and `.pi_apply` rules construct finite tables
and read fixed entries without requiring a default value.
-/
