/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives

/-!
# Polynomial-time option operations

The plain `ComputableInPolyTime.optionSome`, `.optionGetD`, `.optionGetDWithInput`,
`.optionIsSome` and `.optionElimWithInput` rules construct, inspect and eliminate options.
-/
