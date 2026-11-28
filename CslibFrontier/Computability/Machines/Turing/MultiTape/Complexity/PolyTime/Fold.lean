/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops

/-!
# Polynomial-time folds with invariants

The plain `ComputableInPolyTime.foldl'`, `.foldlWith` and specification rules retain the
reachable-prefix accumulator bound, encoded list layout and left-fold order. Bounded-growth
rules discharge the intermediate-size obligations without changing the program.
-/
