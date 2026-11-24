/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ArithHelpers
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactClocked

/-!
# The clock and the number of edges

The clock `clk c x = c·x + c` at input length `x`, and the number of edges `edgesN k s t` of the
block network of a machine with `k` work tapes and `s` states at clock `t`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Cslib.Complexity.CountingSimulation

/-- The clock `c·x + c` at input length `x`. -/
abbrev clk (c x : ℕ) : ℕ := c * x + c

/-- The number of edges of the block network at clock `t`. -/
abbrev edgesN (k s t : ℕ) : ℕ :=
  2 * (numBlocks t * (3 * k + 1) * Turing.MultiTapePTM.letterBits k s (blockLength t))

end Cslib.Complexity.NtimeDspace.ProgTerm
