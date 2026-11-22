/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.LocalCount
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ParamTerm

/-!
# Values of the decider's terms

The number of vertices, the identifier width, the local radix and the number
of copies, as functions of the input length.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing Cslib.Complexity.CountingSimulation

variable {w : List Bool} {k s c : ℕ} {xT : Term} {env : List ℕ} {x : ℕ}
  (hx : StableAt w xT env) (hxv : xT.denote w env = x)
include hx hxv

/-- The number of vertices of the block network at clock `t`. -/
abbrev verticesN (k s t : ℕ) : ℕ :=
  numBlocks t * (3 * k + 2) + numBlocks t * (3 * k + 1) * MultiTapePTM.letterBits k s
      (blockLength t)

end Cslib.Complexity.NtimeDspace.ProgTerm
