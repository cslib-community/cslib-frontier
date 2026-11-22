/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameLocal
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.TameNet

/-!
# Tiers of the parts of a table entry

The table entry is split into the letter decoding, the interval entry and the
old-network entry, each bounded by a separate `tame1` run (one pass), to keep
the proof searches small.
-/

public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term LocalSim _root_.Turing

/-- One pass of `tame`. -/
macro "tame1" : tactic => `(tactic| ((repeat' tame_step) <;> try tame_num))

variable {w : List Bool} {L : ℕ} {env : List ℕ} {k s : ℕ} {State : Type} [DecidableEq State]
  {e : State ≃ Fin s} {machine : MultiTapePTM k Bool State}

end Cslib.Complexity.NtimeDspace.ProgTerm
