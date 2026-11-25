/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Algorithms.Lean.Query.Sort.LEQuery

/-!
# The comparison oracle of a key function

`Cslib.Query.LEQuery.keyOracle key` answers the comparison `a ≤ b` of the query model
`FreeM (LEQuery α)` by comparing the keys `key a ≤ key b` in a linear order. Comparing edges by
their weights `w : E → W` is the oracle of the weight function, as in the comparison (decision
tree) complexity of minimum spanning forests, where a program may compare edge weights but never
see them.

## Main definitions

* `Cslib.Query.LEQuery.keyOracle`: the comparison oracle of `key : α → W`.
-/

public section

namespace Cslib.Query

variable {α : Type} {W : Type*}

/-- The comparison oracle of a key function: `a ≤ b` is answered by `key a ≤ key b`. -/
@[expose] def LEQuery.keyOracle [LE W] [DecidableLE W] (key : α → W) :
    {ι : Type} → LEQuery α ι → ι :=
  LEQuery.oracleOf fun a b => decide (key a ≤ key b)

@[simp] theorem LEQuery.keyOracle_le [LE W] [DecidableLE W] (key : α → W) (a b : α) :
    LEQuery.keyOracle key (.le a b) = decide (key a ≤ key b) :=
  rfl

end Cslib.Query
