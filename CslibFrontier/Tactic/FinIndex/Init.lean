/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set of `fin_index`

The simp set that `fin_index` (`CslibFrontier.Tactic.FinIndex`) rewrites with before it calls
`omega`, declared in a file of its own because an attribute cannot be used in the file declaring
it. A simp set is indexed once, when its lemmas are tagged. Listing the lemmas in each call made
`simp` index them at every call: 0.45 to 0.8 s over the 79 calls in
`CslibFrontier/Computability/WordRAM/OfTuring.lean`.

## Main definitions

* `fin_index_simps`: comparisons of `Fin` values as comparisons of numbers, and `Fin.val` through
  constructors, casts and `if`.
-/

public meta section

/-- The simp set `fin_index_simps` turns `a = b`, `a ≠ b`, `a < b` and `a ≤ b` in `Fin n` into
the same comparison of `a.val` and `b.val`, and moves `Fin.val` through the casts of `Fin` and
`if`. `fin_index` rewrites with it and the list given at the call.

Tag the value lemma of a general operation on `Fin`, of the form `(op i).val = …`, when a call
in the library fails without it. Definitions and facts of one development go in the list of the
call, as in `fin_index [stageLeft]`, where an unused entry is reported. -/
register_simp_attr fin_index_simps

end
