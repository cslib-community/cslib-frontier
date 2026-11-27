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

* `fin_index_simps`: comparisons of `Fin` values as comparisons of numbers, `Fin.append` on
  `Fin.castAdd` and `Fin.natAdd`, and `Fin.val` through constructors, casts and `if`.
-/

public meta section

/-- The simp set `fin_index_simps` turns `a = b`, `a ≠ b`, `a < b` and `a ≤ b` in `Fin n` into
the same comparison of `a.val` and `b.val`, reduces `Fin.append` on `Fin.castAdd` and `Fin.natAdd`,
and moves `Fin.val` through the casts of `Fin` and `if`. `fin_index` rewrites with it and the list
given at the call.

A further member is the value lemma `(op i).val = …` of a constructor or cast `op` of the core or
Mathlib `Fin` API (or an unbranched projection such as `Fin.append_left` and `Fin.append_right`),
with a right-hand side that has no case split and stays in `omega`'s fragment, and only when a call
in the library fails without it. Everything else goes in the list of the call, where an unused
entry is reported: a value lemma that branches, such as `val_finRotate`, and the definitions and
facts of one development, as in `fin_index [stageLeft]`. -/
register_simp_attr fin_index_simps

end
