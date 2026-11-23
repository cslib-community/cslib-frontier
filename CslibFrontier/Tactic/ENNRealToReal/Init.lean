/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# The simp set `ennreal_toReal`

Declares the simp set `ennreal_toReal`, in a file of its own because an attribute cannot be used
in the file declaring it. `CslibFrontier.Tactic.ENNRealToReal` tags its lemmas and defines the
tactic `ennreal_to_real` that uses it.

## Main definitions

* `ennreal_toReal`: pushes `ENNReal.toReal` through the arithmetic of a finite expression.
-/

public meta section

/-- The simp set `ennreal_toReal` pushes `ENNReal.toReal` towards the leaves of an expression:
through `+`, `*`, `∑`, `∏`, `∑'`, natural and real `^`, `⁻¹`, `/`, truncated `-`, `if … then …
else …`, numerals, casts and `ENNReal.ofReal`. The lemmas for `+`, `∑`, `∑'`, `-` and
`ENNReal.ofReal` have side conditions, so the set is meant for
`simp (disch := ennreal_to_real_side) only [ennreal_toReal]`, which is what the tactic
`ennreal_to_real` runs. -/
register_simp_attr ennreal_toReal

end
