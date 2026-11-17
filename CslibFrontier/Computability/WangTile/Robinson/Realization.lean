/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Carrier.Corners

/-!
# Pointed payload realization by the Robinson scaffold

Canonical seed patches have compatible integer carrier addresses and assign address zero to
every corner marker. Their unbounded side lengths therefore realize any pointed payload plane,
by finite-square compactness through the generic routed construction. Each marked board
places the seed at its center and carries a window of the input pointed plane.

## Main results

* `scaffold_realizes`: every pointed payload plane lifts to a plane of the concrete combination.

## References

After [Robinson1971], §7, pp. 201–205 and [JeandelVanier2020], §3.3, Theorem 10, manuscript p. 29.
Ported from lean-wang revision `64268a3aaaef3eac65559352ef94f62ab9c00482`,
`Robinson/Closed104/ShadedCarrierCornerAddressing.lean:435–440`.
-/

public section

namespace Cslib.WangTile.Robinson

/-- The concrete corrected Robinson scaffold realizes every plane whose payload seed is at
its origin. No property of the scaffold is assumed: canonical addressed patches supply it. -/
theorem scaffold_realizes : Realizes scaffold := by
  apply realizes_of_addressedSquares
  intro n
  refine ⟨Canonical.side (n + 1) - 1, ?_, ⟨Carrier.canonicalAddressing (n + 1)⟩⟩
  have := Canonical.lt_side (n + 1)
  omega

end Cslib.WangTile.Robinson
