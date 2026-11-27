/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Robinson.Signals
import CslibFrontier.Computability.WangTile.Robinson.FreeGrid.Obstruction

/-!
# Seeded payload squares in combined Robinson tilings

Every plane tiling of the concrete scaffold has arbitrarily large routed grids. The generic
routing theorem extracts a seeded payload square of each size from any combined tiling.

## Main results

* `scaffold_forces`: forward seed removal for the concrete Robinson scaffold.

## References

After [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3),
revision `64268a3`, `Closed104.OrientedLightForward`, line 32:
the consecutive marked light grid and crossing obstruction are unchanged mathematical
ingredients; payload propagation is supplied by the generic `forces_of_routedGrids`.
-/

public section
namespace Cslib.WangTile.Robinson

/-- Every tiling of the scaffold combined with a seeded payload contains seeded payload
squares of every size. There are no assumptions on the scaffold beyond its definition. -/
theorem scaffold_forces : Forces scaffold := by
  apply forces_of_routedGrids
  intro P n
  let D := DecodedPlane.ofPlane P
  let R := QuarterPlane.regroup D.quarterPlane
  obtain ⟨a, b, scale, cycle, shaded, ⟨grid⟩⟩ := exists_markedFreeGrid D R n
  exact ⟨grid.routedGrid D R a b cycle shaded⟩

end Cslib.WangTile.Robinson
