/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
import CslibFrontier.Computability.WangTile.Robinson.Signals
import CslibFrontier.Computability.WangTile.Robinson.Forcing
import CslibFrontier.Computability.WangTile.Robinson.Realization

/-!
# The concrete Robinson seed-removal map

The finite map first extends a seeded quadrant palette to a pointed-plane palette, then pairs
that palette with the corrected Robinson scaffold. Its computation is primitive recursive.
The concrete forcing and realization theorems discharge both obligations of generic seed
removal: the output tiles the integer plane exactly when the input tiles the seeded quadrant.

## Main definitions

* `removeSeed`: the concrete seeded-to-unseeded palette transformation.

## Main results

* `tilesPlane_removeSeed_iff`: unconditional correctness of concrete seed removal.
* `primrec_removeSeed`: primitive recursiveness for the existing instance encodings.

## References

After [Robinson1971], §7, pp. 201–205 and [JeandelVanier2020], §3.3, Theorem 10, manuscript p. 29.
The assembly follows lean-wang revision `64268a3aaaef3eac65559352ef94f62ab9c00482`:
`LeanWang/Robinson/Final.lean:27–31` (`reduction`) with `LeanWang/Robinson/Reduction.lean:66–86`.
-/

public section

namespace Cslib.WangTile.Robinson

/-- Extend a quadrant seed to a pointed plane and combine it with the concrete scaffold. -/
def removeSeed (I : SeededInstance) : List WangTile :=
  combine scaffold (pointedExtension I)

/-- The concrete seed-removal map is primitive recursive for the tile-list instance codes. -/
theorem primrec_removeSeed : Primrec removeSeed :=
  (primrec_combine scaffold).comp primrec_pointedExtension

/-- The concrete seed-removal palette tiles the plane exactly when the input tiles the seeded
quadrant. Both scaffold properties are proved, with no additional hypothesis. -/
theorem tilesPlane_removeSeed_iff (I : SeededInstance) :
    TilesPlane (removeSeed I) ↔ TilesQuadrant I :=
  tilesPlane_combine_pointedExtension_iff_of_forces_of_realizes
    scaffold_forces scaffold_realizes I

end Cslib.WangTile.Robinson
