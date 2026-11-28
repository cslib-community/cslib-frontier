/-
Copyright (c) 2026 lean-wang contributors, Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.5/5.6, Chris Henson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WangTile.Basic
public import Mathlib.Computability.RE
import CslibFrontier.Computability.WangTile.SeededUndecidable
import CslibFrontier.Computability.WangTile.Robinson.Reduction
import Mathlib.Computability.Reduce

/-!
# Undecidability of the domino problem

Berger's theorem states that no algorithm decides whether a finite Wang palette tiles the
integer plane. Instances here are `List WangTile`; `Primcodable WangTile` is the instance from
`Basic`, through the explicit tuple equivalence `(top, bottom, left, right)`. Tiles have fixed
orientation and natural-number edge colours, with right/left and top/bottom adjacency matching.
There is no prescribed tile, promise on the palette, or hypothesis about a scaffold.

The proof is after Robinson (1971), in Ollinger's (2008) 104-tile form as presented by
Jeandel–Vanier (2020). It is ported and restructured from lean-wang revision
`64268a3aaaef3eac65559352ef94f62ab9c00482`, the prior formalization. Its record has fields
`(n, s, e, w)` and its abstract tiles are `Fin 4 → ℕ` in that direction order. Our fields are
`top = n`, `bottom = s`, `left = w`, `right = e`: the same fixed-orientation tiling problem,
with a primitive-recursive reordering of the last two colour components, not identical codes.
We retain lean-wang's corrected component transcription; agreement of its literal tables with
all printed figures is not proved here.

The seeded-quadrant reduction encodes nonhalting of a universal `TM0` machine.
`Robinson.removeSeed` extends the quadrant to a pointed plane and combines that palette with
the concrete scaffold. Its primitive-recursive certificate and unconditional tileability
equivalence transfer undecidability to the unseeded plane problem. No aperiodicity theorem or
co-recursively-enumerable completeness result is asserted.

## Main results

* `Cslib.WangTile.not_computablePred_tilesPlane`: the domino problem is undecidable.

## References

* [R. Berger, *The undecidability of the domino problem*, Mem. AMS 66 (1966)][Berger1966].
  Internal locator not verified.
* [Robinson1971], §7, printed pp. 201–205.
* [Ollinger2008]. Internal locator not verified.
* [JeandelVanier2020], §1.1, Theorem 1, manuscript p. 2; §3.3, Theorem 10, manuscript p. 29;
  §3.4, pp. 29–30 attributes this proof route to Robinson and its underlying tile set to Ollinger.
* [lean-wang, revision 64268a3, Robinson endpoint](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Final.lean#L49).
-/

public section

namespace Cslib.WangTile

/-- **The domino problem is undecidable** (Berger, [Berger1966], Mem. AMS 66; internal locator
not verified). The proof is after [Robinson1971], §7, pp. 201–205, in the 104-tile form of
[Ollinger2008] (internal locator not verified), as presented by [JeandelVanier2020], §3.3,
Theorem 10, manuscript p. 29, ported and restructured from lean-wang revision `64268a3`.
Instances are
`List WangTile`, with the `Primcodable` tile encoding given by the explicit tuple equivalence
`(top, bottom, left, right)`. The prior formalization uses its `(n, s, e, w)` record and
`Fin 4 → ℕ` tiles; identifying `top = n`, `bottom = s`, `left = w`, `right = e` preserves the
fixed-orientation plane matching problem and reorders the last two coded components. -/
theorem not_computablePred_tilesPlane : ¬ ComputablePred TilesPlane := by
  intro h
  apply not_computablePred_tilesQuadrant
  exact ComputablePred.computable_of_manyOneReducible
    ⟨Robinson.removeSeed, Robinson.primrec_removeSeed.to_comp,
      fun I => (Robinson.tilesPlane_removeSeed_iff I).symm⟩ h

end Cslib.WangTile
