/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.FreeEnd

/-!
# Red-blue conversion

A red wire cannot be joined to a blue one, and in an AND/OR graph the red wire ends that are not
joined come in pairs. The conversion of [HearnDemaine2005, Figure 3] therefore has a second, free
red wire `F`, which this library draws explicitly (`Cslib.Complexity.NCL.Prim.conv`). It is built
(`Cslib.Complexity.NCL.Gadgets.conv`) from an AND vertex with red wires `A`, `E` and blue wire
`B`, an AND vertex with red wires `E`, `F` and blue wire `D`, and a free end on `D`
(`Cslib.Complexity.NCL.Gadgets.freeEnd`), which replaces the OR vertex with a loop of the paper.

With `D` into the second AND vertex and `E` into the first, the first AND vertex is satisfied
exactly when `A` or `B` points into the gadget, and the second whatever `F` does. So this one
inner configuration serves every boundary configuration, and no move needs moves inside.

## Main results

* `Cslib.Complexity.NCL.Gadgets.Conv.openSim`: the gadget implements the conversion.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Gadgets

open Diagram

local notation "R" => Color.red
local notation "B" => Color.blue

namespace Conv

/-- The first layer: AND `(A, E; B)`. -/
@[expose] def top : Diagram Prim [R] [B, R] := gen Prim.andRedToBlueRed

/-- The second layer: AND `(E, F; D)`, beside a continuation of color `c`. -/
@[expose] def mid (c : Color) : Diagram Prim [c, R] [c, R, B] :=
  (Diagram.id [c]).tensor (gen Prim.andRedToRedBlue)

/-- The third layer: a free end on `D`, beside the continuation and `F`. -/
@[expose] def low (c : Color) : Diagram Prim [c, R, B] [c, R] := (Diagram.id [c, R]).tensor freeEnd

end Conv

open Conv in
/-- The conversion: AND `(A, E; B)`, AND `(E, F; D)`, and a free end on `D`. -/
@[expose]
def conv : Diagram Prim [R] [B, R] := (top.comp (mid B)).comp (low B)

namespace Conv

/-- The wire `b` inside the free end. -/
@[expose] def freeEndBranch : conv.Edge :=
  compRight (top.comp (mid B)) (low B) (tensorRight (Diagram.id [B, R]) freeEnd FreeEnd.b)

/-- The certificates: one inner configuration for every boundary configuration, with `E` up into
the first AND vertex, `D` up into the second, and the free end in its canonical configuration.
The only forbidden boundary configuration, `A` up and `B` down, starves the first AND vertex. -/
@[expose] def cert : Cert Prim.conv conv where
  canon β y := if y = .inl 0 then β (.inl 0) else if y = conv.bottom 0 then β (.inr 0)
    else if y = conv.bottom 1 then β (.inr 1) else if y = freeEndBranch then true else false
  rounds := 1
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

/-- **The gadget implements the red-blue conversion.** -/
@[expose] def openSim : OpenSim Prim.interp Prim.interp (gen Prim.conv) conv :=
  OpenSim.ofCert cert (by decide +kernel)

end Conv

end Cslib.Complexity.NCL.Gadgets
