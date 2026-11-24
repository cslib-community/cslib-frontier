/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.FreeEnd
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Gate

/-!
# AND/OR implementations of circuit sources and ends

Close the auxiliary circuit wires using AND/OR vertices. A free blue source is the free-end
graph redrawn with its external wire below. A pair of red ends enters an AND whose blue wire
ends freely. A fixed blue end uses three AND vertices: their internal edges have total weight
five and their total minimum inflow is six, forcing the external blue wire inward. Its forbidden
boundary is checked by three rounds of propagation.

## Main definitions

* `Cslib.Complexity.NCL.Gadgets.freeStart`: a free blue wire starting above.
* `Cslib.Complexity.NCL.Gadgets.redCap`: two free red ends.
* `Cslib.Complexity.NCL.Gadgets.fixedBlue`: a blue end forced toward its AND vertex.

## Main results

* `Cslib.Complexity.NCL.Gadgets.FreeStart.openSim`,
  `Cslib.Complexity.NCL.Gadgets.RedCap.openSim`,
  `Cslib.Complexity.NCL.Gadgets.FixedBlue.openSim`: checked open simulations of the circuit
  generators.

## References

* The free-end construction follows [Hearn and Demaine][HearnDemaine2005, Figure 3].
-/

public section

namespace Cslib.Complexity.NCL.Gadgets

open Diagram

local notation "R" => Color.red
local notation "B" => Color.blue

/-- A free blue source: an OR and two ANDs, with the external blue wire below. -/
@[expose] def freeStart : Diagram Prim [] [B] :=
  (gen Prim.orSource).comp ((Diagram.id [B]).tensor
    (((gen Prim.andSplit).tensor (.id [B])).comp (gen Prim.andSink)))

namespace FreeStart

/-- Keep the second internal blue branch down; the other internal edges point up. -/
@[expose] def cert : Cert Gate.start freeStart where
  canon β y := if y = freeStart.bottom 0 then β (.inr 0) else freeStart.num y == 2
  rounds := 0
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

/-- The AND/OR source permits both directions of its external wire. -/
@[expose] def openSim : OpenSim Gate.interp Prim.interp (gen Gate.start) freeStart :=
  OpenSim.ofCert cert (by decide +kernel)

end FreeStart

/-- Free red ends enter an AND supported by a freely terminated blue wire. -/
@[expose] def redCap : Diagram Prim [R, R] [] := (gen Prim.andJoin).comp freeEnd

namespace RedCap

/-- The blue support points into the AND; the free end uses its canonical second branch. -/
@[expose] def cert : Cert Gate.cap redCap where
  canon β y := if y = .inl 0 then β (.inl 0) else if y = .inl 1 then β (.inl 1)
    else redCap.num y == 4
  rounds := 0
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

/-- The pair of red ends imposes no boundary restriction. -/
@[expose] def openSim : OpenSim Gate.interp Prim.interp (gen Gate.cap) redCap :=
  OpenSim.ofCert cert (by decide +kernel)

end RedCap

/-- Three ANDs force the external blue wire inward. The two lower ANDs share a red and a blue
wire; their remaining red wires connect to the upper AND. -/
@[expose] def fixedBlue : Diagram Prim [] [B] :=
  (gen Prim.andSource).comp ((pad [B] (gen Prim.andRedToRedBlue) [R]).comp
    ((Diagram.id [B]).tensor (gen (show Prim [R, B, R] [] from
      [.and ⟨.inl 0, true⟩ ⟨.inl 2, true⟩ ⟨.inl 1, true⟩]))))

namespace FixedBlue

/-- The canonical internal directions and the refutation of an outward blue wire. -/
@[expose] def cert : Cert (Gate.vert (a := []) (b := [B]) 2) fixedBlue where
  canon β y := if y = fixedBlue.bottom 0 then β (.inr 0) else [2, 3].contains (fixedBlue.num y)
  rounds := 3
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

/-- The gadget implements the single-wire constraint used for an empty disjunction. -/
@[expose] def openSim : OpenSim Gate.interp Prim.interp (gen (Gate.vert 2)) fixedBlue :=
  OpenSim.ofCert cert (by decide +kernel)

end FixedBlue

end Cslib.Complexity.NCL.Gadgets
