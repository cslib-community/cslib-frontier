/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Conv
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Vnoc
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration

/-!
# Conversion drawings around a planar core

Four additional drawings of red-blue conversion complement `Cslib.Complexity.NCL.Gadgets.conv`.
They place the free red wire on either side of the converted wire, above or below the conversion.
The blue-to-red drawing also receives a primitive-generator interpretation.
Each has a fixed internal extension for all allowed boundary states, so boundary reversals
need no internal moves. These drawings pair the free wires along the sides of a crossover.

## Main definitions

* `Cslib.Complexity.NCL.Gadgets.Conv.redToRedBlue`: red input, red-blue output.
* `Cslib.Complexity.NCL.Gadgets.Conv.redBlueToRed`: red-blue input, red output.
* `Cslib.Complexity.NCL.Gadgets.Conv.blueRedToRed`: blue-red input, red output.

## Main results

* `Cslib.Complexity.NCL.Gadgets.Conv.redToRedBlueOpenSim`,
  `Cslib.Complexity.NCL.Gadgets.Conv.redBlueToRedOpenSim`,
  `Cslib.Complexity.NCL.Gadgets.Conv.blueRedToRedOpenSim`: certified open simulations.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Gadgets.Conv

open Diagram

local notation "R" => Color.red
local notation "B" => Color.blue

/-- Red input; free red and blue output, from left to right. -/
@[expose] def redToRedBlue : Diagram Prim [R] [R, B] :=
  ((gen Prim.andRedToRedBlue).comp (pad [] (gen Prim.andRedToBlueRed) [B])).comp
    (pad [] freeEnd [R, B])

/-- Free red and blue input; red output. -/
@[expose] def redBlueToRed : Diagram Prim [R, B] [R] :=
  ((pad [] (gen Prim.andRedToBlueRed) [B]).comp (pad [] freeEnd [R, B])).comp
    (gen [genVertex [R, B] [R] 2] : Diagram Prim [R, B] [R])

/-- Blue and free red input; red output. -/
@[expose] def blueRedToRed : Diagram Prim [B, R] [R] :=
  ((pad [B] (gen Prim.andRedToRedBlue) []).comp (pad [B, R] freeEnd [])).comp
    (gen [genVertex [B, R] [R] 2] : Diagram Prim [B, R] [R])

/-- Red-blue threshold relation with the free output on the left. -/
@[expose] def redToRedBlueGenerator : Prim [R] [R, B] :=
  [⟨[⟨⟨.inl 0, true⟩, 1⟩, ⟨⟨.inr 1, false⟩, 2⟩], 1⟩, .loose ⟨.inr 0, false⟩ 1]

/-- Blue-red threshold relation with the free input on the left. -/
@[expose] def redBlueToRedGenerator : Prim [R, B] [R] :=
  [⟨[⟨⟨.inl 1, true⟩, 2⟩, ⟨⟨.inr 0, false⟩, 1⟩], 1⟩, .loose ⟨.inl 0, true⟩ 1]

/-- Blue-red threshold relation with the free input on the right. -/
@[expose] def blueRedToRedGenerator : Prim [B, R] [R] :=
  [⟨[⟨⟨.inl 0, true⟩, 2⟩, ⟨⟨.inr 0, false⟩, 1⟩], 1⟩, .loose ⟨.inl 1, true⟩ 1]

/-- Two red inputs, the first converted to a blue output and the second free. -/
@[expose] def redRedToBlue : Diagram Prim [R, R] [B] :=
  ((pad [R] (gen Prim.andRedToRedBlue) []).comp (pad [R, R] freeEnd [])).comp
    (gen Prim.andJoin)

/-- Red-blue threshold relation with both red ports above the conversion. -/
@[expose] def redRedToBlueGenerator : Prim [R, R] [B] :=
  [⟨[⟨⟨.inl 0, true⟩, 1⟩, ⟨⟨.inr 0, false⟩, 2⟩], 1⟩, .loose ⟨.inl 1, true⟩ 1]

/-- Blue-red threshold relation with the free red port below and on the right. -/
@[expose] def blueToRedRedGenerator : Prim [B] [R, R] := Gate.interp.verts .vnoc

/-- Abstract conversions surrounding a blue four-port diagram, with the free reds paired by side. -/
@[expose] def abstractFrame (D : Diagram Prim [B, B] [B, B]) : Diagram Prim [R, R] [R, R] :=
  (((gen redToRedBlueGenerator).tensor (gen Prim.conv)).comp (pad [R] D [R])).comp
    ((gen redBlueToRedGenerator).tensor (gen blueRedToRedGenerator))

/-- Surround a blue diagram by concrete conversions, with free reds joined along its sides. -/
@[expose] def surround (D : Diagram Prim [B, B] [B, B]) : Diagram Prim [R, R] [R, R] :=
  ((redToRedBlue.tensor conv).comp (pad [R] D [R])).comp
    (redBlueToRed.tensor blueRedToRed)

/-- Candidate certificates for changing four blue ports to red: corresponding directions agree,
and each boundary move reverses its adjacent blue wire before or after the boundary reversal. -/
@[expose] def frameCert (red : Prim [R, R] [R, R]) (blue : Prim [B, B] [B, B]) :
    Cert red (abstractFrame (gen blue)) :=
  let D := abstractFrame (gen blue)
  let blueEdge (x : Fin 2 ⊕ Fin 2) : D.Edge := D.numEquiv.symm (match x with
    | .inl i => if i = 0 then 3 else 4
    | .inr i => if i = 0 then 6 else 7)
  { canon β y := if y = .inl 0 then β (.inl 0) else if y = .inl 1 then β (.inl 1)
      else if y = D.bottom 0 then β (.inr 0)
      else if y = D.bottom 1 then β (.inr 1)
      else if D.num y = 3 then β (.inl 0) else if D.num y = 4 then β (.inl 1)
      else if D.num y = 6 then β (.inr 0) else if D.num y = 7 then β (.inr 1)
      else false
    rounds := 2
    refute _ := .conflict
    pre β x := if β x = Sum.elim (fun _ => true) (fun _ => false) x then [blueEdge x] else []
    post β x := if β x = Sum.elim (fun _ => true) (fun _ => false) x then [] else [blueEdge x] }

end Cslib.Complexity.NCL.Gadgets.Conv

end

public section

namespace Cslib.Complexity.NCL.Gadgets.Conv

open Diagram

private def redToRedBlueCert : Cert redToRedBlueGenerator redToRedBlue where
  canon β y := if y = .inl 0 then β (.inl 0)
    else if y = redToRedBlue.bottom 0 then β (.inr 0)
    else if y = redToRedBlue.bottom 1 then β (.inr 1) else redToRedBlue.num y == 6
  rounds := 1
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

private def redBlueToRedCert : Cert redBlueToRedGenerator redBlueToRed where
  canon β y := if y = .inl 0 then β (.inl 0) else if y = .inl 1 then β (.inl 1)
    else if y = redBlueToRed.bottom 0 then β (.inr 0)
    else [3, 5].contains (redBlueToRed.num y)
  rounds := 1
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

private def blueRedToRedCert : Cert blueRedToRedGenerator blueRedToRed where
  canon β y := if y = .inl 0 then β (.inl 0) else if y = .inl 1 then β (.inl 1)
    else if y = blueRedToRed.bottom 0 then β (.inr 0)
    else [2, 5].contains (blueRedToRed.num y)
  rounds := 1
  refute _ := .conflict
  pre _ _ := []
  post _ _ := []

/-- The conversion drawing implements its threshold relation and free red endpoint. -/
def redToRedBlueOpenSim :
    OpenSim Prim.interp Prim.interp (gen redToRedBlueGenerator) redToRedBlue :=
  OpenSim.ofCert redToRedBlueCert (by decide +kernel)

/-- The conversion drawing implements its threshold relation and free red endpoint. -/
def redBlueToRedOpenSim :
    OpenSim Prim.interp Prim.interp (gen redBlueToRedGenerator) redBlueToRed :=
  OpenSim.ofCert redBlueToRedCert (by decide +kernel)

/-- The conversion drawing implements its threshold relation and free red endpoint. -/
def blueRedToRedOpenSim :
    OpenSim Prim.interp Prim.interp (gen blueRedToRedGenerator) blueRedToRed :=
  OpenSim.ofCert blueRedToRedCert (by decide +kernel)

private def redRedToBlueCert : Cert redRedToBlueGenerator redRedToBlue where
  canon := blueRedToRedCert.canon
  rounds := blueRedToRedCert.rounds
  refute := blueRedToRedCert.refute
  pre := blueRedToRedCert.pre
  post := blueRedToRedCert.post

/-- The two-input conversion implements its threshold relation and free red endpoint. -/
def redRedToBlueOpenSim :
    OpenSim Prim.interp Prim.interp (gen redRedToBlueGenerator) redRedToBlue :=
  OpenSim.ofCert redRedToBlueCert (by decide +kernel)

private def blueToRedRedCert : Cert blueToRedRedGenerator vnoc where
  canon := Vnoc.cert.canon
  rounds := Vnoc.cert.rounds
  refute := Vnoc.cert.refute
  pre := Vnoc.cert.pre
  post := Vnoc.cert.post

/-- The blue-to-red conversion, interpreted entirely over primitive diagrams. -/
def blueToRedRedOpenSim :
    OpenSim Prim.interp Prim.interp (gen blueToRedRedGenerator) vnoc :=
  OpenSim.ofCert blueToRedRedCert (by decide +kernel)

/-- Concrete conversions preserve any open implementation of the blue center. -/
def surroundOpenSim {D D' : Diagram Prim [Color.blue, Color.blue] [Color.blue, Color.blue]}
    (S : OpenSim Prim.interp Prim.interp D D') :
    OpenSim Prim.interp Prim.interp (abstractFrame D) (surround D') :=
  ((redToRedBlueOpenSim.tensor openSim).comp
    ((OpenSim.idWires [Color.red]).tensor (S.tensor (OpenSim.idWires [Color.red])))).comp
    (redBlueToRedOpenSim.tensor blueRedToRedOpenSim)

end Cslib.Complexity.NCL.Gadgets.Conv
