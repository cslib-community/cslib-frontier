/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Conv
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Gate

/-!
# Blue-to-red conversion

The blue-to-red conversion uses the same two-AND layout and free end as the red-to-blue
conversion [HearnDemaine2005, Figure 3]. The first AND has its blue wire above and both red
wires below. Its extra red wire points into that AND in the canonical configuration, so the
external blue input or the red output must point in. The second AND leaves the other red output
free. The certificate data are shared with the red-to-blue conversion and checked for the new
port weights.

## Main definitions

* `Cslib.Complexity.NCL.Gadgets.vnoc`: the blue-to-red converter with its free red wire.

## Main results

* `Cslib.Complexity.NCL.Gadgets.Vnoc.openSim`: the gadget implements `Gate.vnoc`.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Gadgets

open Diagram

local notation "R" => Color.red

/-- A blue input, red output and free red continuation, using two ANDs and a free end. -/
@[expose] def vnoc : Diagram Prim [Color.blue] [R, R] :=
  ((gen Prim.andSplit).comp (Conv.mid R)).comp (Conv.low R)

namespace Vnoc

/-- The red-to-blue certificate data also specify the blue-to-red canonical configurations. -/
@[expose] def cert : Cert Gate.vnoc vnoc where
  canon := Conv.cert.canon
  rounds := Conv.cert.rounds
  refute := Conv.cert.refute
  pre := Conv.cert.pre
  post := Conv.cert.post

/-- The AND/OR gadget implements the blue-to-red circuit gate. -/
@[expose] def openSim : OpenSim Gate.interp Prim.interp (gen Gate.vnoc) vnoc :=
  OpenSim.ofCert cert (by decide +kernel)

end Vnoc

end Cslib.Complexity.NCL.Gadgets
