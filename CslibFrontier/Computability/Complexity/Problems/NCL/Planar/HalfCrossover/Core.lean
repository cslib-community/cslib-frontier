/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Prim
import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Enumeration

/-!
# The blue core of the half-crossover

The eight AND/OR vertices in [HearnDemaine2005, Figure 8(b)] implement a blue four-port vertex
with minimum inflow four. Its boundary order is top `[C, A]`, bottom `[B, D]`.
Certificates give eleven canonical extensions, five static refutations, and thirty-two directed
boundary moves. Refutations use two propagation rounds and at most one split; each move uses
at most seven internal reversals. `decide +kernel` checks only the four-bit boundary and these
explicit certificates.

## Main definitions

* `Cslib.Complexity.NCL.Planar.HalfCrossover.Core.diagram`: the core drawing.
* `Cslib.Complexity.NCL.Planar.HalfCrossover.Core.vertex`: its abstract threshold interface.

## Main results

* `Cslib.Complexity.NCL.Planar.HalfCrossover.Core.openSim` extends each legal boundary state
  and lifts each legal boundary reversal.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.Planar.HalfCrossover.Core

open Diagram

local notation "R" => Color.red
local notation "B" => Color.blue

/-- The eight-vertex blue core of Figure 8(b), with top ports `[C, A]` and bottom `[B, D]`. -/
@[expose] def diagram : Diagram Prim [B, B] [B, B] :=
  let node (a b : List Color) : Diagram Prim a b := gen [genVertex a b 2]
  (pad [B] (node [] [R, R, B]) [B]).comp <|
  (pad [B, R, R] (node [B, B] [B]) []).comp <|
  (pad [B, R, R] (node [B] [R, R]) []).comp <|
  (pad [] (node [B, R] [R]) [R, R, R]).comp <|
  (pad [R, R, R] (node [R] [R, B]) []).comp <|
  (pad [] (node [R, R] [B]) [R, R, B]).comp <|
  (pad [] (node [B] [B, B]) [R, R, B]).comp
  (pad [B] (node [B, R, R] []) [B])

/-- The four-blue-port vertex requiring at least two inward edges. -/
@[expose] def vertex : Prim [B, B] [B, B] := [genVertex [B, B] [B, B] 4]

end Cslib.Complexity.NCL.Planar.HalfCrossover.Core

end

public section

namespace Cslib.Complexity.NCL.Planar.HalfCrossover.Core

open Diagram

private def innerBits : ℕ → List ℕ
  | 0 | 1 | 2 | 3 => [2, 9, 13]
  | 5 => [2, 3, 8, 9, 11, 13]
  | 6 | 7 => [2, 5, 6, 9]
  | 9 => [4, 5, 7, 13]
  | 10 | 11 => [2, 5, 7, 13]
  | 15 => [2, 3, 5, 7, 8, 11, 13]
  | _ => []

private def refute : ℕ → Refutation ℕ
  | 13 => (.split 2 .conflict .conflict)
  | _ => .conflict

private def forwardMoves : ℕ → ℕ → List (Fin 14) × List (Fin 14)
  | 1, 2 => ([3, 8, 11], [])
  | 1, 3 => ([2, 4, 5, 7, 9], [])
  | 2, 2 => ([5, 6, 13], [])
  | 2, 3 => ([5, 7, 9], [])
  | 3, 2 => ([5, 6, 13], [])
  | 3, 3 => ([5, 7, 9], [])
  | 5, 1 => ([], [5, 6, 13, 11, 8, 3])
  | 7, 3 => ([3, 7, 8, 11, 13, 9], [6])
  | 9, 1 => ([], [4, 2])
  | 11, 2 => ([3, 8, 11], [])
  | _, _ => ([], [])

private def cert : Cert vertex diagram :=
  .ofTable { innerBits, rounds := 2, refute, forward := forwardMoves }

private theorem cert_valid : cert.Valid Prim.interp Prim.interp := by decide +kernel

/-- The blue core implements the four-port threshold vertex, including each legal boundary move. -/
def openSim : OpenSim Prim.interp Prim.interp (gen vertex) diagram :=
  OpenSim.ofCert cert cert_valid

end Cslib.Complexity.NCL.Planar.HalfCrossover.Core
